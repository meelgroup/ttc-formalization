/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.Computation.Num
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Operations: the real-RAM currency of TTC

**The resource claimed** (Theorem 3): the number of operations of a real RAM.  Every
arithmetic operation, every comparison, every random number read and every list cell
written or read costs one.

* `Op` — one charged operation: standard arithmetic of arlib's `NumOp` (`num`: a literal,
  `+ − · /`, `max`, `min`, a comparison, `⌈·⌉`, a loop entry), a real-RAM operation of
  arlib's `RealOp` (`real`: `ℕ → ℝ`, `√`, `exp`, `log`, `u^{1/k}`), one random number
  read (`draw`), or one list cell written or read (`cell`).  `NumOps Op` and `RealOps Op`
  make arlib's names the ones `Op` uses, so arlib's sealed numbers (`Num`) charge in
  this currency.
* `opsTotal` — the number of operations in a tally, each priced at `1`.
* `Round n`, `Tape n` — one round of random numbers, and the tape: a round for every
  `i : ℕ`.  A round holds a fair coin, a standard Gaussian vector and a number in
  `[0, 1]`; `Model/Run.lean` draws the rounds independently from those laws.
* `Oracle n` — **the sealed oracle**: the random tape.  Its field is private and its
  constructor is the noncomputable boundary `Oracle.ofTape`, used only by
  `Model/Run.lean`.
* `drawCoin`, `drawGaussian`, `drawUnit`, `drawPoisson` — the only ways to read the tape.
  Each reads one component of the current round, moves the tape on by one round, and
  charges its `draw`s; the numbers it returns are sealed.

Membership in a polytope is not an operation: TTC decides it by arithmetic on the
polytope's facets, and pays for that arithmetic.

**Assumed**: a Poisson draw costs one operation (`drawPoisson`), as in the paper's
accounting; it is the inverse of the Poisson distribution function at a uniform number.

Operations are vocabulary, not evidence: nothing here asserts a bound.
-/

set_option autoImplicit false

noncomputable section

namespace ttc.Model.Operations

open Arlib.Computation

/-- **One charged operation**: standard arithmetic (`num`), a real-RAM operation
(`real`), one random number read (`draw`), or one list cell written or read (`cell`). -/
inductive Op
  | num (o : NumOp)
  | real (o : RealOp)
  | draw
  | cell
  deriving DecidableEq, Repr

/-- Every operation, listed. -/
def Op.all : List Op :=
  [.num .lit, .num .add, .num .sub, .num .mul, .num .div, .num .max, .num .min,
   .num .cmp, .num .ceil, .num .loop,
   .real .cast, .real .sqrt, .real .exp, .real .log, .real .root, .draw, .cell]

theorem Op.mem_all (o : Op) : o ∈ Op.all := by
  rcases o with o | o | _ | _
  · cases o <;> decide
  · cases o <;> decide
  · decide
  · decide

instance : Fintype Op := Fintype.ofList Op.all Op.mem_all

/-- `Op` uses arlib's names for the standard arithmetic operations. -/
instance : NumOps Op where
  charge := Op.num
  charge_injective := fun _ _ h => Op.num.inj h

/-- `Op` uses arlib's names for the real-RAM operations. -/
instance : RealOps Op where
  charge := Op.real
  charge_injective := fun _ _ h => Op.real.inj h

/-- The storage currency.  No space bound is claimed, so it has one kind. -/
inductive Cell
  | cell
  deriving DecidableEq

/-- The programs of this development: charged computations in the real-RAM currency. -/
abbrev Prog := Charged Op Cell

/-- **The number of operations in a tally**, every operation priced at `1`. -/
def opsTotal (c : CostVec Op) : ℕ := ∑ o, c o

/-- A point of `ℝⁿ` held by the program: one sealed real per coordinate. -/
abbrev NumPoint (n : ℕ) : Type := Fin n → Num ℝ

/-- One round of random numbers: a fair coin, a standard Gaussian vector, and a number in
`[0, 1]`.  The laws are fixed by `Model/Run.lean`. -/
abbrev Round (n : ℕ) := Bool × EuclideanSpace ℝ (Fin n) × ℝ

/-- The random tape: one round for every `i : ℕ`. -/
abbrev Tape (n : ℕ) := ℕ → Round n

/-- The tape after its first round has been read. -/
def Tape.tail {n : ℕ} (t : Tape n) : Tape n := fun i => t (i + 1)

/-- **The sealed oracle**: the random tape.  The field is private: outside this module
the only access is the draws, each of which charges. -/
structure Oracle (n : ℕ) where
  private mk ::
  private tape : Tape n
  /-- The membership calls CV18 may still make (its query cap). -/
  private budget : ℕ

/-- The oracle with random tape `tape`.  **The boundary**: noncomputable, so a program
cannot build the oracle it wants; `Model/Run.lean` draws the tape. -/
def Oracle.ofTape {n : ℕ} (tape : Tape n) : Oracle n := ⟨tape, 0⟩

/-- The oracle with random tape `tape` and `budget` membership calls left.  Not for
programs (it is forbidden by the seal); the analysis uses it to name the oracle in the
middle of a run. -/
def Oracle.withBudget {n : ℕ} (tape : Tape n) (budget : ℕ) : Oracle n := ⟨tape, budget⟩

/-! ### CV18's query cap

CV18 stops a run that would make more than its budget of membership calls (Deviation 3 of
arlib-community's CV18).  The budget is a held count, used as a loop count is: set once,
at the price of one `NumOp.loop`, then consumed by the calls and never handed to the
program. -/

/-- **Set the query cap** to the held count `b`: one `NumOp.loop`. -/
def setBudget {n : ℕ} (b : Num ℕ) (o : Oracle n) : Prog (Unit × Oracle n) :=
  Charged.op (Op.num .loop) ((), ⟨o.tape, b.get⟩)

/-- **Spend one membership call of the cap**: `false`, and nothing spent, once it is
exhausted.  Free, as a loop's own counter is. -/
def spendQuery {n : ℕ} (o : Oracle n) : Prog (Bool × Oracle n) :=
  match o.budget with
  | 0 => pure (false, o)
  | k + 1 => pure (true, ⟨o.tape, k⟩)

/-! ### List cells -/

/-- **Append one cell** `x` to the list `xs`: one `cell`. -/
def push {α : Type} (xs : List α) (x : α) : Prog (List α) := Charged.op Op.cell (xs ++ [x])

/-- **Read one list cell**, the one holding `a`: one `cell`. -/
def cell {α : Type} (a : α) : Prog α := Charged.op Op.cell a

/-- The relabelling that turns `Num.lit`'s one `NumOp.lit` into one `draw`. -/
def drawLabel (o : Op) : CostVec Op :=
  if o = .num .lit then CostVec.one .draw else CostVec.one o

/-- A number read from the tape into the sealed world: one `draw`. -/
def sealDraw {α : Type} (a : α) : Prog (Num α) := Charged.exchange drawLabel (Num.lit a)

/-- **A fair coin**: read the current round's coin, move the tape on, charge one `draw`. -/
def drawCoin {n : ℕ} (o : Oracle n) : Prog (Bool × Oracle n) :=
  Charged.op Op.draw ((o.tape 0).1, ⟨o.tape.tail, o.budget⟩)

/-- **A uniform number in `[0, 1]`**: read the current round's number, move the tape on,
charge one `draw`. -/
def drawUnit {n : ℕ} (o : Oracle n) : Prog (Num ℝ × Oracle n) := do
  let u ← sealDraw (o.tape 0).2.2
  pure (u, ⟨o.tape.tail, o.budget⟩)

/-- The coordinates of a vector read from the tape into the sealed world, one `draw`
each. -/
def sealVector : (m : ℕ) → (Fin m → ℝ) → Prog (NumPoint m)
  | 0, _ => pure Fin.elim0
  | m + 1, v => do
      let x ← sealDraw (v 0)
      let rest ← sealVector m (Fin.tail v)
      pure (Fin.cons x rest)

/-- **A standard Gaussian vector**: read the current round's vector, move the tape on,
charge one `draw` per coordinate. -/
def drawGaussian {n : ℕ} (o : Oracle n) : Prog (NumPoint n × Oracle n) := do
  let g ← sealVector n (WithLp.ofLp (o.tape 0).2.1)
  pure (g, ⟨o.tape.tail, o.budget⟩)

/-- The inverse of the Poisson distribution function: the least `k` with
`u ≤ P(Poisson(λ) ≤ k)`. -/
def poissonQuantile (rate : NNReal) (u : ℝ) : ℕ :=
  sInf {k : ℕ | u ≤ (ProbabilityTheory.poissonMeasure rate).real (Set.Iic k)}

/-- **A Poisson draw** of rate `rate`: the Poisson quantile of the current round's
uniform number; move the tape on, charge one `draw`.  **Assumed** to cost one
operation, as in the paper's accounting. -/
def drawPoisson {n : ℕ} (rate : Num ℝ) (o : Oracle n) : Prog (Num ℕ × Oracle n) := do
  let k ← sealDraw (poissonQuantile (Real.toNNReal rate.get) (o.tape 0).2.2)
  pure (k, ⟨o.tape.tail, o.budget⟩)

/-- The inverse of the `Binomial(N, 1/2)` distribution function: the least `k` with
`u ≤ P(Binomial(N, 1/2) ≤ k)`. -/
def binomialHalfQuantile (N : ℕ) (u : ℝ) : ℕ :=
  sInf {k : ℕ | u ≤ ∑ i ∈ Finset.range (k + 1), ((N.choose i : ℝ) / 2 ^ N)}

/-- **A `Binomial(N, 1/2)` draw**: the binomial quantile of the current round's uniform
number; move the tape on, charge one `draw`.  **Assumed** to cost one operation, as in the
paper's accounting. -/
def drawBinomialHalf {n : ℕ} (N : Num ℕ) (o : Oracle n) : Prog (Num ℕ × Oracle n) := do
  let k ← sealDraw (binomialHalfQuantile N.get (o.tape 0).2.2)
  pure (k, ⟨o.tape.tail, o.budget⟩)

/-! ### Integers -/

/-- The relabelling that turns `Num.lit`'s one `NumOp.lit` into one `o`. -/
def relabelLit (o : Op) (o' : Op) : CostVec Op :=
  if o' = .num .lit then CostVec.one o else CostVec.one o'

/-- **`⌊x⌋`, as an integer**: one `NumOp.ceil` (arlib's rounding operation; its own
`Num.ceil` rounds up to a natural number, and a lattice coordinate may be negative). -/
def floor (x : Num ℝ) : Prog (Num ℤ) :=
  Charged.exchange (relabelLit (.num .ceil)) (Num.lit ⌊x.get⌋)

/-- **An integer read as a real**: one `RealOp.cast` (arlib's own `Num.cast` reads a
natural number). -/
def intCast (z : Num ℤ) : Prog (Num ℝ) :=
  Charged.exchange (relabelLit (.real .cast)) (Num.lit (z.get : ℝ))

/-! The operations on an oracle named by `Oracle.withBudget`.  These are the only facts
about the private fields that the analysis uses. -/

theorem ofTape_eq {n : ℕ} (t : Tape n) : Oracle.ofTape t = Oracle.withBudget t 0 := rfl

theorem setBudget_withBudget {n : ℕ} (b : Num ℕ) (t : Tape n) (k : ℕ) :
    setBudget b (Oracle.withBudget t k) =
      Charged.op (Op.num .loop) ((), Oracle.withBudget t b.get) :=
  rfl

theorem spendQuery_withBudget_zero {n : ℕ} (t : Tape n) :
    spendQuery (Oracle.withBudget t 0) = pure (false, Oracle.withBudget t 0) :=
  rfl

theorem spendQuery_withBudget_succ {n : ℕ} (t : Tape n) (k : ℕ) :
    spendQuery (Oracle.withBudget t (k + 1)) = pure (true, Oracle.withBudget t k) :=
  rfl

theorem drawCoin_withBudget {n : ℕ} (t : Tape n) (k : ℕ) :
    drawCoin (Oracle.withBudget t k) =
      Charged.op Op.draw ((t 0).1, Oracle.withBudget t.tail k) :=
  rfl

theorem drawUnit_withBudget {n : ℕ} (t : Tape n) (k : ℕ) :
    drawUnit (Oracle.withBudget t k) = (do
      let u ← sealDraw (t 0).2.2
      pure (u, Oracle.withBudget t.tail k)) :=
  rfl

theorem drawGaussian_withBudget {n : ℕ} (t : Tape n) (k : ℕ) :
    drawGaussian (Oracle.withBudget t k) = (do
      let g ← sealVector n (WithLp.ofLp (t 0).2.1)
      pure (g, Oracle.withBudget t.tail k)) :=
  rfl

theorem drawPoisson_withBudget {n : ℕ} (rate : Num ℝ) (t : Tape n) (k : ℕ) :
    drawPoisson rate (Oracle.withBudget t k) = (do
      let r ← sealDraw (poissonQuantile (Real.toNNReal rate.get) (t 0).2.2)
      pure (r, Oracle.withBudget t.tail k)) :=
  rfl

theorem drawBinomialHalf_withBudget {n : ℕ} (N : Num ℕ) (t : Tape n) (k : ℕ) :
    drawBinomialHalf N (Oracle.withBudget t k) = (do
      let r ← sealDraw (binomialHalfQuantile N.get (t 0).2.2)
      pure (r, Oracle.withBudget t.tail k)) :=
  rfl

end ttc.Model.Operations
