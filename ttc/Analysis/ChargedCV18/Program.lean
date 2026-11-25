/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18
import Arlib.Probability.Median
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import ttc.Meta.SealedProgram
import ttc.Analysis.ChargedCV18.Operations

/-!
# The charged CV18 program

arlib-community's `cv18Program` (`ArlibCommunity.Algorithms.CV18`) counts membership
queries only: its arithmetic is plain real arithmetic and costs nothing.  This file
writes the same algorithm with every number it computes held sealed, as arlib's `Num`,
and computed through arlib's charged operations (`Counted`), so that a program step
records the arithmetic it spends (`tick`).  `ChargedProgram` is arlib-community's
`ChargedProgram` with that one extra step.

The problem, the cooling schedule, the laws and the numeric parameters are
arlib-community's (`open ArlibCommunity.Algorithms.CV18`); only the charged program and
the counted arithmetic it runs are defined here.  `Analysis/ChargedCV18/Theorem.lean`
proves that deleting the charges gives arlib-community's program back, up to how the
random points are drawn, so the CV18 theorems carry over.
-/

open MeasureTheory

open Arlib
namespace ttc.ChargedCV18

open ArlibCommunity.Algorithms.CV18

/-! ### Sealed numbers and counted arithmetic

The program holds every number it computes as a sealed `Arlib.Computation.Num`: the
number is private to arlib, so the program can neither read it, nor compare it, nor
compute with it except through arlib's charged operations.  A point of `ℝⁿ` is held as
`n` sealed reals (`NumPoint`).

The operations are written with `Counted`, arlib's charged computations
`Arlib.Computation.Charged` in the currency `Op` of `Model/Operations.lean`.  Each
primitive below is one of arlib's `Num` operations: `+`, `−`, `·`, `/`, a comparison,
`max`, `min`, `⌈·⌉` and a literal are `NumOp`s; `ℕ → ℝ`, `√`, `exp`, `log` and `u^{1/k}`
are `RealOp`s.  The tally of a computation (`Counted.tally`) records how many operations of
each kind it spent, and `Counted.cost` prices each at `1`.  A program step `compute c`
(below) records `c`'s tally, so an operation count is read off the program text instead
of being asserted next to it. -/

open Arlib.Computation in
/-- A charged computation of CV18: a value together with the operations spent computing
it, as arlib's `Charged` in the currency `Op`. -/
def Counted (α : Type) : Type := Charged Op Cell α

open Arlib.Computation in
/-- **A point of `ℝⁿ` held by the program**: one sealed real per coordinate. -/
abbrev NumPoint (n : ℕ) : Type := Fin n → Num ℝ

/-- The point of `ℝⁿ` a held point stands for.  **Specification-only**: a program uses it
only to hand a point to the membership oracle (`isMember`). -/
noncomputable def NumPoint.view {n : ℕ} (x : NumPoint n) : AmbientSpace n :=
  WithLp.toLp 2 fun i => (x i).get

namespace Counted

open Arlib.Computation

instance : Monad Counted := inferInstanceAs (Monad (Charged Op Cell))

/-- The value a charged computation produces.  **Specification-only.** -/
noncomputable def value {α : Type} (c : Counted α) : α := Charged.val (κ := Op) (κₛ := Cell) c

/-- The operations a charged computation spends, by kind. -/
def tally {α : Type} (c : Counted α) : CostVec Op := Charged.cost (κ := Op) (κₛ := Cell) c

/-- The number of operations a charged computation spends, each priced at `1`. -/
def cost {α : Type} (c : Counted α) : ℕ := opsTotal c.tally

/-- Return `a` without spending anything. -/
def pure {α : Type} (a : α) : Counted α := Charged.pure a

/-- A constant from outside the sealed world (an input, a parameter, a literal): one
`NumOp.lit`. -/
def lit {α : Type} (a : α) : Counted (Num α) := Num.lit a

/-- The relabelling that turns `lit`'s one `NumOp.lit` into one `draw`. -/
def drawLabel (o : Op) : CostVec Op :=
  if o = .num .lit then CostVec.one .draw else CostVec.one o

/-- **One random number read into the sealed world**: one `draw`.  `Num`'s constructor is
arlib's, so the number is sealed by `Num.lit`, whose charge is relabelled as a `draw`. -/
def pick {α : Type} (a : α) : Counted (Num α) := Charged.exchange drawLabel (Num.lit a)

/-- **Append one cell** `x` to the list `xs`: one `cell`. -/
def push {α : Type} (xs : List α) (x : α) : Counted (List α) := Charged.op Op.cell (xs ++ [x])

/-- **Read one list cell**, the one holding `a`: one `cell`. -/
def cell {α : Type} (a : α) : Counted α := Charged.op Op.cell a

/-- **One membership-oracle call**, passing on the oracle's answer `b`: one `query`. -/
def isMember (b : Bool) : Counted Bool := Charged.op Op.query b

/-- `x + y`: one `NumOp.add`. -/
def add {α : Type} [Add α] (x y : Num α) : Counted (Num α) := Num.add x y

/-- `x − y`: one `NumOp.sub`. -/
def sub {α : Type} [Sub α] (x y : Num α) : Counted (Num α) := Num.sub x y

/-- `x · y`: one `NumOp.mul`. -/
def mul {α : Type} [Mul α] (x y : Num α) : Counted (Num α) := Num.mul x y

/-- `x / y`: one `NumOp.div`. -/
def div {α : Type} [Div α] (x y : Num α) : Counted (Num α) := Num.div x y

/-- The larger of `x` and `y`: one `NumOp.max`. -/
def max {α : Type} [Max α] (x y : Num α) : Counted (Num α) := Num.max x y

/-- The smaller of `x` and `y`: one `NumOp.min`. -/
def min {α : Type} [Min α] (x y : Num α) : Counted (Num α) := Num.min x y

/-- The test `x ≤ y`: one `NumOp.cmp`. -/
def le {α : Type} [LE α] [DecidableLE α] (x y : Num α) : Counted Bool := Num.le x y

/-- The test `x < y`, asked as `¬ (y ≤ x)`: one `NumOp.cmp`. -/
def lt {α : Type} [LinearOrder α] (x y : Num α) : Counted Bool := do
  let b ← Num.le y x
  Counted.pure (!b)

/-- `⌈x⌉₊`, the ceiling as a natural number: one `NumOp.ceil`. -/
noncomputable def ceil (x : Num ℝ) : Counted (Num ℕ) := Num.ceil x

/-- A natural number read as a real: one `RealOp.cast`. -/
def cast (k : Num ℕ) : Counted (Num ℝ) := Num.cast k

/-- `√x`: one `RealOp.sqrt`. -/
noncomputable def sqrt (x : Num ℝ) : Counted (Num ℝ) := Num.sqrt x

/-- `log x`: one `RealOp.log`. -/
noncomputable def log (x : Num ℝ) : Counted (Num ℝ) := Num.log x

/-- `exp x`: one `RealOp.exp`. -/
noncomputable def exp (x : Num ℝ) : Counted (Num ℝ) := Num.exp x

/-- The `k`-th root `u^{1/k}`: one `RealOp.root`. -/
noncomputable def root (u : Num ℝ) (k : Num ℕ) : Counted (Num ℝ) := Num.root u k

/-- The power `x^k` for a power `k` written in the program, by `k` multiplications
starting from the literal `1`. -/
def pow (x : Num ℝ) : ℕ → Counted (Num ℝ)
  | 0 => lit 1
  | k + 1 => do
      let y ← pow x k
      mul y x

/-- **A loop over a held count that can stop early**: run `f` on the state at most `n`
times, stopping as soon as it returns `none`; one `NumOp.loop` plus what the rounds spend
(arlib's `Num.iterateWhile`). -/
def iterateWhile {β : Type} (f : β → Counted (Option β)) (n : Num ℕ) (b : β) : Counted β :=
  Num.iterateWhile (fun _ b => f b) n b

/-- Compute each coordinate `f i` of a vector, one after another; the costs add. -/
def forEach {α : Type} : {n : ℕ} → (Fin n → Counted α) → Counted (Fin n → α)
  | 0, _ => pure Fin.elim0
  | _ + 1, f => do
      let first ← f 0
      let rest ← forEach fun i => f i.succ
      pure (Fin.cons first rest)

/-- The dot product `a₀x₀ + ⋯ + aₙ₋₁xₙ₋₁`: `n` multiplications and `n − 1` additions. -/
def dot : (n : ℕ) → NumPoint n → NumPoint n → Counted (Num ℝ)
  | 0, _, _ => lit 0
  | 1, a, x => mul (a 0) (x 0)
  | n + 2, a, x => do
      let first ← mul (a 0) (x 0)
      let rest ← dot (n + 1) (Fin.tail a) (Fin.tail x)
      add first rest

/-- `‖x‖² = x₀² + ⋯ + xₙ₋₁²`: a dot product, `2n − 1` operations. -/
def normSq {n : ℕ} (x : NumPoint n) : Counted (Num ℝ) := dot n x x

/-- `‖x‖ = √(‖x‖²)`: `2n` operations. -/
noncomputable def norm {n : ℕ} (x : NumPoint n) : Counted (Num ℝ) := do
  let s ← normSq x
  sqrt s

/-- The scaled vector `a • x`: one multiplication per coordinate. -/
def smul {n : ℕ} (a : Num ℝ) (x : NumPoint n) : Counted (NumPoint n) :=
  forEach fun i => mul a (x i)

/-- The vector sum `x + y`: one addition per coordinate. -/
def addVec {n : ℕ} (x y : NumPoint n) : Counted (NumPoint n) :=
  forEach fun i => add (x i) (y i)

/-- The sum `a₀ + ⋯ + aₘ₋₁` of `m ≥ 1` held natural numbers: `m − 1` additions. -/
def sum : (m : ℕ) → (Fin m → Num ℕ) → Counted (Num ℕ)
  | 0, _ => lit 0
  | 1, a => Counted.pure (a 0)
  | m + 2, a => do
      let rest ← sum (m + 1) (Fin.tail a)
      add (a 0) rest

/-- The median of the held numbers `v`, of which there are `m`: the entry of rank
`⌊m/2⌋`, by comparison counting.  For each entry `vᵢ`, count the entries below `vᵢ` and
those at most `vᵢ` (`2|v|` comparisons and `2(|v| − 1)` additions), then test whether
rank `⌊m/2⌋` falls between the two counts (two comparisons), and return the first entry
that passes.  Each entry is read from the list once (`|v|` cells). -/
noncomputable def median (m : Num ℕ) (v : List (Num ℝ)) : Counted (Num ℝ) := do
  let w ← forEach fun i : Fin v.length => cell (v.get i)
  let zero ← lit (0 : ℕ)
  let one ← lit (1 : ℕ)
  let below ← forEach fun i => do
    let flags ← forEach fun j => lt (w j) (w i)
    sum v.length fun j => if flags j then one else zero
  let atMost ← forEach fun i => do
    let flags ← forEach fun j => le (w j) (w i)
    sum v.length fun j => if flags j then one else zero
  let two ← lit (2 : ℕ)
  let rank ← div m two
  let passes ← forEach fun i => do
    let a ← le (below i) rank
    let b ← lt rank (atMost i)
    Counted.pure (a && b)
  match (List.finRange v.length).find? passes with
  | some i => Counted.pure (w i)
  | none => lit 0

/-- `protectedLog x = max 1 (log x)`: three operations. -/
noncomputable def protectedLog (x : Num ℝ) : Counted (Num ℝ) := do
  let l ← log x
  let one ← lit 1
  max one l

/-- A uniform point of the unit ball from a standard Gaussian vector `g` and a uniform
`u ∈ [0, 1]`: `(u^{1/n} / ‖g‖) · g`, where `dim` holds `n`. -/
noncomputable def ballStart {n : ℕ} (dim : Num ℕ) (g : NumPoint n) (u : Num ℝ) :
    Counted (NumPoint n) := do
  let sq ← normSq g
  let len ← sqrt sq
  let radius ← root u dim
  let scale ← div radius len
  smul scale g

/-- The Gaussian log-weight `−‖x‖²/(2s)` at variance `s`: `2n + 4` operations. -/
noncomputable def gaussianLogWeight {n : ℕ} (s : Num ℝ) (x : NumPoint n) :
    Counted (Num ℝ) := do
  let a ← normSq x
  let two ← lit 2
  let t ← mul two s
  let d ← div a t
  let zero ← lit 0
  sub zero d

end Counted

/-! ### Programs -/

/-- A membership-oracle program in dimension `n` returning a `Result`.

A program is a tree of steps: `query x next` asks the oracle whether `x` is in
the body and continues with `next answer`; the `random*` steps draw a value
from a probability law and continue with it; `tick c next` records the tally `c` of
arithmetic operations and continues with `next`; `pure r` returns `r`.  The body is
never an argument, so a program learns about it only through `query` steps.
This is what makes the theorem a statement about a membership-oracle
algorithm, and what lets `Pseudocode.lean` count queries and arithmetic
operations from the program itself.

The algorithm is written with `do` notation (see the `Monad` instance below and
the primitives `isMember`, `drawPoint`, `drawReal`, `compute`); the constructors are only
needed to define the semantics and the cost model. -/
inductive ChargedProgram (n : ℕ) (Result : Type) where
  | pure (result : Result)
  | query (point : AmbientSpace n) (next : Bool → ChargedProgram n Result)
  | randomNat (law : PMF ℕ) (next : ℕ → ChargedProgram n Result)
  | randomPoint (law : Measure (AmbientSpace n))
      (lawProbability : IsProbabilityMeasure law)
      (next : AmbientSpace n → ChargedProgram n Result)
  | randomReal (law : Measure ℝ) (lawProbability : IsProbabilityMeasure law)
      (next : ℝ → ChargedProgram n Result)
  /-- Spend the operations tallied in `ops`, then continue.  Programs use it only
  through `compute`, which takes `ops` from a `Counted` computation. -/
  | tick (ops : Arlib.Computation.CostVec Op) (next : ChargedProgram n Result)

/-- A uniform randomized charged algorithm for ordinary volume. -/
abbrev ChargedVolumeAlgorithm := (q : VolumeParams) → ChargedProgram q.n ℝ

/-- Sequential composition of membership-oracle programs. -/
def ChargedProgram.bind {n : ℕ} {A B : Type}
    (program : ChargedProgram n A)
    (next : A → ChargedProgram n B) : ChargedProgram n B :=
  match program with
  | .pure result => next result
  | .query point branch => .query point (fun answer => (branch answer).bind next)
  | .randomNat law branch => .randomNat law (fun seed => (branch seed).bind next)
  | .randomPoint law hprob branch =>
      .randomPoint law hprob (fun point => (branch point).bind next)
  | .randomReal law hprob branch =>
      .randomReal law hprob (fun value => (branch value).bind next)
  | .tick ops rest => .tick ops (rest.bind next)

/-- **The output law of a program** when every query is answered by `oracle`:
a `query` step follows the oracle's answer, and a random step averages the rest
of the program over its law.  (Query cost is not part of this law; it is read
off the program itself by `queryCost` in `Pseudocode.lean`.) -/
noncomputable def ChargedProgram.runEstimate {n : ℕ} {Result : Type}
    [MeasurableSpace Result] (oracle : AmbientSpace n → Bool) :
    ChargedProgram n Result → Measure Result
  | .pure result => Measure.dirac result
  | .query point next => runEstimate oracle (next (oracle point))
  | .randomNat law next => law.toMeasure.bind fun seed => runEstimate oracle (next seed)
  | .randomPoint law _ next => law.bind fun point => runEstimate oracle (next point)
  | .randomReal law _ next => law.bind fun value => runEstimate oracle (next value)
  | .tick _ next => runEstimate oracle next

/-- `do` notation for oracle programs: `let x ← p; rest` runs `p`, then `rest`. -/
noncomputable instance (n : ℕ) : Monad (ChargedProgram n) where
  pure := .pure
  bind := ChargedProgram.bind

/-- Run the arithmetic `c` and hold its result, spending the operations it tallies.
Neither the oracle nor the output law sees the count (`runEstimate` skips `tick`). -/
noncomputable def compute {n : ℕ} {α : Type} (c : Counted α) : ChargedProgram n α :=
  .tick c.tally (.pure c.value)

/-- Ask the membership oracle whether the held point `x` is in the body: one `query`
(`Counted.isMember`).  This is the only way a program can learn anything about the body; the
oracle, not the program, reads the point. -/
noncomputable def isMember {n : ℕ} (x : NumPoint n) : ChargedProgram n Bool :=
  .query x.view fun b => compute (Counted.isMember b)

/-- Draw a point of `ℝⁿ` from the probability law `law`, and hold it: its `n` coordinates
enter the sealed world one `draw` each (`Counted.pick`). -/
noncomputable def drawPoint {n : ℕ} (law : Measure (AmbientSpace n))
    [h : IsProbabilityMeasure law] : ChargedProgram n (NumPoint n) :=
  .randomPoint law h fun g => compute (Counted.forEach fun i => Counted.pick (g i))

/-- Draw a real number from the probability law `law`, and hold it: one `draw`. -/
noncomputable def drawReal {n : ℕ} (law : Measure ℝ) [h : IsProbabilityMeasure law] :
    ChargedProgram n (Arlib.Computation.Num ℝ) :=
  .randomReal law h fun v => compute (Counted.pick v)

/-- The rounds of `loopUntil`, by their number: run `body` on the state until it stops
(`inr`), at most `rounds` times; `inl` is the state when the rounds run out.  Programs
use it only through `loopUntil`. -/
noncomputable def ChargedProgram.loopRounds {n : ℕ} {β γ : Type}
    (body : β → ChargedProgram n (β ⊕ γ)) :
    ℕ → β → ChargedProgram n (β ⊕ γ)
  | 0, b => .pure (.inl b)
  | rounds + 1, b => (body b).bind fun
      | .inl b' => loopRounds body rounds b'
      | .inr c => .pure (.inr c)

open Arlib.Computation in
/-- **A loop whose length is a held number**, at the price of one `NumOp.loop` plus what
its rounds spend: run `body` from `init` until it stops (`inr`), at most `count` times;
`inl` is the state when the rounds run out.  As in arlib's `Num.iterate`, the count is
consumed and never handed to the program. -/
noncomputable def loopUntil {n : ℕ} {β γ : Type} (count : Num ℕ)
    (body : β → ChargedProgram n (β ⊕ γ)) (init : β) :
    ChargedProgram n (β ⊕ γ) :=
  .tick (CostVec.one (numOpcode Op .loop)) (ChargedProgram.loopRounds body count.get init)

/-- Hand the held number `x` out of the program as its result.  The output of a
volume algorithm is a real number, and this is where it leaves the sealed world. -/
noncomputable def report {n : ℕ} (x : Arlib.Computation.Num ℝ) : ChargedProgram n ℝ :=
  .pure x.get


/-- The standard Gaussian vector on `ℝⁿ`: `n` independent standard Gaussian numbers. -/
noncomputable def standardGaussian (n : ℕ) : Measure (AmbientSpace n) :=
  ProbabilityTheory.stdGaussian (AmbientSpace n)

instance standardGaussian_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (standardGaussian n) := by
  unfold standardGaussian
  infer_instance


/-! ### The tests and weights as counted arithmetic

`Pseudocode.lean` runs each of the formulas above through `compute`, using the
programs below, on held numbers.  Quantities that depend only on the parameters and the
phase variance (`√(C²n)`, the phase radius, the scale factor) enter as inputs; the program
computes them once per call or per phase (section 8).  `Analysis/` proves each program
computes its formula. -/

open Arlib.Computation (Num)

/-- The proper-proposal test `‖y‖ ≤ rootT ∧ ‖y‖ ≤ radius`. -/
noncomputable def properTestProg {n : ℕ} (rootT radius : Num ℝ) (y : NumPoint n) :
    Counted Bool := do
  let ny ← Counted.norm y
  let a ← Counted.le ny rootT
  let b ← Counted.le ny radius
  Counted.pure (a && b)

/-- The lazy Metropolis test `coin ≤ lazyAcceptance sigma2 x y`. -/
noncomputable def lazyTestProg {n : ℕ} (sigma2 : Num ℝ) (x y : NumPoint n) (coin : Num ℝ) :
    Counted Bool := do
  let ly ← Counted.gaussianLogWeight sigma2 y
  let lx ← Counted.gaussianLogWeight sigma2 x
  let ey ← Counted.exp ly
  let ex ← Counted.exp lx
  let r ← Counted.div ey ex
  let one ← Counted.lit 1
  let m ← Counted.min one r
  let two ← Counted.lit 2
  let h ← Counted.div m two
  Counted.le coin h

/-- The speedy-to-target acceptance test
`coin ≤ ½ · e^{−‖y‖²/(2σ²)} / e^{−‖y‖²/(2σ²/c²)}`. -/
noncomputable def scaleAcceptTestProg {n : ℕ} (sigma2 c : Num ℝ) (y : NumPoint n)
    (coin : Num ℝ) : Counted Bool := do
  let cc ← Counted.mul c c
  let v ← Counted.div sigma2 cc
  let a ← Counted.gaussianLogWeight sigma2 y
  let b ← Counted.gaussianLogWeight v y
  let ea ← Counted.exp a
  let eb ← Counted.exp b
  let r ← Counted.div ea eb
  let two ← Counted.lit 2
  let h ← Counted.div r two
  Counted.le coin h

/-- The estimator weight `gaussianRatioWeight sigma2 tau2 x`. -/
noncomputable def gaussianRatioWeightProg {n : ℕ} (sigma2 tau2 : Num ℝ) (x : NumPoint n) :
    Counted (Num ℝ) := do
  let a ← Counted.gaussianLogWeight tau2 x
  let b ← Counted.gaussianLogWeight sigma2 x
  let ea ← Counted.exp a
  let eb ← Counted.exp b
  Counted.div ea eb

/-- The estimator weight `uniformRatioWeight sigma2 x = e^{‖x‖²/(2σ²)}`. -/
noncomputable def uniformRatioWeightProg {n : ℕ} (sigma2 : Num ℝ) (x : NumPoint n) :
    Counted (Num ℝ) := do
  let a ← Counted.normSq x
  let two ← Counted.lit 2
  let t ← Counted.mul two sigma2
  let d ← Counted.div a t
  Counted.exp d

/-- The ball-walk proposal: a uniform point of the ball of radius `radius` around `x`,
`x + radius · ballStart g u`, from a standard Gaussian vector `g` and a uniform `u`;
`dim` holds the dimension. -/
noncomputable def ballProposalProg {n : ℕ} (dim : Num ℕ) (x : NumPoint n) (radius : Num ℝ)
    (g : NumPoint n) (u : Num ℝ) : Counted (NumPoint n) := do
  let p ← Counted.ballStart dim g u
  let s ← Counted.smul radius p
  Counted.addVec x s

/-- The starting point: a Gaussian of variance `variance` per coordinate, `√variance · g`,
from a standard Gaussian vector `g`. -/
noncomputable def gaussianStartProg {n : ℕ} (rootVariance : Num ℝ) (g : NumPoint n) :
    Counted (NumPoint n) :=
  Counted.smul rootVariance g

/-! ## 8. Computing the constants

`cv18Program` computes every number it uses, as counted arithmetic on held numbers, once
where it becomes known: the constants that depend only on the parameters once per call
(`runConstantsProg`), and those that depend on the phase variance once per phase
(`phaseConstantsProg`).  The parameters themselves enter as literals.  `runConstants` and
`phaseConstants` collect the formulas above, and `RunConstants.view` and
`PhaseConstants.view` read a held record; `Analysis/` proves each program computes its
formulas. -/

open Arlib.Computation (Num)

/-- The constants of one call, held by the program. -/
structure RunConstants where
  /-- The dimension `n`, as a real number. -/
  dimension : Num ℝ
  /-- The dimension `n`, as a natural number. -/
  dimensionCount : Num ℕ
  /-- The terminal variance `C²n`. -/
  terminal : Num ℝ
  /-- `√(C²n)`. -/
  rootTerminal : Num ℝ
  /-- `√σ₀²`. -/
  rootInitial : Num ℝ
  /-- The Gaussian integral `(2πσ₀²)^{n/2}`. -/
  gaussianIntegral : Num ℝ
  /-- The scale factor `c` and its inverse. -/
  scale : Num ℝ
  scaleInv : Num ℝ
  /-- The cooling schedule. -/
  schedule : List (Num ℝ)
  sampleCount : Num ℕ
  fixedRateSampleCount : Num ℕ
  maxRetries : Num ℕ
  accuracyLog : Num ℝ
  /-- `blockMixingError q (maxRetries q − 1)`. -/
  blockError : Num ℝ
  warm : Num ℝ
  queryBudget : Num ℕ
  repetitions : Num ℕ

/-- The constants of one call, as numbers. -/
structure RunValues where
  dimension : ℝ
  dimensionCount : ℕ
  terminal : ℝ
  rootTerminal : ℝ
  rootInitial : ℝ
  gaussianIntegral : ℝ
  scale : ℝ
  scaleInv : ℝ
  schedule : List ℝ
  sampleCount : ℕ
  fixedRateSampleCount : ℕ
  maxRetries : ℕ
  accuracyLog : ℝ
  blockError : ℝ
  warm : ℝ
  queryBudget : ℕ
  repetitions : ℕ

/-- The numbers a held record of call constants stands for.  **Specification-only.** -/
noncomputable def RunConstants.view (G : RunConstants) : RunValues where
  dimension := G.dimension.get
  dimensionCount := G.dimensionCount.get
  terminal := G.terminal.get
  rootTerminal := G.rootTerminal.get
  rootInitial := G.rootInitial.get
  gaussianIntegral := G.gaussianIntegral.get
  scale := G.scale.get
  scaleInv := G.scaleInv.get
  schedule := G.schedule.map Num.get
  sampleCount := G.sampleCount.get
  fixedRateSampleCount := G.fixedRateSampleCount.get
  maxRetries := G.maxRetries.get
  accuracyLog := G.accuracyLog.get
  blockError := G.blockError.get
  warm := G.warm.get
  queryBudget := G.queryBudget.get
  repetitions := G.repetitions.get

/-- The constants of one call, as formulas. -/
noncomputable def runConstants (q : VolumeParams) : RunValues where
  dimension := q.n
  dimensionCount := q.n
  terminal := terminalVariance q
  rootTerminal := Real.sqrt (terminalVariance q)
  rootInitial := Real.sqrt (initialVariance q)
  gaussianIntegral := initialGaussianIntegral q
  scale := scaleFactor q
  scaleInv := (scaleFactor q)⁻¹
  schedule := coolingSchedule q
  sampleCount := sampleCount q
  fixedRateSampleCount := fixedRateSampleCount q
  maxRetries := maxRetries q
  accuracyLog := accuracyLog q
  blockError := blockMixingError q (maxRetries q - 1)
  warm := warmConstant q
  queryBudget := queryBudget q
  repetitions := confidenceRepetitions q

/-- The constants of one phase, held by the program. -/
structure PhaseConstants where
  /-- The truncation radius `phaseRadius q σ²`. -/
  radius : Num ℝ
  /-- The ball-walk proposal radius `proposalRadius q σ²`. -/
  proposal : Num ℝ
  /-- The walk length `walkSteps q σ²`. -/
  steps : Num ℕ
  /-- The proposal cap `maxProposals q σ²`. -/
  cap : Num ℕ
  /-- The sample count `phaseSampleCount q σ²`. -/
  samples : Num ℕ

/-- The constants of one phase, as numbers. -/
structure PhaseValues where
  radius : ℝ
  proposal : ℝ
  steps : ℕ
  cap : ℕ
  samples : ℕ

/-- The numbers a held record of phase constants stands for.  **Specification-only.** -/
noncomputable def PhaseConstants.view (P : PhaseConstants) : PhaseValues where
  radius := P.radius.get
  proposal := P.proposal.get
  steps := P.steps.get
  cap := P.cap.get
  samples := P.samples.get

/-- The constants of one phase, as formulas. -/
noncomputable def phaseConstants (q : VolumeParams) (sigma2 : ℝ) : PhaseValues where
  radius := phaseRadius q sigma2
  proposal := proposalRadius q sigma2
  steps := walkSteps q sigma2
  cap := maxProposals q sigma2
  samples := phaseSampleCount q sigma2

namespace Counted

/-- `c · x` for a constant `c` of the program text: a literal and a multiplication. -/
def mulLit (c : ℝ) (x : Num ℝ) : Counted (Num ℝ) := do
  let k ← lit c
  mul k x

/-- `x / c` for a constant `c` of the program text: a literal and a division. -/
noncomputable def divLit (x : Num ℝ) (c : ℝ) : Counted (Num ℝ) := do
  let k ← lit c
  div x k

/-- `c / x` for a constant `c` of the program text: a literal and a division. -/
noncomputable def litDiv (c : ℝ) (x : Num ℝ) : Counted (Num ℝ) := do
  let k ← lit c
  div k x

/-- `max c x` for a constant `c` of the program text: a literal and a `max`. -/
def litMax (c : ℝ) (x : Num ℝ) : Counted (Num ℝ) := do
  let k ← lit c
  max k x

end Counted

/-- One step of the cooling schedule, `nextVariance`. -/
noncomputable def nextVarianceProg (dimension terminal sigma2 : Num ℝ) :
    Counted (Num ℝ) := do
  let one ← Counted.lit 1
  let small ← Counted.le sigma2 one
  let rate ← if small then (do
      let a ← Counted.litDiv 1 dimension
      Counted.add one a)
    else (do
      let b ← Counted.mulLit 2 terminal
      let c ← Counted.div sigma2 b
      Counted.add one c)
  let m ← Counted.mul sigma2 rate
  Counted.min terminal m

/-- One round of the schedule loop: stop once the variance `s` reaches `terminal`,
otherwise record it, take one `nextVariance` step, and count it. -/
noncomputable def scheduleRound (dimension terminal : Num ℝ) (one : Num ℕ)
    (st : List (Num ℝ) × Num ℝ × Num ℕ) : Counted (Option (List (Num ℝ) × Num ℝ × Num ℕ)) := do
  let stop ← Counted.le terminal st.2.1
  if stop then Counted.pure none else do
    let next ← nextVarianceProg dimension terminal st.2.1
    let count' ← Counted.add st.2.2 one
    let done ← Counted.push st.1 st.2.1
    Counted.pure (some (done, next, count'))

/-- The cooling schedule from `sigma2` on, and its length: stop once the variance
reaches `terminal`, otherwise take one more `nextVariance` step, for at most `fuel` steps
(a held count; the loop stops on its test). -/
noncomputable def scheduleProg (dimension terminal : Num ℝ) (fuel : Num ℕ) (sigma2 : Num ℝ) :
    Counted (List (Num ℝ) × Num ℕ) := do
  let one ← Counted.lit (1 : ℕ)
  let r ← Counted.iterateWhile (scheduleRound dimension terminal one) fuel ([], sigma2, one)
  let schedule ← Counted.push r.1 r.2.1
  Counted.pure (schedule, r.2.2)

/-- The constants of one call, computed. -/
noncomputable def runConstantsProg (q : VolumeParams) : Counted RunConstants := do
  -- the parameters
  let nN ← Counted.lit q.n
  let n ← Counted.cast nN
  let eps ← Counted.lit q.eps
  let roundness ← Counted.lit q.roundness
  let p ← Counted.lit q.p
  -- the terminal variance `C²n`
  let a ← Counted.litDiv 8 eps
  let pl ← Counted.protectedLog a
  let pl2 ← Counted.pow pl 2
  let t1 ← Counted.mulLit 1024 roundness
  let t2 ← Counted.mul t1 n
  let t3 ← Counted.mul t2 pl2
  let m1 ← Counted.max n t3
  let T ← Counted.litMax 1 m1
  let rootT ← Counted.sqrt T
  -- the starting variance and the Gaussian integral
  let d ← Counted.mulLit 64 n
  let s0 ← Counted.div eps d
  let rootS0 ← Counted.sqrt s0
  let pi ← Counted.lit Real.pi
  let tp ← Counted.mulLit 2 pi
  let tps ← Counted.mul tp s0
  let lt ← Counted.log tps
  let half ← Counted.divLit n 2
  let ex ← Counted.mul lt half
  let Z ← Counted.exp ex
  -- the scale factor
  let twoN ← Counted.mulLit 2 n
  let invTwoN ← Counted.litDiv 1 twoN
  let one ← Counted.lit 1
  let c ← Counted.sub one invTwoN
  let cInv ← Counted.litDiv 1 c
  -- the schedule, run until the variance reaches `C²n`; it takes at most
  -- `⌈2n(6 + plog(n/ε))⌉ + ⌈3 C²n⌉` steps
  let ne ← Counted.div n eps
  let plne ← Counted.protectedLog ne
  let six ← Counted.lit 6
  let sl1 ← Counted.add six plne
  let sl2 ← Counted.mul twoN sl1
  let slow ← Counted.ceil sl2
  let fa1 ← Counted.mulLit 3 T
  let fast ← Counted.ceil fa1
  let fuel ← Counted.add slow fast
  let schedule ← scheduleProg n T fuel s0
  let sched := schedule.1
  let phases := schedule.2
  -- sample counts
  let e2 ← Counted.pow eps 2
  let plT ← Counted.protectedLog T
  let sc1 ← Counted.mulLit 512 plT
  let sc2 ← Counted.div sc1 e2
  let sampleN ← Counted.ceil sc2
  let fr1 ← Counted.mulLit 4096 plne
  let fr2 ← Counted.div fr1 e2
  let fixedN ← Counted.ceil fr2
  -- the error budget
  let largest ← Counted.max fixedN sampleN
  let np ← Counted.cast phases
  let tr1 ← Counted.mulLit 1024 np
  let trunc ← Counted.div tr1 e2
  let tr4 ← Counted.pow trunc 4
  let de1 ← Counted.mulLit 4096 tr4
  let de2 ← Counted.mul de1 np
  let dep ← Counted.div e2 de2
  let lr ← Counted.cast largest
  let sm1 ← Counted.mulLit 3 lr
  let sm2 ← Counted.mul sm1 np
  let sme ← Counted.div dep sm2
  let r1 ← Counted.litDiv 4 sme
  let r2 ← Counted.protectedLog r1
  let r3 ← Counted.mulLit 128 r2
  let retries ← Counted.ceil r3
  let oneN ← Counted.lit (1 : ℕ)
  let attempts ← Counted.sub retries oneN
  let ar ← Counted.cast attempts
  let ar1 ← Counted.add ar one
  let ar4 ← Counted.mulLit 4 ar1
  let blockErr ← Counted.div sme ar4
  let core ← Counted.divLit sme 768
  let radial ← Counted.divLit sme 8
  let nc ← Counted.div n core
  let plc ← Counted.protectedLog nc
  let nr ← Counted.div n radial
  let plr ← Counted.protectedLog nr
  let acc ← Counted.max plc plr
  let h ← Counted.lit (1 / 2 : ℝ)
  let eh ← Counted.exp h
  let w1 ← Counted.mulLit 4 eh
  let warm ← Counted.mul eh w1
  -- the query budget
  let mr ← Counted.litMax 1 roundness
  let n3 ← Counted.pow n 3
  let b1 ← Counted.mul mr n3
  let b2 ← Counted.div b1 e2
  let ie ← Counted.litDiv 1 eps
  let pie ← Counted.protectedLog ie
  let pie2 ← Counted.pow pie 2
  let b3 ← Counted.mul b2 pie2
  let plne2 ← Counted.pow plne 2
  let b4 ← Counted.mul b3 plne2
  let plT2 ← Counted.pow plT 2
  let base ← Counted.mul b4 plT2
  let rr1 ← Counted.mul base acc
  let ib ← Counted.litDiv 1 blockErr
  let pib ← Counted.protectedLog ib
  let pib2 ← Counted.pow pib 2
  let rate ← Counted.mul rr1 pib2
  let qb1 ← Counted.mulLit (64 * runCostConstant) rate
  let budget ← Counted.ceil qb1
  -- the number of repetitions
  let ip ← Counted.litDiv 1 p
  let pip ← Counted.protectedLog ip
  let rp ← Counted.mulLit 8 pip
  let reps ← Counted.ceil rp
  Counted.pure ⟨n, nN, T, rootT, rootS0, Z, c, cInv, sched, sampleN, fixedN, retries, acc,
    blockErr, warm, budget, reps⟩

/-- `walkRequirement` at warmness `M` and error `err`, given the proposal radius and
`√σ²`. -/
noncomputable def walkRequirementProg (dimension proposal rootSigma M err : Num ℝ) :
    Counted (Num ℝ) := do
  let lM ← Counted.log M
  let ie ← Counted.litDiv 1 err
  let li ← Counted.log ie
  let t ← Counted.mulLit 2 li
  let num ← Counted.add lM t
  let two ← Counted.lit 2
  let l2 ← Counted.log two
  let a ← Counted.mul proposal l2
  let sn ← Counted.sqrt dimension
  let b ← Counted.mulLit 640 rootSigma
  let c ← Counted.mul b sn
  let d ← Counted.div a c
  let d2 ← Counted.pow d 2
  let e ← Counted.div num d2
  let f ← Counted.mulLit 4 e
  let one ← Counted.lit 1
  Counted.add f one

/-- The constants of one phase, computed from the call's constants. -/
noncomputable def phaseConstantsProg (G : RunConstants) (sigma2 : Num ℝ) :
    Counted PhaseConstants := do
  let s ← Counted.sqrt sigma2
  let na ← Counted.mul G.dimension G.accuracyLog
  let sa ← Counted.sqrt na
  let r1 ← Counted.mulLit 32 s
  let radius ← Counted.mul r1 sa
  let one ← Counted.lit 1
  let m ← Counted.min s one
  let pd ← Counted.mulLit 4096 sa
  let proposal ← Counted.div m pd
  let M ← Counted.mulLit 16 G.warm
  let two ← Counted.lit 2
  let first ← walkRequirementProg G.dimension proposal s M G.blockError
  let retry ← walkRequirementProg G.dimension proposal s two G.blockError
  let mx ← Counted.max first retry
  let mx1 ← Counted.litMax 1 mx
  let steps ← Counted.ceil mx1
  let ws ← Counted.cast steps
  let c1 ← Counted.mulLit 2 ws
  let c2 ← Counted.mul c1 M
  let c3 ← Counted.div c2 G.blockError
  let c4 ← Counted.ceil c3
  let cap ← Counted.add G.queryBudget c4
  let small ← Counted.le sigma2 one
  let samples := if small then G.fixedRateSampleCount else G.sampleCount
  Counted.pure ⟨radius, proposal, steps, cap, samples⟩



/-! ## 1. Cost model -/

/-- **Worst-case number of membership-oracle calls** of a program.

Each membership call costs exactly `1`; random draws and arithmetic (`tick`) cost `0`.
The maximum is taken over every oracle answer and every outcome of every random
draw, so a bound on `queryCost` holds on every execution of the program. -/
noncomputable def ChargedProgram.queryCost {n : ℕ} {α : Type} :
    ChargedProgram n α → ℕ∞
  | .pure _ => 0
  | .query _ next => 1 + ⨆ answer, (next answer).queryCost
  | .randomNat _ next => ⨆ seed, (next seed).queryCost
  | .randomPoint _ _ next => ⨆ point, (next point).queryCost
  | .randomReal _ _ next => ⨆ value, (next value).queryCost
  | .tick _ next => next.queryCost

/-- **Worst-case number of arithmetic operations** of a program: the operations
tallied by its `compute` steps, each priced at `1` (`opsTotal`), maximised over every
oracle answer and every outcome of every random draw.  Membership calls are counted
separately, by `queryCost`. -/
noncomputable def ChargedProgram.opCost {n : ℕ} {α : Type} :
    ChargedProgram n α → ℕ∞
  | .pure _ => 0
  | .query _ next => ⨆ answer, (next answer).opCost
  | .randomNat _ next => ⨆ seed, (next seed).opCost
  | .randomPoint _ _ next => ⨆ point, (next point).opCost
  | .randomReal _ _ next => ⨆ value, (next value).opCost
  | .tick ops next => (opsTotal ops : ℕ∞) + next.opCost

/-! ## 2. The algorithm -/

open Arlib.Computation (Num)

variable (q : VolumeParams) (G : RunConstants)

/-! The algorithm holds every number it computes sealed (`Num`, `NumPoint`).  It reads
every number it uses from `G`, the constants of the call (`runConstantsProg`), or from
`P`, the constants of the current phase (`phaseConstantsProg`), each computed once as
counted arithmetic.  A loop whose length the algorithm computed is a `loopUntil` over the
held count. -/

/-! ### The ball walk -/

/-- **One ball-walk step** toward `N(0, σ²I)` restricted to `K`.  Propose a
uniform point `y` in a small ball around `x` and query it.  If `y` is proper
(inside the body and inside the truncation radii), move to `y` with the lazy
Metropolis probability; otherwise stay at `x`.  The flag reports whether `y`
was proper.  The proposal is built from a standard Gaussian vector and a uniform
number (`ballProposalProg`). -/
noncomputable def ballWalkStep (P : PhaseConstants) (sigma2 : Num ℝ) (x : NumPoint q.n) :
    ChargedProgram q.n (Bool × NumPoint q.n) := do
  let g ← drawPoint (standardGaussian q.n)
  let u ← drawReal uniformUnit
  let y ← compute (ballProposalProg G.dimensionCount x P.proposal g u)
  let inside ← isMember y
  let coin ← drawReal uniformUnit
  let proper ← compute (properTestProg G.rootTerminal P.radius y)
  let move ← compute (lazyTestProg sigma2 x y coin)
  if inside = true ∧ proper = true then
    pure (true, if move = true then y else x)
  else
    pure (false, x)

/-- One round of `properWalk`, with `left` proper steps still to make from `x`.  With none
left, make the endpoint membership call at the shrunk point and stop with `x`; otherwise
take a ball-walk step, and count it if it was proper. -/
noncomputable def properWalkRound (P : PhaseConstants) (sigma2 : Num ℝ) (left : Num ℕ)
    (x : NumPoint q.n) :
    ChargedProgram q.n ((Num ℕ × NumPoint q.n) ⊕ NumPoint q.n) := do
  let done ← compute (do
    let zero ← Counted.lit (0 : ℕ)
    Counted.le left zero)
  if done then do
    let y ← compute (Counted.smul G.scaleInv x)
    let _ ← isMember y
    pure (.inr x)
  else do
    let (proper, y) ← ballWalkStep q G P sigma2 x
    if proper then do
      let left' ← compute (do
        let one ← Counted.lit (1 : ℕ)
        Counted.sub left one)
      pure (.inl (left', y))
    else
      pure (.inl (left, y))

/-- **Deviation 1: walk length counted in proper steps.**  Take ball-walk steps
from `x` until `walkSteps` proper proposals have been made, and return the final
point.  Give up (`none`) once `cap` proposals have been made in total.  On
success one more membership call is made at the shrunk endpoint; its answer is
not used. -/
noncomputable def properWalk (P : PhaseConstants) (sigma2 : Num ℝ) (cap : Num ℕ)
    (x : NumPoint q.n) : ChargedProgram q.n (Option (NumPoint q.n)) := do
  let r ← loopUntil cap (fun s => properWalkRound q G P sigma2 s.1 s.2) (P.steps, x)
  pure (match r with
    | .inl _ => none
    | .inr y => some y)

/-! ### Drawing the samples of one phase -/

/-- **Deviation 2: speedy-to-target rejection.**  One attempt at turning the
walk point `x` (on the body enlarged by `c`) into a sample of `N(0, σ²I)`
restricted to `K`: shrink it to `y = x / c`, query `y`, and accept with
probability `½ · f_σ²(y) / f_{σ²/c²}(y)`. -/
noncomputable def rejectionAttempt (P : PhaseConstants) (sigma2 : Num ℝ) (x : NumPoint q.n) :
    ChargedProgram q.n (Bool × NumPoint q.n) := do
  let y ← compute (Counted.smul G.scaleInv x)
  let inside ← isMember y
  let coin ← drawReal uniformUnit
  let proper ← compute (properTestProg G.rootTerminal P.radius y)
  let accept ← compute (scaleAcceptTestProg sigma2 G.scale y coin)
  if inside = true ∧ proper = true ∧ accept = true then
    pure (true, y)
  else
    pure (false, y)

/-- One attempt at a sample: a proper-step walk from `x` (at most `walkCap` proposals)
followed by one rejection attempt.  It stops with the accepted sample and the walk's
endpoint (`inr (some _)`), or with `inr none` if the walk gave up; a rejection hands the
walk's endpoint to the next attempt (`inl`). -/
noncomputable def sampleAttempt (P : PhaseConstants) (sigma2 : Num ℝ) (walkCap : Num ℕ)
    (x : NumPoint q.n) :
    ChargedProgram q.n (NumPoint q.n ⊕ Option (NumPoint q.n × NumPoint q.n)) := do
  let some y ← properWalk q G P sigma2 walkCap x | pure (.inr none)
  let (accepted, z) ← rejectionAttempt q G P sigma2 y
  if accepted then pure (.inr (some (z, y))) else pure (.inl y)

/-- What one sample's attempts come to.  On acceptance of `z` with the walk ended at `y`,
add `weight z` to the running total and continue from `y` (`inl`); otherwise abandon the
phase (`inr`). -/
noncomputable def sampleFinish (weight : NumPoint q.n → Counted (Num ℝ)) (total : Num ℝ) :
    NumPoint q.n ⊕ Option (NumPoint q.n × NumPoint q.n) →
      ChargedProgram q.n ((Num ℝ × NumPoint q.n) ⊕ Unit)
  | .inr (some (z, y)) => do
      let w ← compute (weight z)
      let total' ← compute (Counted.add total w)
      pure (.inl (total', y))
  | .inr none => pure (.inr ())
  | .inl _ => pure (.inr ())

/-- One sample: at most `maxRetries` attempts from the current point, then
`sampleFinish`. -/
noncomputable def sampleRound (P : PhaseConstants) (sigma2 : Num ℝ)
    (weight : NumPoint q.n → Counted (Num ℝ)) (walkCap : Num ℕ)
    (state : Num ℝ × NumPoint q.n) :
    ChargedProgram q.n ((Num ℝ × NumPoint q.n) ⊕ Unit) := do
  let attempt ← loopUntil G.maxRetries (sampleAttempt q G P sigma2 walkCap) state.2
  sampleFinish q weight state.1 attempt

/-- **Draw `samples` samples and add up `weight` over them** (Figure 1:
"draw k samples X₁ … X_k").  Each sample is a proper-step walk from the
current point followed by one rejection attempt, retried from where the walk
stopped at most `maxRetries` times.  Running out of retries, or a walk giving
up, abandons the phase (`none`).  Returns the total and the last walk point. -/
noncomputable def collectSamples (P : PhaseConstants) (sigma2 : Num ℝ)
    (weight : NumPoint q.n → Counted (Num ℝ)) (samples : Num ℕ) (start : NumPoint q.n) :
    ChargedProgram q.n (Option (Num ℝ × NumPoint q.n)) := do
  let (zero, walkCap) ← compute (do
    let zero ← Counted.lit (0 : ℝ)
    let one ← Counted.lit (1 : ℕ)
    let walkCap ← Counted.add P.cap one
    Counted.pure (zero, walkCap))
  let r ← loopUntil samples (sampleRound q G P sigma2 weight walkCap) (zero, start)
  pure (match r with
    | .inl s => some s
    | .inr _ => none)

/-! ### The phases -/

/-- **One cooling phase** from variance `σ²` to `τ²`: draw
`k = phaseSampleCount q σ²` samples and return the ratio estimate
`W = (1/k) Σⱼ f_τ²(Xⱼ) / f_σ²(Xⱼ)`, together with the point the next phase
starts from.  The walk runs on the body enlarged by `c`, so the starting point
is scaled by `c` and the final point by `1/c`. -/
noncomputable def coolingPhase (sigma2 tau2 : Num ℝ) (x : NumPoint q.n) :
    ChargedProgram q.n (Option (Num ℝ × NumPoint q.n)) := do
  let P ← compute (phaseConstantsProg G sigma2)
  let start ← compute (Counted.smul G.scale x)
  let some (total, y) ← collectSamples q G P sigma2 (gaussianRatioWeightProg sigma2 tau2)
      P.samples start
    | pure none
  let W ← compute (do
    let k ← Counted.cast P.samples
    Counted.div total k)
  let z ← compute (Counted.smul G.scaleInv y)
  pure (some (W, z))

/-- **The final Gaussian-to-uniform phase** at variance `σ²`: draw
`k = sampleCount q` samples and return `U = (1/k) Σⱼ 1 / f_σ²(Xⱼ)`. -/
noncomputable def uniformPhase (sigma2 : Num ℝ) (x : NumPoint q.n) :
    ChargedProgram q.n (Option (Num ℝ)) := do
  let P ← compute (phaseConstantsProg G sigma2)
  let start ← compute (Counted.smul G.scale x)
  let some (total, _) ← collectSamples q G P sigma2 (uniformRatioWeightProg sigma2)
      G.sampleCount start
    | pure none
  let U ← compute (do
    let k ← Counted.cast G.sampleCount
    Counted.div total k)
  pure (some U)

/-- **The starting point**: a point of `N(0, σ₀²I)`, `σ₀ · g` for a standard
Gaussian vector `g`, and one membership call.  The run is abandoned (`none`) if the
point is outside the body or outside the truncation radius. -/
noncomputable def initialSample :
    ChargedProgram q.n (Option (NumPoint q.n)) := do
  let g ← drawPoint (standardGaussian q.n)
  let x ← compute (gaussianStartProg G.rootInitial g)
  let inside ← isMember x
  let near ← compute (do
    let nx ← Counted.norm x
    Counted.le nx G.rootTerminal)
  pure (if inside = true ∧ near = true then some x else none)

/-- **The cooling loop**: run `coolingPhase` for each consecutive pair of
variances in the list, each phase starting where the previous one stopped, and
multiply the ratio estimates. -/
noncomputable def coolingPhases :
    List (Num ℝ) → NumPoint q.n →
      ChargedProgram q.n (Option (Num ℝ × NumPoint q.n))
  | sigma2 :: tau2 :: rest, x => do
      let s ← compute (Counted.cell sigma2)
      let t ← compute (Counted.cell tau2)
      let some (W, y) ← coolingPhase q G s t x | pure none
      let some (product, z) ← coolingPhases (tau2 :: rest) y | pure none
      let P ← compute (Counted.mul W product)
      pure (some (P, z))
  | _, x => do
      let one ← compute (Counted.lit (1 : ℝ))
      pure (some (one, x))

/-! ### One run, and the median of independent runs -/

/-- **One run of Figure 1**: starting point, the cooling phases along the
schedule `coolingSchedule q`, the final Gaussian-to-uniform phase,
and the product with the known Gaussian integral `(2πσ₀²)^{n/2}`.  A failed
step makes the run report `0`. -/
noncomputable def figureOneRun : ChargedProgram q.n (Num ℝ) := do
  let some x₀ ← initialSample q G | compute (Counted.lit 0)
  let some (product, x) ← coolingPhases q G G.schedule x₀ | compute (Counted.lit 0)
  let some U ← uniformPhase q G G.terminal x | compute (Counted.lit 0)
  compute (do
    let a ← Counted.mul G.gaussianIntegral product
    Counted.mul a U)

/-- Run a program with a budget of `budget` membership calls.  A call beyond
the budget stops the program with result `none`; random draws use no budget. -/
noncomputable def ChargedProgram.withQueryCap
    {n : ℕ} {Result : Type} :
    ℕ → ChargedProgram n Result →
      ChargedProgram n (Option Result)
  | _, .pure result => .pure (some result)
  | 0, .query _ _ => .pure none
  | budget + 1, .query point next =>
      .query point fun answer => withQueryCap budget (next answer)
  | budget, .randomNat law next =>
      .randomNat law fun seed => withQueryCap budget (next seed)
  | budget, .randomPoint law hprob next =>
      .randomPoint law hprob fun point => withQueryCap budget (next point)
  | budget, .randomReal law hprob next =>
      .randomReal law hprob fun value => withQueryCap budget (next value)
  | budget, .tick ops next => .tick ops (withQueryCap budget next)

open Arlib.Computation in
/-- Run a program with a held budget of membership calls, at the price of one
`NumOp.loop`: the budget bounds the program's queries as a loop count bounds its rounds,
and, like a loop count, it is consumed and never handed to the program. -/
noncomputable def ChargedProgram.withHeldQueryCap {n : ℕ} {Result : Type}
    (budget : Num ℕ) (p : ChargedProgram n Result) :
    ChargedProgram n (Option Result) :=
  .tick (CostVec.one (numOpcode Op .loop)) (p.withQueryCap budget.get)

/-- **Answering the queries with a charged membership routine.**  `p.answerWith member`
is `p` with every membership query `x` replaced by running the arithmetic `member x` and
continuing with its answer.  A caller that can decide membership by computation (for a
polytope, by checking its facets) runs the same program this way: the queries are gone,
and their arithmetic is tallied like any other `compute` step. -/
noncomputable def ChargedProgram.answerWith {n : ℕ} {Result : Type}
    (member : AmbientSpace n → Counted Bool) :
    ChargedProgram n Result → ChargedProgram n Result
  | .pure result => .pure result
  | .query point next =>
      .tick (member point).tally (answerWith member (next (member point).value))
  | .randomNat law next => .randomNat law fun seed => answerWith member (next seed)
  | .randomPoint law hprob next =>
      .randomPoint law hprob fun point => answerWith member (next point)
  | .randomReal law hprob next =>
      .randomReal law hprob fun value => answerWith member (next value)
  | .tick ops next => .tick ops (answerWith member next)

/-- **Deviation 3: global query budget.**  One run of Figure 1, stopped and
reporting `0` if it would exceed `queryBudget q`
membership calls. -/
noncomputable def cappedRun : ChargedProgram q.n (Num ℝ) := do
  let result ← (figureOneRun q G).withHeldQueryCap G.queryBudget
  match result with
  | some estimate => pure estimate
  | none => compute (Counted.lit 0)

/-- `count` independent runs of `run`, in order. -/
noncomputable def repeatIndependently {n : ℕ} (count : Num ℕ)
    (run : ChargedProgram n (Num ℝ)) :
    ChargedProgram n (List (Num ℝ)) := do
  let r ← loopUntil (γ := Empty) count
    (fun estimates => do
      let x ← run
      let estimates' ← compute (Counted.push estimates x)
      pure (.inl estimates'))
    []
  pure (match r with
    | .inl estimates => estimates
    | .inr e => e.elim)

/-- **The CV18 volume algorithm**: the median of `confidenceRepetitions q`
independent capped runs of Figure 1.  This is the program Theorem 1.1 is
about. -/
noncomputable def cv18Program : ChargedVolumeAlgorithm := fun q => do
  let G ← compute (runConstantsProg q)
  let estimates ← repeatIndependently G.repetitions (cappedRun q G)
  let m ← compute (Counted.median G.repetitions estimates)
  report m

#sealedProgram cv18Program


end ttc.ChargedCV18
