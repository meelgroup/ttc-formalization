/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Model.Operations
import ttc.Model.Prelude
import ttc.Meta.CostSeal
import ttc.Meta.ModelClosure
import ArlibCommunity.Algorithms.CV18.Model.Prelude

/-!
# The TTC program, sealed

Algorithm `ttc` as a charged program.  Every number it computes is a sealed `Num`, computed
by arlib's charged operations; its only randomness is the sealed tape of
`Model/Operations.lean`, read through the program monad `M`.  `#ttcProgramSeal` checks that
nothing in it computes for free.

* **The arithmetic** (`A`): arlib's `Num` operations, and the vectors, dot products, norms
  and medians written with them.
* **CV18** (`cv18`): ported from the charged CV18 tree (`Analysis/ChargedCV18/Program.lean`)
  to `M`.  A membership call runs a charged membership routine supplied by the caller —
  TTC decides membership in a polytope by arithmetic on its facets (`allFacets`) — and
  spends one call of CV18's query cap, which ends the run (`failure`) when exhausted.
* **The sampler** (`hitAndRunStep`, `roundPoint`, `sampleUntilAccepted`): the lazy
  Hit-and-Run walk with exact chords from the facets, KV97 rounding, and rejection.
* **Algorithm `ttc`** (`estimator`): `GetPrecision`, then for each component CV18, the
  deletion pass, the rate check, the Poisson draw, the halving loop, and the samples.

The input is each component's facets and the results of the linear programs
(`ComponentInput`, `Model/Prelude.lean`), read in at one literal per number.

The two unbounded loops (the halving loop and the retries for an accepted sample) take a
number of rounds `fuel`, and stop the run (`failure`) when it runs out; `Model/Run.lean`
runs the program with the least fuel that finishes.
-/
set_option autoImplicit false

noncomputable section

namespace ttc.Program

open Arlib.Computation (Num Charged CostVec)
open ttc.Model.Operations
open ArlibCommunity.Algorithms.CV18 (runCostConstant)

/-! ## The program monad -/

/-- A program step: it reads and moves the oracle (the tape, and CV18's query cap), may
stop early (`failure`), and is charged. -/
abbrev M (n : ℕ) := OptionT (StateT (Oracle n) Prog)

/-- Run charged arithmetic as a program step. -/
def run {n : ℕ} {α : Type} (c : Prog α) : M n α :=
  OptionT.lift (StateT.lift c)

/-- An oracle operation as a program step. -/
def withOracle {n : ℕ} {α : Type} (f : Oracle n → Prog (α × Oracle n)) : M n α :=
  OptionT.lift (StateT.mk f)

/-- A standard Gaussian vector from the tape. -/
def gaussian {n : ℕ} : M n (NumPoint n) := withOracle drawGaussian

/-- A uniform number in `[0, 1]` from the tape. -/
def unit {n : ℕ} : M n (Num ℝ) := withOracle drawUnit

/-- A fair coin from the tape. -/
def coin {n : ℕ} : M n Bool := withOracle drawCoin

/-- A Poisson number of rate `rate` from the tape. -/
def poisson {n : ℕ} (rate : Num ℝ) : M n (Num ℕ) := withOracle (drawPoisson rate)

/-- Set CV18's query cap to the held count `b`. -/
def queryCap {n : ℕ} (b : Num ℕ) : M n Unit := withOracle (setBudget b)

/-- **A membership call of CV18**: spend one call of the query cap (stopping the run if it
is exhausted), then decide membership by the charged routine `member`. -/
def isMember {n : ℕ} (member : NumPoint n → Prog Bool) (x : NumPoint n) : M n Bool := do
  let ok ← withOracle spendQuery
  if ok then run (member x) else failure

/-- **A loop whose length is a held number**, at the price of one `NumOp.loop` plus what
its rounds spend (arlib's `Num.iterateWhile`): run `body` from `init` until it stops
(`inr`), at most `count` times; `inl` is the state when the rounds run out.  A round that
stops the run stops the loop with it. -/
def loopUntil {n : ℕ} {β γ : Type} (count : Num ℕ) (body : β → M n (β ⊕ γ)) (init : β) :
    M n (β ⊕ γ) :=
  OptionT.mk (StateT.mk fun o =>
    Num.iterateWhile (κ := Op) (κₛ := Cell)
      (fun _ (s : Option (β ⊕ γ) × Oracle n) => match s with
        | (some (.inl b), o) => do
            let r ← ((body b).run).run o
            pure (some r)
        | _ => pure none)
      count (some (.inl init), o))

/-! ## Arithmetic on sealed numbers

Each primitive is one of arlib's `Num` operations: `+`, `−`, `·`, `/`, a comparison,
`max`, `min`, `⌈·⌉` and a literal are `NumOp`s; `ℕ → ℝ`, `√`, `exp`, `log` and `u^{1/k}`
are `RealOp`s. -/

namespace A

/-- Return `a` without spending anything. -/
def pure {α : Type} (a : α) : Prog α := Charged.pure a

/-- A constant from outside the sealed world (an input, a parameter, a literal): one
`NumOp.lit`. -/
def lit {α : Type} (a : α) : Prog (Num α) := Num.lit a

/-- Append one list cell: one `cell`. -/
def push {α : Type} (xs : List α) (x : α) : Prog (List α) := ttc.Model.Operations.push xs x

/-- Read one list cell: one `cell`. -/
def cell {α : Type} (a : α) : Prog α := ttc.Model.Operations.cell a

def add {α : Type} [Add α] (x y : Num α) : Prog (Num α) := Num.add x y
def sub {α : Type} [Sub α] (x y : Num α) : Prog (Num α) := Num.sub x y
def mul {α : Type} [Mul α] (x y : Num α) : Prog (Num α) := Num.mul x y
def div {α : Type} [Div α] (x y : Num α) : Prog (Num α) := Num.div x y
def max {α : Type} [Max α] (x y : Num α) : Prog (Num α) := Num.max x y
def min {α : Type} [Min α] (x y : Num α) : Prog (Num α) := Num.min x y
def le {α : Type} [LE α] [DecidableLE α] (x y : Num α) : Prog Bool := Num.le x y

/-- The test `x < y`, asked as `¬ (y ≤ x)`: one `NumOp.cmp`. -/
def lt {α : Type} [LinearOrder α] (x y : Num α) : Prog Bool := do
  let b ← Num.le y x
  pure (!b)

noncomputable def ceil (x : Num ℝ) : Prog (Num ℕ) := Num.ceil x
def cast (k : Num ℕ) : Prog (Num ℝ) := Num.cast k
noncomputable def sqrt (x : Num ℝ) : Prog (Num ℝ) := Num.sqrt x
noncomputable def log (x : Num ℝ) : Prog (Num ℝ) := Num.log x
noncomputable def exp (x : Num ℝ) : Prog (Num ℝ) := Num.exp x
noncomputable def root (u : Num ℝ) (k : Num ℕ) : Prog (Num ℝ) := Num.root u k

def pow (x : Num ℝ) : ℕ → Prog (Num ℝ)
  | 0 => lit 1
  | k + 1 => do
      let y ← pow x k
      mul y x

/-- **A loop over a held count that can stop early**: run `f` on the state at most `n`
times, stopping as soon as it returns `none`; one `NumOp.loop` plus what the rounds spend
(arlib's `Num.iterateWhile`). -/
def iterateWhile {β : Type} (f : β → Prog (Option β)) (n : Num ℕ) (b : β) : Prog β :=
  Num.iterateWhile (fun _ b => f b) n b

/-- Compute each coordinate `f i` of a vector, one after another; the costs add. -/
def forEach {α : Type} : {n : ℕ} → (Fin n → Prog α) → Prog (Fin n → α)
  | 0, _ => pure Fin.elim0
  | _ + 1, f => do
      let first ← f 0
      let rest ← forEach fun i => f i.succ
      pure (Fin.cons first rest)

/-- The dot product `a₀x₀ + ⋯ + aₙ₋₁xₙ₋₁`: `n` multiplications and `n − 1` additions. -/
def dot : (n : ℕ) → NumPoint n → NumPoint n → Prog (Num ℝ)
  | 0, _, _ => lit 0
  | 1, a, x => mul (a 0) (x 0)
  | n + 2, a, x => do
      let first ← mul (a 0) (x 0)
      let rest ← dot (n + 1) (Fin.tail a) (Fin.tail x)
      add first rest

/-- `‖x‖² = x₀² + ⋯ + xₙ₋₁²`: a dot product, `2n − 1` operations. -/
def normSq {n : ℕ} (x : NumPoint n) : Prog (Num ℝ) := dot n x x

/-- `‖x‖ = √(‖x‖²)`: `2n` operations. -/
noncomputable def norm {n : ℕ} (x : NumPoint n) : Prog (Num ℝ) := do
  let s ← normSq x
  sqrt s

/-- The scaled vector `a • x`: one multiplication per coordinate. -/
def smul {n : ℕ} (a : Num ℝ) (x : NumPoint n) : Prog (NumPoint n) :=
  forEach fun i => mul a (x i)

/-- The vector sum `x + y`: one addition per coordinate. -/
def addVec {n : ℕ} (x y : NumPoint n) : Prog (NumPoint n) :=
  forEach fun i => add (x i) (y i)

/-- The sum `a₀ + ⋯ + aₘ₋₁` of a non-empty list of held natural numbers: one addition
fewer than its length. -/
def sumList : List (Num ℕ) → Prog (Num ℕ)
  | [] => lit 0
  | [a] => A.pure a
  | a :: b :: rest => do
      let r ← sumList (b :: rest)
      add a r

/-- The first entry whose flag is set, or `0` if there is none. -/
def firstPassing : List (Num ℝ × Bool) → Prog (Num ℝ)
  | [] => lit 0
  | e :: rest => if e.2 then A.pure e.1 else firstPassing rest

/-- The median of the held numbers `v`, of which there are `m`: the entry of rank
`⌊m/2⌋`, by comparison counting.  Each entry is read from the list once (`|v|` cells);
then for each entry `vᵢ`, count the entries below `vᵢ` and those at most `vᵢ` (`2|v|`
comparisons and `2(|v| − 1)` additions), and test whether rank `⌊m/2⌋` falls between the
two counts (two comparisons).  Return the first entry that passes. -/
noncomputable def median (m : Num ℕ) (v : List (Num ℝ)) : Prog (Num ℝ) := do
  let w ← v.mapM cell
  let zero ← lit (0 : ℕ)
  let one ← lit (1 : ℕ)
  let two ← lit (2 : ℕ)
  let rank ← div m two
  let passes ← w.mapM fun wi => do
    let fb ← w.mapM fun wj => lt wj wi
    let below ← sumList (fb.map fun f => if f then one else zero)
    let fa ← w.mapM fun wj => le wj wi
    let atMost ← sumList (fa.map fun f => if f then one else zero)
    let a ← le below rank
    let b ← lt rank atMost
    A.pure (wi, a && b)
  firstPassing passes

/-- `protectedLog x = max 1 (log x)`: three operations. -/
noncomputable def protectedLog (x : Num ℝ) : Prog (Num ℝ) := do
  let l ← log x
  let one ← lit 1
  max one l

/-- A uniform point of the unit ball from a standard Gaussian vector `g` and a uniform
`u ∈ [0, 1]`: `(u^{1/n} / ‖g‖) · g`, where `dim` holds `n`. -/
noncomputable def ballStart {n : ℕ} (dim : Num ℕ) (g : NumPoint n) (u : Num ℝ) :
    Prog (NumPoint n) := do
  let sq ← normSq g
  let len ← sqrt sq
  let radius ← root u dim
  let scale ← div radius len
  smul scale g

/-- The Gaussian log-weight `−‖x‖²/(2s)` at variance `s`: `2n + 4` operations. -/
noncomputable def gaussianLogWeight {n : ℕ} (s : Num ℝ) (x : NumPoint n) :
    Prog (Num ℝ) := do
  let a ← normSq x
  let two ← lit 2
  let t ← mul two s
  let d ← div a t
  let zero ← lit 0
  sub zero d

end A

/-! ## CV18

### The tests and weights
-/

open Arlib.Computation (Num)

/-- The proper-proposal test `‖y‖ ≤ rootT ∧ ‖y‖ ≤ radius`. -/
noncomputable def properTestProg {n : ℕ} (rootT radius : Num ℝ) (y : NumPoint n) :
    Prog Bool := do
  let ny ← A.norm y
  let a ← A.le ny rootT
  let b ← A.le ny radius
  A.pure (a && b)

/-- The lazy Metropolis test `coin ≤ lazyAcceptance sigma2 x y`. -/
noncomputable def lazyTestProg {n : ℕ} (sigma2 : Num ℝ) (x y : NumPoint n) (coin : Num ℝ) :
    Prog Bool := do
  let ly ← A.gaussianLogWeight sigma2 y
  let lx ← A.gaussianLogWeight sigma2 x
  let ey ← A.exp ly
  let ex ← A.exp lx
  let r ← A.div ey ex
  let one ← A.lit 1
  let m ← A.min one r
  let two ← A.lit 2
  let h ← A.div m two
  A.le coin h

/-- The speedy-to-target acceptance test
`coin ≤ ½ · e^{−‖y‖²/(2σ²)} / e^{−‖y‖²/(2σ²/c²)}`. -/
noncomputable def scaleAcceptTestProg {n : ℕ} (sigma2 c : Num ℝ) (y : NumPoint n)
    (coin : Num ℝ) : Prog Bool := do
  let cc ← A.mul c c
  let v ← A.div sigma2 cc
  let a ← A.gaussianLogWeight sigma2 y
  let b ← A.gaussianLogWeight v y
  let ea ← A.exp a
  let eb ← A.exp b
  let r ← A.div ea eb
  let two ← A.lit 2
  let h ← A.div r two
  A.le coin h

/-- The estimator weight `gaussianRatioWeight sigma2 tau2 x`. -/
noncomputable def gaussianRatioWeightProg {n : ℕ} (sigma2 tau2 : Num ℝ) (x : NumPoint n) :
    Prog (Num ℝ) := do
  let a ← A.gaussianLogWeight tau2 x
  let b ← A.gaussianLogWeight sigma2 x
  let ea ← A.exp a
  let eb ← A.exp b
  A.div ea eb

/-- The estimator weight `uniformRatioWeight sigma2 x = e^{‖x‖²/(2σ²)}`. -/
noncomputable def uniformRatioWeightProg {n : ℕ} (sigma2 : Num ℝ) (x : NumPoint n) :
    Prog (Num ℝ) := do
  let a ← A.normSq x
  let two ← A.lit 2
  let t ← A.mul two sigma2
  let d ← A.div a t
  A.exp d

/-- The ball-walk proposal: a uniform point of the ball of radius `radius` around `x`,
`x + radius · ballStart g u`, from a standard Gaussian vector `g` and a uniform `u`;
`dim` holds the dimension. -/
noncomputable def ballProposalProg {n : ℕ} (dim : Num ℕ) (x : NumPoint n) (radius : Num ℝ)
    (g : NumPoint n) (u : Num ℝ) : Prog (NumPoint n) := do
  let p ← A.ballStart dim g u
  let s ← A.smul radius p
  A.addVec x s

/-- The starting point: a Gaussian of variance `variance` per coordinate, `√variance · g`,
from a standard Gaussian vector `g`. -/
noncomputable def gaussianStartProg {n : ℕ} (rootVariance : Num ℝ) (g : NumPoint n) :
    Prog (NumPoint n) :=
  A.smul rootVariance g

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

namespace A

/-- `c · x` for a constant `c` of the program text: a literal and a multiplication. -/
def mulLit (c : ℝ) (x : Num ℝ) : Prog (Num ℝ) := do
  let k ← lit c
  mul k x

/-- `x / c` for a constant `c` of the program text: a literal and a division. -/
noncomputable def divLit (x : Num ℝ) (c : ℝ) : Prog (Num ℝ) := do
  let k ← lit c
  div x k

/-- `c / x` for a constant `c` of the program text: a literal and a division. -/
noncomputable def litDiv (c : ℝ) (x : Num ℝ) : Prog (Num ℝ) := do
  let k ← lit c
  div k x

/-- `max c x` for a constant `c` of the program text: a literal and a `max`. -/
def litMax (c : ℝ) (x : Num ℝ) : Prog (Num ℝ) := do
  let k ← lit c
  max k x

end A

/-- One step of the cooling schedule, `nextVariance`. -/
noncomputable def nextVarianceProg (dimension terminal sigma2 : Num ℝ) :
    Prog (Num ℝ) := do
  let one ← A.lit 1
  let small ← A.le sigma2 one
  let rate ← if small then (do
      let a ← A.litDiv 1 dimension
      A.add one a)
    else (do
      let b ← A.mulLit 2 terminal
      let c ← A.div sigma2 b
      A.add one c)
  let m ← A.mul sigma2 rate
  A.min terminal m

/-- One round of the schedule loop: stop once the variance `s` reaches `terminal`,
otherwise record it, take one `nextVariance` step, and count it. -/
noncomputable def scheduleRound (dimension terminal : Num ℝ) (one : Num ℕ)
    (st : List (Num ℝ) × Num ℝ × Num ℕ) : Prog (Option (List (Num ℝ) × Num ℝ × Num ℕ)) := do
  let stop ← A.le terminal st.2.1
  if stop then A.pure none else do
    let next ← nextVarianceProg dimension terminal st.2.1
    let count' ← A.add st.2.2 one
    let done ← A.push st.1 st.2.1
    A.pure (some (done, next, count'))

/-- The cooling schedule from `sigma2` on, and its length: stop once the variance
reaches `terminal`, otherwise take one more `nextVariance` step, for at most `fuel` steps
(a held count; the loop stops on its test). -/
noncomputable def scheduleProg (dimension terminal : Num ℝ) (fuel : Num ℕ) (sigma2 : Num ℝ) :
    Prog (List (Num ℝ) × Num ℕ) := do
  let one ← A.lit (1 : ℕ)
  let r ← A.iterateWhile (scheduleRound dimension terminal one) fuel ([], sigma2, one)
  let schedule ← A.push r.1 r.2.1
  A.pure (schedule, r.2.2)

/-- The constants of one call, computed. -/
noncomputable def runConstantsProg (d : ℕ) (eps roundness p : Num ℝ) :
    Prog RunConstants := do
  -- the parameters: the dimension is read in; the accuracy `eps`, the confidence `p`
  -- and the roundness are held numbers the caller computed
  let nN ← A.lit d
  let n ← A.cast nN
  -- the terminal variance `C²n`
  let a ← A.litDiv 8 eps
  let pl ← A.protectedLog a
  let pl2 ← A.pow pl 2
  let t1 ← A.mulLit 1024 roundness
  let t2 ← A.mul t1 n
  let t3 ← A.mul t2 pl2
  let m1 ← A.max n t3
  let T ← A.litMax 1 m1
  let rootT ← A.sqrt T
  -- the starting variance and the Gaussian integral
  let d ← A.mulLit 64 n
  let s0 ← A.div eps d
  let rootS0 ← A.sqrt s0
  let pi ← A.lit Real.pi
  let tp ← A.mulLit 2 pi
  let tps ← A.mul tp s0
  let lt ← A.log tps
  let half ← A.divLit n 2
  let ex ← A.mul lt half
  let Z ← A.exp ex
  -- the scale factor
  let twoN ← A.mulLit 2 n
  let invTwoN ← A.litDiv 1 twoN
  let one ← A.lit 1
  let c ← A.sub one invTwoN
  let cInv ← A.litDiv 1 c
  -- the schedule, run until the variance reaches `C²n`; it takes at most
  -- `⌈2n(6 + plog(n/ε))⌉ + ⌈3 C²n⌉` steps
  let ne ← A.div n eps
  let plne ← A.protectedLog ne
  let six ← A.lit 6
  let sl1 ← A.add six plne
  let sl2 ← A.mul twoN sl1
  let slow ← A.ceil sl2
  let fa1 ← A.mulLit 3 T
  let fast ← A.ceil fa1
  let fuel ← A.add slow fast
  let schedule ← scheduleProg n T fuel s0
  let sched := schedule.1
  let phases := schedule.2
  -- sample counts
  let e2 ← A.pow eps 2
  let plT ← A.protectedLog T
  let sc1 ← A.mulLit 512 plT
  let sc2 ← A.div sc1 e2
  let sampleN ← A.ceil sc2
  let fr1 ← A.mulLit 4096 plne
  let fr2 ← A.div fr1 e2
  let fixedN ← A.ceil fr2
  -- the error budget
  let largest ← A.max fixedN sampleN
  let np ← A.cast phases
  let tr1 ← A.mulLit 1024 np
  let trunc ← A.div tr1 e2
  let tr4 ← A.pow trunc 4
  let de1 ← A.mulLit 4096 tr4
  let de2 ← A.mul de1 np
  let dep ← A.div e2 de2
  let lr ← A.cast largest
  let sm1 ← A.mulLit 3 lr
  let sm2 ← A.mul sm1 np
  let sme ← A.div dep sm2
  let r1 ← A.litDiv 4 sme
  let r2 ← A.protectedLog r1
  let r3 ← A.mulLit 128 r2
  let retries ← A.ceil r3
  let oneN ← A.lit (1 : ℕ)
  let attempts ← A.sub retries oneN
  let ar ← A.cast attempts
  let ar1 ← A.add ar one
  let ar4 ← A.mulLit 4 ar1
  let blockErr ← A.div sme ar4
  let core ← A.divLit sme 768
  let radial ← A.divLit sme 8
  let nc ← A.div n core
  let plc ← A.protectedLog nc
  let nr ← A.div n radial
  let plr ← A.protectedLog nr
  let acc ← A.max plc plr
  let h ← A.lit (1 / 2 : ℝ)
  let eh ← A.exp h
  let w1 ← A.mulLit 4 eh
  let warm ← A.mul eh w1
  -- the query budget
  let mr ← A.litMax 1 roundness
  let n3 ← A.pow n 3
  let b1 ← A.mul mr n3
  let b2 ← A.div b1 e2
  let ie ← A.litDiv 1 eps
  let pie ← A.protectedLog ie
  let pie2 ← A.pow pie 2
  let b3 ← A.mul b2 pie2
  let plne2 ← A.pow plne 2
  let b4 ← A.mul b3 plne2
  let plT2 ← A.pow plT 2
  let base ← A.mul b4 plT2
  let rr1 ← A.mul base acc
  let ib ← A.litDiv 1 blockErr
  let pib ← A.protectedLog ib
  let pib2 ← A.pow pib 2
  let rate ← A.mul rr1 pib2
  let qb1 ← A.mulLit (64 * runCostConstant) rate
  let budget ← A.ceil qb1
  -- the number of repetitions
  let ip ← A.litDiv 1 p
  let pip ← A.protectedLog ip
  let rp ← A.mulLit 8 pip
  let reps ← A.ceil rp
  A.pure ⟨n, nN, T, rootT, rootS0, Z, c, cInv, sched, sampleN, fixedN, retries, acc,
    blockErr, warm, budget, reps⟩

/-- `walkRequirement` at warmness `M` and error `err`, given the proposal radius and
`√σ²`. -/
noncomputable def walkRequirementProg (dimension proposal rootSigma M err : Num ℝ) :
    Prog (Num ℝ) := do
  let lM ← A.log M
  let ie ← A.litDiv 1 err
  let li ← A.log ie
  let t ← A.mulLit 2 li
  let num ← A.add lM t
  let two ← A.lit 2
  let l2 ← A.log two
  let a ← A.mul proposal l2
  let sn ← A.sqrt dimension
  let b ← A.mulLit 640 rootSigma
  let c ← A.mul b sn
  let d ← A.div a c
  let d2 ← A.pow d 2
  let e ← A.div num d2
  let f ← A.mulLit 4 e
  let one ← A.lit 1
  A.add f one

/-- The constants of one phase, computed from the call's constants. -/
noncomputable def phaseConstantsProg (G : RunConstants) (sigma2 : Num ℝ) :
    Prog PhaseConstants := do
  let s ← A.sqrt sigma2
  let na ← A.mul G.dimension G.accuracyLog
  let sa ← A.sqrt na
  let r1 ← A.mulLit 32 s
  let radius ← A.mul r1 sa
  let one ← A.lit 1
  let m ← A.min s one
  let pd ← A.mulLit 4096 sa
  let proposal ← A.div m pd
  let M ← A.mulLit 16 G.warm
  let two ← A.lit 2
  let first ← walkRequirementProg G.dimension proposal s M G.blockError
  let retry ← walkRequirementProg G.dimension proposal s two G.blockError
  let mx ← A.max first retry
  let mx1 ← A.litMax 1 mx
  let steps ← A.ceil mx1
  let ws ← A.cast steps
  let c1 ← A.mulLit 2 ws
  let c2 ← A.mul c1 M
  let c3 ← A.div c2 G.blockError
  let c4 ← A.ceil c3
  let cap ← A.add G.queryBudget c4
  let small ← A.le sigma2 one
  let samples := if small then G.fixedRateSampleCount else G.sampleCount
  A.pure ⟨radius, proposal, steps, cap, samples⟩



variable (d : ℕ) (G : RunConstants) (member : NumPoint d → Prog Bool)

/-! ### The ball walk -/

/-- **One ball-walk step** toward `N(0, σ²I)` restricted to `K`.  Propose a
uniform point `y` in a small ball around `x` and query it.  If `y` is proper
(inside the body and inside the truncation radii), move to `y` with the lazy
Metropolis probability; otherwise stay at `x`.  The flag reports whether `y`
was proper.  The proposal is built from a standard Gaussian vector and a uniform
number (`ballProposalProg`). -/
noncomputable def ballWalkStep (P : PhaseConstants) (sigma2 : Num ℝ) (x : NumPoint d) :
    M d (Bool × NumPoint d) := do
  let g ← gaussian
  let u ← unit
  let y ← run (ballProposalProg G.dimensionCount x P.proposal g u)
  let inside ← isMember member y
  let coin ← unit
  let proper ← run (properTestProg G.rootTerminal P.radius y)
  let move ← run (lazyTestProg sigma2 x y coin)
  if inside = true ∧ proper = true then
    pure (true, if move = true then y else x)
  else
    pure (false, x)

/-- One round of `properWalk`, with `left` proper steps still to make from `x`.  With none
left, make the endpoint membership call at the shrunk point and stop with `x`; otherwise
take a ball-walk step, and count it if it was proper. -/
noncomputable def properWalkRound (P : PhaseConstants) (sigma2 : Num ℝ) (left : Num ℕ)
    (x : NumPoint d) :
    M d ((Num ℕ × NumPoint d) ⊕ NumPoint d) := do
  let done ← run (do
    let zero ← A.lit (0 : ℕ)
    A.le left zero)
  if done then do
    let y ← run (A.smul G.scaleInv x)
    let _ ← isMember member y
    pure (.inr x)
  else do
    let (proper, y) ← ballWalkStep d G member P sigma2 x
    if proper then do
      let left' ← run (do
        let one ← A.lit (1 : ℕ)
        A.sub left one)
      pure (.inl (left', y))
    else
      pure (.inl (left, y))

/-- **Deviation 1: walk length counted in proper steps.**  Take ball-walk steps
from `x` until `walkSteps` proper proposals have been made, and return the final
point.  Give up (`none`) once `cap` proposals have been made in total.  On
success one more membership call is made at the shrunk endpoint; its answer is
not used. -/
noncomputable def properWalk (P : PhaseConstants) (sigma2 : Num ℝ) (cap : Num ℕ)
    (x : NumPoint d) : M d (Option (NumPoint d)) := do
  let r ← loopUntil cap (fun s => properWalkRound d G member P sigma2 s.1 s.2) (P.steps, x)
  pure (match r with
    | .inl _ => none
    | .inr y => some y)

/-! ### Drawing the samples of one phase -/

/-- **Deviation 2: speedy-to-target rejection.**  One attempt at turning the
walk point `x` (on the body enlarged by `c`) into a sample of `N(0, σ²I)`
restricted to `K`: shrink it to `y = x / c`, query `y`, and accept with
probability `½ · f_σ²(y) / f_{σ²/c²}(y)`. -/
noncomputable def rejectionAttempt (P : PhaseConstants) (sigma2 : Num ℝ) (x : NumPoint d) :
    M d (Bool × NumPoint d) := do
  let y ← run (A.smul G.scaleInv x)
  let inside ← isMember member y
  let coin ← unit
  let proper ← run (properTestProg G.rootTerminal P.radius y)
  let accept ← run (scaleAcceptTestProg sigma2 G.scale y coin)
  if inside = true ∧ proper = true ∧ accept = true then
    pure (true, y)
  else
    pure (false, y)

/-- One attempt at a sample: a proper-step walk from `x` (at most `walkCap` proposals)
followed by one rejection attempt.  It stops with the accepted sample and the walk's
endpoint (`inr (some _)`), or with `inr none` if the walk gave up; a rejection hands the
walk's endpoint to the next attempt (`inl`). -/
noncomputable def sampleAttempt (P : PhaseConstants) (sigma2 : Num ℝ) (walkCap : Num ℕ)
    (x : NumPoint d) :
    M d (NumPoint d ⊕ Option (NumPoint d × NumPoint d)) := do
  let some y ← properWalk d G member P sigma2 walkCap x | pure (.inr none)
  let (accepted, z) ← rejectionAttempt d G member P sigma2 y
  if accepted then pure (.inr (some (z, y))) else pure (.inl y)

/-- What one sample's attempts come to.  On acceptance of `z` with the walk ended at `y`,
add `weight z` to the running total and continue from `y` (`inl`); otherwise abandon the
phase (`inr`). -/
noncomputable def sampleFinish (weight : NumPoint d → Prog (Num ℝ)) (total : Num ℝ) :
    NumPoint d ⊕ Option (NumPoint d × NumPoint d) →
      M d ((Num ℝ × NumPoint d) ⊕ Unit)
  | .inr (some (z, y)) => do
      let w ← run (weight z)
      let total' ← run (A.add total w)
      pure (.inl (total', y))
  | .inr none => pure (.inr ())
  | .inl _ => pure (.inr ())

/-- One sample: at most `maxRetries` attempts from the current point, then
`sampleFinish`. -/
noncomputable def sampleRound (P : PhaseConstants) (sigma2 : Num ℝ)
    (weight : NumPoint d → Prog (Num ℝ)) (walkCap : Num ℕ)
    (state : Num ℝ × NumPoint d) :
    M d ((Num ℝ × NumPoint d) ⊕ Unit) := do
  let attempt ← loopUntil G.maxRetries (sampleAttempt d G member P sigma2 walkCap) state.2
  sampleFinish d weight state.1 attempt

/-- **Draw `samples` samples and add up `weight` over them** (Figure 1:
"draw k samples X₁ … X_k").  Each sample is a proper-step walk from the
current point followed by one rejection attempt, retried from where the walk
stopped at most `maxRetries` times.  Running out of retries, or a walk giving
up, abandons the phase (`none`).  Returns the total and the last walk point. -/
noncomputable def collectSamples (P : PhaseConstants) (sigma2 : Num ℝ)
    (weight : NumPoint d → Prog (Num ℝ)) (samples : Num ℕ) (start : NumPoint d) :
    M d (Option (Num ℝ × NumPoint d)) := do
  let (zero, walkCap) ← run (do
    let zero ← A.lit (0 : ℝ)
    let one ← A.lit (1 : ℕ)
    let walkCap ← A.add P.cap one
    A.pure (zero, walkCap))
  let r ← loopUntil samples (sampleRound d G member P sigma2 weight walkCap) (zero, start)
  pure (match r with
    | .inl s => some s
    | .inr _ => none)

/-! ### The phases -/

/-- **One cooling phase** from variance `σ²` to `τ²`: draw
`k = phaseSampleCount q σ²` samples and return the ratio estimate
`W = (1/k) Σⱼ f_τ²(Xⱼ) / f_σ²(Xⱼ)`, together with the point the next phase
starts from.  The walk runs on the body enlarged by `c`, so the starting point
is scaled by `c` and the final point by `1/c`. -/
noncomputable def coolingPhase (sigma2 tau2 : Num ℝ) (x : NumPoint d) :
    M d (Option (Num ℝ × NumPoint d)) := do
  let P ← run (phaseConstantsProg G sigma2)
  let start ← run (A.smul G.scale x)
  let some (total, y) ← collectSamples d G member P sigma2 (gaussianRatioWeightProg sigma2 tau2)
      P.samples start
    | pure none
  let W ← run (do
    let k ← A.cast P.samples
    A.div total k)
  let z ← run (A.smul G.scaleInv y)
  pure (some (W, z))

/-- **The final Gaussian-to-uniform phase** at variance `σ²`: draw
`k = sampleCount q` samples and return `U = (1/k) Σⱼ 1 / f_σ²(Xⱼ)`. -/
noncomputable def uniformPhase (sigma2 : Num ℝ) (x : NumPoint d) :
    M d (Option (Num ℝ)) := do
  let P ← run (phaseConstantsProg G sigma2)
  let start ← run (A.smul G.scale x)
  let some (total, _) ← collectSamples d G member P sigma2 (uniformRatioWeightProg sigma2)
      G.sampleCount start
    | pure none
  let U ← run (do
    let k ← A.cast G.sampleCount
    A.div total k)
  pure (some U)

/-- **The starting point**: a point of `N(0, σ₀²I)`, `σ₀ · g` for a standard
Gaussian vector `g`, and one membership call.  The run is abandoned (`none`) if the
point is outside the body or outside the truncation radius. -/
noncomputable def initialSample :
    M d (Option (NumPoint d)) := do
  let g ← gaussian
  let x ← run (gaussianStartProg G.rootInitial g)
  let inside ← isMember member x
  let near ← run (do
    let nx ← A.norm x
    A.le nx G.rootTerminal)
  pure (if inside = true ∧ near = true then some x else none)

/-- **The cooling loop**: run `coolingPhase` for each consecutive pair of
variances in the list, each phase starting where the previous one stopped, and
multiply the ratio estimates. -/
noncomputable def coolingPhases :
    List (Num ℝ) → NumPoint d →
      M d (Option (Num ℝ × NumPoint d))
  | sigma2 :: tau2 :: rest, x => do
      let s ← run (A.cell sigma2)
      let t ← run (A.cell tau2)
      let some (W, y) ← coolingPhase d G member s t x | pure none
      let some (product, z) ← coolingPhases (tau2 :: rest) y | pure none
      let P ← run (A.mul W product)
      pure (some (P, z))
  | _, x => do
      let one ← run (A.lit (1 : ℝ))
      pure (some (one, x))

/-! ### One run, and the median of independent runs -/

/-- **One run of Figure 1**: starting point, the cooling phases along the
schedule `coolingSchedule q`, the final Gaussian-to-uniform phase,
and the product with the known Gaussian integral `(2πσ₀²)^{n/2}`.  A failed
step makes the run report `0`. -/
noncomputable def figureOneRun : M d (Num ℝ) := do
  let some x₀ ← initialSample d G member | run (A.lit 0)
  let some (product, x) ← coolingPhases d G member G.schedule x₀ | run (A.lit 0)
  let some U ← uniformPhase d G member G.terminal x | run (A.lit 0)
  run (do
    let a ← A.mul G.gaussianIntegral product
    A.mul a U)

/-- **Deviation 3: global query budget.**  One run of Figure 1, stopped and
reporting `0` if it would exceed `queryBudget q`
membership calls. -/
noncomputable def cappedRun : M d (Num ℝ) := do
  queryCap G.queryBudget
  (figureOneRun d G member) <|> run (A.lit 0)

/-- `count` independent runs of `run`, in order. -/
noncomputable def repeatIndependently {n : ℕ} (count : Num ℕ)
    (body : M n (Num ℝ)) :
    M n (List (Num ℝ)) := do
  let r ← loopUntil (γ := Empty) count
    (fun estimates => do
      let x ← body
      let estimates' ← run (A.push estimates x)
      pure (.inl estimates'))
    []
  pure (match r with
    | .inl estimates => estimates
    | .inr e => e.elim)

/-- **The CV18 volume algorithm**: the median of `confidenceRepetitions q`
independent capped runs of Figure 1.  This is the program Theorem 1.1 is
about. -/
noncomputable def cv18 (eps roundness p : Num ℝ) : M d (Num ℝ) := do
  let G ← run (runConstantsProg d eps roundness p)
  let estimates ← repeatIndependently G.repetitions (cappedRun d G member)
  run (A.median G.repetitions estimates)



/-! ## TTC

### A component in the sealed world -/

/-- A component read into the sealed world: its facets and its LP results, every number
held.  The facet count `facets` is the length of the input, not a number the program
computes with. -/
structure Loaded (d : ℕ) where
  facets : ℕ
  normal : Fin facets → NumPoint d
  offset : Fin facets → Num ℝ
  inradius : Num ℝ
  incenter : NumPoint d
  boundingRadius : Num ℝ
  /-- The facet count `r`, as a real number. -/
  facetReal : Num ℝ

/-- **Read a component**: one literal per number it is given. -/
noncomputable def load {d : ℕ} (c : ComponentInput d) : Prog (Loaded d) := do
  let normal ← A.forEach fun j => A.forEach fun i => A.lit (c.normal j i)
  let offset ← A.forEach fun j => A.lit (c.offset j)
  let inradius ← A.lit c.inradius
  let incenter ← A.forEach fun i => A.lit (c.incenter i)
  let boundingRadius ← A.lit c.boundingRadius
  let r ← A.lit c.facetCount
  let facetReal ← A.cast r
  A.pure ⟨c.facetCount, normal, offset, inradius, incenter, boundingRadius, facetReal⟩

/-- **The membership test** `aⱼ · x ≤ bⱼ` for every facet `j = 0, …, r − 1`, one facet
after another: `2 d r` operations. -/
def allFacets {d : ℕ} : (r : ℕ) → (Fin r → NumPoint d) → (Fin r → Num ℝ) → NumPoint d →
    Prog Bool
  | 0, _, _, _ => A.pure true
  | r + 1, a, b, x => do
      let s ← A.dot d (a 0) x
      let ok ← A.le s (b 0)
      let rest ← allFacets r (Fin.tail a) (Fin.tail b) x
      A.pure (ok && rest)

/-- `10^b` for a held exponent `b`: `exp (b · log 10)`. -/
noncomputable def pow10 (b : Num ℕ) : Prog (Num ℝ) := do
  let bR ← A.cast b
  let ten ← A.lit (10 : ℝ)
  let l ← A.log ten
  let e ← A.mul bR l
  A.exp e

/-- `a^k` for a held positive base `a` and a held exponent `k`: `exp (k · log a)`. -/
noncomputable def powHeld (a : Num ℝ) (k : Num ℕ) : Prog (Num ℝ) := do
  let kR ← A.cast k
  let l ← A.log a
  let e ← A.mul kR l
  A.exp e

/-- The offsets of `scale · P`: `scale · bⱼ` for each facet. -/
def scaledOffsets {d : ℕ} (L : Loaded d) (scale : Num ℝ) : Prog (Fin L.facets → Num ℝ) :=
  A.forEach fun j => A.mul scale (L.offset j)

/-- The offsets of CV18's normalized body `(P − z)/γ`: `(bⱼ − aⱼ · z)/γ` for each facet. -/
def cv18Offsets {d : ℕ} (L : Loaded d) : Prog (Fin L.facets → Num ℝ) :=
  A.forEach fun j => do
    let az ← A.dot d (L.normal j) L.incenter
    let slack ← A.sub (L.offset j) az
    A.div slack L.inradius

/-! ### `GetPrecision` (Algorithm `getprec`) -/

/-- The inball size `(64 m n / η) √(log (4 r_tot / η))` the lattice comparison asks of
every component, for `m` components with `r_tot` facets in all. -/
noncomputable def latticeRadiusProg (m dim totalFacets eta : Num ℝ) : Prog (Num ℝ) := do
  let a ← A.mulLit 64 m
  let b ← A.mul a dim
  let c ← A.div b eta
  let f ← A.mulLit 4 totalFacets
  let g ← A.div f eta
  let l ← A.log g
  let s ← A.sqrt l
  A.mul c s

/-- **`GetPrecision`**: `⌈log₁₀ maxratio⌉` with `maxratio = max (1, maxᵢ γ / γᵢ)`. -/
noncomputable def getPrecision {d : ℕ} (required : Num ℝ) (Ls : List (Loaded d)) :
    Prog (Num ℕ) := do
  let one ← A.lit (1 : ℝ)
  let maxratio ← Ls.foldlM (fun acc L => do
      let ratio ← A.div required L.inradius
      A.max acc ratio) one
  let l ← A.log maxratio
  let ten ← A.lit (10 : ℝ)
  let l10 ← A.log ten
  let q ← A.div l l10
  A.ceil q

/-! ### `GenerateSamples`: Hit-and-Run, rounding and rejection -/

/-- The direction `g/‖g‖`. -/
noncomputable def normalize {d : ℕ} (g : NumPoint d) : Prog (NumPoint d) := do
  let len ← A.norm g
  let one ← A.lit (1 : ℝ)
  let inv ← A.div one len
  A.smul inv g

/-- Where the line `x + tθ` crosses the facet `a · y ≤ β`: at `t = (β − a·x)/(a·θ)`, a
lower endpoint if `a·θ < 0`, an upper one if `a·θ > 0`; `none` is no endpoint on that
side. -/
noncomputable def facetEndpoints {d : ℕ} (a : NumPoint d) (β : Num ℝ) (x θ : NumPoint d) :
    Prog (Option (Num ℝ) × Option (Num ℝ)) := do
  let c ← A.dot d a θ
  let ax ← A.dot d a x
  let slack ← A.sub β ax
  let q ← A.div slack c
  let zero ← A.lit (0 : ℝ)
  let neg ← A.lt c zero
  let pos ← A.lt zero c
  A.pure (if neg then some q else none, if pos then some q else none)

/-- The larger of two lower endpoints; `none` is `−∞`. -/
def maxEnd : Option (Num ℝ) → Option (Num ℝ) → Prog (Option (Num ℝ))
  | some x, some y => do
      let z ← A.max x y
      A.pure (some z)
  | some x, none => A.pure (some x)
  | none, y => A.pure y

/-- The smaller of two upper endpoints; `none` is `+∞`. -/
def minEnd : Option (Num ℝ) → Option (Num ℝ) → Prog (Option (Num ℝ))
  | some x, some y => do
      let z ← A.min x y
      A.pure (some z)
  | some x, none => A.pure (some x)
  | none, y => A.pure y

/-- The chord `{x + tθ} ∩ P = [lo, hi]`: the largest lower and the smallest upper endpoint
over all facets. -/
noncomputable def chord {d : ℕ} : (r : ℕ) → (Fin r → NumPoint d) → (Fin r → Num ℝ) →
    NumPoint d → NumPoint d → Prog (Option (Num ℝ) × Option (Num ℝ))
  | 0, _, _, _, _ => A.pure (none, none)
  | r + 1, a, β, x, θ => do
      let first ← facetEndpoints (a 0) (β 0) x θ
      let rest ← chord r (Fin.tail a) (Fin.tail β) x θ
      let lo ← maxEnd first.1 rest.1
      let hi ← minEnd first.2 rest.2
      A.pure (lo, hi)

/-- **One lazy Hit-and-Run step** from `x` in the polytope with facets `a`, offsets `β`:
a fair coin keeps `x`; otherwise take the direction `θ = g/‖g‖` of a Gaussian vector `g`,
find the chord through `x`, and move to a uniform point of it. -/
noncomputable def hitAndRunStep {d : ℕ} (r : ℕ) (a : Fin r → NumPoint d) (β : Fin r → Num ℝ)
    (x : NumPoint d) : M d (NumPoint d) := do
  let stay ← coin
  if stay then pure x else do
    let g ← gaussian
    let θ ← run (normalize g)
    let ends ← run (chord r a β x θ)
    match ends with
    | (some lo, some hi) => do
        let ok ← run (A.lt lo hi)
        if ok then do
          let u ← unit
          run (do
            let width ← A.sub hi lo
            let shift ← A.mul u width
            let t ← A.add lo shift
            A.forEach fun i => do
              let step ← A.mul t (θ i)
              A.add (x i) step)
        else pure x
    | _ => pure x

/-- `steps` Hit-and-Run steps from `x`. -/
noncomputable def hitAndRunWalk {d : ℕ} (r : ℕ) (a : Fin r → NumPoint d) (β : Fin r → Num ℝ)
    (steps : Num ℕ) (x : NumPoint d) : M d (NumPoint d) := do
  let res ← loopUntil (γ := Empty) steps (fun y => do
      let y' ← hitAndRunStep r a β y
      pure (.inl y')) x
  pure (match res with
    | .inl y => y
    | .inr e => e.elim)

/-- The rounding of `roundPoint`, coordinate by coordinate. -/
noncomputable def roundCoords {d : ℕ} (one : Num ℤ) :
    (k : ℕ) → (Fin k → Num ℝ) → M d (Fin k → Num ℤ)
  | 0, _ => pure Fin.elim0
  | k + 1, q => do
      let v ← unit
      let z ← run (do
        let fl ← floor (q 0)
        let flR ← intCast fl
        let frac ← A.sub (q 0) flR
        let up ← A.lt v frac
        if up then A.add fl one else A.pure fl)
      let rest ← roundCoords one k (Fin.tail q)
      pure (Fin.cons z rest)

/-- **KV97 rounding**: coordinate `pᵢ` becomes `⌊pᵢ⌋ + 1` with probability `pᵢ − ⌊pᵢ⌋`
and `⌊pᵢ⌋` otherwise, from a uniform number of the tape.  The result is held by its
integer coordinates. -/
noncomputable def roundPoint {d : ℕ} (p : NumPoint d) : M d (Fin d → Num ℤ) := do
  let one ← run (A.lit (1 : ℤ))
  roundCoords one d p

/-- A lattice point held by its integer coordinates, as a point: one cast per
coordinate. -/
def latticeReal {d : ℕ} (z : Fin d → Num ℤ) : Prog (NumPoint d) :=
  A.forEach fun i => intCast (z i)

/-- The membership test of a lattice point in `10^b · P` (offsets `scaled`). -/
def latticeMember {d : ℕ} (L : Loaded d) (scaled : Fin L.facets → Num ℝ)
    (z : Fin d → Num ℤ) : Prog Bool := do
  let x ← latticeReal z
  allFacets L.facets L.normal scaled x

/-- The walk's constants for a component at precision scale `scale = 10^b` and accuracy
`η`: the walk body's offsets `(10^b bⱼ + κ ‖aⱼ‖ − aⱼ · z')/γ'` in the chart where the
scaled inball `B(z', γ')` is the unit ball, the chart `(γ', z')`, and the walk length
`T = ⌈C n³ (R'₀/γ')² log (2R'₀)⌉` with `R'₀ = (1 + κ/γ') · 10^b R₀`. -/
structure WalkConstants (d r : ℕ) where
  offsets : Fin r → Num ℝ
  scaledInradius : Num ℝ
  scaledIncenter : NumPoint d
  steps : Num ℕ

/-- The walk's constants, computed. -/
noncomputable def walkConstantsProg {d : ℕ} (L : Loaded d) (scale eta dim : Num ℝ) :
    Prog (WalkConstants d L.facets) := do
  -- the KV97 inflation `κ = √(2 log (4/(η/4))) + √(2 log r)`
  let e ← A.divLit eta 4
  let q ← A.litDiv 4 e
  let lq ← A.log q
  let lq2 ← A.mulLit 2 lq
  let c ← A.sqrt lq2
  let lr ← A.log L.facetReal
  let lr2 ← A.mulLit 2 lr
  let sr ← A.sqrt lr2
  let κ ← A.add c sr
  -- the scaled inball
  let γ' ← A.mul scale L.inradius
  let z' ← A.smul scale L.incenter
  let offsets ← A.forEach fun j => do
    let sb ← A.mul scale (L.offset j)
    let aa ← A.normSq (L.normal j)
    let na ← A.sqrt aa
    let infl ← A.mul κ na
    let bj ← A.add sb infl
    let az ← A.dot d (L.normal j) z'
    let slack ← A.sub bj az
    A.div slack γ'
  -- the walk length
  let one ← A.lit (1 : ℝ)
  let kg ← A.div κ γ'
  let k1 ← A.add one kg
  let sR ← A.mul scale L.boundingRadius
  let R' ← A.mul k1 sR
  let ratio ← A.div R' γ'
  let ratio2 ← A.pow ratio 2
  let n3 ← A.pow dim 3
  let t1 ← A.mulLit ((2 : ℝ) ^ 68) n3
  let t2 ← A.mul t1 ratio2
  let twoR ← A.mulLit 2 R'
  let lg ← A.log twoR
  let t3 ← A.mul t2 lg
  let steps ← A.ceil t3
  A.pure ⟨offsets, γ', z', steps⟩

/-- **One attempt at a sample**: a start point uniform in the unit ball, the walk, the
chart back to `10^b · P'`, rounding, and the membership test of the rounded point in
`10^b · P` (offsets `scaled`). -/
noncomputable def sampleTry {d : ℕ} (L : Loaded d) (W : WalkConstants d L.facets)
    (scaled : Fin L.facets → Num ℝ) (dimN : Num ℕ) : M d (Option (Fin d → Num ℤ)) := do
  let g ← gaussian
  let u ← unit
  let y₀ ← run (A.ballStart dimN g u)
  let y ← hitAndRunWalk L.facets L.normal W.offsets W.steps y₀
  let p ← run (A.forEach fun i => do
    let s ← A.mul W.scaledInradius (y i)
    A.add s (W.scaledIncenter i))
  let z ← roundPoint p
  let ok ← run (latticeMember L scaled z)
  pure (if ok then some z else none)

/-- **One accepted sample**: attempts until one is accepted.  The loop is unbounded; it is
run with `fuel` rounds, and stops the run (`failure`) when they run out (`Model/Run.lean`
gives it enough). -/
noncomputable def sampleUntilAccepted {d : ℕ} (L : Loaded d) (W : WalkConstants d L.facets)
    (scaled : Fin L.facets → Num ℝ) (dimN : Num ℕ) : ℕ → M d (Fin d → Num ℤ)
  | 0 => failure
  | fuel + 1 => do
      let r ← sampleTry L W scaled dimN
      match r with
      | some z => pure z
      | none => sampleUntilAccepted L W scaled dimN fuel

/-! ### The state of the algorithm -/

/-- The state of Algorithm `ttc`: the probability `p`, the retained lattice points `X`
(each held by its integer coordinates in the decimal-scaled frame), and `|X|`. -/
structure State (d : ℕ) where
  p : Num ℝ
  X : List (Fin d → Num ℤ)
  size : Num ℕ

/-- Keep the copies for which `keep` says so, counting them. -/
noncomputable def filterCopies {d : ℕ} (keep : (Fin d → Num ℤ) → M d Bool)
    (X : List (Fin d → Num ℤ)) : M d (List (Fin d → Num ℤ) × Num ℕ) := do
  let zero ← run (A.lit (0 : ℕ))
  let one ← run (A.lit (1 : ℕ))
  X.foldlM (fun (acc : List (Fin d → Num ℤ) × Num ℕ) x => do
      let x ← run (A.cell x)
      let k ← keep x
      if k then do
        let ys ← run (A.push acc.1 x)
        let c ← run (A.add acc.2 one)
        pure (ys, c)
      else pure acc) ([], zero)

/-- The parameters of the run, held. -/
structure Params where
  /-- `ε' = ε / 12`. -/
  epsPrime : Num ℝ
  /-- `δ' = δ / (4m)`. -/
  deltaPrime : Num ℝ
  /-- `Thresh`. -/
  thresh : Num ℝ
  /-- The dimension, as a real and as a count. -/
  dim : Num ℝ
  dimN : Num ℕ
  /-- `10^b` and `10^{bn}`. -/
  scale : Num ℝ
  scaleN : Num ℝ

/-- **The halving loop** `while Nᵢ + |X| > Thresh`: halve `X`, `Nᵢ ← Binomial(Nᵢ, 1/2)`,
`p ← p / 2`.  The loop is unbounded; it is run with `fuel` rounds, and stops the run
(`failure`) when they run out. -/
noncomputable def halve {d : ℕ} (K : Params) : ℕ → Num ℝ → List (Fin d → Num ℤ) → Num ℕ →
    Num ℕ → M d (Num ℝ × List (Fin d → Num ℤ) × Num ℕ × Num ℕ)
  | 0, _, _, _, _ => failure
  | f + 1, p, X, size, N => do
      let stop ← run (do
        let total ← A.add size N
        let totalR ← A.cast total
        A.le totalR K.thresh)
      if stop then pure (p, X, size, N) else do
        let (X', size') ← filterCopies (fun _ => coin) X
        let N' ← withOracle (drawBinomialHalf N)
        let p' ← run (A.divLit p 2)
        halve K f p' X' size' N'

/-- CV18's parameters, as the step computes them. -/
noncomputable def cv18ParamsProg {d : ℕ} (K : Params) (L : Loaded d) : Prog (Num ℝ × Num ℝ × Num ℝ) := do
  let epsC ← A.divLit K.epsPrime 2
  let pC ← A.divLit K.deltaPrime 2
  let rg ← A.div L.boundingRadius L.inradius
  let m ← A.litMax 1 rg
  let m2 ← A.pow m 2
  let roundness ← A.div m2 K.dim
  A.pure (epsC, pC, roundness)

/-- The scaled volume `t = 10^{bn} · γⁿ · max 0 v`, as the step computes it. -/
noncomputable def tProg {d : ℕ} (K : Params) (L : Loaded d) (v : Num ℝ) : Prog (Num ℝ) := do
  let zero ← A.lit (0 : ℝ)
  let v' ← A.max zero v
  let γn ← powHeld L.inradius K.dimN
  let vol ← A.mul γn v'
  A.mul K.scaleN vol

/-- **One iteration of the `for` loop** on the component `L`. -/
noncomputable def step {d : ℕ} (fuel : ℕ) (K : Params) (L : Loaded d) (s : State d) :
    M d (State d) := do
  -- `t ← 10^{bn} · ComputeVolume(Kᵢ, ε', δ')`: CV18 on `(P − z)/γ`, rescaled by `γⁿ`
  let off' ← run (cv18Offsets L)
  let (epsC, pC, roundness) ← run (cv18ParamsProg K L)
  let v ← cv18 d (allFacets L.facets L.normal off') epsC roundness pC
  let t ← run (tProg K L v)
  -- remove from `X` every point of `Pᵢ`, by the membership test in `10^b · Pᵢ`
  let scaled ← run (scaledOffsets L K.scale)
  let (X, size) ← filterCopies (fun x => do
      let inside ← run (latticeMember L scaled x)
      pure (!inside)) s.X
  -- `if t p ≥ Thresh`: `k ← ⌈log₂ (t p / Thresh)⌉`, `p ← p · 2^{-k}`, keep each point with
  -- probability `2^{-k}`
  let tp ← run (A.mul t s.p)
  let big ← run (A.le K.thresh tp)
  let (p, X, size) ← (if big then (do
      let (p', keepProb) ← run (do
        let ratio ← A.div tp K.thresh
        let lr ← A.log ratio
        let two ← A.lit (2 : ℝ)
        let l2 ← A.log two
        let kR ← A.div lr l2
        let k ← A.ceil kR
        let twoK ← powHeld two k
        let p' ← A.div s.p twoK
        let one ← A.lit (1 : ℝ)
        let keepProb ← A.div one twoK
        A.pure (p', keepProb))
      let (X', size') ← filterCopies (fun _ => do
          let u ← unit
          run (A.lt u keepProb)) X
      pure (p', X', size'))
    else pure (s.p, X, size))
  -- `Nᵢ ← Poisson(t · p)`
  let rate ← run (A.mul t p)
  let N ← poisson rate
  -- `while Nᵢ + |X| > Thresh`: halve `X`, `Nᵢ ← Binomial(Nᵢ, 1/2)`, `p ← p / 2`
  let (p, X, size, N) ← halve K fuel p X size N
  -- `S ← GenerateSamples(Kᵢ, Nᵢ, b, ε')`; `X.Append(S)`
  let W ← run (walkConstantsProg L K.scale K.epsPrime K.dim)
  let res ← loopUntil (γ := Empty) N (fun (acc : List (Fin d → Num ℤ) × Num ℕ) => do
      let z ← sampleUntilAccepted L W scaled K.dimN fuel
      let ys ← run (A.push acc.1 z)
      let c ← run (do
        let one ← A.lit (1 : ℕ)
        A.add acc.2 one)
      pure (.inl (ys, c))) (X, size)
  let (X, size) := match res with
    | .inl r => r
    | .inr e => e.elim
  pure ⟨p, X, size⟩

/-- The parameters of the run, computed (as in `estimator`). -/
noncomputable def paramsProg {d : ℕ} (cs : List (ComponentInput d)) (Ls : List (Loaded d)) (eps delta : ℝ) :
    Prog Params := do
  let dimN ← A.lit d
  let dim ← A.cast dimN
  let zero ← A.lit (0 : ℕ)
  let one ← A.lit (1 : ℕ)
  let (mN, rTot) ← cs.foldlM (fun (acc : Num ℕ × Num ℕ) c => do
      let m' ← A.add acc.1 one
      let r ← A.lit c.facetCount
      let t' ← A.add acc.2 r
      A.pure (m', t')) (zero, zero)
  let m ← A.cast mN
  let rTotR ← A.cast rTot
  let eps ← A.lit eps
  let delta ← A.lit delta
  let epsPrime ← A.divLit eps 12
  let m4 ← A.mulLit 4 m
  let deltaPrime ← A.div delta m4
  let a1 ← A.litDiv 24 delta
  let a2 ← A.log a1
  let a3 ← A.mulLit 24 a2
  let one ← A.lit (1 : ℝ)
  let b1 ← A.sub one epsPrime
  let b2 ← A.pow epsPrime 2
  let b3 ← A.mul b1 b2
  let first ← A.div a3 b3
  let c1 ← A.litDiv 6 delta
  let c2 ← A.log c1
  let c3 ← A.log m
  let c4 ← A.add c2 c3
  let second ← A.mulLit 15 c4
  let thresh ← A.max first second
  let eta ← A.divLit eps 96
  let required ← latticeRadiusProg m dim rTotR eta
  let b ← getPrecision required Ls
  let scale ← pow10 b
  let bn ← A.mul b dimN
  let scaleN ← pow10 bn
  A.pure (⟨epsPrime, deltaPrime, thresh, dim, dimN, scale, scaleN⟩ : Params)

/-- **Algorithm `ttc`** on the components `cs` with accuracy `ε` and confidence `δ`, its
unbounded loops run with `fuel` rounds.  Output `|X| / (p · 10^{bn})`. -/
noncomputable def estimator {d : ℕ} (fuel : ℕ) (cs : List (ComponentInput d)) (eps delta : ℝ) :
    M d (Num ℝ) := do
  match cs with
  | [] => run (A.lit (0 : ℝ))
  | _ :: _ => do
    let Ls ← run (cs.mapM load)
    let K ← run (paramsProg cs Ls eps delta)
    -- `p ← Thresh`, `X ← ∅`
    let zero ← run (A.lit (0 : ℕ))
    let final ← Ls.foldlM (fun s L => step fuel K L s) (⟨K.thresh, [], zero⟩ : State d)
    run (do
      let size ← A.cast final.size
      let den ← A.mul final.p K.scaleN
      A.div size den)

end ttc.Program

end

#ttcProgramSeal ttc.Program
#ttcExecutableModule ttc.Model.Program
