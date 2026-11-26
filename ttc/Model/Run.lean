/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Model.Program
import ttc.Model.Prelude
import Mathlib.Probability.ProductMeasure

/-!
# Running the sealed TTC program

* `roundLaw`, `tapeLaw` — the random tape: independent rounds, each a fair coin, a
  standard Gaussian vector and a uniform number in `[0, 1]`.
* `componentsOf` — the program's input: each component's facets, and the results of the
  linear programs `MaxInscribedBall` and `BoundingRadius` (computed by preprocessing, not
  by the program).
* `execution` — the program run on a tape with `fuel` rounds for its unbounded loops.
* `fuelNeeded` — the least fuel with which the run finishes; the run of Algorithm `ttc` on
  a tape is the run with that fuel.  More fuel changes nothing once the run finishes.
* `estimate` — the output law; `operations` — the operation count of the run on a tape.
-/

set_option autoImplicit false

noncomputable section

namespace ttc.SealedRun

open MeasureTheory
open Arlib.Computation (Num Charged)
open ttc.Model.Operations

/-- One round of the tape: a fair coin, a standard Gaussian vector and a uniform number in
`[0, 1]`, independent. -/
def roundLaw (n : ℕ) : Measure (Round n) :=
  fairCoinLaw.prod ((ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))).prod
    (volume.restrict (Set.Icc (0 : ℝ) 1)))

/-- The random tape: independent rounds. -/
def tapeLaw (n : ℕ) : Measure (Tape n) := Measure.infinitePi fun _ => roundLaw n

/-- A component as the program receives it: its facets, the Chebyshev centre and radius,
and the bounding radius. -/
def componentInput {n : ℕ} (P : PolytopeData n) : ComponentInput n where
  facetCount := P.presentation.facetCount
  normal := P.presentation.normal
  offset := P.presentation.offset
  inradius := P.inradius
  incenter := P.incenter
  boundingRadius := P.BoundingRadius

/-- The program's input: the components of the decomposition, in order. -/
def componentsOf {n k : ℕ} {F : LRAFormula n k} (D : Decomposition F) :
    List (ComponentInput n) :=
  List.ofFn fun i => componentInput (D.component i)

/-- **The run on a tape**, with `fuel` rounds for the unbounded loops: the output (`none`
if the fuel ran out) and the oracle at the end, as a charged computation. -/
def execution {n : ℕ} (fuel : ℕ) (cs : List (ComponentInput n)) (eps delta : ℝ)
    (t : Tape n) : Prog (Option (Num ℝ) × Oracle n) :=
  ((ttc.Program.estimator fuel cs eps delta).run).run (Oracle.ofTape t)

/-- The run finishes with `fuel` rounds. -/
def Finishes {n : ℕ} (fuel : ℕ) (cs : List (ComponentInput n)) (eps delta : ℝ)
    (t : Tape n) : Prop :=
  ((execution fuel cs eps delta t).val.1).isSome

/-- The least fuel with which the run finishes (`0` on the null set of tapes on which it
never does). -/
def fuelNeeded {n : ℕ} (cs : List (ComponentInput n)) (eps delta : ℝ) (t : Tape n) : ℕ :=
  sInf {f | Finishes f cs eps delta t}

/-- **The run of Algorithm `ttc` on a tape**: the run with the fuel it needs. -/
def runOn {n : ℕ} (cs : List (ComponentInput n)) (eps delta : ℝ) (t : Tape n) :
    Prog (Option (Num ℝ) × Oracle n) :=
  execution (fuelNeeded cs eps delta t) cs eps delta t

/-- The output on a tape. -/
def output {n : ℕ} (cs : List (ComponentInput n)) (eps delta : ℝ) (t : Tape n) : NNReal :=
  match (runOn cs eps delta t).val.1 with
  | some x => Real.toNNReal x.get
  | none => 0

/-- The operations the run spends on a tape, each priced at `1`. -/
def operations {n : ℕ} (cs : List (ComponentInput n)) (eps delta : ℝ) (t : Tape n) : ℕ :=
  opsTotal (Charged.cost (runOn cs eps delta t))

/-- **The output law of Algorithm `ttc`** on a formula, through its preprocessing. -/
def estimate {n k : ℕ} (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (params : ApproxParams) (prep : TTCPreprocessor n k) : Measure NNReal :=
  (tapeLaw n).map (output (componentsOf (prep.run F hbounded)) params.epsilon params.delta)

/-- **The expected operation count** of Algorithm `ttc` on a formula. -/
def expectedOperations {n k : ℕ} (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F)) (params : ApproxParams)
    (prep : TTCPreprocessor n k) : ENNReal :=
  ∫⁻ t, (operations (componentsOf (prep.run F hbounded)) params.epsilon params.delta t : ENNReal)
    ∂(tapeLaw n)

end ttc.SealedRun
