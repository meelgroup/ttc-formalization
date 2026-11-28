import ttc.Analysis.MembershipCost
import ttc.Analysis.LegacyRun
import ttc.Analysis.ChebyshevCenter

/-!
# The reference parametrisation of `ttc`

Algorithm `ttc` (`Model/Program.lean`) starts from `p = Thresh`, scales volumes by
`10^{bn}` only, and outputs `|X| / (p · 10^{bn})`. The analysis below is written in the
equivalent normalisation `p = 1`, `t = Thresh · 10^{bn} · v`, output
`|X| / (p · Thresh · 10^{bn})`, in which every reachable rate is a dyadic `2^{-level}`. The
rate check of lines `line:check-threshold`–`line:final-remove` is written here as the
first-exit loop "halve while `t p / 2^r > Thresh`", whose exit round is the paper's
`k = ⌈log₂ (t p / Thresh)⌉`.

The two programs make the same random choices: `TTCSimulation.lean` proves that the
algorithm's state is this reference state with `p` multiplied by `Thresh`, so that their
output laws, and their charged output laws, coincide.

Nothing here is part of the audited statement surface.
-/

noncomputable section

open scoped ENNReal NNReal ProbabilityTheory unitInterval
open MeasureTheory

namespace ttc

/-- The reference start `p = 1`, `X = ∅`. -/
def TTCState.unitInitial (n : Nat) : TTCState n where
  p := 1
  X := ∅
  nextLabel := 0

/-- The reference scaled volume `Thresh · 10^{bn} · v`. -/
def ttcReference.t (b n : Nat) (Thresh : Real) (volumeEstimate : NNReal) : NNReal :=
  Real.toNNReal Thresh * (10 : NNReal) ^ (b * n) * volumeEstimate

/-- The number of halvings of the rate check: the least `r` with `t p / 2^r ≤ Thresh`. -/
def ttcReference.firstLoopExit {n : Nat} (s : TTCState n) (t : NNReal)
    (Thresh : Real) : Nat :=
  sInf {rounds : Nat |
    ((t * s.p / (2 : NNReal) ^ rounds : NNReal) : Real) ≤ Thresh}

/-- The state after the rate check. -/
def ttcReference.firstLoopResult {n : Nat} (s : TTCState n)
    (t : NNReal) (Thresh : Real) (coins : Nat × Nat → Bool) : TTCState n :=
  let rounds := ttcReference.firstLoopExit s t Thresh
  { p := s.p / (2 : NNReal) ^ rounds
    X := samplesAfter coins rounds s.X
    nextLabel := s.nextLabel }

/-- The rate check. -/
def ttcReference.firstLoop {n : Nat} (s : TTCState n)
    (t : NNReal) (Thresh : Real) : Measure (TTCState n) :=
  fairCoinStreamLaw.map (ttcReference.firstLoopResult s t Thresh)

/-- The reference output `|X| / (p · Thresh · 10^{bn})`. -/
def EstReference {n : Nat} (b : Nat) (Thresh : Real)
    (s : TTCState n) : NNReal :=
  (s.X.card : NNReal) /
    (s.p * Real.toNNReal Thresh * (10 : NNReal) ^ (b * n))

/-- One reference iteration of the `for` loop. -/
def ttcReference.step {n k : Nat} (O : TTCOracles n k) (b : Nat)
    (ε' δ' Thresh : Real) (P : PolytopeData n)
    (state : TTCState n) : Measure (TTCState n) :=
  (O.ComputeVolume P ε' δ').bind fun volumeOutcome =>
    let t := ttcReference.t b n Thresh volumeOutcome.2
    let withoutDuplicates := state.removeComponent P
    (ttcReference.firstLoop withoutDuplicates t Thresh).bind fun firstThinned =>
      (Poisson (t * firstThinned.p)).bind fun N =>
        (ttcPseudocode.secondLoop firstThinned N Thresh).bind fun secondThinned =>
          (O.GenerateSamples P secondThinned.2 b ε').map fun S =>
            secondThinned.1.addBatch S

/-- The reference `for` loop. -/
def ttcReference.loop {n k : Nat} (O : TTCOracles n k) (b : Nat)
    (ε' δ' Thresh : Real) :
    List (PolytopeData n) → TTCState n → Measure (TTCState n)
  | [], state => Measure.dirac state
  | P :: rest, state =>
      (ttcReference.step O b ε' δ' Thresh P state).bind
        (ttcReference.loop O b ε' δ' Thresh rest)

/-- The reference run. -/
def ttcReference {n k : Nat} (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F)) (params : ApproxParams)
    (O : TTCOracles n k) : Measure NNReal :=
  let D := O.preprocessing.run F hbounded
  if D.componentCount = 0 then
    Measure.dirac 0
  else
    let b := O.choosePrecision D params
    let Thresh := params.Thresh D.componentCount
    (ttcReference.loop O b params.ε'
      (params.δ' D.componentCount) Thresh
      (List.ofFn D.component) (TTCState.unitInitial n)).map
        (EstReference b Thresh)

/-- The charge of the rate check: when it halves, one survival draw per stored copy and
the scalar work for `k` and `p`. -/
def ttcReference.firstLoopCost {n : Nat} (s : TTCState n)
    (t : NNReal) (Thresh : Real) : Nat :=
  if ttcReference.firstLoopExit s t Thresh = 0 then 0
  else TTCRuntime.rateThinningRoundOperations s.X.card

/-- The rate check with its charge retained. -/
def ttcReference.firstLoopWithCost {n : Nat} (s : TTCState n)
    (t : NNReal) (Thresh : Real) : Measure (TTCState n × Nat) :=
  fairCoinStreamLaw.map fun coins =>
    (ttcReference.firstLoopResult s t Thresh coins,
      ttcReference.firstLoopCost s t Thresh)

/-- One charged reference iteration. -/
def ttcReference.stepWithCost {n k : Nat} (O : CostedTTCOracles n k)
    (b : Nat) (ε' δ' Thresh : Real) (P : PolytopeData n)
    (state : TTCState n) : Measure (TTCState n × Nat) :=
  costedBind (O.computeVolumeWithCost P ε' δ') fun volumeOutcome =>
    let t := ttcReference.t b n Thresh volumeOutcome.2
    let withoutDuplicates := state.removeComponent P
    let deletionCost := TTCRuntime.deletionPassOperations n
      P.presentation.facetCount state.X.card
        (state.X.card - withoutDuplicates.X.card)
    costedBind (costedCharge (Measure.dirac withoutDuplicates) deletionCost)
      fun deleted =>
        costedBind (ttcReference.firstLoopWithCost deleted t Thresh)
          fun firstThinned =>
            costedBind
              (costedCharge (Poisson (t * firstThinned.p))
                TTCRuntime.poissonDrawOperations)
              fun N =>
                costedBind (ttcPseudocode.secondLoopWithCost firstThinned N Thresh)
                  fun secondThinned =>
                    costedBind
                      (O.generateSamplesWithCost P secondThinned.2 b ε')
                      fun S =>
                        costedCharge (Measure.dirac (secondThinned.1.addBatch S))
                          (secondThinned.2 * TTCRuntime.appendCopyOperations)

/-- The charged reference `for` loop. -/
def ttcReference.loopWithCost {n k : Nat} (O : CostedTTCOracles n k)
    (b : Nat) (ε' δ' Thresh : Real) :
    List (PolytopeData n) → TTCState n → Measure (TTCState n × Nat)
  | [], state => Measure.dirac (state, 0)
  | P :: rest, state =>
      costedBind
        (ttcReference.stepWithCost O b ε' δ' Thresh P state)
        (ttcReference.loopWithCost O b ε' δ' Thresh rest)

/-- The charged reference run. -/
def ttcReferenceWithCost {n k : Nat} (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F)) (params : ApproxParams)
    (O : CostedTTCOracles n k) (preprocessingOperations : Nat) :
    Measure (NNReal × Nat) :=
  let D := O.base.preprocessing.run F hbounded
  if D.componentCount = 0 then
    Measure.dirac (0, preprocessingOperations)
  else
    let b := O.base.choosePrecision D params
    let Thresh := params.Thresh D.componentCount
    (ttcReference.loopWithCost O b params.ε'
      (params.δ' D.componentCount) Thresh
      (List.ofFn D.component) (TTCState.unitInitial n)).map
        fun result => (EstReference b Thresh result.1,
          preprocessingOperations + result.2)

/-- The reference run with the concrete subroutines. -/
def ttcRef {n k : Nat} (hn : 3 ≤ n) (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F)) (params : ApproxParams)
    (prep : TTCPreprocessor n k) : Measure NNReal :=
  ttcReference F hbounded params (ttcSubroutines hn prep)

/-- The charged reference run with the concrete subroutines. -/
def ttcRefWithCost {n k : Nat} (hn : 3 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (params : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations cv18NonQueryFactor : Nat) : Measure (NNReal × Nat) :=
  ttcReferenceWithCost F hbounded params
    (ttcCostedSubroutines hn prep cv18NonQueryFactor)
    preprocessingOperations

end ttc
