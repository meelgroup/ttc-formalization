import Kr25Ssmxt.Model.Prelude
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.ProductMeasure

/-!
# Algorithm `ttc`, with its subroutines as slots

This file follows Algorithm `ttc` (`sections/algo.tex`) line by line. Paper line labels are
quoted in the section headers. The subroutines `BooleanAbstraction`, `toDNF`,
`GetPrecision`, `ComputeVolume` and `GenerateSamples` are slots of `TTCOracles`;
`Model/Run.lean` fills them, and its `ttc` is the algorithm the theorems are about.

Random choices are composed with `Measure.bind`, so every adaptive call is a fresh
conditional draw. "Remove every element of `X` with probability 1/2" is realised by an
infinite stream of independent fair coins, one per round and per labelled copy; the two
unbounded `while` loops are their first-exit semantics under that stream (`sInf` totalises
the null set of streams on which no exit occurs). Labelling the `N` pending Poisson copies
too makes the second loop's `N ← Binomial(N, 1/2)` the same coins' survivor count.
-/

noncomputable section

open scoped ENNReal NNReal ProbabilityTheory unitInterval
open MeasureTheory

namespace Kr25Ssmxt

/-! ## Data passed between the lines -/

/-- A `ComputeVolume` result, tagged by membership in its batch good event. -/
abbrev VolumeOutcome := Bool × NNReal

/--
A lattice point is stored by its decimal precision and integer coordinates.  This is the
countable state space actually used by the paper's sampler; `toPoint` is its realization in
the ambient real space.
-/
abbrev LatticePoint (n : Nat) := Nat × (Fin n → Int)

/-- Realization of a coded decimal-lattice point. -/
def LatticePoint.toPoint {n : Nat} (x : LatticePoint n) : Point n :=
  fun i => (x.2 i : Real) / (10 : Real) ^ x.1

/-- Coded points of precision `b` lying in a component. -/
def codedLatticePoints {n : Nat} (P : PolytopeData n) (b : Nat) : Set (LatticePoint n) :=
  {x | x.1 = b ∧ x.toPoint ∈ P.carrier}

/-- A `GenerateSamples` batch: `count` lattice points. -/
abbrev SampleBatch (n count : Nat) := Fin count → LatticePoint n

/-- A labelled lattice copy; equal points may occur with different labels. -/
abbrev SampleCopy (n : Nat) := Nat × LatticePoint n

/-! ## Lines `line:boolabs`, `line:allsat`, `line:getprec`: preprocessing and precision -/

/-- `BooleanAbstraction`, `toDNF`, and the normalization of the DNF cubes into
full-dimensional polytopes. -/
structure TTCPreprocessor (n k : Nat) where
  booleanAbstraction : (F : LRAFormula n k) → BooleanAbstraction F
  toDNF : {F : LRAFormula n k} → (A : BooleanAbstraction F) → DNFResult A
  normalize : {F : LRAFormula n k} → (A : BooleanAbstraction F) →
    DNFResult A → Bornology.IsBounded (solutionSet F) → Decomposition F

/-- Lines `line:boolabs` and `line:allsat`, then normalization: the polytopes `Pᵢ`. -/
def TTCPreprocessor.run {n k : Nat} (prep : TTCPreprocessor n k)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F)) :
    Decomposition F :=
  let abstraction := prep.booleanAbstraction F
  let cubes := prep.toDNF abstraction
  prep.normalize abstraction cubes hbounded

/-- The subroutines Algorithm `ttc` calls. -/
structure TTCOracles (n k : Nat) where
  /-- `BooleanAbstraction` and `toDNF` (lines `line:boolabs`, `line:allsat`). -/
  preprocessing : TTCPreprocessor n k
  /-- `b ← GetPrecision(F_d, M, ε / 96)` (line `line:getprec`). -/
  choosePrecision : {F : LRAFormula n k} → (D : Decomposition F) → (p : ApproxParams) → Nat
  /-- `ComputeVolume(Pᵢ, ε', δ')` (line `line:volume`). -/
  ComputeVolume : PolytopeData n → Real → Real → Measure VolumeOutcome
  /-- `GenerateSamples(Pᵢ, Nᵢ, b, ε', δ')` (line `line:sample`). -/
  GenerateSamples : (P : PolytopeData n) → (count b : Nat) →
    Real → Real → Measure (SampleBatch n count)

/-! ## Line `line:candidate`: `p ← 1`, `X ← ∅` -/

/-- The state of Algorithm `ttc`: the probability `p`, the multiset `X` of labelled
lattice copies, and the next fresh label. -/
structure TTCState (n : Nat) where
  p : NNReal
  X : Finset (SampleCopy n)
  nextLabel : Nat

/--
The state carries the product measurable structure of its mathematical fields.  In
particular, the retained collection is discrete because `SampleCopy n` is countable.  This
matches the paper's lattice-supported execution and makes its finite control state measurable.
-/
instance TTCState.instMeasurableSpace (n : Nat) : MeasurableSpace (TTCState n) :=
  MeasurableSpace.comap (fun s => (s.p, s.X, s.nextLabel)) inferInstance

/-- `p ← 1`, `X ← ∅`. -/
def TTCState.initial (n : Nat) : TTCState n where
  p := 1
  X := ∅
  nextLabel := 0

/-! ## Line `line:volume`: `t ← Thresh · 10^{bn} · ComputeVolume(Pᵢ, ε', δ')` -/

/-- `t = Thresh · 10^{bn} · v` for a `ComputeVolume` estimate `v`. -/
def ttcPseudocode.t (b n : Nat) (Thresh : Real) (volumeEstimate : NNReal) : NNReal :=
  Real.toNNReal Thresh * (10 : NNReal) ^ (b * n) * volumeEstimate

/-! ## Line `line:inside-remove`: remove from `X` every `s ∈ Pᵢ` -/

/-- Remove every retained copy whose point lies in `Pᵢ`. -/
def TTCState.removeComponent {n : Nat} (s : TTCState n) (P : PolytopeData n) : TTCState n := by
  classical
  exact { s with X := s.X.filter (fun copy => copy.2.toPoint ∉ P.carrier) }

/-! ## "Remove every element of `X` with probability 1/2" -/

/-- The probability `1/2`, coerced into Mathlib's unit interval. -/
def fairProbability : unitInterval :=
  Set.projIcc (0 : Real) 1 zero_le_one (1 / 2)

/-- One fair deletion coin. -/
def fairCoinLaw : Measure Bool :=
  ProbabilityTheory.bernoulliMeasure true false fairProbability

/-- Independent fair coins indexed by thinning round and copy label. -/
def fairCoinStreamLaw : Measure (Nat × Nat → Bool) :=
  Measure.infinitePi (fun _ : Nat × Nat => fairCoinLaw)

/-- Whether a labelled copy survives the first `rounds` rounds. -/
def survives (coins : Nat × Nat → Bool) (rounds label : Nat) : Prop :=
  ∀ r < rounds, coins (r, label) = true

/-- Retained copies after a fixed number of coupled fair thinnings. -/
def samplesAfter {n : Nat} (coins : Nat × Nat → Bool) (rounds : Nat)
    (samples : Finset (SampleCopy n)) : Finset (SampleCopy n) := by
  classical
  exact samples.filter (fun copy => survives coins rounds copy.1)

/-- Pending Poisson copies after the same number of coupled fair thinnings. -/
def pendingAfter (coins : Nat × Nat → Bool) (rounds firstLabel count : Nat) : Nat :=
  by
    classical
    exact ((Finset.range count).filter
      (fun i => survives coins rounds (firstLabel + i))).card

/-! ## Line `line:prob-remove`: `while p ≥ Thresh / t`, halve `X` and `p` -/

/-- The first `while` guard becomes false after this many halvings. -/
def ttcPseudocode.firstLoopExit {n : Nat} (s : TTCState n) (t : NNReal)
    (Thresh : Real) : Nat :=
  sInf {rounds : Nat |
    ((t * s.p / (2 : NNReal) ^ rounds : NNReal) : Real) < Thresh}

/-- The state when the first `while` loop exits. -/
def ttcPseudocode.firstLoopResult {n : Nat} (s : TTCState n)
    (t : NNReal) (Thresh : Real) (coins : Nat × Nat → Bool) : TTCState n :=
  let rounds := ttcPseudocode.firstLoopExit s t Thresh
  { p := s.p / (2 : NNReal) ^ rounds
    X := samplesAfter coins rounds s.X
    nextLabel := s.nextLabel }

/-- The first `while` loop. -/
def ttcPseudocode.firstLoop {n : Nat} (s : TTCState n)
    (t : NNReal) (Thresh : Real) : Measure (TTCState n) :=
  fairCoinStreamLaw.map (ttcPseudocode.firstLoopResult s t Thresh)

/-! ## `Nᵢ ← Poisson(t · p)` -/

/-- `Poisson(λ)`. -/
abbrev Poisson (rate : NNReal) : Measure ℕ := ProbabilityTheory.poissonMeasure rate

/-! ## Lines `line:final-check-threshold` to `line:final-update-prob`:
`while Nᵢ + |X| > Thresh`, halve `X`, `Nᵢ ← Binomial(Nᵢ, 1/2)`, `p ← p / 2` -/

/-- The second `while` guard has become false after `rounds` halvings. -/
def ttcPseudocode.secondLoopExit {n : Nat} (s : TTCState n) (N : Nat) (Thresh : Real)
    (coins : Nat × Nat → Bool) (rounds : Nat) : Prop :=
  (samplesAfter coins rounds s.X).card +
      pendingAfter coins rounds s.nextLabel N ≤ Thresh

/-- First-exit round, with `sInf ∅ = 0` only on a nonterminating coin stream. -/
def ttcPseudocode.secondLoopExitRound {n : Nat} (s : TTCState n) (N : Nat) (Thresh : Real)
    (coins : Nat × Nat → Bool) : Nat :=
  sInf {rounds | ttcPseudocode.secondLoopExit s N Thresh coins rounds}

/-- The state and `Nᵢ` when the second `while` loop exits. -/
def ttcPseudocode.secondLoopResult {n : Nat} (s : TTCState n) (N : Nat) (Thresh : Real)
    (coins : Nat × Nat → Bool) : TTCState n × Nat :=
  let rounds := ttcPseudocode.secondLoopExitRound s N Thresh coins
  ({ p := s.p / (2 : NNReal) ^ rounds
     X := samplesAfter coins rounds s.X
     nextLabel := s.nextLabel },
   pendingAfter coins rounds s.nextLabel N)

/-- The second `while` loop. -/
def ttcPseudocode.secondLoop {n : Nat} (s : TTCState n) (N : Nat)
    (Thresh : Real) : Measure (TTCState n × Nat) :=
  fairCoinStreamLaw.map (ttcPseudocode.secondLoopResult s N Thresh)

/-! ## Line `line:sample`: `S ← GenerateSamples(Pᵢ, Nᵢ, b, ε', δ')`; `X.Append(S)` -/

/-- `X.Append(S)`, giving the new copies fresh labels so multiplicity is kept. -/
def TTCState.addBatch {n count : Nat} (s : TTCState n)
    (points : Fin count → LatticePoint n) : TTCState n := by
  classical
  let added : Finset (SampleCopy n) :=
    Finset.univ.image (fun i => (s.nextLabel + i.val, points i))
  exact
    { p := s.p
      X := s.X ∪ added
      nextLabel := s.nextLabel + count }

/-! ## Line `line:output`: output `|X| / (p · Thresh · 10^{bn})` -/

/-- The output `Est = |X| / (p · Thresh · 10^{bn})`. -/
def Est {n : Nat} (b : Nat) (Thresh : Real)
    (s : TTCState n) : NNReal :=
  (s.X.card : NNReal) /
    (s.p * Real.toNNReal Thresh * (10 : NNReal) ^ (b * n))

/-! ## The algorithm -/

/-- One iteration of the `for` loop (lines `line:final-for-sketch-begin` to
`line:final-for-sketch-end`) on the polytope `Pᵢ`. -/
def ttcPseudocode.step {n k : Nat} (O : TTCOracles n k) (b : Nat)
    (ε' δ' Thresh : Real) (P : PolytopeData n)
    (state : TTCState n) : Measure (TTCState n) :=
  (O.ComputeVolume P ε' δ').bind fun volumeOutcome =>
    let t := ttcPseudocode.t b n Thresh volumeOutcome.2
    let withoutDuplicates := state.removeComponent P
    (ttcPseudocode.firstLoop withoutDuplicates t Thresh).bind fun firstThinned =>
      (Poisson (t * firstThinned.p)).bind fun N =>
        (ttcPseudocode.secondLoop firstThinned N Thresh).bind fun secondThinned =>
          (O.GenerateSamples P secondThinned.2 b ε' δ').map fun S =>
            secondThinned.1.addBatch S

/-- The `for` loop over `P₁, …, Pₘ`. -/
def ttcPseudocode.loop {n k : Nat} (O : TTCOracles n k) (b : Nat)
    (ε' δ' Thresh : Real) :
    List (PolytopeData n) → TTCState n → Measure (TTCState n)
  | [], state => Measure.dirac state
  | P :: rest, state =>
      (ttcPseudocode.step O b ε' δ' Thresh P state).bind
        (ttcPseudocode.loop O b ε' δ' Thresh rest)

/-- Algorithm `ttc(F, ε, δ)` with the subroutines `O`. An empty decomposition has volume
zero and outputs `0`. -/
def ttcPseudocode {n k : Nat} (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F)) (params : ApproxParams)
    (O : TTCOracles n k) : Measure NNReal :=
  let D := O.preprocessing.run F hbounded
  if D.componentCount = 0 then
    Measure.dirac 0
  else
    let b := O.choosePrecision D params
    let Thresh := params.Thresh D.componentCount
    (ttcPseudocode.loop O b params.ε'
      (params.δ' D.componentCount) Thresh
      (List.ofFn D.component) (TTCState.initial n)).map
        (Est b Thresh)

/-! ## The same algorithm with operation counts (for Theorem 3) -/

/-- Compose two charged random computations, adding their operation counts. -/
def costedBind {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (first : Measure (α × Nat)) (next : α → Measure (β × Nat)) :
    Measure (β × Nat) :=
  first.bind fun result =>
    (next result.1).map fun continuation =>
      (continuation.1, result.2 + continuation.2)

/-- Add a fixed real-RAM charge to a random computation. -/
def costedCharge {α : Type*} [MeasurableSpace α]
    (law : Measure α) (operations : Nat) : Measure (α × Nat) :=
  law.map fun result => (result, operations)

/-- An upper charge for the first loop: each round visits at most the copies
present at entry, and performs its guard and rate update. -/
def ttcPseudocode.firstLoopCost {n : Nat} (s : TTCState n)
    (t : NNReal) (Thresh : Real) : Nat :=
  ttcPseudocode.firstLoopExit s t Thresh *
    TTCRuntime.rateThinningRoundOperations s.X.card

/-- The first loop with its charged rounds retained in the result. -/
def ttcPseudocode.firstLoopWithCost {n : Nat} (s : TTCState n)
    (t : NNReal) (Thresh : Real) : Measure (TTCState n × Nat) :=
  fairCoinStreamLaw.map fun coins =>
    (ttcPseudocode.firstLoopResult s t Thresh coins,
      ttcPseudocode.firstLoopCost s t Thresh)

/-- An upper charge for the second loop. The pending count is represented by
one binomial draw per round, regardless of its numeric value. -/
def ttcPseudocode.secondLoopCost {n : Nat} (s : TTCState n) (N : Nat)
    (Thresh : Real) (coins : Nat × Nat → Bool) : Nat :=
  ttcPseudocode.secondLoopExitRound s N Thresh coins *
    TTCRuntime.countThinningRoundOperations s.X.card

/-- The second loop with its charged rounds retained. -/
def ttcPseudocode.secondLoopWithCost {n : Nat} (s : TTCState n) (N : Nat)
    (Thresh : Real) : Measure ((TTCState n × Nat) × Nat) :=
  fairCoinStreamLaw.map fun coins =>
    (ttcPseudocode.secondLoopResult s N Thresh coins,
      ttcPseudocode.secondLoopCost s N Thresh coins)

/-- Charged implementations of `ComputeVolume` and `GenerateSamples`. -/
structure CostedTTCOracles (n k : Nat) where
  base : TTCOracles n k
  computeVolumeWithCost : (P : PolytopeData n) → Real → Real →
    Measure (VolumeOutcome × Nat)
  generateSamplesWithCost : (P : PolytopeData n) → (count b : Nat) →
    Real → Real → Measure (SampleBatch n count × Nat)

/-- One charged iteration of the `for` loop, using the fixed real-RAM charges in `Prelude`.
The oracle fields retain their own charges, including retries. -/
def ttcPseudocode.stepWithCost {n k : Nat} (O : CostedTTCOracles n k)
    (b : Nat) (ε' δ' Thresh : Real) (P : PolytopeData n)
    (state : TTCState n) : Measure (TTCState n × Nat) :=
  costedBind (O.computeVolumeWithCost P ε' δ') fun volumeOutcome =>
    let t := ttcPseudocode.t b n Thresh volumeOutcome.2
    let withoutDuplicates := state.removeComponent P
    let deletionCost := TTCRuntime.deletionPassOperations n
      P.presentation.facetCount state.X.card
        (state.X.card - withoutDuplicates.X.card)
    costedBind (costedCharge (Measure.dirac withoutDuplicates) deletionCost)
      fun deleted =>
        costedBind (ttcPseudocode.firstLoopWithCost deleted t Thresh)
          fun firstThinned =>
            costedBind
              (costedCharge (Poisson (t * firstThinned.p))
                TTCRuntime.poissonDrawOperations)
              fun N =>
                costedBind (ttcPseudocode.secondLoopWithCost firstThinned N Thresh)
                  fun secondThinned =>
                    costedBind
                      (O.generateSamplesWithCost P secondThinned.2 b ε' δ')
                      fun S =>
                        costedCharge (Measure.dirac (secondThinned.1.addBatch S))
                          (secondThinned.2 * TTCRuntime.appendCopyOperations)

/-- The charged `for` loop, in the paper's component order. -/
def ttcPseudocode.loopWithCost {n k : Nat} (O : CostedTTCOracles n k)
    (b : Nat) (ε' δ' Thresh : Real) :
    List (PolytopeData n) → TTCState n → Measure (TTCState n × Nat)
  | [], state => Measure.dirac (state, 0)
  | P :: rest, state =>
      costedBind
        (ttcPseudocode.stepWithCost O b ε' δ' Thresh P state)
        (ttcPseudocode.loopWithCost O b ε' δ' Thresh rest)

/-- A charged `ttc` law whose first coordinate is the output `Est`. -/
def ttcPseudocodeWithCost {n k : Nat} (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F)) (params : ApproxParams)
    (O : CostedTTCOracles n k) (preprocessingOperations : Nat) :
    Measure (NNReal × Nat) :=
  let D := O.base.preprocessing.run F hbounded
  if D.componentCount = 0 then
    Measure.dirac (0, preprocessingOperations)
  else
    let b := O.base.choosePrecision D params
    let Thresh := params.Thresh D.componentCount
    (ttcPseudocode.loopWithCost O b params.ε'
      (params.δ' D.componentCount) Thresh
      (List.ofFn D.component) (TTCState.initial n)).map
        fun result => (Est b Thresh result.1,
          preprocessingOperations + result.2)

#krModelClosure ttcPseudocode

end Kr25Ssmxt


namespace Kr25Ssmxt

#krSurplusIn Kr25Ssmxt.Model.Program from ttcPseudocode
  ttcPseudocode.firstLoopWithCost ttcPseudocode.secondLoopWithCost ttcPseudocodeWithCost

end Kr25Ssmxt
