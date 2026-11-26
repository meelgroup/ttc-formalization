import ttc.Analysis.LegacyPrelude
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
`Analysis/LegacyRun.lean` fills them, and its `ttc` is the reference law used in the correctness proof.

Random choices are composed with `Measure.bind`, so every adaptive call is a fresh
conditional draw. Random deletions are realised by an infinite stream of independent fair
coins, one per round and per labelled copy: "remove every element of `X` with probability
`1 - 2^{-k}`" keeps a copy when its first `k` coins all show `true`, and "remove every element
of `X` with probability 1/2" is one round. The unbounded `while` loop is its first-exit
semantics under that stream (`sInf` totalises the null set of streams on which no exit
occurs). Labelling the `N` pending Poisson copies too makes that loop's
`N ← Binomial(N, 1/2)` the same coins' survivor count.
-/

noncomputable section

open scoped ENNReal NNReal ProbabilityTheory unitInterval
open MeasureTheory

namespace ttc

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

/-- The subroutines Algorithm `ttc` calls. -/
structure TTCOracles (n k : Nat) where
  /-- `BooleanAbstraction` and `toDNF` (lines `line:boolabs`, `line:allsat`). -/
  preprocessing : TTCPreprocessor n k
  /-- `b ← GetPrecision(F_d, M, ε / 96)` (line `line:getprec`). -/
  choosePrecision : {F : LRAFormula n k} → (D : Decomposition F) → (p : ApproxParams) → Nat
  /-- `ComputeVolume(Pᵢ, ε', δ')` (line `line:volume`). -/
  ComputeVolume : PolytopeData n → Real → Real → Measure VolumeOutcome
  /-- `GenerateSamples(Kᵢ, Nᵢ, b, ε')` (line `line:sample`). -/
  GenerateSamples : (P : PolytopeData n) → (count b : Nat) →
    Real → Measure (SampleBatch n count)

/-! ## `p ← Thresh`, `X ← ∅` -/

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

/-- `p ← Thresh`, `X ← ∅`. -/
def TTCState.initial (n : Nat) (Thresh : Real) : TTCState n where
  p := Real.toNNReal Thresh
  X := ∅
  nextLabel := 0

/-! ## Line `line:volume`: `t ← 10^{bn} · ComputeVolume(Kᵢ, ε', δ')` -/

/-- `t = 10^{bn} · v` for a `ComputeVolume` estimate `v`. -/
def ttcPseudocode.t (b n : Nat) (volumeEstimate : NNReal) : NNReal :=
  (10 : NNReal) ^ (b * n) * volumeEstimate

/-! ## Line `line:inside-remove`: remove from `X` every `s ∈ Pᵢ` -/

/-- Remove every retained copy whose point lies in `Pᵢ`, as decided by the membership
test `memberProg`. -/
def TTCState.removeComponent {n : Nat} (s : TTCState n) (P : PolytopeData n) : TTCState n :=
  { s with X := s.X.filter (fun copy => (P.presentation.memberProg copy.2.toPoint).value = false) }

/-- The charge for the deletion pass: what `memberProg` spends on each stored copy, plus one
operation for each copy removed. -/
def TTCState.deletionCost {n : Nat} (s : TTCState n) (P : PolytopeData n) : Nat :=
  (∑ copy ∈ s.X, (P.presentation.memberProg copy.2.toPoint).cost) +
    (s.X.card - (s.removeComponent P).X.card) * TTCRuntime.deleteCopyOperations

/-! ## "Remove every element of `X` with probability 1/2" -/

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

/-! ## Lines `line:check-threshold` to `line:final-remove`:
`if t p ≥ Thresh`: `k ← ⌈log₂ (t p / Thresh)⌉`, `p ← p · 2^{-k}`,
remove every element of `X` with probability `1 - 2^{-k}` -/

/-- The exponent `k` of lines `line:check-threshold` and `line:final-k`; it is `0` when the
guard `t p ≥ Thresh` fails, so that the state is left unchanged. -/
def ttcPseudocode.rateHalvings {n : Nat} (s : TTCState n) (t : NNReal)
    (Thresh : Real) : Nat :=
  if Thresh ≤ ((t * s.p : NNReal) : Real) then
    Nat.ceil (Real.logb 2 (((t * s.p : NNReal) : Real) / Thresh))
  else 0

/-- `p ← p · 2^{-k}` and "remove every element of `X` with probability `1 - 2^{-k}`": a copy
is kept exactly when its `k` independent fair coins all show `true`, which happens with
probability `2^{-k}`, independently across copies. -/
def ttcPseudocode.rateCheckResult {n : Nat} (s : TTCState n)
    (t : NNReal) (Thresh : Real) (coins : Nat × Nat → Bool) : TTCState n :=
  let k := ttcPseudocode.rateHalvings s t Thresh
  { p := s.p / (2 : NNReal) ^ k
    X := samplesAfter coins k s.X
    nextLabel := s.nextLabel }

/-- Lines `line:check-threshold` to `line:final-remove`. -/
def ttcPseudocode.rateCheck {n : Nat} (s : TTCState n)
    (t : NNReal) (Thresh : Real) : Measure (TTCState n) :=
  fairCoinStreamLaw.map (ttcPseudocode.rateCheckResult s t Thresh)

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

/-! ## Line `line:sample`: `S ← GenerateSamples(Kᵢ, Nᵢ, b, ε')`; `X.Append(S)` -/

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

/-! ## Line `line:output`: output `|X| / (p · 10^{bn})` -/

/-- The output `Est = |X| / (p · 10^{bn})`. -/
def Est {n : Nat} (b : Nat) (s : TTCState n) : NNReal :=
  (s.X.card : NNReal) / (s.p * (10 : NNReal) ^ (b * n))

/-! ## The algorithm -/

/-- One iteration of the `for` loop (lines `line:final-for-sketch-begin` to
`line:final-for-sketch-end`) on the polytope `Kᵢ`. -/
def ttcPseudocode.step {n k : Nat} (O : TTCOracles n k) (b : Nat)
    (ε' δ' Thresh : Real) (P : PolytopeData n)
    (state : TTCState n) : Measure (TTCState n) :=
  (O.ComputeVolume P ε' δ').bind fun volumeOutcome =>
    let t := ttcPseudocode.t b n volumeOutcome.2
    let withoutDuplicates := state.removeComponent P
    (ttcPseudocode.rateCheck withoutDuplicates t Thresh).bind fun rateChecked =>
      (Poisson (t * rateChecked.p)).bind fun N =>
        (ttcPseudocode.secondLoop rateChecked N Thresh).bind fun secondThinned =>
          (O.GenerateSamples P secondThinned.2 b ε').map fun S =>
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
      (List.ofFn D.component) (TTCState.initial n Thresh)).map
        (Est b)

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

/-- The charge for lines `line:check-threshold` to `line:final-remove`: when `k > 0`, one
survival draw per stored copy and the scalar work for `k` and `p`. -/
def ttcPseudocode.rateCheckCost {n : Nat} (s : TTCState n)
    (t : NNReal) (Thresh : Real) : Nat :=
  if ttcPseudocode.rateHalvings s t Thresh = 0 then 0
  else TTCRuntime.rateThinningRoundOperations s.X.card

/-- The rate check with its charge retained in the result. -/
def ttcPseudocode.rateCheckWithCost {n : Nat} (s : TTCState n)
    (t : NNReal) (Thresh : Real) : Measure (TTCState n × Nat) :=
  fairCoinStreamLaw.map fun coins =>
    (ttcPseudocode.rateCheckResult s t Thresh coins,
      ttcPseudocode.rateCheckCost s t Thresh)

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
  /-- The one-time cost of preparing the oracles for a polytope at precision `b` and
  accuracy `ε'`, such as rewriting its offsets. -/
  setupCost : PolytopeData n → Nat → Real → Nat
  computeVolumeWithCost : (P : PolytopeData n) → Real → Real →
    Measure (VolumeOutcome × Nat)
  generateSamplesWithCost : (P : PolytopeData n) → (count b : Nat) →
    Real → Measure (SampleBatch n count × Nat)

/-- One charged iteration of the `for` loop, using the fixed real-RAM charges in `Prelude`.
Preparing the oracles for the polytope (`O.setupCost`) is charged with the deletion pass.
The oracle fields retain their own charges, including retries. -/
def ttcPseudocode.stepWithCost {n k : Nat} (O : CostedTTCOracles n k)
    (b : Nat) (ε' δ' Thresh : Real) (P : PolytopeData n)
    (state : TTCState n) : Measure (TTCState n × Nat) :=
  costedBind (O.computeVolumeWithCost P ε' δ') fun volumeOutcome =>
    let t := ttcPseudocode.t b n volumeOutcome.2
    let withoutDuplicates := state.removeComponent P
    let deletionCost := O.setupCost P b ε' + state.deletionCost P
    costedBind (costedCharge (Measure.dirac withoutDuplicates) deletionCost)
      fun deleted =>
        costedBind (ttcPseudocode.rateCheckWithCost deleted t Thresh)
          fun rateChecked =>
            costedBind
              (costedCharge (Poisson (t * rateChecked.p))
                TTCRuntime.poissonDrawOperations)
              fun N =>
                costedBind (ttcPseudocode.secondLoopWithCost rateChecked N Thresh)
                  fun secondThinned =>
                    costedBind
                      (O.generateSamplesWithCost P secondThinned.2 b ε')
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
      (List.ofFn D.component) (TTCState.initial n Thresh)).map
        fun result => (Est b result.1,
          preprocessingOperations + result.2)

end ttc
