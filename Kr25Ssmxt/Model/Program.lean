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
# The TTC program

This module contains the oracle-parametric executable core.  The encoding follows the
paper's mathematical control flow.  Boolean abstraction, DNF
conversion, normalization, and precision selection are certified deterministic stages.
The two geometric routines are probability kernels.  The volume tag records its batch-level
good event; the sampler tag permits a general implementation contract, while the paper's
independently restarted Hit-and-Run construction instantiates it with an always-true tag.
All later random choices are composed with `Measure.bind`, so every adaptive call is a fresh
conditional draw.

The two unbounded thinning loops are represented by their first-exit semantics under an
infinite stream of independent fair coins.  `sInf` totalizes the null set of streams on which
no exit occurs; the analysis must prove that this exceptional set has measure zero.  Giving
each retained and pending copy a distinct natural label makes the shared thinning coupling
literal: its surviving pending cardinality is the binomial update, while the same round's
independent coordinates thin the retained multiset.
-/

noncomputable section

open scoped ENNReal NNReal ProbabilityTheory unitInterval
open MeasureTheory

namespace Kr25Ssmxt

/-- A certified precision: the output of `GetPrecision(F_d, M, ε / 96)`. -/
structure PrecisionChoice {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) where
  value : Nat
  adequate : PrecisionAdequate D value p.precisionEta

/-- `maxratio` of Algorithm `getprec`: the largest ratio of the required radius
`γ = (64 m n / η) √(log (4 r / η))` to a component's inradius, starting from `1`.
The inradius is each component's certified inball radius. -/
noncomputable def getPrecisionRatio {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (η : Real) : Real :=
  max 1 ((Finset.univ.sup fun i : Fin D.componentCount =>
    Real.toNNReal (latticeRadiusRequirement D η / (D.component i).inradius) :
      NNReal) : Real)

/-- Algorithm `getprec(F_d, M, η)`: return `⌈log₁₀ maxratio⌉`. -/
noncomputable def getPrecision {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (η : Real) : Nat :=
  Nat.ceil (Real.logb 10 (getPrecisionRatio D η))

/-- The precision returned by `getprec` meets its specification. -/
theorem getPrecision_adequate {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (η : Real) :
    PrecisionAdequate D (getPrecision D η) η := by
  intro i
  have hγ := (D.component i).inradius_pos
  have hratio1 : (1 : Real) ≤ getPrecisionRatio D η := le_max_left _ _
  have hterm : latticeRadiusRequirement D η / (D.component i).inradius ≤
      getPrecisionRatio D η := by
    refine (Real.le_coe_toNNReal _).trans (le_trans ?_ (le_max_right _ _))
    exact NNReal.coe_le_coe.mpr (Finset.le_sup
      (f := fun i : Fin D.componentCount => Real.toNNReal
        (latticeRadiusRequirement D η / (D.component i).inradius))
      (Finset.mem_univ i))
  have hpow : getPrecisionRatio D η ≤ (10 : Real) ^ getPrecision D η := by
    have hpos : 0 < getPrecisionRatio D η := by linarith
    calc getPrecisionRatio D η
        = (10 : Real) ^ Real.logb 10 (getPrecisionRatio D η) :=
          (Real.rpow_logb (by norm_num) (by norm_num) hpos).symm
      _ ≤ (10 : Real) ^ (getPrecision D η : Real) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
      _ = (10 : Real) ^ getPrecision D η := Real.rpow_natCast _ _
  have := (div_le_iff₀ hγ).mp (hterm.trans hpow)
  linarith

/-- Line 3 of Algorithm `ttc`: `b ← GetPrecision(F_d, M, ε / 96)`. -/
noncomputable def getPrecisionChoice {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) : PrecisionChoice D p :=
  ⟨getPrecision D p.precisionEta, getPrecision_adequate D p.precisionEta⟩

/-- Certified deterministic preprocessing carried out by TTC, rather than supplied per input.
The precision stage is not a parameter: it is `getprec`, see
`TTCPreprocessor.choosePrecision`. -/
structure TTCPreprocessor (n k : Nat) where
  booleanAbstraction : (F : LRAFormula n k) → BooleanAbstraction F
  toDNF : {F : LRAFormula n k} → (A : BooleanAbstraction F) → DNFResult A
  normalize : {F : LRAFormula n k} → (A : BooleanAbstraction F) →
    DNFResult A → Bornology.IsBounded (solutionSet F) → Decomposition F

/-- TTC's precision stage is always Algorithm `getprec` at `ε / 96`. -/
noncomputable def TTCPreprocessor.choosePrecision {n k : Nat}
    (_prep : TTCPreprocessor n k) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) : PrecisionChoice D p :=
  getPrecisionChoice D p

/-- Boolean abstraction, DNF conversion, and geometric normalization in paper order. -/
def TTCPreprocessor.run {n k : Nat} (prep : TTCPreprocessor n k)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F)) :
    Decomposition F :=
  let abstraction := prep.booleanAbstraction F
  let cubes := prep.toDNF abstraction
  prep.normalize abstraction cubes hbounded

/-- A volume-oracle result is tagged by membership in its batch good event. -/
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

/-- A sample batch retains a tag so certified fallible implementations remain representable. -/
abbrev SampleBatch (n count : Nat) := Bool × (Fin count → LatticePoint n)

/-- The deterministic certified stages and the two randomized geometric oracles. -/
structure TTCOracles (n k : Nat) where
  preprocessing : TTCPreprocessor n k
  computeVolume : PolytopeData n → Real → Real → Measure VolumeOutcome
  generateSamples : (P : PolytopeData n) → (count b : Nat) →
    Real → Real → Measure (SampleBatch n count)

/-- Pointwise multiplicative almost-uniformity on one finite lattice set. -/
def AlmostUniformPointwise {n : Nat} (μ : Measure (LatticePoint n))
    (S : Set (LatticePoint n)) (η : Real) : Prop :=
  IsProbabilityMeasure μ ∧ S.Finite ∧ S.Nonempty ∧ μ Sᶜ = 0 ∧
    ∀ x ∈ S, μ.real {x} ∈ Arlib.relErr η (1 / S.ncard)

/-- The required relative-volume guarantee for every call made in this TTC run. -/
def ComputeVolumeContract {n k : Nat} (O : TTCOracles n k)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) : Prop :=
  let D := O.preprocessing.run F hbounded
  ∀ i,
    let law := O.computeVolume (D.component i) p.epsilonPrime
      (p.deltaPrime D.componentCount)
    IsProbabilityMeasure law ∧
      law.real {o | o.1 = false} ≤ p.deltaPrime D.componentCount ∧
      ∀ᵐ o ∂law, o.1 = true →
        (o.2 : Real) ∈ Arlib.relErr p.epsilonPrime
          (volume (D.component i).carrier).toReal

/-- A labelled lattice copy; equal points may occur with different labels. -/
abbrev SampleCopy (n : Nat) := Nat × LatticePoint n

/-- The mutable mathematical state of TTC. -/
structure TTCState (n : Nat) where
  rate : NNReal
  samples : Finset (SampleCopy n)
  nextLabel : Nat

/--
The state carries the product measurable structure of its mathematical fields.  In
particular, the retained collection is discrete because `SampleCopy n` is countable.  This
matches the paper's lattice-supported execution and makes its finite control state measurable.
-/
instance TTCState.instMeasurableSpace (n : Nat) : MeasurableSpace (TTCState n) :=
  MeasurableSpace.comap (fun s => (s.rate, s.samples, s.nextLabel)) inferInstance

/-- Initial state: dyadic rate one and an empty retained multiset. -/
def TTCState.initial (n : Nat) : TTCState n where
  rate := 1
  samples := ∅
  nextLabel := 0

/-- Remove every retained copy whose point lies in the next component. -/
def TTCState.removeComponent {n : Nat} (s : TTCState n) (P : PolytopeData n) : TTCState n := by
  classical
  exact { s with samples := s.samples.filter (fun copy => copy.2.toPoint ∉ P.carrier) }

/-- Add a generated batch, retaining multiplicity via fresh labels. -/
def TTCState.addBatch {n count : Nat} (s : TTCState n)
    (points : Fin count → LatticePoint n) : TTCState n := by
  classical
  let added : Finset (SampleCopy n) :=
    Finset.univ.image (fun i => (s.nextLabel + i.val, points i))
  exact
    { rate := s.rate
      samples := s.samples ∪ added
      nextLabel := s.nextLabel + count }

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

/-- The first loop guard has become false at this dyadic level. -/
def thinningExit {n : Nat} (s : TTCState n) (pending : Nat) (threshold : Real)
    (coins : Nat × Nat → Bool) (rounds : Nat) : Prop :=
  (samplesAfter coins rounds s.samples).card +
      pendingAfter coins rounds s.nextLabel pending ≤ threshold

/-- First-exit round, with `sInf ∅ = 0` only on a nonterminating coin stream. -/
def firstExitRound {n : Nat} (s : TTCState n) (pending : Nat) (threshold : Real)
    (coins : Nat × Nat → Bool) : Nat :=
  sInf {rounds | thinningExit s pending threshold coins rounds}

/-- State and pending count at the first exit from a thinning loop. -/
def thinningResult {n : Nat} (s : TTCState n) (pending : Nat) (threshold : Real)
    (coins : Nat × Nat → Bool) : TTCState n × Nat :=
  let rounds := firstExitRound s pending threshold coins
  ({ rate := s.rate / (2 : NNReal) ^ rounds
     samples := samplesAfter coins rounds s.samples
     nextLabel := s.nextLabel },
   pendingAfter coins rounds s.nextLabel pending)

/-- Measure-level first-exit semantics for one unbounded fair-thinning loop. -/
def thinUntil {n : Nat} (s : TTCState n) (pending : Nat)
    (threshold : Real) : Measure (TTCState n × Nat) :=
  fairCoinStreamLaw.map (thinningResult s pending threshold)

/-! ## TTC as printed in the current manuscript -/

/-- The first while guard becomes false after this many rate halvings. -/
def manuscriptRateExit {n : Nat} (s : TTCState n) (intensity : NNReal)
    (threshold : Real) : Nat :=
  sInf {rounds : Nat |
    ((intensity * s.rate / (2 : NNReal) ^ rounds : NNReal) : Real) < threshold}

/-- The manuscript's rate loop thins stored copies before drawing the Poisson count. -/
def manuscriptRateThinningResult {n : Nat} (s : TTCState n)
    (intensity : NNReal) (threshold : Real) (coins : Nat × Nat → Bool) : TTCState n :=
  let rounds := manuscriptRateExit s intensity threshold
  { rate := s.rate / (2 : NNReal) ^ rounds
    samples := samplesAfter coins rounds s.samples
    nextLabel := s.nextLabel }

def manuscriptRateThinUntil {n : Nat} (s : TTCState n)
    (intensity : NNReal) (threshold : Real) : Measure (TTCState n) :=
  fairCoinStreamLaw.map (manuscriptRateThinningResult s intensity threshold)

/-- An upper charge for the first loop: each round visits at most the copies
present at entry, and performs its guard and rate update. -/
def manuscriptRateThinningCost {n : Nat} (s : TTCState n)
    (intensity : NNReal) (threshold : Real) : Nat :=
  manuscriptRateExit s intensity threshold *
    TTCRuntime.rateThinningRoundOperations s.samples.card

/-- The first loop with its charged rounds retained in the result. -/
def manuscriptRateThinWithCost {n : Nat} (s : TTCState n)
    (intensity : NNReal) (threshold : Real) : Measure (TTCState n × Nat) :=
  fairCoinStreamLaw.map fun coins =>
    (manuscriptRateThinningResult s intensity threshold coins,
      manuscriptRateThinningCost s intensity threshold)

/-- An upper charge for the second loop. The pending count is represented by
one binomial draw per round, regardless of its numeric value. -/
def manuscriptCountThinningCost {n : Nat} (s : TTCState n) (pending : Nat)
    (threshold : Real) (coins : Nat × Nat → Bool) : Nat :=
  firstExitRound s pending threshold coins *
    TTCRuntime.countThinningRoundOperations s.samples.card

/-- The existing second-loop law with its charged rounds retained. -/
def manuscriptCountThinWithCost {n : Nat} (s : TTCState n) (pending : Nat)
    (threshold : Real) : Measure ((TTCState n × Nat) × Nat) :=
  fairCoinStreamLaw.map fun coins =>
    (thinningResult s pending threshold coins,
      manuscriptCountThinningCost s pending threshold coins)

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

/-- The scaled volume estimate `t = Threshold * 10^(b*n) * VolED(P)`. -/
def manuscriptIntensity (b n : Nat) (threshold : Real) (volumeEstimate : NNReal) : NNReal :=
  Real.toNNReal threshold * (10 : NNReal) ^ (b * n) * volumeEstimate

/-- The manuscript output `|X| / (p * Threshold * 10^(b*n))`. -/
def manuscriptEstimate {n : Nat} (b : Nat) (threshold : Real)
    (s : TTCState n) : NNReal :=
  (s.samples.card : NNReal) /
    (s.rate * Real.toNNReal threshold * (10 : NNReal) ^ (b * n))

/-- One manuscript component: delete, rate-thin, draw Poisson, count-thin, sample, append. -/
def manuscriptProcessComponent {n k : Nat} (O : TTCOracles n k) (b : Nat)
    (epsilonPrime deltaPrime threshold : Real) (P : PolytopeData n)
    (state : TTCState n) : Measure (TTCState n) :=
  (O.computeVolume P epsilonPrime deltaPrime).bind fun volumeOutcome =>
    let intensity := manuscriptIntensity b n threshold volumeOutcome.2
    let withoutDuplicates := state.removeComponent P
    (manuscriptRateThinUntil withoutDuplicates intensity threshold).bind fun firstThinned =>
      (ProbabilityTheory.poissonMeasure (intensity * firstThinned.rate)).bind fun pending =>
        (thinUntil firstThinned pending threshold).bind fun secondThinned =>
          (O.generateSamples P secondThinned.2 b epsilonPrime deltaPrime).map fun batch =>
            secondThinned.1.addBatch batch.2

def manuscriptProcessComponents {n k : Nat} (O : TTCOracles n k) (b : Nat)
    (epsilonPrime deltaPrime threshold : Real) :
    List (PolytopeData n) → TTCState n → Measure (TTCState n)
  | [], state => Measure.dirac state
  | P :: rest, state =>
      (manuscriptProcessComponent O b epsilonPrime deltaPrime threshold P state).bind
        (manuscriptProcessComponents O b epsilonPrime deltaPrime threshold rest)

/-- Current Algorithm 1, apart from the certified preprocessing and clipped oracle adapter. -/
def manuscriptTTC {n k : Nat} (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F)) (params : ApproxParams)
    (O : TTCOracles n k) : Measure NNReal :=
  let D := O.preprocessing.run F hbounded
  if D.componentCount = 0 then
    Measure.dirac 0
  else
    let b := (O.preprocessing.choosePrecision D params).value
    let threshold := params.threshold D.componentCount
    (manuscriptProcessComponents O b params.epsilonPrime
      (params.deltaPrime D.componentCount) threshold
      (List.ofFn D.component) (TTCState.initial n)).map
        (manuscriptEstimate b threshold)

/-! ## The same manuscript control flow with operation counts -/

/-- Charged implementations of TTC's two geometric oracle calls. -/
structure CostedTTCOracles (n k : Nat) where
  base : TTCOracles n k
  computeVolumeWithCost : (P : PolytopeData n) → Real → Real →
    Measure (VolumeOutcome × Nat)
  generateSamplesWithCost : (P : PolytopeData n) → (count b : Nat) →
    Real → Real → Measure (SampleBatch n count × Nat)

/-- One charged manuscript component, using the fixed real-RAM charges in `Prelude`.
The oracle fields retain their own charges, including retries. -/
def manuscriptProcessComponentWithCost {n k : Nat} (O : CostedTTCOracles n k)
    (b : Nat) (epsilonPrime deltaPrime threshold : Real) (P : PolytopeData n)
    (state : TTCState n) : Measure (TTCState n × Nat) :=
  costedBind (O.computeVolumeWithCost P epsilonPrime deltaPrime) fun volumeOutcome =>
    let intensity := manuscriptIntensity b n threshold volumeOutcome.2
    let withoutDuplicates := state.removeComponent P
    let deletionCost := TTCRuntime.deletionPassOperations n
      P.presentation.facetCount state.samples.card
        (state.samples.card - withoutDuplicates.samples.card)
    costedBind (costedCharge (Measure.dirac withoutDuplicates) deletionCost)
      fun deleted =>
        costedBind (manuscriptRateThinWithCost deleted intensity threshold)
          fun firstThinned =>
            costedBind
              (costedCharge
                (ProbabilityTheory.poissonMeasure (intensity * firstThinned.rate))
                TTCRuntime.poissonDrawOperations)
              fun pending =>
                costedBind (manuscriptCountThinWithCost firstThinned pending threshold)
                  fun secondThinned =>
                    costedBind
                      (O.generateSamplesWithCost P secondThinned.2 b epsilonPrime deltaPrime)
                      fun batch =>
                        costedCharge (Measure.dirac (secondThinned.1.addBatch batch.2))
                          (secondThinned.2 * TTCRuntime.appendCopyOperations)

/-- The charged component sequence retains the manuscript's component order. -/
def manuscriptProcessComponentsWithCost {n k : Nat} (O : CostedTTCOracles n k)
    (b : Nat) (epsilonPrime deltaPrime threshold : Real) :
    List (PolytopeData n) → TTCState n → Measure (TTCState n × Nat)
  | [], state => Measure.dirac (state, 0)
  | P :: rest, state =>
      costedBind
        (manuscriptProcessComponentWithCost O b epsilonPrime deltaPrime threshold P state)
        (manuscriptProcessComponentsWithCost O b epsilonPrime deltaPrime threshold rest)

/-- A charged TTC law whose first coordinate is the manuscript estimate. -/
def manuscriptTTCWithCost {n k : Nat} (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F)) (params : ApproxParams)
    (O : CostedTTCOracles n k) (preprocessingOperations : Nat) :
    Measure (NNReal × Nat) :=
  let D := O.base.preprocessing.run F hbounded
  if D.componentCount = 0 then
    Measure.dirac (0, preprocessingOperations)
  else
    let b := (O.base.preprocessing.choosePrecision D params).value
    let threshold := params.threshold D.componentCount
    (manuscriptProcessComponentsWithCost O b params.epsilonPrime
      (params.deltaPrime D.componentCount) threshold
      (List.ofFn D.component) (TTCState.initial n)).map
        fun result => (manuscriptEstimate b threshold result.1,
          preprocessingOperations + result.2)

#krModelClosure manuscriptTTC

end Kr25Ssmxt


namespace Kr25Ssmxt

#krSurplusIn Kr25Ssmxt.Model.Program from manuscriptTTC
  manuscriptRateThinWithCost manuscriptCountThinWithCost

end Kr25Ssmxt
