import Kr25Ssmxt.Model.Prelude
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

/-- A certified precision satisfies both geometric uses in the algorithm. -/
structure PrecisionChoice {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) where
  value : Nat
  adequate : PrecisionAdequate D value p.latticeEta p.epsilonPrime

/-- Certified deterministic preprocessing carried out by TTC, rather than supplied per input. -/
structure TTCPreprocessor (n k : Nat) where
  booleanAbstraction : (F : LRAFormula n k) → BooleanAbstraction F
  toDNF : {F : LRAFormula n k} → (A : BooleanAbstraction F) → DNFResult A
  normalize : {F : LRAFormula n k} → (A : BooleanAbstraction F) →
    DNFResult A → Bornology.IsBounded (solutionSet F) → Decomposition F
  choosePrecision : {F : LRAFormula n k} → (D : Decomposition F) →
    (p : ApproxParams) → PrecisionChoice D p

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

/-- A batch's samples are IID from one law after conditioning on its good tag. -/
def IIDBatchOnGood {n count : Nat} (law : Measure (SampleBatch n count))
    (pointLaw : Measure (LatticePoint n)) : Prop :=
  (ProbabilityTheory.cond law {o | o.1 = true}).map Prod.snd =
    Measure.pi (fun _ : Fin count => pointLaw)

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

/-- The required batch-level, pointwise, conditionally IID sampling guarantee.

The repaired paper's Hit-and-Run construction is unconditional: independent restarts yield
the product law and its tag can be constantly true, making the failure bound below zero.
-/
def GenerateSamplesContract {n k : Nat} (O : TTCOracles n k)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) : Prop :=
  let D := O.preprocessing.run F hbounded
  let b := (O.preprocessing.choosePrecision D p).value
  ∀ (i) (count : Nat),
    let law := O.generateSamples (D.component i) count b p.epsilonPrime
      (p.deltaPrime D.componentCount)
    IsProbabilityMeasure law ∧
      law.real {o | o.1 = false} ≤ p.deltaPrime D.componentCount ∧
      ∃ pointLaw : Measure (LatticePoint n),
        AlmostUniformPointwise pointLaw
          (codedLatticePoints (D.component i) b) p.epsilonPrime ∧
        IIDBatchOnGood law pointLaw

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

/-- The public estimator `|X| / p`. -/
def TTCState.estimate {n : Nat} (s : TTCState n) : NNReal :=
  (s.samples.card : NNReal) / s.rate

/-- Initial state: dyadic rate one and an empty retained multiset. -/
def TTCState.initial (n : Nat) : TTCState n where
  rate := 1
  samples := ∅
  nextLabel := 0

/-- The lattice count converted back to the ambient volume scale. -/
def scaledLatticeVolume {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (b : Nat) : NNReal :=
  (D.latticePoints b).ncard / (10 : NNReal) ^ (b * n)

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

/-- One component iteration of `ttcCore`. -/
def processComponent {n k : Nat} (O : TTCOracles n k) (b : Nat)
    (epsilonPrime deltaPrime threshold : Real) (P : PolytopeData n)
    (state : TTCState n) : Measure (TTCState n) :=
  (O.computeVolume P epsilonPrime deltaPrime).bind fun volumeOutcome =>
    let withoutDuplicates := state.removeComponent P
    (ProbabilityTheory.poissonMeasure (volumeOutcome.2 * withoutDuplicates.rate)).bind fun pending =>
      (thinUntil withoutDuplicates pending threshold).bind fun thinned =>
        (O.generateSamples P thinned.2 b epsilonPrime deltaPrime).bind fun batch =>
          (thinUntil (thinned.1.addBatch batch.2) 0 threshold).map Prod.fst

/-- Sequentially process the normalized components in DNF order. -/
def processComponents {n k : Nat} (O : TTCOracles n k) (b : Nat)
    (epsilonPrime deltaPrime threshold : Real) :
    List (PolytopeData n) → TTCState n → Measure (TTCState n)
  | [], state => Measure.dirac state
  | P :: rest, state =>
      (processComponent O b epsilonPrime deltaPrime threshold P state).bind
        (processComponents O b epsilonPrime deltaPrime threshold rest)

/--
The theoretical TTC output law.  The empty normalized family returns zero before any
division by `m`; otherwise it selects a repaired precision, executes the streaming core,
and returns exactly the single nonnegative estimate `|X| / p`.  Accuracy for the nonempty
branch is conditional on the public high-intensity premise.
-/
def ttc {n k : Nat} (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F)) (params : ApproxParams)
    (O : TTCOracles n k) : Measure NNReal :=
  let D := O.preprocessing.run F hbounded
  if D.componentCount = 0 then
    Measure.dirac 0
  else
    let b := (O.preprocessing.choosePrecision D params).value
    (processComponents O b params.epsilonPrime (params.deltaPrime D.componentCount)
      (params.threshold D.componentCount) (List.ofFn D.component) (TTCState.initial n)).map
        TTCState.estimate

/-! ## TTC as printed in the current manuscript

The older `ttc` core above remains the subject of the existing streaming proof chain.
The definitions below give the changed algorithm its own law, so that a theorem about
the older core cannot be mistaken for a theorem about the manuscript program. -/

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

/--
The nontrivial probabilistic result supplied by the Poissonized finite-union streaming
analysis.  It is restricted to the regime in which the initial scaled lattice volume is
large enough for the paper's dyadic concentration argument.  This condition is now a public
premise of the headline accuracy theorem; the algorithm does not compute it.

This is deliberately a named proposition rather than an axiom.  The headline theorem takes
its proof through `Prior`, making the borrowed streaming result part of the public theorem
assumptions.
-/
def StreamingCoreAccuracy
    {n k : Nat}
    (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (params : ApproxParams)
    (O : TTCOracles n k) : Prop :=
  let D := O.preprocessing.run F hbounded
  let b := (O.preprocessing.choosePrecision D params).value
  ComputeVolumeContract O F hbounded params →
    GenerateSamplesContract O F hbounded params →
    D.componentCount ≠ 0 →
    (∀ i,
      (volume (D.component i).carrier).toReal ∈
        Arlib.relErr params.latticeEta
          (((D.component i).carrier ∩ decimalLattice b n).ncard /
            (10 : Real) ^ (b * n))) →
    params.threshold D.componentCount / 4 ≤ (scaledLatticeVolume D b : Real) →
    let core := processComponents O b params.epsilonPrime
      (params.deltaPrime D.componentCount) (params.threshold D.componentCount)
      (List.ofFn D.component) (TTCState.initial n)
    (core.map TTCState.estimate).real
        {estimate | (estimate : Real) ∈
          Arlib.relErr (params.epsilon / 2) (scaledLatticeVolume D b : Real)} ≥
      1 - params.delta

#krModelClosure ttc
#krModelClosure manuscriptTTC

end Kr25Ssmxt

/-!
# Prior work used by the TTC analysis

A borrowed result is separated from the program body: it appears as a field here and
therefore remains visible in the headline theorem rather than as an axiom hidden in a proof.
-/

namespace Kr25Ssmxt

/-- Every result this development takes from prior work rather than proving. -/
structure Prior : Prop where
  streamingCoreAccuracy :
    ∀ {n k : Nat} (F : LRAFormula n k)
      (hbounded : Bornology.IsBounded (solutionSet F))
      (params : ApproxParams) (O : TTCOracles n k),
      StreamingCoreAccuracy F hbounded params O

#krSurplusIn Kr25Ssmxt.Model.Program from ttc manuscriptTTC StreamingCoreAccuracy Prior
  manuscriptRateThinWithCost manuscriptCountThinWithCost

end Kr25Ssmxt
