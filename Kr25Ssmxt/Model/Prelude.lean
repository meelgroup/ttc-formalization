import Arlib.Prelude
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.ProductMeasure
import Kr25Ssmxt.Meta.ModelClosure
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.MetricSpace.Bounded

/-!
# TTC model vocabulary

This audit surface uses finite syntax for QF-LRA and Mathlib's actual Euclidean,
set, metric, and measure notions.  A normalized component is represented by its
finite closed-halfspace presentation together with a certified positive inball
and boundedness.  This makes the paper's lattice arguments statements about the
same carriers whose Lebesgue volume appears in the headline, rather than about
an unrelated abstract collection of sets.
-/

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory

namespace Kr25Ssmxt

/-! ## Vocabulary -/

/-- Points in the positive-dimensional real ambient space used by the paper. -/
abbrev Point (n : Nat) := Fin n → Real

/-- The five relations admitted by quantifier-free linear-real arithmetic. -/
inductive LinearRelation where
  | lt | le | eq | ge | gt
  deriving DecidableEq

/-- A linear-real atom `a · x rel c`. -/
structure LinearAtom (n : Nat) where
  coefficients : Point n
  relation : LinearRelation
  constant : Real

/-- The finite QF-LRA syntax, including pure Boolean variables. -/
inductive LRAFormula (n k : Nat) where
  | atom : LinearAtom n → LRAFormula n k
  | boolVar : Fin k → LRAFormula n k
  | truth : LRAFormula n k
  | falsity : LRAFormula n k
  | neg : LRAFormula n k → LRAFormula n k
  | and : LRAFormula n k → LRAFormula n k → LRAFormula n k
  | or : LRAFormula n k → LRAFormula n k → LRAFormula n k

/-- Truth of a linear atom at a real point. -/
def LinearAtom.Holds {n : Nat} (A : LinearAtom n) (x : Point n) : Prop :=
  match A.relation with
  | .lt => dotProduct A.coefficients x < A.constant
  | .le => dotProduct A.coefficients x ≤ A.constant
  | .eq => dotProduct A.coefficients x = A.constant
  | .ge => dotProduct A.coefficients x ≥ A.constant
  | .gt => dotProduct A.coefficients x > A.constant

/-- Satisfaction uses a valuation only for the pure Boolean variables. -/
def LRAFormula.Satisfies {n k : Nat} :
    LRAFormula n k → (Fin k → Bool) → Point n → Prop
  | .atom A, _, x => A.Holds x
  | .boolVar i, β, _ => β i = true
  | .truth, _, _ => True
  | .falsity, _, _ => False
  | .neg F, β, x => ¬ F.Satisfies β x
  | .and F G, β, x => F.Satisfies β x ∧ G.Satisfies β x
  | .or F G, β, x => F.Satisfies β x ∨ G.Satisfies β x

/-- Pure Boolean variables are existentially projected out of the geometric set. -/
def solutionSet {n k : Nat} (F : LRAFormula n k) : Set (Point n) :=
  {x | ∃ β : Fin k → Bool, F.Satisfies β x}

/-- Generic finite propositional syntax used by Boolean abstraction. -/
inductive BoolFormula (α : Type*) where
  | atom : α → BoolFormula α
  | truth : BoolFormula α
  | falsity : BoolFormula α
  | neg : BoolFormula α → BoolFormula α
  | and : BoolFormula α → BoolFormula α → BoolFormula α
  | or : BoolFormula α → BoolFormula α → BoolFormula α

/-- Evaluation of finite propositional syntax. -/
def BoolFormula.Holds {α : Type*} : BoolFormula α → (α → Prop) → Prop
  | .atom a, v => v a
  | .truth, _ => True
  | .falsity, _ => False
  | .neg F, v => ¬ F.Holds v
  | .and F G, v => F.Holds v ∧ G.Holds v
  | .or F G, v => F.Holds v ∨ G.Holds v

/-- An abstracted input is either a theory atom or a pure Boolean input. -/
inductive AbstractAtom (n k : Nat) where
  | theory : LinearAtom n → AbstractAtom n k
  | pure : Fin k → AbstractAtom n k

/-- Semantics of one input of the Boolean abstraction. -/
def AbstractAtom.Holds {n k : Nat} (A : AbstractAtom n k)
    (β : Fin k → Bool) (x : Point n) : Prop :=
  match A with
  | .theory atom => atom.Holds x
  | .pure i => β i = true

/-- The paper's Boolean abstraction together with its static semantic certificate. -/
structure BooleanAbstraction {n k : Nat} (F : LRAFormula n k) where
  atomCount : Nat
  circuit : BoolFormula (Fin atomCount)
  source : Fin atomCount → AbstractAtom n k
  correct : ∀ β x, circuit.Holds (fun i => (source i).Holds β x) ↔ F.Satisfies β x

/-- A signed propositional literal. -/
structure Literal (α : Type*) where
  atom : α
  positive : Bool

/-- Truth of a signed literal. -/
def Literal.Holds {α : Type*} (l : Literal α) (v : α → Prop) : Prop :=
  if l.positive then v l.atom else ¬ v l.atom

/-- A DNF cube is a finite conjunction of signed literals. -/
abbrev Cube (α : Type*) := List (Literal α)

/-- Truth of a DNF cube. -/
def Cube.Holds {α : Type*} (C : Cube α) (v : α → Prop) : Prop :=
  ∀ l ∈ C, l.Holds v

/-- Truth of a finite list of DNF cubes. -/
def dnfHolds {α : Type*} (D : List (Cube α)) (v : α → Prop) : Prop :=
  ∃ C ∈ D, C.Holds v

/-- A certified result of converting the abstract Boolean circuit to DNF. -/
structure DNFResult {n k : Nat} {F : LRAFormula n k} (A : BooleanAbstraction F) where
  cubes : List (Cube (Fin A.atomCount))
  correct : ∀ v, dnfHolds cubes v ↔ A.circuit.Holds v

/-- A finite presentation by closed halfspaces `normal i · x ≤ offset i`. -/
structure HalfspacePresentation (n : Nat) where
  facetCount : Nat
  normal : Fin facetCount → Point n
  offset : Fin facetCount → Real

/-- The carrier of a closed-halfspace presentation. -/
def HalfspacePresentation.carrier {n : Nat} (H : HalfspacePresentation n) : Set (Point n) :=
  {x | ∀ i, dotProduct (H.normal i) x ≤ H.offset i}

/-- A surviving normalized component, with the geometric read-offs used by the paper.

`outerRadius` is an explicit preprocessing certificate, rather than merely a consequence
of `bounded`.  CV18's cooling schedule and running-time bound depend quantitatively on this
number, so hiding it behind classical choice would not describe an executable algorithm. -/
structure PolytopeData (n : Nat) where
  presentation : HalfspacePresentation n
  facets_pos : 0 < presentation.facetCount
  incenter : Point n
  inradius : Real
  inradius_pos : 0 < inradius
  inball : Metric.closedBall incenter inradius ⊆ presentation.carrier
  bounded : Bornology.IsBounded presentation.carrier
  outerRadius : Real
  outerRadius_nonneg : 0 ≤ outerRadius
  outer_bound : ∀ x ∈ presentation.carrier,
    ‖(WithLp.toLp 2 x : EuclideanSpace Real (Fin n))‖ ≤ outerRadius

/-- The geometric carrier of a normalized component. -/
abbrev PolytopeData.carrier {n : Nat} (P : PolytopeData n) : Set (Point n) :=
  P.presentation.carrier

/-- A normalized finite family whose union agrees almost everywhere with the formula.

An empty family is permitted and is the exact zero-volume branch.  Every component in a
nonempty family is already bounded, nonempty, and full-dimensional by `PolytopeData`.
-/
structure Decomposition {n k : Nat} (F : LRAFormula n k) where
  componentCount : Nat
  component : Fin componentCount → PolytopeData n
  solution_ae : ∀ᵐ x ∂(volume : Measure (Point n)),
    x ∈ ⋃ i, (component i).carrier ↔ x ∈ solutionSet F

/-- The union `Q` of all normalized components. -/
def Decomposition.union {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) : Set (Point n) :=
  ⋃ i, (D.component i).carrier

/-- The axis-parallel decimal lattice `10⁻ᵇ ℤⁿ`. -/
def decimalLattice (b n : Nat) : Set (Point n) :=
  {x | ∀ i, ∃ z : Int, x i = (z : Real) / (10 : Real) ^ b}

/-- The final lattice-point set `Q ∩ L_b^n`. -/
def Decomposition.latticePoints {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (b : Nat) : Set (Point n) :=
  D.union ∩ decimalLattice b n

/-- Total number of halfspaces in the chosen presentations. -/
def Decomposition.totalFacets {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) : Nat :=
  ∑ i, (D.component i).presentation.facetCount

/-- External accuracy and confidence parameters. -/
structure ApproxParams where
  epsilon : Real
  delta : Real
  epsilon_pos : 0 < epsilon
  epsilon_le_one : epsilon ≤ 1
  delta_pos : 0 < delta
  delta_le_one : delta ≤ 1

/-- The paper's internal relative-error parameter `ε' = ε / 12`. -/
def ApproxParams.epsilonPrime (p : ApproxParams) : Real := p.epsilon / 12

/-- The lattice comparison parameter `η = ε / 8`. -/
def ApproxParams.latticeEta (p : ApproxParams) : Real := p.epsilon / 8

/-- The per-component failure budget `δ' = δ / (4m)`; used only when `m > 0`. -/
def ApproxParams.deltaPrime (p : ApproxParams) (m : Nat) : Real := p.delta / (4 * m)

/-- The threshold printed in Algorithm `ttc`; used only in the nonempty branch. -/
def ApproxParams.threshold (p : ApproxParams) (m : Nat) : Real :=
  max (24 * Real.log (24 / p.delta) /
      ((1 - p.epsilonPrime) * p.epsilonPrime ^ 2))
    (15 * (Real.log (6 / p.delta) + Real.log m))

/-- The inball size required by the finite-union lattice comparison. -/
def latticeRadiusRequirement {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (η : Real) : Real :=
  (64 * D.componentCount * n / η) *
    Real.sqrt (Real.log (4 * D.totalFacets / η))

/-- The stronger inball size required by the pointwise lattice sampler. -/
def samplerRadiusRequirement {n : Nat} (P : PolytopeData n) (η : Real) : Real :=
  (512 * n / η) *
    Real.sqrt (Real.log (32 * P.presentation.facetCount / η))

/-- The useful specification of a working precision: both cited geometric results apply. -/
def PrecisionAdequate {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (b : Nat) (latticeEta sampleEta : Real) : Prop :=
  ∀ i, max (latticeRadiusRequirement D latticeEta)
      (samplerRadiusRequirement (D.component i) sampleEta) ≤
    (10 : Real) ^ b * (D.component i).inradius

/-! ## Runtime vocabulary -/

namespace TTCRuntime

/-- One polytope membership query scans every facet and costs `dimension * facets`
real-arithmetic operations in the paper's cost model. -/
def membershipQueryOperations (dimension facets queries : Nat) : Nat :=
  dimension * facets * queries

/-- Cost of one accepted sample: its Hit-and-Run transitions and final membership test,
multiplied by the integer upper bound `2` on the paper's expected rejection count. -/
def acceptedSampleOperations (dimension facets steps : Nat) : Nat :=
  2 * membershipQueryOperations dimension facets (steps + 1)

/-- Model-level trace of TTC's geometric calls. -/
structure TTCMembershipRuntimeCertificate {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) where
  volumeQueryCount : Fin D.componentCount → Nat
  samplerStepCount : Fin D.componentCount → Nat

/-- Maximum number of accepted samples charged per component. -/
def sampleCap (p : ApproxParams) (componentCount : Nat) : Nat :=
  Nat.ceil (p.threshold componentCount)

/-- Total geometric-oracle operations represented by a runtime trace. -/
def TTCMembershipRuntimeCertificate.operations {n k : Nat} {F : LRAFormula n k}
    {D : Decomposition F} {p : ApproxParams}
    (cert : TTCMembershipRuntimeCertificate D p) : Nat :=
  ∑ i : Fin D.componentCount,
    (membershipQueryOperations n (D.component i).presentation.facetCount
        (cert.volumeQueryCount i) +
      sampleCap p D.componentCount *
        acceptedSampleOperations n (D.component i).presentation.facetCount
          (cert.samplerStepCount i))

/-- Volume kernel in Theorem 3 before facets and suppressed factors. -/
def theorem3VolumeKernel (n : Nat) (rho epsilon : Real) : Real :=
  max ((n : Real) ^ 3 * rho ^ 2) ((n : Real) ^ 4) / epsilon ^ 2

/-- Per-sample kernel in Theorem 3. -/
def theorem3SamplingKernel (n : Nat) (rho : Real) : Real :=
  (n : Real) ^ 5 * rho ^ 2

/-- Exact multiplier containing the factors suppressed by the paper's `O` notation. -/
def theorem3SuppressedFactor (epsilon threshold volumeOverhead samplingOverhead : Real) :
    Real :=
  volumeOverhead / epsilon ^ 2 + threshold * samplingOverhead

/-- Geometric monomial in the headline statement of Theorem 3. -/
def theorem3HeadlineCore (componentCount n rMax : Nat) (rho : Real) : Real :=
  (componentCount : Real) * (n : Real) ^ 5 * rho ^ 2 * rMax

/-- Componentwise oracle estimates assumed by the model-level statement of Theorem 3. -/
structure Theorem3OracleBounds {n k : Nat} {F : LRAFormula n k}
    {D : Decomposition F} {p : ApproxParams}
    (cert : TTCMembershipRuntimeCertificate D p) (rho : Real) (rMax : Nat) where
  one_le_rho : 1 ≤ rho
  volumeOverhead : Real
  volumeOverhead_nonneg : 0 ≤ volumeOverhead
  samplingOverhead : Real
  samplingOverhead_nonneg : 0 ≤ samplingOverhead
  facets_le : ∀ i, (D.component i).presentation.facetCount ≤ rMax
  volume_operations_le : ∀ i,
    (membershipQueryOperations n (D.component i).presentation.facetCount
        (cert.volumeQueryCount i) : Real) ≤
      ((D.component i).presentation.facetCount : Real) * volumeOverhead *
        theorem3VolumeKernel n rho p.epsilon
  sample_operations_le : ∀ i,
    (acceptedSampleOperations n (D.component i).presentation.facetCount
        (cert.samplerStepCount i) : Real) ≤
      ((D.component i).presentation.facetCount : Real) * samplingOverhead *
        theorem3SamplingKernel n rho

end TTCRuntime

end Kr25Ssmxt

/-!
# The theoretical TTC algorithm

The encoding follows the paper's mathematical control flow.  Boolean abstraction, DNF
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

#modelClosure ttc

end Kr25Ssmxt
