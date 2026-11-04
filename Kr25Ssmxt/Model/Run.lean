import Kr25Ssmxt.Model.Program
import Mathlib.Probability.Distributions.Geometric
import ArlibCommunity.Algorithms.CV18
import ArlibCommunity.Algorithms.HitAndRun.Model.Theorem
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Lattice.KV97.Inflate
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Lattice.Rounding.RoundLaw
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.PointwiseRoute
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Probability.Rejection

/-!
# The concrete TTC run

This file is the executable part of the audit surface. It imports the current
arlib-community CV18 and Hit-and-Run algorithms directly and adapts their laws to TTC's
component representation. Proofs that these definitions meet TTC's contracts remain under
`Analysis/`; no TTC definition in this file depends on an `Analysis/` declaration.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory InnerProductSpace

namespace Kr25Ssmxt

/-! ## Executable polytope bridges -/

/-- The coordinate identity from TTC's product space to arlib's Euclidean space. -/
def toEuclidean {n : Nat} (x : Point n) : EuclideanSpace Real (Fin n) :=
  WithLp.toLp 2 x

/-- A TTC facet normal in arlib's Euclidean representation. -/
def PolytopeData.arlibNormal {n : Nat} (P : PolytopeData n) :
    Fin P.presentation.facetCount → EuclideanSpace Real (Fin n) :=
  fun i => toEuclidean (P.presentation.normal i)

/-- The positive dilation carrying the precision-`b` decimal lattice to `ℤⁿ`. -/
def decimalScale (b : Nat) : Real := (10 : Real) ^ b

/-- Facet offsets of the decimal-dilated body. -/
def PolytopeData.scaledOffset {n : Nat} (P : PolytopeData n) (b : Nat) :
    Fin P.presentation.facetCount → Real :=
  fun i => decimalScale b * P.presentation.offset i

/-- The arlib body obtained by scaling every point of `P` by `10^b`. -/
def PolytopeData.scaledBody {n : Nat} (P : PolytopeData n) (b : Nat) :
    Set (EuclideanSpace Real (Fin n)) :=
  Arlib.Polytope.body P.arlibNormal (P.scaledOffset b)

/-- Pull the component back along `y ↦ inradius • y + incenter`. -/
def PolytopeData.cv18Body {n : Nat} (P : PolytopeData n) :
    Set (EuclideanSpace Real (Fin n)) :=
  (fun y => P.inradius • y + toEuclidean P.incenter) ⁻¹'
    Arlib.Polytope.body P.arlibNormal P.presentation.offset

/-! ## Direct CV18 law -/

namespace CommunityCV18

open ArlibCommunity.Algorithms.CV18

/-- The parameter regime of every CV18 call made by TTC. -/
def AdmissibleCV18Request (eta delta : Real) : Prop :=
  0 < eta ∧ eta ≤ 1 ∧ 0 < delta ∧ delta ≤ 1

/-- A positive roundness value computed from the actual normalized body. -/
noncomputable def roundness {n : Nat} (P : PolytopeData n) : Real :=
  |(∫ x in P.cv18Body, ‖x‖ ^ 2) / (volume P.cv18Body).toReal| + 1

/-- The CV18 parameters used by TTC. -/
def params {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (eta delta : Real) (h : AdmissibleCV18Request eta delta) : VolumeParams where
  n := n
  dim_ok := hn
  eps := eta / 2
  heps := ⟨div_pos h.1 (by norm_num), by linarith [h.2.1]⟩
  p := delta / 2
  hp := ⟨div_pos h.2.2.1 (by norm_num), by linarith [h.2.2.2]⟩
  roundness := roundness P
  roundness_pos := by unfold roundness; positivity

/-- The current scheduled, capped, amplified CV18 membership-oracle program. -/
def algorithm : VolumeAlgorithm :=
  amplifyOracleProgram figureOneFinalScheduledCappedValueProgram

/-- The syntax-derived worst-case membership-query budget of the concrete amplified
CV18 program.  The two factors are, respectively, the number of confidence repetitions
and the query cap of one scheduled execution. -/
def queryBudget (q : VolumeParams) : Nat :=
  confidenceRepetitions q * figureOneFinalScheduledQueryBudget q

/-- The concrete CV18 query budget for a TTC request.  The zero branch agrees with the
total fallback branch of `communityCV18VolumeLaw`. -/
def queryBudgetFor {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (eta delta : Real) : Nat := by
  classical
  exact if h : AdmissibleCV18Request eta delta then
    queryBudget (params hn P eta delta h)
  else
    0

/-- Every component request made by TTC is within the imported CV18
parameter domain. -/
theorem admissibleTTCRequest {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (i : Fin D.componentCount) :
    AdmissibleCV18Request p.epsilonPrime (p.deltaPrime D.componentCount) := by
  have hcount : 0 < D.componentCount := lt_of_le_of_lt (Nat.zero_le i) i.isLt
  have hdenom : 0 < (4 * D.componentCount : Real) := by
    exact_mod_cast Nat.mul_pos (by norm_num : 0 < 4) hcount
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact div_pos p.epsilon_pos (by norm_num)
  · dsimp only [ApproxParams.epsilonPrime]
    linarith [p.epsilon_le_one]
  · exact div_pos p.delta_pos hdenom
  · dsimp only [ApproxParams.deltaPrime]
    rw [div_le_iff₀ hdenom]
    have hcountR : (1 : Real) ≤ D.componentCount := by exact_mod_cast hcount
    nlinarith [p.delta_le_one]

/-- Exact finite-facet membership in the normalized TTC component. -/
noncomputable def query {n : Nat} (P : PolytopeData n) :
    EuclideanSpace Real (Fin n) → Bool := by
  classical
  exact fun x => if x ∈ P.cv18Body then true else false

/-- The estimator law obtained by running the imported CV18 program. -/
def law {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (eta delta : Real) (h : AdmissibleCV18Request eta delta) : Measure Real :=
  (algorithm (params hn P eta delta h)).runEstimate (query P)

/-- The concrete success event used to tag the CV18 estimate. -/
def successSet {n : Nat} (P : PolytopeData n) (eta : Real) : Set Real :=
  {estimate | estimate ∈ Arlib.relErr (eta / 2) (volume P.cv18Body).toReal}

/-- Boolean tag for membership in the CV18 success event. -/
noncomputable def successTag {n : Nat} (P : PolytopeData n) (eta : Real)
    (estimate : Real) : Bool := by
  classical
  exact if estimate ∈ successSet P eta then true else false

/-- CV18's estimator law with TTC's success tag and nonnegative output type. -/
def taggedLaw {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (eta delta : Real) (h : AdmissibleCV18Request eta delta) : Measure VolumeOutcome :=
  (law hn P eta delta h).map fun estimate =>
    (successTag P eta estimate, Real.toNNReal estimate)

end CommunityCV18

/-- The six logarithmic factors in the scheduled amplified CV18 query rate.
The exact terminal scale and block mixing error are retained. -/
noncomputable def TTCRuntime.theorem3CV18LogEnvelope
    (q : ArlibCommunity.Algorithms.CV18.VolumeParams) : Real :=
  ArlibCommunity.Algorithms.CV18.protectedLog (1 / q.p) *
  ArlibCommunity.Algorithms.CV18.protectedLog (1 / q.eps) ^ 2 *
  ArlibCommunity.Algorithms.CV18.protectedLog ((q.n : Real) / q.eps) ^ 2 *
  ArlibCommunity.Algorithms.CV18.protectedLog
    (ArlibCommunity.Algorithms.CV18.volumeTerminalScale q) ^ 2 *
  ArlibCommunity.Algorithms.CV18.figureOneScheduledAccuracyLog q *
  ArlibCommunity.Algorithms.CV18.protectedLog
    (1 / ArlibCommunity.Algorithms.CV18.figureOneCorrectedBlockMixingError q
      (ArlibCommunity.Algorithms.CV18.figureOneSafeRetryCount q - 1)) ^ 2

/-- Explicit TTC CV18 query envelope obtained by inserting `ρ` into the
imported scheduled complexity rate. -/
noncomputable def TTCRuntime.theorem3CV18QueryEnvelope
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams) (i : Fin D.componentCount) : Nat :=
  let q := CommunityCV18.params (by omega) (D.component i) p.epsilonPrime
    (p.deltaPrime D.componentCount) (CommunityCV18.admissibleTTCRequest D p i)
  Nat.ceil (45 * (64 *
    ArlibCommunity.Algorithms.CV18.figureOneFinalScheduledExpectedCostConstant
    + 1) *
    (n : Real) ^ 3 * (TTCRuntime.theorem3Rho D) ^ 2 / (p.epsilonPrime / 2) ^ 2 *
    TTCRuntime.theorem3CV18LogEnvelope q)

/-- Largest of the explicit scheduled CV18 logarithmic products across TTC's
normalized components. The empty family's value is zero. -/
noncomputable def TTCRuntime.theorem3CV18LogMax
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams) : Real :=
  ((Finset.univ.sup fun i : Fin D.componentCount =>
    let q := CommunityCV18.params (by omega) (D.component i) p.epsilonPrime
      (p.deltaPrime D.componentCount) (CommunityCV18.admissibleTTCRequest D p i)
    Real.toNNReal (TTCRuntime.theorem3CV18LogEnvelope q) : NNReal) : Real)

/-- Uniform CV18 query cap after maximizing only its logarithmic product
over components. -/
noncomputable def TTCRuntime.theorem3CV18QueryMax
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams) : Nat :=
  Nat.ceil (45 * (64 *
    ArlibCommunity.Algorithms.CV18.figureOneFinalScheduledExpectedCostConstant
    + 1) *
    (n : Real) ^ 3 * (TTCRuntime.theorem3Rho D) ^ 2 / (p.epsilonPrime / 2) ^ 2 *
    TTCRuntime.theorem3CV18LogMax hn D p)

/-- The positive determinant of TTC's inverse normalization chart. -/
def PolytopeData.cv18VolumeScale {n : Nat} (P : PolytopeData n) : NNReal :=
  ⟨P.inradius ^ n, pow_nonneg P.inradius_pos.le n⟩

/-- Preserve the success tag and rescale a normalized-body estimate. -/
def PolytopeData.rescaleCV18Outcome {n : Nat} (P : PolytopeData n)
    (o : VolumeOutcome) : VolumeOutcome :=
  (o.1, P.cv18VolumeScale * o.2)

/-- Push a normalized-body estimator law through determinant rescaling. -/
def PolytopeData.rescaleCV18Law {n : Nat} (P : PolytopeData n)
    (mu : Measure VolumeOutcome) : Measure VolumeOutcome :=
  mu.map P.rescaleCV18Outcome

/-- The total concrete CV18 call used by TTC. -/
def communityCV18VolumeLaw {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (eta delta : Real) : Measure VolumeOutcome := by
  classical
  exact if h : CommunityCV18.AdmissibleCV18Request eta delta then
    P.rescaleCV18Law (CommunityCV18.taggedLaw hn P eta delta h)
  else
    Measure.dirac (true, 0)

/-- The concrete query budget really bounds every charged execution of the CV18 program.
This is the cost claim used by the public runtime theorem; it contains no caller-supplied
oracle estimate. -/
def CommunityCV18.MembershipCostCertified {n : Nat} (hn : 3 ≤ n)
    (P : PolytopeData n) (eta delta : Real) : Prop := by
  classical
  exact if h : CommunityCV18.AdmissibleCV18Request eta delta then
      (CommunityCV18.algorithm
        (CommunityCV18.params hn P eta delta h)).MembershipCostBound
        (CommunityCV18.queryBudgetFor hn P eta delta)
    else
      True

/-! ## Direct finite-step Hit-and-Run/KV97 law -/

open Arlib.Lattice.Rounding

/-- The integer lattice embedded in arlib's Euclidean state space. -/
def kv97LatEmb (n : Nat) (z : Fin n → Int) : EuclideanSpace Real (Fin n) :=
  WithLp.toLp 2 fun i => (z i : Real)

/-- The current community randomized-rounding law as a Markov kernel. -/
def kv97RoundingKernel (n : Nat) :
    Kernel (EuclideanSpace Real (Fin n)) (Fin n → Int) where
  toFun p := roundLaw (WithLp.ofLp p)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have heq : (fun p : EuclideanSpace Real (Fin n) => roundLaw (WithLp.ofLp p) s) =
        fun p => ∑' z : Fin n → Int,
          s.indicator (fun z => roundLaw (WithLp.ofLp p) {z}) z := by
      funext p
      exact (Measure.tsum_indicator_apply_singleton (roundLaw (WithLp.ofLp p)) s hs).symm
    rw [heq]
    apply Measurable.tsum
    intro z
    by_cases hz : z ∈ s
    · simp only [Set.indicator_of_mem hz, roundLaw_singleton]
      change Measurable fun p => ENNReal.ofReal (prodTent (kv97LatEmb n z) p)
      exact (measurable_prodTent (kv97LatEmb n z)).ennreal_ofReal
    · simp only [Set.indicator_of_notMem hz]
      fun_prop

instance (n : Nat) : IsMarkovKernel (kv97RoundingKernel n) := by
  constructor
  intro p
  change IsProbabilityMeasure (roundLaw (WithLp.ofLp p))
  infer_instance

/-- Draw from a continuous law, then round every coordinate independently. -/
def kv97RoundedMeasureLaw {n : Nat}
    (mu : Measure (EuclideanSpace Real (Fin n))) : Measure (Fin n → Int) :=
  mu.bind (kv97RoundingKernel n)

/-- Attach TTC's decimal precision to an integer vector returned by KV97. -/
def encodeInteger {n : Nat} (b : Nat) (z : Fin n → Int) : LatticePoint n := (b, z)

/-- Integer vectors accepted by rejection from the scaled TTC component. -/
def acceptedIntegers {n : Nat} (P : PolytopeData n) (b : Nat) : Set (Fin n → Int) :=
  {z | kv97LatEmb n z ∈ P.scaledBody b}

/-- Round, reject outside the scaled component, and attach TTC's precision code. -/
def acceptedRoundedLatticeLaw {n : Nat}
    (mu : Measure (EuclideanSpace Real (Fin n))) (P : PolytopeData n) (b : Nat) :
    Measure (LatticePoint n) :=
  (Arlib.condOn (kv97RoundedMeasureLaw mu) (acceptedIntegers P b)).map
    (encodeInteger b)

/-- The success probability of a rounded proposal, clamped into the unit
interval so the retry law is total even outside the certified sampler regime. -/
def roundedAcceptanceProbability {n : Nat}
    (mu : Measure (EuclideanSpace Real (Fin n))) (P : PolytopeData n) (b : Nat) :
    unitInterval :=
  ⟨min 1 (max 0 ((kv97RoundedMeasureLaw mu).real (acceptedIntegers P b))),
    ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩⟩

/-- A geometric number of failed proposals followed by one accepted rounded
point. The first marginal is the existing conditional sampler law. -/
def acceptedRoundedWithAttempts {n : Nat}
    (mu : Measure (EuclideanSpace Real (Fin n))) (P : PolytopeData n) (b : Nat) :
    Measure (LatticePoint n × Nat) :=
  ((ProbabilityTheory.geometricMeasure (roundedAcceptanceProbability mu P b)).prod
    (acceptedRoundedLatticeLaw mu P b)).map fun pair => (pair.2, pair.1 + 1)

/-- The inflated KV97 body sampled by TTC. -/
def hitAndRunBody {n : Nat} (P : PolytopeData n) (b : Nat) (eta : Real) :
    Set (EuclideanSpace Real (Fin n)) :=
  Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b)
    (Arlib.KV97.cOf eta) (P.presentation.facetCount : Real)

/-- The explicitly inflated offsets scanned by the finite-facet implementation. -/
def hitAndRunOffset {n : Nat} (P : PolytopeData n) (b : Nat) (eta : Real) :
    Fin P.presentation.facetCount → Real :=
  fun i => P.scaledOffset b i +
    Arlib.KV97.kappaOf (Arlib.KV97.cOf eta) (P.presentation.facetCount : Real) *
      ‖P.arlibNormal i‖

/-! ## Similarity-normalized finite-facet walk

The manuscript's sampler bound uses the ratio of outer and inner radii. The
chart below gives its walk a unit inball before selecting its deadline.
`Analysis/NormalizedHitAndRunGeometry.lean` proves the mapped law satisfies
the KV97 TV contract. -/

/-- Radius and center of the inscribed ball after decimal dilation. -/
def PolytopeData.scaledInradius {n : Nat} (P : PolytopeData n) (b : Nat) : Real :=
  decimalScale b * P.inradius

def PolytopeData.scaledIncenter {n : Nat} (P : PolytopeData n) (b : Nat) :
    EuclideanSpace Real (Fin n) :=
  decimalScale b • toEuclidean P.incenter

/-- The positive similarity from normalized to decimal-scaled coordinates. -/
def PolytopeData.samplerChart {n : Nat} (P : PolytopeData n) (b : Nat)
    (y : EuclideanSpace Real (Fin n)) : EuclideanSpace Real (Fin n) :=
  P.scaledInradius b • y + P.scaledIncenter b

/-- Facet offsets after centering and dividing by the scaled inradius. -/
def PolytopeData.normalizedHitAndRunOffset {n : Nat} (P : PolytopeData n)
    (b : Nat) (eta : Real) : Fin P.presentation.facetCount → Real :=
  fun i =>
    (hitAndRunOffset P b eta i -
      ⟪P.arlibNormal i, P.scaledIncenter b⟫_Real) / P.scaledInradius b

/-- The body on which the finite-facet walk should run for a ratio-based deadline. -/
def PolytopeData.normalizedHitAndRunBody {n : Nat} (P : PolytopeData n)
    (b : Nat) (eta : Real) : Set (EuclideanSpace Real (Fin n)) :=
  Arlib.Polytope.body P.arlibNormal (P.normalizedHitAndRunOffset b eta)

/-- The canonical geometric parameters passed to the community mixing deadline. -/
def hitAndRunDiameter {n : Nat} (P : PolytopeData n) (b : Nat) (eta : Real) : Real :=
  Metric.diam (hitAndRunBody P b eta)

def hitAndRunWarmness {n : Nat} (P : PolytopeData n) (b : Nat) (eta : Real) : Real :=
  (volume (hitAndRunBody P b eta) /
    volume (Metric.ball (decimalScale b • toEuclidean P.incenter) 1)).toReal

def hitAndRunTolerance {n : Nat} (P : PolytopeData n) (b : Nat) (eta : Real) : Real :=
  min 1 ((eta / 8) / (volume (hitAndRunBody P b eta)).toReal)

/-- The deadline selected on the unit-inball body; its diameter can be bounded
by the radius ratio rather than by `10^b` times the absolute outer radius. -/
def normalizedHitAndRunSteps {n : Nat} (P : PolytopeData n) (b : Nat)
    (eta : Real) : Nat :=
  Nat.ceil (ArlibCommunity.Algorithms.HitAndRun.deadline n
    (Metric.diam (P.normalizedHitAndRunBody b eta))
    (volume (P.normalizedHitAndRunBody b eta) /
      volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)).toReal
    (hitAndRunTolerance P b eta))

/-- Explicit logarithmic envelope for the normalized TTC sampler deadline.
The unit-ball term depends only on the dimension. -/
noncomputable def TTCRuntime.theorem3SamplerLogEnvelope
    (n b : Nat) (rho outerRadiusMax eta : Real) : Real :=
  Real.log 8 + (n : Real) * Real.log (4 * rho + 1) +
    2 * ((n : Real) * ((b : Real) * Real.log 10 + Real.log 6 +
      max 0 (Real.log outerRadiusMax)) +
      Real.log (1 + 8 / eta) +
      Real.log (1 +
        (volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)).toReal))

/-- A logarithmic factor independent of decimal precision and outer radius. -/
noncomputable def TTCRuntime.theorem3SamplerLogFactor
    (n : Nat) (rho eta : Real) : Real :=
  Real.log 8 + Real.log (4 * rho + 1) +
    2 * (Real.log 10 + Real.log 6 + 1 + Real.log (1 + 8 / eta) +
      Real.log (1 +
        (volume (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1)).toReal))

/-- The explicit factors suppressed in the corrected Theorem 3 headline after
the oracle rates and the thinning counter are put on a common scale. -/
noncomputable def TTCRuntime.theorem3ParameterFactor
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams) : Real :=
  45 * (64 *
      ArlibCommunity.Algorithms.CV18.figureOneFinalScheduledExpectedCostConstant + 1) *
      TTCRuntime.theorem3CV18LogMax hn D p / (p.epsilonPrime / 2) ^ 2 +
    (2 : Real) ^ 68 *
      (Real.log 8 + Real.log (4 * TTCRuntime.theorem3Rho D + 1) +
        2 * (Real.log 10 + Real.log 6 + 1 +
          Real.log (1 + 8 / p.epsilonPrime) + 2)) + 20

/-- The exact finite walk length selected from arlib-community's displayed deadline. -/
def hitAndRunSteps {n : Nat} (P : PolytopeData n) (b : Nat) (eta : Real) : Nat :=
  Nat.ceil (ArlibCommunity.Algorithms.HitAndRun.deadline n
    (hitAndRunDiameter P b eta) (hitAndRunWarmness P b eta)
    (hitAndRunTolerance P b eta))

/-- The runtime budgets of exactly the community implementations selected by
`communityTTC`: the syntax-derived CV18 query cap and the finite Hit-and-Run deadline. -/
def communityMembershipRuntimeCertificate {n k : Nat} (hn : 21 ≤ n)
    {F : LRAFormula n k} (D : Decomposition F) (b : Nat) (p : ApproxParams) :
    TTCRuntime.TTCMembershipRuntimeCertificate D p where
  volumeQueryCount := fun i =>
    CommunityCV18.queryBudgetFor (by omega) (D.component i)
      p.epsilonPrime (p.deltaPrime D.componentCount)
  samplerStepCount := fun i => normalizedHitAndRunSteps (D.component i) b p.epsilonPrime

/-- The imported finite-step Hit-and-Run law before randomized rounding. -/
def hitAndRunContinuousLaw {n : Nat} (P : PolytopeData n) (b : Nat) (eta : Real) :
    Measure (EuclideanSpace Real (Fin n)) :=
  Arlib.MarkovChains.iterate
    (Arlib.MarkovChains.lazy
      (ArlibCommunity.Algorithms.HitAndRun.finiteFacetStep
        P.arlibNormal (hitAndRunOffset P b eta)))
    (Arlib.uniformOn volume
      (Metric.ball (decimalScale b • toEuclidean P.incenter) 1))
    (hitAndRunSteps P b eta)

/-- The finite-facet walk in unit-inball coordinates, mapped back to the
decimal-scaled body before KV97 rounding. -/
def normalizedHitAndRunContinuousLaw {n : Nat} (P : PolytopeData n)
    (b : Nat) (eta : Real) : Measure (EuclideanSpace Real (Fin n)) :=
  (Arlib.MarkovChains.iterate
    (Arlib.MarkovChains.lazy
      (ArlibCommunity.Algorithms.HitAndRun.finiteFacetStep
        P.arlibNormal (P.normalizedHitAndRunOffset b eta)))
    (Arlib.uniformOn volume
      (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1))
    (normalizedHitAndRunSteps P b eta)).map (P.samplerChart b)

/-- TTC's one-point sampler law. Proof arguments document the route certified in Analysis;
the law itself is the explicit imported algorithm above. -/
def hitAndRunPointLaw {n : Nat} (_hn : 21 ≤ n) (P : PolytopeData n) (b : Nat)
    (_hunit : 1 ≤ decimalScale b * P.inradius)
    (eta : Real) (_heta0 : 0 < eta) (_heta1 : eta ≤ 1)
    (_hfinite : (codedLatticePoints P b).Finite)
    (_hnonempty : (codedLatticePoints P b).Nonempty) : Measure (LatticePoint n) :=
  acceptedRoundedLatticeLaw (hitAndRunContinuousLaw P b eta) P b

/-- The manuscript sampler uses a unit-inball chart before each finite-facet walk. -/
def normalizedHitAndRunPointLaw {n : Nat} (_hn : 21 ≤ n)
    (P : PolytopeData n) (b : Nat)
    (_hunit : 1 ≤ decimalScale b * P.inradius)
    (eta : Real) (_heta0 : 0 < eta) (_heta1 : eta ≤ 1)
    (_hfinite : (codedLatticePoints P b).Finite)
    (_hnonempty : (codedLatticePoints P b).Nonempty) : Measure (LatticePoint n) :=
  acceptedRoundedLatticeLaw (normalizedHitAndRunContinuousLaw P b eta) P b

/-- A one-point trace retaining the geometric number of rejection attempts.
Each attempt pays for its finite walk, rounding and membership test. -/
def normalizedHitAndRunPointWithCostLaw {n : Nat} (P : PolytopeData n)
    (b : Nat) (eta : Real) : Measure (LatticePoint n × Nat) :=
  (acceptedRoundedWithAttempts (normalizedHitAndRunContinuousLaw P b eta) P b).map
    fun result =>
      (result.1, result.2 * TTCRuntime.samplingAttemptOperations n
        P.presentation.facetCount (normalizedHitAndRunSteps P b eta))

/-- Independent accepted points, retaining the sum of all retry costs. -/
def normalizedHitAndRunBatchWithCostLaw {n : Nat} (P : PolytopeData n)
    (count b : Nat) (eta : Real) : Measure (SampleBatch n count × Nat) :=
  (Measure.pi (fun _ : Fin count => normalizedHitAndRunPointWithCostLaw P b eta)).map
    fun draws =>
      ((true, fun i => (draws i).1), ∑ i : Fin count, (draws i).2)

/-- Independent restarts from a point law, tagged as an unconditionally successful batch. -/
def iidSampleBatchLaw {n count : Nat} (pointLaw : Measure (LatticePoint n)) :
    Measure (SampleBatch n count) :=
  (Measure.pi (fun _ : Fin count => pointLaw)).map (fun samples => (true, samples))

/-- A total fallback used only outside the certified preprocessing regime. -/
def failedSampleBatchLaw {n count : Nat} : Measure (SampleBatch n count) :=
  Measure.dirac (false, fun _ => default)

/-- TTC sampling calls routed directly through arlib-community Hit-and-Run and KV97. -/
def hitAndRunSamplingOracles {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k) :
    TTCOracles n k := by
  classical
  exact
    { preprocessing := prep
      computeVolume := fun P _ _ => Measure.dirac
        (true, ⟨(volume P.carrier).toReal, ENNReal.toReal_nonneg⟩)
      generateSamples := fun P count b eta _ =>
        if h : 1 ≤ decimalScale b * P.inradius ∧ 0 < eta ∧ eta ≤ 1 ∧
            (codedLatticePoints P b).Finite ∧ (codedLatticePoints P b).Nonempty then
          iidSampleBatchLaw
            (hitAndRunPointLaw hn P b h.1 eta h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
        else
          failedSampleBatchLaw }

/-- The concrete oracle bundle used by TTC: current community CV18 for volume and current
community finite-step Hit-and-Run followed by KV97 rounding/rejection for sampling. -/
def communityCV18HitAndRunOracles {n k : Nat} (hn : 21 ≤ n)
    (prep : TTCPreprocessor n k) : TTCOracles n k :=
  { hitAndRunSamplingOracles hn prep with
    computeVolume := communityCV18VolumeLaw (by omega) }

/-- TTC with both geometric routines fixed to the imported community implementations. -/
def communityTTC {n k : Nat} (hn : 21 ≤ n) (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F)) (params : ApproxParams)
    (prep : TTCPreprocessor n k) : Measure NNReal :=
  ttc F hbounded params (communityCV18HitAndRunOracles hn prep)

/-- The paper's lower and upper clipping interval for a component volume estimate. -/
def PolytopeData.manuscriptVolumeLower {n : Nat} (P : PolytopeData n)
    (eta : Real) : NNReal :=
  Real.toNNReal ((1 - eta) * (2 * P.inradius / Real.sqrt n) ^ n)

def PolytopeData.manuscriptVolumeUpper {n : Nat} (P : PolytopeData n)
    (eta : Real) : NNReal :=
  Real.toNNReal ((1 + eta) * (2 * P.outerRadius) ^ n)

/-- Clip a CV18 result while preserving its diagnostic success tag. -/
def PolytopeData.clipManuscriptVolume {n : Nat} (P : PolytopeData n)
    (eta : Real) (o : VolumeOutcome) : VolumeOutcome :=
  (o.1, max (P.manuscriptVolumeLower eta)
    (min (P.manuscriptVolumeUpper eta) o.2))

/-- The same community oracles, with the manuscript's post-CV18 clipping. -/
def communityManuscriptOracles {n k : Nat} (hn : 21 ≤ n)
    (prep : TTCPreprocessor n k) : TTCOracles n k := by
  classical
  exact { communityCV18HitAndRunOracles hn prep with
    computeVolume := fun P eta delta =>
      (communityCV18VolumeLaw (by omega) P eta delta).map
        (P.clipManuscriptVolume eta)
    generateSamples := fun P count b eta _ =>
      if h : 1 ≤ decimalScale b * P.inradius ∧ 0 < eta ∧ eta ≤ 1 ∧
          (codedLatticePoints P b).Finite ∧ (codedLatticePoints P b).Nonempty then
        iidSampleBatchLaw
          (normalizedHitAndRunPointLaw hn P b h.1 eta h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
      else failedSampleBatchLaw }

/-- The current manuscript TTC control flow with concrete CV18 and Hit-and-Run calls. -/
def communityManuscriptTTC {n k : Nat} (hn : 21 ≤ n) (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F)) (params : ApproxParams)
    (prep : TTCPreprocessor n k) : Measure NNReal :=
  manuscriptTTC F hbounded params (communityManuscriptOracles hn prep)

/-- Charged implementations of the manuscript's two geometric calls. The
CV18 charge includes its certified membership-query budget and the public
non-query allowance factor; the sampler retains its random retry count. -/
def communityManuscriptCostedOracles {n k : Nat} (hn : 21 ≤ n)
    (prep : TTCPreprocessor n k) (cv18NonQueryFactor : Nat) :
    CostedTTCOracles n k := by
  classical
  exact
    { base := communityManuscriptOracles hn prep
      computeVolumeWithCost := fun P eta delta =>
        let queries := CommunityCV18.queryBudgetFor (by omega) P eta delta
        let membership := TTCRuntime.membershipQueryOperations n
          P.presentation.facetCount queries
        let nonQuery := cv18NonQueryFactor *
          TTCRuntime.membershipQueryOperations n P.presentation.facetCount
            (queries + 1)
        costedCharge
          ((communityManuscriptOracles hn prep).computeVolume P eta delta)
          (membership + nonQuery)
      generateSamplesWithCost := fun P count b eta _ =>
        if h : 1 ≤ decimalScale b * P.inradius ∧ 0 < eta ∧ eta ≤ 1 ∧
            (codedLatticePoints P b).Finite ∧ (codedLatticePoints P b).Nonempty then
          normalizedHitAndRunBatchWithCostLaw P count b eta
        else costedCharge failedSampleBatchLaw 0 }

def communityManuscriptTTCWithCost {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (params : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations cv18NonQueryFactor : Nat) : Measure (NNReal × Nat) :=
  manuscriptTTCWithCost F hbounded params
    (communityManuscriptCostedOracles hn prep cv18NonQueryFactor)
    preprocessingOperations

/-- Explicit arithmetic-operation allowance for one component of the charged
manuscript run. The finite sum of these allowances is proved to bound the
whole run's expected cost in `Analysis/ManuscriptComponentExpectation`. -/
noncomputable def TTCRuntime.manuscriptExpectedComponentBudget {n : Nat}
    (hn : 21 ≤ n) (p : ApproxParams) (m b cv18NonQueryFactor : Nat)
    (P : PolytopeData n) : ENNReal :=
  let cap := TTCRuntime.sampleCap p m
  let upperIntensity := manuscriptIntensity b n (p.threshold m)
    (max (P.manuscriptVolumeLower p.epsilonPrime)
      (P.manuscriptVolumeUpper p.epsilonPrime))
  (TTCRuntime.membershipQueryOperations n P.presentation.facetCount
      (CommunityCV18.queryBudgetFor (by omega) P p.epsilonPrime (p.deltaPrime m)) +
    cv18NonQueryFactor * TTCRuntime.membershipQueryOperations n
      P.presentation.facetCount
      (CommunityCV18.queryBudgetFor (by omega) P p.epsilonPrime (p.deltaPrime m) + 1) :
      ENNReal) +
  cap * (TTCRuntime.facetScanOperations n P.presentation.facetCount + 1) +
  (Nat.clog 2 (Nat.ceil ((upperIntensity : Real) / p.threshold m) + 1) : ENNReal) *
    TTCRuntime.rateThinningRoundOperations cap +
  TTCRuntime.poissonDrawOperations +
  4 * TTCRuntime.countThinningRoundOperations cap +
  (cap : ENNReal) *
    (2 * TTCRuntime.samplingAttemptOperations n P.presentation.facetCount
      (normalizedHitAndRunSteps P b p.epsilonPrime) +
      TTCRuntime.appendCopyOperations)

/-- The same component allowance with decimal precision exposed linearly.
The remaining volume logarithm is the clipped geometric volume bound. -/
noncomputable def TTCRuntime.manuscriptExpectedComponentBudgetLinearPrecision {n : Nat}
    (hn : 21 ≤ n) (p : ApproxParams) (m b cv18NonQueryFactor : Nat)
    (P : PolytopeData n) : ENNReal :=
  let cap := TTCRuntime.sampleCap p m
  let v := max (P.manuscriptVolumeLower p.epsilonPrime)
    (P.manuscriptVolumeUpper p.epsilonPrime)
  (TTCRuntime.membershipQueryOperations n P.presentation.facetCount
      (CommunityCV18.queryBudgetFor (by omega) P p.epsilonPrime (p.deltaPrime m)) +
    cv18NonQueryFactor * TTCRuntime.membershipQueryOperations n
      P.presentation.facetCount
      (CommunityCV18.queryBudgetFor (by omega) P p.epsilonPrime (p.deltaPrime m) + 1) :
      ENNReal) +
  cap * (TTCRuntime.facetScanOperations n P.presentation.facetCount + 1) +
  ((4 * (b * n) + Nat.clog 2 (Nat.ceil (v : Real) + 1) : Nat) : ENNReal) *
    TTCRuntime.rateThinningRoundOperations cap +
  TTCRuntime.poissonDrawOperations +
  4 * TTCRuntime.countThinningRoundOperations cap +
  (cap : ENNReal) *
    (2 * TTCRuntime.samplingAttemptOperations n P.presentation.facetCount
      (normalizedHitAndRunSteps P b p.epsilonPrime) +
      TTCRuntime.appendCopyOperations)

/-- Component budget after replacing the concrete sampler walk length by the
radius-ratio and precision envelope proved in `Analysis/NormalizedDiameterRuntime`. -/
noncomputable def TTCRuntime.manuscriptExpectedComponentBudgetGeometric
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams) (b cv18NonQueryFactor : Nat)
    (i : Fin D.componentCount) : ENNReal :=
  let P := D.component i
  let cap := TTCRuntime.sampleCap p D.componentCount
  let v := max (P.manuscriptVolumeLower p.epsilonPrime)
    (P.manuscriptVolumeUpper p.epsilonPrime)
  let samplerSteps := Nat.ceil ((2 : Real) ^ 68 * (n : Real) ^ 2 *
    (TTCRuntime.theorem3Rho D) ^ 2 *
    TTCRuntime.theorem3SamplerLogEnvelope n b
      (TTCRuntime.theorem3Rho D)
      (TTCRuntime.theorem3OuterRadiusMax D) p.epsilonPrime)
  (TTCRuntime.membershipQueryOperations n P.presentation.facetCount
      (CommunityCV18.queryBudgetFor (by omega) P p.epsilonPrime
        (p.deltaPrime D.componentCount)) +
    cv18NonQueryFactor * TTCRuntime.membershipQueryOperations n
      P.presentation.facetCount
      (CommunityCV18.queryBudgetFor (by omega) P p.epsilonPrime
        (p.deltaPrime D.componentCount) + 1) : ENNReal) +
  cap * (TTCRuntime.facetScanOperations n P.presentation.facetCount + 1) +
  ((4 * (b * n) + Nat.clog 2 (Nat.ceil (v : Real) + 1) : Nat) : ENNReal) *
    TTCRuntime.rateThinningRoundOperations cap +
  TTCRuntime.poissonDrawOperations +
  4 * TTCRuntime.countThinningRoundOperations cap +
  (cap : ENNReal) *
    (2 * TTCRuntime.samplingAttemptOperations n P.presentation.facetCount
      samplerSteps + TTCRuntime.appendCopyOperations)

/-- The same geometric allowance with the first-loop volume clip reduced to
the global outer-radius logarithm. -/
noncomputable def TTCRuntime.manuscriptExpectedComponentBudgetGeometricClip
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams) (b cv18NonQueryFactor : Nat)
    (i : Fin D.componentCount) : ENNReal :=
  let P := D.component i
  let cap := TTCRuntime.sampleCap p D.componentCount
  let samplerSteps := Nat.ceil ((2 : Real) ^ 68 * (n : Real) ^ 2 *
    (TTCRuntime.theorem3Rho D) ^ 2 *
    TTCRuntime.theorem3SamplerLogEnvelope n b
      (TTCRuntime.theorem3Rho D)
      (TTCRuntime.theorem3OuterRadiusMax D) p.epsilonPrime)
  (TTCRuntime.membershipQueryOperations n P.presentation.facetCount
      (CommunityCV18.queryBudgetFor (by omega) P p.epsilonPrime
        (p.deltaPrime D.componentCount)) +
    cv18NonQueryFactor * TTCRuntime.membershipQueryOperations n
      P.presentation.facetCount
      (CommunityCV18.queryBudgetFor (by omega) P p.epsilonPrime
        (p.deltaPrime D.componentCount) + 1) : ENNReal) +
  cap * (TTCRuntime.facetScanOperations n P.presentation.facetCount + 1) +
  ((4 * (b * n) + (2 + n * Nat.clog 2
      (Nat.ceil (4 * TTCRuntime.theorem3OuterRadiusMax D) + 1)) : Nat) : ENNReal) *
    TTCRuntime.rateThinningRoundOperations cap +
  TTCRuntime.poissonDrawOperations +
  4 * TTCRuntime.countThinningRoundOperations cap +
  (cap : ENNReal) *
    (2 * TTCRuntime.samplingAttemptOperations n P.presentation.facetCount
      samplerSteps + TTCRuntime.appendCopyOperations)

/-- Fully substituted per-component allowance: CV18 queries and normalized
Hit-and-Run steps use their proved polynomial-times-logarithmic envelopes. -/
noncomputable def TTCRuntime.manuscriptExpectedComponentBudgetTheorem3
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams) (b cv18NonQueryFactor : Nat)
    (i : Fin D.componentCount) : ENNReal :=
  let P := D.component i
  let cap := TTCRuntime.sampleCap p D.componentCount
  let queries := TTCRuntime.theorem3CV18QueryEnvelope hn D p i
  let samplerSteps := Nat.ceil ((2 : Real) ^ 68 * (n : Real) ^ 2 *
    (TTCRuntime.theorem3Rho D) ^ 2 *
    TTCRuntime.theorem3SamplerLogEnvelope n b
      (TTCRuntime.theorem3Rho D)
      (TTCRuntime.theorem3OuterRadiusMax D) p.epsilonPrime)
  (TTCRuntime.membershipQueryOperations n P.presentation.facetCount queries +
    cv18NonQueryFactor * TTCRuntime.membershipQueryOperations n
      P.presentation.facetCount (queries + 1) : ENNReal) +
  cap * (TTCRuntime.facetScanOperations n P.presentation.facetCount + 1) +
  ((4 * (b * n) + (2 + n * Nat.clog 2
      (Nat.ceil (4 * TTCRuntime.theorem3OuterRadiusMax D) + 1)) : Nat) : ENNReal) *
    TTCRuntime.rateThinningRoundOperations cap +
  TTCRuntime.poissonDrawOperations +
  4 * TTCRuntime.countThinningRoundOperations cap +
  (cap : ENNReal) *
    (2 * TTCRuntime.samplingAttemptOperations n P.presentation.facetCount
      samplerSteps + TTCRuntime.appendCopyOperations)

/-- One allowance valid for every component after taking only the maximum
facet count and maximum CV18 logarithmic product. -/
noncomputable def TTCRuntime.theorem3UniformComponentBudget
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams) (b cv18NonQueryFactor : Nat) :
    ENNReal :=
  let r := TTCRuntime.theorem3RMax D
  let cap := TTCRuntime.sampleCap p D.componentCount
  let queries := TTCRuntime.theorem3CV18QueryMax hn D p
  let samplerSteps := Nat.ceil ((2 : Real) ^ 68 * (n : Real) ^ 2 *
    (TTCRuntime.theorem3Rho D) ^ 2 *
    TTCRuntime.theorem3SamplerLogEnvelope n b
      (TTCRuntime.theorem3Rho D)
      (TTCRuntime.theorem3OuterRadiusMax D) p.epsilonPrime)
  (TTCRuntime.membershipQueryOperations n r queries +
    cv18NonQueryFactor * TTCRuntime.membershipQueryOperations n r (queries + 1) :
      ENNReal) +
  cap * (TTCRuntime.facetScanOperations n r + 1) +
  ((4 * (b * n) + (2 + n * Nat.clog 2
      (Nat.ceil (4 * TTCRuntime.theorem3OuterRadiusMax D) + 1)) : Nat) : ENNReal) *
    TTCRuntime.rateThinningRoundOperations cap +
  TTCRuntime.poissonDrawOperations +
  4 * TTCRuntime.countThinningRoundOperations cap +
  (cap : ENNReal) *
    (2 * TTCRuntime.samplingAttemptOperations n r samplerSteps +
      TTCRuntime.appendCopyOperations)

#krModelClosure communityTTC
#krModelClosure communityManuscriptTTC

end Kr25Ssmxt
