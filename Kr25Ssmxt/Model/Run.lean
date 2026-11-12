import Kr25Ssmxt.Model.Program
import Mathlib.Probability.Distributions.Geometric
import ArlibCommunity.Algorithms.CV18
import ArlibCommunity.Algorithms.HitAndRun.Model.Theorem
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Lattice.KV97.Inflate
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Lattice.Rounding.RoundLaw
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.PointwiseRoute
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Probability.Rejection

/-!
# Algorithm `ttc` with its concrete subroutines

`Model/Program.lean` states Algorithm `ttc` with its subroutines as slots. This file fills
them, in the order the algorithm calls them:

* `GetPrecision` (line `line:getprec`, Algorithm `getprec`), with `MaxInscribedBall`
  computed by the Chebyshev-centre LP;
* `ComputeVolume` (line `line:volume`): arlib-community's CV18 volume algorithm, followed by
  the paper's clipping;
* `GenerateSamples` (line `line:sample`): arlib-community's Hit-and-Run walk, KV97
  randomized rounding and rejection.

`ttc` assembles them; it is the algorithm Theorems 1 and 3 are about. Proofs that these
definitions meet their specifications are under `Analysis/`; no definition here depends on
an `Analysis/` declaration.
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

/-! ## Line `line:prec:getmaxball`: `MaxInscribedBall` by the Chebyshev-centre LP

Line 7 of Algorithm `getprec` computes the radius `γ̂` of the largest ball inscribed in a
component "using an LP algorithm". For `P = {x | aⱼ · x ≤ bⱼ}` this is the Chebyshev-centre
linear program

  `maximize t  subject to  aⱼ · c + t ‖aⱼ‖₂ ≤ bⱼ  for every facet j`

in the variables `(c, t)`. `MaxInscribedBall` is its optimum value. The LP's feasible pairs
are exactly the `ℓ₂` balls inside the component (`euclideanBall_subset_iff_chebyshevFeasible`),
so its optimum is the maximal inscribed radius, i.e. the component's `inradius`
(`PolytopeData.MaxInscribedBall_eq_inradius`). -/

/-- The constraints of the Chebyshev-centre LP at the point `(c, t)`. -/
def HalfspacePresentation.chebyshevFeasible {n : Nat} (H : HalfspacePresentation n)
    (c : Point n) (t : Real) : Prop :=
  ∀ j, dotProduct (H.normal j) c + t * ‖toEuclidean (H.normal j)‖ ≤ H.offset j

/-- The optimum value of the Chebyshev-centre LP. -/
def HalfspacePresentation.MaxInscribedBall {n : Nat} (H : HalfspacePresentation n) : Real :=
  sSup {t | ∃ c, H.chebyshevFeasible c t}

/-! ## Line `line:getprec`: `GetPrecision` (Algorithm `getprec`) -/

/-- `maxratio` of Algorithm `getprec`: the largest ratio of the required radius
`γ = (64 m n / η) √(log (4 r / η))` to a component's maximal inscribed radius `γ̂`,
starting from `1`. `γ̂` is computed by the Chebyshev-centre LP (line 7 of `getprec`). -/
def getPrecisionRatio {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (η : Real) : Real :=
  max 1 ((Finset.univ.sup fun i : Fin D.componentCount =>
    Real.toNNReal (latticeRadiusRequirement D η / (D.component i).presentation.MaxInscribedBall) :
      NNReal) : Real)

/-- Algorithm `getprec(F_d, M, η)`: return `⌈log₁₀ maxratio⌉`. -/
def GetPrecision {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (η : Real) : Nat :=
  Nat.ceil (Real.logb 10 (getPrecisionRatio D η))

/-- Pull the component back along `y ↦ inradius • y + incenter`. -/
def PolytopeData.cv18Body {n : Nat} (P : PolytopeData n) :
    Set (EuclideanSpace Real (Fin n)) :=
  (fun y => P.inradius • y + toEuclidean P.incenter) ⁻¹'
    Arlib.Polytope.body P.arlibNormal P.presentation.offset



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

/-- The current scheduled, capped, amplified CV18 membership-oracle program:
arlib-community's `cv18Program`, the subject of `cv18TheoremOneOne_program`. -/
def algorithm : VolumeAlgorithm :=
  cv18Program

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

/-- The paper's lower and upper clipping interval for a component volume estimate. -/
def PolytopeData.volumeClipLower {n : Nat} (P : PolytopeData n)
    (eta : Real) : NNReal :=
  Real.toNNReal ((1 - eta) * (2 * P.inradius / Real.sqrt n) ^ n)

def PolytopeData.volumeClipUpper {n : Nat} (P : PolytopeData n)
    (eta : Real) : NNReal :=
  Real.toNNReal ((1 + eta) * (2 * P.outerRadius) ^ n)

/-- Clip a CV18 result while preserving its diagnostic success tag. -/
def PolytopeData.clipVolume {n : Nat} (P : PolytopeData n)
    (eta : Real) (o : VolumeOutcome) : VolumeOutcome :=
  (o.1, max (P.volumeClipLower eta)
    (min (P.volumeClipUpper eta) o.2))

/-! ## Line `line:sample`: `GenerateSamples` is Hit-and-Run, KV97 rounding and rejection -/

open Arlib.Lattice.Rounding

/-- The integer lattice embedded in arlib's Euclidean state space. -/
def kv97LatEmb (n : Nat) (z : Fin n → Int) : EuclideanSpace Real (Fin n) :=
  WithLp.toLp 2 fun i => (z i : Real)

/-- Draw from a continuous law, then round every coordinate independently. -/
def kv97RoundedMeasureLaw {n : Nat}
    (mu : Measure (EuclideanSpace Real (Fin n))) : Measure (Fin n → Int) :=
  mu.bind fun p => roundLaw (WithLp.ofLp p)

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

The paper's sampler bound uses the ratio of outer and inner radii. The
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

/-- The paper sampler uses a unit-inball chart before each finite-facet walk. -/
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
      ((fun i => (draws i).1), ∑ i : Fin count, (draws i).2)

/-- Independent restarts from a point law. -/
def iidSampleBatchLaw {n count : Nat} (pointLaw : Measure (LatticePoint n)) :
    Measure (SampleBatch n count) :=
  Measure.pi (fun _ : Fin count => pointLaw)

/-- A total fallback used only outside the certified preprocessing regime. -/
def failedSampleBatchLaw {n count : Nat} : Measure (SampleBatch n count) :=
  Measure.dirac (fun _ => default)

/-! ## Algorithm `ttc` -/

/-- The concrete oracle bundle: community CV18 with the paper's post-CV18 clipping, and the
normalized community Hit-and-Run walk followed by KV97 rounding and rejection. -/
def ttcSubroutines {n k : Nat} (hn : 21 ≤ n)
    (prep : TTCPreprocessor n k) : TTCOracles n k := by
  classical
  exact {
    preprocessing := prep
    choosePrecision := fun D p => GetPrecision D p.precisionEta
    ComputeVolume := fun P eta delta =>
      (communityCV18VolumeLaw (by omega) P eta delta).map
        (P.clipVolume eta)
    GenerateSamples := fun P count b eta _ =>
      if h : 1 ≤ decimalScale b * P.inradius ∧ 0 < eta ∧ eta ≤ 1 ∧
          (codedLatticePoints P b).Finite ∧ (codedLatticePoints P b).Nonempty then
        iidSampleBatchLaw
          (normalizedHitAndRunPointLaw hn P b h.1 eta h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
      else failedSampleBatchLaw }

/-- **Algorithm `ttc`** with `GetPrecision`, `ComputeVolume` and `GenerateSamples` as above. -/
def ttc {n k : Nat} (hn : 21 ≤ n) (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F)) (params : ApproxParams)
    (prep : TTCPreprocessor n k) : Measure NNReal :=
  ttcPseudocode F hbounded params (ttcSubroutines hn prep)

/-- `t = Thresh · 10^{bn} · ComputeVolume(Pᵢ)` (line `line:volume`) of `ttc`; the same
quantity as `ttcPseudocode.t`. -/
abbrev ttc.t (b n : Nat) (Thresh : Real) (volumeEstimate : NNReal) : NNReal :=
  ttcPseudocode.t b n Thresh volumeEstimate

/-! ## The charged run (Theorem 3) -/

/-- Charged implementations of the paper's two geometric calls. The
CV18 charge includes its certified membership-query budget and the public
non-query allowance factor; the sampler retains its random retry count. -/
def ttcCostedSubroutines {n k : Nat} (hn : 21 ≤ n)
    (prep : TTCPreprocessor n k) (cv18NonQueryFactor : Nat) :
    CostedTTCOracles n k := by
  classical
  exact
    { base := ttcSubroutines hn prep
      computeVolumeWithCost := fun P eta delta =>
        let queries := CommunityCV18.queryBudgetFor (by omega) P eta delta
        let membership := TTCRuntime.membershipQueryOperations n
          P.presentation.facetCount queries
        let nonQuery := cv18NonQueryFactor *
          TTCRuntime.membershipQueryOperations n P.presentation.facetCount
            (queries + 1)
        costedCharge
          ((ttcSubroutines hn prep).ComputeVolume P eta delta)
          (membership + nonQuery)
      generateSamplesWithCost := fun P count b eta _ =>
        if h : 1 ≤ decimalScale b * P.inradius ∧ 0 < eta ∧ eta ≤ 1 ∧
            (codedLatticePoints P b).Finite ∧ (codedLatticePoints P b).Nonempty then
          normalizedHitAndRunBatchWithCostLaw P count b eta
        else costedCharge failedSampleBatchLaw 0 }

def ttcWithCost {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (params : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations cv18NonQueryFactor : Nat) : Measure (NNReal × Nat) :=
  ttcPseudocodeWithCost F hbounded params
    (ttcCostedSubroutines hn prep cv18NonQueryFactor)
    preprocessingOperations

/-! ## Constants in the Theorem 3 bound -/

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

open Classical in
/-- Largest of the explicit scheduled CV18 logarithmic products across TTC's
normalized components. The empty family's value is zero. -/
noncomputable def TTCRuntime.theorem3CV18LogMax
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams) : Real :=
  ((Finset.univ.sup fun i : Fin D.componentCount =>
    Real.toNNReal (if h : CommunityCV18.AdmissibleCV18Request p.ε' (p.δ' D.componentCount)
      then TTCRuntime.theorem3CV18LogEnvelope
        (CommunityCV18.params (by omega) (D.component i) p.ε' (p.δ' D.componentCount) h)
      else 0) : NNReal) : Real)

/-- The explicit factors suppressed in the corrected Theorem 3 headline after
the oracle rates and the thinning counter are put on a common scale. -/
noncomputable def TTCRuntime.theorem3ParameterFactor
    {n k : Nat} {F : LRAFormula n k} (hn : 21 ≤ n)
    (D : Decomposition F) (p : ApproxParams) : Real :=
  45 * (64 *
      ArlibCommunity.Algorithms.CV18.figureOneFinalScheduledExpectedCostConstant + 1) *
      TTCRuntime.theorem3CV18LogMax hn D p / (p.ε' / 2) ^ 2 +
    (2 : Real) ^ 68 *
      (Real.log 8 + Real.log (4 * TTCRuntime.theorem3Rho D + 1) +
        2 * (Real.log 10 + Real.log 6 + 1 +
          Real.log (1 + 8 / p.ε') + 2)) + 20

#krModelClosure ttc

end Kr25Ssmxt
