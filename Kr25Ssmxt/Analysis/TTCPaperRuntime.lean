import Kr25Ssmxt.Analysis.CV18HitAndRunOracles
import Kr25Ssmxt.Model.Prelude

/-!
# TTC runtime in the paper's membership-query real-RAM model

This file deliberately uses the cost convention from the paper: one membership query for
an `n`-dimensional polytope with `r` facets is one complete facet scan and is charged
`n * r` real-arithmetic operations.  It combines the current arlib-community CV18
membership-query certificate with the finite-step Hit-and-Run deadline used by TTC's
sampler.

The charge is for geometric-oracle work only.  It does not claim a machine-level cost for
DNF preprocessing, exact random-number generation, Poisson bookkeeping, or thinning.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Kr25Ssmxt
namespace PaperRuntime

open TTCRuntime

/-- A certificate for the exact current arlib-community CV18 program invoked on one TTC
component.  `queryCount` is a worst-case membership-query bound supplied by
`MembershipCostBound`; `operations` merely converts that count using `n * r`. -/
structure CV18MembershipRun {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (eta delta : Real) where
  admissible : AdmissibleCV18Request eta delta
  constant : Real
  constant_pos : 0 < constant
  queryCount : Nat
  costBound :
    (CommunityCV18.algorithm
      (CommunityCV18.params hn P eta delta admissible)).MembershipCostBound queryCount
  queryCount_le :
    queryCount ≤ Nat.ceil
      (constant *
        (ArlibCommunity.Algorithms.CV18.volumeScheduledBaseComplexityRate
            (CommunityCV18.params hn P eta delta admissible) *
          ArlibCommunity.Algorithms.CV18.protectedLog
            (1 / (CommunityCV18.params hn P eta delta admissible).p)))

/-- The explicit arlib-community schedule cap certified for this CV18 run. -/
def CV18MembershipRun.scheduleQueryCap {n : Nat} {hn : 3 ≤ n} {P : PolytopeData n}
    {eta delta : Real} (run : CV18MembershipRun hn P eta delta) : Nat :=
  Nat.ceil
    (run.constant *
      (ArlibCommunity.Algorithms.CV18.volumeScheduledBaseComplexityRate
          (CommunityCV18.params hn P eta delta run.admissible) *
        ArlibCommunity.Algorithms.CV18.protectedLog
          (1 / (CommunityCV18.params hn P eta delta run.admissible).p)))

def CV18MembershipRun.operations {n : Nat} {hn : 3 ≤ n} {P : PolytopeData n}
    {eta delta : Real} (run : CV18MembershipRun hn P eta delta) : Nat :=
  membershipQueryOperations n P.presentation.facetCount run.queryCount

theorem exists_cv18MembershipRun {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (eta delta : Real) (h : AdmissibleCV18Request eta delta) :
    Nonempty (CV18MembershipRun hn P eta delta) := by
  obtain ⟨C, hC, calls, hcost, hle⟩ :=
    CommunityCV18.membershipCostBound hn P eta delta h
  exact ⟨
    { admissible := h
      constant := C
      constant_pos := hC
      queryCount := calls
      costBound := hcost
      queryCount_le := hle }⟩

/-- CV18's proved membership-query budget, converted monotonically to the paper's
`n * r` operation budget. -/
theorem CV18MembershipRun.operations_le_schedule {n : Nat} {hn : 3 ≤ n}
    {P : PolytopeData n} {eta delta : Real}
    (run : CV18MembershipRun hn P eta delta) :
    run.operations ≤ membershipQueryOperations n P.presentation.facetCount
      run.scheduleQueryCap := by
  unfold CV18MembershipRun.operations membershipQueryOperations
  exact Nat.mul_le_mul_left _ run.queryCount_le

/-- The finite Hit-and-Run walk and pointwise-correct KV97 sampler used for one TTC
component, retaining the actual mixing deadline rather than hiding it in an oracle. -/
structure HitAndRunMembershipRun {n : Nat} (P : PolytopeData n) (b : Nat)
    (eta : Real) where
  diameter : Real
  steps : Nat
  diameter_bound :
    ∀ x ∈ Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b)
        (Arlib.KV97.cOf eta) (P.presentation.facetCount : Real),
      ∀ y ∈ Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b)
        (Arlib.KV97.cOf eta) (P.presentation.facetCount : Real),
        dist x y ≤ diameter
  deadline_bound :
    Arlib.MarkovChains.hrDeadlineUncond n diameter
        (volume (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b)
            (Arlib.KV97.cOf eta) (P.presentation.facetCount : Real)) /
          volume (Metric.ball (decimalScale b • toEuclidean P.incenter) 1)).toReal
        (min 1 ((eta / 8) /
          (volume (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b)
            (Arlib.KV97.cOf eta) (P.presentation.facetCount : Real))).toReal)) ≤
      (steps : Real)
  steps_eq_ceil_deadline :
    steps = Nat.ceil (Arlib.MarkovChains.hrDeadlineUncond n diameter
        (volume (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b)
            (Arlib.KV97.cOf eta) (P.presentation.facetCount : Real)) /
          volume (Metric.ball (decimalScale b • toEuclidean P.incenter) 1)).toReal
        (min 1 ((eta / 8) /
          (volume (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b)
            (Arlib.KV97.cOf eta) (P.presentation.facetCount : Real))).toReal)))
  pointwise_accuracy :
    AlmostUniformPointwise
      (acceptedRoundedLatticeLaw
        (Arlib.MarkovChains.iterate
          (Arlib.MarkovChains.lazy (Arlib.MarkovChains.hitAndRun
            (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b)
              (Arlib.KV97.cOf eta) (P.presentation.facetCount : Real))))
          (Arlib.uniformOn volume
            (Metric.ball (decimalScale b • toEuclidean P.incenter) 1)) steps)
        P b)
      (codedLatticePoints P b) eta

def HitAndRunMembershipRun.operations {n : Nat} {P : PolytopeData n} {b : Nat}
    {eta : Real} (run : HitAndRunMembershipRun P b eta) : Nat :=
  acceptedSampleOperations n P.presentation.facetCount run.steps

theorem exists_hitAndRunMembershipRun {n : Nat} (hn : 21 ≤ n)
    (P : PolytopeData n) (b : Nat)
    (hunit : 1 ≤ decimalScale b * P.inradius)
    {eta : Real} (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hfinite : (codedLatticePoints P b).Finite)
    (hnonempty : (codedLatticePoints P b).Nonempty) :
    Nonempty (HitAndRunMembershipRun P b eta) := by
  obtain ⟨D, steps, hD, hdeadline, hmceil, haccuracy⟩ :=
    P.exists_hitAndRun_latticePointLaw hn b hunit heta0 heta1 hfinite hnonempty
  exact ⟨
    { diameter := D
      steps := steps
      diameter_bound := hD
      deadline_bound := hdeadline
      steps_eq_ceil_deadline := hmceil
      pointwise_accuracy := haccuracy }⟩

/-- The sampler charge uses exactly the ceiling of the proved current-community mixing
deadline, rather than an unconstrained larger walk length. -/
theorem HitAndRunMembershipRun.operations_eq_deadline {n : Nat}
    {P : PolytopeData n} {b : Nat} {eta : Real}
    (run : HitAndRunMembershipRun P b eta) :
    run.operations = acceptedSampleOperations n P.presentation.facetCount
      (Nat.ceil (Arlib.MarkovChains.hrDeadlineUncond n run.diameter
        (volume (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b)
            (Arlib.KV97.cOf eta) (P.presentation.facetCount : Real)) /
          volume (Metric.ball (decimalScale b • toEuclidean P.incenter) 1)).toReal
        (min 1 ((eta / 8) /
          (volume (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b)
            (Arlib.KV97.cOf eta) (P.presentation.facetCount : Real))).toReal)))) := by
  unfold HitAndRunMembershipRun.operations
  rw [run.steps_eq_ceil_deadline]

/-- Analysis witness connecting every model-level query/step count to the concrete CV18
and Hit-and-Run executions selected for that TTC component. -/
structure CommunityRuntimeCertificate {n k : Nat} (hn : 21 ≤ n)
    {F : LRAFormula n k} (D : Decomposition F) (b : Nat) (p : ApproxParams) where
  volume : ∀ i : Fin D.componentCount,
    CV18MembershipRun (by omega) (D.component i)
      p.epsilonPrime (p.deltaPrime D.componentCount)
  sampler : ∀ i : Fin D.componentCount,
    HitAndRunMembershipRun (D.component i) b p.epsilonPrime

/-- Forget implementation details while retaining exactly the counts used by the public
model-level runtime theorem. -/
def CommunityRuntimeCertificate.toModel {n k : Nat} {hn : 21 ≤ n}
    {F : LRAFormula n k} {D : Decomposition F} {b : Nat} {p : ApproxParams}
    (cert : CommunityRuntimeCertificate hn D b p) :
    TTCRuntime.TTCMembershipRuntimeCertificate D p where
  volumeQueryCount := fun i => (cert.volume i).queryCount
  samplerStepCount := fun i => (cert.sampler i).steps

private lemma ttc_request_admissible {n k : Nat} {F : LRAFormula n k}
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

/-- Existence of the exact paper-cost certificate for every geometric call made by TTC.
No volume or sampling oracle hypothesis remains. -/
theorem ttc_membership_runtime_certificate {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k) :
    let D := prep.run F hbounded
    let b := (prep.choosePrecision D p).value
    Nonempty (CommunityRuntimeCertificate hn D b p) := by
  dsimp only
  let D := prep.run F hbounded
  let choice := prep.choosePrecision D p
  let b := choice.value
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have heta0 : 0 < p.epsilonPrime := div_pos p.epsilon_pos (by norm_num)
  have heta1 : p.epsilonPrime ≤ 1 := by
    dsimp only [ApproxParams.epsilonPrime]
    linarith [p.epsilon_le_one]
  classical
  let volumeRun : ∀ i : Fin D.componentCount,
      CV18MembershipRun (by omega) (D.component i)
        p.epsilonPrime (p.deltaPrime D.componentCount) :=
    fun i => Classical.choice
      (exists_cv18MembershipRun (by omega) (D.component i) _ _
        (ttc_request_admissible D p i))
  let samplerRun : ∀ i : Fin D.componentCount,
      HitAndRunMembershipRun (D.component i) b p.epsilonPrime := fun i => by
    have hset := coded_lattice_points_finite_nonempty hn0 D p b choice.adequate i
    have hunit : 1 ≤ decimalScale b * (D.component i).inradius :=
      (one_le_samplerRadiusRequirement hn0 (D.component i) heta0 heta1).trans
        ((le_max_right _ _).trans (choice.adequate i))
    exact Classical.choice
      (exists_hitAndRunMembershipRun hn (D.component i) b hunit heta0 heta1 hset.1 hset.2)
  exact ⟨{ volume := volumeRun, sampler := samplerRun }⟩

/-- The current arlib-community implementations discharge the public model-level runtime
trace interface. -/
theorem ttc_model_runtime_certificate {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k) :
    let D := prep.run F hbounded
    Nonempty (TTCRuntime.TTCMembershipRuntimeCertificate D p) := by
  dsimp only
  obtain ⟨cert⟩ := ttc_membership_runtime_certificate hn F hbounded p prep
  exact ⟨cert.toModel⟩

/-- Paper algebra after replacing component-specific facet/query/step counts by maxima.
This is the finite-sum form behind the paper's soft-O TTC runtime calculation. -/
theorem operations_le_maxima {n k : Nat} {hn : 21 ≤ n}
    {F : LRAFormula n k} {D : Decomposition F} {b : Nat} {p : ApproxParams}
    (cert : CommunityRuntimeCertificate hn D b p)
    (rMax volumeQueryMax samplerStepMax : Nat)
    (hfacets : ∀ i, (D.component i).presentation.facetCount ≤ rMax)
    (hvolume : ∀ i, (cert.volume i).queryCount ≤ volumeQueryMax)
    (hsampler : ∀ i, (cert.sampler i).steps ≤ samplerStepMax) :
    cert.toModel.operations ≤
      D.componentCount *
        (membershipQueryOperations n rMax volumeQueryMax +
          sampleCap p D.componentCount *
            acceptedSampleOperations n rMax samplerStepMax) := by
  unfold TTCRuntime.TTCMembershipRuntimeCertificate.operations
    CommunityRuntimeCertificate.toModel
  calc
    (∑ i : Fin D.componentCount, (
        membershipQueryOperations n (D.component i).presentation.facetCount
            (cert.volume i).queryCount +
          sampleCap p D.componentCount *
            acceptedSampleOperations n (D.component i).presentation.facetCount
              (cert.sampler i).steps)) ≤
        ∑ _i : Fin D.componentCount,
          (membershipQueryOperations n rMax volumeQueryMax +
            sampleCap p D.componentCount *
              acceptedSampleOperations n rMax samplerStepMax) := by
      apply Finset.sum_le_sum
      intro i _hi
      unfold membershipQueryOperations acceptedSampleOperations
      have hf := hfacets i
      have hv := hvolume i
      have hs := hsampler i
      apply Nat.add_le_add
      · exact Nat.mul_le_mul (Nat.mul_le_mul_left n hf) hv
      · apply Nat.mul_le_mul_left
        apply Nat.mul_le_mul_left
        exact Nat.mul_le_mul (Nat.mul_le_mul_left n hf) (Nat.add_le_add_right hs 1)
    _ = D.componentCount *
        (membershipQueryOperations n rMax volumeQueryMax +
          sampleCap p D.componentCount *
            acceptedSampleOperations n rMax samplerStepMax) := by
      simp [Nat.mul_comm]

/-! ## Theorem 3 (`thm:runtime`) -/

/-- Analysis-only unsimplified expression used between the componentwise oracle bounds
and the public headline expression. -/
private def theorem3DetailedRuntime (componentCount n rMax : Nat)
    (rho epsilon threshold volumeOverhead samplingOverhead : Real) : Real :=
  (componentCount : Real) * rMax *
    (volumeOverhead * theorem3VolumeKernel n rho epsilon +
      threshold * samplingOverhead * theorem3SamplingKernel n rho)

private lemma theorem3VolumeKernel_nonneg (n : Nat) (rho epsilon : Real) :
    0 ≤ theorem3VolumeKernel n rho epsilon := by
  unfold theorem3VolumeKernel
  positivity

private lemma theorem3SamplingKernel_nonneg (n : Nat) (rho : Real) :
    0 ≤ theorem3SamplingKernel n rho := by
  unfold theorem3SamplingKernel
  positivity

/-- The main-loop summation in Theorem 3: exactly `m` component costs, each dominated by
the two cited oracle bounds, give the paper's first displayed total-runtime expression. -/
theorem certificate_operations_le_theorem3Detailed {n k : Nat}
    {F : LRAFormula n k} {D : Decomposition F} {p : ApproxParams}
    (cert : TTCRuntime.TTCMembershipRuntimeCertificate D p)
    {rho : Real} {rMax : Nat}
    (bounds : TTCRuntime.Theorem3OracleBounds cert rho rMax) :
    (cert.operations : Real) ≤
      theorem3DetailedRuntime D.componentCount n rMax rho p.epsilon
        (sampleCap p D.componentCount) bounds.volumeOverhead bounds.samplingOverhead := by
  rw [TTCRuntime.TTCMembershipRuntimeCertificate.operations, Nat.cast_sum]
  calc
    (∑ i : Fin D.componentCount,
        ((membershipQueryOperations n (D.component i).presentation.facetCount
              (cert.volumeQueryCount i) +
            sampleCap p D.componentCount *
              acceptedSampleOperations n (D.component i).presentation.facetCount
                (cert.samplerStepCount i) : Nat) : Real)) ≤
        ∑ i : Fin D.componentCount,
          ((D.component i).presentation.facetCount : Real) *
            (bounds.volumeOverhead * theorem3VolumeKernel n rho p.epsilon +
              (sampleCap p D.componentCount : Real) * bounds.samplingOverhead *
                theorem3SamplingKernel n rho) := by
      apply Finset.sum_le_sum
      intro i _hi
      push_cast
      calc
        (membershipQueryOperations n (D.component i).presentation.facetCount
              (cert.volumeQueryCount i) : Real) +
            (sampleCap p D.componentCount : Real) *
              (acceptedSampleOperations n (D.component i).presentation.facetCount
                (cert.samplerStepCount i) : Real) ≤
            ((D.component i).presentation.facetCount : Real) * bounds.volumeOverhead *
                theorem3VolumeKernel n rho p.epsilon +
              (sampleCap p D.componentCount : Real) *
                (((D.component i).presentation.facetCount : Real) *
                  bounds.samplingOverhead * theorem3SamplingKernel n rho) := by
          exact add_le_add (bounds.volume_operations_le i)
            (mul_le_mul_of_nonneg_left (bounds.sample_operations_le i) (by positivity))
        _ = ((D.component i).presentation.facetCount : Real) *
            (bounds.volumeOverhead * theorem3VolumeKernel n rho p.epsilon +
              (sampleCap p D.componentCount : Real) * bounds.samplingOverhead *
                theorem3SamplingKernel n rho) := by ring
    _ ≤ ∑ _i : Fin D.componentCount,
          (rMax : Real) *
            (bounds.volumeOverhead * theorem3VolumeKernel n rho p.epsilon +
              (sampleCap p D.componentCount : Real) * bounds.samplingOverhead *
                theorem3SamplingKernel n rho) := by
      apply Finset.sum_le_sum
      intro i _hi
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast bounds.facets_le i
      · exact add_nonneg
          (mul_nonneg bounds.volumeOverhead_nonneg
            (theorem3VolumeKernel_nonneg n rho p.epsilon))
          (mul_nonneg
            (mul_nonneg (by positivity) bounds.samplingOverhead_nonneg)
            (theorem3SamplingKernel_nonneg n rho))
    _ = theorem3DetailedRuntime D.componentCount n rMax rho p.epsilon
          (sampleCap p D.componentCount) bounds.volumeOverhead bounds.samplingOverhead := by
      simp [theorem3DetailedRuntime]
      ring

/-- The algebraic simplification on the last line of Theorem 3.  It proves the headline
monomial while retaining, as an explicit multiplier, precisely the accuracy, threshold,
logarithmic, constant, and warm-start factors suppressed by the paper. -/
theorem theorem3DetailedRuntime_le_headline {componentCount n rMax : Nat}
    {rho epsilon threshold volumeOverhead samplingOverhead : Real}
    (hn : 1 ≤ n) (hrho : 1 ≤ rho) (_hepsilon : 0 < epsilon)
    (_hthreshold : 0 ≤ threshold) (hvolume : 0 ≤ volumeOverhead)
    (_hsampling : 0 ≤ samplingOverhead) :
    theorem3DetailedRuntime componentCount n rMax rho epsilon threshold
        volumeOverhead samplingOverhead ≤
      theorem3HeadlineCore componentCount n rMax rho *
        theorem3SuppressedFactor epsilon threshold volumeOverhead samplingOverhead := by
  let N : Real := n
  have hN : 1 ≤ N := by
    change (1 : Real) ≤ (n : Real)
    exact_mod_cast hn
  have hN2 : 1 ≤ N ^ 2 := by nlinarith [sq_nonneg (N - 1)]
  have hrho2 : 1 ≤ rho ^ 2 := by nlinarith [sq_nonneg (rho - 1)]
  have hfirst : N ^ 3 * rho ^ 2 ≤ N ^ 5 * rho ^ 2 := by
    calc
      N ^ 3 * rho ^ 2 = (N ^ 3 * rho ^ 2) * 1 := by ring
      _ ≤ (N ^ 3 * rho ^ 2) * N ^ 2 := by
        exact mul_le_mul_of_nonneg_left hN2 (by positivity)
      _ = N ^ 5 * rho ^ 2 := by ring
  have hsecond : N ^ 4 ≤ N ^ 5 * rho ^ 2 := by
    have hNrho : 1 ≤ N * rho ^ 2 :=
      one_le_mul_of_one_le_of_one_le hN hrho2
    calc
      N ^ 4 = N ^ 4 * 1 := by ring
      _ ≤ N ^ 4 * (N * rho ^ 2) := by
        exact mul_le_mul_of_nonneg_left hNrho (by positivity)
      _ = N ^ 5 * rho ^ 2 := by ring
  have hmax : max (N ^ 3 * rho ^ 2) (N ^ 4) ≤ N ^ 5 * rho ^ 2 :=
    max_le hfirst hsecond
  have hvolumeKernel : theorem3VolumeKernel n rho epsilon ≤
      (N ^ 5 * rho ^ 2) / epsilon ^ 2 := by
    unfold theorem3VolumeKernel
    change max (N ^ 3 * rho ^ 2) (N ^ 4) / epsilon ^ 2 ≤ _
    exact div_le_div_of_nonneg_right hmax (sq_nonneg epsilon)
  have hinner :
      volumeOverhead * theorem3VolumeKernel n rho epsilon +
          threshold * samplingOverhead * theorem3SamplingKernel n rho ≤
        (N ^ 5 * rho ^ 2) *
          (volumeOverhead / epsilon ^ 2 + threshold * samplingOverhead) := by
    calc
      volumeOverhead * theorem3VolumeKernel n rho epsilon +
          threshold * samplingOverhead * theorem3SamplingKernel n rho ≤
        volumeOverhead * ((N ^ 5 * rho ^ 2) / epsilon ^ 2) +
          threshold * samplingOverhead * theorem3SamplingKernel n rho := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hvolumeKernel hvolume) le_rfl
      _ = (N ^ 5 * rho ^ 2) *
          (volumeOverhead / epsilon ^ 2 + threshold * samplingOverhead) := by
            simp only [theorem3SamplingKernel]
            change volumeOverhead * (N ^ 5 * rho ^ 2 / epsilon ^ 2) +
                threshold * samplingOverhead * (N ^ 5 * rho ^ 2) = _
            ring
  unfold theorem3DetailedRuntime theorem3HeadlineCore theorem3SuppressedFactor
  change (componentCount : Real) * rMax *
      (volumeOverhead * theorem3VolumeKernel n rho epsilon +
        threshold * samplingOverhead * theorem3SamplingKernel n rho) ≤
    (componentCount : Real) * N ^ 5 * rho ^ 2 * rMax *
      (volumeOverhead / epsilon ^ 2 + threshold * samplingOverhead)
  calc
    (componentCount : Real) * rMax *
        (volumeOverhead * theorem3VolumeKernel n rho epsilon +
          threshold * samplingOverhead * theorem3SamplingKernel n rho) ≤
      (componentCount : Real) * rMax *
        ((N ^ 5 * rho ^ 2) *
          (volumeOverhead / epsilon ^ 2 + threshold * samplingOverhead)) := by
            exact mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = (componentCount : Real) * N ^ 5 * rho ^ 2 * rMax *
        (volumeOverhead / epsilon ^ 2 + threshold * samplingOverhead) := by ring

/-- Formal version of Theorem 3 (`thm:runtime`) for the concrete TTC oracle certificate.
The right-hand side is exactly `m n^5 rho^2 r_max` times the factors suppressed by the
paper's `O` notation. -/
theorem ttc_total_runtime_theorem3 {n k : Nat} {hn : 21 ≤ n}
    {F : LRAFormula n k} {D : Decomposition F} {p : ApproxParams}
    (cert : TTCRuntime.TTCMembershipRuntimeCertificate D p)
    {rho : Real} {rMax : Nat}
    (bounds : TTCRuntime.Theorem3OracleBounds cert rho rMax) :
    (cert.operations : Real) ≤
      theorem3HeadlineCore D.componentCount n rMax rho *
        theorem3SuppressedFactor p.epsilon (sampleCap p D.componentCount)
          bounds.volumeOverhead bounds.samplingOverhead := by
  exact (certificate_operations_le_theorem3Detailed cert bounds).trans
    (theorem3DetailedRuntime_le_headline (by omega) bounds.one_le_rho p.epsilon_pos
      (by positivity) bounds.volumeOverhead_nonneg bounds.samplingOverhead_nonneg)

/-- End-to-end Theorem 3 for the current community implementations.  The CV18 query
certificate and Hit-and-Run deadline are constructed for every component.  Their exact
finite maxima, normalized by the two displayed paper kernels, supply the factors hidden by
the paper's `O` notation; callers no longer provide an oracle-cost hypothesis. -/
theorem community_ttc_total_runtime_theorem3 {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k) :
    let D := prep.run F hbounded
    let b := (prep.choosePrecision D p).value
    ∃ communityCert : CommunityRuntimeCertificate hn D b p,
      ∃ bounds : TTCRuntime.Theorem3OracleBounds communityCert.toModel
          (theorem3Rho D) (theorem3RMax D),
        (communityCert.toModel.operations : Real) ≤
          theorem3HeadlineCore D.componentCount n (theorem3RMax D) (theorem3Rho D) *
            theorem3SuppressedFactor p.epsilon (sampleCap p D.componentCount)
              bounds.volumeOverhead bounds.samplingOverhead := by
  let D := prep.run F hbounded
  let b := (prep.choosePrecision D p).value
  change ∃ communityCert : CommunityRuntimeCertificate hn D b p,
    ∃ bounds : TTCRuntime.Theorem3OracleBounds communityCert.toModel
        (theorem3Rho D) (theorem3RMax D),
      (communityCert.toModel.operations : Real) ≤
        theorem3HeadlineCore D.componentCount n (theorem3RMax D) (theorem3Rho D) *
          theorem3SuppressedFactor p.epsilon (sampleCap p D.componentCount)
            bounds.volumeOverhead bounds.samplingOverhead
  obtain ⟨communityCert⟩ := ttc_membership_runtime_certificate hn F hbounded p prep
  let cert := communityCert.toModel
  let rho := theorem3Rho D
  let rMax := theorem3RMax D
  let volumeKernel := theorem3VolumeKernel n rho p.epsilon
  let samplingKernel := theorem3SamplingKernel n rho
  have hn0 : 0 < n := by omega
  have hnR : (0 : Real) < n := by exact_mod_cast hn0
  have hrho : 1 ≤ rho := by
    unfold rho theorem3Rho
    exact le_max_left _ _
  have hrho0 : 0 < rho := lt_of_lt_of_le zero_lt_one hrho
  have hvolumeKernel : 0 < volumeKernel := by
    unfold volumeKernel theorem3VolumeKernel
    apply div_pos
    · exact lt_of_lt_of_le (pow_pos hnR 4) (le_max_right _ _)
    · exact sq_pos_of_pos p.epsilon_pos
  have hsamplingKernel : 0 < samplingKernel := by
    unfold samplingKernel theorem3SamplingKernel
    positivity
  let volumeLocal : Fin D.componentCount → NNReal := fun i =>
    Real.toNNReal
      ((membershipQueryOperations n 1 (communityCert.volume i).scheduleQueryCap : Real) /
        volumeKernel)
  let samplingLocal : Fin D.componentCount → NNReal := fun i =>
    Real.toNNReal
      ((acceptedSampleOperations n 1 (communityCert.sampler i).steps : Real) /
        samplingKernel)
  let volumeOverhead : NNReal := Finset.univ.sup volumeLocal
  let samplingOverhead : NNReal := Finset.univ.sup samplingLocal
  have volumeLocal_le (i : Fin D.componentCount) :
      ((membershipQueryOperations n 1
          (communityCert.volume i).scheduleQueryCap : Real) / volumeKernel) ≤
        (volumeOverhead : Real) := by
    have hnonneg : 0 ≤
        ((membershipQueryOperations n 1
          (communityCert.volume i).scheduleQueryCap : Real) / volumeKernel) := by
      positivity
    rw [← Real.coe_toNNReal _ hnonneg]
    exact_mod_cast (Finset.le_sup (f := volumeLocal) (Finset.mem_univ i))
  have samplingLocal_le (i : Fin D.componentCount) :
      ((acceptedSampleOperations n 1 (communityCert.sampler i).steps : Real) /
          samplingKernel) ≤ (samplingOverhead : Real) := by
    have hnonneg : 0 ≤
        ((acceptedSampleOperations n 1 (communityCert.sampler i).steps : Real) /
          samplingKernel) := by
      positivity
    rw [← Real.coe_toNNReal _ hnonneg]
    exact_mod_cast (Finset.le_sup (f := samplingLocal) (Finset.mem_univ i))
  let bounds : TTCRuntime.Theorem3OracleBounds cert rho rMax :=
    { one_le_rho := hrho
      volumeOverhead := volumeOverhead
      volumeOverhead_nonneg := by positivity
      samplingOverhead := samplingOverhead
      samplingOverhead_nonneg := by positivity
      facets_le := fun i => by
        unfold rMax theorem3RMax
        exact Finset.le_sup (f := fun j : Fin D.componentCount =>
          (D.component j).presentation.facetCount) (Finset.mem_univ i)
      volume_operations_le := fun i => by
        let run := communityCert.volume i
        have hquery : run.queryCount ≤ run.scheduleQueryCap := run.queryCount_le
        have hqueryOps :
            (membershipQueryOperations n (D.component i).presentation.facetCount
              run.queryCount : Real) ≤
            (membershipQueryOperations n (D.component i).presentation.facetCount
              run.scheduleQueryCap : Real) := by
          exact_mod_cast Nat.mul_le_mul_left
            (n * (D.component i).presentation.facetCount) hquery
        calc
          (membershipQueryOperations n (D.component i).presentation.facetCount
              (cert.volumeQueryCount i) : Real) ≤
              (membershipQueryOperations n (D.component i).presentation.facetCount
                run.scheduleQueryCap : Real) := by
                  simpa [cert, CommunityRuntimeCertificate.toModel, run] using hqueryOps
          _ = ((D.component i).presentation.facetCount : Real) *
              (((membershipQueryOperations n 1 run.scheduleQueryCap : Real) /
                volumeKernel)) * volumeKernel := by
                  rw [mul_assoc, div_mul_cancel₀ _ hvolumeKernel.ne']
                  simp [membershipQueryOperations]
                  ring
          _ ≤ ((D.component i).presentation.facetCount : Real) *
              (volumeOverhead : Real) * volumeKernel := by
                gcongr
                simpa [run] using volumeLocal_le i
          _ = ((D.component i).presentation.facetCount : Real) *
              (volumeOverhead : Real) * theorem3VolumeKernel n rho p.epsilon := by
                rfl
      sample_operations_le := fun i => by
        let run := communityCert.sampler i
        calc
          (acceptedSampleOperations n (D.component i).presentation.facetCount
              (cert.samplerStepCount i) : Real) =
              ((D.component i).presentation.facetCount : Real) *
                (((acceptedSampleOperations n 1 run.steps : Real) /
                  samplingKernel)) * samplingKernel := by
                    rw [mul_assoc, div_mul_cancel₀ _ hsamplingKernel.ne']
                    simp [cert, CommunityRuntimeCertificate.toModel, run,
                      acceptedSampleOperations, membershipQueryOperations]
                    ring
          _ ≤ ((D.component i).presentation.facetCount : Real) *
              (samplingOverhead : Real) * samplingKernel := by
                gcongr
                simpa [run] using samplingLocal_le i
          _ = ((D.component i).presentation.facetCount : Real) *
              (samplingOverhead : Real) * theorem3SamplingKernel n rho := by
                rfl }
  refine ⟨communityCert, bounds, ?_⟩
  exact ttc_total_runtime_theorem3 (hn := hn) cert bounds

/-- Model-facing corollary of `community_ttc_total_runtime_theorem3`.  It erases the
implementation fields only after the concrete CV18 `MembershipCostBound` and Hit-and-Run
deadline have been used to construct the public certificate and its bounds. -/
theorem model_ttc_total_runtime_theorem3 {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k) :
    let D := prep.run F hbounded
    ∃ cert : TTCRuntime.TTCMembershipRuntimeCertificate D p,
      ∃ bounds : TTCRuntime.Theorem3OracleBounds cert
          (theorem3Rho D) (theorem3RMax D),
        (cert.operations : Real) ≤
          theorem3HeadlineCore D.componentCount n (theorem3RMax D) (theorem3Rho D) *
            theorem3SuppressedFactor p.epsilon (sampleCap p D.componentCount)
              bounds.volumeOverhead bounds.samplingOverhead := by
  dsimp only
  obtain ⟨communityCert, bounds, hbound⟩ :=
    community_ttc_total_runtime_theorem3 hn F hbounded p prep
  exact ⟨communityCert.toModel, bounds, hbound⟩

/-- Accuracy and the paper-level membership-operation certificate for the same concrete
CV18/Hit-and-Run TTC instance. -/
theorem ttc_accuracy_and_membership_runtime
    (hprior : Prior) {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (hregime :
      let D := prep.run F hbounded
      let b := (prep.choosePrecision D p).value
      D.componentCount = 0 ∨
        p.threshold D.componentCount / 4 ≤ (scaledLatticeVolume D b : Real)) :
    (IsProbabilityMeasure
        (ttc F hbounded p (communityCV18HitAndRunOracles hn prep)) ∧
      (ttc F hbounded p (communityCV18HitAndRunOracles hn prep)).real
          {estimate | (estimate : Real) ∈
            Arlib.relErr p.epsilon (volume (solutionSet F)).toReal} ≥
        1 - p.delta) ∧
      (let D := prep.run F hbounded
       let b := (prep.choosePrecision D p).value
       Nonempty (CommunityRuntimeCertificate hn D b p)) := by
  constructor
  · exact ttc_volume_accuracy_communityCV18_hitAndRun hprior hn F hbounded p prep hregime
  · exact ttc_membership_runtime_certificate hn F hbounded p prep

#print axioms ttc_membership_runtime_certificate
#print axioms CV18MembershipRun.operations_le_schedule
#print axioms HitAndRunMembershipRun.operations_eq_deadline
#print axioms operations_le_maxima
#print axioms certificate_operations_le_theorem3Detailed
#print axioms theorem3DetailedRuntime_le_headline
#print axioms ttc_total_runtime_theorem3
#print axioms community_ttc_total_runtime_theorem3
#print axioms model_ttc_total_runtime_theorem3
#print axioms ttc_accuracy_and_membership_runtime

end PaperRuntime
end Kr25Ssmxt
