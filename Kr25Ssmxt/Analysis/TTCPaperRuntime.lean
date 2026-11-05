import Kr25Ssmxt.Analysis.CV18HitAndRunOracles
import Kr25Ssmxt.Analysis.ManuscriptThinningCosts
import Kr25Ssmxt.Model.Prelude

/-!
# TTC runtime in the paper's membership-query real-RAM model

The model surface fixes the concrete cost certificate: CV18 is charged its syntax-derived
query budget, and sampling is charged the finite Hit-and-Run deadline used by
`communityTTC`. This file proves the charged CV18 budget and the resulting Theorem 3
inequality. It introduces no alternate runtime structures or oracle-bound assumptions.

The charge is for geometric-oracle work only. It does not claim a machine-level cost for
DNF preprocessing, exact random-number generation, Poisson bookkeeping, or thinning.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Kr25Ssmxt
namespace PaperRuntime

open TTCRuntime

/-- Markov's inequality in the form needed for a high-probability runtime bound.
The cutoff is the expected-cost budget divided by the allowed failure probability,
so its dependence on that probability is polynomial of degree one. This lemma
requires a costed run law; `communityTTC` currently records only its estimate. -/
theorem runtime_tail_le_of_expected_cost
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (cost : Ω → ENNReal) (hcost : Measurable cost)
    (budget failure : ENNReal)
    (hbudget0 : budget ≠ 0) (hbudgetTop : budget ≠ ∞)
    (hfailure0 : failure ≠ 0) (hfailureTop : failure ≠ ∞)
    (hexpected : ∫⁻ ω, cost ω ∂μ ≤ budget) :
    μ {ω | budget / failure ≤ cost ω} ≤ failure := by
  have hcutoff0 : budget / failure ≠ 0 :=
    ENNReal.div_ne_zero.mpr ⟨hbudget0, hfailureTop⟩
  have hcutoffTop : budget / failure ≠ ∞ :=
    ENNReal.div_ne_top hbudgetTop hfailure0
  apply (ENNReal.mul_le_mul_iff_right hcutoff0 hcutoffTop).mp
  calc
    (budget / failure) * μ {ω | budget / failure ≤ cost ω} ≤
        ∫⁻ ω, cost ω ∂μ :=
      MeasureTheory.mul_meas_ge_le_lintegral hcost (budget / failure)
    _ ≤ budget := hexpected
    _ = (budget / failure) * failure :=
      (ENNReal.div_mul_cancel hfailure0 hfailureTop).symm

theorem ttc_request_admissible {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (i : Fin D.componentCount) :
    CommunityCV18.AdmissibleCV18Request
      p.epsilonPrime (p.deltaPrime D.componentCount) := by
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

end PaperRuntime
namespace CommunityCV18

/-- The explicit query budget stored in the Model certificate bounds every charged run of
the concrete amplified CV18 program. -/
theorem membershipCostCertified {n : Nat} (hn : 3 ≤ n)
    (P : PolytopeData n) (eta delta : Real)
    (h : AdmissibleCV18Request eta delta) :
    MembershipCostCertified hn P eta delta := by
  rw [MembershipCostCertified, dif_pos h, queryBudgetFor, dif_pos h]
  apply ArlibCommunity.Algorithms.CV18.MembershipOracleProgram.QueryBound.toMembershipCostBound
  simpa [algorithm, ArlibCommunity.Algorithms.CV18.cv18Program, queryBudget] using
    ArlibCommunity.Algorithms.CV18.amplifyOracleProgram_queryBound
      ArlibCommunity.Algorithms.CV18.figureOneFinalScheduledCappedValueProgram
      (params hn P eta delta h)
      (ArlibCommunity.Algorithms.CV18.figureOneFinalScheduledCappedValueProgram_queryBound
        (params hn P eta delta h))

/-- Reprice each charged CV18 membership call as a scan of `r` facets in dimension
`n`. This is a bound on membership work; the imported program's non-query
arithmetic is not part of its charged semantics. -/
theorem membershipArithmeticCostBound {n : Nat} (hn : 3 ≤ n)
    (P : PolytopeData n) (eta delta : Real)
    (h : AdmissibleCV18Request eta delta)
    (oracle : ArlibCommunity.Algorithms.CV18.AmbientSpace n → Bool)
    (choices : ArlibCommunity.Algorithms.CV18.MembershipOracleProgram.MembershipCostChoices n) :
    n * P.presentation.facetCount *
        Arlib.Computation.Charged.steps
          (Arlib.Computation.Rate.unit Arlib.Computation.StdOp)
          ((algorithm (params hn P eta delta h)).chargedMembershipRun oracle choices) ≤
      TTCRuntime.membershipQueryOperations n P.presentation.facetCount
        (queryBudgetFor hn P eta delta) := by
  have hcert := membershipCostCertified hn P eta delta h
  rw [MembershipCostCertified, dif_pos h] at hcert
  have hsteps := hcert oracle choices
  simpa only [TTCRuntime.membershipQueryOperations, Nat.mul_assoc] using
    Nat.mul_le_mul_left (n * P.presentation.facetCount) hsteps

end CommunityCV18
namespace PaperRuntime

open TTCRuntime

/-- Every CV18 budget in the concrete TTC runtime certificate is certified against the
charged semantics of the imported program. -/
theorem community_volume_cost_certified {n k : Nat} (hn : 21 ≤ n)
    {F : LRAFormula n k} (D : Decomposition F) (p : ApproxParams) :
    ∀ i : Fin D.componentCount,
      CommunityCV18.MembershipCostCertified (by omega) (D.component i)
        p.epsilonPrime (p.deltaPrime D.componentCount) := by
  intro i
  exact CommunityCV18.membershipCostCertified (by omega) (D.component i)
    p.epsilonPrime (p.deltaPrime D.componentCount) (ttc_request_admissible D p i)

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

/-- The exact finite maxima defined on the Model surface dominate every component cost;
summing the components gives the detailed first display in the paper's proof. -/
theorem certificate_operations_le_theorem3Detailed {n k : Nat} (hn : 1 ≤ n)
    {F : LRAFormula n k} {D : Decomposition F} {p : ApproxParams}
    (cert : TTCMembershipRuntimeCertificate D p) :
    (cert.operations : Real) ≤
      theorem3DetailedRuntime D.componentCount n (theorem3RMax D)
        (theorem3Rho D) p.epsilon (sampleCap p D.componentCount)
        (theorem3VolumeOverhead cert (theorem3Rho D))
        (theorem3SamplingOverhead cert (theorem3Rho D)) := by
  let rho := theorem3Rho D
  let rMax := theorem3RMax D
  let volumeKernel := theorem3VolumeKernel n rho p.epsilon
  let samplingKernel := theorem3SamplingKernel n rho
  have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnR : (0 : Real) < n := by exact_mod_cast hn0
  have hrho : 1 ≤ rho := by
    unfold rho theorem3Rho
    exact le_max_left _ _
  have hvolumeKernel : 0 < volumeKernel := by
    unfold volumeKernel theorem3VolumeKernel
    apply div_pos
    · exact lt_of_lt_of_le (pow_pos hnR 4) (le_max_right _ _)
    · exact sq_pos_of_pos p.epsilon_pos
  have hsamplingKernel : 0 < samplingKernel := by
    unfold samplingKernel theorem3SamplingKernel
    have hrho0 : 0 < rho := lt_of_lt_of_le zero_lt_one hrho
    positivity
  have hvolumeOverhead : 0 ≤ theorem3VolumeOverhead cert rho := by
    unfold theorem3VolumeOverhead
    positivity
  have hsamplingOverhead : 0 ≤ theorem3SamplingOverhead cert rho := by
    unfold theorem3SamplingOverhead
    positivity
  have volumeLocal_le (i : Fin D.componentCount) :
      ((membershipQueryOperations n 1 (cert.volumeQueryCount i) : Real) /
          volumeKernel) ≤ theorem3VolumeOverhead cert rho := by
    have hnonneg : 0 ≤
        ((membershipQueryOperations n 1 (cert.volumeQueryCount i) : Real) /
          volumeKernel) := by positivity
    rw [← Real.coe_toNNReal _ hnonneg]
    unfold theorem3VolumeOverhead
    exact_mod_cast (Finset.le_sup
      (f := fun j : Fin D.componentCount => Real.toNNReal
        ((membershipQueryOperations n 1 (cert.volumeQueryCount j) : Real) /
          theorem3VolumeKernel n rho p.epsilon)) (Finset.mem_univ i))
  have samplingLocal_le (i : Fin D.componentCount) :
      ((acceptedSampleOperations n 1 (cert.samplerStepCount i) : Real) /
          samplingKernel) ≤ theorem3SamplingOverhead cert rho := by
    have hnonneg : 0 ≤
        ((acceptedSampleOperations n 1 (cert.samplerStepCount i) : Real) /
          samplingKernel) := by positivity
    rw [← Real.coe_toNNReal _ hnonneg]
    unfold theorem3SamplingOverhead
    exact_mod_cast (Finset.le_sup
      (f := fun j : Fin D.componentCount => Real.toNNReal
        ((acceptedSampleOperations n 1 (cert.samplerStepCount j) : Real) /
          theorem3SamplingKernel n rho)) (Finset.mem_univ i))
  have volumeOperations_le (i : Fin D.componentCount) :
      (membershipQueryOperations n (D.component i).presentation.facetCount
          (cert.volumeQueryCount i) : Real) ≤
        ((D.component i).presentation.facetCount : Real) *
          theorem3VolumeOverhead cert rho * volumeKernel := by
    calc
      (membershipQueryOperations n (D.component i).presentation.facetCount
          (cert.volumeQueryCount i) : Real) =
          ((D.component i).presentation.facetCount : Real) *
            (((membershipQueryOperations n 1 (cert.volumeQueryCount i) : Real) /
              volumeKernel)) * volumeKernel := by
                rw [mul_assoc, div_mul_cancel₀ _ hvolumeKernel.ne']
                simp [membershipQueryOperations]
                ring
      _ ≤ ((D.component i).presentation.facetCount : Real) *
          theorem3VolumeOverhead cert rho * volumeKernel := by
            apply mul_le_mul_of_nonneg_right _ hvolumeKernel.le
            exact mul_le_mul_of_nonneg_left (volumeLocal_le i) (by positivity)
  have sampleOperations_le (i : Fin D.componentCount) :
      (acceptedSampleOperations n (D.component i).presentation.facetCount
          (cert.samplerStepCount i) : Real) ≤
        ((D.component i).presentation.facetCount : Real) *
          theorem3SamplingOverhead cert rho * samplingKernel := by
    calc
      (acceptedSampleOperations n (D.component i).presentation.facetCount
          (cert.samplerStepCount i) : Real) =
          ((D.component i).presentation.facetCount : Real) *
            (((acceptedSampleOperations n 1 (cert.samplerStepCount i) : Real) /
              samplingKernel)) * samplingKernel := by
                rw [mul_assoc, div_mul_cancel₀ _ hsamplingKernel.ne']
                simp [acceptedSampleOperations, membershipQueryOperations]
                ring
      _ ≤ ((D.component i).presentation.facetCount : Real) *
          theorem3SamplingOverhead cert rho * samplingKernel := by
            apply mul_le_mul_of_nonneg_right _ hsamplingKernel.le
            exact mul_le_mul_of_nonneg_left (samplingLocal_le i) (by positivity)
  rw [TTCMembershipRuntimeCertificate.operations, Nat.cast_sum]
  calc
    (∑ i : Fin D.componentCount,
        ((membershipQueryOperations n (D.component i).presentation.facetCount
              (cert.volumeQueryCount i) +
            sampleCap p D.componentCount *
              acceptedSampleOperations n (D.component i).presentation.facetCount
                (cert.samplerStepCount i) : Nat) : Real)) ≤
        ∑ i : Fin D.componentCount,
          ((D.component i).presentation.facetCount : Real) *
            (theorem3VolumeOverhead cert rho * volumeKernel +
              (sampleCap p D.componentCount : Real) *
                theorem3SamplingOverhead cert rho * samplingKernel) := by
      apply Finset.sum_le_sum
      intro i _hi
      push_cast
      calc
        (membershipQueryOperations n (D.component i).presentation.facetCount
              (cert.volumeQueryCount i) : Real) +
            (sampleCap p D.componentCount : Real) *
              (acceptedSampleOperations n (D.component i).presentation.facetCount
                (cert.samplerStepCount i) : Real) ≤
            ((D.component i).presentation.facetCount : Real) *
                theorem3VolumeOverhead cert rho * volumeKernel +
              (sampleCap p D.componentCount : Real) *
                (((D.component i).presentation.facetCount : Real) *
                  theorem3SamplingOverhead cert rho * samplingKernel) := by
          exact add_le_add (volumeOperations_le i)
            (mul_le_mul_of_nonneg_left (sampleOperations_le i) (by positivity))
        _ = ((D.component i).presentation.facetCount : Real) *
            (theorem3VolumeOverhead cert rho * volumeKernel +
              (sampleCap p D.componentCount : Real) *
                theorem3SamplingOverhead cert rho * samplingKernel) := by ring
    _ ≤ ∑ _i : Fin D.componentCount,
          (rMax : Real) *
            (theorem3VolumeOverhead cert rho * volumeKernel +
              (sampleCap p D.componentCount : Real) *
                theorem3SamplingOverhead cert rho * samplingKernel) := by
      apply Finset.sum_le_sum
      intro i _hi
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Finset.le_sup
          (f := fun j : Fin D.componentCount =>
            (D.component j).presentation.facetCount) (Finset.mem_univ i)
      · exact add_nonneg
          (mul_nonneg hvolumeOverhead (theorem3VolumeKernel_nonneg n rho p.epsilon))
          (mul_nonneg (mul_nonneg (by positivity) hsamplingOverhead)
            (theorem3SamplingKernel_nonneg n rho))
    _ = theorem3DetailedRuntime D.componentCount n (theorem3RMax D)
          (theorem3Rho D) p.epsilon (sampleCap p D.componentCount)
          (theorem3VolumeOverhead cert (theorem3Rho D))
          (theorem3SamplingOverhead cert (theorem3Rho D)) := by
      simp [theorem3DetailedRuntime, rho, rMax, volumeKernel, samplingKernel]
      ring

private lemma theorem3DetailedRuntime_le_headline {componentCount n rMax : Nat}
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
    have hNrho : 1 ≤ N * rho ^ 2 := one_le_mul_of_one_le_of_one_le hN hrho2
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
            ring
  unfold theorem3DetailedRuntime theorem3HeadlineCore theorem3SuppressedFactor
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

/-- Theorem 3 for any concrete Model certificate. Its overheads are definitions computed
from that certificate, so this theorem has no componentwise oracle-bound hypothesis. -/
theorem certificate_operations_le_theorem3 {n k : Nat} (hn : 1 ≤ n)
    {F : LRAFormula n k} {D : Decomposition F} {p : ApproxParams}
    (cert : TTCMembershipRuntimeCertificate D p) :
    (cert.operations : Real) ≤
      theorem3HeadlineCore D.componentCount n (theorem3RMax D) (theorem3Rho D) *
        theorem3SuppressedFactor p.epsilon (sampleCap p D.componentCount)
          (theorem3VolumeOverhead cert (theorem3Rho D))
          (theorem3SamplingOverhead cert (theorem3Rho D)) := by
  exact (certificate_operations_le_theorem3Detailed hn cert).trans
    (theorem3DetailedRuntime_le_headline hn
      (by unfold theorem3Rho; exact le_max_left _ _) p.epsilon_pos
      (by positivity)
      (by unfold theorem3VolumeOverhead; positivity)
      (by unfold theorem3SamplingOverhead; positivity))

/-- Accounting bound for preprocessing plus the certificate fixed by `communityTTC`'s
imported CV18 and Hit-and-Run implementations. `preprocessingOperations` is the
externally measured cost of Boolean abstraction, DNF conversion, normalization, and
precision selection. This does not assert a bound on the cost of the measure-valued
`communityTTC` program itself. -/
theorem community_runtime_cost_bound {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations : Nat) :
    let D := prep.run F hbounded
    let b := (prep.choosePrecision D p).value
    let cert := communityMembershipRuntimeCertificate hn D b p
    (∀ i : Fin D.componentCount,
        CommunityCV18.MembershipCostCertified (by omega) (D.component i)
          p.epsilonPrime (p.deltaPrime D.componentCount)) ∧
      ((preprocessingOperations + cert.operations : Nat) : Real) ≤
        preprocessingOperations +
        theorem3HeadlineCore D.componentCount n (theorem3RMax D) (theorem3Rho D) *
          theorem3SuppressedFactor p.epsilon (sampleCap p D.componentCount)
            (theorem3VolumeOverhead cert (theorem3Rho D))
            (theorem3SamplingOverhead cert (theorem3Rho D)) := by
  dsimp only
  let D := prep.run F hbounded
  let b := (prep.choosePrecision D p).value
  let cert := communityMembershipRuntimeCertificate hn D b p
  constructor
  · exact community_volume_cost_certified hn D p
  · simpa only [Nat.cast_add, add_comm] using
      (add_le_add_left (certificate_operations_le_theorem3 (by omega) cert)
        (preprocessingOperations : Real))

/-- A TTC-specific Markov interface for a future costed implementation. The hypothesis
`houtput` identifies its estimate marginal with the manuscript TTC law. `hexpected`
is the still-missing operational cost theorem, with `extraExpectedOperations`
standing for deletion, thinning, Poisson bookkeeping, and sampler retries.
The conclusion has a linear `1 / failure` runtime cutoff. -/
theorem community_ttc_runtime_tail_of_expected_cost {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations extraExpectedOperations : Nat)
    (costed : Measure (NNReal × Nat))
    (_houtput : costed.map Prod.fst = communityManuscriptTTC hn F hbounded p prep)
    (hexpected :
      let D := prep.run F hbounded
      let b := (prep.choosePrecision D p).value
      let cert := communityMembershipRuntimeCertificate hn D b p
      ∫⁻ run, (run.2 : ENNReal) ∂costed ≤
        ((preprocessingOperations + cert.operations + extraExpectedOperations : Nat) :
          ENNReal))
    (failure : ENNReal) (hfailure0 : failure ≠ 0)
    (hfailureTop : failure ≠ ∞) :
    let D := prep.run F hbounded
    let b := (prep.choosePrecision D p).value
    let cert := communityMembershipRuntimeCertificate hn D b p
    costed {run | ((preprocessingOperations + cert.operations +
        extraExpectedOperations + 1 : Nat) : ENNReal) / failure ≤ run.2} ≤
      failure := by
  dsimp only at hexpected ⊢
  let D := prep.run F hbounded
  let b := (prep.choosePrecision D p).value
  let cert := communityMembershipRuntimeCertificate hn D b p
  let budget : Nat := preprocessingOperations + cert.operations +
    extraExpectedOperations + 1
  have hbudget0 : (budget : ENNReal) ≠ 0 := by
    simp [budget]
  have hbudgetTop : (budget : ENNReal) ≠ ∞ := by simp
  have hmean : ∫⁻ run, (run.2 : ENNReal) ∂costed ≤ (budget : ENNReal) := by
    exact hexpected.trans (by exact_mod_cast Nat.le_succ _)
  exact runtime_tail_le_of_expected_cost costed
    (fun run : NNReal × Nat => (run.2 : ENNReal)) (by fun_prop)
    budget failure hbudget0 hbudgetTop hfailure0 hfailureTop hmean

#print axioms runtime_tail_le_of_expected_cost
#print axioms community_ttc_runtime_tail_of_expected_cost
#print axioms CommunityCV18.membershipCostCertified
#print axioms CommunityCV18.membershipArithmeticCostBound
#print axioms certificate_operations_le_theorem3
#print axioms community_runtime_cost_bound

end PaperRuntime
end Kr25Ssmxt
