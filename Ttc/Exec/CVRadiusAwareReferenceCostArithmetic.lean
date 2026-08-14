import Ttc.Exec.CVGaussianScoreAwareConcretePhaseWitness
import Ttc.Exec.CVHybridSourceSharpEnvelope

/-!
# Radius-aware arithmetic for the constant-`2e` retained-history reference

This file separates the two deterministic layers in the retained-history cost route.

* The exact reference mean pays the adjacent-Gaussian reference warmness `2e`, not the
  operational warm certificate.
* Operational warmness enters only through the logarithm used by the literal adjustable
  deadline.
* The source hybrid proposal cancellation is then applied before comparison with
  `sourceOneRunQueryEnvelope`.

The final theorem isolates the two exact remaining scalar obligations.  This is sharper
than a uniform phase-count/deadline maximum: it permits the cold/hot weighted cancellation
from `CVHybridRuntimeAccounting`.
-/

namespace Ttc.CVRadiusAwareReferenceCostArithmetic

open Ttc.CVGaussianSourceSharpCost
open Ttc.CVGaussianScoreAwareParameters
open Ttc.CVGaussianScoreAwareSharpScheduleBound
open Ttc.CVGaussianAdaptiveMixing
open Ttc.CVHybridSchedule
open Ttc.CVHybridSourceSharpEnvelope
open Ttc.CVCorrectedRuntime
open Ttc.CVSourcePolynomialCutoffCapstone
open Arlib.GaussianCooling.Chunked
open scoped ENNReal BigOperators

/-- Literal retry-times-deadline accounting of all active score-aware phases. -/
noncomputable def scoreAwareRetryDeadlineAccounting
    (n m k : Nat) (eps delta : Real) (sigmaSq : Nat → Real)
    (slack boundSq : Nat → Real) (operationalWarm : Nat → ENNReal) : Real :=
  ∑ i ∈ Finset.range m,
    if i + 1 < m then
      (scoreAwareRetries m k eps slack boundSq i : Real) *
        (adjustableSpeedyDeadline n delta (sigmaSq i)
          ((2 * operationalWarm i) / scoreAwareEta m k eps slack boundSq i)
          (scoreAwareZeta m k eps slack boundSq i) : Real)
    else 0

theorem scoreAwareRetryDeadlineAccounting_nonneg
    (n m k : Nat) (eps delta : Real) (sigmaSq : Nat → Real)
    (slack boundSq : Nat → Real) (operationalWarm : Nat → ENNReal) :
    0 ≤ scoreAwareRetryDeadlineAccounting n m k eps delta sigmaSq
      slack boundSq operationalWarm := by
  unfold scoreAwareRetryDeadlineAccounting
  positivity

/-- Exact factorization of the reference-law phase sum.  The operational warmness is
absent from the multiplicative warm factor and survives only inside the deadline. -/
theorem sharpReferencePhaseSum_eq_retryDeadlineAccounting
    (n m k : Nat) (eps delta : Real) (sigmaSq : Nat → Real)
    (slack boundSq : Nat → Real) (operationalWarm : Nat → ENNReal) :
    (k : Real) * ∑ i ∈ Finset.range m,
        gaussianActiveMeanEnvelopeReal m (fun _ ↦ gaussianReferenceWarm)
          (scoreAwareGaussianSteps n delta sigmaSq m k eps slack boundSq operationalWarm)
          (scoreAwareRetries m k eps slack boundSq) i =
      10 * (2 * Real.exp 1) * (k : Real) *
        scoreAwareRetryDeadlineAccounting n m k eps delta sigmaSq
          slack boundSq operationalWarm := by
  rw [sharpReferencePhaseSum_scoreAware_eq]
  unfold scoreAwareRetryDeadlineAccounting
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> ring

/-- The weighted source hybrid core, before multiplying by the number of estimator draws. -/
noncomputable def sourceHybridProposalCore
    (n : Nat) (N s0 : Real) (J : Nat) (q : Real) : Real :=
  2 * coldPhases n s0 +
    4 * q ^ 2 * (n : Real) ^ 2 *
      adaptiveSourceHotSigmaMass N (coldEnd n s0) J

theorem proposalAccounting_one_eq
    (n k J : Nat) (N s0 q : Real) :
    proposalAccounting n N s0 J k 1 q =
      (k : Real) * sourceHybridProposalCore n N s0 J q := by
  unfold proposalAccounting sourceHybridProposalCore
  norm_num

/-- A weighted retry/deadline comparison is exactly enough to attach the literal
score-aware reference execution to the source hybrid proposal accounting.  Unlike the
old uniform `m*L*T` bound, this premise can retain cold/hot cancellation phase by phase. -/
theorem sharpReferencePhaseSum_le_hybridAccounting
    (n m k J : Nat) (eps delta N s0 q overhead : Real)
    (sigmaSq : Nat → Real) (slack boundSq : Nat → Real)
    (operationalWarm : Nat → ENNReal)
    (hoverhead0 : 0 ≤ overhead)
    (hweighted :
      scoreAwareRetryDeadlineAccounting n m k eps delta sigmaSq
          slack boundSq operationalWarm ≤
        overhead * sourceHybridProposalCore n N s0 J q) :
    (k : Real) * ∑ i ∈ Finset.range m,
        gaussianActiveMeanEnvelopeReal m (fun _ ↦ gaussianReferenceWarm)
          (scoreAwareGaussianSteps n delta sigmaSq m k eps slack boundSq operationalWarm)
          (scoreAwareRetries m k eps slack boundSq) i ≤
      10 * (2 * Real.exp 1) * overhead *
        proposalAccounting n N s0 J k 1 q := by
  rw [sharpReferencePhaseSum_eq_retryDeadlineAccounting,
    proposalAccounting_one_eq]
  have hk0 : (0 : Real) ≤ k := by positivity
  have href0 : 0 ≤ 10 * (2 * Real.exp 1) := by positivity
  calc
    10 * (2 * Real.exp 1) * (k : Real) *
        scoreAwareRetryDeadlineAccounting n m k eps delta sigmaSq
          slack boundSq operationalWarm ≤
      10 * (2 * Real.exp 1) * (k : Real) *
        (overhead * sourceHybridProposalCore n N s0 J q) := by
          gcongr
    _ = 10 * (2 * Real.exp 1) * overhead *
        ((k : Real) * sourceHybridProposalCore n N s0 J q) := by ring

/-- Substitute the exact-law weighted sample count and the proved cold/hot cancellation.
All schedule dependence is now in the one logarithmic retry/deadline overhead. -/
theorem sharpReferencePhaseSum_estimatorSamples_le_sourceSharp
    {n J : Nat} (hn : 1 ≤ n)
    {N s0 eps q delta overhead : Real}
    (hN : 0 < N) (hs0 : 0 < s0) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hbelow : ∀ j, j < J → adaptiveChunkStart N (coldEnd n s0) j ≤ N)
    (m : Nat) (sigmaSq : Nat → Real) (slack boundSq : Nat → Real)
    (operationalWarm : Nat → ENNReal)
    (hoverhead0 : 0 ≤ overhead)
    (hweighted :
      scoreAwareRetryDeadlineAccounting n m
          (estimatorSamples n (coldPhases n s0) J eps) eps delta sigmaSq
          slack boundSq operationalWarm ≤
        overhead * sourceHybridProposalCore n N s0 J q) :
    let k := estimatorSamples n (coldPhases n s0) J eps
    (k : Real) * ∑ i ∈ Finset.range m,
        gaussianActiveMeanEnvelopeReal m (fun _ ↦ gaussianReferenceWarm)
          (scoreAwareGaussianSteps n delta sigmaSq m k eps slack boundSq operationalWarm)
          (scoreAwareRetries m k eps slack boundSq) i ≤
      10 * (2 * Real.exp 1) * overhead *
        sourceSharpProposalEnvelope n N s0 eps J 1 q := by
  let k := estimatorSamples n (coldPhases n s0) J eps
  have href := sharpReferencePhaseSum_le_hybridAccounting n m k J eps delta
    N s0 q overhead sigmaSq slack boundSq operationalWarm hoverhead0 hweighted
  have hproposal := proposalAccounting_estimatorSamples_le_sourceSharp
    (n := n) (J := J) (r := 1) (q := q) hn hN hs0 heps heps1 hbelow
  dsimp only [k]
  exact href.trans (mul_le_mul_of_nonneg_left hproposal (by positivity))

/-- Final source-budget adapter.  `hweighted` is the exact radius-aware
retry/deadline lemma still required, and `hsource` is now a pure asymptotic arithmetic
comparison between the already-cancelled hybrid expression and the advertised source
envelope. -/
theorem sharpReferencePhaseSum_estimatorSamples_le_sourceBudget
    {runtimeConstant radius : Real} {n J : Nat} (hn : 1 ≤ n)
    {N s0 eps q delta overhead : Real}
    (hN : 0 < N) (hs0 : 0 < s0) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hbelow : ∀ j, j < J → adaptiveChunkStart N (coldEnd n s0) j ≤ N)
    (m : Nat) (sigmaSq : Nat → Real) (slack boundSq : Nat → Real)
    (operationalWarm : Nat → ENNReal)
    (hoverhead0 : 0 ≤ overhead)
    (hweighted :
      scoreAwareRetryDeadlineAccounting n m
          (estimatorSamples n (coldPhases n s0) J eps) eps delta sigmaSq
          slack boundSq operationalWarm ≤
        overhead * sourceHybridProposalCore n N s0 J q)
    (hsource : 10 * (2 * Real.exp 1) * overhead *
        sourceSharpProposalEnvelope n N s0 eps J 1 q ≤
      sourceOneRunQueryEnvelope runtimeConstant n radius eps) :
    let k := estimatorSamples n (coldPhases n s0) J eps
    (k : ENNReal) * ∑ i ∈ Finset.range m,
        gaussianActiveMeanEnvelope m (fun _ ↦ gaussianReferenceWarm)
          (scoreAwareGaussianSteps n delta sigmaSq m k eps slack boundSq operationalWarm)
          (scoreAwareRetries m k eps slack boundSq) i ≤
      sourceOneRunQueryBudget runtimeConstant n radius eps := by
  let k := estimatorSamples n (coldPhases n s0) J eps
  apply sharpPhaseSum_le_sourceBudget_of_real
  exact (sharpReferencePhaseSum_estimatorSamples_le_sourceSharp hn hN hs0 heps heps1
    hbelow m sigmaSq slack boundSq operationalWarm hoverhead0 hweighted).trans hsource

/-! ## Why an operational-warm upper bound is genuinely necessary -/

/-- The adjustable deadline is unbounded in its warm argument even after fixing an
arbitrary finite nonzero mixing tolerance.  This is the version needed by the literal
score-aware schedule, whose final argument is `scoreAwareZeta` rather than `1`. -/
theorem exists_adjustableSpeedyDeadline_gt_at
    (T : Nat) (eta : ENNReal) (heta0 : eta ≠ 0) (hetatop : eta ≠ ⊤) :
    ∃ M : ENNReal, M ≠ ⊤ ∧
      T < adjustableSpeedyDeadline 1 1 1 M eta := by
  let A : Real := ((T : Real) + 1) * Real.log 2 ^ 2 + 1
  let B : Real := A - 2 * Real.log (1 / eta.toReal)
  let M : ENNReal := ENNReal.ofReal (Real.exp B)
  refine ⟨M, by simp [M], ?_⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hspec := adjustableSpeedyDeadline_spec 1 1 1 M eta
  have hMreal : M.toReal = Real.exp B := by
    simp [M, (Real.exp_pos B).le]
  rw [hMreal, Real.log_exp] at hspec
  have hcombine : B + 2 * Real.log (1 / eta.toReal) = A := by
    dsimp only [B]
    ring
  rw [hcombine] at hspec
  have hstrict : (T : Real) <
      4 * 640 ^ 2 * 1 * ((1 : Nat) : Real) * A /
          (1 * Real.log 2) ^ 2 + 1 := by
    dsimp only [A]
    norm_num only [Nat.cast_one, mul_one, one_mul]
    field_simp [hlog2.ne']
    have hT0 : (0 : Real) ≤ T := by positivity
    nlinarith [sq_pos_of_pos hlog2]
  have hcast : (T : Real) <
      (adjustableSpeedyDeadline 1 1 1 M eta : Real) :=
    hstrict.trans_le hspec
  exact_mod_cast hcast

/-- No universal source-envelope comparison can quantify over an unrestricted
`operationalWarm`, even with a single active phase and all other scalar schedule inputs
fixed.  Thus the missing warm-recurrence upper bound is semantic, not an arithmetic
artifact of the hybrid cancellation. -/
theorem exists_operationalWarm_sharpReferencePhaseSum_gt_sourceEnvelope
    (runtimeConstant radius : Real) :
    ∃ operationalWarm : Nat → ENNReal,
      sourceOneRunQueryEnvelope runtimeConstant 1 radius (1 / 2) <
        (1 : Real) * ∑ i ∈ Finset.range 2,
          gaussianActiveMeanEnvelopeReal 2 (fun _ ↦ gaussianReferenceWarm)
            (scoreAwareGaussianSteps 1 1 (fun _ ↦ 1) 2 1 (1 / 2)
              (fun _ ↦ 1) (fun _ ↦ 1) operationalWarm)
            (scoreAwareRetries 2 1 (1 / 2) (fun _ ↦ 1) (fun _ ↦ 1)) i := by
  let share := scoreAwareShare 2 1 (1 / 2) (fun _ ↦ 1) (fun _ ↦ 1) 0
  let etaWarm := scoreAwareEta 2 1 (1 / 2) (fun _ ↦ 1) (fun _ ↦ 1) 0
  let etaMix := scoreAwareZeta 2 1 (1 / 2) (fun _ ↦ 1) (fun _ ↦ 1) 0
  have hshare : 0 < share := by
    exact scoreAwareShare_pos (m := 2) (k := 1)
      (by norm_num : (0 : Real) < 1 / 2) (fun _ ↦ by norm_num)
      (fun _ ↦ by norm_num) 0
  have hetaWarm0 : etaWarm ≠ 0 := by
    apply ne_of_gt
    change 0 < ENNReal.ofReal share
    rw [ENNReal.ofReal_pos]
    exact hshare
  have hetaWarmTop : etaWarm ≠ ⊤ := by
    simp [etaWarm, scoreAwareEta]
  have hetaMix0 : etaMix ≠ 0 := by
    apply ne_of_gt
    change 0 < ENNReal.ofReal (share / 32)
    rw [ENNReal.ofReal_pos]
    exact div_pos hshare (by norm_num)
  have hetaMixTop : etaMix ≠ ⊤ := by
    simp [etaMix, scoreAwareZeta]
  obtain ⟨T, hT⟩ :=
    exists_nat_gt (sourceOneRunQueryEnvelope runtimeConstant 1 radius (1 / 2))
  obtain ⟨M, hMtop, hdeadline⟩ :=
    exists_adjustableSpeedyDeadline_gt_at T etaMix hetaMix0 hetaMixTop
  let operationalWarm : Nat → ENNReal := fun _ ↦ M * etaWarm / 2
  refine ⟨operationalWarm, ?_⟩
  have hwarmarg : (2 * operationalWarm 0) / etaWarm = M := by
    have htwo0 : (2 : ENNReal) ≠ 0 := by norm_num
    have htwotop : (2 : ENNReal) ≠ ⊤ := by norm_num
    have hinner : 2 * operationalWarm 0 = M * etaWarm := by
      dsimp only [operationalWarm]
      rw [div_eq_mul_inv]
      calc
        2 * (M * etaWarm * 2⁻¹) = M * etaWarm * (2 * 2⁻¹) := by ac_rfl
        _ = M * etaWarm := by
          rw [ENNReal.mul_inv_cancel htwo0 htwotop, mul_one]
    rw [hinner]
    exact ENNReal.mul_div_cancel_right hetaWarm0 hetaWarmTop
  have hretries : (1 : Real) ≤
      scoreAwareRetries 2 1 (1 / 2) (fun _ ↦ 1) (fun _ ↦ 1) 0 := by
    have hindex := Ttc.CVAdaptive.explicitDyadicTailIndex_pos hshare
      (scoreAwareShare_lt_one (m := 2) (k := 1)
        (by norm_num : (0 : Real) < 1 / 2) (by norm_num) 0)
    have hrNat : 1 ≤
        scoreAwareRetries 2 1 (1 / 2) (fun _ ↦ 1) (fun _ ↦ 1) 0 := by
      rw [scoreAwareRetries]
      change 1 ≤ 16 * Ttc.CVAdaptive.explicitDyadicTailIndex share
      omega
    exact_mod_cast hrNat
  simp only [one_mul, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [gaussianActiveMeanEnvelopeReal_scoreAware,
    gaussianActiveMeanEnvelopeReal_scoreAware]
  norm_num only [Nat.reduceAdd, Nat.reduceLT, if_true, if_false, add_zero]
  change sourceOneRunQueryEnvelope runtimeConstant 1 radius (1 / 2) <
    10 * (scoreAwareRetries 2 1 (1 / 2) (fun _ ↦ 1) (fun _ ↦ 1) 0 : Real) *
      (adjustableSpeedyDeadline 1 1 1
        ((2 * operationalWarm 0) /
          scoreAwareEta 2 1 (1 / 2) (fun _ ↦ 1) (fun _ ↦ 1) 0)
        (scoreAwareZeta 2 1 (1 / 2) (fun _ ↦ 1) (fun _ ↦ 1) 0) : Real) *
      (2 * Real.exp 1)
  rw [show scoreAwareEta 2 1 (1 / 2) (fun _ ↦ 1) (fun _ ↦ 1) 0 = etaWarm by rfl,
    show scoreAwareZeta 2 1 (1 / 2) (fun _ ↦ 1) (fun _ ↦ 1) 0 = etaMix by rfl,
    hwarmarg]
  have hdeadlineReal : (T : Real) <
      (adjustableSpeedyDeadline 1 1 1 M etaMix : Real) := by
    exact_mod_cast hdeadline
  calc
    sourceOneRunQueryEnvelope runtimeConstant 1 radius (1 / 2) < (T : Real) := hT
    _ < (adjustableSpeedyDeadline 1 1 1 M etaMix : Real) := hdeadlineReal
    _ ≤ 10 * (scoreAwareRetries 2 1 (1 / 2)
          (fun _ ↦ 1) (fun _ ↦ 1) 0 : Real) *
        (adjustableSpeedyDeadline 1 1 1 M etaMix : Real) *
        (2 * Real.exp 1) := by
      have hd0 : (0 : Real) ≤ adjustableSpeedyDeadline 1 1 1 M etaMix := by
        positivity
      have he : 1 ≤ 2 * Real.exp 1 := by
        nlinarith [Real.exp_one_gt_d9]
      calc
        (adjustableSpeedyDeadline 1 1 1 M etaMix : Real) =
            1 * (adjustableSpeedyDeadline 1 1 1 M etaMix : Real) * 1 := by ring
        _ ≤ 10 * (scoreAwareRetries 2 1 (1 / 2)
              (fun _ ↦ 1) (fun _ ↦ 1) 0 : Real) *
            (adjustableSpeedyDeadline 1 1 1 M etaMix : Real) *
            (2 * Real.exp 1) := by
          gcongr
          nlinarith

/-!
The current library cannot discharge `hweighted` from positivity/finiteness alone.
`exists_adjustableSpeedyDeadline_gt` proves that the literal deadline is unbounded as the
admitted operational warmness grows.  Therefore a concrete retained-history capstone must
use the minimal warm recurrence (or a sharper joint-history warm theorem) and a quantitative
lower bound on `scoreAwareShare`; merely knowing that both are finite is insufficient.
-/

#print axioms sharpReferencePhaseSum_eq_retryDeadlineAccounting
#print axioms proposalAccounting_one_eq
#print axioms sharpReferencePhaseSum_le_hybridAccounting
#print axioms sharpReferencePhaseSum_estimatorSamples_le_sourceSharp
#print axioms sharpReferencePhaseSum_estimatorSamples_le_sourceBudget
#print axioms exists_adjustableSpeedyDeadline_gt_at
#print axioms exists_operationalWarm_sharpReferencePhaseSum_gt_sourceEnvelope

end Ttc.CVRadiusAwareReferenceCostArithmetic
