import Ttc.Exec.CVColdOperationalTransition
import Ttc.Exec.CVHybridOperationalWarmLog
import Ttc.Exec.CVGaussianScoreAwareSharpScheduleBound
import Ttc.Exec.CVHotRefreshHonestRuntime
import Ttc.Exec.CVColdRefreshWarmEnvelope
import Ttc.Exec.CVGaussianColdHotRecursiveStep
import Ttc.Exec.CVWarmBudgetRecurrence

/-!
# Cold actual-warm deadlines and retained-reference cost

The mixing deadline is selected from the (possibly compounding) actual-path warmness.
The expected cost, however, is evaluated on the separate retained reference schedule.
This file keeps those two quantities separate and supplies the deterministic arithmetic
needed by the concrete cold schedule.
-/

set_option autoImplicit false

namespace Ttc.CVColdActualWarmReferenceCostArithmetic

open Ttc.CVGaussianAdaptiveMixing
open Ttc.CVGaussianScoreAwareSharpScheduleBound
open Ttc.CVGaussianScoreAwareParameters
open Ttc.CVHybridOperationalWarmLog
open Ttc.CVColdOperationalTransition
open Ttc.CVHotRefreshHonestRuntime
open Ttc.CVColdRefreshWarmEnvelope
open Ttc.CVSourceTruncatedFixedCost
open Ttc.CVCorrectedFixedBlockCost
open Ttc.CVGaussianColdHotRecursiveStep
open Ttc.CVColdResetSeedWarm
open Ttc.CVWarmBudgetRecurrence
open scoped ENNReal BigOperators

/-- Logarithmic payload dominating the adjustable deadline when actual warmth follows
`hybridOperationalWarm`. -/
noncomputable def coldActualWarmDeadlineLogEnvelope
    (n L i : Nat) (M0 eta zeta : ENNReal) : Real :=
  (i : Real) * Real.log (hybridOperationalWarmBase n L).toReal +
    Real.log M0.toReal + Real.log 2 + Real.log (1 / eta.toReal) +
      2 * Real.log (1 / zeta.toReal)

/-- Closed natural-number deadline corresponding to the logarithmic envelope. -/
noncomputable def coldActualWarmDeadlineEnvelope
    (n L i : Nat) (delta sigmaSq : Real) (M0 eta zeta : ENNReal) : Nat :=
  ⌈4 * 640 ^ 2 * sigmaSq * (n : Real) *
      coldActualWarmDeadlineLogEnvelope n L i M0 eta zeta /
        (delta * Real.log 2) ^ 2 + 1⌉₊ + 1

theorem coldActualWarmDeadlineLogEnvelope_nonneg
    {n L i : Nat} {M0 eta zeta : ENNReal}
    (hM0 : 1 ≤ M0) (hM0top : M0 ≠ ⊤)
    (heta0 : eta ≠ 0) (hetatop : eta ≠ ⊤) (heta1 : eta ≤ 1)
    (hzeta0 : zeta ≠ 0) (hzetatop : zeta ≠ ⊤) (hzeta1 : zeta ≤ 1) :
    0 ≤ coldActualWarmDeadlineLogEnvelope n L i M0 eta zeta := by
  have hbaseTop : hybridOperationalWarmBase n L ≠ ⊤ := by
    unfold hybridOperationalWarmBase
    exact (ENNReal.add_ne_top).2
      ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top L)
        (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top), by norm_num⟩
  have hbaseReal : 1 ≤ (hybridOperationalWarmBase n L).toReal := by
    have h := ENNReal.toReal_mono hbaseTop
      (show (1 : ENNReal) ≤ hybridOperationalWarmBase n L by
        unfold hybridOperationalWarmBase
        exact le_add_left le_rfl)
    simpa using h
  have hM0Real : 1 ≤ M0.toReal := by
    simpa using ENNReal.toReal_mono hM0top hM0
  have hetaPos : 0 < eta.toReal := ENNReal.toReal_pos heta0 hetatop
  have hzetaPos : 0 < zeta.toReal := ENNReal.toReal_pos hzeta0 hzetatop
  have hetaReal : eta.toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono (by norm_num : (1 : ENNReal) ≠ ⊤) heta1
  have hzetaReal : zeta.toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono (by norm_num : (1 : ENNReal) ≠ ⊤) hzeta1
  have hetaInv : 1 ≤ 1 / eta.toReal := by
    rw [le_div_iff₀ hetaPos]
    simpa using hetaReal
  have hzetaInv : 1 ≤ 1 / zeta.toReal := by
    rw [le_div_iff₀ hzetaPos]
    simpa using hzetaReal
  have hlogBase := Real.log_nonneg hbaseReal
  have hlogM0 := Real.log_nonneg hM0Real
  have hlogTwo : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hlogEta := Real.log_nonneg hetaInv
  have hlogZeta := Real.log_nonneg hzetaInv
  have hi0 : (0 : Real) ≤ i := by positivity
  unfold coldActualWarmDeadlineLogEnvelope
  positivity

theorem coldActualWarm_deadlineLogPayload_le
    {n L i : Nat} {N s0 : Real} {retries : Nat → Nat}
    {M0 eta zeta : ENNReal}
    (hM0 : 1 ≤ M0) (hM0top : M0 ≠ ⊤)
    (hretries : ∀ j, retries j ≤ L)
    (hrate0 : ∀ j, 0 ≤ Ttc.CVHybridSchedule.phaseRate n N s0 j)
    (hrateHalf : ∀ j, Ttc.CVHybridSchedule.phaseRate n N s0 j ≤ 1 / 2)
    (heta0 : eta ≠ 0) (hetatop : eta ≠ ⊤)
    (hzeta0 : zeta ≠ 0) (hzetatop : zeta ≠ ⊤) :
    Real.log (((2 * hybridOperationalWarm n N s0 retries M0 i) / eta).toReal) +
        2 * Real.log (1 / zeta.toReal) ≤
      coldActualWarmDeadlineLogEnvelope n L i M0 eta zeta := by
  have hlogWarm := log_hybridOperationalWarm_toReal_le
    hM0 hM0top hretries hrate0 hrateHalf i
  have hwarmTop : hybridOperationalWarm n N s0 retries M0 i ≠ ⊤ := by
    apply ne_top_of_le_ne_top _
      (hybridOperationalWarm_le_pow_envelope hM0 hretries hrate0 hrateHalf i)
    exact ENNReal.mul_ne_top
      (ENNReal.pow_ne_top (by
        unfold hybridOperationalWarmBase
        exact (ENNReal.add_ne_top).2
          ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top L)
            (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top), by norm_num⟩))
      hM0top
  have hwarmPos : 0 < (hybridOperationalWarm n N s0 retries M0 i).toReal := by
    exact ENNReal.toReal_pos
      (ne_of_gt ((by norm_num : (0 : ENNReal) < 1).trans_le
        (one_le_hybridOperationalWarm hM0 i))) hwarmTop
  have hetaPos : 0 < eta.toReal := ENNReal.toReal_pos heta0 hetatop
  rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    Real.log_div (mul_ne_zero (by norm_num) hwarmPos.ne') hetaPos.ne',
    Real.log_mul (by norm_num) hwarmPos.ne']
  unfold coldActualWarmDeadlineLogEnvelope
  have hlogEta : -Real.log eta.toReal = Real.log (1 / eta.toReal) := by
    rw [one_div, Real.log_inv]
  linarith [hlogEta]

/-- The literal cold adjustable deadline is controlled by the affine log-warm envelope.
No retained-reference warm factor occurs in this statement. -/
theorem adjustableSpeedyDeadline_coldActualWarm_le
    {n L i : Nat} {N s0 delta sigmaSq : Real} {retries : Nat → Nat}
    {M0 eta zeta : ENNReal}
    (hM0 : 1 ≤ M0) (hM0top : M0 ≠ ⊤)
    (hretries : ∀ j, retries j ≤ L)
    (hrate0 : ∀ j, 0 ≤ Ttc.CVHybridSchedule.phaseRate n N s0 j)
    (hrateHalf : ∀ j, Ttc.CVHybridSchedule.phaseRate n N s0 j ≤ 1 / 2)
    (heta0 : eta ≠ 0) (hetatop : eta ≠ ⊤)
    (hzeta0 : zeta ≠ 0) (hzetatop : zeta ≠ ⊤)
    (hdelta : delta ≠ 0) (hsigma : 0 ≤ sigmaSq) :
    adjustableSpeedyDeadline n delta sigmaSq
        ((2 * hybridOperationalWarm n N s0 retries M0 i) / eta) zeta ≤
      coldActualWarmDeadlineEnvelope n L i delta sigmaSq M0 eta zeta := by
  apply adjustableSpeedyDeadline_le_ceil_of_expression_le
  have hpayload := coldActualWarm_deadlineLogPayload_le
    (i := i) hM0 hM0top hretries hrate0 hrateHalf heta0 hetatop hzeta0 hzetatop
  have hcoef : 0 ≤ 4 * 640 ^ 2 * sigmaSq * (n : Real) := by positivity
  have hden : 0 < (delta * Real.log 2) ^ 2 := by
    exact sq_pos_of_ne_zero (mul_ne_zero hdelta (Real.log_pos (by norm_num)).ne')
  unfold adjustableSpeedyDeadlineExpression
  simpa only [add_comm] using add_le_add_right
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpayload hcoef) hden.le) 1

/-! The next lemma is deliberately generic in the operational step and retry functions.
It is the bridge used by a concrete constructor while those functions are assembled
from score-aware tolerances. -/

theorem coldReferenceRetrySum_le_of_bounds
    {cold L D : Nat} {referenceWarm : Nat → ENNReal} {W : ENNReal}
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (hretries : ∀ i, i < cold → retries i ≤ L)
    (hsteps : ∀ i j, i < cold → j < retries i → steps i j ≤ D)
    (hwarm : ∀ i, i < cold → referenceWarm i ≤ W) :
    ∑ i ∈ Finset.range cold,
        ∑ j ∈ Finset.range (retries i),
          10 * ((steps i j : ENNReal) * referenceWarm i) ≤
      (cold : ENNReal) * ((L : ENNReal) *
        (10 * ((D : ENNReal) * W))) := by
  calc
    ∑ i ∈ Finset.range cold,
        ∑ j ∈ Finset.range (retries i),
          10 * ((steps i j : ENNReal) * referenceWarm i) ≤
      ∑ i ∈ Finset.range cold,
        ∑ _j ∈ Finset.range (retries i),
          10 * ((D : ENNReal) * W) := by
            apply Finset.sum_le_sum
            intro i hi
            apply Finset.sum_le_sum
            intro j hj
            gcongr
            · exact_mod_cast hsteps i j (Finset.mem_range.mp hi)
                (Finset.mem_range.mp hj)
            · exact hwarm i (Finset.mem_range.mp hi)
    _ ≤ ∑ _i ∈ Finset.range cold,
        (L : ENNReal) * (10 * ((D : ENNReal) * W)) := by
          apply Finset.sum_le_sum
          intro i hi
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          gcongr
          exact_mod_cast hretries i (Finset.mem_range.mp hi)
    _ = (cold : ENNReal) * ((L : ENNReal) *
        (10 * ((D : ENNReal) * W))) := by simp

/-- Phasewise variant, retaining the varying deadline instead of replacing it by a
global maximum.  This is the form needed for cold-variance cancellation. -/
theorem coldReferenceRetrySum_le_phasewise
    {cold L : Nat} {D : Nat → Nat} {referenceWarm : Nat → ENNReal} {W : ENNReal}
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (hretries : ∀ i, i < cold → retries i ≤ L)
    (hsteps : ∀ i j, i < cold → j < retries i → steps i j ≤ D i)
    (hwarm : ∀ i, i < cold → referenceWarm i ≤ W) :
    ∑ i ∈ Finset.range cold,
        ∑ j ∈ Finset.range (retries i),
          10 * ((steps i j : ENNReal) * referenceWarm i) ≤
      ∑ i ∈ Finset.range cold,
        (L : ENNReal) * (10 * ((D i : ENNReal) * W)) := by
  apply Finset.sum_le_sum
  intro i hi
  calc
    ∑ j ∈ Finset.range (retries i),
        10 * ((steps i j : ENNReal) * referenceWarm i) ≤
      ∑ _j ∈ Finset.range (retries i),
        10 * ((D i : ENNReal) * W) := by
          apply Finset.sum_le_sum
          intro j hj
          gcongr
          · exact_mod_cast hsteps i j (Finset.mem_range.mp hi)
              (Finset.mem_range.mp hj)
          · exact hwarm i (Finset.mem_range.mp hi)
    _ ≤ (L : ENNReal) * (10 * ((D i : ENNReal) * W)) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      gcongr
      exact_mod_cast hretries i (Finset.mem_range.mp hi)

/-- One constant bounds the entire retained cold reference schedule.  Crucially, it
does not contain the actual-path recurrence. -/
noncomputable def coldRetainedReferenceWarmCap (n : Nat) (M0 : ENNReal) : ENNReal :=
  max M0 (coldSuccessorWarmConstant n)

theorem coldOperationalWarmSchedule_le_cap
    (n : Nat) (M0 : ENNReal) (i : Nat) :
    coldOperationalWarmSchedule M0 n i ≤ coldRetainedReferenceWarmCap n M0 := by
  cases i with
  | zero => exact le_max_left _ _
  | succ i => exact le_max_right _ _

theorem coldRetainedReferenceWarmCap_ne_top
    {M0 : ENNReal} (hM0top : M0 ≠ ⊤) (n : Nat) :
    coldRetainedReferenceWarmCap n M0 ≠ ⊤ := by
  unfold coldRetainedReferenceWarmCap coldSuccessorWarmConstant
  exact max_ne_top hM0top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num)))

/-- The changing-body cold reference factor is dimension-uniform.  The coarse constant
`18` is chosen to keep the downstream runtime arithmetic elementary. -/
theorem coldSuccessorWarmConstant_le_eighteen
    {n : Nat} (hn : 1 ≤ n) :
    coldSuccessorWarmConstant n ≤ 18 := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  have hnPos : (0 : Real) < n := by positivity
  have hc : 0 < c := by
    dsimp only [c]
    have : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hcHalf : (1 / 2 : Real) ≤ c := by
    dsimp only [c]
    have : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hnegLog : -Real.log c ≤ c⁻¹ - 1 := by
    linarith [Real.one_sub_inv_le_log_of_pos hc]
  have hinvGap : (n : Real) * (c⁻¹ - 1) ≤ 1 := by
    have hcne : c ≠ 0 := hc.ne'
    have hden : 0 < 2 * (n : Real) - 1 := by linarith
    have hcInv : c⁻¹ = (2 * (n : Real)) / (2 * (n : Real) - 1) := by
      dsimp only [c]
      field_simp [hnPos.ne', hden.ne']
    have heq : (n : Real) * (c⁻¹ - 1) =
        (n : Real) / (2 * (n : Real) - 1) := by
      rw [hcInv]
      rw [div_sub_one hden.ne']
      have hnum : 2 * (n : Real) - (2 * (n : Real) - 1) = 1 := by ring
      rw [hnum, one_div, div_eq_mul_inv]
    rw [heq, div_le_one hden]
    linarith
  have hlogPow : Real.log (c⁻¹ ^ n) ≤ 1 := by
    rw [Real.log_pow, Real.log_inv]
    nlinarith [mul_le_mul_of_nonneg_left hnegLog (Nat.cast_nonneg n)]
  have hpow : c⁻¹ ^ n ≤ Real.exp 1 :=
    (Real.log_le_iff_le_exp (pow_pos (inv_pos.mpr hc) n)).mp hlogPow
  have he1 : Real.exp 1 ≤ 3 := (Real.exp_one_lt_three).le
  have heHalf : Real.exp (1 / 2) ≤ 3 := by
    exact (Real.exp_le_exp.2 (by norm_num : (1 / 2 : Real) ≤ 1)).trans he1
  unfold coldSuccessorWarmConstant
  dsimp only [c] at hpow
  calc
    ENNReal.ofReal ((1 - 1 / (2 * (n : Real)))⁻¹ ^ n) *
          (ENNReal.ofReal (Real.exp (1 / 2)) * 2) ≤
        ENNReal.ofReal (Real.exp 1) *
          (ENNReal.ofReal (Real.exp (1 / 2)) * 2) := by gcongr
    _ ≤ ENNReal.ofReal 3 * (ENNReal.ofReal 3 * 2) := by
      gcongr
    _ = 18 := by norm_num

theorem coldRetainedReferenceWarmCap_le_eighteen
    {n : Nat} (hn : 1 ≤ n) {M0 : ENNReal} (hM0 : M0 ≤ 18) :
    coldRetainedReferenceWarmCap n M0 ≤ 18 := by
  exact max_le hM0 (coldSuccessorWarmConstant_le_eighteen hn)

/-! ## Sharp cold-only actual recurrence -/

/-- Actual-path cold warmth after charging the survival-weighted fallback by one. -/
noncomputable def coldActualWarm
    (n : Nat) (retries : Nat → Nat) (M0 : ENNReal) : Nat → ENNReal
  | 0 => M0
  | i + 1 => (retries i : ENNReal) *
      ((16 * coldSuccessorWarmConstant n) * coldActualWarm n retries M0 i) + 1

/-- Dimension-uniform geometric base for the cold recurrence. -/
noncomputable def coldActualWarmBase (L : Nat) : ENNReal :=
  (L : ENNReal) * (16 * 18) + 1

theorem one_le_coldActualWarm
    {n : Nat} {retries : Nat → Nat} {M0 : ENNReal} (hM0 : 1 ≤ M0) :
    ∀ i, 1 ≤ coldActualWarm n retries M0 i := by
  intro i
  cases i with
  | zero => exact hM0
  | succ i => rw [coldActualWarm]; exact le_add_left le_rfl

theorem coldActualWarm_le_pow_envelope
    {n L : Nat} (hn : 1 ≤ n) {retries : Nat → Nat} {M0 : ENNReal}
    (hM0 : 1 ≤ M0) (hretries : ∀ i, retries i ≤ L) :
    ∀ i, coldActualWarm n retries M0 i ≤ coldActualWarmBase L ^ i * M0 := by
  intro i
  induction i with
  | zero => simp [coldActualWarm]
  | succ i ih =>
      rw [coldActualWarm, pow_succ]
      have hretry : (retries i : ENNReal) ≤ L := by exact_mod_cast hretries i
      have hwarmOne := one_le_coldActualWarm
        (n := n) (retries := retries) hM0 i
      calc
        (retries i : ENNReal) *
              ((16 * coldSuccessorWarmConstant n) * coldActualWarm n retries M0 i) + 1 ≤
            coldActualWarmBase L * coldActualWarm n retries M0 i := by
          unfold coldActualWarmBase
          calc
            (retries i : ENNReal) *
                  ((16 * coldSuccessorWarmConstant n) *
                    coldActualWarm n retries M0 i) + 1 ≤
                (L : ENNReal) * ((16 * 18) *
                    coldActualWarm n retries M0 i) +
                  coldActualWarm n retries M0 i := by
                    gcongr
                    exact coldSuccessorWarmConstant_le_eighteen hn
            _ = ((L : ENNReal) * (16 * 18) + 1) *
                coldActualWarm n retries M0 i := by ring
        _ ≤ coldActualWarmBase L * (coldActualWarmBase L ^ i * M0) := by gcongr
        _ = coldActualWarmBase L ^ i * M0 * coldActualWarmBase L := by ac_rfl
        _ = coldActualWarmBase L ^ i * coldActualWarmBase L * M0 := by
          rw [mul_assoc, mul_comm M0 (coldActualWarmBase L), ← mul_assoc]

theorem log_coldActualWarm_toReal_le
    {n L : Nat} (hn : 1 ≤ n) {retries : Nat → Nat} {M0 : ENNReal}
    (hM0 : 1 ≤ M0) (hM0top : M0 ≠ ⊤)
    (hretries : ∀ i, retries i ≤ L) (i : Nat) :
    Real.log (coldActualWarm n retries M0 i).toReal ≤
      (i : Real) * Real.log (coldActualWarmBase L).toReal + Real.log M0.toReal := by
  have hbaseTop : coldActualWarmBase L ≠ ⊤ := by
    unfold coldActualWarmBase
    exact (ENNReal.add_ne_top).2
      ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top L) (by norm_num), by norm_num⟩
  have htop : coldActualWarm n retries M0 i ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (coldActualWarm_le_pow_envelope hn hM0 hretries i)
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top hbaseTop) hM0top
  have hwarmPos : 0 < (coldActualWarm n retries M0 i).toReal :=
    ENNReal.toReal_pos
      (ne_of_gt ((by norm_num : (0 : ENNReal) < 1).trans_le
        (one_le_coldActualWarm hM0 i))) htop
  have hbound := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top hbaseTop) hM0top)
    (coldActualWarm_le_pow_envelope hn hM0 hretries i)
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow] at hbound
  have hlog := Real.log_le_log hwarmPos hbound
  have hbasePos : 0 < (coldActualWarmBase L).toReal := by
    exact ENNReal.toReal_pos
      (by unfold coldActualWarmBase; positivity) hbaseTop
  have hM0pos : 0 < M0.toReal :=
    ENNReal.toReal_pos (ne_of_gt ((by norm_num : (0 : ENNReal) < 1).trans_le hM0)) hM0top
  rw [Real.log_mul (pow_ne_zero i hbasePos.ne') hM0pos.ne', Real.log_pow] at hlog
  simpa [mul_comm] using hlog

/-- The exact accepted coefficient used by the recursive concrete cold schedule is
bounded by a dimension-free multiple of the retry cap. -/
theorem coldAcceptedFactor_le_retryEnvelope
    {n L : Nat} (hn : 1 ≤ n) {retries : Nat → Nat}
    (hretries : ∀ i, retries i ≤ L) (i : Nat) :
    coldAcceptedFactor n retries i ≤ max 1 ((L : ENNReal) * 288) := by
  unfold coldAcceptedFactor
  apply max_le_max le_rfl
  calc
    (retries i : ENNReal) *
          (16 * (ENNReal.ofReal (((1 - 1 / (2 * (n : Real)))⁻¹) ^ n) *
            (ENNReal.ofReal (Real.exp (1 / 2)) * 2))) ≤
        (L : ENNReal) * (16 * 18) := by
          gcongr
          · exact_mod_cast hretries i
          · simpa only [coldSuccessorWarmConstant] using
              coldSuccessorWarmConstant_le_eighteen hn
    _ = (L : ENNReal) * 288 := by norm_num

theorem coldResetTruncatedWarmConst_le_six_pow
    (n i : Nat) :
    coldResetTruncatedWarmConst n i ≤ 2 * (6 : ENNReal) ^ i := by
  have he : ENNReal.ofReal (Real.exp (1 / 2)) ≤ 3 := by
    simpa using ENNReal.ofReal_le_ofReal
      ((Real.exp_le_exp.2 (by norm_num : (1 / 2 : Real) ≤ 1)).trans
        (Real.exp_one_lt_three.le))
  unfold coldResetTruncatedWarmConst
  rw [show ENNReal.ofReal 2 = (2 : ENNReal) by norm_num]
  calc
    2 * (ENNReal.ofReal (Real.exp (1 / 2)) * 2) ^ i ≤
        2 * (3 * 2 : ENNReal) ^ i := by gcongr
    _ = 2 * (6 : ENNReal) ^ i := by norm_num

theorem coldResetFullWarmConst_le_six_pow (i : Nat) :
    coldResetFullWarmConst i ≤ 2 * (6 : ENNReal) ^ i := by
  have he : ENNReal.ofReal (Real.exp (1 / 2)) ≤ 6 := by
    calc
      ENNReal.ofReal (Real.exp (1 / 2)) ≤ ENNReal.ofReal 3 := by
        apply ENNReal.ofReal_le_ofReal
        exact (Real.exp_le_exp.2 (by norm_num : (1 / 2 : Real) ≤ 1)).trans
          (Real.exp_one_lt_three.le)
      _ ≤ 6 := by norm_num
  unfold coldResetFullWarmConst
  simpa only [ENNReal.ofReal_ofNat] using
    (mul_le_mul_left' (pow_le_pow_left' he i) (2 : ENNReal))

/-- A single phase of the exact concrete cold recurrence is bounded by a linear retry
term times `6^(i+1)`.  Summing its logarithm therefore produces a quadratic phase term,
not an exponential runtime factor. -/
theorem coldAccepted_add_fallback_le_productEnvelope
    {n cold L : Nat} (hn : 1 ≤ n) {retries : Nat → Nat}
    (hretries : ∀ i, retries i ≤ L) {i : Nat} (hi : i < cold) :
    coldAcceptedFactor n retries i +
        (if i + 1 < cold then coldResetTruncatedWarmConst n (i + 1)
          else coldResetFullWarmConst (i + 1)) ≤
      (max 1 ((L : ENNReal) * 288) + 2) * (6 : ENNReal) ^ (i + 1) := by
  have hpow : (1 : ENNReal) ≤ 6 ^ (i + 1) := one_le_pow₀ (by norm_num)
  have ha := coldAcceptedFactor_le_retryEnvelope hn hretries i
  have hf : (if i + 1 < cold then coldResetTruncatedWarmConst n (i + 1)
      else coldResetFullWarmConst (i + 1)) ≤ 2 * (6 : ENNReal) ^ (i + 1) := by
    split_ifs
    · exact coldResetTruncatedWarmConst_le_six_pow n (i + 1)
    · exact coldResetFullWarmConst_le_six_pow (i + 1)
  calc
    _ ≤ max 1 ((L : ENNReal) * 288) + 2 * (6 : ENNReal) ^ (i + 1) :=
      add_le_add ha hf
    _ ≤ max 1 ((L : ENNReal) * 288) * (6 : ENNReal) ^ (i + 1) +
        2 * (6 : ENNReal) ^ (i + 1) := by
          gcongr
          exact le_mul_of_one_le_right' hpow
    _ = (max 1 ((L : ENNReal) * 288) + 2) * (6 : ENNReal) ^ (i + 1) := by ring

noncomputable def coldConcreteFallbackFactor
    (n cold i : Nat) : ENNReal :=
  if i + 1 < cold then coldResetTruncatedWarmConst n (i + 1)
  else coldResetFullWarmConst (i + 1)

theorem coldConcreteFallbackFactor_le_six_pow (n cold i : Nat) :
    coldConcreteFallbackFactor n cold i ≤ 2 * (6 : ENNReal) ^ (i + 1) := by
  unfold coldConcreteFallbackFactor
  split_ifs
  · exact coldResetTruncatedWarmConst_le_six_pow n (i + 1)
  · exact coldResetFullWarmConst_le_six_pow (i + 1)

/-- A single constant base absorbs both the accepted multiplier and the geometrically
growing additive fallback.  This is sharper than multiplying all additive fallback
factors and is the key to an affine, rather than quadratic, deadline logarithm. -/
noncomputable def coldLinearWarmBase (L : Nat) : ENNReal :=
  max 1 ((L : ENNReal) * 288) + 12

theorem six_le_coldLinearWarmBase (L : Nat) :
    (6 : ENNReal) ≤ coldLinearWarmBase L := by
  unfold coldLinearWarmBase
  calc
    (6 : ENNReal) ≤ 1 + 12 := by norm_num
    _ ≤ max 1 ((L : ENNReal) * 288) + 12 := by
      simpa only [add_comm] using
        add_le_add_right (le_max_left 1 ((L : ENNReal) * 288)) 12

theorem recursiveWarmBudget_cold_le_linear_pow
    {n cold L : Nat} (hn : 1 ≤ n) {retries : Nat → Nat}
    (hretries : ∀ j, retries j ≤ L)
    {initial : ENNReal} (hinitial : 1 ≤ initial) : ∀ i,
    recursiveWarmBudget initial (coldAcceptedFactor n retries)
        (coldConcreteFallbackFactor n cold) i ≤
      initial * coldLinearWarmBase L ^ i := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
      rw [recursiveWarmBudget_succ, pow_succ]
      have hA := coldAcceptedFactor_le_retryEnvelope hn hretries i
      have hF := coldConcreteFallbackFactor_le_six_pow n cold i
      have h6pow : (6 : ENNReal) ^ i ≤ coldLinearWarmBase L ^ i :=
        pow_le_pow_left' (six_le_coldLinearWarmBase L) i
      have hF' : coldConcreteFallbackFactor n cold i ≤
          12 * coldLinearWarmBase L ^ i := by
        calc
          _ ≤ 2 * (6 : ENNReal) ^ (i + 1) := hF
          _ = 12 * (6 : ENNReal) ^ i := by rw [pow_succ]; ring
          _ ≤ 12 * coldLinearWarmBase L ^ i := mul_le_mul_left' h6pow _
      calc
        coldAcceptedFactor n retries i *
              recursiveWarmBudget initial (coldAcceptedFactor n retries)
                (coldConcreteFallbackFactor n cold) i +
            coldConcreteFallbackFactor n cold i ≤
          max 1 ((L : ENNReal) * 288) *
              (initial * coldLinearWarmBase L ^ i) +
            12 * coldLinearWarmBase L ^ i := add_le_add
              (mul_le_mul hA ih bot_le bot_le) hF'
        _ ≤ (max 1 ((L : ENNReal) * 288) * initial + 12 * initial) *
              coldLinearWarmBase L ^ i := by
                rw [add_mul]
                apply add_le_add
                · rw [mul_assoc]
                · exact mul_le_mul_right'
                    (le_mul_of_one_le_right' hinitial) _
        _ = initial * (coldLinearWarmBase L ^ i * coldLinearWarmBase L) := by
          unfold coldLinearWarmBase
          ring

theorem log_recursiveWarmBudget_cold_le_linear
    {n cold L : Nat} (hn : 1 ≤ n) {retries : Nat → Nat}
    (hretries : ∀ j, retries j ≤ L)
    {initial : ENNReal} (hinitial : 1 ≤ initial) (hinitialTop : initial ≠ ⊤)
    (i : Nat) :
    Real.log (recursiveWarmBudget initial (coldAcceptedFactor n retries)
        (coldConcreteFallbackFactor n cold) i).toReal ≤
      Real.log initial.toReal + (i : Real) * Real.log (coldLinearWarmBase L).toReal := by
  have hbaseTop : coldLinearWarmBase L ≠ ⊤ := by
    unfold coldLinearWarmBase
    exact ENNReal.add_ne_top.2
      ⟨max_ne_top (by norm_num)
        (ENNReal.mul_ne_top (ENNReal.natCast_ne_top L) (by norm_num)), by norm_num⟩
  have htargetTop : initial * coldLinearWarmBase L ^ i ≠ ⊤ :=
    ENNReal.mul_ne_top hinitialTop (ENNReal.pow_ne_top hbaseTop)
  have hrecTop : recursiveWarmBudget initial (coldAcceptedFactor n retries)
      (coldConcreteFallbackFactor n cold) i ≠ ⊤ := by
    apply ne_top_of_le_ne_top _
      (recursiveWarmBudget_cold_le_linear_pow (cold := cold) hn hretries hinitial i)
    exact htargetTop
  have hrecPos : 0 < (recursiveWarmBudget initial (coldAcceptedFactor n retries)
      (coldConcreteFallbackFactor n cold) i).toReal := by
    apply ENNReal.toReal_pos
    · exact ne_of_gt ((by norm_num : (0 : ENNReal) < 1).trans_le
        (one_le_recursiveWarmBudget hinitial (fun j ↦ by
          unfold coldAcceptedFactor
          exact le_max_left _ _) i))
    · exact hrecTop
  have hreal := ENNReal.toReal_mono htargetTop
    (recursiveWarmBudget_cold_le_linear_pow (cold := cold) hn hretries hinitial i)
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow] at hreal
  have hlog := Real.log_le_log hrecPos hreal
  have hinitPos : 0 < initial.toReal :=
    ENNReal.toReal_pos (ne_of_gt ((by norm_num : (0 : ENNReal) < 1).trans_le hinitial))
      hinitialTop
  have hbasePos : 0 < (coldLinearWarmBase L).toReal := by
    apply ENNReal.toReal_pos
    · exact ne_of_gt ((by norm_num : (0 : ENNReal) < 6).trans_le
        (six_le_coldLinearWarmBase L))
    · exact hbaseTop
  rw [Real.log_mul hinitPos.ne' (pow_ne_zero i hbasePos.ne'), Real.log_pow] at hlog
  simpa [mul_comm] using hlog

theorem log_coldAccepted_add_fallback_le
    {n cold L : Nat} (hn : 1 ≤ n) {retries : Nat → Nat}
    (hretries : ∀ i, retries i ≤ L) {i : Nat} (hi : i < cold) :
    Real.log (coldAcceptedFactor n retries i +
        coldConcreteFallbackFactor n cold i).toReal ≤
      Real.log (max 1 ((L : ENNReal) * 288) + 2).toReal +
        (i + 1 : Nat) * Real.log 6 := by
  let B : ENNReal := max 1 ((L : ENNReal) * 288) + 2
  have hle : coldAcceptedFactor n retries i +
      coldConcreteFallbackFactor n cold i ≤ B * 6 ^ (i + 1) := by
    simpa only [B, coldConcreteFallbackFactor] using
      coldAccepted_add_fallback_le_productEnvelope hn hretries hi
  have hBtop : B ≠ ⊤ := by
    dsimp only [B]
    exact ENNReal.add_ne_top.2
      ⟨(max_ne_top (by norm_num) (ENNReal.mul_ne_top
        (ENNReal.natCast_ne_top L) (by norm_num))), by norm_num⟩
  have htargetTop : B * 6 ^ (i + 1) ≠ ⊤ :=
    ENNReal.mul_ne_top hBtop (ENNReal.pow_ne_top (by norm_num))
  have hreal := ENNReal.toReal_mono htargetTop hle
  have hsourcePos : 0 <
      (coldAcceptedFactor n retries i + coldConcreteFallbackFactor n cold i).toReal := by
    have hone : (1 : ENNReal) ≤ coldAcceptedFactor n retries i :=
      le_max_left _ _
    have hsourceTop : coldAcceptedFactor n retries i +
        coldConcreteFallbackFactor n cold i ≠ ⊤ := by
      apply ne_top_of_le_ne_top _ hle
      exact htargetTop
    exact ENNReal.toReal_pos
      (ne_of_gt ((by norm_num : (0 : ENNReal) < 1).trans_le
        (hone.trans (le_add_right le_rfl)))) hsourceTop
  have hlog := Real.log_le_log hsourcePos hreal
  have hBpos : 0 < B.toReal := by
    apply ENNReal.toReal_pos
    · dsimp only [B]
      exact ne_of_gt ((by norm_num : (0 : ENNReal) < 1).trans_le
        ((le_max_left 1 ((L : ENNReal) * 288)).trans (le_add_right le_rfl)))
    · exact hBtop
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    Real.log_mul hBpos.ne' (pow_ne_zero _ (by norm_num : (6 : Real) ≠ 0)),
    Real.log_pow] at hlog
  simpa only [B, Nat.cast_ofNat] using hlog

/-- Log envelope for the exact cold prefix of the concrete recursive warm budget. -/
theorem log_recursiveWarmBudget_coldPrefix_le
    {n cold L i : Nat} (hn : 1 ≤ n) (hi : i ≤ cold)
    {retries : Nat → Nat} (hretries : ∀ j, retries j ≤ L)
    {initial : ENNReal} (hinitial : 1 ≤ initial) (hinitialTop : initial ≠ ⊤) :
    Real.log (recursiveWarmBudget initial (coldAcceptedFactor n retries)
        (coldConcreteFallbackFactor n cold) i).toReal ≤
      Real.log initial.toReal + ∑ j ∈ Finset.range i,
        (Real.log (max 1 ((L : ENNReal) * 288) + 2).toReal +
          (j + 1 : Nat) * Real.log 6) := by
  have hAone : ∀ j, 1 ≤ coldAcceptedFactor n retries j := by
    intro j
    unfold coldAcceptedFactor
    exact le_max_left _ _
  have hAtop : ∀ j, coldAcceptedFactor n retries j ≠ ⊤ := by
    intro j
    unfold coldAcceptedFactor
    exact max_ne_top (by norm_num)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top
        (by norm_num) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num)))))
  have hFtop : ∀ j, coldConcreteFallbackFactor n cold j ≠ ⊤ := by
    intro j
    unfold coldConcreteFallbackFactor coldResetTruncatedWarmConst coldResetFullWarmConst
    split_ifs
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.pow_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num)))
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hrec := log_recursiveWarmBudget_toReal_le_sum
    hinitial hAone hinitialTop hAtop hFtop i
  have hsum :
      ∑ j ∈ Finset.range i,
          Real.log (coldAcceptedFactor n retries j +
            coldConcreteFallbackFactor n cold j).toReal ≤
        ∑ j ∈ Finset.range i,
          (Real.log (max 1 ((L : ENNReal) * 288) + 2).toReal +
            (j + 1 : Nat) * Real.log 6) := by
    apply Finset.sum_le_sum
    intro j hj
    exact log_coldAccepted_add_fallback_le hn hretries
      (lt_of_lt_of_le (Finset.mem_range.mp hj) hi)
  exact hrec.trans (by
    simpa only [add_comm] using add_le_add_left hsum (Real.log initial.toReal))

/-- Closed quadratic form of the preceding exact cold-prefix log sum. -/
theorem log_recursiveWarmBudget_coldPrefix_le_quadratic
    {n cold L i : Nat} (hn : 1 ≤ n) (hi : i ≤ cold)
    {retries : Nat → Nat} (hretries : ∀ j, retries j ≤ L)
    {initial : ENNReal} (hinitial : 1 ≤ initial) (hinitialTop : initial ≠ ⊤) :
    Real.log (recursiveWarmBudget initial (coldAcceptedFactor n retries)
        (coldConcreteFallbackFactor n cold) i).toReal ≤
      Real.log initial.toReal +
        (i : Real) * Real.log (max 1 ((L : ENNReal) * 288) + 2).toReal +
          (i : Real) ^ 2 * Real.log 6 := by
  have hraw := log_recursiveWarmBudget_coldPrefix_le
    hn hi hretries hinitial hinitialTop
  have hlog6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hsum :
      ∑ j ∈ Finset.range i,
          (Real.log (max 1 ((L : ENNReal) * 288) + 2).toReal +
            (j + 1 : Nat) * Real.log 6) ≤
        ∑ _j ∈ Finset.range i,
          (Real.log (max 1 ((L : ENNReal) * 288) + 2).toReal +
            (i : Real) * Real.log 6) := by
    apply Finset.sum_le_sum
    intro j hj
    gcongr
    exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hj)
  have hadd :
      Real.log initial.toReal +
          ∑ j ∈ Finset.range i,
            (Real.log (max 1 ((L : ENNReal) * 288) + 2).toReal +
              (j + 1 : Nat) * Real.log 6) ≤
        Real.log initial.toReal +
          ∑ _j ∈ Finset.range i,
            (Real.log (max 1 ((L : ENNReal) * 288) + 2).toReal +
              (i : Real) * Real.log 6) := by
    simpa only [add_comm] using
      add_le_add_left hsum (Real.log initial.toReal)
  refine hraw.trans (hadd.trans_eq ?_)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-! ## Exact recursive-warm deadline payload

The preceding quadratic estimate is now inserted directly into the score-aware
deadline.  This is the recurrence used by the concrete cold schedule; unlike the older
`hybridOperationalWarm` envelope above, it includes the independent unresolved-tail
fallback exactly. -/

noncomputable def coldRecursiveWarmDeadlineLogEnvelope
    (L i : Nat) (initial : ENNReal) (share : Real) : Real :=
  Real.log initial.toReal +
    (i : Real) * Real.log (coldLinearWarmBase L).toReal +
      Real.log 2 + 2 * Real.log 32 + 3 * Real.log (1 / share)

noncomputable def coldRecursiveWarmDeadlineEnvelope
    (n L i : Nat) (initial : ENNReal) (share : Real) : Nat :=
  ⌈4 * 640 ^ 2 * (72 * (n : Real) ^ 3) *
      coldRecursiveWarmDeadlineLogEnvelope L i initial share /
        Real.log 2 ^ 2 + 1⌉₊ + 1

theorem coldRecursiveWarm_deadlineLogPayload_scoreAware_le
    {n cold m k L i : Nat} {eps : Real} {slack boundSq : Nat → Real}
    {retries : Nat → Nat} {initial : ENNReal}
    (hn : 1 ≤ n) (hi : i ≤ cold)
    (hretries : ∀ j, retries j ≤ L)
    (hinitial : 1 ≤ initial) (hinitialTop : initial ≠ ⊤)
    (heps : 0 < eps) (hslack : ∀ j, 0 < slack j)
    (hbound : ∀ j, 0 < boundSq j) :
    let warm := recursiveWarmBudget initial (coldAcceptedFactor n retries)
      (coldConcreteFallbackFactor n cold) i
    let share := scoreAwareShare m k eps slack boundSq i
    Real.log (((2 * warm) / scoreAwareEta m k eps slack boundSq i).toReal) +
        2 * Real.log (1 / (scoreAwareZeta m k eps slack boundSq i).toReal) ≤
      coldRecursiveWarmDeadlineLogEnvelope L i initial share := by
  dsimp only
  let warm := recursiveWarmBudget initial (coldAcceptedFactor n retries)
    (coldConcreteFallbackFactor n cold) i
  let share := scoreAwareShare m k eps slack boundSq i
  have hshare : 0 < share := scoreAwareShare_pos heps hslack hbound i
  have hshare0 : 0 ≤ share := hshare.le
  have hshare32 : 0 ≤ share / 32 := by positivity
  have hlogWarm := log_recursiveWarmBudget_cold_le_linear
    (cold := cold) hn hretries hinitial hinitialTop i
  have hAone : ∀ j, 1 ≤ coldAcceptedFactor n retries j := by
    intro j
    unfold coldAcceptedFactor
    exact le_max_left _ _
  have hAtop : ∀ j, coldAcceptedFactor n retries j ≠ ⊤ := by
    intro j
    unfold coldAcceptedFactor
    exact max_ne_top (by norm_num)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ENNReal.mul_ne_top (by norm_num)
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num)))))
  have hFtop : ∀ j, coldConcreteFallbackFactor n cold j ≠ ⊤ := by
    intro j
    unfold coldConcreteFallbackFactor coldResetTruncatedWarmConst coldResetFullWarmConst
    split_ifs
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.pow_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num)))
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hwarmTop : warm ≠ ⊤ := by
    dsimp only [warm]
    exact recursiveWarmBudget_ne_top hinitialTop hAtop hFtop i
  have hwarmPos : 0 < warm.toReal := by
    apply ENNReal.toReal_pos
    · exact ne_of_gt ((by norm_num : (0 : ENNReal) < 1).trans_le
        (one_le_recursiveWarmBudget hinitial hAone i))
    · exact hwarmTop
  change Real.log (((2 * warm) / ENNReal.ofReal share).toReal) +
      2 * Real.log (1 / (ENNReal.ofReal (share / 32)).toReal) ≤ _
  rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal hshare0, ENNReal.toReal_ofReal hshare32]
  have htwo : (2 : Real) ≠ 0 := by norm_num
  have hthirtytwo : (32 : Real) ≠ 0 := by norm_num
  have hshareNe : share ≠ 0 := hshare.ne'
  rw [Real.log_div (mul_ne_zero htwo hwarmPos.ne') hshareNe,
    Real.log_mul htwo hwarmPos.ne']
  have honeShare : (1 / share : Real) ≠ 0 := one_div_ne_zero hshareNe
  rw [show 1 / (share / 32) = 32 * (1 / share) by field_simp,
    Real.log_mul hthirtytwo honeShare]
  have hlogInv : Real.log (1 / share) = -Real.log share := by
    rw [one_div, Real.log_inv]
  rw [hlogInv]
  unfold coldRecursiveWarmDeadlineLogEnvelope
  linarith

/-- Final generic cold accounting bridge: arbitrary operational steps are bounded
phasewise, while the reference multiplier is the constant retained-reference cap. -/
theorem coldOperationalReferenceRetrySum_le_phasewise
    {cold L n : Nat} {D : Nat → Nat} {M0 : ENNReal}
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (hretries : ∀ i, i < cold → retries i ≤ L)
    (hsteps : ∀ i j, i < cold → j < retries i → steps i j ≤ D i) :
    ∑ i ∈ Finset.range cold,
        ∑ j ∈ Finset.range (retries i),
          10 * ((steps i j : ENNReal) * coldOperationalWarmSchedule M0 n i) ≤
      ∑ i ∈ Finset.range cold,
        (L : ENNReal) * (10 * ((D i : ENNReal) *
          coldRetainedReferenceWarmCap n M0)) := by
  exact coldReferenceRetrySum_le_phasewise steps retries hretries hsteps
    (fun i _ ↦ coldOperationalWarmSchedule_le_cap n M0 i)

/-- Real per-phase mean chosen for the concrete retained cold reference. -/
noncomputable def coldOperationalReferencePhaseMeanReal
    (n : Nat) (M0 : ENNReal) (L D : Nat) : Real :=
  10 * (L : Real) * (D : Real) * (coldRetainedReferenceWarmCap n M0).toReal

theorem coldOperationalReferencePhaseMeanReal_nonneg
    (n : Nat) (M0 : ENNReal) (L D : Nat) :
    0 ≤ coldOperationalReferencePhaseMeanReal n M0 L D := by
  unfold coldOperationalReferencePhaseMeanReal
  positivity

theorem sum_coldOperationalReferencePhaseMeanReal_eq
    (cold n L : Nat) (M0 : ENNReal) (D : Nat → Nat) :
    ∑ i ∈ Finset.range cold,
        coldOperationalReferencePhaseMeanReal n M0 L (D i) =
      10 * (L : Real) * (coldRetainedReferenceWarmCap n M0).toReal *
        ∑ i ∈ Finset.range cold, (D i : Real) := by
  unfold coldOperationalReferencePhaseMeanReal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem sum_coldOperationalReferencePhaseMeanReal_le_uniform
    {cold n L Dmax : Nat} {M0 : ENNReal} {D : Nat → Nat}
    (hD : ∀ i, i < cold → D i ≤ Dmax) :
    ∑ i ∈ Finset.range cold,
        coldOperationalReferencePhaseMeanReal n M0 L (D i) ≤
      (cold : Real) *
        coldOperationalReferencePhaseMeanReal n M0 L Dmax := by
  calc
    ∑ i ∈ Finset.range cold,
        coldOperationalReferencePhaseMeanReal n M0 L (D i) ≤
      ∑ _i ∈ Finset.range cold,
        coldOperationalReferencePhaseMeanReal n M0 L Dmax := by
          apply Finset.sum_le_sum
          intro i hi
          unfold coldOperationalReferencePhaseMeanReal
          gcongr
          exact_mod_cast hD i (Finset.mem_range.mp hi)
    _ = (cold : Real) *
        coldOperationalReferencePhaseMeanReal n M0 L Dmax := by simp

/-- Per-phase `hcostShape` discharge used directly by the concrete certificate. -/
theorem coldOperationalReferenceRetryPhase_le_of_bounds
    {n i L D : Nat} {M0 : ENNReal} (hM0top : M0 ≠ ⊤)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (hretries : retries i ≤ L)
    (hsteps : ∀ j, j < retries i → steps i j ≤ D) :
    ∑ j ∈ Finset.range (retries i),
        10 * ((steps i j : ENNReal) * coldOperationalWarmSchedule M0 n i) ≤
      ENNReal.ofReal (coldOperationalReferencePhaseMeanReal n M0 L D) := by
  have hcapTop := coldRetainedReferenceWarmCap_ne_top hM0top n
  have hraw :
      ∑ j ∈ Finset.range (retries i),
          10 * ((steps i j : ENNReal) * coldOperationalWarmSchedule M0 n i) ≤
        (L : ENNReal) * (10 * ((D : ENNReal) *
          coldRetainedReferenceWarmCap n M0)) := by
    calc
      ∑ j ∈ Finset.range (retries i),
          10 * ((steps i j : ENNReal) * coldOperationalWarmSchedule M0 n i) ≤
        ∑ _j ∈ Finset.range (retries i),
          10 * ((D : ENNReal) * coldRetainedReferenceWarmCap n M0) := by
            apply Finset.sum_le_sum
            intro j hj
            gcongr
            · exact_mod_cast hsteps j (Finset.mem_range.mp hj)
            · exact coldOperationalWarmSchedule_le_cap n M0 i
      _ ≤ (L : ENNReal) * (10 * ((D : ENNReal) *
          coldRetainedReferenceWarmCap n M0)) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        gcongr
  calc
    _ ≤ (L : ENNReal) * (10 * ((D : ENNReal) *
        coldRetainedReferenceWarmCap n M0)) := hraw
    _ = ENNReal.ofReal (coldOperationalReferencePhaseMeanReal n M0 L D) := by
      unfold coldOperationalReferencePhaseMeanReal
      rw [ENNReal.ofReal_mul (by positivity : (0 : Real) ≤ 10 * L * D),
        ENNReal.ofReal_mul (by positivity : (0 : Real) ≤ 10 * L),
        ENNReal.ofReal_mul (by positivity : (0 : Real) ≤ 10),
        ENNReal.ofReal_toReal hcapTop]
      norm_num
      ac_rfl

/-! ## Radius-four cold geometry -/

/-- The honest capped-step coefficient applies verbatim to the radius-four cold step
(`q=4`). -/
theorem sigmaSq_mul_n_div_fixedRadiusFourDelta_sq_le
    {n : Nat} (hn : 1 ≤ n) {sigmaSq : Real} (hsigma : 0 < sigmaSq) :
    sigmaSq * (n : Real) / (fixedRadiusFourDelta n sigmaSq) ^ 2 ≤
      hotCappedStepCoefficient n 4 sigmaSq := by
  simpa only [fixedRadiusFourDelta, show max (8 : Real) (2 * 4) = 8 by norm_num]
    using sigmaSq_mul_n_div_adaptiveTerminalDeltaQ_sq_le
      (n := n) (q := (4 : Real)) hn hsigma

/-- On a cold coordinate with variance at most `n`, the full capped-step coefficient is
bounded by `68 n^4`. -/
theorem hotCappedStepCoefficient_four_le_sixtyEight_n_four
    {n : Nat} (hn : 1 ≤ n) {sigmaSq : Real}
    (hsigma0 : 0 ≤ sigmaSq) (hsigmaN : sigmaSq ≤ (n : Real)) :
    hotCappedStepCoefficient n 4 sigmaSq ≤
      68 * (n : Real) ^ 4 := by
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : Real) ≤ n := hnR.trans' (by norm_num)
  have hn2 : (n : Real) ^ 2 ≤ (n : Real) ^ 4 := by
    nlinarith [sq_nonneg ((n : Real) ^ 2 - 1)]
  unfold hotCappedStepCoefficient
  norm_num only [Nat.cast_ofNat, max_eq_left]
  have hsig : sigmaSq * (n : Real) ^ 3 ≤ (n : Real) ^ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsigmaN) (pow_nonneg hn0 3)]
  nlinarith

/-- Every active fixed-rate cold variance is at most `n`. -/
theorem fixedSigmaSq_le_n_of_lt_coldPhases
    {n : Nat} (hn : 2 ≤ n) {s0 : Real} (hs0 : 0 < s0) (hs01 : s0 ≤ 1)
    {i : Nat} (hi : i < Ttc.CVHybridSchedule.coldPhases n s0) :
    fixedSigmaSq n s0 i ≤ (n : Real) := by
  have hmono := Ttc.CVColdCrossPhaseWarm.fixedSigmaSq_le_succ
    (by omega : 1 ≤ n) hs0 i
  exact hmono.trans
    (fixedSigmaSq_succ_le_n_of_lt_coldPhases hn hs0 hs01 hi)

/-- The cold block actually stops near variance one.  Keeping this sharper fact avoids
an artificial extra dimension factor in the radius-four mixing coefficient. -/
theorem fixedSigmaSq_le_two_of_lt_coldPhases
    {n : Nat} (hn : 1 ≤ n) {s0 : Real} (hs0 : 0 < s0) (hs01 : s0 ≤ 1)
    {i : Nat} (hi : i < Ttc.CVHybridSchedule.coldPhases n s0) :
    fixedSigmaSq n s0 i ≤ 2 := by
  have hindex : i ≤ Ttc.CVHybridSchedule.coldPhases n s0 := Nat.le_of_lt hi
  have hsched : fixedSigmaSq n s0 i ≤ Ttc.CVHybridSchedule.coldEnd n s0 := by
    unfold fixedSigmaSq Ttc.CVHybridSchedule.coldEnd
    exact (Arlib.GaussianCooling.geomSchedule_strictMono hs0
      (by positivity : 0 < 1 / (n : Real))).monotone hindex
  have hend := Ttc.CVHybridSchedule.coldEnd_lt_one_add_inv hn hs0 hs01
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  have hinv : 1 / (n : Real) ≤ 1 := by
    rw [div_le_one (by positivity : (0 : Real) < n)]
    exact hnR
  linarith

/-- Sharp cold-block capped-step coefficient.  Since cold variances never exceed two,
the radius-four walk costs `O(n^3)`, not the coarser `O(n^4)` bound. -/
theorem fixedRadiusFour_stepCoefficient_le_seventyTwo_n_three
    {n : Nat} (hn : 2 ≤ n) {s0 : Real} (hs0 : 0 < s0) (hs01 : s0 ≤ 1)
    {i : Nat} (hi : i < Ttc.CVHybridSchedule.coldPhases n s0) :
    fixedSigmaSq n s0 i * (n : Real) /
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i)) ^ 2 ≤
      72 * (n : Real) ^ 3 := by
  have hs : 0 < fixedSigmaSq n s0 i := by
    unfold fixedSigmaSq
    exact Arlib.GaussianCooling.geomSchedule_pos hs0 (by positivity) i
  have hcoef := sigmaSq_mul_n_div_fixedRadiusFourDelta_sq_le
    (by omega : 1 ≤ n) hs
  have hsTwo := fixedSigmaSq_le_two_of_lt_coldPhases
    (by omega : 1 ≤ n) hs0 hs01 hi
  have hnR : (1 : Real) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : Real) ≤ n := by positivity
  have hn23 : (n : Real) ^ 2 ≤ (n : Real) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (n : Real)) (sub_nonneg.mpr hnR)]
  apply hcoef.trans
  unfold hotCappedStepCoefficient
  norm_num only [Nat.cast_ofNat, max_eq_left]
  have hsig : fixedSigmaSq n s0 i * (n : Real) ^ 3 ≤
      2 * (n : Real) ^ 3 := by gcongr
  nlinarith

/-! ## Stationary-reference deadlines

With the product-state phase reset, the law used to establish each phase error is the
phase stationary law itself.  Its warmness is exactly one. -/

noncomputable def coldStationaryDeadlineLogEnvelope (share : Real) : Real :=
  Real.log 2 + 2 * Real.log 32 + 3 * Real.log (1 / share)

noncomputable def coldStationaryDeadlineEnvelope
    (n : Nat) (share : Real) : Nat :=
  ⌈4 * 640 ^ 2 * (72 * (n : Real) ^ 3) *
      coldStationaryDeadlineLogEnvelope share / Real.log 2 ^ 2 + 1⌉₊ + 1

theorem stationary_scoreAware_deadlineLogPayload_eq
    {m k i : Nat} {eps : Real} {slack boundSq : Nat → Real}
    (heps : 0 < eps) (hslack : ∀ j, 0 < slack j)
    (hbound : ∀ j, 0 < boundSq j) :
    Real.log (((2 : ENNReal) /
          scoreAwareEta m k eps slack boundSq i).toReal) +
        2 * Real.log (1 /
          (scoreAwareZeta m k eps slack boundSq i).toReal) =
      coldStationaryDeadlineLogEnvelope
        (scoreAwareShare m k eps slack boundSq i) := by
  let share := scoreAwareShare m k eps slack boundSq i
  have hshare : 0 < share := scoreAwareShare_pos heps hslack hbound i
  have hshare0 : 0 ≤ share := hshare.le
  have hshare32 : 0 ≤ share / 32 := by positivity
  change Real.log (((2 : ENNReal) / ENNReal.ofReal share).toReal) +
      2 * Real.log (1 / (ENNReal.ofReal (share / 32)).toReal) = _
  rw [ENNReal.toReal_div, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal hshare0, ENNReal.toReal_ofReal hshare32]
  have htwo : (2 : Real) ≠ 0 := by norm_num
  have hthirtytwo : (32 : Real) ≠ 0 := by norm_num
  have hshareNe : share ≠ 0 := hshare.ne'
  rw [Real.log_div htwo hshareNe]
  have honeShare : (1 / share : Real) ≠ 0 := one_div_ne_zero hshareNe
  rw [show 1 / (share / 32) = 32 * (1 / share) by field_simp,
    Real.log_mul hthirtytwo honeShare]
  unfold coldStationaryDeadlineLogEnvelope
  simp only [one_div, Real.log_inv]
  ring

theorem coldStationaryDeadlineLogEnvelope_nonneg
    {m k i : Nat} {eps : Real} {slack boundSq : Nat → Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hslack : ∀ j, 0 < slack j) (hbound : ∀ j, 0 < boundSq j) :
    0 ≤ coldStationaryDeadlineLogEnvelope
      (scoreAwareShare m k eps slack boundSq i) := by
  have hshare := scoreAwareShare_pos (m := m) (k := k)
    heps hslack hbound i
  have hshareOne : scoreAwareShare m k eps slack boundSq i ≤ 1 :=
    (scoreAwareShare_lt_one (m := m) (k := k)
      (slack := slack) (boundSq := boundSq) heps heps1 i).le
  have hinv : 1 ≤ 1 / scoreAwareShare m k eps slack boundSq i := by
    rw [le_div_iff₀ hshare]
    simpa using hshareOne
  unfold coldStationaryDeadlineLogEnvelope
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog32 : 0 ≤ Real.log 32 := Real.log_nonneg (by norm_num)
  have hloginv : 0 ≤ Real.log
      (1 / scoreAwareShare m k eps slack boundSq i) := Real.log_nonneg hinv
  positivity

/-- Honest radius-four deadline for a stationary cold reference.  The geometric
coefficient is `72 n^3`; operational warmth is absent. -/
theorem adjustableSpeedyDeadline_fixedRadiusFour_stationary_scoreAware_le
    {n m k i : Nat} {s0 eps : Real} {slack boundSq : Nat → Real}
    (hn : 2 ≤ n) (hs0 : 0 < s0) (hs01 : s0 ≤ 1)
    (hi : i < Ttc.CVHybridSchedule.coldPhases n s0)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hslack : ∀ j, 0 < slack j) (hbound : ∀ j, 0 < boundSq j) :
    adjustableSpeedyDeadline n
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
        (fixedSigmaSq n s0 i)
        ((2 : ENNReal) / scoreAwareEta m k eps slack boundSq i)
        (scoreAwareZeta m k eps slack boundSq i) ≤
      coldStationaryDeadlineEnvelope n
        (scoreAwareShare m k eps slack boundSq i) := by
  apply adjustableSpeedyDeadline_le_ceil_of_expression_le
  let s := fixedSigmaSq n s0 i
  let d := fixedRadiusFourDelta n s
  let payload := Real.log (((2 : ENNReal) /
      scoreAwareEta m k eps slack boundSq i).toReal) +
        2 * Real.log (1 / (scoreAwareZeta m k eps slack boundSq i).toReal)
  let envelope := coldStationaryDeadlineLogEnvelope
    (scoreAwareShare m k eps slack boundSq i)
  have hs : 0 < s := by
    dsimp only [s]
    unfold fixedSigmaSq
    exact Arlib.GaussianCooling.geomSchedule_pos hs0 (by positivity) i
  have hd : 0 < d := by
    dsimp only [d]
    exact fixedRadiusFourDelta_pos (by omega) hs
  have hpayload : payload = envelope := by
    dsimp only [payload, envelope]
    exact stationary_scoreAware_deadlineLogPayload_eq heps hslack hbound
  have henv0 : 0 ≤ envelope := by
    dsimp only [envelope]
    exact coldStationaryDeadlineLogEnvelope_nonneg heps heps1 hslack hbound
  have hgeom : s * (n : Real) / d ^ 2 ≤ 72 * (n : Real) ^ 3 := by
    simpa only [s, d] using
      fixedRadiusFour_stepCoefficient_le_seventyTwo_n_three hn hs0 hs01 hi
  have hstep : (s * (n : Real) / d ^ 2) * payload ≤
      (72 * (n : Real) ^ 3) * envelope := by
    rw [hpayload]
    exact mul_le_mul_of_nonneg_right hgeom henv0
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hscaled := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hstep (by positivity : (0 : Real) ≤ 4 * 640 ^ 2))
    (sq_nonneg (Real.log 2))
  unfold adjustableSpeedyDeadlineExpression
  dsimp only [s, d, payload, envelope] at hscaled
  have hleft :
      4 * 640 ^ 2 * fixedSigmaSq n s0 i * (n : Real) *
          (Real.log (((2 : ENNReal) /
              scoreAwareEta m k eps slack boundSq i).toReal) +
            2 * Real.log (1 /
              (scoreAwareZeta m k eps slack boundSq i).toReal)) /
            (fixedRadiusFourDelta n (fixedSigmaSq n s0 i) * Real.log 2) ^ 2 =
        (4 * 640 ^ 2 *
          ((fixedSigmaSq n s0 i * (n : Real) /
            fixedRadiusFourDelta n (fixedSigmaSq n s0 i) ^ 2) *
            (Real.log (((2 : ENNReal) /
                scoreAwareEta m k eps slack boundSq i).toReal) +
              2 * Real.log (1 /
                (scoreAwareZeta m k eps slack boundSq i).toReal)))) /
          Real.log 2 ^ 2 := by
    field_simp [hd.ne', hlog.ne']
  rw [hleft]
  simpa only [add_comm, mul_assoc] using add_le_add_right hscaled 1

theorem coldRecursiveWarmDeadlineLogEnvelope_nonneg
    {m k L i : Nat} {eps : Real} {slack boundSq : Nat → Real}
    {initial : ENNReal}
    (hinitial : 1 ≤ initial) (hinitialTop : initial ≠ ⊤)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hslack : ∀ j, 0 < slack j) (hbound : ∀ j, 0 < boundSq j) :
    0 ≤ coldRecursiveWarmDeadlineLogEnvelope L i initial
      (scoreAwareShare m k eps slack boundSq i) := by
  have hinitReal : 1 ≤ initial.toReal := by
    simpa using ENNReal.toReal_mono hinitialTop hinitial
  have hBtop : coldLinearWarmBase L ≠ ⊤ := by
    unfold coldLinearWarmBase
    exact ENNReal.add_ne_top.2
      ⟨max_ne_top (by norm_num)
        (ENNReal.mul_ne_top (ENNReal.natCast_ne_top L) (by norm_num)), by norm_num⟩
  have hBReal : 1 ≤ (coldLinearWarmBase L).toReal := by
    have hB : (1 : ENNReal) ≤ coldLinearWarmBase L :=
      (by norm_num : (1 : ENNReal) ≤ 6).trans (six_le_coldLinearWarmBase L)
    simpa using ENNReal.toReal_mono hBtop hB
  have hstationary := coldStationaryDeadlineLogEnvelope_nonneg
    (m := m) (k := k) (i := i) heps heps1 hslack hbound
  unfold coldRecursiveWarmDeadlineLogEnvelope
    coldStationaryDeadlineLogEnvelope at *
  have hi0 : (0 : Real) ≤ i := by positivity
  have hlogInit := Real.log_nonneg hinitReal
  have hlogB := Real.log_nonneg hBReal
  have hphase : 0 ≤ (i : Real) * Real.log (coldLinearWarmBase L).toReal :=
    mul_nonneg hi0 hlogB
  linarith

/-- Literal concrete cold deadline under the exact recursive actual-path warm budget.
The retained reference still pays warmness one; this theorem controls only the number of
steps selected for the common operational kernel. -/
theorem adjustableSpeedyDeadline_fixedRadiusFour_recursiveWarm_scoreAware_le
    {n cold m k L i : Nat} {s0 eps : Real} {slack boundSq : Nat → Real}
    {retries : Nat → Nat} {initial : ENNReal}
    (hn : 2 ≤ n) (hs0 : 0 < s0) (hs01 : s0 ≤ 1)
    (hi : i < cold) (hcold : cold ≤ Ttc.CVHybridSchedule.coldPhases n s0)
    (hretries : ∀ j, retries j ≤ L)
    (hinitial : 1 ≤ initial) (hinitialTop : initial ≠ ⊤)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hslack : ∀ j, 0 < slack j) (hbound : ∀ j, 0 < boundSq j) :
    adjustableSpeedyDeadline n
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
        (fixedSigmaSq n s0 i)
        ((2 * recursiveWarmBudget initial (coldAcceptedFactor n retries)
          (coldConcreteFallbackFactor n cold) i) /
            scoreAwareEta m k eps slack boundSq i)
        (scoreAwareZeta m k eps slack boundSq i) ≤
      coldRecursiveWarmDeadlineEnvelope n L i initial
        (scoreAwareShare m k eps slack boundSq i) := by
  apply adjustableSpeedyDeadline_le_ceil_of_expression_le
  let s := fixedSigmaSq n s0 i
  let d := fixedRadiusFourDelta n s
  let payload := Real.log (((2 * recursiveWarmBudget initial
      (coldAcceptedFactor n retries) (coldConcreteFallbackFactor n cold) i) /
        scoreAwareEta m k eps slack boundSq i).toReal) +
      2 * Real.log (1 / (scoreAwareZeta m k eps slack boundSq i).toReal)
  let envelope := coldRecursiveWarmDeadlineLogEnvelope L i initial
    (scoreAwareShare m k eps slack boundSq i)
  have hs : 0 < s := by
    dsimp only [s]
    unfold fixedSigmaSq
    exact Arlib.GaussianCooling.geomSchedule_pos hs0 (by positivity) i
  have hd : 0 < d := by
    dsimp only [d]
    exact fixedRadiusFourDelta_pos (by omega) hs
  have hpayload : payload ≤ envelope := by
    dsimp only [payload, envelope]
    exact coldRecursiveWarm_deadlineLogPayload_scoreAware_le
      (by omega : 1 ≤ n) (Nat.le_of_lt hi) hretries
        hinitial hinitialTop heps hslack hbound
  have henv0 : 0 ≤ envelope := by
    dsimp only [envelope]
    exact coldRecursiveWarmDeadlineLogEnvelope_nonneg
      hinitial hinitialTop heps heps1 hslack hbound
  have hgeom : s * (n : Real) / d ^ 2 ≤ 72 * (n : Real) ^ 3 := by
    simpa only [s, d] using
      fixedRadiusFour_stepCoefficient_le_seventyTwo_n_three hn hs0 hs01
        (lt_of_lt_of_le hi hcold)
  have hstep : (s * (n : Real) / d ^ 2) * payload ≤
      (72 * (n : Real) ^ 3) * envelope := by
    calc
      _ ≤ (s * (n : Real) / d ^ 2) * envelope := by
        exact mul_le_mul_of_nonneg_left hpayload (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hgeom henv0
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hscaled := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hstep (by positivity : (0 : Real) ≤ 4 * 640 ^ 2))
    (sq_nonneg (Real.log 2))
  unfold adjustableSpeedyDeadlineExpression
  dsimp only [s, d, payload, envelope] at hscaled
  have hleft :
      4 * 640 ^ 2 * fixedSigmaSq n s0 i * (n : Real) *
          (Real.log (((2 * recursiveWarmBudget initial
              (coldAcceptedFactor n retries)
              (coldConcreteFallbackFactor n cold) i) /
                scoreAwareEta m k eps slack boundSq i).toReal) +
            2 * Real.log (1 /
              (scoreAwareZeta m k eps slack boundSq i).toReal)) /
            (fixedRadiusFourDelta n (fixedSigmaSq n s0 i) * Real.log 2) ^ 2 =
        (4 * 640 ^ 2 *
          ((fixedSigmaSq n s0 i * (n : Real) /
            fixedRadiusFourDelta n (fixedSigmaSq n s0 i) ^ 2) *
            (Real.log (((2 * recursiveWarmBudget initial
                (coldAcceptedFactor n retries)
                (coldConcreteFallbackFactor n cold) i) /
                  scoreAwareEta m k eps slack boundSq i).toReal) +
              2 * Real.log (1 /
                (scoreAwareZeta m k eps slack boundSq i).toReal)))) /
          Real.log 2 ^ 2 := by
    field_simp [hd.ne', hlog.ne']
  rw [hleft]
  simpa only [add_comm, mul_assoc] using add_le_add_right hscaled 1

theorem sum_retries_mul_adjustableSpeedyDeadline_cold_recursiveWarm_le
    {n cold m k L : Nat} {s0 eps : Real} {slack boundSq : Nat → Real}
    {retries : Nat → Nat} {initial : ENNReal}
    (hn : 2 ≤ n) (hs0 : 0 < s0) (hs01 : s0 ≤ 1)
    (hcold : cold ≤ Ttc.CVHybridSchedule.coldPhases n s0)
    (hretries : ∀ j, retries j ≤ L)
    (hinitial : 1 ≤ initial) (hinitialTop : initial ≠ ⊤)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hslack : ∀ j, 0 < slack j) (hbound : ∀ j, 0 < boundSq j) :
    ∑ i ∈ Finset.range cold,
        retries i * adjustableSpeedyDeadline n
          (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
          (fixedSigmaSq n s0 i)
          ((2 * recursiveWarmBudget initial (coldAcceptedFactor n retries)
            (coldConcreteFallbackFactor n cold) i) /
              scoreAwareEta m k eps slack boundSq i)
          (scoreAwareZeta m k eps slack boundSq i) ≤
      ∑ i ∈ Finset.range cold,
        retries i * coldRecursiveWarmDeadlineEnvelope n L i initial
          (scoreAwareShare m k eps slack boundSq i) := by
  apply Finset.sum_le_sum
  intro i hi
  apply Nat.mul_le_mul_left
  exact adjustableSpeedyDeadline_fixedRadiusFour_recursiveWarm_scoreAware_le
    hn hs0 hs01 (Finset.mem_range.mp hi) hcold hretries
      hinitial hinitialTop heps heps1 hslack hbound

/-- Phasewise stationary cold deadlines sum without any operational-warm multiplier. -/
theorem sum_retries_mul_adjustableSpeedyDeadline_cold_stationary_le
    {n cold m k : Nat} {s0 eps : Real} {slack boundSq : Nat → Real}
    (retries : Nat → Nat)
    (hn : 2 ≤ n) (hs0 : 0 < s0) (hs01 : s0 ≤ 1)
    (hcold : cold ≤ Ttc.CVHybridSchedule.coldPhases n s0)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hslack : ∀ j, 0 < slack j) (hbound : ∀ j, 0 < boundSq j) :
    ∑ i ∈ Finset.range cold,
        retries i * adjustableSpeedyDeadline n
          (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
          (fixedSigmaSq n s0 i)
          ((2 : ENNReal) / scoreAwareEta m k eps slack boundSq i)
          (scoreAwareZeta m k eps slack boundSq i) ≤
      ∑ i ∈ Finset.range cold,
        retries i * coldStationaryDeadlineEnvelope n
          (scoreAwareShare m k eps slack boundSq i) := by
  apply Finset.sum_le_sum
  intro i hi
  apply Nat.mul_le_mul_left
  exact adjustableSpeedyDeadline_fixedRadiusFour_stationary_scoreAware_le
    hn hs0 hs01 (lt_of_lt_of_le (Finset.mem_range.mp hi) hcold)
      heps heps1 hslack hbound

/-- Uniform finite form of the stationary cold accounting.  This theorem identifies
the only remaining scalar input: a common retry cap and a common deadline cap. -/
theorem sum_retries_mul_adjustableSpeedyDeadline_cold_stationary_le_uniform
    {n cold m k L D : Nat} {s0 eps : Real} {slack boundSq : Nat → Real}
    (hn : 2 ≤ n) (hs0 : 0 < s0) (hs01 : s0 ≤ 1)
    (hcold : cold ≤ Ttc.CVHybridSchedule.coldPhases n s0)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hslack : ∀ j, 0 < slack j) (hbound : ∀ j, 0 < boundSq j)
    (hretries : ∀ i, i < cold →
      scoreAwareRetries m k eps slack boundSq i ≤ L)
    (hdeadline : ∀ i, i < cold →
      coldStationaryDeadlineEnvelope n
        (scoreAwareShare m k eps slack boundSq i) ≤ D) :
    ∑ i ∈ Finset.range cold,
        scoreAwareRetries m k eps slack boundSq i *
          adjustableSpeedyDeadline n
            (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
            (fixedSigmaSq n s0 i)
            ((2 : ENNReal) / scoreAwareEta m k eps slack boundSq i)
            (scoreAwareZeta m k eps slack boundSq i) ≤
      cold * (L * D) := by
  calc
    _ ≤ ∑ i ∈ Finset.range cold,
        scoreAwareRetries m k eps slack boundSq i *
          coldStationaryDeadlineEnvelope n
            (scoreAwareShare m k eps slack boundSq i) :=
      sum_retries_mul_adjustableSpeedyDeadline_cold_stationary_le
        (scoreAwareRetries m k eps slack boundSq)
        hn hs0 hs01 hcold heps heps1 hslack hbound
    _ ≤ ∑ _i ∈ Finset.range cold, L * D := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.mul_le_mul (hretries i (Finset.mem_range.mp hi))
        (hdeadline i (Finset.mem_range.mp hi))
    _ = cold * (L * D) := by simp

/-- Exact stationary-reference real phase mean after applying uniform retry/deadline
bounds.  There is no cross-phase or actual-path warm factor. -/
noncomputable def coldStationaryReferencePhaseMeanReal (L D : Nat) : Real :=
  10 * (L : Real) * (D : Real)

theorem sum_coldStationaryReferencePhaseMeanReal
    (cold L D : Nat) :
    ∑ _i ∈ Finset.range cold, coldStationaryReferencePhaseMeanReal L D =
      10 * (cold : Real) * (L : Real) * (D : Real) := by
  simp only [coldStationaryReferencePhaseMeanReal, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  ring

/-- Uniform polynomial coefficient for every active cold phase. -/
theorem fixedRadiusFour_stepCoefficient_le_sixtyEight_n_four
    {n : Nat} (hn : 2 ≤ n) {s0 : Real} (hs0 : 0 < s0) (hs01 : s0 ≤ 1)
    {i : Nat} (hi : i < Ttc.CVHybridSchedule.coldPhases n s0) :
    fixedSigmaSq n s0 i * (n : Real) /
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i)) ^ 2 ≤
      68 * (n : Real) ^ 4 := by
  have hs : 0 < fixedSigmaSq n s0 i := by
    unfold fixedSigmaSq
    exact Arlib.GaussianCooling.geomSchedule_pos hs0 (by positivity) i
  exact (sigmaSq_mul_n_div_fixedRadiusFourDelta_sq_le (by omega) hs).trans
    (hotCappedStepCoefficient_four_le_sixtyEight_n_four (by omega) hs.le
      (fixedSigmaSq_le_n_of_lt_coldPhases hn hs0 hs01 hi))

/-- Phase-uniform polynomial cold deadline; all phase dependence is now logarithmic. -/
noncomputable def coldPolynomialDeadlineEnvelope
    (n L i : Nat) (M0 eta zeta : ENNReal) : Nat :=
  ⌈4 * 640 ^ 2 * (68 * (n : Real) ^ 4) *
      coldActualWarmDeadlineLogEnvelope n L i M0 eta zeta /
        Real.log 2 ^ 2 + 1⌉₊ + 1

theorem adjustableSpeedyDeadline_fixedRadiusFour_actualWarm_le_polynomial
    {n L i : Nat} {N s0 : Real} {retries : Nat → Nat}
    {M0 eta zeta : ENNReal}
    (hn : 2 ≤ n) (hs0 : 0 < s0) (hs01 : s0 ≤ 1)
    (hi : i < Ttc.CVHybridSchedule.coldPhases n s0)
    (hM0 : 1 ≤ M0) (hM0top : M0 ≠ ⊤)
    (hretries : ∀ j, retries j ≤ L)
    (hrate0 : ∀ j, 0 ≤ Ttc.CVHybridSchedule.phaseRate n N s0 j)
    (hrateHalf : ∀ j, Ttc.CVHybridSchedule.phaseRate n N s0 j ≤ 1 / 2)
    (heta0 : eta ≠ 0) (hetatop : eta ≠ ⊤)
    (hzeta0 : zeta ≠ 0) (hzetatop : zeta ≠ ⊤)
    (henv0 : 0 ≤ coldActualWarmDeadlineLogEnvelope n L i M0 eta zeta) :
    adjustableSpeedyDeadline n
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
        (fixedSigmaSq n s0 i)
        ((2 * hybridOperationalWarm n N s0 retries M0 i) / eta) zeta ≤
      coldPolynomialDeadlineEnvelope n L i M0 eta zeta := by
  apply adjustableSpeedyDeadline_le_ceil_of_expression_le
  have hpayload := coldActualWarm_deadlineLogPayload_le
    (i := i) hM0 hM0top hretries hrate0 hrateHalf
      heta0 hetatop hzeta0 hzetatop
  let s := fixedSigmaSq n s0 i
  let d := fixedRadiusFourDelta n s
  let payload := Real.log
      (((2 * hybridOperationalWarm n N s0 retries M0 i) / eta).toReal) +
        2 * Real.log (1 / zeta.toReal)
  let envelope := coldActualWarmDeadlineLogEnvelope n L i M0 eta zeta
  have hs : 0 < s := by
    dsimp only [s]
    unfold fixedSigmaSq
    exact Arlib.GaussianCooling.geomSchedule_pos hs0 (by positivity) i
  have hd : 0 < d := by
    dsimp only [d]
    exact fixedRadiusFourDelta_pos (by omega) hs
  have hgeom : s * (n : Real) / d ^ 2 ≤ 68 * (n : Real) ^ 4 := by
    simpa only [s, d] using
      fixedRadiusFour_stepCoefficient_le_sixtyEight_n_four hn hs0 hs01 hi
  have hstep : (s * (n : Real) / d ^ 2) * payload ≤
      (68 * (n : Real) ^ 4) * envelope := by
    calc
      (s * (n : Real) / d ^ 2) * payload ≤
          (s * (n : Real) / d ^ 2) * envelope := by
            exact mul_le_mul_of_nonneg_left
              (by simpa only [payload, envelope] using hpayload) (by positivity)
      _ ≤ (68 * (n : Real) ^ 4) * envelope := by
        exact mul_le_mul_of_nonneg_right hgeom (by simpa only [envelope] using henv0)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hscaled := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hstep (by positivity : (0 : Real) ≤ 4 * 640 ^ 2))
    (sq_nonneg (Real.log 2))
  unfold adjustableSpeedyDeadlineExpression
  dsimp only [s, d, payload, envelope] at hscaled
  have hleft :
      4 * 640 ^ 2 * fixedSigmaSq n s0 i * (n : Real) *
          (Real.log (((2 * hybridOperationalWarm n N s0 retries M0 i) / eta).toReal) +
            2 * Real.log (1 / zeta.toReal)) /
            (fixedRadiusFourDelta n (fixedSigmaSq n s0 i) * Real.log 2) ^ 2 =
        (4 * 640 ^ 2 *
          ((fixedSigmaSq n s0 i * (n : Real) /
            fixedRadiusFourDelta n (fixedSigmaSq n s0 i) ^ 2) *
            (Real.log (((2 * hybridOperationalWarm n N s0 retries M0 i) / eta).toReal) +
              2 * Real.log (1 / zeta.toReal)))) / Real.log 2 ^ 2 := by
    field_simp [hd.ne', hlog.ne']
  rw [hleft]
  simpa only [add_comm, mul_assoc] using add_le_add_right hscaled 1

/-- Convenience form discharging nonnegativity of the deadline envelope from the usual
mixing-tolerance bounds. -/
theorem adjustableSpeedyDeadline_fixedRadiusFour_actualWarm_le_polynomial_of_le_one
    {n L i : Nat} {N s0 : Real} {retries : Nat → Nat}
    {M0 eta zeta : ENNReal}
    (hn : 2 ≤ n) (hs0 : 0 < s0) (hs01 : s0 ≤ 1)
    (hi : i < Ttc.CVHybridSchedule.coldPhases n s0)
    (hM0 : 1 ≤ M0) (hM0top : M0 ≠ ⊤)
    (hretries : ∀ j, retries j ≤ L)
    (hrate0 : ∀ j, 0 ≤ Ttc.CVHybridSchedule.phaseRate n N s0 j)
    (hrateHalf : ∀ j, Ttc.CVHybridSchedule.phaseRate n N s0 j ≤ 1 / 2)
    (heta0 : eta ≠ 0) (hetatop : eta ≠ ⊤) (heta1 : eta ≤ 1)
    (hzeta0 : zeta ≠ 0) (hzetatop : zeta ≠ ⊤) (hzeta1 : zeta ≤ 1) :
    adjustableSpeedyDeadline n
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
        (fixedSigmaSq n s0 i)
        ((2 * hybridOperationalWarm n N s0 retries M0 i) / eta) zeta ≤
      coldPolynomialDeadlineEnvelope n L i M0 eta zeta := by
  exact adjustableSpeedyDeadline_fixedRadiusFour_actualWarm_le_polynomial
    hn hs0 hs01 hi hM0 hM0top hretries hrate0 hrateHalf
      heta0 hetatop hzeta0 hzetatop
      (coldActualWarmDeadlineLogEnvelope_nonneg hM0 hM0top
        heta0 hetatop heta1 hzeta0 hzetatop hzeta1)

#print axioms coldActualWarm_deadlineLogPayload_le
#print axioms adjustableSpeedyDeadline_coldActualWarm_le
#print axioms coldReferenceRetrySum_le_of_bounds
#print axioms coldOperationalReferenceRetrySum_le_phasewise
#print axioms fixedRadiusFour_stepCoefficient_le_sixtyEight_n_four
#print axioms adjustableSpeedyDeadline_fixedRadiusFour_actualWarm_le_polynomial
#print axioms log_recursiveWarmBudget_coldPrefix_le_quadratic
#print axioms fixedRadiusFour_stepCoefficient_le_seventyTwo_n_three
#print axioms adjustableSpeedyDeadline_fixedRadiusFour_stationary_scoreAware_le
#print axioms adjustableSpeedyDeadline_fixedRadiusFour_recursiveWarm_scoreAware_le
#print axioms sum_retries_mul_adjustableSpeedyDeadline_cold_recursiveWarm_le

end Ttc.CVColdActualWarmReferenceCostArithmetic
