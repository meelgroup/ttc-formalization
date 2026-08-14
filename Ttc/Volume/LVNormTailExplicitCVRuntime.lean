/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.LVNormTailExplicitUniform

/-! # Explicit logarithmic truncation and runtime geometry for `CVAdmissible` bodies -/

namespace Ttc.CVAdaptive

open MeasureTheory Metric Set
open Arlib Ttc.CV
open scoped ENNReal

variable {n : ℕ}

theorem tvLe_uniformOn_cvAdmissible_explicitDyadicClosure
    (hn : 2 ≤ n) {K : Set (Space n)} {R2 eta : ℝ}
    (hK : Ttc.CVAdmissible K R2) (heta0 : 0 < eta) (heta1 : eta < 1) :
    TVLe
      (Arlib.uniformOn volume
        (closure K ∩ closedBall 0
          (explicitDyadicMomentRadius (Ttc.cvSecondMoment K) eta)))
      (Arlib.uniformOn volume (closure K)) (ENNReal.ofReal eta) := by
  rcases hK with ⟨hconv, hball, hK0, hKtop, hm⟩
  have hvol : volume (closure K) = volume K :=
    Arlib.addHaar_closure_of_convex volume hconv
  have hsubK : K ⊆ closedBall (0 : Space n) (cvRadius K) :=
    subset_closedBall_cvRadius hconv hball hKtop
  have hbounded : Bornology.IsBounded (closure K) :=
    Metric.isBounded_closedBall.subset (closure_minimal hsubK isClosed_closedBall)
  exact tvLe_uniformOn_explicitDyadicMomentRadius hn hconv.closure isClosed_closure hbounded
    isClosed_closure.measurableSet (hvol.symm ▸ hK0)
    (cvSecondMoment_pos (by omega) ⟨hconv, hball, hK0, hKtop, hm⟩)
    heta0 heta1
    (centeredMoment_closure_cvSecondMoment ⟨hconv, hball, hK0, hKtop, hm⟩)

/-- The explicit multiplicative radius factor, still expressed using the integer ceiling. -/
noncomputable def explicitDyadicRadiusFactor (eta : ℝ) : ℝ :=
  1 + Real.sqrt 2 + 4 * Real.sqrt 3 * explicitDyadicTailIndex eta

/-- A literal logarithmic upper envelope for `explicitDyadicRadiusFactor`. -/
noncomputable def explicitDyadicLogFactor (eta : ℝ) : ℝ :=
  1 + Real.sqrt 2 + 4 * Real.sqrt 3 * (Real.logb 2 (1 / eta) + 1)

theorem explicitDyadicRadiusFactor_nonneg (eta : ℝ) :
    0 ≤ explicitDyadicRadiusFactor eta := by
  unfold explicitDyadicRadiusFactor
  positivity

theorem explicitDyadicRadiusFactor_lt_logFactor {eta : ℝ}
    (heta0 : 0 < eta) (heta1 : eta < 1) :
    explicitDyadicRadiusFactor eta < explicitDyadicLogFactor eta := by
  unfold explicitDyadicRadiusFactor explicitDyadicLogFactor
  have hN := explicitDyadicTailIndex_lt_logb_add_one heta0 heta1
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  nlinarith

theorem explicitDyadicLogFactor_pos {eta : ℝ}
    (heta0 : 0 < eta) (heta1 : eta < 1) :
    0 < explicitDyadicLogFactor eta :=
  (explicitDyadicRadiusFactor_nonneg eta).trans_lt
    (explicitDyadicRadiusFactor_lt_logFactor heta0 heta1)

/-- Dimension-normalized runtime radius for the explicit logarithmic truncation. -/
noncomputable def explicitDyadicRuntimeC (n : ℕ) (R2 eta : ℝ) : ℝ :=
  max 1 (Real.sqrt R2 * explicitDyadicRadiusFactor eta / Real.sqrt n)

theorem one_le_explicitDyadicRuntimeC (n : ℕ) (R2 eta : ℝ) :
    1 ≤ explicitDyadicRuntimeC n R2 eta := le_max_left _ _

theorem explicitDyadicRuntimeC_pos (n : ℕ) (R2 eta : ℝ) :
    0 < explicitDyadicRuntimeC n R2 eta :=
  one_pos.trans_le (one_le_explicitDyadicRuntimeC n R2 eta)

theorem explicitDyadicMomentRadius_cvSecondMoment_le_runtimeC_sqrt_n
    (hn : 1 ≤ n) {K : Set (Space n)} {R2 eta : ℝ}
    (hK : Ttc.CVAdmissible K R2) (_hR2 : 0 ≤ R2) :
    explicitDyadicMomentRadius (Ttc.cvSecondMoment K) eta ≤
      explicitDyadicRuntimeC n R2 eta * Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hM : Real.sqrt (Ttc.cvSecondMoment K) ≤ Real.sqrt R2 :=
    Real.sqrt_le_sqrt hK.2.2.2.2
  have hfac : 0 ≤ explicitDyadicRadiusFactor eta :=
    explicitDyadicRadiusFactor_nonneg eta
  have hraw : Real.sqrt R2 * explicitDyadicRadiusFactor eta / Real.sqrt n ≤
      explicitDyadicRuntimeC n R2 eta := le_max_right _ _
  unfold explicitDyadicMomentRadius explicitDyadicRadiusFactor at *
  calc
    Real.sqrt (Ttc.cvSecondMoment K) *
          (1 + Real.sqrt 2 + 4 * Real.sqrt 3 * explicitDyadicTailIndex eta) ≤
        Real.sqrt R2 *
          (1 + Real.sqrt 2 + 4 * Real.sqrt 3 * explicitDyadicTailIndex eta) := by
      exact mul_le_mul_of_nonneg_right hM hfac
    _ = (Real.sqrt R2 *
          (1 + Real.sqrt 2 + 4 * Real.sqrt 3 * explicitDyadicTailIndex eta) /
            Real.sqrt n) * Real.sqrt n := by
      field_simp [hsn.ne']
    _ ≤ explicitDyadicRuntimeC n R2 eta * Real.sqrt n :=
      mul_le_mul_of_nonneg_right hraw (Real.sqrt_nonneg _)

/-- The truncated closure fits the standard `C * sqrt n` sampler geometry. -/
theorem inter_explicitDyadicBall_subset_runtimeBall
    (hn : 1 ≤ n) {K : Set (Space n)} {R2 eta : ℝ}
    (hK : Ttc.CVAdmissible K R2) (hR2 : 0 ≤ R2) :
    closure K ∩ closedBall 0
        (explicitDyadicMomentRadius (Ttc.cvSecondMoment K) eta) ⊆
      closedBall 0 (explicitDyadicRuntimeC n R2 eta * Real.sqrt n) := by
  intro x hx
  exact mem_closedBall_zero_iff.mpr ((mem_closedBall_zero_iff.mp hx.2).trans
    (explicitDyadicMomentRadius_cvSecondMoment_le_runtimeC_sqrt_n hn hK hR2))

/-- The dimension-normalized radius has exactly the `max {R2*n^2,n^3}` geometry of the
source runtime, with one explicit squared logarithmic factor. -/
theorem explicitDyadicRuntimeC_sq_mul_n_cube_le
    (hn : 1 ≤ n) {R2 eta : ℝ} (hR2 : 0 ≤ R2)
    (heta0 : 0 < eta) (heta1 : eta < 1) :
    explicitDyadicRuntimeC n R2 eta ^ 2 * (n : ℝ) ^ 3 ≤
      2 * (n : ℝ) ^ 3 +
        2 * R2 * explicitDyadicLogFactor eta ^ 2 * (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hR2s : Real.sqrt R2 ^ 2 = R2 := Real.sq_sqrt hR2
  have hns : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  let F := explicitDyadicRadiusFactor eta
  let L := explicitDyadicLogFactor eta
  let q := Real.sqrt R2 * F / Real.sqrt n
  have hF0 : 0 ≤ F := explicitDyadicRadiusFactor_nonneg eta
  have hL0 : 0 ≤ L := (explicitDyadicLogFactor_pos heta0 heta1).le
  have hFL : F ≤ L := (explicitDyadicRadiusFactor_lt_logFactor heta0 heta1).le
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hC : explicitDyadicRuntimeC n R2 eta ≤ 1 + q := by
    unfold explicitDyadicRuntimeC
    dsimp [q, F]
    exact max_le (by linarith) (by linarith)
  have hC0 : 0 ≤ explicitDyadicRuntimeC n R2 eta :=
    (explicitDyadicRuntimeC_pos n R2 eta).le
  have hCsq : explicitDyadicRuntimeC n R2 eta ^ 2 ≤ 2 + 2 * q ^ 2 := by
    calc
      explicitDyadicRuntimeC n R2 eta ^ 2 ≤ (1 + q) ^ 2 := by nlinarith
      _ ≤ 2 + 2 * q ^ 2 := by nlinarith [sq_nonneg (1 - q)]
  have hF2 : F ^ 2 ≤ L ^ 2 := by nlinarith
  calc
    explicitDyadicRuntimeC n R2 eta ^ 2 * (n : ℝ) ^ 3 ≤
        (2 + 2 * q ^ 2) * (n : ℝ) ^ 3 := by
      exact mul_le_mul_of_nonneg_right hCsq (by positivity)
    _ = 2 * (n : ℝ) ^ 3 + 2 * R2 * F ^ 2 * (n : ℝ) ^ 2 := by
      dsimp [q]
      rw [div_pow, mul_pow, hR2s, hns]
      field_simp [hn0.ne']
    _ ≤ 2 * (n : ℝ) ^ 3 + 2 * R2 * L ^ 2 * (n : ℝ) ^ 2 := by
      gcongr
    _ = 2 * (n : ℝ) ^ 3 +
        2 * R2 * explicitDyadicLogFactor eta ^ 2 * (n : ℝ) ^ 2 := by
      rfl

/-- Source-shaped polynomial envelope for the explicit truncation geometry. -/
theorem explicitDyadicRuntimeC_source_envelope
    (hn : 1 ≤ n) {R2 eta : ℝ} (hR2 : 0 ≤ R2)
    (heta0 : 0 < eta) (heta1 : eta < 1) :
    explicitDyadicRuntimeC n R2 eta ^ 2 * (n : ℝ) ^ 3 ≤
      4 * max (R2 * (n : ℝ) ^ 2) ((n : ℝ) ^ 3) *
        explicitDyadicLogFactor eta ^ 2 := by
  have h := explicitDyadicRuntimeC_sq_mul_n_cube_le hn hR2 heta0 heta1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hL : 1 ≤ explicitDyadicLogFactor eta := by
    unfold explicitDyadicLogFactor
    have hlog : 0 ≤ Real.logb 2 (1 / eta) :=
      (Real.logb_pos (by norm_num : (1 : ℝ) < 2)
        ((lt_div_iff₀ heta0).2 (by simpa using heta1))).le
    have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have ht : 0 ≤ 4 * Real.sqrt 3 * (Real.logb 2 (1 / eta) + 1) := by
      positivity
    linarith
  have hL2 : 1 ≤ explicitDyadicLogFactor eta ^ 2 := by nlinarith
  have hmaxR : R2 * (n : ℝ) ^ 2 ≤
      max (R2 * (n : ℝ) ^ 2) ((n : ℝ) ^ 3) := le_max_left _ _
  have hmaxN : (n : ℝ) ^ 3 ≤
      max (R2 * (n : ℝ) ^ 2) ((n : ℝ) ^ 3) := le_max_right _ _
  have hmax0 : 0 ≤ max (R2 * (n : ℝ) ^ 2) ((n : ℝ) ^ 3) := by positivity
  have hN : (n : ℝ) ^ 3 ≤
      max (R2 * (n : ℝ) ^ 2) ((n : ℝ) ^ 3) *
        explicitDyadicLogFactor eta ^ 2 :=
    hmaxN.trans (le_mul_of_one_le_right hmax0 hL2)
  have hR : R2 * explicitDyadicLogFactor eta ^ 2 * (n : ℝ) ^ 2 ≤
      max (R2 * (n : ℝ) ^ 2) ((n : ℝ) ^ 3) *
        explicitDyadicLogFactor eta ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hmaxR
      (sq_nonneg (explicitDyadicLogFactor eta))]
  nlinarith

/-- The logarithmic factor after allocating one quarter of the requested accuracy to
moment truncation. -/
noncomputable def explicitDyadicSourceLogFactor (epsilon : ℝ) : ℝ :=
  1 + Real.sqrt 2 + 4 * Real.sqrt 3 * (Real.logb 2 (4 / epsilon) + 1)

theorem explicitDyadicLogFactor_quarter {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    explicitDyadicLogFactor (epsilon / 4) = explicitDyadicSourceLogFactor epsilon := by
  have hinv : 1 / (epsilon / 4) = (4 / epsilon : ℝ) := by
    field_simp [hepsilon.ne']
  unfold explicitDyadicLogFactor explicitDyadicSourceLogFactor
  rw [hinv]

/-- Source-regime specialization: the squared sampler geometry is bounded by
`4 * max {R2*n^2,n^3}` times the square of an explicit `log(4/epsilon)` factor. -/
theorem explicitDyadicRuntimeC_quarter_source_envelope
    (hn : 1 ≤ n) {R2 epsilon : ℝ} (hR2 : 0 ≤ R2)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 4) :
    explicitDyadicRuntimeC n R2 (epsilon / 4) ^ 2 * (n : ℝ) ^ 3 ≤
      4 * max (R2 * (n : ℝ) ^ 2) ((n : ℝ) ^ 3) *
        explicitDyadicSourceLogFactor epsilon ^ 2 := by
  have heta0 : 0 < epsilon / 4 := by positivity
  have heta1 : epsilon / 4 < 1 := by linarith
  simpa only [explicitDyadicLogFactor_quarter hepsilon0] using
    explicitDyadicRuntimeC_source_envelope hn hR2 heta0 heta1

end Ttc.CVAdaptive

#print axioms Ttc.CVAdaptive.tvLe_uniformOn_cvAdmissible_explicitDyadicClosure
#print axioms Ttc.CVAdaptive.explicitDyadicMomentRadius_cvSecondMoment_le_runtimeC_sqrt_n
#print axioms Ttc.CVAdaptive.inter_explicitDyadicBall_subset_runtimeBall
#print axioms Ttc.CVAdaptive.explicitDyadicRuntimeC_sq_mul_n_cube_le
#print axioms Ttc.CVAdaptive.explicitDyadicRuntimeC_source_envelope
#print axioms Ttc.CVAdaptive.explicitDyadicRuntimeC_quarter_source_envelope
