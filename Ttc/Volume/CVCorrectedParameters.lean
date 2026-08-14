/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVCorrectedAccuracy
import Arlib.Convexity.GaussianCooling.ChunkedVarBudget

/-!
# Concrete scalar parameters for corrected `lem:accuracy`

These deliberately conservative constants absorb both source corrections:

* the raw-square coefficient is indexed by `i+1`;
* the truncation union costs `3m/α`.

The sample budget is `k ε² ≥ 100000 (m+1)`, the truncation level is
`α = 100000 (m+1)/ε²`, and the per-transition dependence target is
`ν = ε²/(100000 α⁴ (m+1))`.  They are polynomial in the phase count and
accuracy.  Constants are intentionally loose: this file is an honest reusable
feasibility bundle, not a constant optimization.
-/

namespace Ttc.CVCorrected

open MeasureTheory Set ProbabilityTheory Arlib.GaussianCooling

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

noncomputable def correctedAlpha (m : ℕ) (ε : ℝ) : ℝ :=
  100000 * ((m : ℝ) + 1) / ε ^ 2

noncomputable def correctedNu (m : ℕ) (ε : ℝ) : ℝ :=
  ε ^ 2 / (100000 * correctedAlpha m ε ^ 4 * ((m : ℝ) + 1))

noncomputable def correctedQ (ε : ℝ) : ℝ := 1 + ε ^ 2 / 1000

noncomputable def correctedInnerAccuracy (ε : ℝ) : ℝ := ε / 4

noncomputable def correctedMeanAccuracy (ε : ℝ) : ℝ := ε / 4

/-- The corrected polynomial sample-count requirement. -/
def CorrectedSampleBudget (m k : ℕ) (ε : ℝ) : Prop :=
  100000 * ((m : ℝ) + 1) ≤ (k : ℝ) * ε ^ 2

theorem correctedAlpha_pos {m : ℕ} {ε : ℝ} (hε : 0 < ε) :
    0 < correctedAlpha m ε := by
  rw [correctedAlpha]
  exact div_pos (mul_pos (by norm_num) (by positivity)) (sq_pos_of_pos hε)

theorem one_le_correctedAlpha {m : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1 ≤ correctedAlpha m ε := by
  have he2 : ε ^ 2 ≤ 1 := by nlinarith [sq_nonneg ε]
  have hm : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  rw [correctedAlpha, le_div_iff₀ (sq_pos_of_pos hε)]
  nlinarith

theorem phase_div_correctedAlpha_le {m : ℕ} {ε : ℝ} (hε : 0 < ε) :
    (m : ℝ) / correctedAlpha m ε ≤ ε ^ 2 / 100000 := by
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hmp : 0 < (m : ℝ) + 1 := by positivity
  rw [correctedAlpha]
  field_simp [ne_of_gt hε, ne_of_gt hmp]
  nlinarith

theorem correctedNu_nonneg {m : ℕ} {ε : ℝ} : 0 ≤ correctedNu m ε := by
  unfold correctedNu
  positivity

theorem correctedNu_alpha_four_mul_le {m r : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hr : r ≤ m + 1) :
    2 * correctedNu m ε * correctedAlpha m ε ^ 4 * (r : ℝ) ≤
      ε ^ 2 / 50000 := by
  have ha := correctedAlpha_pos (m := m) hε
  have hmp : 0 < (m : ℝ) + 1 := by positivity
  have hr' : (r : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hr
  rw [correctedNu]
  field_simp [ne_of_gt ha, ne_of_gt hmp]
  nlinarith [sq_nonneg ε]

theorem corrected_covariance_scalar {m : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    2 * correctedNu m ε * correctedAlpha m ε ^ 2 ≤
      1 / (2 * correctedAlpha m ε) := by
  have ha1 := one_le_correctedAlpha (m := m) hε hε1
  have ha := correctedAlpha_pos (m := m) hε
  have hmp : 0 < (m : ℝ) + 1 := by positivity
  rw [correctedNu]
  field_simp [ne_of_gt ha, ne_of_gt hmp]
  have he2 : ε ^ 2 ≤ 1 := by nlinarith [sq_nonneg ε]
  nlinarith

theorem corrected_mean_dependence_le {m : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    2 * correctedNu m ε * correctedAlpha m ε ^ 2 * (m : ℝ) ≤
      correctedMeanAccuracy ε := by
  have ha1 := one_le_correctedAlpha (m := m) hε hε1
  have ha := correctedAlpha_pos (m := m) hε
  have hfour := correctedNu_alpha_four_mul_le (m := m) (r := m) hε (Nat.le_succ m)
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  unfold correctedMeanAccuracy
  have he2 : ε ^ 2 ≤ ε := by nlinarith [sq_nonneg ε]
  have ha2 : 1 ≤ correctedAlpha m ε ^ 2 := one_le_pow₀ ha1
  nlinarith [mul_nonneg (correctedNu_nonneg (m := m) (ε := ε)) hm0]

/-- The `k` budget makes every prefix product of the phase ratios
`1+8/k` at most `1+ε²/6250`. -/
theorem phaseMomentRatio_pow_le {m k i : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hk : CorrectedSampleBudget m k ε)
    (hi : i ≤ m) :
    (1 + 8 / (k : ℝ)) ^ i ≤ 1 + ε ^ 2 / 6250 := by
  have hkpos : 0 < k := by
    by_contra hk0
    have : k = 0 := Nat.eq_zero_of_not_pos hk0
    rw [CorrectedSampleBudget, this] at hk
    norm_num at hk
    have : (0 : ℝ) < 100000 * ((m : ℝ) + 1) := by positivity
    linarith
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hkpos
  have hiR : (i : ℝ) ≤ (m : ℝ) := by exact_mod_cast hi
  have hx0 : 0 ≤ (8 : ℝ) / k := div_nonneg (by norm_num) hkR.le
  have hexpArg : (i : ℝ) * (8 / (k : ℝ)) ≤ ε ^ 2 / 12500 := by
    rw [CorrectedSampleBudget] at hk
    have hki : 100000 * (i : ℝ) ≤ (k : ℝ) * ε ^ 2 := by
      calc
        100000 * (i : ℝ) ≤ 100000 * ((m : ℝ) + 1) := by nlinarith
        _ ≤ _ := hk
    rw [show (i : ℝ) * (8 / (k : ℝ)) = ((i : ℝ) * 8) / (k : ℝ) by ring]
    rw [div_le_iff₀ hkR]
    nlinarith
  calc
    (1 + 8 / (k : ℝ)) ^ i ≤ Real.exp ((i : ℝ) * (8 / (k : ℝ))) :=
      one_add_pow_le_exp hx0 i
    _ ≤ Real.exp (ε ^ 2 / 12500) := Real.exp_le_exp.mpr hexpArg
    _ ≤ 1 + 2 * (ε ^ 2 / 12500) := by
      apply exp_le_one_add_two_mul
      · positivity
      · have he2 : ε ^ 2 ≤ 1 := by nlinarith [sq_nonneg ε]
        nlinarith
    _ = 1 + ε ^ 2 / 6250 := by ring

/-- Concrete phase moment ratios imply the prefix second-moment estimate used
by the corrected recursion. -/
theorem prefixSecondMean_le_concrete [IsProbabilityMeasure μ]
    (V : ℕ → Ω → ℝ) {m k i : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hk : CorrectedSampleBudget m k ε)
    (hi : i ≤ m) (hV0 : ∀ j ω, 0 ≤ V j ω)
    (hratio : ∀ j,
      (∫ ω, (V j ω) ^ 2 ∂μ) ≤ (1 + 8 / (k : ℝ)) * (∫ ω, V j ω ∂μ) ^ 2) :
    prefixSecondMean μ V i ≤
      (1 + ε ^ 2 / 6250) * (prefixMean μ V i) ^ 2 := by
  have hkpos : 0 < (k : ℝ) := by
    have : 0 < k := by
      by_contra hk0
      have hkz : k = 0 := Nat.eq_zero_of_not_pos hk0
      rw [CorrectedSampleBudget, hkz] at hk
      norm_num at hk
      have : (0 : ℝ) < 100000 * ((m : ℝ) + 1) := by positivity
      linarith
    exact_mod_cast this
  have hc0 : ∀ _j : ℕ, 0 ≤ (1 + 8 / (k : ℝ)) := fun _ => by positivity
  have hbase := prefixSecondMean_le_mul_prefixMean_sq V
    (fun _ => 1 + 8 / (k : ℝ)) hV0 hc0 hratio i
  have hprod : prefixMomentRatio (fun _ => 1 + 8 / (k : ℝ)) i =
      (1 + 8 / (k : ℝ)) ^ i := by
    simp [prefixMomentRatio]
  rw [hprod] at hbase
  exact hbase.trans (mul_le_mul_of_nonneg_right
    (phaseMomentRatio_pow_le hε hε1 hk hi) (sq_nonneg _))

/-- Numeric heart: all corrected scalar premises, including the final relative
second moment and the `1/5` failure budget. -/
theorem corrected_parameter_bundle [IsProbabilityMeasure μ]
    (V : ℕ → Ω → ℝ) {m k : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hk : CorrectedSampleBudget m k ε)
    (hV0 : ∀ j ω, 0 ≤ V j ω)
    (hratio : ∀ j,
      (∫ ω, (V j ω) ^ 2 ∂μ) ≤ (1 + 8 / (k : ℝ)) * (∫ ω, V j ω ∂μ) ^ 2) :
    let α := correctedAlpha m ε
    let ν := correctedNu m ε
    let q := correctedQ ε
    let εc := correctedInnerAccuracy ε
    let η := correctedMeanAccuracy ε
    (1 ≤ α) ∧
    AccuracyLowerScalar μ V α ν m ∧
    (∀ i < m, 1 + 2 * ν * α ^ 2 * ((i + 1 : ℕ) : ℝ) ≤ 2) ∧
    (0 < 1 - (m : ℝ) / α) ∧
    ((m : ℝ) / α ≤ η) ∧
    (2 * ν * α ^ 2 * (m : ℝ) ≤ η) ∧
    (εc + η + εc * η ≤ ε) ∧
    ((1 + 2 * ν * α ^ 4 * (m : ℝ)) * prefixSecondMean μ V m ≤
      q * (1 - (m : ℝ) / α) ^ 2 * (prefixMean μ V m) ^ 2) ∧
    ((q - 1) / εc ^ 2 + 3 * (m : ℝ) / α + 1 / 20 ≤ 1 / 5) := by
  dsimp
  have ha1 := one_le_correctedAlpha (m := m) hε hε1
  have ht := phase_div_correctedAlpha_le (m := m) hε
  have he2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have he2le : ε ^ 2 ≤ 1 := by nlinarith [sq_nonneg ε]
  have hP2 := prefixSecondMean_le_concrete V hε hε1 hk le_rfl hV0 hratio
  have hC : 1 + 2 * correctedNu m ε * correctedAlpha m ε ^ 4 * (m : ℝ) ≤
      1 + ε ^ 2 / 50000 := by
    have h := correctedNu_alpha_four_mul_le (m := m) (r := m) hε (Nat.le_succ m)
    norm_num at h ⊢
    exact h
  have hscalar2 :
      (1 + 2 * correctedNu m ε * correctedAlpha m ε ^ 4 * (m : ℝ)) *
          prefixSecondMean μ V m ≤
        correctedQ ε * (1 - (m : ℝ) / correctedAlpha m ε) ^ 2 *
          (prefixMean μ V m) ^ 2 := by
    have hP0 : 0 ≤ (prefixMean μ V m) ^ 2 := sq_nonneg _
    have hP20 : 0 ≤ prefixSecondMean μ V m := prefixSecondMean_nonneg V m
    have hC0 : 0 ≤ 1 + 2 * correctedNu m ε * correctedAlpha m ε ^ 4 * (m : ℝ) := by
      have hterm : 0 ≤ 2 * correctedNu m ε * correctedAlpha m ε ^ 4 * (m : ℝ) :=
        mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) (correctedNu_nonneg (m := m) (ε := ε)))
            (pow_nonneg (le_trans (by norm_num) ha1) 4))
          (Nat.cast_nonneg m)
      linarith
    calc
      _ ≤ (1 + ε ^ 2 / 50000) *
          ((1 + ε ^ 2 / 6250) * (prefixMean μ V m) ^ 2) := by
            exact (mul_le_mul_of_nonneg_left hP2 hC0).trans
              (mul_le_mul_of_nonneg_right hC
                (mul_nonneg (by positivity) hP0))
      _ ≤ correctedQ ε * (1 - (m : ℝ) / correctedAlpha m ε) ^ 2 *
          (prefixMean μ V m) ^ 2 := by
        unfold correctedQ
        have ht0 : 0 ≤ (m : ℝ) / correctedAlpha m ε := by positivity
        have hsquare :
            (1 - ε ^ 2 / 100000) ^ 2 ≤
              (1 - (m : ℝ) / correctedAlpha m ε) ^ 2 := by
          apply (sq_le_sq₀ (by nlinarith) (by nlinarith)).2
          nlinarith
        have hnum :
            (1 + ε ^ 2 / 50000) * (1 + ε ^ 2 / 6250) ≤
              (1 + ε ^ 2 / 1000) * (1 - ε ^ 2 / 100000) ^ 2 := by
          nlinarith [sq_nonneg (ε ^ 2), mul_nonneg (sq_nonneg ε) (sub_nonneg.mpr he2le)]
        simpa [mul_assoc] using mul_le_mul_of_nonneg_right
          (hnum.trans (mul_le_mul_of_nonneg_left hsquare (by positivity))) hP0
  refine ⟨ha1, ?_, ?_, ?_, ?_, ?_, ?_, hscalar2, ?_⟩
  · constructor
    · exact corrected_covariance_scalar hε hε1
    · intro i hi
      have hi' : i + 1 ≤ m := Nat.succ_le_iff.mpr hi
      have hCi := correctedNu_alpha_four_mul_le (m := m) (r := i + 1) hε
        (hi'.trans (Nat.le_succ m))
      have hP2i := prefixSecondMean_le_concrete V hε hε1 hk hi' hV0 hratio
      have hP0 : 0 ≤ (prefixMean μ V (i + 1)) ^ 2 := sq_nonneg _
      have hP20 : 0 ≤ prefixSecondMean μ V (i + 1) := prefixSecondMean_nonneg V (i + 1)
      have hC0 : 0 ≤ 1 + 2 * correctedNu m ε * correctedAlpha m ε ^ 4 *
          ((i + 1 : ℕ) : ℝ) := by
        have hterm : 0 ≤ 2 * correctedNu m ε * correctedAlpha m ε ^ 4 *
            ((i + 1 : ℕ) : ℝ) :=
          mul_nonneg
            (mul_nonneg (mul_nonneg (by norm_num)
              (correctedNu_nonneg (m := m) (ε := ε)))
                (pow_nonneg (le_trans (by norm_num) ha1) 4))
            (Nat.cast_nonneg (i + 1))
        linarith
      calc
        _ ≤ (1 + ε ^ 2 / 50000) *
            ((1 + ε ^ 2 / 6250) * (prefixMean μ V (i + 1)) ^ 2) := by
              exact (mul_le_mul_of_nonneg_left hP2i hC0).trans
                (mul_le_mul_of_nonneg_right (by linarith)
                  (mul_nonneg (by positivity) hP0))
        _ ≤ 2 * (prefixMean μ V (i + 1)) ^ 2 := by
          simpa [mul_assoc] using mul_le_mul_of_nonneg_right
            (show (1 + ε ^ 2 / 50000) * (1 + ε ^ 2 / 6250) ≤ 2 by
              nlinarith [sq_nonneg (ε ^ 2)]) hP0
  · intro i hi
    have hi' : i + 1 ≤ m := Nat.succ_le_iff.mpr hi
    have h4 := correctedNu_alpha_four_mul_le (m := m) (r := i + 1) hε
      (hi'.trans (Nat.le_succ m))
    have ha2 : 1 ≤ correctedAlpha m ε ^ 2 := one_le_pow₀ ha1
    nlinarith [correctedNu_nonneg (m := m) (ε := ε)]
  · nlinarith
  · unfold correctedMeanAccuracy
    have he2ε : ε ^ 2 ≤ ε := by nlinarith [sq_nonneg ε]
    nlinarith
  · exact corrected_mean_dependence_le hε hε1
  · unfold correctedInnerAccuracy correctedMeanAccuracy
    nlinarith [sq_nonneg ε]
  · unfold correctedQ correctedInnerAccuracy
    have htrunc : 3 * (m : ℝ) / correctedAlpha m ε ≤ 3 * ε ^ 2 / 100000 := by
      calc
        3 * (m : ℝ) / correctedAlpha m ε =
            3 * ((m : ℝ) / correctedAlpha m ε) := by ring
        _ ≤ 3 * (ε ^ 2 / 100000) := mul_le_mul_of_nonneg_left ht (by norm_num)
        _ = 3 * ε ^ 2 / 100000 := by ring
    rw [show ((1 + ε ^ 2 / 1000) - 1) / (ε / 4) ^ 2 = 2 / 125 by
      field_simp [ne_of_gt hε]
      ring]
    nlinarith

/-- A direct concrete-parameter instance of the corrected generic accuracy
theorem.  The only schedule-specific scalar input left is the polynomial sample
budget `CorrectedSampleBudget`; exact coupling is allocated probability `1/20`.
-/
theorem corrected_lem_accuracy_concrete [IsProbabilityMeasure μ]
    (V Wbar W : ℕ → Ω → ℝ) {m k : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hk : CorrectedSampleBudget m k ε)
    (hVm : ∀ j, Measurable (V j)) (hV0 : ∀ j ω, 0 ≤ V j ω)
    (hEpos : ∀ j, 0 < ∫ ω, V j ω ∂μ)
    (hVcap : ∀ j ω, V j ω ≤
      2 * correctedAlpha m ε * ∫ z, V j z ∂μ)
    (hV2 : ∀ j, Integrable (fun ω => (V j ω) ^ 2) μ)
    (hV2cap : ∀ j ω, (V j ω) ^ 2 ≤
      2 * correctedAlpha m ε ^ 2 * ∫ z, (V j z) ^ 2 ∂μ)
    (hindep : ∀ i, NuIndep μ
      (accuracyU μ V (correctedAlpha m ε) i) (V (i + 1)) (correctedNu m ε))
    (hindepSq : ∀ i, NuIndep μ
      (fun ω => (accuracyU μ V (correctedAlpha m ε) i ω) ^ 2)
      (fun ω => (V (i + 1) ω) ^ 2) (correctedNu m ε))
    (hWm : ∀ j, Measurable (Wbar j)) (hW0 : ∀ j ω, 0 ≤ Wbar j ω)
    (hWint : ∀ j, Integrable (Wbar j) μ)
    (hWEpos : ∀ j, 0 < ∫ ω, Wbar j ω ∂μ)
    (hVdef : ∀ j ω, V j ω = min (Wbar j ω)
      (correctedAlpha m ε * ∫ z, Wbar j z ∂μ))
    (hratio : ∀ j,
      (∫ ω, (V j ω) ^ 2 ∂μ) ≤
        (1 + 8 / (k : ℝ)) * (∫ ω, V j ω ∂μ) ^ 2)
    {Eexact : Set Ω} (hEexact : MeasurableSet Eexact)
    (hExactFail : μ.real Eexactᶜ ≤ 1 / 20)
    (hExact : ∀ ω ∈ Eexact, phaseProduct Wbar m ω = phaseProduct W m ω) :
    μ.real {ω | phaseProduct W m ω ∉ relErr ε (prefixMean μ V m)} ≤ 1 / 5 := by
  rcases corrected_parameter_bundle V hε hε1 hk hV0 hratio with
    ⟨hα, hscalar, hcoef, hmeanPos, hmeanLo, hmeanHi, hcompose, hsecond, hbudget⟩
  have hq : 0 ≤ correctedQ ε := by
    rw [correctedQ]
    positivity
  have hεc : 0 < correctedInnerAccuracy ε := by
    rw [correctedInnerAccuracy]
    positivity
  have hη : 0 ≤ correctedMeanAccuracy ε := by
    rw [correctedMeanAccuracy]
    positivity
  have hbad := corrected_lem_accuracy_of_recursion V Wbar W
    (α := correctedAlpha m ε) (ν := correctedNu m ε) (q := correctedQ ε)
    (εc := correctedInnerAccuracy ε) (η := correctedMeanAccuracy ε)
    (ε := ε) (δexact := 1 / 20) hα hq hεc hη hVm hV0 hEpos hVcap hV2
    hV2cap hindep hindepSq hWm hW0 hWint hWEpos hVdef hscalar hcoef hmeanPos
    hsecond hmeanLo hmeanHi hcompose hEexact hExactFail hExact
  exact hbad.trans hbudget

#print axioms phaseMomentRatio_pow_le
#print axioms prefixSecondMean_le_concrete
#print axioms corrected_parameter_bundle
#print axioms corrected_lem_accuracy_concrete

end Ttc.CVCorrected
