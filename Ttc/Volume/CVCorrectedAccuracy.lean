/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Probability.AccuracyLowerRecursion
import Ttc.Volume.CousinsVempala

/-!
# Corrected dependent-sample form of Cousins--Vempala `lem:accuracy`

This capstone combines the corrected `U` recursion with Chebyshev, the two
Markov truncation estimates, a finite union bound, and an external exact
coupling event.  No independence between the bad events is assumed.

The corrected losses from the preceding files are retained: `U_m` has lower
mean factor `1-m/α`, and the raw square step uses `(i+1)`.  Their effect is
confined to the explicit scalar hypotheses below.
-/

namespace Ttc.CVCorrected

open MeasureTheory Set ProbabilityTheory Arlib.GaussianCooling
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Product of the first `m` paper-indexed phase variables. -/
noncomputable def phaseProduct (F : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) : ℝ :=
  ∏ j ∈ Finset.range m, F (j + 1) ω

/-- A strict-threshold real-valued Markov inequality. -/
theorem measureReal_lt_le_integral_div [IsFiniteMeasure μ]
    {F : Ω → ℝ} (hF0 : ∀ ω, 0 ≤ F ω)
    (hFint : Integrable F μ) {a : ℝ} (ha : 0 < a) :
    μ.real {ω | a < F ω} ≤ (∫ ω, F ω ∂μ) / a := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (Filter.Eventually.of_forall hF0) hFint a
  have hmono : μ.real {ω | a < F ω} ≤ μ.real {ω | a ≤ F ω} :=
    measureReal_mono (by
      intro ω hω
      change a < F ω at hω
      change a ≤ F ω
      exact hω.le) (measure_ne_top μ _)
  rw [le_div_iff₀ ha]
  calc
    μ.real {ω | a < F ω} * a = a * μ.real {ω | a < F ω} := by ring
    _ ≤ a * μ.real {ω | a ≤ F ω} := mul_le_mul_of_nonneg_left hmono ha.le
    _ ≤ ∫ ω, F ω ∂μ := hmarkov

/-- If none of the recursive truncations fires, `U_m` is the product of the
`V` variables. -/
theorem accuracyU_eq_phaseProduct_of_noTruncation
    (V : ℕ → Ω → ℝ) (α : ℝ) (m : ℕ) (ω : Ω)
    (hgood : ∀ i < m,
      accuracyU μ V α (i + 1) ω = accuracyU μ V α i ω * V (i + 1) ω) :
    accuracyU μ V α m ω = phaseProduct V m ω := by
  induction m with
  | zero => simp [phaseProduct]
  | succ m ih =>
      rw [hgood m (Nat.lt_succ_self m), ih (fun i hi => hgood i (hi.trans_le (Nat.le_succ m)))]
      simp [phaseProduct, Finset.prod_range_succ]

/-- One `U`-truncation failure has probability at most `2/α`.  The scalar
premise is the corrected mean coefficient at this step. -/
theorem measureReal_accuracyU_truncation_ne_le [IsProbabilityMeasure μ]
    (V : ℕ → Ω → ℝ) {α ν : ℝ} (hα : 1 ≤ α)
    (hVm : ∀ j, Measurable (V j)) (hV0 : ∀ j ω, 0 ≤ V j ω)
    (hEpos : ∀ j, 0 < ∫ ω, V j ω ∂μ)
    (hVcap : ∀ j ω, V j ω ≤ 2 * α * ∫ z, V j z ∂μ)
    (hindep : ∀ i, NuIndep μ (accuracyU μ V α i) (V (i + 1)) ν)
    (i : ℕ) (hcoef : 1 + 2 * ν * α ^ 2 * ((i + 1 : ℕ) : ℝ) ≤ 2) :
    μ.real {ω | accuracyU μ V α (i + 1) ω ≠
        accuracyU μ V α i ω * V (i + 1) ω} ≤ 2 / α := by
  let R : Ω → ℝ := fun ω => accuracyU μ V α i ω * V (i + 1) ω
  let P : ℝ := prefixMean μ V (i + 1)
  have hα0 : 0 < α := lt_of_lt_of_le zero_lt_one hα
  have hPpos : 0 < P := prefixMean_pos V hEpos (i + 1)
  have hR0 : ∀ ω, 0 ≤ R ω := fun ω =>
    mul_nonneg (accuracyU_nonneg V hα0.le hV0 i ω) (hV0 (i + 1) ω)
  have hUint := integrable_accuracyU (μ := μ) V hα hVm hV0 i
  have hVint := integrable_V_of_le_two_mul (μ := μ) V hVm hV0 hVcap (i + 1)
  have hRint : Integrable R μ :=
    hVint.bdd_mul (measurable_accuracyU V α hVm i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (accuracyU_nonneg V hα0.le hV0 i ω)]
        exact accuracyU_le_cap V hα i ω)
  have hbadsub :
      {ω | accuracyU μ V α (i + 1) ω ≠
          accuracyU μ V α i ω * V (i + 1) ω} ⊆ {ω | α * P < R ω} := by
    intro ω hω
    simp only [accuracyU_succ] at hω
    by_contra hn
    exact hω (min_eq_left (not_lt.mp hn))
  have hrawUpper : (∫ ω, R ω ∂μ) ≤
      (1 + 2 * ν * α ^ 2 * ((i + 1 : ℕ) : ℝ)) * P := by
    have hUi := integral_accuracyU_le (μ := μ) V hα hVm hV0 hVcap hindep i
    have hcov := accuracyU_mul_V_covariance_le (μ := μ) V hα hVm hV0 hVcap i
      (hindep i)
    have hE0 : 0 ≤ ∫ ω, V (i + 1) ω ∂μ := (hEpos (i + 1)).le
    have hmul := mul_le_mul_of_nonneg_right hUi hE0
    rw [abs_le] at hcov
    change (∫ ω, accuracyU μ V α i ω * V (i + 1) ω ∂μ) ≤
      (1 + 2 * ν * α ^ 2 * ((i + 1 : ℕ) : ℝ)) * prefixMean μ V (i + 1)
    rw [prefixMean_succ]
    rw [prefixMean_succ] at hcov
    push_cast
    nlinarith [hmul, hcov.2]
  have hmarkov := measureReal_lt_le_integral_div hR0 hRint
    (mul_pos hα0 hPpos)
  calc
    μ.real {ω | accuracyU μ V α (i + 1) ω ≠
        accuracyU μ V α i ω * V (i + 1) ω}
        ≤ μ.real {ω | α * P < R ω} :=
          measureReal_mono hbadsub (measure_ne_top μ _)
    _ ≤ (∫ ω, R ω ∂μ) / (α * P) := hmarkov
    _ ≤ ((1 + 2 * ν * α ^ 2 * ((i + 1 : ℕ) : ℝ)) * P) / (α * P) := by
      gcongr
    _ ≤ 2 / α := by
      field_simp [ne_of_gt hα0, ne_of_gt hPpos]
      nlinarith

/-- Markov controls one phase truncation `V_j = min(Wbar_j, α E Wbar_j)` by
`1/α`. -/
theorem measureReal_phase_truncation_ne_le [IsProbabilityMeasure μ]
    {Wbar V : ℕ → Ω → ℝ} {α : ℝ} (hα : 1 ≤ α)
    (hW0 : ∀ j ω, 0 ≤ Wbar j ω)
    (hWint : ∀ j, Integrable (Wbar j) μ) (hWEpos : ∀ j, 0 < ∫ ω, Wbar j ω ∂μ)
    (hVdef : ∀ j ω, V j ω = min (Wbar j ω) (α * ∫ z, Wbar j z ∂μ))
    (j : ℕ) :
    μ.real {ω | V j ω ≠ Wbar j ω} ≤ 1 / α := by
  have hα0 : 0 < α := lt_of_lt_of_le zero_lt_one hα
  have hEpos := hWEpos j
  have hsub : {ω | V j ω ≠ Wbar j ω} ⊆
      {ω | α * (∫ z, Wbar j z ∂μ) < Wbar j ω} := by
    intro ω hω
    change V j ω ≠ Wbar j ω at hω
    rw [hVdef j ω] at hω
    change α * (∫ z, Wbar j z ∂μ) < Wbar j ω
    by_contra hn
    exact hω (min_eq_left (not_lt.mp hn))
  have hmarkov := measureReal_lt_le_integral_div (hW0 j) (hWint j)
    (mul_pos hα0 hEpos)
  calc
    μ.real {ω | V j ω ≠ Wbar j ω}
        ≤ μ.real {ω | α * (∫ z, Wbar j z ∂μ) < Wbar j ω} :=
          measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ (∫ z, Wbar j z ∂μ) / (α * ∫ z, Wbar j z ∂μ) := hmarkov
    _ = 1 / α := by field_simp [ne_of_gt hα0, ne_of_gt hEpos]

/-- Chebyshev for `U_m`, transferred from its mean to `prefixMean`. -/
theorem measureReal_accuracyU_notMem_relErr_prefixMean_le [IsProbabilityMeasure μ]
    (V : ℕ → Ω → ℝ) {α ν q εc η ε : ℝ}
    (hα : 1 ≤ α) (hεc : 0 < εc) (hη : 0 ≤ η)
    (hVm : ∀ j, Measurable (V j)) (hV0 : ∀ j ω, 0 ≤ V j ω)
    (hEpos : ∀ j, 0 < ∫ ω, V j ω ∂μ)
    (hV2 : ∀ j, Integrable (fun ω => (V j ω) ^ 2) μ)
    {m : ℕ}
    (hlower : (1 - (m : ℝ) / α) * prefixMean μ V m ≤
      ∫ ω, accuracyU μ V α m ω ∂μ)
    (hupper : (∫ ω, accuracyU μ V α m ω ∂μ) ≤
      (1 + 2 * ν * α ^ 2 * (m : ℝ)) * prefixMean μ V m)
    (hsecond : (∫ ω, (accuracyU μ V α m ω) ^ 2 ∂μ) ≤
      q * (∫ ω, accuracyU μ V α m ω ∂μ) ^ 2)
    (hmeanPos : 0 < 1 - (m : ℝ) / α)
    (hmeanLo : (m : ℝ) / α ≤ η) (hmeanHi : 2 * ν * α ^ 2 * (m : ℝ) ≤ η)
    (hcompose : εc + η + εc * η ≤ ε) :
    μ.real {ω | accuracyU μ V α m ω ∉ relErr ε (prefixMean μ V m)} ≤
      (q - 1) / εc ^ 2 := by
  have hPpos := prefixMean_pos V hEpos m
  have hEUpos : 0 < ∫ ω, accuracyU μ V α m ω ∂μ := by
    exact lt_of_lt_of_le (mul_pos hmeanPos hPpos) hlower
  have hmean : (∫ ω, accuracyU μ V α m ω ∂μ) ∈
      relErr η (prefixMean μ V m) := by
    constructor
    · calc
        (1 - η) * prefixMean μ V m ≤
            (1 - (m : ℝ) / α) * prefixMean μ V m := by
              gcongr
        _ ≤ _ := hlower
    · calc
        _ ≤ (1 + 2 * ν * α ^ 2 * (m : ℝ)) * prefixMean μ V m := hupper
        _ ≤ (1 + η) * prefixMean μ V m := by gcongr
  have hU2int := integrable_accuracyU_sq (μ := μ) V hα hVm hV0 hV2 m
  have hULp : MemLp (accuracyU μ V α m) 2 μ :=
    (memLp_two_iff_integrable_sq
      (measurable_accuracyU V α hVm m).aestronglyMeasurable).2 hU2int
  have hcheb := Ttc.CV.measure_notMem_relErr_le (μ := μ) hULp hεc hEUpos hsecond
  have hsub : {ω | accuracyU μ V α m ω ∉ relErr ε (prefixMean μ V m)} ⊆
      {ω | accuracyU μ V α m ω ∉
        relErr εc (∫ z, accuracyU μ V α m z ∂μ)} := by
    intro ω hbad hgood
    have hcomp := Ttc.CV.relErr_trans hεc.le hη hPpos.le hgood hmean
    exact hbad (Ttc.CV.relErr_mono hcompose hPpos.le hcomp)
  have hq1 : 1 ≤ q := by
    have hj := sq_integral_le_integral_sq
      (measurable_accuracyU V α hVm m) hU2int
    have hEU2 : 0 < (∫ ω, accuracyU μ V α m ω ∂μ) ^ 2 := sq_pos_of_pos hEUpos
    nlinarith
  calc
    μ.real {ω | accuracyU μ V α m ω ∉ relErr ε (prefixMean μ V m)}
        ≤ μ.real {ω | accuracyU μ V α m ω ∉
            relErr εc (∫ z, accuracyU μ V α m z ∂μ)} :=
          measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ (q - 1) / εc ^ 2 := by
      rw [Measure.real]
      have hre := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb
      rw [ENNReal.toReal_ofReal
        (div_nonneg (sub_nonneg.mpr hq1) (sq_nonneg εc))] at hre
      exact hre

/-- **Corrected generic `lem:accuracy`.** The output product is relatively
accurate except on the Chebyshev event, an `O(m/α)` truncation union, and the
external exact-coupling failure event. -/
theorem corrected_lem_accuracy [IsProbabilityMeasure μ]
    (V Wbar W : ℕ → Ω → ℝ) {α ν q εc η ε δexact : ℝ}
    (hα : 1 ≤ α) (hεc : 0 < εc) (hη : 0 ≤ η)
    (hVm : ∀ j, Measurable (V j)) (hV0 : ∀ j ω, 0 ≤ V j ω)
    (hEpos : ∀ j, 0 < ∫ ω, V j ω ∂μ)
    (hVcap : ∀ j ω, V j ω ≤ 2 * α * ∫ z, V j z ∂μ)
    (hV2 : ∀ j, Integrable (fun ω => (V j ω) ^ 2) μ)
    (hindep : ∀ i, NuIndep μ (accuracyU μ V α i) (V (i + 1)) ν)
    (_hWm : ∀ j, Measurable (Wbar j)) (hW0 : ∀ j ω, 0 ≤ Wbar j ω)
    (hWint : ∀ j, Integrable (Wbar j) μ) (hWEpos : ∀ j, 0 < ∫ ω, Wbar j ω ∂μ)
    (hVdef : ∀ j ω, V j ω = min (Wbar j ω) (α * ∫ z, Wbar j z ∂μ))
    {m : ℕ}
    (hcoef : ∀ i < m, 1 + 2 * ν * α ^ 2 * ((i + 1 : ℕ) : ℝ) ≤ 2)
    (hlower : (1 - (m : ℝ) / α) * prefixMean μ V m ≤
      ∫ ω, accuracyU μ V α m ω ∂μ)
    (hupper : (∫ ω, accuracyU μ V α m ω ∂μ) ≤
      (1 + 2 * ν * α ^ 2 * (m : ℝ)) * prefixMean μ V m)
    (hsecond : (∫ ω, (accuracyU μ V α m ω) ^ 2 ∂μ) ≤
      q * (∫ ω, accuracyU μ V α m ω ∂μ) ^ 2)
    (hmeanPos : 0 < 1 - (m : ℝ) / α)
    (hmeanLo : (m : ℝ) / α ≤ η) (hmeanHi : 2 * ν * α ^ 2 * (m : ℝ) ≤ η)
    (hcompose : εc + η + εc * η ≤ ε)
    {Eexact : Set Ω} (_hEexact : MeasurableSet Eexact)
    (hExactFail : μ.real Eexactᶜ ≤ δexact)
    (hExact : ∀ ω ∈ Eexact, phaseProduct Wbar m ω = phaseProduct W m ω) :
    μ.real {ω | phaseProduct W m ω ∉ relErr ε (prefixMean μ V m)} ≤
      (q - 1) / εc ^ 2 + 3 * (m : ℝ) / α + δexact := by
  let BU : Fin m → Set Ω := fun i =>
    {ω | accuracyU μ V α ((i : ℕ) + 1) ω ≠
      accuracyU μ V α (i : ℕ) ω * V ((i : ℕ) + 1) ω}
  let BV : Fin m → Set Ω := fun i => {ω | V ((i : ℕ) + 1) ω ≠ Wbar ((i : ℕ) + 1) ω}
  let BC : Set Ω := {ω | accuracyU μ V α m ω ∉ relErr ε (prefixMean μ V m)}
  have hBC := measureReal_accuracyU_notMem_relErr_prefixMean_le V hα hεc hη hVm hV0
    hEpos hV2 hlower hupper hsecond hmeanPos hmeanLo hmeanHi hcompose
  have hBU : ∀ i : Fin m, μ.real (BU i) ≤ 2 / α := fun i =>
    measureReal_accuracyU_truncation_ne_le V hα hVm hV0 hEpos hVcap hindep i
      (hcoef i i.isLt)
  have hBV : ∀ i : Fin m, μ.real (BV i) ≤ 1 / α := fun i =>
    measureReal_phase_truncation_ne_le hα hW0 hWint hWEpos hVdef ((i : ℕ) + 1)
  have hsubset : {ω | phaseProduct W m ω ∉ relErr ε (prefixMean μ V m)} ⊆
      BC ∪ (⋃ i, BU i) ∪ (⋃ i, BV i) ∪ Eexactᶜ := by
    intro ω hbad
    contrapose! hbad
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_compl_iff, not_or, not_exists,
      not_not] at hbad
    rcases hbad with ⟨⟨⟨hC, hUs⟩, hVs⟩, hEx⟩
    have hUeq := accuracyU_eq_phaseProduct_of_noTruncation V α m ω fun i hi => by
      exact not_ne_iff.mp (hUs ⟨i, hi⟩)
    have hVeq : phaseProduct V m ω = phaseProduct Wbar m ω := by
      apply Finset.prod_congr rfl
      intro j hj
      exact not_ne_iff.mp (hVs ⟨j, Finset.mem_range.mp hj⟩)
    intro hwbad
    change phaseProduct W m ω ∉ relErr ε (prefixMean μ V m) at hwbad
    have hC' : accuracyU μ V α m ω ∈ relErr ε (prefixMean μ V m) := by
      exact Classical.not_not.mp (by simpa [BC] using hC)
    rw [hUeq, hVeq, hExact ω hEx] at hC'
    exact hwbad hC'
  calc
    μ.real {ω | phaseProduct W m ω ∉ relErr ε (prefixMean μ V m)}
        ≤ μ.real (BC ∪ (⋃ i, BU i) ∪ (⋃ i, BV i) ∪ Eexactᶜ) :=
          measureReal_mono hsubset (measure_ne_top μ _)
    _ ≤ μ.real BC + μ.real (⋃ i, BU i) + μ.real (⋃ i, BV i) + μ.real Eexactᶜ := by
      have h1 : μ.real (BC ∪ ⋃ i, BU i) ≤
          μ.real BC + μ.real (⋃ i, BU i) := measureReal_union_le _ _
      have h2 : μ.real ((BC ∪ ⋃ i, BU i) ∪ ⋃ i, BV i) ≤
          μ.real (BC ∪ ⋃ i, BU i) + μ.real (⋃ i, BV i) := measureReal_union_le _ _
      have h3 : μ.real (((BC ∪ ⋃ i, BU i) ∪ ⋃ i, BV i) ∪ Eexactᶜ) ≤
          μ.real ((BC ∪ ⋃ i, BU i) ∪ ⋃ i, BV i) + μ.real Eexactᶜ :=
        measureReal_union_le _ _
      linarith
    _ ≤ (q - 1) / εc ^ 2 + (m : ℝ) * (2 / α) + (m : ℝ) * (1 / α) + δexact := by
      gcongr
      · exact (measureReal_iUnion_fintype_le BU).trans (by
          calc
            ∑ i : Fin m, μ.real (BU i) ≤ ∑ _i : Fin m, 2 / α := Finset.sum_le_sum fun i _ => hBU i
            _ = (m : ℝ) * (2 / α) := by simp)
      · exact (measureReal_iUnion_fintype_le BV).trans (by
          calc
            ∑ i : Fin m, μ.real (BV i) ≤ ∑ _i : Fin m, 1 / α := Finset.sum_le_sum fun i _ => hBV i
            _ = (m : ℝ) * (1 / α) := by simp)
    _ = (q - 1) / εc ^ 2 + 3 * (m : ℝ) / α + δexact := by ring

/-- The same capstone with its three moment hypotheses discharged directly by
`AccuracyLowerRecursion`.  This is the plug-in form for the corrected
`lem:accuracy` development. -/
theorem corrected_lem_accuracy_of_recursion [IsProbabilityMeasure μ]
    (V Wbar W : ℕ → Ω → ℝ) {α ν q εc η ε δexact : ℝ}
    (hα : 1 ≤ α) (hq : 0 ≤ q) (hεc : 0 < εc) (hη : 0 ≤ η)
    (hVm : ∀ j, Measurable (V j)) (hV0 : ∀ j ω, 0 ≤ V j ω)
    (hEpos : ∀ j, 0 < ∫ ω, V j ω ∂μ)
    (hVcap : ∀ j ω, V j ω ≤ 2 * α * ∫ z, V j z ∂μ)
    (hV2 : ∀ j, Integrable (fun ω => (V j ω) ^ 2) μ)
    (hV2cap : ∀ j ω,
      (V j ω) ^ 2 ≤ 2 * α ^ 2 * ∫ z, (V j z) ^ 2 ∂μ)
    (hindep : ∀ i, NuIndep μ (accuracyU μ V α i) (V (i + 1)) ν)
    (hindepSq : ∀ i, NuIndep μ (fun ω => (accuracyU μ V α i ω) ^ 2)
      (fun ω => (V (i + 1) ω) ^ 2) ν)
    (hWm : ∀ j, Measurable (Wbar j)) (hW0 : ∀ j ω, 0 ≤ Wbar j ω)
    (hWint : ∀ j, Integrable (Wbar j) μ) (hWEpos : ∀ j, 0 < ∫ ω, Wbar j ω ∂μ)
    (hVdef : ∀ j ω, V j ω = min (Wbar j ω) (α * ∫ z, Wbar j z ∂μ))
    {m : ℕ} (hscalar : AccuracyLowerScalar μ V α ν m)
    (hcoef : ∀ i < m, 1 + 2 * ν * α ^ 2 * ((i + 1 : ℕ) : ℝ) ≤ 2)
    (hmeanPos : 0 < 1 - (m : ℝ) / α)
    (hsecondScalar :
      (1 + 2 * ν * α ^ 4 * (m : ℝ)) * prefixSecondMean μ V m ≤
        q * (1 - (m : ℝ) / α) ^ 2 * (prefixMean μ V m) ^ 2)
    (hmeanLo : (m : ℝ) / α ≤ η) (hmeanHi : 2 * ν * α ^ 2 * (m : ℝ) ≤ η)
    (hcompose : εc + η + εc * η ≤ ε)
    {Eexact : Set Ω} (hEexact : MeasurableSet Eexact)
    (hExactFail : μ.real Eexactᶜ ≤ δexact)
    (hExact : ∀ ω ∈ Eexact, phaseProduct Wbar m ω = phaseProduct W m ω) :
    μ.real {ω | phaseProduct W m ω ∉ relErr ε (prefixMean μ V m)} ≤
      (q - 1) / εc ^ 2 + 3 * (m : ℝ) / α + δexact := by
  obtain ⟨hlower, hupper, hsecond⟩ :=
    accuracyU_mean_and_secondMoment V hα hq hVm hV0 hEpos hVcap hV2 hV2cap
      hindep hindepSq (i := m) (m := m) le_rfl hscalar hmeanPos hsecondScalar
  exact corrected_lem_accuracy V Wbar W hα hεc hη hVm hV0 hEpos hVcap hV2 hindep
    hWm hW0 hWint hWEpos hVdef hcoef hlower hupper hsecond hmeanPos hmeanLo hmeanHi
    hcompose hEexact hExactFail hExact

/-- The paper's advertised `4/5` success follows once the explicit total bad
budget is at most `1/5`. -/
theorem corrected_lem_accuracy_four_fifths [IsProbabilityMeasure μ]
    (W : ℕ → Ω → ℝ) (hWm : ∀ j, Measurable (W j))
    {m : ℕ} {ε target failure : ℝ}
    (hbad : μ.real {ω | phaseProduct W m ω ∉ relErr ε target} ≤ failure)
    (hbudget : failure ≤ 1 / 5) :
    4 / 5 ≤ μ.real {ω | phaseProduct W m ω ∈ relErr ε target} := by
  have hprodmeas : Measurable (phaseProduct W m) := by
    unfold phaseProduct
    fun_prop
  have hgoodm : MeasurableSet {ω | phaseProduct W m ω ∈ relErr ε target} :=
    measurableSet_Icc.preimage hprodmeas
  have hcompl : {ω | phaseProduct W m ω ∉ relErr ε target} =
      {ω | phaseProduct W m ω ∈ relErr ε target}ᶜ := rfl
  rw [hcompl, measureReal_compl hgoodm] at hbad
  rw [probReal_univ] at hbad
  nlinarith

#print axioms measureReal_accuracyU_truncation_ne_le
#print axioms measureReal_phase_truncation_ne_le
#print axioms measureReal_accuracyU_notMem_relErr_prefixMean_le
#print axioms corrected_lem_accuracy
#print axioms corrected_lem_accuracy_of_recursion
#print axioms corrected_lem_accuracy_four_fifths

end Ttc.CVCorrected
