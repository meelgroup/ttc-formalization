/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.PublicRuntime
import ttc.Analysis.GetPrecisionBound

/-! # The arithmetic bound in headline form -/

set_option autoImplicit false

noncomputable section

namespace ttc

open scoped ENNReal

namespace Tape

open TTCRuntime

variable {n k : ℕ} {F : LRAFormula n k}

private theorem lmax_one (a : ℝ) : 1 ≤ max 1 a := le_max_left _ _

private theorem runtimeLog_one_le (D : Decomposition F) (p : ApproxParams) :
    1 ≤ ttcRuntimeLog D p := by
  unfold ttcRuntimeLog
  linarith [lmax_one (Real.log (10000 * (D.componentCount : ℝ) * n * RMax D *
      Rho D ^ 2 / (p.epsilon * p.delta))),
    le_max_left 0 (Real.log (theorem3OuterRadiusMax D)),
    le_max_left 0 (Real.log (theorem3InverseInradiusMax D))]

private theorem inputProduct_le (D : Decomposition F) (p : ApproxParams) (hm : 0 < D.componentCount)
    (hn : 1 ≤ n) :
    (1 : ℝ) ≤ 10000 * (D.componentCount : ℝ) * n * RMax D * Rho D ^ 2 /
      (p.epsilon * p.delta) := by
  have m : (1 : ℝ) ≤ D.componentCount := by exact_mod_cast hm
  have n' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have r : (1 : ℝ) ≤ RMax D := by exact_mod_cast D.theorem3RMax_pos hm
  have ρ : 1 ≤ Rho D := lmax_one _
  have hε := p.epsilon_pos
  have hδ := p.delta_pos
  have hE : p.epsilon * p.delta ≤ 1 := (mul_le_mul_of_nonneg_right p.epsilon_le_one hδ.le).trans (by simpa using p.delta_le_one)
  apply (le_div_iff₀ (by positivity)).2
  calc
    _ ≤ 1 := by simpa using hE
    _ ≤ 10000 * (D.componentCount : ℝ) * n * RMax D * Rho D ^ 2 := by
      calc
        (1 : ℝ) = 1 * 1 * 1 * 1 * 1 ^ 2 := by norm_num
        _ ≤ _ := by gcongr; norm_num

-- Common pattern: show the argument of a logarithm is bounded by the
-- positive input product, then use the protected logarithm in the rate.
private theorem runtimeLog_controls {x : ℝ} (D : Decomposition F) (p : ApproxParams)
    (hx : 0 < x) (h : x ≤ 10000 * (D.componentCount : ℝ) * n * RMax D *
      Rho D ^ 2 / (p.epsilon * p.delta)) :
    max 1 (Real.log x) ≤ ttcRuntimeLog D p := by
  have hb := max_le_max (le_rfl : (1 : ℝ) ≤ 1) (Real.log_le_log hx h)
  unfold ttcRuntimeLog
  linarith [le_max_left 0 (Real.log (theorem3OuterRadiusMax D)),
    le_max_left 0 (Real.log (theorem3InverseInradiusMax D))]

/-- Every simple argument needed by the population, cooling, and walk logs
is covered by a single input product. The last inequality covers the CV18
confidence-amplified query logarithm. -/
private theorem commonLogBounds (D : Decomposition F) (p : ApproxParams)
    (hm : 0 < D.componentCount) (hn : 1 ≤ n) :
    let L := ttcRuntimeLog D p
    Real.log (24 / p.delta) ≤ L ∧ Real.log (6 / p.delta) ≤ L ∧
    Real.log D.componentCount ≤ L ∧ Real.log n ≤ L ∧
    max 1 (Real.log (192 / p.epsilon)) ≤ L ∧
    max 1 (Real.log (24 * n / p.epsilon)) ≤ L ∧
    max 1 (Real.log (8 * D.componentCount / p.delta)) ≤ L ∧
    max 1 (Real.log (960 * n * D.componentCount * Rho D ^ 2 /
      (p.epsilon * p.delta))) ≤ L := by
  dsimp only
  have m : (1 : ℝ) ≤ D.componentCount := by exact_mod_cast hm
  have n' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have r : (1 : ℝ) ≤ RMax D := by exact_mod_cast D.theorem3RMax_pos hm
  have ρ : 1 ≤ Rho D := lmax_one _
  have hε := p.epsilon_pos
  have hδ := p.delta_pos
  have hε1 := p.epsilon_le_one
  have hδ1 := p.delta_le_one
  have hden : 0 < p.epsilon * p.delta := mul_pos hε hδ
  have h (c a b q : ℝ) (hc : 0 ≤ c) (hc' : c ≤ 10000) (ha : 0 ≤ a) (ha' : a ≤ D.componentCount)
      (hb : 0 ≤ b) (hb' : b ≤ n) (hq : 0 ≤ q) (hq' : q ≤ Rho D ^ 2) :
      c * a * b * q / (p.epsilon * p.delta) ≤
        10000 * (D.componentCount : ℝ) * n * RMax D * Rho D ^ 2 /
          (p.epsilon * p.delta) := by
    have hh : (1 : ℝ) ≤ RMax D := r
    calc
      _ = c * a * b * 1 * q / (p.epsilon * p.delta) := by ring
      _ ≤ _ := by gcongr
  have hq : (1 : ℝ) ≤ Rho D ^ 2 := one_le_pow₀ ρ
  have h24 := h 24 1 1 1 (by norm_num) (by norm_num) zero_le_one m zero_le_one n' zero_le_one hq
  have h6 := h 6 1 1 1 (by norm_num) (by norm_num) zero_le_one m zero_le_one n' zero_le_one hq
  have hm' := h 1 D.componentCount 1 1 zero_le_one (by norm_num)
    (by positivity) le_rfl zero_le_one n' zero_le_one hq
  have hn' := h 1 1 n 1 zero_le_one (by norm_num)
    zero_le_one m (by positivity) le_rfl zero_le_one hq
  have h192 := h 192 1 1 1 (by norm_num) (by norm_num) zero_le_one m zero_le_one n' zero_le_one hq
  have h24n := h 24 1 n 1 (by norm_num) (by norm_num) zero_le_one m (by positivity)
    le_rfl zero_le_one hq
  have h8m := h 8 D.componentCount 1 1 (by norm_num) (by norm_num) (by positivity)
    le_rfl zero_le_one n' zero_le_one hq
  have h960 := h 960 D.componentCount n (Rho D ^ 2) (by norm_num) (by norm_num)
    (by positivity) le_rfl (by positivity) le_rfl (by positivity) le_rfl
  have lowerE (x : ℝ) (hx : 0 ≤ x) : x / p.delta ≤ x / (p.epsilon * p.delta) :=
    div_le_div_of_nonneg_left hx hden (by nlinarith)
  have lowerD (x : ℝ) (hx : 0 ≤ x) : x / p.epsilon ≤ x / (p.epsilon * p.delta) :=
    div_le_div_of_nonneg_left hx hden (by nlinarith)
  refine ⟨(le_max_right _ _).trans (runtimeLog_controls D p (by positivity)
      ((lowerE 24 (by norm_num)).trans (by simpa using h24))),
    (le_max_right _ _).trans (runtimeLog_controls D p (by positivity)
      ((lowerE 6 (by norm_num)).trans (by simpa using h6))), ?_, ?_,
    runtimeLog_controls D p (by positivity) ((lowerD 192 (by norm_num)).trans (by simpa using h192)),
    runtimeLog_controls D p (by positivity) ((lowerD _ (by positivity)).trans (by simpa using h24n)),
    runtimeLog_controls D p (by positivity) ((lowerE _ (by positivity)).trans (by simpa using h8m)),
    runtimeLog_controls D p (by positivity) (by convert h960 using 1; ring)⟩
  · have hz : 0 < (D.componentCount : ℝ) := by exact_mod_cast hm
    have hden1 : p.epsilon * p.delta ≤ 1 :=
      (mul_le_mul_of_nonneg_right hε1 hδ.le).trans (by simpa using hδ1)
    have hmDiv : (D.componentCount : ℝ) ≤ D.componentCount / (p.epsilon * p.delta) :=
      (le_div_iff₀ hden).2 (by nlinarith [mul_nonneg hz.le (sub_nonneg.mpr hden1)])
    exact (le_max_right _ _).trans (runtimeLog_controls D p hz (hmDiv.trans (by simpa using hm')))
  · have hz : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hden1 : p.epsilon * p.delta ≤ 1 :=
      (mul_le_mul_of_nonneg_right hε1 hδ.le).trans (by simpa using hδ1)
    have hnDiv : (n : ℝ) ≤ n / (p.epsilon * p.delta) :=
      (le_div_iff₀ hden).2 (by nlinarith [mul_nonneg hz.le (sub_nonneg.mpr hden1)])
    exact (le_max_right _ _).trans (runtimeLog_controls D p hz (hnDiv.trans (by simpa using hn')))

private theorem facet_le_max (D : Decomposition F) (i : Fin D.componentCount) :
    (D.component i).presentation.facetCount ≤ RMax D :=
  Finset.le_sup (f := fun j => (D.component j).presentation.facetCount) (Finset.mem_univ i)

private theorem totalFacets_le_mul (D : Decomposition F) :
    D.totalFacets ≤ D.componentCount * RMax D := by
  unfold Decomposition.totalFacets
  calc
    _ ≤ ∑ _ : Fin D.componentCount, RMax D := Finset.sum_le_sum (fun i _ => facet_le_max D i)
    _ = _ := by simp

private theorem max_logb_mul_log (x : ℝ) :
    max 0 (Real.logb 10 x) * Real.log 10 = max 0 (Real.log x) := by
  have h : 0 < Real.log (10 : ℝ) := Real.log_pos (by norm_num)
  rw [max_mul_of_nonneg _ _ h.le, zero_mul, Real.logb, div_mul_cancel₀ _ h.ne']

private theorem walkLog_le (D : Decomposition F) (p : ApproxParams) (hm : 0 < D.componentCount)
    (hn : 1 ≤ n) :
    (GetPrecision D p.precisionEta : ℝ) * Real.log 10 + Real.log 6 + Real.log n +
      max 0 (Real.log (theorem3OuterRadiusMax D)) ≤ 22 * ttcRuntimeLog D p := by
  let X := 10000 * (D.componentCount : ℝ) * n * RMax D * Rho D ^ 2 / (p.epsilon * p.delta)
  let L := ttcRuntimeLog D p
  have hX : 1 ≤ X := inputProduct_le D p hm hn
  have heps := p.epsilon_pos
  have hdelta := p.delta_pos
  have hm1 : (1 : ℝ) ≤ D.componentCount := by exact_mod_cast hm
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr1 : (1 : ℝ) ≤ RMax D := by exact_mod_cast D.theorem3RMax_pos hm
  have hρ : (1 : ℝ) ≤ Rho D ^ 2 := one_le_pow₀ (lmax_one _)
  have hden : 0 < p.epsilon * p.delta := mul_pos heps hdelta
  have heps' : p.epsilon * p.delta ≤ p.epsilon := by
    simpa using mul_le_mul_of_nonneg_left p.delta_le_one heps.le
  have num_le (c d' r' : ℝ) (hc : 0 ≤ c) (hc' : c ≤ 10000)
      (hd : 0 ≤ d') (hd' : d' ≤ n) (hr : 0 ≤ r') (hr' : r' ≤ RMax D) :
      c * D.componentCount * d' * r' / (p.epsilon * p.delta) ≤ X := by
    dsimp only [X]
    calc
      _ = c * D.componentCount * d' * r' * 1 / (p.epsilon * p.delta) := by ring
      _ ≤ _ := by gcongr
  have hmul (y : ℝ) (hy : 0 ≤ y) : y / p.epsilon ≤ y / (p.epsilon * p.delta) :=
    div_le_div_of_nonneg_left hy hden heps'
  have hA : 64 * (D.componentCount : ℝ) * n / p.precisionEta ≤ X := by
    unfold ApproxParams.precisionEta
    calc
      _ = 6144 * (D.componentCount : ℝ) * n * 1 / p.epsilon := by ring
      _ ≤ _ := hmul _ (by positivity)
      _ ≤ _ := num_le 6144 n 1 (by norm_num) (by norm_num) (by positivity) le_rfl zero_le_one hr1
  have ht : (D.totalFacets : ℝ) ≤ D.componentCount * RMax D := by exact_mod_cast totalFacets_le_mul D
  have hB : 4 * (D.totalFacets : ℝ) / p.precisionEta ≤ X := by
    unfold ApproxParams.precisionEta
    calc
      _ = 384 * (D.totalFacets : ℝ) / p.epsilon := by ring
      _ ≤ 384 * (D.componentCount : ℝ) * 1 * RMax D / p.epsilon := by
        simp only [mul_one]
        apply div_le_div_of_nonneg_right _ heps.le
        linarith only [ht]
      _ ≤ _ := hmul _ (by positivity)
      _ ≤ _ := num_le 384 1 (RMax D) (by norm_num) (by norm_num) zero_le_one hn1 (by positivity) le_rfl
  have ht0 : 0 < D.totalFacets := ((D.component ⟨0, hm⟩).facets_pos).trans_le
    (D.facetCount_le_totalFacets ⟨0, hm⟩)
  have harg : 0 < 4 * (D.totalFacets : ℝ) / p.precisionEta := by
    have hh : (0 : ℝ) < D.totalFacets := by exact_mod_cast ht0
    positivity [show 0 < p.precisionEta from div_pos heps (by norm_num)]
  have hB' := Real.log_le_sub_one_of_pos harg
  have hs : Real.sqrt (Real.log (4 * (D.totalFacets : ℝ) / p.precisionEta)) ≤ X := by
    have hs₁ : Real.log (4 * (D.totalFacets : ℝ) / p.precisionEta) ≤ X ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hX) (show 0 ≤ X by linarith)]
    simpa only [Real.sqrt_sq (show 0 ≤ X by linarith)] using Real.sqrt_le_sqrt hs₁
  have hrad : latticeRadiusRequirement D p.precisionEta ≤ X ^ 2 := by
    unfold latticeRadiusRequirement
    rw [pow_two]
    gcongr
  have hL : 1 ≤ L := runtimeLog_one_le D p
  have hXL : Real.log X ≤ L := (le_max_right _ _).trans
    (runtimeLog_controls D p (show 0 < X by linarith) le_rfl)
  have hradL : max 0 (Real.log (latticeRadiusRequirement D p.precisionEta)) ≤ 2 * L := by
    apply max_le (by linarith)
    by_cases hp : 0 < latticeRadiusRequirement D p.precisionEta
    · have h := Real.log_le_log hp hrad
      rw [Real.log_pow] at h
      norm_num at h
      linarith
    · rw [show latticeRadiusRequirement D p.precisionEta = 0 from
        le_antisymm (not_lt.mp hp) (latticeRadiusRequirement_precisionEta_nonneg D p), Real.log_zero]
      linarith
  have hInv : max 0 (Real.log (theorem3InverseInradiusMax D)) ≤ L := by
    unfold L ttcRuntimeLog
    linarith [lmax_one (Real.log X), le_max_left 0 (Real.log (theorem3OuterRadiusMax D))]
  have hOut : max 0 (Real.log (theorem3OuterRadiusMax D)) ≤ L := by
    unfold L ttcRuntimeLog
    linarith [lmax_one (Real.log X), le_max_left 0 (Real.log (theorem3InverseInradiusMax D))]
  have h10 : (0 : ℝ) ≤ Real.log 10 := Real.log_nonneg (by norm_num)
  have hb := mul_le_mul_of_nonneg_right (getPrecision_le_theorem3PrecisionBound D p) h10
  unfold theorem3PrecisionBound at hb
  simp only [add_mul, one_mul, max_logb_mul_log] at hb
  have h6 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)
  have h10' := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)
  have hlogs := (commonLogBounds D p hm hn).2.2.2.1
  change Real.log (n : ℝ) ≤ L at hlogs
  linarith

private theorem walkLength_le (hn : 21 ≤ n) (D : Decomposition F) (p : ApproxParams)
    (i : Fin D.componentCount) :
    (arithmeticWalkLength (D.component i) (GetPrecision D p.precisionEta) p.epsilon : ℝ) ≤
      (2 : ℝ) ^ 80 * (n : ℝ) ^ 4 * Rho D ^ 2 * ttcRuntimeLog D p := by
  let b := GetPrecision D p.precisionEta
  let L := ttcRuntimeLog D p
  let B := (b : ℝ) * Real.log 10 + Real.log 6 + Real.log n +
    max 0 (Real.log (theorem3OuterRadiusMax D))
  have hy := walkLog_le D p (Nat.zero_lt_of_lt i.isLt) (by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hρ : 1 ≤ Rho D := lmax_one _
  have hL : 1 ≤ L := runtimeLog_one_le D p
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    have h10 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 10)
    have h6 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 6)
    have hn0 := Real.log_nonneg hn1
    positivity
  have hG := D.normalizedHitAndRunSteps_le_explicitEnvelope hn b p
    (getPrecisionChoice D p).adequate i
  change arithmeticWalkLength (D.component i) b p.epsilon ≤ _ at hG
  have hW : arithmeticWalkLength (D.component i) b p.epsilon ≤
      Nat.ceil ((2 : ℝ) ^ 68 * 5 * (n : ℝ) ^ 4 * Rho D ^ 2 * B) := by
    refine hG.trans_eq (congrArg Nat.ceil ?_)
    unfold theorem3SamplerLogEnvelope B
    ring
  have hceil := Nat.ceil_lt_add_one (show
      0 ≤ (2 : ℝ) ^ 68 * 5 * (n : ℝ) ^ 4 * Rho D ^ 2 * B by positivity)
  have hW' : (arithmeticWalkLength (D.component i) b p.epsilon : ℝ) ≤
      (Nat.ceil ((2 : ℝ) ^ 68 * 5 * (n : ℝ) ^ 4 * Rho D ^ 2 * B) : ℝ) := by exact_mod_cast hW
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 4 * Rho D ^ 2 * L := by
    calc
      (1 : ℝ) = 1 ^ 4 * 1 ^ 2 * 1 := by norm_num
      _ ≤ _ := by gcongr
  have hmain : (2 : ℝ) ^ 68 * 5 * (n : ℝ) ^ 4 * Rho D ^ 2 * B ≤
      (2 : ℝ) ^ 68 * 110 * ((n : ℝ) ^ 4 * Rho D ^ 2 * L) := by
    calc
      _ ≤ (2 : ℝ) ^ 68 * 5 * (n : ℝ) ^ 4 * Rho D ^ 2 * (22 * L) := by
        gcongr
      _ = _ := by ring
  change (arithmeticWalkLength (D.component i) b p.epsilon : ℝ) ≤ _
  linarith

private theorem roundness_le (D : Decomposition F) (i : Fin D.componentCount) :
    max 1 (arithmeticRoundness (D.component i)) ≤ 5 * Rho D ^ 2 := by
  have h1 : (1 : ℝ) ≤ Rho D ^ 2 := one_le_pow₀ (lmax_one _)
  have h := D.communityCV18_roundness_le_rho i
  change arithmeticRoundness (D.component i) ≤ _ at h
  exact max_le (by linarith) (by linarith)

private theorem population_le (D : Decomposition F) (p : ApproxParams)
    (hm : 0 < D.componentCount) (hn : 1 ≤ n) :
    arithmeticPopulationNumerator p D.componentCount ≤ 4000 * ttcRuntimeLog D p := by
  obtain ⟨h24, h6, hM, -⟩ := commonLogBounds D p hm hn
  unfold arithmeticPopulationNumerator
  linarith [runtimeLog_one_le D p]

private theorem repetitions_le (D : Decomposition F) (p : ApproxParams)
    (hm : 0 < D.componentCount) (hn : 1 ≤ n) :
    (arithmeticCV18Repetitions D.componentCount p : ℝ) ≤ 9 * ttcRuntimeLog D p := by
  have h := (commonLogBounds D p hm hn).2.2.2.2.2.2.1
  have heq : 1 / (p.delta / (8 * (D.componentCount : ℝ))) =
      8 * D.componentCount / p.delta := by
    rw [div_div_eq_mul_div]
    ring
  unfold arithmeticCV18Repetitions
  rw [heq]
  have hc := Nat.ceil_lt_add_one
    (show 0 ≤ 8 * max 1 (Real.log (8 * D.componentCount / p.delta)) by positivity)
  linarith [runtimeLog_one_le D p]

private theorem schedule_le (D : Decomposition F) (p : ApproxParams) (hn : 1 ≤ n)
    (i : Fin D.componentCount) :
    (arithmeticScheduleCap n p (arithmeticRoundness (D.component i)) : ℝ) ≤
      20000 * (n : ℝ) * Rho D ^ 2 * ttcRuntimeLog D p ^ 2 := by
  let L := ttcRuntimeLog D p
  let U := (n : ℝ) * Rho D ^ 2 * L ^ 2
  let roundness := arithmeticRoundness (D.component i)
  have hL : 1 ≤ L := runtimeLog_one_le D p
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have hL2' : L ≤ L ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hL) (show 0 ≤ L by linarith)]
  have hR : (1 : ℝ) ≤ Rho D ^ 2 := one_le_pow₀ (lmax_one _)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hU : (n : ℝ) ≤ U := by
    calc
      (n : ℝ) = n * 1 * 1 := by ring
      _ ≤ _ := by dsimp only [U]; gcongr
  have hU1 : 1 ≤ U := hn1.trans hU
  have hm := Nat.zero_lt_of_lt i.isLt
  obtain ⟨-, -, -, -, hLa, hLb, -⟩ := commonLogBounds D p hm hn
  have hC : roundness ≤ 5 * Rho D ^ 2 := (le_max_right _ _).trans (roundness_le D i)
  let a := max 1 (Real.log (8 / (p.epsilon / 24)))
  let b := max 1 (Real.log ((n : ℝ) / (p.epsilon / 24)))
  have ha : a ≤ L := by
    dsimp only [a]
    rw [show 8 / (p.epsilon / 24) = 192 / p.epsilon by ring]
    exact hLa
  have hb : b ≤ L := by
    dsimp only [b]
    rw [show (n : ℝ) / (p.epsilon / 24) = 24 * n / p.epsilon by ring]
    exact hLb
  have ha0 : 0 ≤ a := zero_le_one.trans (lmax_one _)
  have hb0 : 0 ≤ b := zero_le_one.trans (lmax_one _)
  let T := max 1 (max (n : ℝ) (1024 * roundness * n * a ^ 2))
  have hTnum : 1024 * roundness * n * a ^ 2 ≤ 5120 * U := by
    calc
      _ ≤ 1024 * (5 * Rho D ^ 2) * n * L ^ 2 := by gcongr
      _ = _ := by dsimp only [U]; ring
  have hT : T ≤ 5120 * U := by
    unfold T
    exact max_le (by linarith) (max_le (by linarith) hTnum)
  have hslow : 2 * (n : ℝ) * (6 + b) ≤ 14 * U := by
    have hnU : (n : ℝ) * L ≤ U := by
      calc (n : ℝ) * L = n * 1 * L := by ring
           _ ≤ _ := by dsimp only [U]; gcongr
    have h := mul_le_mul_of_nonneg_left (show 6 + b ≤ 7 * L by linarith)
      (show 0 ≤ 2 * (n : ℝ) by positivity)
    linarith
  have hsc := Nat.ceil_lt_add_one (show 0 ≤ 2 * (n : ℝ) * (6 + b) by positivity)
  have hfc := Nat.ceil_lt_add_one (show 0 ≤ 3 * T by
    have hh : 1 ≤ T := lmax_one _
    linarith)
  change ((Nat.ceil (2 * (n : ℝ) * (6 + b)) + Nat.ceil (3 * T) + 1 : ℕ) : ℝ) ≤ _
  push_cast
  calc
    _ ≤ 20000 * U := by linarith
    _ = _ := by dsimp only [U, L]; ring

private theorem queries_le (D : Decomposition F) (p : ApproxParams) (hn : 1 ≤ n)
    (i : Fin D.componentCount) :
    arithmeticQueryNumerator n D.componentCount p (arithmeticRoundness (D.component i)) ≤
      (10 : ℝ) ^ 50 * (n : ℝ) ^ 3 * Rho D ^ 2 * ttcRuntimeLog D p ^ 10 := by
  let a := max 1 (arithmeticRoundness (D.component i))
  have ha : a ≤ 5 * Rho D ^ 2 := roundness_le D i
  have ha1 : 1 ≤ a := lmax_one _
  have hε := p.epsilon_pos
  have hδ := p.delta_pos
  have hm := Nat.zero_lt_of_lt i.isLt
  have hm0 : (0 : ℝ) < D.componentCount := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let X := (n : ℝ) * a / ((p.epsilon / 24) * (p.delta / (8 * D.componentCount)))
  have hX : X ≤ 960 * n * D.componentCount * Rho D ^ 2 / (p.epsilon * p.delta) := by
    dsimp only [X]
    calc
      _ ≤ (n : ℝ) * (5 * Rho D ^ 2) / ((p.epsilon / 24) * (p.delta / (8 * D.componentCount))) := by
        gcongr
      _ = _ := by field_simp [hε.ne', hδ.ne', hm0.ne']; ring
  have hL : max 1 (Real.log X) ≤ ttcRuntimeLog D p :=
    (max_le_max (le_rfl : (1 : ℝ) ≤ 1) (Real.log_le_log (by dsimp only [X]; positivity) hX)).trans
      (commonLogBounds D p hm hn).2.2.2.2.2.2.2
  unfold arithmeticQueryNumerator
  change 576 * (585 * (10 : ℝ) ^ 30) * (a * (n : ℝ) ^ 3) *
      (14113440000 * max 1 (Real.log X) ^ 10) ≤ _
  calc
    _ ≤ 576 * (585 * (10 : ℝ) ^ 30) * ((5 * Rho D ^ 2) * (n : ℝ) ^ 3) *
        (14113440000 * ttcRuntimeLog D p ^ 10) := by gcongr
    _ ≤ _ := by
      have h0 : 0 ≤ (n : ℝ) ^ 3 * Rho D ^ 2 * ttcRuntimeLog D p ^ 10 := by positivity
      nlinarith

/-- Combining the numerical allowances costs one power of the dimension
per facet per walk step. The query and population allowances are added. -/
private theorem scalar_component_bound (n r ρ L ε T S J P Q : ℝ)
    (hn : 1 ≤ n) (hr : 1 ≤ r) (hρ : 1 ≤ ρ) (hL : 1 ≤ L)
    (he : 0 < ε) (he1 : ε ≤ 1)
    (hT0 : 0 ≤ T) (hS0 : 0 ≤ S) (hJ0 : 0 ≤ J) (hP0 : 0 ≤ P) (hQ0 : 0 ≤ Q)
    (hT : T ≤ (2 : ℝ) ^ 80 * n ^ 4 * ρ ^ 2 * L)
    (hS : S ≤ 20000 * n * ρ ^ 2 * L ^ 2)
    (hJ : J ≤ 9 * L) (hP : P ≤ 4000 * L)
    (hQ : Q ≤ (10 : ℝ) ^ 50 * n ^ 3 * ρ ^ 2 * L ^ 10) :
    let perTry := 13 * n + 5 + 2 * n * r + T * (6 * n + 8 + r * (4 * n + 5))
    let base := r * (2 * n + 2) + 20 + (200 + 12 * S) + r +
      (100 + n + r * (4 * n + 10)) + 76 +
      J * (S * (2 * n + 83) + (7 * n + 87) + (4 * J + 5))
    r * (n + 1) + n + 4 +
      (base + ((n + 2 * n * r + 31 + 2 * perTry) * P + (12 * n + 31 + 2 * n * r) * Q) / ε ^ 2) +
      110 ≤
      (10 : ℝ) ^ 54 * (n ^ 5 * ρ ^ 2 * r * L ^ 10) / ε ^ 2 := by
  intro perTry base
  let X := n ^ 5 * ρ ^ 2 * r * L ^ 10
  let U := n * ρ ^ 2 * L ^ 2
  have hn0 : 0 ≤ n := by linarith
  have hr0 : 0 ≤ r := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hρ0 : 0 ≤ ρ := by linarith
  have hρ2 : 1 ≤ ρ ^ 2 := one_le_pow₀ hρ
  have hX0 : 0 ≤ X := by dsimp [X]; positivity
  have hX1 : 1 ≤ X := by
    calc (1 : ℝ) = 1 ^ 5 * 1 ^ 2 * 1 * 1 ^ 10 := by norm_num
         _ ≤ _ := by dsimp only [X]; gcongr
  have monoBlock (a b : ℕ) (ha : a ≤ 5) (hb : b ≤ 10) :
      n ^ a * ρ ^ 2 * r * L ^ b ≤ X := by
    dsimp only [X]
    gcongr
  have hn_nr : n ≤ n * r := le_mul_of_one_le_right hn0 hr
  have hr_nr : r ≤ n * r := le_mul_of_one_le_left hr0 hn
  have hnr1 : 1 ≤ n * r := hn.trans hn_nr
  have hnr : n * r ≤ X := by
    calc
      _ ≤ n * ρ ^ 2 * r := by
        have hh := mul_le_mul_of_nonneg_left hρ2 hn0
        have := mul_le_mul_of_nonneg_right hh hr0
        simpa using this
      _ = n ^ 1 * ρ ^ 2 * r * L ^ 0 := by simp
      _ ≤ _ := monoBlock 1 0 (by norm_num) (by norm_num)
  have hU0 : 0 ≤ U := by dsimp only [U]; positivity
  have hU : U ≤ X := by
    calc
      U = n ^ 1 * ρ ^ 2 * 1 * L ^ 2 := by simp [U]
      _ ≤ n ^ 1 * ρ ^ 2 * r * L ^ 2 := by gcongr
      _ ≤ _ := monoBlock 1 2 (by norm_num) (by norm_num)
  have hL_U : L ≤ U := by
    have hL2 : L ≤ L ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hL) hL0]
    calc
      L ≤ L ^ 2 := hL2
      _ = 1 * 1 * L ^ 2 := by ring
      _ ≤ _ := by dsimp only [U]; gcongr
  have hU1 : 1 ≤ U := hL.trans hL_U
  have hnU : n ≤ n * U := le_mul_of_one_le_right hn0 hU1
  have hL_nU : L ≤ n * U := hL_U.trans (le_mul_of_one_le_left hU0 hn)
  have hJint : S * (2 * n + 83) + (7 * n + 87) + (4 * J + 5) ≤ 1800000 * n * U := by
    have hA : S * (2 * n + 83) ≤ (20000 * U) * (85 * n) := by
      apply mul_le_mul _ (by linarith) (by positivity) (by positivity)
      calc S ≤ _ := hS
           _ = _ := by dsimp only [U]; ring
    linarith [hA, hnU, hL_nU, hJ, hL]
  have hMed : J * (S * (2 * n + 83) + (7 * n + 87) + (4 * J + 5)) ≤ 16200000 * X := by
    calc
      _ ≤ (9 * L) * (1800000 * n * U) := by gcongr
      _ = 16200000 * (n ^ 2 * ρ ^ 2 * 1 * L ^ 3) := by dsimp only [U]; ring
      _ ≤ 16200000 * (n ^ 2 * ρ ^ 2 * r * L ^ 3) := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left (monoBlock 2 3 (by norm_num) (by norm_num)) (by norm_num)
  have hfixed : (r * (n + 1) + n + 4) + base + 110 ≤ (10 : ℝ) ^ 9 * X := by
    dsimp only [base]
    have hs' : S ≤ 20000 * U := hS.trans_eq (by dsimp only [U]; ring)
    linarith only [hMed, hnr, hn_nr, hr_nr, hX1, hs', hU]
  have hstep : 6 * n + 8 + r * (4 * n + 5) ≤ 23 * (n * r) := by
    nlinarith only [hn_nr, hr_nr, hnr1]
  have hcoef : n + 2 * n * r + 31 + 2 * perTry ≤ 80 * (n * r) * (1 + T) := by
    dsimp only [perTry]
    have hh := mul_le_mul_of_nonneg_left hstep hT0
    nlinarith only [hh, hn_nr, hnr1, mul_nonneg (mul_nonneg hn0 hr0) hT0]
  have hwalk1 : 1 ≤ n ^ 4 * ρ ^ 2 * L := by
    calc (1 : ℝ) = 1 ^ 4 * 1 ^ 2 * 1 := by norm_num
         _ ≤ _ := by gcongr
  have hT' : 1 + T ≤ (2 : ℝ) ^ 81 * (n ^ 4 * ρ ^ 2 * L) := by linarith
  have hpop : (n + 2 * n * r + 31 + 2 * perTry) * P ≤ (10 : ℝ) ^ 33 * X := by
    calc
      _ ≤ (80 * (n * r) * (1 + T)) * (4000 * L) :=
        mul_le_mul hcoef hP hP0 (by positivity)
      _ ≤ (80 * (n * r) * ((2 : ℝ) ^ 81 * (n ^ 4 * ρ ^ 2 * L))) * (4000 * L) := by
        gcongr
      _ = (80 * (2 : ℝ) ^ 81 * 4000) * (n ^ 5 * ρ ^ 2 * r * L ^ 2) := by ring
      _ ≤ (80 * (2 : ℝ) ^ 81 * 4000) * X :=
        mul_le_mul_of_nonneg_left (monoBlock 5 2 le_rfl (by norm_num)) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) hX0
  have hcv : (12 * n + 31 + 2 * n * r) * Q ≤ (10 : ℝ) ^ 52 * X := by
    calc
      _ ≤ (45 * (n * r)) * ((10 : ℝ) ^ 50 * n ^ 3 * ρ ^ 2 * L ^ 10) :=
        mul_le_mul (by linarith only [hn_nr, hnr1]) hQ hQ0 (by positivity)
      _ = (45 * (10 : ℝ) ^ 50) * (n ^ 4 * ρ ^ 2 * r * L ^ 10) := by ring
      _ ≤ (45 * (10 : ℝ) ^ 50) * X :=
        mul_le_mul_of_nonneg_left (monoBlock 4 10 (by norm_num) le_rfl) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) hX0
  have he2 : 0 < ε ^ 2 := sq_pos_of_pos he
  have he2' : ε ^ 2 ≤ 1 := by nlinarith [mul_nonneg he.le (sub_nonneg.mpr he1)]
  have hfix' : (10 : ℝ) ^ 9 * X ≤ (10 : ℝ) ^ 9 * X / ε ^ 2 :=
    (le_div_iff₀ he2).2 (by
      calc _ ≤ ((10 : ℝ) ^ 9 * X) * 1 := mul_le_mul_of_nonneg_left he2' (by positivity)
           _ = _ := mul_one _)
  calc
    _ = ((r * (n + 1) + n + 4) + base + 110) +
        ((n + 2 * n * r + 31 + 2 * perTry) * P + (12 * n + 31 + 2 * n * r) * Q) / ε ^ 2 := by ring
    _ ≤ (10 : ℝ) ^ 9 * X / ε ^ 2 + (((10 : ℝ) ^ 33 * X) + (10 : ℝ) ^ 52 * X) / ε ^ 2 :=
      add_le_add (hfixed.trans hfix') (div_le_div_of_nonneg_right (add_le_add hpop hcv) he2.le)
    _ = (((10 : ℝ) ^ 9 + (10 : ℝ) ^ 33 + (10 : ℝ) ^ 52) * X) / ε ^ 2 := by ring
    _ ≤ (10 : ℝ) ^ 54 * X / ε ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hX0) he2.le

private theorem component_le_rate (hn : 21 ≤ n) (D : Decomposition F) (p : ApproxParams)
    (i : Fin D.componentCount) :
    let r := (D.component i).presentation.facetCount
    (((r * (n + 1) + n + 4 : ℕ) : ℝ) +
      arithmeticComponentBound D.componentCount (GetPrecision D p.precisionEta) p (D.component i)) +
      110 ≤ (10 : ℝ) ^ 54 *
        ((n : ℝ) ^ 5 * Rho D ^ 2 * RMax D * ttcRuntimeLog D p ^ 10) / p.epsilon ^ 2 := by
  intro r
  let m := D.componentCount
  let C := D.component i
  let L := ttcRuntimeLog D p
  let ρ := Rho D
  let T := arithmeticWalkLength C (GetPrecision D p.precisionEta) p.epsilon
  let S := arithmeticScheduleCap n p (arithmeticRoundness C)
  let J := arithmeticCV18Repetitions m p
  let P := arithmeticPopulationNumerator p m
  let Q := arithmeticQueryNumerator n m p (arithmeticRoundness C)
  have hm : 0 < m := Nat.zero_lt_of_lt i.isLt
  have hn' : 1 ≤ n := by omega
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn'
  have hr : (1 : ℝ) ≤ r := by exact_mod_cast C.facets_pos
  have hρ : 1 ≤ ρ := lmax_one _
  have hL : 1 ≤ L := runtimeLog_one_le D p
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hδ := p.delta_pos
  have hδ1 := p.delta_le_one
  have hP0 : 0 ≤ P := by
    dsimp only [P, arithmeticPopulationNumerator]
    have h1 := Real.log_nonneg ((one_le_div hδ).2 (by linarith : p.delta ≤ 24))
    have h2 := Real.log_nonneg ((one_le_div hδ).2 (by linarith : p.delta ≤ 6))
    have h3 := Real.log_nonneg hm1
    positivity
  have hQ0 : 0 ≤ Q := by unfold Q arithmeticQueryNumerator; positivity
  have h := scalar_component_bound n r ρ L p.epsilon T S J P Q hn1 hr hρ hL p.epsilon_pos
    p.epsilon_le_one (by positivity) (by positivity) (by positivity) hP0 hQ0
    (walkLength_le hn D p i) (schedule_le D p hn' i)
    (repetitions_le D p hm hn') (population_le D p hm hn') (queries_le D p hn' i)
  have h' : ((r * (n + 1) + n + 4 : ℕ) : ℝ) +
      arithmeticComponentBound m (GetPrecision D p.precisionEta) p C + 110 ≤
        (10 : ℝ) ^ 54 * ((n : ℝ) ^ 5 * ρ ^ 2 * r * L ^ 10) / p.epsilon ^ 2 := by
    simpa only [arithmeticComponentBound, C, m, T, S, J, P, Q, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one] using h
  refine h'.trans ?_
  have hrmax : (r : ℝ) ≤ RMax D := by exact_mod_cast facet_le_max D i
  gcongr

/-- The explicit arithmetic envelope is at most an absolute constant times the
public rate. This only bounds the allowance and does not change the program. -/
theorem ttcArithmeticBound_le_runtimeRate (hn : 21 ≤ n) (D : Decomposition F) (p : ApproxParams) :
    ttcArithmeticBound D p ≤ (10 : ℝ) ^ 54 * ttcRuntimeRate D p := by
  by_cases h : D.componentCount = 0
  · simp only [ttcArithmeticBound, ttcRuntimeRate, h, ite_true, mul_one]
    norm_num
  let m := D.componentCount
  let b := GetPrecision D p.precisionEta
  let A := fun i : Fin m =>
    ((((D.component i).presentation.facetCount * (n + 1) + n + 4 : ℕ) : ℝ) +
      arithmeticComponentBound m b p (D.component i))
  let B := (10 : ℝ) ^ 54 * ((n : ℝ) ^ 5 * Rho D ^ 2 * RMax D * ttcRuntimeLog D p ^ 10) /
    p.epsilon ^ 2
  have hm : (1 : ℝ) ≤ m := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h : 1 ≤ D.componentCount)
  simp only [ttcArithmeticBound, ttcRuntimeRate, ite_eq_right h]
  change 100 + 10 * (m : ℝ) + (∑ i, A i) ≤ _
  calc
    _ ≤ ∑ i : Fin m, (A i + 110) := by
      conv_rhs => rw [Finset.sum_add_distrib]
      try simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      linarith
    _ ≤ ∑ _ : Fin m, B := Finset.sum_le_sum (fun i _ => component_le_rate hn D p i)
    _ = _ := by simp [Finset.sum_const, Fintype.card_fin, B, m, nsmul_eq_mul]; ring

theorem sealed_expectedOperations_le_runtimeRate (hn : 21 ≤ n) (F : LRAFormula n k)
    (hb : Bornology.IsBounded (solutionSet F)) (p : ApproxParams)
    (prep : TTCPreprocessor n k) :
    SealedRun.expectedOperations F hb p prep ≤
      ENNReal.ofReal ((10 : ℝ) ^ 54 * ttcRuntimeRate (prep.run F hb) p) :=
  (sealed_expectedOperations_le_arithmeticBound hn F hb p prep).trans
    (ENNReal.ofReal_le_ofReal (ttcArithmeticBound_le_runtimeRate hn (prep.run F hb) p))

end Tape

end ttc
