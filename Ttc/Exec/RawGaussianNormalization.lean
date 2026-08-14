/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.RawGaussianMembershipKernel

/-!
# Normalizing the traced raw Gaussian proposal

This file proves the measure-algebra identity which identifies the operational raw proposal
kernel with `properProposalGaussianAux`.
-/

namespace Ttc.RawGaussianMembership

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains
open Ttc.MembershipQuery
open scoped ENNReal Classical

variable {n : Nat}

private theorem inv_volume_ball_mul_volume_diff
    {K : Set (State n)} (hK : MeasurableSet K) (delta : Real) (hdelta : 0 < delta)
    (x : State n) :
    (volume (ball x delta))⁻¹ * volume (ball x delta \ K) = 1 - ell K delta x := by
  have hV0 : volume (ball x delta) ≠ 0 :=
    (Metric.measure_ball_pos volume x hdelta).ne'
  have hVtop : volume (ball x delta) ≠ ⊤ := measure_ball_lt_top.ne
  have hWtop : volume (ball x delta ∩ K) ≠ ⊤ :=
    ne_top_of_le_ne_top hVtop (measure_mono inter_subset_left)
  have hdiff : ball x delta \ K = ball x delta \ (ball x delta ∩ K) := by
    ext y
    simp only [mem_diff, mem_ball, mem_inter_iff]
    tauto
  rw [hdiff, measure_diff (s₁ := ball x delta) (s₂ := ball x delta ∩ K)
      inter_subset_left (measurableSet_ball.inter hK).nullMeasurableSet hWtop,
    ENNReal.mul_sub (fun _ _ => ENNReal.inv_ne_top.2 hV0),
    ENNReal.inv_mul_cancel hV0 hVtop, ell_apply, ENNReal.div_eq_inv_mul]

private theorem normalized_proper_rejection
    {K : Set (State n)} (_hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (x : State n) :
    (volume (ball x delta))⁻¹ *
        (∫⁻ y in K ∩ ball x delta, 1 - metropolisAccept s x y) =
      ell K delta x * (1 - speedyMetropolisMove K delta s x) := by
  have hV0 : volume (ball x delta) ≠ 0 :=
    (Metric.measure_ball_pos volume x hdelta).ne'
  have hVtop : volume (ball x delta) ≠ ⊤ := measure_ball_lt_top.ne
  have hWtop : volume (K ∩ ball x delta) ≠ ⊤ :=
    ne_top_of_le_ne_top hVtop (measure_mono inter_subset_right)
  have hacc : Measurable (fun y : State n => metropolisAccept s x y) :=
    ((continuous_metropolisAccept (n := n) s).comp
      (continuous_const.prodMk continuous_id)).measurable
  have haccEq : (∫⁻ y in K ∩ ball x delta, metropolisAccept s x y) =
      ∫⁻ y in K, metropolisDensity s delta x y := by
    change (∫⁻ y in K ∩ ball x delta, metropolisAccept s x y) =
      ∫⁻ y in K, (ball x delta).indicator (metropolisAccept s x) y
    rw [lintegral_indicator measurableSet_ball,
      Measure.restrict_restrict measurableSet_ball]
    rw [inter_comm]
  by_cases hW0 : volume (K ∩ ball x delta) = 0
  · have hell0 : ell K delta x = 0 := by
      rw [ell_apply, inter_comm, hW0, ENNReal.div_eq_inv_mul, mul_zero]
    rw [setLIntegral_measure_zero _ _ hW0, hell0, zero_mul, mul_zero]
  have haccIntTop : (∫⁻ y in K ∩ ball x delta, metropolisAccept s x y) ≠ ⊤ := by
    rw [haccEq]
    apply ne_top_of_le_ne_top hVtop
    exact (lintegral_metropolisDensity_le K delta s x).trans (measure_mono inter_subset_left)
  have hsub : (∫⁻ y in K ∩ ball x delta, 1 - metropolisAccept s x y) =
      volume (K ∩ ball x delta) -
        (∫⁻ y in K ∩ ball x delta, metropolisAccept s x y) := by
    rw [lintegral_sub hacc haccIntTop]
    · rw [setLIntegral_one]
    · filter_upwards with (y : State n)
      exact metropolisAccept_le_one s x y
  rw [hsub]
  rw [ENNReal.mul_sub (fun _ _ => ENNReal.inv_ne_top.2 hV0)]
  rw [haccEq]
  rw [ell_apply K delta x, ENNReal.div_eq_inv_mul]
  rw [speedyMetropolisMove_apply K delta s x, ENNReal.div_eq_inv_mul]
  rw [ENNReal.mul_sub
    (a := (volume (ball x delta))⁻¹ * volume (ball x delta ∩ K))
    (b := 1)
    (c := (volume (ball x delta ∩ K))⁻¹ *
      (∫⁻ y in K, metropolisDensity s delta x y))
    (fun _ _ => ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hV0)
      (ne_top_of_le_ne_top hVtop (measure_mono inter_subset_left)))]
  rw [mul_one, mul_assoc,
    ← mul_assoc (volume (ball x delta ∩ K)),
    ENNReal.mul_inv_cancel (by simpa only [inter_comm] using hW0)
      (ne_top_of_le_ne_top hVtop (measure_mono inter_subset_left)), one_mul,
    inter_comm]

theorem rawNormalizationIdentity
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta) :
    RawNormalizationIdentity hK delta s := by
  intro x t ht
  rw [Arlib.uniformOn_def, lintegral_smul_measure, smul_eq_mul,
    properProposalGaussianAux_apply_set hK delta s x ht,
    speedyMetropolisGaussian_apply_set hK delta s x
      ((by fun_prop : Measurable (fun y : State n => (true, y))) ht)]
  have hacc : Measurable (fun y : State n => metropolisAccept s x y) :=
    ((continuous_metropolisAccept (n := n) s).comp
      (continuous_const.prodMk continuous_id)).measurable
  have htrueInd : Measurable (fun y : State n => t.indicator 1 (true, y)) :=
    ((measurable_const : Measurable (1 : Bool × State n → ENNReal)).indicator ht).comp
      (measurable_const.prodMk measurable_id)
  have hmove : Measurable (fun y : State n =>
      metropolisAccept s x y * t.indicator 1 (true, y)) := hacc.mul htrueInd
  change (volume (ball x delta))⁻¹ *
      (∫⁻ y, K.piecewise
        (fun y => metropolisAccept s x y * t.indicator 1 (true, y) +
          (1 - metropolisAccept s x y) * t.indicator 1 (true, x))
        (fun _y => t.indicator 1 (false, x)) y
        ∂(volume.restrict (ball x delta))) = _
  rw [lintegral_piecewise hK, lintegral_add_left hmove]
  have hmoveEq :
      (∫⁻ y in K, metropolisAccept s x y * t.indicator 1 (true, y)
          ∂(volume.restrict (ball x delta))) =
        ∫⁻ y in (fun y : State n => (true, y)) ⁻¹' t ∩ K,
          metropolisDensity s delta x y := by
    rw [Measure.restrict_restrict hK]
    change (∫⁻ y in K ∩ ball x delta,
        metropolisAccept s x y * t.indicator 1 (true, y)) =
      ∫⁻ y in (fun y : State n => (true, y)) ⁻¹' t ∩ K,
        (ball x delta).indicator (metropolisAccept s x) y
    rw [lintegral_indicator measurableSet_ball,
      Measure.restrict_restrict measurableSet_ball]
    have hpre : MeasurableSet ((fun y : State n => (true, y)) ⁻¹' t) :=
      ht.preimage (measurable_const.prodMk measurable_id)
    calc
      (∫⁻ y in K ∩ ball x delta,
          metropolisAccept s x y * t.indicator 1 (true, y)) =
          ∫⁻ y in K ∩ ball x delta,
            ((fun y : State n => (true, y)) ⁻¹' t).indicator
              (metropolisAccept s x) y := by
            apply setLIntegral_congr_fun (hK.inter measurableSet_ball)
            intro y _hy
            by_cases hyt : (true, y) ∈ t <;> simp [hyt]
      _ = ∫⁻ y in ball x delta ∩ ((fun y : State n => (true, y)) ⁻¹' t ∩ K),
          metropolisAccept s x y := by
            rw [lintegral_indicator hpre, Measure.restrict_restrict hpre]
            have hset : (fun y : State n => (true, y)) ⁻¹' t ∩
                (K ∩ ball x delta) =
              ball x delta ∩ ((fun y : State n => (true, y)) ⁻¹' t ∩ K) := by
              ext y
              simp only [mem_inter_iff, mem_preimage]
              tauto
            rw [hset]
  rw [hmoveEq]
  let A : ENNReal := ∫⁻ y in (fun y : State n => (true, y)) ⁻¹' t ∩ K,
    metropolisDensity s delta x y
  let cT : ENNReal := t.indicator 1 (true, x)
  let cF : ENNReal := t.indicator 1 (false, x)
  have hAle : A ≤ volume (ball x delta ∩ K) := by
    dsimp only [A]
    exact (lintegral_metropolisDensity_le
      ((fun y : State n => (true, y)) ⁻¹' t ∩ K) delta s x).trans
        (measure_mono (inter_subset_inter_right _ inter_subset_right))
  have hmoveNorm : (volume (ball x delta))⁻¹ * A =
      ell K delta x * ((volume (ball x delta ∩ K))⁻¹ * A) := by
    rw [volume_ball_eq x delta]
    exact (ell_mul_inv_volume_inter_ball K delta x hAle).symm
  have hrejNorm : (volume (ball x delta))⁻¹ *
        (∫⁻ y in K, (1 - metropolisAccept s x y) * cT
          ∂(volume.restrict (ball x delta))) =
      ell K delta x * ((1 - speedyMetropolisMove K delta s x) * cT) := by
    rw [Measure.restrict_restrict hK]
    have honeSub : Measurable (fun y : State n =>
        (1 : ENNReal) - metropolisAccept s x y) := measurable_const.sub hacc
    have hpull := lintegral_mul_const (μ := volume.restrict (K ∩ ball x delta)) cT honeSub
    change (volume (ball x delta))⁻¹ *
        (∫⁻ y, (1 - metropolisAccept s x y) * cT
          ∂(volume.restrict (K ∩ ball x delta))) = _
    rw [hpull, ← mul_assoc,
      normalized_proper_rejection hK delta s hdelta x, mul_assoc]
  have houtNorm : (volume (ball x delta))⁻¹ *
        (∫⁻ _y in Kᶜ, cF ∂(volume.restrict (ball x delta))) =
      (1 - ell K delta x) * cF := by
    rw [Measure.restrict_restrict hK.compl]
    change (volume (ball x delta))⁻¹ *
        (∫⁻ _y in Kᶜ ∩ ball x delta, cF) = _
    rw [lintegral_const, Measure.restrict_apply_univ, mul_comm cF,
      ← mul_assoc]
    have hset : Kᶜ ∩ ball x delta = ball x delta \ K := by
      ext y
      simp [and_comm]
    rw [hset, inv_volume_ball_mul_volume_diff hK delta hdelta x]
  change (volume (ball x delta))⁻¹ *
      (A +
        (∫⁻ y in K, (1 - metropolisAccept s x y) * cT
          ∂(volume.restrict (ball x delta))) +
        (∫⁻ _y in Kᶜ, cF ∂(volume.restrict (ball x delta)))) =
    ell K delta x *
        ((volume (ball x delta ∩ K))⁻¹ * A +
          (1 - speedyMetropolisMove K delta s x) * cT) +
      (1 - ell K delta x) * cF
  rw [mul_add, mul_add, hmoveNorm, hrejNorm, houtNorm]
  rw [← mul_add]

theorem map_rawRoundKernel_output
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (x : State n) :
    Measure.map rawRoundOutput
        (rawRoundKernel (MembershipOracle.ofMeasurableSet K hK) delta s hdelta x) =
      properProposalGaussianAux K hK delta s x :=
  map_rawRoundKernel_output_of_normalization hK delta s hdelta
    (rawNormalizationIdentity hK delta s hdelta) x

#print axioms rawNormalizationIdentity
#print axioms map_rawRoundKernel_output

end Ttc.RawGaussianMembership
