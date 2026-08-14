/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.LVNormTailDyadic
import Ttc.Volume.MomentRadiusTruncation

/-! # Uniform-volume and TV consequences of the direct LV tail -/

namespace Ttc.CVAdaptive

open MeasureTheory Metric Set
open Arlib Arlib.MarkovChains
open scoped ENNReal

variable {n : ℕ}

noncomputable def dyadicMomentRadius (M eta : ℝ) (heta : 0 < eta) : ℝ :=
  Real.sqrt M * (1 + Real.sqrt 2 + 4 * Real.sqrt 3 * dyadicTailIndex eta heta)

theorem volume_sdiff_dyadicMomentRadius_toReal_le
    (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKb : Bornology.IsBounded K)
    {M eta : ℝ} (hM : 0 < M) (heta : 0 < eta)
    (hmoment : (∫ x in K, (‖x‖ ^ 2 - M)) = 0) :
    (volume (K \ closedBall 0 (dyadicMomentRadius M eta heta))).toReal ≤
      eta * (volume K).toReal := by
  let O : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | dyadicMomentRadius M eta heta < ‖x‖}
  have hO : MeasurableSet O :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have hKtop : volume K ≠ ⊤ :=
    (Metric.isCompact_of_isClosed_isBounded hKcl hKb).measure_lt_top.ne
  have hIon : IntegrableOn (O.indicator (fun _ => (1 : ℝ))) K :=
    (integrableOn_const hKtop).indicator hO
  have hconst : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin n) =>
      1 / (2 : ℝ) ^ dyadicTailIndex eta heta) K := integrableOn_const hKtop
  have h := body_normTail_chosen_dyadic hn hKc hKcl hKb hM heta hmoment
  change (∫ x in K, O.indicator (fun _ => (1 : ℝ)) x -
    1 / (2 : ℝ) ^ dyadicTailIndex eta heta) ≤ 0 at h
  have hreal : (volume (K ∩ O)).toReal ≤
      (1 / (2 : ℝ) ^ dyadicTailIndex eta heta) * (volume K).toReal := by
    rw [show (∫ x in K, O.indicator (fun _ => (1 : ℝ)) x -
          1 / (2 : ℝ) ^ dyadicTailIndex eta heta) =
        (∫ x in K, O.indicator (fun _ => (1 : ℝ)) x) -
          ∫ _x in K, (1 / (2 : ℝ) ^ dyadicTailIndex eta heta) by
      rw [integral_sub hIon hconst]] at h
    have hcint : (∫ _x : EuclideanSpace ℝ (Fin n) in K,
        (1 / (2 : ℝ) ^ dyadicTailIndex eta heta)) =
        (1 / (2 : ℝ) ^ dyadicTailIndex eta heta) * (volume K).toReal := by
      rw [setIntegral_const, smul_eq_mul, measureReal_def]
      ring
    rw [setIntegral_indicator hO, setIntegral_const, smul_eq_mul, mul_one,
      measureReal_def] at h
    rw [hcint] at h
    simpa only [O, dyadicMomentRadius] using (sub_nonpos.mp h)
  have hset : K \ closedBall 0 (dyadicMomentRadius M eta heta) = K ∩ O := by
    ext x
    simp [O, mem_closedBall]
  rw [hset]
  exact hreal.trans (mul_le_mul_of_nonneg_right
    (inv_two_pow_dyadicTailIndex_le heta) (ENNReal.toReal_nonneg))

theorem volume_sdiff_dyadicMomentRadius_div_le
    (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKb : Bornology.IsBounded K)
    (hK0 : volume K ≠ 0) {M eta : ℝ} (hM : 0 < M) (heta : 0 < eta)
    (hmoment : (∫ x in K, (‖x‖ ^ 2 - M)) = 0) :
    volume (K \ closedBall 0 (dyadicMomentRadius M eta heta)) / volume K ≤
      ENNReal.ofReal eta := by
  have hKtop : volume K ≠ ⊤ :=
    (Metric.isCompact_of_isClosed_isBounded hKcl hKb).measure_lt_top.ne
  have hSsub : K \ closedBall 0 (dyadicMomentRadius M eta heta) ⊆ K := sdiff_subset
  have hStop : volume (K \ closedBall 0 (dyadicMomentRadius M eta heta)) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hSsub) (lt_top_iff_ne_top.2 hKtop))
  rw [← ENNReal.toReal_le_toReal (ENNReal.div_ne_top hStop hK0) ENNReal.ofReal_ne_top,
    ENNReal.toReal_div, ENNReal.toReal_ofReal heta.le]
  apply (div_le_iff₀ (ENNReal.toReal_pos hK0 hKtop)).2
  exact volume_sdiff_dyadicMomentRadius_toReal_le hn hKc hKcl hKb hM heta hmoment

theorem tvLe_uniformOn_dyadicMomentRadius
    (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKb : Bornology.IsBounded K)
    (hKm : MeasurableSet K) (hK0 : volume K ≠ 0)
    {M eta : ℝ} (hM : 0 < M) (heta0 : 0 < eta) (heta1 : eta < 1)
    (hmoment : (∫ x in K, (‖x‖ ^ 2 - M)) = 0) :
    TVLe
      (Arlib.uniformOn volume (K ∩ closedBall 0 (dyadicMomentRadius M eta heta0)))
      (Arlib.uniformOn volume K) (ENNReal.ofReal eta) := by
  let A := K ∩ closedBall 0 (dyadicMomentRadius M eta heta0)
  have hAm : MeasurableSet A := hKm.inter measurableSet_closedBall
  have hKtop : volume K ≠ ⊤ :=
    (Metric.isCompact_of_isClosed_isBounded hKcl hKb).measure_lt_top.ne
  have hratio : volume (K \ A) / volume K ≤ ENNReal.ofReal eta := by
    simpa only [A, Set.sdiff_self_inter] using
      volume_sdiff_dyadicMomentRadius_div_le hn hKc hKcl hKb hK0 hM heta0 hmoment
  have hA0 : volume A ≠ 0 := by
    intro hAz
    have hadd : volume A + volume (K \ A) = volume K := by
      have h := measure_inter_add_sdiff (μ := volume) K hAm
      rwa [inter_eq_self_of_subset_right inter_subset_left] at h
    have htailEq : volume (K \ A) = volume K := by simpa [hAz] using hadd
    have hdiv : volume (K \ A) / volume K = 1 := by
      rw [htailEq, ENNReal.div_self hK0 hKtop]
    have : (1 : ENNReal) ≤ ENNReal.ofReal eta := by simpa [hdiv] using hratio
    exact (not_le_of_gt (by rw [ENNReal.ofReal_lt_one]; exact heta1)) this
  exact (tvLe_condOn_subset hAm hKm inter_subset_left hA0 hKtop).mono hratio

end Ttc.CVAdaptive

#print axioms Ttc.CVAdaptive.volume_sdiff_dyadicMomentRadius_div_le
#print axioms Ttc.CVAdaptive.tvLe_uniformOn_dyadicMomentRadius
