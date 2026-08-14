/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.MomentRadiusTruncation
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Circumradius-free truncation from a second moment

This is the unconditional Markov fallback for moment-radius truncation.  It needs no
log-concavity: an `ENNReal` second-moment bound by `R^2` gives tail at most `eps` outside
the ball of radius `R / sqrt eps`.  It is polynomially worse in `1/eps` than the logarithmic
radius supplied by LV07 Lemma 5.7, but uses only the current measure-theory API.
-/

namespace Ttc.CVAdaptive

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]

/-- ENNReal Markov bound for the norm tail at an arbitrary positive radius. -/
theorem norm_tail_le_of_lintegral_sq_le (mu : Measure E) {R r : Real}
    (hr : 0 < r)
    (hmoment : (∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂mu) <= ENNReal.ofReal (R ^ 2)) :
    mu {x | r < ‖x‖} <= ENNReal.ofReal (R ^ 2) / ENNReal.ofReal (r ^ 2) := by
  let f : E → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (‖x‖ ^ 2)
  have hf : Measurable f := (measurable_norm.pow_const 2).ennreal_ofReal
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hsub : {x : E | r < ‖x‖} ⊆ {x | ENNReal.ofReal (r ^ 2) <= f x} := by
    intro x hx
    exact ENNReal.ofReal_le_ofReal
      (le_of_lt ((sq_lt_sq₀ hr.le (norm_nonneg x)).2 hx))
  calc
    mu {x : E | r < ‖x‖} <= mu {x | ENNReal.ofReal (r ^ 2) <= f x} := measure_mono hsub
    _ <= (∫⁻ x, f x ∂mu) / ENNReal.ofReal (r ^ 2) :=
      meas_ge_le_lintegral_div hf.aemeasurable (ENNReal.ofReal_ne_zero_iff.mpr hr2)
        ENNReal.ofReal_ne_top
    _ <= ENNReal.ofReal (R ^ 2) / ENNReal.ofReal (r ^ 2) :=
      by simpa only [f] using
        ENNReal.div_le_div_right hmoment (ENNReal.ofReal (r ^ 2))

noncomputable def markovMomentTruncationRadius (R eps : Real) : Real :=
  R / Real.sqrt eps

theorem markovMomentTruncationRadius_pos {R eps : Real} (hR : 0 < R) (heps : 0 < eps) :
    0 < markovMomentTruncationRadius R eps := by
  unfold markovMomentTruncationRadius
  positivity

/-- The unconditional moment-only tail bound at radius `R / sqrt eps`. -/
theorem norm_tail_markovMomentTruncation_le (mu : Measure E) {R eps : Real}
    (hR : 0 < R) (heps : 0 < eps)
    (hmoment : (∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂mu) <= ENNReal.ofReal (R ^ 2)) :
    mu {x | markovMomentTruncationRadius R eps < ‖x‖} <= ENNReal.ofReal eps := by
  have hsqrt : 0 < Real.sqrt eps := Real.sqrt_pos.2 heps
  have hr : 0 < R / Real.sqrt eps := div_pos hR hsqrt
  have h := norm_tail_le_of_lintegral_sq_le mu hr hmoment
  have hratio : R ^ 2 / (R / Real.sqrt eps) ^ 2 = eps := by
    rw [div_pow, Real.sq_sqrt heps.le]
    field_simp [hR.ne', heps.ne']
  rw [← ENNReal.ofReal_div_of_pos (sq_pos_of_pos hr), hratio] at h
  simpa only [markovMomentTruncationRadius] using h

section Euclidean

variable {n : Nat}

private theorem tailSet_eq_sdiff_markovBall
    (K : Set (EuclideanSpace Real (Fin n))) (r : Real) :
    {x | r < ‖x‖} ∩ K = K \ closedBall 0 r := by
  ext x
  simp only [mem_inter_iff, mem_setOf_eq, mem_sdiff, mem_closedBall, not_le]
  aesop

/-- Relative volume loss at the unconditional Markov radius `R / sqrt eps`. -/
theorem volume_sdiff_markovMomentTruncation_le_relative
    {K : Set (EuclideanSpace Real (Fin n))} (hKm : MeasurableSet K)
    {R eps : Real} (hR : 0 < R) (heps : 0 < eps)
    (hmoment : (∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(Arlib.uniformOn volume K)) <=
      ENNReal.ofReal (R ^ 2)) :
    volume (K \ closedBall 0 (markovMomentTruncationRadius R eps)) / volume K <=
      ENNReal.ofReal eps := by
  have htail := norm_tail_markovMomentTruncation_le
    (Arlib.uniformOn volume K) hR heps hmoment
  rw [Arlib.uniformOn_apply volume hKm
    (measurableSet_lt measurable_const measurable_norm)] at htail
  rwa [tailSet_eq_sdiff_markovBall] at htail

/-- Total-variation form of the unconditional Markov moment-radius truncation. -/
theorem tvLe_uniformOn_markovMomentTruncation
    {K : Set (EuclideanSpace Real (Fin n))} (hKm : MeasurableSet K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    {R eps : Real} (hR : 0 < R) (heps0 : 0 < eps) (heps1 : eps < 1)
    (hmoment : (∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(Arlib.uniformOn volume K)) <=
      ENNReal.ofReal (R ^ 2)) :
    TVLe
      (Arlib.uniformOn volume (K ∩ closedBall 0 (markovMomentTruncationRadius R eps)))
      (Arlib.uniformOn volume K) (ENNReal.ofReal eps) := by
  let A := K ∩ closedBall 0 (markovMomentTruncationRadius R eps)
  have hAm : MeasurableSet A := hKm.inter measurableSet_closedBall
  have hratio : volume (K \ A) / volume K <= ENNReal.ofReal eps := by
    have h := volume_sdiff_markovMomentTruncation_le_relative
      hKm hR heps0 hmoment
    simpa only [A, Set.sdiff_self_inter] using h
  have hepsENN : ENNReal.ofReal eps < 1 := by
    rw [ENNReal.ofReal_lt_one]
    exact heps1
  have hA0 : volume A ≠ 0 := by
    intro hAz
    have hadd : volume A + volume (K \ A) = volume K := by
      have h := measure_inter_add_sdiff (μ := volume) K hAm
      rwa [inter_eq_self_of_subset_right inter_subset_left] at h
    have htailEq : volume (K \ A) = volume K := by simpa [hAz] using hadd
    have hone : (1 : ENNReal) <= ENNReal.ofReal eps := by
      have hdiv : volume (K \ A) / volume K = 1 := by
        rw [htailEq, ENNReal.div_self hK0 hKtop]
      simpa [hdiv] using hratio
    exact (not_le_of_gt hepsENN) hone
  exact (tvLe_condOn_subset hAm hKm inter_subset_left hA0 hKtop).mono hratio

end Euclidean

end Ttc.CVAdaptive

#print axioms Ttc.CVAdaptive.norm_tail_le_of_lintegral_sq_le
#print axioms Ttc.CVAdaptive.norm_tail_markovMomentTruncation_le
#print axioms Ttc.CVAdaptive.volume_sdiff_markovMomentTruncation_le_relative
#print axioms Ttc.CVAdaptive.tvLe_uniformOn_markovMomentTruncation
