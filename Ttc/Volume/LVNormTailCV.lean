/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.LVNormTailUniform
import Ttc.Volume.CVMomentInputBridge

/-! # Direct logarithmic moment truncation for `CVAdmissible` bodies -/

namespace Ttc.CVAdaptive

open MeasureTheory Metric Set
open Arlib Ttc.CV
open scoped ENNReal

variable {n : ℕ}

theorem cvSecondMoment_pos (hn : 1 ≤ n) {K : Set (Space n)} {R2 : ℝ}
    (hK : Ttc.CVAdmissible K R2) :
    0 < Ttc.cvSecondMoment K := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  rcases hK with ⟨hconv, hball, hK0, hKtop, _hmom⟩
  have hvol : volume (closure K) = volume K :=
    Arlib.addHaar_closure_of_convex volume hconv
  have hKm : MeasurableSet (closure K) := isClosed_closure.measurableSet
  have hsub : K ⊆ closedBall (0 : Space n) (cvRadius K) :=
    subset_closedBall_cvRadius hconv hball hKtop
  have hint := integrable_norm_sq_uniformOn_of_subset_closedBall hKm (hvol.symm ▸ hK0)
    (hvol.symm ▸ hKtop) (cvRadius_pos K).le (closure_minimal hsub isClosed_closedBall)
  have hsupp : Function.support (fun x : Space n => ‖x‖ ^ 2) = ({0} : Set (Space n))ᶜ := by
    ext x
    simp [Function.mem_support, norm_eq_zero]
  rw [← cvSecondMoment_closure_eq_of_convex hconv]
  apply (integral_pos_iff_support_of_nonneg (fun x => sq_nonneg ‖x‖) hint).2
  rw [hsupp]
  haveI : IsProbabilityMeasure (Arlib.uniformOn volume (closure K)) :=
    Arlib.isProbabilityMeasure_uniformOn volume (hvol.symm ▸ hK0) (hvol.symm ▸ hKtop)
  have hsingle : Arlib.uniformOn volume (closure K) ({0} : Set (Space n)) = 0 := by
    rw [Arlib.uniformOn_apply volume hKm (measurableSet_singleton (0 : Space n))]
    have hz : volume (({0} : Set (Space n)) ∩ closure K) = 0 :=
      measure_mono_null inter_subset_left (measure_singleton (0 : Space n))
    rw [hz]
    simp
  have hsingleTop : Arlib.uniformOn volume (closure K) ({0} : Set (Space n)) ≠ ⊤ := by
    rw [hsingle]
    exact ENNReal.zero_ne_top
  rw [measure_compl (μ := Arlib.uniformOn volume (closure K))
    (s := ({0} : Set (Space n))) (measurableSet_singleton (0 : Space n)) hsingleTop, hsingle]
  simp

theorem centeredMoment_closure_cvSecondMoment
    {K : Set (Space n)} {R2 : ℝ} (hK : Ttc.CVAdmissible K R2) :
    (∫ x in closure K, (‖x‖ ^ 2 - Ttc.cvSecondMoment K)) = 0 := by
  rcases hK with ⟨hconv, hball, hK0, hKtop, hm⟩
  have hvol : volume (closure K) = volume K :=
    Arlib.addHaar_closure_of_convex volume hconv
  have hnorm := Arlib.setIntegral_eq_measure_mul_integral_uniformOn volume
    (hvol.symm ▸ hK0) (hvol.symm ▸ hKtop) (fun x : Space n => ‖x‖ ^ 2)
  rw [uniformOn_closure_eq_of_convex hconv] at hnorm
  have hconst : (∫ _x : Space n in closure K, Ttc.cvSecondMoment K) =
      (volume (closure K)).toReal * Ttc.cvSecondMoment K := by
    rw [setIntegral_const, smul_eq_mul, measureReal_def]
  have hsubK : K ⊆ closedBall (0 : Space n) (cvRadius K) :=
    subset_closedBall_cvRadius hconv hball hKtop
  have hsubCl : closure K ⊆ closedBall (0 : Space n) (cvRadius K) :=
    closure_minimal hsubK isClosed_closedBall
  have hintOn : IntegrableOn (fun x : Space n => ‖x‖ ^ 2) (closure K) volume := by
    refine Measure.integrableOn_of_bounded (M := cvRadius K ^ 2) (hvol.symm ▸ hKtop)
      ((continuous_norm.pow 2).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem isClosed_closure.measurableSet] with x hx
    have hxR : ‖x‖ ≤ cvRadius K := mem_closedBall_zero_iff.mp (hsubCl hx)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x‖)]
    nlinarith [norm_nonneg x]
  rw [integral_sub hintOn (integrableOn_const (hvol.symm ▸ hKtop)), hnorm, hconst]
  simp [Ttc.cvSecondMoment, smul_eq_mul]

theorem tvLe_uniformOn_cvAdmissible_dyadicClosure
    (hn : 2 ≤ n) {K : Set (Space n)} {R2 eta : ℝ}
    (hK : Ttc.CVAdmissible K R2) (heta0 : 0 < eta) (heta1 : eta < 1) :
    TVLe
      (Arlib.uniformOn volume
        (closure K ∩ closedBall 0
          (dyadicMomentRadius (Ttc.cvSecondMoment K) eta heta0)))
      (Arlib.uniformOn volume (closure K)) (ENNReal.ofReal eta) := by
  rcases hK with ⟨hconv, hball, hK0, hKtop, hm⟩
  have hvol : volume (closure K) = volume K :=
    Arlib.addHaar_closure_of_convex volume hconv
  have hsubK : K ⊆ closedBall (0 : Space n) (cvRadius K) :=
    subset_closedBall_cvRadius hconv hball hKtop
  have hbounded : Bornology.IsBounded (closure K) :=
    (Metric.isBounded_closedBall.subset (closure_minimal hsubK isClosed_closedBall))
  exact tvLe_uniformOn_dyadicMomentRadius hn hconv.closure isClosed_closure hbounded
    isClosed_closure.measurableSet (hvol.symm ▸ hK0) (cvSecondMoment_pos (by omega)
      ⟨hconv, hball, hK0, hKtop, hm⟩) heta0 heta1
      (centeredMoment_closure_cvSecondMoment ⟨hconv, hball, hK0, hKtop, hm⟩)

/-- The chosen logarithmic truncation radius is bounded by the same dyadic factor times the
public moment bound `sqrt R2`. -/
theorem dyadicMomentRadius_cvSecondMoment_le
    {K : Set (Space n)} {R2 eta : ℝ} (hK : Ttc.CVAdmissible K R2)
    (_hR2 : 0 ≤ R2) (heta : 0 < eta) :
    dyadicMomentRadius (Ttc.cvSecondMoment K) eta heta ≤
      Real.sqrt R2 * (1 + Real.sqrt 2 + 4 * Real.sqrt 3 * dyadicTailIndex eta heta) := by
  unfold dyadicMomentRadius
  apply mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hK.2.2.2.2)
  positivity

end Ttc.CVAdaptive

#print axioms Ttc.CVAdaptive.tvLe_uniformOn_cvAdmissible_dyadicClosure
#print axioms Ttc.CVAdaptive.dyadicMomentRadius_cvSecondMoment_le
