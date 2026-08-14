/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVTheorem11
import Ttc.Volume.CVBodyRegularization
import Ttc.Volume.MomentRadiusMarkovTruncation
import Ttc.Volume.CVMomentMarkovRuntime

/-!
# Connecting the CV second-moment input to moment truncation

`CVAdmissible` records the second moment as a real Bochner integral.  The Markov and
LV truncation interfaces use the nonnegative `ENNReal` integral.  This file proves that
the two presentations agree for an admissible convex body.  It also transports the
moment through closure, which is the measurable body used by the concrete sampler.
-/

namespace Ttc.CVAdaptive

open MeasureTheory Metric Set
open Arlib Ttc.CV
open scoped ENNReal

variable {n : Nat}

/-- Closing a convex body does not change its uniform probability measure. -/
theorem uniformOn_closure_eq_of_convex {K : Set (Space n)} (hK : Convex Real K) :
    Arlib.uniformOn volume (closure K) = Arlib.uniformOn volume K := by
  rw [Arlib.uniformOn_def, Arlib.uniformOn_def,
    Arlib.addHaar_closure_of_convex volume hK,
    Measure.restrict_congr_set (Arlib.ae_eq_closure_of_convex volume hK)]

/-- In particular, closing a convex body preserves the second moment used in
`CVAdmissible`. -/
theorem cvSecondMoment_closure_eq_of_convex {K : Set (Space n)} (hK : Convex Real K) :
    Ttc.cvSecondMoment (closure K) = Ttc.cvSecondMoment K := by
  unfold Ttc.cvSecondMoment
  rw [uniformOn_closure_eq_of_convex hK]

/-- Squared norm is integrable under the uniform law of a positive finite body contained
in a finite ball. -/
theorem integrable_norm_sq_uniformOn_of_subset_closedBall
    {K : Set (Space n)} {R : Real} (hKm : MeasurableSet K) (hK0 : volume K ≠ 0)
    (hKtop : volume K ≠ ⊤) (hR : 0 <= R)
    (hsub : K ⊆ closedBall 0 R) :
    Integrable (fun x : Space n => ‖x‖ ^ 2) (Arlib.uniformOn volume K) := by
  have hintOn : IntegrableOn (fun x : Space n => ‖x‖ ^ 2) K volume := by
    refine Measure.integrableOn_of_bounded (M := R ^ 2) hKtop
      ((continuous_norm.pow 2).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem hKm] with x hx
    have hxR : ‖x‖ <= R := mem_closedBall_zero_iff.mp (hsub hx)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x‖)]
    nlinarith [norm_nonneg x]
  rw [Arlib.uniformOn_def]
  exact hintOn.smul_measure (ENNReal.inv_ne_top.2 hK0)

/-- On a bounded positive finite body, the `ENNReal` squared-norm moment is exactly the
`ofReal` of the real moment used in the statement of Theorem 1.1. -/
theorem lintegral_norm_sq_uniformOn_eq_ofReal_cvSecondMoment
    {K : Set (Space n)} {R : Real} (hKm : MeasurableSet K) (hK0 : volume K ≠ 0)
    (hKtop : volume K ≠ ⊤) (hR : 0 <= R)
    (hsub : K ⊆ closedBall 0 R) :
    (∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(Arlib.uniformOn volume K)) =
      ENNReal.ofReal (Ttc.cvSecondMoment K) := by
  have hint := integrable_norm_sq_uniformOn_of_subset_closedBall hKm hK0 hKtop hR hsub
  have hnn : ∀ x : Space n, 0 <= ‖x‖ ^ 2 := fun _ => sq_nonneg _
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)]
  rfl

/-- The public `CVAdmissible` moment hypothesis, after the lossless closure
regularization, supplies exactly the nonnegative moment inequality consumed by Markov
truncation. -/
theorem cvAdmissible_lintegral_closure_le {K : Set (Space n)} {R2 : Real}
    (hK : Ttc.CVAdmissible K R2) :
    (∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(Arlib.uniformOn volume (closure K))) <=
      ENNReal.ofReal R2 := by
  rcases hK with ⟨hconv, hball, hK0, hKtop, hmoment⟩
  have hvol : volume (closure K) = volume K :=
    Arlib.addHaar_closure_of_convex volume hconv
  have hsubK : K ⊆ closedBall (0 : Space n) (cvRadius K) :=
    subset_closedBall_cvRadius hconv hball hKtop
  have hsub : closure K ⊆ closedBall (0 : Space n) (cvRadius K) :=
    closure_minimal hsubK isClosed_closedBall
  rw [lintegral_norm_sq_uniformOn_eq_ofReal_cvSecondMoment
    isClosed_closure.measurableSet (hvol.symm ▸ hK0) (hvol.symm ▸ hKtop)
      (cvRadius_pos K).le hsub,
    cvSecondMoment_closure_eq_of_convex hconv]
  exact ENNReal.ofReal_le_ofReal hmoment

/-- A direct Markov-truncation TV theorem from the public Theorem 1.1 input contract.
The truncated body is the closure of `K` intersected with the ball of radius
`sqrt R2 / sqrt eta`. -/
theorem tvLe_uniformOn_cvAdmissible_markovClosure
    {K : Set (Space n)} {R2 eta : Real} (hK : Ttc.CVAdmissible K R2)
    (hR2 : 0 < R2) (heta0 : 0 < eta) (heta1 : eta < 1) :
    TVLe
      (Arlib.uniformOn volume
        (closure K ∩ closedBall 0
          (markovMomentTruncationRadius (Real.sqrt R2) eta)))
      (Arlib.uniformOn volume (closure K)) (ENNReal.ofReal eta) := by
  rcases hK with ⟨hconv, hball, hK0, hKtop, hmoment⟩
  have hvol : volume (closure K) = volume K :=
    Arlib.addHaar_closure_of_convex volume hconv
  have hsqrt : 0 < Real.sqrt R2 := Real.sqrt_pos.2 hR2
  apply tvLe_uniformOn_markovMomentTruncation isClosed_closure.measurableSet
    (hvol.symm ▸ hK0) (hvol.symm ▸ hKtop) hsqrt heta0 heta1
  simpa [Real.sq_sqrt hR2.le] using
    (cvAdmissible_lintegral_closure_le
      (K := K) (R2 := R2) ⟨hconv, hball, hK0, hKtop, hmoment⟩)

/-- The dimension-normalized radius of the admissible-input Markov truncation has the
explicit polynomial bound `2n + 2 R2/eta`. -/
theorem cvAdmissible_markovRuntimeC_sq_mul_n_le
    (hn : 1 <= n) {R2 eta : Real} (hR2 : 0 < R2) (heta : 0 < eta) :
    markovRuntimeC n (Real.sqrt R2) eta ^ 2 * (n : Real) <=
      2 * (n : Real) + 2 * R2 / eta := by
  simpa [Real.sq_sqrt hR2.le] using
    (markovRuntimeC_sq_mul_n_le hn (Real.sqrt_pos.2 hR2) heta)

/-- The regularized, Markov-truncated input lies in precisely the runtime ball controlled
by the preceding polynomial estimate. -/
theorem closure_inter_markovBall_subset_runtimeBall
    (hn : 1 <= n) {K : Set (Space n)} {R2 eta : Real} :
    closure K ∩ closedBall 0
        (markovMomentTruncationRadius (Real.sqrt R2) eta) ⊆
      closedBall 0 (markovRuntimeC n (Real.sqrt R2) eta * Real.sqrt n) :=
  inter_markovBall_subset_runtimeBall hn

end Ttc.CVAdaptive

#print axioms Ttc.CVAdaptive.uniformOn_closure_eq_of_convex
#print axioms Ttc.CVAdaptive.cvSecondMoment_closure_eq_of_convex
#print axioms Ttc.CVAdaptive.cvAdmissible_lintegral_closure_le
#print axioms Ttc.CVAdaptive.tvLe_uniformOn_cvAdmissible_markovClosure
#print axioms Ttc.CVAdaptive.cvAdmissible_markovRuntimeC_sq_mul_n_le
#print axioms Ttc.CVAdaptive.closure_inter_markovBall_subset_runtimeBall
