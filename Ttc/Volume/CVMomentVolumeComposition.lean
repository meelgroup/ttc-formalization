/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVMomentInputBridge
import Ttc.Volume.CVEndpointComposition

/-!
# Composing a moment truncation with a volume estimate

The moment-only Markov truncation already gives a relative volume-tail estimate in
`ENNReal`.  This file converts that estimate to the paper's real-valued `relErr` interface
and composes an estimate for the truncated body with the original body.

This is the fully proved polynomial fallback while the sharper logarithmic-radius LV07
tail remains under formalization.
-/

namespace Ttc.CVAdaptive

open MeasureTheory Metric Set
open Ttc.CV

variable {n : Nat}

/-- If removing a measurable subset loses at most an `eta` fraction of volume, the
remaining volume is an `eta`-relative approximation to the original volume. -/
theorem volume_inter_mem_relErr_of_sdiff_div_le
    {K A : Set (Space n)} (hAm : MeasurableSet A)
    (hAK : A ⊆ K) (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    {eta : Real} (heta0 : 0 ≤ eta)
    (htail : volume (K \ A) / volume K ≤ ENNReal.ofReal eta) :
    (volume A).toReal ∈ Ttc.relErr eta (volume K).toReal := by
  have hAtop : volume A ≠ ⊤ :=
    ne_top_of_le_ne_top hKtop (measure_mono hAK)
  have htailtop : volume (K \ A) ≠ ⊤ :=
    ne_top_of_le_ne_top hKtop (measure_mono sdiff_subset)
  have hsum : volume A + volume (K \ A) = volume K := by
    have h := measure_inter_add_sdiff (μ := volume) K hAm
    rwa [inter_eq_self_of_subset_right hAK] at h
  have hsumR : (volume A).toReal + (volume (K \ A)).toReal =
      (volume K).toReal := by
    rw [← ENNReal.toReal_add hAtop htailtop, hsum]
  have htailR : (volume (K \ A)).toReal ≤ eta * (volume K).toReal := by
    have h := ENNReal.toReal_mono (by simp [hKtop]) htail
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal heta0] at h
    have hKpos : 0 < (volume K).toReal := ENNReal.toReal_pos hK0 hKtop
    exact (div_le_iff₀ hKpos).mp h
  have hA0 : 0 ≤ (volume A).toReal := ENNReal.toReal_nonneg
  have hK0R : 0 ≤ (volume K).toReal := ENNReal.toReal_nonneg
  have hAle : (volume A).toReal ≤ (volume K).toReal :=
    ENNReal.toReal_mono hKtop (measure_mono hAK)
  constructor
  · nlinarith
  · nlinarith

/-- Markov moment truncation, now stated directly as relative accuracy of volumes. -/
theorem volume_markovClosure_mem_relErr
    {K : Set (Space n)} {R2 eta : Real} (hK : Ttc.CVAdmissible K R2)
    (hR2 : 0 < R2) (heta0 : 0 < eta) :
    (volume (closure K ∩ closedBall 0
      (markovMomentTruncationRadius (Real.sqrt R2) eta))).toReal ∈
      Ttc.relErr eta (volume K).toReal := by
  let A := closure K ∩ closedBall 0
    (markovMomentTruncationRadius (Real.sqrt R2) eta)
  have hvol : volume (closure K) = volume K :=
    Arlib.addHaar_closure_of_convex volume hK.1
  have htail : volume (closure K \ A) / volume (closure K) ≤ ENNReal.ofReal eta := by
    have hmoment :
        (∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2)
          ∂(Arlib.uniformOn volume (closure K))) ≤
          ENNReal.ofReal ((Real.sqrt R2) ^ 2) := by
      simpa [Real.sq_sqrt hR2.le] using cvAdmissible_lintegral_closure_le hK
    have hsqrt : 0 < Real.sqrt R2 := Real.sqrt_pos.2 hR2
    have h := volume_sdiff_markovMomentTruncation_le_relative
      (K := closure K) isClosed_closure.measurableSet hsqrt heta0 hmoment
    simpa only [A, Set.sdiff_self_inter] using h
  have hmem := volume_inter_mem_relErr_of_sdiff_div_le
    (isClosed_closure.measurableSet.inter measurableSet_closedBall)
    (inter_subset_left : A ⊆ closure K) (hvol.symm ▸ hK.2.2.1)
    (hvol.symm ▸ hK.2.2.2.1) heta0.le htail
  simpa only [A, hvol] using hmem

/-- An `eps`-accurate estimate of the Markov-truncated body is an
`eps + eta + eps*eta`-accurate estimate of the original body. -/
theorem mem_relErr_markovClosure_trans
    {K : Set (Space n)} {R2 eta eps x : Real} (hK : Ttc.CVAdmissible K R2)
    (hR2 : 0 < R2) (heta0 : 0 < eta)
    (heps0 : 0 ≤ eps)
    (hx : x ∈ Ttc.relErr eps
      (volume (closure K ∩ closedBall 0
        (markovMomentTruncationRadius (Real.sqrt R2) eta))).toReal) :
    x ∈ Ttc.relErr (eps + eta + eps * eta) (volume K).toReal := by
  exact relErr_trans heps0 heta0.le (volume K).toReal_nonneg hx
    (volume_markovClosure_mem_relErr hK hR2 heta0)

#print axioms volume_inter_mem_relErr_of_sdiff_div_le
#print axioms volume_markovClosure_mem_relErr
#print axioms mem_relErr_markovClosure_trans

end Ttc.CVAdaptive
