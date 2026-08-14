/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.AdaptiveChunkEndpoints

/-!
# Replacing the cold normalizer and composing the hot endpoint

The exact cooling telescope multiplies by `A0`; the executable estimator knows an ambient
normalizer `Z0`.  The cold Chernoff theorem places `A0` between `(1-eta) Z0` and `Z0`.
This file records the resulting one-sided correction and composes it with the hot bias.
-/

namespace Ttc.CV

open Set

/-- Replacing the exact cold normalizer by its known ambient upper bound costs
`(eps+eta)/(1-eta)` relative error. -/
theorem mem_relErr_replace_coldNormalizer {A0 Z0 X Am eps eta : ℝ}
    (hA0 : 0 < A0) (hX : 0 ≤ X)
    (heps0 : 0 ≤ eps) (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (hA0le : A0 ≤ Z0) (hcold : A0 ∈ relErr eta Z0)
    (hrun : A0 * X ∈ relErr eps Am) :
    Z0 * X ∈ relErr ((eps + eta) / (1 - eta)) Am := by
  have hden : 0 < 1 - eta := by linarith
  have hAm0 : 0 ≤ Am := by
    by_contra h
    have hupper := hrun.2
    have hfac : 0 ≤ 1 + eps := by linarith
    have : (1 + eps) * Am < 0 := mul_neg_of_pos_of_neg (by linarith) (lt_of_not_ge h)
    nlinarith
  have hlow : (1 - (eps + eta) / (1 - eta)) * Am ≤ Z0 * X := by
    have hrunlow := hrun.1
    have hmul : A0 * X ≤ Z0 * X := mul_le_mul_of_nonneg_right hA0le hX
    have hcoef : 1 - (eps + eta) / (1 - eta) ≤ 1 - eps := by
      rw [sub_le_sub_iff_left, le_div_iff₀ hden]
      nlinarith
    exact (mul_le_mul_of_nonneg_right hcoef hAm0).trans (hrunlow.trans hmul)
  have hcoldlow : (1 - eta) * Z0 ≤ A0 := hcold.1
  have hZX : (1 - eta) * (Z0 * X) ≤ A0 * X := by
    nlinarith [mul_le_mul_of_nonneg_right hcoldlow hX]
  have hrunup := hrun.2
  have huppre : (1 - eta) * (Z0 * X) ≤ (1 + eps) * Am := hZX.trans hrunup
  have hcoef : 1 + (eps + eta) / (1 - eta) = (1 + eps) / (1 - eta) := by
    field_simp
    ring
  have hup : Z0 * X ≤ (1 + (eps + eta) / (1 - eta)) * Am := by
    rw [hcoef, div_mul_eq_mul_div]
    exact (le_div_iff₀ hden).2 (by nlinarith)
  exact ⟨hlow, hup⟩

/-- Cold-normalizer replacement followed by the hot Gaussian-to-volume bias. -/
theorem mem_relErr_replace_cold_and_hot {A0 Z0 X Am V eps eta theta : ℝ}
    (hA0 : 0 < A0) (hX : 0 ≤ X)
    (heps0 : 0 ≤ eps) (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (htheta0 : 0 ≤ theta) (hV : 0 ≤ V)
    (hA0le : A0 ≤ Z0) (hcold : A0 ∈ relErr eta Z0)
    (hrun : A0 * X ∈ relErr eps Am)
    (hhot : Am ∈ relErr theta V) :
    Z0 * X ∈ relErr
      ((eps + eta) / (1 - eta) + theta +
        ((eps + eta) / (1 - eta)) * theta) V := by
  have hfirst := mem_relErr_replace_coldNormalizer hA0 hX heps0 heta0 heta1
    hA0le hcold hrun
  exact relErr_trans (div_nonneg (add_nonneg heps0 heta0) (by linarith)) htheta0 hV
    hfirst hhot

#print axioms mem_relErr_replace_coldNormalizer
#print axioms mem_relErr_replace_cold_and_hot

end Ttc.CV
