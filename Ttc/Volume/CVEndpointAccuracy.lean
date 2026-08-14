/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVEndpointComposition
import Ttc.Volume.CVAdaptiveExact

/-!
# Endpoint correction for the median CV estimator

The exact cooling theorem estimates the last restricted Gaussian normalizer after multiplying
each run by the unknown first restricted normalizer.  The executable estimator instead uses the
known ambient Gaussian normalizer.  This file lifts the pointwise endpoint algebra through the
positive scaling equivariance of the concrete median selector.
-/

namespace Ttc.CV

open MeasureTheory Set
open Arlib.Probability

/-- The concrete finite median selector commutes with multiplication by a positive scalar. -/
theorem medianSel_mul_pos {r : ℕ} (c : ℝ) (hc : 0 < c) (v : Fin r → ℝ) :
    medianSel (fun i => c * v i) = c * medianSel v := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst r
    simp [medianSel]
  have hne : (Finset.univ : Finset (Fin r)).Nonempty :=
    ⟨⟨0, hr⟩, Finset.mem_univ _⟩
  unfold medianSel
  rw [dif_pos hr]
  have hfilter (i : Fin r) :
      (Finset.univ.filter fun j => c * v i ≤ c * v j) =
        Finset.univ.filter fun j => v i ≤ v j := by
    apply Finset.filter_congr
    intro j _
    exact mul_le_mul_iff_of_pos_left hc
  have hinf :
      Finset.univ.inf' hne (fun i => c * v i) =
        c * Finset.univ.inf' hne v := by
    change Finset.univ.inf' hne (fun i => (OrderIso.mulLeft₀ c hc) (v i)) =
      (OrderIso.mulLeft₀ c hc) (Finset.univ.inf' hne v)
    exact (map_finset_inf' (OrderIso.mulLeft₀ c hc) hne v).symm
  have hbranch (i : Fin r) :
      (if r ≤ 2 * (Finset.univ.filter fun j => c * v i ≤ c * v j).card then c * v i
        else Finset.univ.inf' hne (fun j => c * v j)) =
        c * (if r ≤ 2 * (Finset.univ.filter fun j => v i ≤ v j).card then v i
          else Finset.univ.inf' hne v) := by
    rw [hfilter, hinf]
    split <;> simp_all
  simp only [dif_pos hr]
  calc
    Finset.univ.sup' hne
        (fun i => if r ≤ 2 * (Finset.univ.filter fun j => c * v i ≤ c * v j).card
          then c * v i else Finset.univ.inf' hne (fun j => c * v j)) =
        Finset.univ.sup' hne (fun i => c *
          (if r ≤ 2 * (Finset.univ.filter fun j => v i ≤ v j).card then v i
            else Finset.univ.inf' hne v)) :=
      Finset.sup'_congr hne rfl fun i _ => hbranch i
    _ = c * Finset.univ.sup' hne
        (fun i => if r ≤ 2 * (Finset.univ.filter fun j => v i ≤ v j).card then v i
          else Finset.univ.inf' hne v) :=
      (Finset.mul₀_sup' hc.le
        (fun i => if r ≤ 2 * (Finset.univ.filter fun j => v i ≤ v j).card then v i
          else Finset.univ.inf' hne v) Finset.univ hne).symm

/-- Replace the cold endpoint and then the hot endpoint inside the probability guarantee for the
actual median estimator.  The `X` values are the unnormalised run products. -/
theorem measureReal_median_replace_cold_and_hot
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {r : ℕ}
    {X : Fin r → Ω → ℝ} {A0 Z0 Am V eps eta theta p : ℝ}
    (hr : 0 < r) (hA0 : 0 < A0) (hZ0 : 0 < Z0)
    (hX0 : ∀ t ω, 0 ≤ X t ω)
    (heps0 : 0 ≤ eps) (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (htheta0 : 0 ≤ theta) (hV : 0 ≤ V)
    (hA0le : A0 ≤ Z0) (hcold : A0 ∈ relErr eta Z0)
    (hhot : Am ∈ relErr theta V)
    (hgood : 1 - p ≤ μ.real
      {ω | medianSel (fun t => A0 * X t ω) ∈ relErr eps Am}) :
    1 - p ≤ μ.real
      {ω | medianSel (fun t => Z0 * X t ω) ∈
        relErr ((eps + eta) / (1 - eta) + theta +
          ((eps + eta) / (1 - eta)) * theta) V} := by
  refine hgood.trans (measureReal_mono ?_)
  intro ω hω
  have hmed0 : 0 ≤ medianSel (fun t => X t ω) := by
    by_contra hneg
    have hmedian := (medianSel_isMedian (fun t => X t ω)).1
    have hempty : (Finset.univ.filter fun t => X t ω ≤ medianSel (fun t => X t ω)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro t _ ht
      exact (not_le_of_gt ((lt_of_not_ge hneg).trans_le (hX0 t ω))) ht
    rw [hempty] at hmedian
    simp at hmedian
    omega
  simp only [Set.mem_setOf_eq] at hω ⊢
  rw [medianSel_mul_pos A0 hA0] at hω
  rw [medianSel_mul_pos Z0 hZ0]
  exact mem_relErr_replace_cold_and_hot hA0 hmed0 heps0 heta0 heta1 htheta0 hV
    hA0le hcold hω hhot

/-- Probability-level cold-normalizer replacement when the cooling telescope already ends
at the desired target (in particular, after the final Gaussian-to-uniform phase). -/
theorem measureReal_median_replace_cold
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {r : ℕ}
    {X : Fin r → Ω → ℝ} {A0 Z0 V eps eta p : ℝ}
    (hr : 0 < r) (hA0 : 0 < A0) (hZ0 : 0 < Z0)
    (hX0 : ∀ t ω, 0 ≤ X t ω)
    (heps0 : 0 ≤ eps) (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (hA0le : A0 ≤ Z0) (hcold : A0 ∈ relErr eta Z0)
    (hgood : 1 - p ≤ μ.real
      {ω | medianSel (fun t => A0 * X t ω) ∈ relErr eps V}) :
    1 - p ≤ μ.real
      {ω | medianSel (fun t => Z0 * X t ω) ∈
        relErr ((eps + eta) / (1 - eta)) V} := by
  refine hgood.trans (measureReal_mono ?_)
  intro ω hω
  have hmed0 : 0 ≤ medianSel (fun t => X t ω) := by
    by_contra hneg
    have hmedian := (medianSel_isMedian (fun t => X t ω)).1
    have hempty : (Finset.univ.filter fun t => X t ω ≤ medianSel (fun t => X t ω)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro t _ ht
      exact (not_le_of_gt ((lt_of_not_ge hneg).trans_le (hX0 t ω))) ht
    rw [hempty] at hmedian
    simp at hmedian
    omega
  simp only [Set.mem_setOf_eq] at hω ⊢
  rw [medianSel_mul_pos A0 hA0] at hω
  rw [medianSel_mul_pos Z0 hZ0]
  exact mem_relErr_replace_coldNormalizer hA0 hmed0 heps0 heta0 heta1 hA0le hcold hω

#print axioms medianSel_mul_pos
#print axioms measureReal_median_replace_cold
#print axioms measureReal_median_replace_cold_and_hot

end Ttc.CV
