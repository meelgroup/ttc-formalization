/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Rounding.Cl
import Ttc.Rounding.Tent
import Mathlib.MeasureTheory.Integral.Pi

/-!
# The rounding kernel of independent coordinatewise rounding

`Ttc.RoundingKernel` (`Rounding/Cl`) takes double stochasticity `∫ k p x dp = 1` as
a field, because it is a property of the construction rather than a generic fact.
Here the construction is supplied: independent coordinatewise randomized rounding,
whose kernel is the product of the one-dimensional tent densities of
`Rounding/Tent`,

  `k p x = ∏ᵢ tent(pᵢ − xᵢ)`.

`Ttc.integral_prod_tent` proves the normalisation outright, by Fubini over the
product measure and translation invariance in each coordinate — so `Ttc.prodKernel`
is a `Ttc.RoundingKernel` with *nothing* assumed.
-/

namespace Ttc

open MeasureTheory

variable {n : ℕ}

/-- Coordinate projection on `Space n` is measurable. -/
theorem measurable_coord (i : Fin n) : Measurable (fun p : Space n => p i) :=
  (measurable_pi_apply i).comp (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurable

/-- Coordinate projection on `Space n` is continuous. -/
theorem continuous_coord (i : Fin n) : Continuous (fun p : Space n => p i) :=
  (continuous_apply i).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).continuous

/-- **The product normalisation.** `∫ ∏ᵢ tent(pᵢ − xᵢ) dp = 1`: Fubini over the
product measure, then translation invariance and `Ttc.integral_tent` in each
coordinate. This is `Ttc.RoundingKernel.normalised`, *proved*. -/
theorem integral_prod_tent (n : ℕ) (x : Space n) :
    ∫ p : Space n, ∏ i, tent (p i - x i) = 1 := by
  have hC : (∫ p : Space n, ∏ i, tent (p i - x i))
      = ∫ q : Fin n → ℝ, ∏ i, tent (q i - x i) := by
    exact (PiLp.volume_preserving_ofLp (Fin n)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding
      (g := fun q : Fin n → ℝ => ∏ i, tent (q i - x i))
  rw [hC, integral_fintype_prod_volume_eq_prod (fun i u => tent (u - x i))]
  have h1 : ∀ i : Fin n, ∫ u : ℝ, tent (u - x i) = 1 := by
    intro i
    rw [(measurePreserving_sub_right (volume : Measure ℝ) (x i)).integral_comp
      (MeasurableEquiv.subRight (x i)).measurableEmbedding tent, integral_tent]
  simp [h1]

/-- The paper's `C(x)`: the side-2 box about `x`, where the displacement lives. -/
def roundBox (x : Space n) : Set (Space n) := {p | ∀ i, |p i - x i| ≤ 1}

theorem measurableSet_roundBox (x : Space n) : MeasurableSet (roundBox x) := by
  have hrw : roundBox x = ⋂ i, {p : Space n | |p i - x i| ≤ 1} := by
    ext p; simp [roundBox]
  rw [hrw]
  exact MeasurableSet.iInter fun i =>
    measurableSet_le (((measurable_coord i).sub measurable_const).abs) measurable_const

/-- A point of the box is within `√n` of the centre — so the box is bounded. -/
theorem norm_sub_le_of_mem_roundBox {x p : Space n} (h : p ∈ roundBox x) :
    ‖p - x‖ ≤ Real.sqrt n := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖(p - x) i‖ ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hi : ‖(p - x) i‖ = |p i - x i| := by simp [Real.norm_eq_abs]
        rw [hi]
        nlinarith [abs_nonneg (p i - x i), h i]
    _ = (n : ℝ) := by simp

theorem roundBox_subset_closedBall (x : Space n) :
    roundBox x ⊆ Metric.closedBall x (Real.sqrt n) := by
  intro p hp
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact norm_sub_le_of_mem_roundBox hp

/-- The product density vanishes off the box: some coordinate's displacement
exceeds `1`, and that factor of the product is `0`. -/
theorem prod_tent_eq_zero_of_notMem {x p : Space n} (h : p ∉ roundBox x) :
    ∏ i, tent (p i - x i) = 0 := by
  simp only [roundBox, Set.mem_setOf_eq, not_forall, not_le] at h
  obtain ⟨i, hi⟩ := h
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  exact tent_eq_zero_of_one_le hi.le

theorem continuous_prod_tent (x : Space n) :
    Continuous (fun p : Space n => ∏ i, tent (p i - x i)) :=
  continuous_finsetProd _ fun i _ =>
    continuous_tent.comp ((continuous_coord i).sub continuous_const)

theorem integrable_prod_tent (x : Space n) :
    Integrable (fun p : Space n => ∏ i, tent (p i - x i)) := by
  refine (continuous_prod_tent x).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_closedBall x (Real.sqrt n)) ?_
  intro p hp
  exact prod_tent_eq_zero_of_notMem fun hbox => hp (roundBox_subset_closedBall x hbox)

/-- **The rounding kernel of independent coordinatewise randomized rounding.**

Every field is proved; nothing is assumed. In particular `normalised` — the
double stochasticity that `Ttc.RoundingKernel` otherwise takes on trust — is
`Ttc.integral_prod_tent`. -/
noncomputable def prodKernel (n : ℕ) : RoundingKernel n where
  k := fun p x => ∏ i, tent (p i - x i)
  supp := roundBox
  supp_meas := measurableSet_roundBox
  nonneg := fun _ _ => Finset.prod_nonneg fun _ _ => tent_nonneg _
  integrable := integrable_prod_tent
  vanishes := fun _ _ hp => prod_tent_eq_zero_of_notMem hp
  normalised := integral_prod_tent n

end Ttc
