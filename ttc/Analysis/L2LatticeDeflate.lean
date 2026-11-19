import ArlibCommunity.Foundations.Convex.Basic.Polytope

/-! # Deflating a polytope with an inscribed `ℓ₂` ball

The `κ`-deflation `P'' = {x | ⟪A i, x⟫ ≤ b i - κ ‖A i‖}` of a polytope containing
an `ℓ₂` ball of radius `γ ≥ κ` about `c` contains the `(1 - κ/γ)`-homothety of the
polytope about `c` (the second half of the paper's Claim `cl:recenter`), so
`vol P'' ≥ (1 - κ/γ)ⁿ vol P`.  This mirrors `ArlibCommunity.Foundations.Convex.Polytope.volume_inflate_le`.

The file also collects two elementary power bounds used by the union lemma. -/

namespace ttc

open MeasureTheory Set
open scoped InnerProductSpace

variable {n : ℕ} {ι : Type*}

/-- The deflation contains the `(1 - κ/γ)`-homothety of the body about the centre
of an inscribed ball of radius `γ ≥ κ`. -/
theorem homothety_subset_deflate {A : ι → EuclideanSpace ℝ (Fin n)} {b : ι → ℝ}
    {c : EuclideanSpace ℝ (Fin n)} {γ κ : ℝ} (hγ : 0 < γ) (hκ0 : 0 ≤ κ)
    (hκγ : κ ≤ γ) (hball : Metric.ball c γ ⊆ ArlibCommunity.Foundations.Convex.Polytope.body A b) :
    AffineMap.homothety c (1 - κ / γ) '' ArlibCommunity.Foundations.Convex.Polytope.body A b ⊆
      ArlibCommunity.Foundations.Convex.Polytope.inflate A b (-κ) := by
  rintro _ ⟨x, hx, rfl⟩
  intro i
  have hcen := ArlibCommunity.Foundations.Convex.Polytope.inner_center_le_of_ball_subset hγ hball i
  have hxi : ⟪A i, x⟫_ℝ ≤ b i := hx i
  set s : ℝ := 1 - κ / γ with hs
  have hs0 : 0 ≤ s := by
    rw [hs, sub_nonneg, div_le_one hγ]; exact hκγ
  have hs1 : 0 ≤ 1 - s := by
    rw [hs]; have := div_nonneg hκ0 hγ.le; linarith
  have hγs : (1 - s) * γ = κ := by
    rw [hs]; field_simp; ring
  rw [AffineMap.homothety_apply]
  simp only [vsub_eq_sub, vadd_eq_add, inner_add_right, inner_smul_right, inner_sub_right]
  have hnorm := norm_nonneg (A i)
  have h1 : s * ⟪A i, x⟫_ℝ ≤ s * b i := mul_le_mul_of_nonneg_left hxi hs0
  have h2 : (1 - s) * (⟪A i, c⟫_ℝ + γ * ‖A i‖) ≤ (1 - s) * b i :=
    mul_le_mul_of_nonneg_left hcen hs1
  have h3 : (1 - s) * (γ * ‖A i‖) = κ * ‖A i‖ := by rw [← mul_assoc, hγs]
  nlinarith

/-- **The volume cost of deflating.** `vol P'' ≥ (1 - κ/γ)ⁿ · vol P` whenever `P`
contains an `ℓ₂` ball of radius `γ ≥ κ ≥ 0`. -/
theorem volume_deflate_ge {A : ι → EuclideanSpace ℝ (Fin n)} {b : ι → ℝ}
    {c : EuclideanSpace ℝ (Fin n)} {γ κ : ℝ} (hγ : 0 < γ) (hκ0 : 0 ≤ κ)
    (hκγ : κ ≤ γ) (hball : Metric.ball c γ ⊆ ArlibCommunity.Foundations.Convex.Polytope.body A b) :
    ENNReal.ofReal ((1 - κ / γ) ^ n) * volume (ArlibCommunity.Foundations.Convex.Polytope.body A b) ≤
      volume (ArlibCommunity.Foundations.Convex.Polytope.inflate A b (-κ)) := by
  have hs0 : 0 ≤ 1 - κ / γ := by
    rw [sub_nonneg, div_le_one hγ]; exact hκγ
  have hmono := measure_mono (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (homothety_subset_deflate hγ hκ0 hκγ hball)
  rwa [Measure.addHaar_image_homothety, finrank_euclideanSpace_fin,
    abs_of_nonneg (pow_nonneg hs0 n)] at hmono

/-- `(1 + t)ᵏ ≤ 1 + 2kt` while `kt ≤ 1/2`. -/
theorem one_add_pow_le_one_add_two_mul {t : ℝ} (ht : 0 ≤ t) :
    ∀ k : ℕ, (k : ℝ) * t ≤ 1 / 2 → (1 + t) ^ k ≤ 1 + 2 * k * t
  | 0, _ => by simp
  | k + 1, hk => by
      have hk' : (k : ℝ) * t ≤ 1 / 2 := by
        have : (k : ℝ) * t ≤ ((k + 1 : ℕ) : ℝ) * t := by
          apply mul_le_mul_of_nonneg_right _ ht; exact_mod_cast Nat.le_succ k
        linarith
      have ih := one_add_pow_le_one_add_two_mul ht k hk'
      have hkt : 0 ≤ (k : ℝ) * t := mul_nonneg (Nat.cast_nonneg k) ht
      rw [pow_succ]
      push_cast at hk ⊢
      have h1 : 0 ≤ 1 + t := by linarith
      calc (1 + t) ^ k * (1 + t) ≤ (1 + 2 * k * t) * (1 + t) :=
            mul_le_mul_of_nonneg_right ih h1
        _ ≤ 1 + 2 * (k + 1) * t := by nlinarith

/-- Bernoulli's inequality in the form `1 - kt ≤ (1 - t)ᵏ` for `t ≤ 1`. -/
theorem one_sub_mul_le_one_sub_pow {t : ℝ} (ht : t ≤ 1) (k : ℕ) :
    1 - k * t ≤ (1 - t) ^ k := by
  have h := one_add_mul_le_pow (a := -t) (by linarith) k
  have : (1 : ℝ) + -t = 1 - t := by ring
  rw [this] at h
  linarith

end ttc
