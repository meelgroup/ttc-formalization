/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Nonconv.Core

/-!
# `lem:lattice`: transporting `lem:nonconv` to the fine lattice `𝕃ⁿ`

The algorithm does not count integer points; it counts points of
`𝕃ⁿ = 10^(−ρ)·ℤⁿ`. `lem:lattice` transports `lem:nonconv` along the "canonical isomorphism
`φ : 𝕃ⁿ → ℤⁿ`" — which is just the dilation by `c = 10^ρ`.

Everything in this file is proved. Concretely:

* `Ttc.ncard_inter_lattice_smul` — the dilation is a bijection from `Q ∩ 𝕃ⁿ` to
  `(c·Q) ∩ ℤⁿ`, so the two counts agree. (The paper: "since `φ` preserves the
  lattice structure, `|φ(Q) ∩ ℤⁿ| = |Q ∩ 𝕃ⁿ|`".)
* `Ttc.volume_smul_body` — `vol(c·Q) = cⁿ · vol Q`. (The paper: "the volume scales
  by `10^(ρ·n)`".)
* `Ttc.lattice_of_scaled` — combining the two: `lem:nonconv`'s conclusion for `c·Q`
  becomes `lem:lattice`'s conclusion for `Q`.

The inscribed-ball condition also transports (`Ttc.ball_radius_scales`): a ball of
radius `r` for `Q` becomes one of radius `c·r` for `c·Q`, which is why
`GetPrecision` returns `⌈log₁₀(γ/γ̂)⌉`.
-/

namespace Ttc

open MeasureTheory Set Pointwise

variable {n : ℕ}

/-- Dilating by `c` carries the fine lattice onto the integer lattice. -/
theorem smul_fineLattice {c : ℝ} (hc : c ≠ 0) :
    c • fineLattice n c = intLattice n := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ i
    obtain ⟨k, hk⟩ := hy i
    exact ⟨k, by simp [hk, mul_inv_cancel_left₀ hc]⟩
  · intro hx
    refine ⟨c⁻¹ • x, fun i => ?_, ?_⟩
    · obtain ⟨k, hk⟩ := hx i
      exact ⟨k, by simp [hk]⟩
    · show c • c⁻¹ • x = x
      rw [smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- Dilation commutes with intersecting against the respective lattices. -/
theorem smul_inter_fineLattice {c : ℝ} (hc : c ≠ 0) (Q : Set (Space n)) :
    c • (Q ∩ fineLattice n c) = (c • Q) ∩ intLattice n := by
  rw [smul_set_inter₀ (by simpa using hc), smul_fineLattice hc]

/-- **The counting half of `lem:lattice`.** The number of fine-lattice points in `Q`
equals the number of integer points in the dilate `c·Q`. -/
theorem ncard_inter_lattice_smul {c : ℝ} (hc : c ≠ 0) (Q : Set (Space n)) :
    (Q ∩ fineLattice n c).ncard = ((c • Q) ∩ intLattice n).ncard := by
  rw [← smul_inter_fineLattice hc Q]
  exact (Set.ncard_image_of_injective _ (smul_right_injective (Space n) hc)).symm

/-- **The volume half of `lem:lattice`.** Lebesgue measure on `ℝⁿ` scales by `cⁿ`. -/
theorem volume_smul_body {c : ℝ} (hc : 0 ≤ c) (Q : Set (Space n)) :
    volume (c • Q) = ENNReal.ofReal (c ^ n) * volume Q := by
  rw [(volume : Measure (Space n)).addHaar_smul_of_nonneg hc, finrank_euclideanSpace_fin]

/-- The inscribed-ball radius scales with the dilation: this is why `GetPrecision`
compares `γ` against the largest inscribed radius `γ̂` and returns
`⌈log₁₀(γ/γ̂)⌉`. -/
theorem ball_radius_scales {c r : ℝ} (hc : 0 < c) (Q : Set (Space n)) (z : Space n)
    (h : Metric.ball z r ⊆ Q) : Metric.ball (c • z) (c * r) ⊆ c • Q := by
  intro y hy
  refine ⟨c⁻¹ • y, h ?_, ?_⟩
  · have hd : ‖y - c • z‖ < c * r := by
      rw [← dist_eq_norm]; exact Metric.mem_ball.1 hy
    have hrw : c⁻¹ • y - z = c⁻¹ • (y - c • z) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul]
    rw [Metric.mem_ball, dist_eq_norm, hrw, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hc)]
    calc c⁻¹ * ‖y - c • z‖ < c⁻¹ * (c * r) := mul_lt_mul_of_pos_left hd (inv_pos.2 hc)
      _ = r := by field_simp
  · show c • c⁻¹ • y = y
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hc), one_smul]

/-- **`lem:lattice`.** If `lem:nonconv`'s two-sided bound holds for the dilate
`c·Q` against its integer-point count, then it holds for `Q` against its
fine-lattice count, divided by `cⁿ`.

`N` is `|Q ∩ 𝕃ⁿ| = |(c·Q) ∩ ℤⁿ|`, `volQ` is `vol Q`, and `volS = cⁿ · volQ` is
`vol (c·Q)`. With `c = 10^ρ` this is exactly the statement of `lem:lattice`. -/
theorem lattice_of_scaled {η N c volQ volS : ℝ} (hc : 0 < c)
    (hscale : volS = c ^ n * volQ)
    (hlow : (1 - η) * N ≤ volS) (hupp : volS ≤ (1 + η) * N) :
    (1 - η) / c ^ n * N ≤ volQ ∧ volQ ≤ (1 + η) / c ^ n * N := by
  have hcn : (0:ℝ) < c ^ n := pow_pos hc n
  constructor
  · rw [div_mul_eq_mul_div, div_le_iff₀ hcn]
    calc (1 - η) * N ≤ volS := hlow
      _ = c ^ n * volQ := hscale
      _ = volQ * c ^ n := by ring
  · rw [div_mul_eq_mul_div, le_div_iff₀ hcn]
    calc volQ * c ^ n = c ^ n * volQ := by ring
      _ = volS := hscale.symm
      _ ≤ (1 + η) * N := hupp

/-! ## `lem:lattice`, instantiated

Everything above is about free reals. This section fixes that: `Ttc.normalisedCount`
(`Model/Prelude`) is an actual normalised lattice count of the actual solution set,
and `lem:lattice` becomes a statement about `Ttc.volSol` — conditional only on
`lem:nonconv` for the dilate, which is itself about actual sets.
-/

theorem latticeScale_pos (ρ : ℤ) : 0 < latticeScale ρ := zpow_pos (by norm_num) ρ

theorem latticeScale_ne_zero (ρ : ℤ) : latticeScale ρ ≠ 0 := (latticeScale_pos ρ).ne'

/-- Dilating the solution set multiplies its volume by `10^(ρ·n)`. Holds with no
finiteness hypothesis: if the volume is infinite both sides are `0` after
`toReal`. -/
theorem volSol_smul {A : Type*} {n : ℕ} (M : A → Set (Space n)) (φ : BForm A) (ρ : ℤ) :
    (volume (latticeScale ρ • sol M φ)).toReal
      = (latticeScale ρ) ^ n * volSol M φ := by
  rw [volume_smul_body (latticeScale_pos ρ).le, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg (latticeScale_pos ρ).le n)]
  rfl

/-- The count of `𝕃ⁿ`-points of `Sol(F)` is the count of `ℤⁿ`-points of its
dilate — `Ttc.ncard_inter_lattice_smul` at the algorithm's scale. -/
theorem latticeCount_eq {A : Type*} {n : ℕ} (M : A → Set (Space n)) (φ : BForm A) (ρ : ℤ) :
    (latticeCount M φ ρ : ℝ)
      = (((latticeScale ρ • sol M φ) ∩ intLattice n).ncard : ℝ) := by
  rw [latticeCount, ncard_inter_lattice_smul (latticeScale_ne_zero ρ)]

/-- **`lem:lattice`, about the real objects.**

Given `lem:nonconv`'s two-sided bound for the dilate `10^ρ · Sol(F)` against its
integer-point count, the same bound holds for `Sol(F)` against
`Ttc.normalisedCount` — i.e. `|Sol(F) ∩ 𝕃ⁿ| / 10^(ρ·n)`.

This is the instantiation `lattice_of_scaled` was stated for: no free reals, no
`hscale` hypothesis (it is `Ttc.volSol_smul`), and `N` is a genuine lattice count
(`Ttc.latticeCount_eq`). -/
theorem lattice_bounds {A : Type*} {n : ℕ} (M : A → Set (Space n)) (φ : BForm A)
    (ρ : ℤ) {η : ℝ}
    (hlow : (1 - η) * (((latticeScale ρ • sol M φ) ∩ intLattice n).ncard : ℝ)
              ≤ (volume (latticeScale ρ • sol M φ)).toReal)
    (hupp : (volume (latticeScale ρ • sol M φ)).toReal
              ≤ (1 + η) * (((latticeScale ρ • sol M φ) ∩ intLattice n).ncard : ℝ)) :
    (1 - η) * normalisedCount M φ ρ ≤ volSol M φ ∧
      volSol M φ ≤ (1 + η) * normalisedCount M φ ρ := by
  obtain ⟨h1, h2⟩ :=
    lattice_of_scaled (n := n) (latticeScale_pos ρ) (volSol_smul M φ ρ) hlow hupp
  rw [normalisedCount, latticeCount_eq]
  constructor
  · calc (1 - η) * ((((latticeScale ρ • sol M φ) ∩ intLattice n).ncard : ℝ)
            / (latticeScale ρ) ^ n)
        = (1 - η) / (latticeScale ρ) ^ n
            * (((latticeScale ρ • sol M φ) ∩ intLattice n).ncard : ℝ) := by ring
      _ ≤ volSol M φ := h1
  · calc volSol M φ
        ≤ (1 + η) / (latticeScale ρ) ^ n
            * (((latticeScale ρ • sol M φ) ∩ intLattice n).ncard : ℝ) := h2
      _ = (1 + η) * ((((latticeScale ρ • sol M φ) ∩ intLattice n).ncard : ℝ)
            / (latticeScale ρ) ^ n) := by ring

end Ttc
