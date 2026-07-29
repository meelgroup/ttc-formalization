/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Internal.Nonconv

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

/-- The integer lattice inside `ℝⁿ`. -/
def intLattice (n : ℕ) : Set (Space n) := {x | ∀ i, ∃ k : ℤ, x i = (k : ℝ)}

/-- The refined lattice `𝕃ⁿ = c⁻¹ · ℤⁿ`; the algorithm uses `c = 10^ρ`. -/
def fineLattice (n : ℕ) (c : ℝ) : Set (Space n) := {x | ∀ i, ∃ k : ℤ, x i = c⁻¹ * (k : ℝ)}

@[simp]
theorem mem_intLattice {x : Space n} : x ∈ intLattice n ↔ ∀ i, ∃ k : ℤ, x i = (k : ℝ) :=
  Iff.rfl

@[simp]
theorem mem_fineLattice {c : ℝ} {x : Space n} :
    x ∈ fineLattice n c ↔ ∀ i, ∃ k : ℤ, x i = c⁻¹ * (k : ℝ) := Iff.rfl

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

end Ttc
