/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Ttc.Internal.Arith
import Ttc.Problem

/-!
# The geometry of `lem:nonconv`: inflating, deflating, and the scaling containment

`lem:nonconv` of the paper works with a finite family of polytopes
`P_i = {x | A_ij x ≤ b_ij}`, their **inflations** `P'_i` (offsets `b_ij + κ‖A_ij‖`)
and **deflations** `P''_i` (offsets `b_ij − κ‖A_ij‖`), and the scalar

  `k = max_{i,j} (b_ij + κ‖A_ij‖) / (b_ij − κ‖A_ij‖)`.

The geometric step of the proof is `Q' ⊆ k·Q''`, whence `vol Q' ≤ kⁿ · vol Q''`.
Both are proved here in full.

## Modelling

We index *all* facets of *all* polytopes by one type `F`, with `part : F → ι`
recording which polytope a facet belongs to. A facet carries a linear functional
`f j` (the paper's `x ↦ A_ij x`), an offset `b j`, and a nonnegative weight `w j`
(the paper's `‖A_ij‖`). Keeping `w` as a separate datum rather than literally
`‖A_ij‖` costs nothing and avoids inner-product bookkeeping: the argument only
uses linearity of `f j` and `0 ≤ w j`.

## Bug-oracle note: the inscribed ball must be centred at the origin

The paper derives the bound on `k` from "each `P_i` contains an `ℓ₂`-ball of radius
at least `γ`", concluding `b_ij ≥ γ‖A_ij‖`. That implication needs the ball to be
centred at the **origin**: a ball of radius `γ` centred at `c` only gives
`b_ij − A_ij c ≥ γ‖A_ij‖`. Since the scaling `x ↦ x/k` used in the proof is a
homothety about the origin, the argument genuinely requires the origin-centred
version (and, for a *union*, a common centre for all `P_i`). We therefore take
`γ * w j ≤ b j` as an explicit hypothesis (`facet_ratio_le`) and flag the gap.
-/

namespace Ttc

open MeasureTheory Set Pointwise

variable {n : ℕ} {ι F : Type*}

/-- A family of polytopes presented by facets. `part j` says which polytope facet
`j` belongs to, `f j` is the linear form `x ↦ A_ij x`, `b j` the offset, and `w j`
the weight `‖A_ij‖`. -/
structure FacetSystem (n : ℕ) (ι F : Type*) where
  /-- Which polytope each facet belongs to. -/
  part : F → ι
  /-- The linear form cutting out the facet. -/
  f : F → (Space n →ₗ[ℝ] ℝ)
  /-- The offset of the facet. -/
  b : F → ℝ
  /-- The weight `‖A_ij‖` by which the facet is displaced. -/
  w : F → ℝ
  /-- Weights are nonnegative (they are norms). -/
  w_nonneg : ∀ j, 0 ≤ w j

namespace FacetSystem

variable (S : FacetSystem n ι F)

/-- The polytope `P i` with offsets shifted by `t * w j`. `t = 0` gives `P i`,
`t = κ` gives the inflation `P' i`, `t = -κ` the deflation `P'' i`. -/
def piece (t : ℝ) (i : ι) : Set (Space n) :=
  {x | ∀ j, S.part j = i → S.f j x ≤ S.b j + t * S.w j}

/-- The union `Q` of the family, with offsets shifted by `t * w j`. -/
def body (t : ℝ) : Set (Space n) := ⋃ i, S.piece t i

@[simp]
theorem mem_piece {t : ℝ} {i : ι} {x : Space n} :
    x ∈ S.piece t i ↔ ∀ j, S.part j = i → S.f j x ≤ S.b j + t * S.w j := Iff.rfl

@[simp]
theorem mem_body {t : ℝ} {x : Space n} : x ∈ S.body t ↔ ∃ i, x ∈ S.piece t i := by
  simp [body]

/-- Shrinking the offsets shrinks the pieces: `P'' i ⊆ P i ⊆ P' i`. -/
theorem piece_mono {s t : ℝ} (h : s ≤ t) (i : ι) : S.piece s i ⊆ S.piece t i := by
  intro x hx j hj
  exact le_trans (hx j hj) (by nlinarith [S.w_nonneg j])

/-- Consequently `Q'' ⊆ Q ⊆ Q'`. -/
theorem body_mono {s t : ℝ} (h : s ≤ t) : S.body s ⊆ S.body t := by
  intro x hx
  obtain ⟨i, hi⟩ := S.mem_body.1 hx
  exact S.mem_body.2 ⟨i, S.piece_mono h i hi⟩

/-! ## The scaling containment `Q' ⊆ k · Q''` -/

/-- **The geometric step of `lem:nonconv`.** If every facet satisfies
`b j + κ w j ≤ k * (b j − κ w j)` then the inflated body is contained in the
`k`-dilate of the deflated body.

This is the paper's "`p ∈ Q'` implies `p/k ∈ Q''`, hence `Q' ⊆ kQ''`". -/
theorem inflated_subset_smul_deflated {κ k : ℝ} (hk : 0 < k)
    (hfacet : ∀ j, S.b j + κ * S.w j ≤ k * (S.b j - κ * S.w j)) :
    S.body κ ⊆ k • S.body (-κ) := by
  intro x hx
  obtain ⟨i, hi⟩ := S.mem_body.1 hx
  refine ⟨k⁻¹ • x, S.mem_body.2 ⟨i, ?_⟩, ?_⟩
  · intro j hj
    have hlin : S.f j (k⁻¹ • x) = k⁻¹ * S.f j x := by
      rw [map_smul]; rfl
    have hx' : S.f j x ≤ S.b j + κ * S.w j := hi j hj
    have hkey : S.f j x ≤ k * (S.b j - κ * S.w j) := le_trans hx' (hfacet j)
    rw [hlin]
    have : k⁻¹ * S.f j x ≤ k⁻¹ * (k * (S.b j - κ * S.w j)) := by
      exact mul_le_mul_of_nonneg_left hkey (by positivity)
    calc k⁻¹ * S.f j x ≤ k⁻¹ * (k * (S.b j - κ * S.w j)) := this
      _ = S.b j - κ * S.w j := by field_simp
      _ = S.b j + (-κ) * S.w j := by ring
  · show k • k⁻¹ • x = x
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hk), one_smul]

/-- **`vol Q' ≤ kⁿ · vol Q''`.** The measure-theoretic consequence of the scaling
containment, using that Lebesgue measure on `ℝⁿ` scales by `kⁿ` under dilation. -/
theorem volume_inflated_le {κ k : ℝ} (hk : 0 < k)
    (hfacet : ∀ j, S.b j + κ * S.w j ≤ k * (S.b j - κ * S.w j)) :
    volume (S.body κ) ≤ ENNReal.ofReal (k ^ n) * volume (S.body (-κ)) := by
  have hsub := S.inflated_subset_smul_deflated hk hfacet
  have hmono := measure_mono (μ := (volume : Measure (Space n))) hsub
  rwa [(volume : Measure (Space n)).addHaar_smul_of_nonneg (le_of_lt hk),
    finrank_euclideanSpace_fin] at hmono

/-! ## Bounding `k` from an origin-centred inscribed ball -/

end FacetSystem

/-- If `γ * w ≤ b` (the origin-centred inscribed-ball condition for one facet) and
`0 ≤ κ < γ`, then that facet satisfies the ratio bound with
`k = (γ + κ)/(γ − κ)`. -/
theorem facet_ratio_le {γ κ b w : ℝ} (hw : 0 ≤ w) (hκ : 0 ≤ κ) (hκγ : κ < γ)
    (hb : γ * w ≤ b) :
    b + κ * w ≤ ((γ + κ) / (γ - κ)) * (b - κ * w) := by
  have hγκ : (0:ℝ) < γ - κ := by linarith
  have hγ : 0 < γ := lt_of_le_of_lt hκ hκγ
  have hbw : κ * w ≤ γ * w := by nlinarith
  have hpos : 0 ≤ b - κ * w := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hγκ]
  nlinarith

/-- **The per-facet ratio is *antitone* in the facet's distance from the origin.**

Writing `t = b/‖A‖` for the (signed) distance from the origin to the facet, the
quantity the paper maximises is `(t + κ)/(t − κ)`, which is *decreasing* in `t` on
`(κ, ∞)`. So the `max` defining `k` is attained at the facet **nearest** the
origin, not the farthest — and bounding `k` *above* therefore requires the
inscribed-radius hypothesis at **every** facet, equivalently at the nearest one. -/
theorem ratio_antitone {κ s t : ℝ} (hκ : 0 ≤ κ) (hs : κ < s) (hst : s ≤ t) :
    (t + κ) / (t - κ) ≤ (s + κ) / (s - κ) := by
  have h1 : (0:ℝ) < s - κ := by linarith
  have h2 : (0:ℝ) < t - κ := by linarith
  rw [div_le_div_iff₀ h2 h1]
  nlinarith

/-- **The hypothesis really is needed at every facet.** If even one facet lies at
distance strictly between `κ` and `γ` from the origin, the per-facet inequality
required by `Ttc.FacetSystem.inflated_subset_smul_deflated` *fails* at that facet
— so knowing `γ·w ≤ b` only at the farthest facet is not enough.

The proof needs neither `0 < w` nor `κ·w < b`: the inequality fails for *every*
facet with `b < γ·w`. Those binders are kept only to name the intended regime. -/
theorem facet_ratio_fails {γ κ b w : ℝ} (_hw : 0 < w) (hκ : 0 < κ) (hκγ : κ < γ)
    (_hlo : κ * w < b) (hhi : b < γ * w) :
    ((γ + κ) / (γ - κ)) * (b - κ * w) < b + κ * w := by
  have hγκ : (0:ℝ) < γ - κ := by linarith
  rw [div_mul_eq_mul_div, div_lt_iff₀ hγκ]
  nlinarith

/-- The uniform version: an origin-centred ball of radius `γ` inside every polytope
of the family yields the facet hypothesis of
`Ttc.FacetSystem.inflated_subset_smul_deflated` with `k = (γ + κ)/(γ − κ)`. -/
theorem FacetSystem.facet_bound_of_ball (S : FacetSystem n ι F) {γ κ : ℝ}
    (hκ : 0 ≤ κ) (hκγ : κ < γ) (hball : ∀ j, γ * S.w j ≤ S.b j) (j : F) :
    S.b j + κ * S.w j ≤ ((γ + κ) / (γ - κ)) * (S.b j - κ * S.w j) :=
  facet_ratio_le (S.w_nonneg j) hκ hκγ (hball j)

/-- `k = (γ + κ)/(γ − κ)` is positive when `0 ≤ κ < γ`. -/
theorem ratio_pos {γ κ : ℝ} (hκ : 0 ≤ κ) (hκγ : κ < γ) : 0 < (γ + κ) / (γ - κ) := by
  have : (0:ℝ) < γ := lt_of_le_of_lt hκ hκγ
  apply div_pos <;> linarith

/-- **The geometric half of `lem:nonconv`, assembled.** Under the origin-centred
inscribed-ball hypothesis with the paper's radius `γ = (16n/η)√(log(4r/η))` and
displacement `κ ≤ 2√(log(4r/η))`, the inflated body's volume exceeds the deflated
body's by at most the factor `(1 + η/4)/(1 − η/4)` of `claim:helper`. -/
theorem FacetSystem.volume_inflated_le_helper (S : FacetSystem n ι F) {η κ L : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hn : 1 ≤ n) (hL : 0 < L)
    (hκ0 : 0 ≤ κ) (hκle : κ ≤ 2 * Real.sqrt L)
    (hball : ∀ j, ((16 * n / η) * Real.sqrt L) * S.w j ≤ S.b j) :
    volume (S.body κ) ≤
      ENNReal.ofReal ((1 + η / 4) / (1 - η / 4)) * volume (S.body (-κ)) := by
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  set γ : ℝ := (16 * n / η) * Real.sqrt L with hγdef
  have hcpos : (16:ℝ) ≤ 16 * n / η := by rw [le_div_iff₀ hη]; nlinarith
  have hκγ : κ < γ := by
    have : 2 * Real.sqrt L < γ := by
      rw [hγdef]; exact mul_lt_mul_of_pos_right (by linarith) hsL
    linarith
  have hkpos : 0 < (γ + κ) / (γ - κ) := ratio_pos hκ0 hκγ
  refine le_trans (S.volume_inflated_le hkpos
    (S.facet_bound_of_ball hκ0 hκγ hball)) ?_
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (claim_helper_of hη hη1 hn hL hκ0 hκle)) le_rfl

end Ttc
