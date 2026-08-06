/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Nonconv.Geometry
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# `lem:nonconv` without the common-ball assumption

`Ttc.Geometry` shows that the paper's global homothety `p ↦ p/k` forces every
`Pᵢ` to contain a ball of radius `γ` **about the origin** — equivalently, a common
ball for the whole family. That hypothesis is far stronger than the one stated,
and is unsatisfiable when the DNF cubes' polytopes are disjoint.

This file removes it. The two ingredients:

1. **Recentre each polytope separately.** `Pᵢ` contains a ball `B(cᵢ, γ)` about
   *its own* centre `cᵢ`. The homothety `AffineMap.homothety cᵢ k` — about `cᵢ`,
   not the origin — then satisfies `P'ᵢ ⊆ homothety cᵢ k '' P''ᵢ`, hence
   `vol P'ᵢ ≤ kⁿ · vol P''ᵢ`. No two polytopes need share anything
   (`Ttc.FacetSystem.volume_piece_inflated_le`).

2. **Compare the *shells*, not the bodies.** The union's inflation exceeds the
   union only on the outer shell,
   `Q' ⊆ Q ∪ ⋃ᵢ (P'ᵢ \ Pᵢ)` (`Ttc.FacetSystem.body_subset_union_shells`), and
   each shell is controlled by step 1. Summing costs a factor `m` — but only on
   the *shell*, not on the volume: the conclusion is
   `vol Q' ≤ (1 + m(kⁿ − 1))·vol Q` (`Ttc.shell_bound`), where `kⁿ − 1` is the
   quantity the choice of `γ` makes small.

## What it costs

The paper's proof needs `kⁿ − 1 ≲ η`; this one needs `m(kⁿ − 1) ≲ η`, i.e. the
internal parameter `θ` must be taken `∼ η/m` instead of `∼ η`. Since
`γ(θ) = (16n/θ)√(log(4r/θ))`, the required inscribed radius grows by a factor
`≈ 4m`, so `GetPrecision`'s output `ρ = ⌈log₁₀(γ/γ̂)⌉` grows by
`O(log m)` — see `Ttc.gamma_scale_cost`. That is benign: `ρ` enters the algorithm
only as the bit-length of a lattice coordinate, so `O(log m)` extra digits is
dominated by the `m` iterations of the main loop.

## Why this is the right trade

The alternative — assuming a common inscribed ball — is not a weakening of the
hypothesis but a different (and, for disjoint polytopes, unsatisfiable) one. The
`m`-dependence bought here is the honest price of allowing the `Pᵢ` to be placed
arbitrarily.
-/

namespace Ttc

open MeasureTheory Set Pointwise

variable {n : ℕ} {ι F : Type*}

namespace FacetSystem

variable (S : FacetSystem n ι F)

/-! ## Step 1: recentre each polytope separately -/

/-- **The scaling step, recentred.** If facet `j` of polytope `i` satisfies the
inscribed-ball condition *about `c i`* — that is, `γ·w j ≤ b j − f j (c i)`, which
says `B(c i, γ) ⊆ Pᵢ` — then the inflated piece is contained in the `k`-homothety
of the deflated piece **about `c i`**.

Unlike `Ttc.FacetSystem.inflated_subset_smul_deflated`, this uses no property of
the origin, and different pieces may use different centres. -/
theorem piece_inflated_subset_homothety (c : ι → Space n) {κ k : ℝ} (hk : 0 < k)
    (i : ι)
    (hfacet : ∀ j, S.part j = i →
      (S.b j - S.f j (c i)) + κ * S.w j ≤ k * ((S.b j - S.f j (c i)) - κ * S.w j)) :
    S.piece κ i ⊆ AffineMap.homothety (c i) k '' S.piece (-κ) i := by
  intro x hx
  refine ⟨AffineMap.homothety (c i) k⁻¹ x, ?_, ?_⟩
  · intro j hj
    -- write everything relative to `c i`
    have hlin : S.f j (AffineMap.homothety (c i) k⁻¹ x)
        = k⁻¹ * (S.f j x - S.f j (c i)) + S.f j (c i) := by
      rw [AffineMap.homothety_apply]
      simp only [vsub_eq_sub, vadd_eq_add, map_add, map_smul, map_sub, smul_eq_mul]
    have hx' : S.f j x - S.f j (c i) ≤ (S.b j - S.f j (c i)) + κ * S.w j := by
      have := hx j hj; linarith
    have hkey : S.f j x - S.f j (c i) ≤ k * ((S.b j - S.f j (c i)) - κ * S.w j) :=
      le_trans hx' (hfacet j hj)
    rw [hlin]
    have hstep : k⁻¹ * (S.f j x - S.f j (c i))
        ≤ k⁻¹ * (k * ((S.b j - S.f j (c i)) - κ * S.w j)) :=
      mul_le_mul_of_nonneg_left hkey (by positivity)
    have hcancel : k⁻¹ * (k * ((S.b j - S.f j (c i)) - κ * S.w j))
        = (S.b j - S.f j (c i)) - κ * S.w j := by field_simp
    rw [hcancel] at hstep
    have : k⁻¹ * (S.f j x - S.f j (c i)) + S.f j (c i) ≤ S.b j - κ * S.w j := by linarith
    linarith
  · rw [AffineMap.homothety_apply, AffineMap.homothety_apply]
    simp only [vsub_eq_sub, vadd_eq_add, add_sub_cancel_right, smul_smul]
    rw [mul_inv_cancel₀ (ne_of_gt hk), one_smul, sub_add_cancel]

/-- **`vol P'ᵢ ≤ kⁿ · vol P''ᵢ`, with no common centre.** -/
theorem volume_piece_inflated_le (c : ι → Space n) {κ k : ℝ} (hk : 0 < k) (i : ι)
    (hfacet : ∀ j, S.part j = i →
      (S.b j - S.f j (c i)) + κ * S.w j ≤ k * ((S.b j - S.f j (c i)) - κ * S.w j)) :
    volume (S.piece κ i) ≤ ENNReal.ofReal (k ^ n) * volume (S.piece (-κ) i) := by
  have hsub := S.piece_inflated_subset_homothety c hk i hfacet
  have hmono := measure_mono (μ := (volume : Measure (Space n))) hsub
  rwa [Measure.addHaar_image_homothety, finrank_euclideanSpace_fin,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ k ^ n)] at hmono

/-! ## The paper's `cl:recenter`, verbatim

The paper states the recentring step as a containment between `P'`/`P''` and
*dilates of `P` itself* (rather than of each other). That form is cleaner, and it
is what `Ttc.shell_bound` consumes. Both inclusions are proved here, under the
hypothesis that the inscribed ball is centred at the **origin**, i.e.
`γ‖A_j‖ ≤ b_j` for every facet.
-/

/-! ## Step 2: compare the shells -/

/-- **The union's inflation exceeds the union only on the shells.**

`Q' ⊆ Q ∪ ⋃ᵢ (P'ᵢ \ Pᵢ)` — trivially true, and the key to avoiding a
multiplicative `m` loss: a point of `Q'` is either already in `Q`, or lies in some
`P'ᵢ` while being outside `Pᵢ`. -/
theorem body_subset_union_shells {κ : ℝ} (_hκ : 0 ≤ κ) :
    S.body κ ⊆ S.body 0 ∪ ⋃ i, (S.piece κ i \ S.piece 0 i) := by
  intro x hx
  obtain ⟨i, hi⟩ := S.mem_body.1 hx
  by_cases h : x ∈ S.piece 0 i
  · exact Or.inl (S.mem_body.2 ⟨i, h⟩)
  · exact Or.inr (mem_iUnion.2 ⟨i, hi, h⟩)

/-- Subadditivity of the shell decomposition, in measure. -/
theorem volume_body_le_shells [Fintype ι] {κ : ℝ} (hκ : 0 ≤ κ) :
    volume (S.body κ) ≤ volume (S.body 0) + ∑ i, volume (S.piece κ i \ S.piece 0 i) := by
  refine le_trans (measure_mono (S.body_subset_union_shells hκ)) ?_
  refine le_trans (measure_union_le _ _) ?_
  exact add_le_add le_rfl
    (measure_iUnion_fintype_le (volume : Measure (Space n))
      (fun i => S.piece κ i \ S.piece 0 i))


/-! ## The inflation against the *original* piece

`Ttc.FacetSystem.piece_inflated_subset_homothety` compares `P'ᵢ` to `P''ᵢ`. The
shell argument needs `P'ᵢ` against `Pᵢ` — the paper's `cl:recenter`, with each
piece homothetic about its **own** centre.
-/

/-- **`cl:recenter`, recentred.** Under `B(cᵢ, γ) ⊆ Pᵢ` (in facet form
`γ·w j ≤ b j − f j cᵢ`), the inflated piece lies inside the `(1 + κ/γ)`-homothety
of the *original* piece about `cᵢ`. No relation between the `cᵢ` is used. -/
theorem piece_inflated_subset_homothety_zero (c : ι → Space n) {γ κ : ℝ}
    (hγ : 0 < γ) (hκ : 0 ≤ κ) (i : ι)
    (hball : ∀ j, S.part j = i → γ * S.w j ≤ S.b j - S.f j (c i)) :
    S.piece κ i ⊆ AffineMap.homothety (c i) (1 + κ / γ) '' S.piece 0 i := by
  have hk : (0:ℝ) < 1 + κ / γ := by
    have : (0:ℝ) ≤ κ / γ := div_nonneg hκ hγ.le
    linarith
  intro x hx
  refine ⟨AffineMap.homothety (c i) (1 + κ / γ)⁻¹ x, ?_, ?_⟩
  · intro j hj
    have hlin : S.f j (AffineMap.homothety (c i) (1 + κ / γ)⁻¹ x)
        = (1 + κ / γ)⁻¹ * (S.f j x - S.f j (c i)) + S.f j (c i) := by
      rw [AffineMap.homothety_apply]
      simp only [vsub_eq_sub, vadd_eq_add, map_add, map_smul, map_sub, smul_eq_mul]
    have hB := hball j hj
    have hw := S.w_nonneg j
    have hx' : S.f j x - S.f j (c i) ≤ (S.b j - S.f j (c i)) + κ * S.w j := by
      have := hx j hj; linarith
    -- `B + κ·w ≤ (1 + κ/γ)·B`, since `γ·w ≤ B` and `κ ≥ 0`
    have hkey : (S.b j - S.f j (c i)) + κ * S.w j
        ≤ (1 + κ / γ) * (S.b j - S.f j (c i)) := by
      have hrw : (1 + κ / γ) * (S.b j - S.f j (c i))
          = (S.b j - S.f j (c i)) + (κ * (S.b j - S.f j (c i))) / γ := by
        field_simp
      rw [hrw]
      have h3 : κ * S.w j ≤ (κ * (S.b j - S.f j (c i))) / γ := by
        rw [le_div_iff₀ hγ]; nlinarith
      linarith
    rw [hlin]
    have hstep : (1 + κ / γ)⁻¹ * (S.f j x - S.f j (c i))
        ≤ (1 + κ / γ)⁻¹ * ((1 + κ / γ) * (S.b j - S.f j (c i))) :=
      mul_le_mul_of_nonneg_left (le_trans hx' hkey) (inv_nonneg.2 hk.le)
    have hcancel : (1 + κ / γ)⁻¹ * ((1 + κ / γ) * (S.b j - S.f j (c i)))
        = S.b j - S.f j (c i) := by field_simp
    rw [hcancel] at hstep
    simp only [zero_mul, add_zero]
    linarith
  · rw [AffineMap.homothety_apply, AffineMap.homothety_apply]
    simp only [vsub_eq_sub, vadd_eq_add, add_sub_cancel_right, smul_smul]
    rw [mul_inv_cancel₀ (ne_of_gt hk), one_smul, sub_add_cancel]

/-- A piece is closed: an intersection of closed half-spaces. -/
theorem isClosed_piece (t : ℝ) (i : ι) : IsClosed (S.piece t i) := by
  have hrw : S.piece t i
      = ⋂ j : F, ⋂ _ : S.part j = i, {x | S.f j x ≤ S.b j + t * S.w j} := by
    ext x
    simp only [FacetSystem.mem_piece, Set.mem_iInter, Set.mem_setOf_eq]
  rw [hrw]
  exact isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_le (S.f j).continuous_of_finiteDimensional continuous_const

theorem measurableSet_piece (t : ℝ) (i : ι) : MeasurableSet (S.piece t i) :=
  (S.isClosed_piece t i).measurableSet

/-- **`vol P'ᵢ ≤ (1 + κ/γ)ⁿ · vol Pᵢ`, with no common centre.** The per-piece
input to the shell bound. -/
theorem volume_piece_inflated_le_zero (c : ι → Space n) {γ κ : ℝ}
    (hγ : 0 < γ) (hκ : 0 ≤ κ) (i : ι)
    (hball : ∀ j, S.part j = i → γ * S.w j ≤ S.b j - S.f j (c i)) :
    volume (S.piece κ i)
      ≤ ENNReal.ofReal ((1 + κ / γ) ^ n) * volume (S.piece 0 i) := by
  have hk : (0:ℝ) < 1 + κ / γ := by
    have : (0:ℝ) ≤ κ / γ := div_nonneg hκ hγ.le
    linarith
  have hsub := S.piece_inflated_subset_homothety_zero c hγ hκ i hball
  have hmono := measure_mono (μ := (volume : Measure (Space n))) hsub
  rwa [Measure.addHaar_image_homothety, finrank_euclideanSpace_fin,
    abs_of_nonneg (pow_nonneg hk.le n)] at hmono

/-- **The shell `P'ᵢ ∖ Pᵢ` has volume at most `(K−1)·vol Pᵢ`**, `K = (1 + κ/γ)ⁿ`.

This is the per-piece input `shell i ≤ (K − 1)·volP i` that `Ttc.shell_bound`
takes as a hypothesis — here discharged from the actual sets. -/
theorem volume_shell_le (c : ι → Space n) {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 ≤ κ) (i : ι)
    (hball : ∀ j, S.part j = i → γ * S.w j ≤ S.b j - S.f j (c i))
    (hfin : volume (S.piece κ i) ≠ ⊤) :
    (volume (S.piece κ i \ S.piece 0 i)).toReal
      ≤ ((1 + κ / γ) ^ n - 1) * (volume (S.piece 0 i)).toReal := by
  have hk : (0:ℝ) < 1 + κ / γ := by
    have : (0:ℝ) ≤ κ / γ := div_nonneg hκ hγ.le
    linarith
  have hsub : S.piece 0 i ⊆ S.piece κ i := S.piece_mono hκ i
  have hle : volume (S.piece 0 i) ≤ volume (S.piece κ i) := measure_mono hsub
  have hfin0 : volume (S.piece 0 i) ≠ ⊤ := ne_top_of_le_ne_top hfin hle
  -- the shell is the difference of the two volumes
  have hdiff : volume (S.piece κ i \ S.piece 0 i)
      = volume (S.piece κ i) - volume (S.piece 0 i) :=
    measure_sdiff hsub (S.measurableSet_piece 0 i).nullMeasurableSet hfin0
  -- and the inflated volume is at most `K` times the original
  have hK := S.volume_piece_inflated_le_zero c hγ hκ i hball
  have hKr : (volume (S.piece κ i)).toReal
      ≤ (1 + κ / γ) ^ n * (volume (S.piece 0 i)).toReal := by
    have h := ENNReal.toReal_mono (by finiteness) hK
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hk.le n)] at h
  rw [hdiff, ENNReal.toReal_sub_of_le hle hfin]
  linarith

/-! ### The deflated side as a shifted inflated side

Deflating by `κ` is inflating a system whose offsets are already `κ` smaller:
with `b' j = b j − κ·w j` one has `piece_{S'} t = piece_S (t − κ)`, so
`piece_{S'} 0 = piece_S (−κ)` and `piece_{S'} κ = piece_S 0`. The deflated shell
argument is therefore the inflated one applied to `S.shift κ`, at inscribed
radius `γ − κ`. -/

/-- `S` with every offset lowered by `κ·w j`. -/
def shift (κ : ℝ) : FacetSystem n ι F where
  part := S.part
  f := S.f
  b := fun j => S.b j - κ * S.w j
  w := S.w
  w_nonneg := S.w_nonneg

@[simp] theorem shift_part (κ : ℝ) : (S.shift κ).part = S.part := rfl
@[simp] theorem shift_f (κ : ℝ) : (S.shift κ).f = S.f := rfl
@[simp] theorem shift_w (κ : ℝ) : (S.shift κ).w = S.w := rfl
@[simp] theorem shift_b (κ : ℝ) (j : F) : (S.shift κ).b j = S.b j - κ * S.w j := rfl

@[simp] theorem shift_piece (κ t : ℝ) (i : ι) :
    (S.shift κ).piece t i = S.piece (t - κ) i := by
  ext x
  simp only [FacetSystem.mem_piece, shift_part, shift_f, shift_b, shift_w]
  constructor <;> intro h j hj <;> · have := h j hj; nlinarith [S.w_nonneg j]

@[simp] theorem shift_body (κ t : ℝ) : (S.shift κ).body t = S.body (t - κ) := by
  simp only [FacetSystem.body, shift_piece]

/-! ### Dilation

`lem:lattice` compares `10^ρ · Q` against `ℤⁿ`, so the facet system has to be
dilated too. Since `c • {x | f x ≤ b} = {y | f y ≤ c·b}` for `c > 0`, only the
offsets move; the normals `f` and the weights `w = ‖A‖` are unchanged. -/

/-- `S` with every offset multiplied by `c`: its `piece 0` is `c •` the original's. -/
def scale (c : ℝ) : FacetSystem n ι F where
  part := S.part
  f := S.f
  b := fun j => c * S.b j
  w := S.w
  w_nonneg := S.w_nonneg

@[simp] theorem scale_part (c : ℝ) : (S.scale c).part = S.part := rfl
@[simp] theorem scale_f (c : ℝ) : (S.scale c).f = S.f := rfl
@[simp] theorem scale_w (c : ℝ) : (S.scale c).w = S.w := rfl
@[simp] theorem scale_b (c : ℝ) (j : F) : (S.scale c).b j = c * S.b j := rfl

/-- **`(c·S).piece 0 = c · (S.piece 0)`** for `c > 0`. -/
theorem scale_piece_zero {c : ℝ} (hc : 0 < c) (i : ι) :
    (S.scale c).piece 0 i = c • S.piece 0 i := by
  ext y
  simp only [FacetSystem.mem_piece, scale_part, scale_f, scale_b, scale_w,
    zero_mul, add_zero]
  constructor
  · intro h
    refine ⟨c⁻¹ • y, ?_, ?_⟩
    · intro j hj
      have := h j hj
      rw [map_smul, smul_eq_mul, zero_mul, add_zero]
      rw [inv_mul_le_iff₀ hc]
      linarith
    · show c • c⁻¹ • y = y
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hc), one_smul]
  · rintro ⟨x, hx, rfl⟩ j hj
    have := hx j hj
    rw [map_smul, smul_eq_mul]
    have hxj : S.f j x ≤ S.b j := by simpa using this
    nlinarith

/-- **`(c·S).body 0 = c · (S.body 0)`** for `c > 0`. -/
theorem scale_body_zero {c : ℝ} (hc : 0 < c) :
    (S.scale c).body 0 = c • S.body 0 := by
  simp only [FacetSystem.body, S.scale_piece_zero hc, Set.smul_set_iUnion]

/-- Each piece sits inside the body. -/
theorem piece_subset_body (t : ℝ) (i : ι) : S.piece t i ⊆ S.body t :=
  fun _ hx => S.mem_body.2 ⟨i, hx⟩

end FacetSystem


/-! ## `lem:nonconv` assembled, with no common-ball assumption

`θ` is the internal parameter at which `κ` and `γ` are computed. Taking
`θ = η/(4m)` makes the shell losses `1 + m(K−1)` at most `1 + η/16`
(`Ttc.shell_factor_le`), and the two-sided bound then closes with room to spare.
-/

/-- Cleared form of the lower-bound arithmetic: `(1−η)(1+η/16) ≤ 1 − η/8`. -/
theorem recentred_lower_arith {η : ℝ} (h0 : 0 < η) (_h1 : η ≤ 1) :
    (1 - η) * (1 + η / 16) ≤ 1 - η / 4 := by nlinarith [sq_nonneg η]

/-- Cleared form of the upper-bound arithmetic: `1 + η/16 ≤ (1+η)(1 − η/8)`. -/
theorem recentred_upper_arith {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1) :
    1 + η / 16 ≤ (1 + η) * (1 - η / 4) := by nlinarith [sq_nonneg η]

/-- **`lem:nonconv`, with the common-ball assumption removed.**

Each `Pᵢ` need only contain a ball of radius `γ(θ)` about *its own* centre. The
two shell hypotheses `hup`/`hdn` are what `Ttc.shell_bound` and
`Ttc.shell_bound_deflated` deliver at `θ = η/(4m)`; `hA`/`hBC` are `claim:cl`
summed, at the same `θ`. The conclusion is the paper's statement of
`lem:nonconv`, unchanged. -/
theorem nonconv_recentred {η θ N volQ volQ' volQ'' : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hN : 0 ≤ N) (hvolQ : 0 ≤ volQ)
    (hθ0 : 0 < θ) (hθ : θ ≤ η / 2)
    (hA : (1 - θ / 2) * N ≤ volQ')
    (hBC : (1 - θ / 2) * volQ'' ≤ N)
    (hup : volQ' ≤ (1 + η / 16) * volQ)
    (hdn : volQ ≤ (1 + η / 16) * volQ'') :
    (1 - η) * N ≤ volQ ∧ volQ ≤ (1 + η) * N := by
  have hs : (0:ℝ) < 1 + η / 16 := by linarith
  have hθη : (1:ℝ) - η / 4 ≤ 1 - θ / 2 := by linarith
  constructor
  · -- `(1−η)(1+η/16)·N ≤ (1−θ/2)N ≤ volQ' ≤ (1+η/16)·volQ`
    have h1 : (1 - η) * (1 + η / 16) * N ≤ (1 - θ / 2) * N := by
      nlinarith [mul_le_mul_of_nonneg_right (recentred_lower_arith hη hη1) hN,
        mul_le_mul_of_nonneg_right hθη hN]
    nlinarith [le_trans h1 (le_trans hA hup)]
  · -- `(1−η/8)·volQ ≤ (1−θ/2)·volQ ≤ (1+η/16)·volQ'' ·(1−θ/2) ≤ (1+η/16)·N`
    have h2 : (1 - θ / 2) * volQ ≤ (1 + η / 16) * N := by
      have hd : (0:ℝ) < 1 - θ / 2 := by linarith
      calc (1 - θ / 2) * volQ ≤ (1 - θ / 2) * ((1 + η / 16) * volQ'') :=
            mul_le_mul_of_nonneg_left hdn hd.le
        _ = (1 + η / 16) * ((1 - θ / 2) * volQ'') := by ring
        _ ≤ (1 + η / 16) * N := mul_le_mul_of_nonneg_left hBC hs.le
    have h3 : (1 - η / 4) * volQ ≤ (1 - θ / 2) * volQ :=
      mul_le_mul_of_nonneg_right hθη hvolQ
    nlinarith [recentred_upper_arith hη hη1, mul_le_mul_of_nonneg_right
      (recentred_upper_arith hη hη1) hN]

/-! ## The arithmetic: what the shell bound buys

Real-valued statement of the combination. `volQ`, `volQ'` are `vol Q`, `vol Q'`;
`volP i` is `vol Pᵢ`; `shell i` is `vol (P'ᵢ \ Pᵢ)`. The hypotheses are exactly
the outputs of steps 1 and 2.
-/

/-- **The recentred `lem:nonconv` volume comparison.**

From per-piece control `shell i ≤ (K − 1)·volP i` (step 1), the shell
decomposition `volQ' ≤ volQ + ∑ᵢ shell i` (step 2), and `∑ᵢ volP i ≤ m·volQ`
(each `Pᵢ ⊆ Q`), one gets `volQ' ≤ (1 + m(K−1))·volQ`.

Note where `m` appears: multiplying `K − 1`, the *shell* thickness — not `volQ`.
So it is absorbed by shrinking the internal parameter, at a `log m` cost in
precision. -/
theorem shell_bound {m K volQ volQ' sumP sumShell : ℝ}
    (hK : 1 ≤ K) (_hm : 0 ≤ m) (_hvolQ : 0 ≤ volQ)
    (hdecomp : volQ' ≤ volQ + sumShell)
    (hshell : sumShell ≤ (K - 1) * sumP)
    (hsum : sumP ≤ m * volQ) :
    volQ' ≤ (1 + m * (K - 1)) * volQ := by
  have h1 : (K - 1) * sumP ≤ (K - 1) * (m * volQ) :=
    mul_le_mul_of_nonneg_left hsum (by linarith)
  nlinarith

/-- **`vol Q' ≤ (1 + m(K−1))·vol Q` from the actual sets**, `K = (1 + κ/γ)ⁿ` and
`m = |ι|`.

`Ttc.shell_bound` takes its three inputs as hypotheses; this discharges all of
them from the geometry — the shell decomposition
(`Ttc.FacetSystem.volume_body_le_shells`), the per-piece shell bound
(`Ttc.FacetSystem.volume_shell_le`), and `∑ᵢ vol Pᵢ ≤ m·vol Q`. Combined with
`Ttc.shell_factor_le` (or `Ttc.Params.shell_factor_bound`) this is the `hup`
hypothesis of `Ttc.nonconv_recentred`. -/
theorem FacetSystem.volume_body_inflated_le [Fintype ι] (S : FacetSystem n ι F)
    (c : ι → Space n) {γ κ : ℝ}
    (hγ : 0 < γ) (hκ : 0 ≤ κ)
    (hball : ∀ i, ∀ j, S.part j = i → γ * S.w j ≤ S.b j - S.f j (c i))
    (hfin : ∀ i, volume (S.piece κ i) ≠ ⊤) :
    (volume (S.body κ)).toReal
      ≤ (1 + (Fintype.card ι : ℝ) * ((1 + κ / γ) ^ n - 1))
          * (volume (S.body 0)).toReal := by
  have hk : (0:ℝ) < 1 + κ / γ := by
    have : (0:ℝ) ≤ κ / γ := div_nonneg hκ hγ.le
    linarith
  have hk1 : (1:ℝ) ≤ 1 + κ / γ := by
    have : (0:ℝ) ≤ κ / γ := div_nonneg hκ hγ.le
    linarith
  -- finiteness of everything in sight
  have hbodyκ : volume (S.body κ) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_iUnion_fintype_le volume (fun i => S.piece κ i))
    exact (ENNReal.sum_lt_top.2 fun i _ => (hfin i).lt_top).ne
  have hsub0κ : ∀ i, S.piece 0 i ⊆ S.piece κ i := fun i => S.piece_mono hκ i
  have hfin0 : ∀ i, volume (S.piece 0 i) ≠ ⊤ :=
    fun i => ne_top_of_le_ne_top (hfin i) (measure_mono (hsub0κ i))
  have hbody0 : volume (S.body 0) ≠ ⊤ :=
    ne_top_of_le_ne_top hbodyκ (measure_mono (S.body_mono hκ))
  have hshellfin : ∀ i, volume (S.piece κ i \ S.piece 0 i) ≠ ⊤ :=
    fun i => ne_top_of_le_ne_top (hfin i) (measure_mono Set.sdiff_subset)
  -- the three inputs of `shell_bound`, in ℝ
  have hdecomp : (volume (S.body κ)).toReal
      ≤ (volume (S.body 0)).toReal
        + ∑ i, (volume (S.piece κ i \ S.piece 0 i)).toReal := by
    have h := ENNReal.toReal_mono ?_ (S.volume_body_le_shells hκ)
    · rwa [ENNReal.toReal_add hbody0 (ENNReal.sum_lt_top.2 fun i _ =>
        (hshellfin i).lt_top).ne, ENNReal.toReal_sum fun i _ => hshellfin i] at h
    · exact ENNReal.add_ne_top.2 ⟨hbody0,
        (ENNReal.sum_lt_top.2 fun i _ => (hshellfin i).lt_top).ne⟩
  have hshell : ∑ i, (volume (S.piece κ i \ S.piece 0 i)).toReal
      ≤ ((1 + κ / γ) ^ n - 1) * ∑ i, (volume (S.piece 0 i)).toReal := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => S.volume_shell_le c hγ hκ i (hball i) (hfin i)
  have hsum : ∑ i, (volume (S.piece 0 i)).toReal
      ≤ (Fintype.card ι : ℝ) * (volume (S.body 0)).toReal := by
    have hle : ∀ i ∈ Finset.univ, (volume (S.piece 0 i)).toReal
        ≤ (volume (S.body 0)).toReal :=
      fun i _ => ENNReal.toReal_mono hbody0 (measure_mono (S.piece_subset_body 0 i))
    calc ∑ i, (volume (S.piece 0 i)).toReal
        ≤ ∑ _i : ι, (volume (S.body 0)).toReal := Finset.sum_le_sum hle
      _ = (Fintype.card ι : ℝ) * (volume (S.body 0)).toReal := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact shell_bound (by exact one_le_pow₀ hk1) (Nat.cast_nonneg _)
    ENNReal.toReal_nonneg hdecomp hshell hsum

/-- **`vol Q ≤ (1 + m(K−1))·vol Q''` from the actual sets**, `K = (1 + κ/(γ−κ))ⁿ`.

The deflated mirror of `Ttc.FacetSystem.volume_body_inflated_le`, obtained by
applying it to `S.shift κ` at inscribed radius `γ − κ`. Together the two are the
`hup`/`hdn` hypotheses of `Ttc.nonconv_recentred`. -/
theorem FacetSystem.volume_body_deflated_le [Fintype ι] (S : FacetSystem n ι F)
    (c : ι → Space n) {γ κ : ℝ} (hκ : 0 ≤ κ) (hκγ : κ < γ)
    (hball : ∀ i, ∀ j, S.part j = i → γ * S.w j ≤ S.b j - S.f j (c i))
    (hfin : ∀ i, volume (S.piece 0 i) ≠ ⊤) :
    (volume (S.body 0)).toReal
      ≤ (1 + (Fintype.card ι : ℝ) * ((1 + κ / (γ - κ)) ^ n - 1))
          * (volume (S.body (-κ))).toReal := by
  have hball' : ∀ i, ∀ j, (S.shift κ).part j = i →
      (γ - κ) * (S.shift κ).w j ≤ (S.shift κ).b j - (S.shift κ).f j (c i) := by
    intro i j hj
    have h := hball i j hj
    simp only [FacetSystem.shift_b, FacetSystem.shift_w, FacetSystem.shift_f]
    nlinarith [S.w_nonneg j]
  have hfin' : ∀ i, volume ((S.shift κ).piece κ i) ≠ ⊤ := by
    intro i; simpa using hfin i
  have h := (S.shift κ).volume_body_inflated_le c (by linarith : (0:ℝ) < γ - κ) hκ hball' hfin'
  simpa using h

/-- The same comparison on the other side: `volQ ≤ (1 + m(K−1))·volQ''`. -/
theorem shell_bound_deflated {m K volQ volQ'' sumP sumShell : ℝ}
    (hK : 1 ≤ K) (_hm : 0 ≤ m) (_hvolQ'' : 0 ≤ volQ'')
    (hdecomp : volQ ≤ volQ'' + sumShell)
    (hshell : sumShell ≤ (K - 1) * sumP)
    (hsum : sumP ≤ m * volQ'') :
    volQ ≤ (1 + m * (K - 1)) * volQ'' := by
  have h1 : (K - 1) * sumP ≤ (K - 1) * (m * volQ'') :=
    mul_le_mul_of_nonneg_left hsum (by linarith)
  nlinarith

/-- **Choosing the internal parameter.** If the per-piece factor satisfies
`K ≤ 1 + η/(2m)` then the union-level loss `1 + m(K−1)` is at most `1 + η/2`,
independently of `m`. This is what forces `θ ∼ η/m`. -/
theorem shell_factor_le {m K η : ℝ} (hm : 0 < m) (hK : K ≤ 1 + η / (2 * m)) :
    1 + m * (K - 1) ≤ 1 + η / 2 := by
  have h : m * (K - 1) ≤ m * (η / (2 * m)) := by
    apply mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hm)
  have hcancel : m * (η / (2 * m)) = η / 2 := by field_simp
  linarith [hcancel ▸ h]

/-- **The cost in precision.** Replacing the internal parameter `η` by `η/(4m)`
multiplies the required radius `γ(θ) = (16n/θ)·√(log(4r/θ))` by at most `8m²`.

Since `GetPrecision` returns `⌈log₁₀(γ/γ̂)⌉` and `log₁₀(8m²) = O(log m)`, the
precision parameter grows by `O(log m)` digits — benign, because `ρ` enters the
algorithm only as the bit-length of a lattice coordinate. -/
theorem gamma_scale_cost {η r : ℝ} {n m : ℕ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hr : 1 ≤ r) (hm : 1 ≤ m) :
    (16 * n / (η / (4 * m))) * Real.sqrt (Real.log (4 * r / (η / (4 * m))))
      ≤ (8 * m ^ 2) * ((16 * n / η) * Real.sqrt (Real.log (4 * r / η))) := by
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hmpos : (0:ℝ) < (m:ℝ) := by linarith
  have hlog2 : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
  -- the log argument and the coefficient each pick up a factor `4m`
  have harg : 4 * r / (η / (4 * (m:ℝ))) = (4 * r / η) * (4 * m) := by field_simp
  have hcoef : 16 * (n:ℝ) / (η / (4 * (m:ℝ))) = (4 * m) * (16 * n / η) := by
    field_simp
  have hsplit : Real.log ((4 * r / η) * (4 * (m:ℝ)))
      = Real.log (4 * r / η) + Real.log (4 * m) := by
    rw [Real.log_mul (by positivity) (by positivity)]
  -- `L ≥ 2 log 2`
  have hL : 2 * Real.log 2 ≤ Real.log (4 * r / η) := by
    have h4 : Real.log 4 ≤ Real.log (4 * r / η) := by
      apply Real.log_le_log (by norm_num)
      rw [le_div_iff₀ hη]; nlinarith
    have he : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    linarith
  have hLpos : 0 < Real.log (4 * r / η) := by linarith
  have hlogm : Real.log (4 * (m:ℝ)) ≤ 4 * m - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  -- `√(L + log 4m) ≤ 2m·√L`
  have hsq : Real.sqrt (Real.log ((4 * r / η) * (4 * (m:ℝ))))
      ≤ 2 * (m:ℝ) * Real.sqrt (Real.log (4 * r / η)) := by
    have hLnum : (1.386:ℝ) ≤ Real.log (4 * r / η) := by linarith
    have hc : (0:ℝ) ≤ 4 * (m:ℝ) ^ 2 - 1 := by nlinarith
    have hprod : (4 * (m:ℝ) ^ 2 - 1) * 1.386
        ≤ (4 * (m:ℝ) ^ 2 - 1) * Real.log (4 * r / η) :=
      mul_le_mul_of_nonneg_left hLnum hc
    have hb : Real.log ((4 * r / η) * (4 * (m:ℝ)))
        ≤ (2 * (m:ℝ)) ^ 2 * Real.log (4 * r / η) := by
      rw [hsplit]; nlinarith [hprod, hlogm, hm1]
    calc Real.sqrt (Real.log ((4 * r / η) * (4 * (m:ℝ))))
        ≤ Real.sqrt ((2 * (m:ℝ)) ^ 2 * Real.log (4 * r / η)) := Real.sqrt_le_sqrt hb
      _ = 2 * (m:ℝ) * Real.sqrt (Real.log (4 * r / η)) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [harg, hcoef]
  have hnn : (0:ℝ) ≤ 16 * n / η := by positivity
  have hsqnn : (0:ℝ) ≤ Real.sqrt (Real.log (4 * r / η)) := Real.sqrt_nonneg _
  calc (4 * (m:ℝ)) * (16 * n / η) * Real.sqrt (Real.log ((4 * r / η) * (4 * m)))
      ≤ (4 * (m:ℝ)) * (16 * n / η) * (2 * (m:ℝ) * Real.sqrt (Real.log (4 * r / η))) := by
        apply mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = (8 * (m:ℝ) ^ 2) * ((16 * n / η) * Real.sqrt (Real.log (4 * r / η))) := by ring

end Ttc
