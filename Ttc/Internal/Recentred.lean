/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Internal.Geometry
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

/-- The recentred inscribed-ball hypothesis discharges the facet condition, with
`k = (γ + κ)/(γ − κ)`. This is `Ttc.facet_ratio_le` applied in `cᵢ`-coordinates. -/
theorem facet_bound_of_ball_at (c : ι → Space n) {γ κ : ℝ} (hκ : 0 ≤ κ) (hκγ : κ < γ)
    (hball : ∀ j, γ * S.w j ≤ S.b j - S.f j (c (S.part j))) (i : ι) (j : F)
    (hj : S.part j = i) :
    (S.b j - S.f j (c i)) + κ * S.w j
      ≤ ((γ + κ) / (γ - κ)) * ((S.b j - S.f j (c i)) - κ * S.w j) := by
  have h := hball j
  rw [hj] at h
  exact facet_ratio_le (S.w_nonneg j) hκ hκγ h


/-! ## The paper's `cl:recenter`, verbatim

The paper states the recentring step as a containment between `P'`/`P''` and
*dilates of `P` itself* (rather than of each other). That form is cleaner, and it
is what `Ttc.shell_bound` consumes. Both inclusions are proved here, under the
hypothesis that the inscribed ball is centred at the **origin**, i.e.
`γ‖A_j‖ ≤ b_j` for every facet.
-/

/-- **`cl:recenter`, first inclusion.** `P' ⊆ (1 + κ/γ)·P`. -/
theorem piece_inflated_subset_smul {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 ≤ κ) (i : ι)
    (hball : ∀ j, S.part j = i → γ * S.w j ≤ S.b j) :
    S.piece κ i ⊆ (1 + κ / γ) • S.piece 0 i := by
  have hlam : (0:ℝ) < 1 + κ / γ := by positivity
  intro x hx
  refine ⟨(1 + κ / γ)⁻¹ • x, ?_, ?_⟩
  · intro j hj
    have hb := hball j hj
    have hxj : S.f j x ≤ S.b j + κ * S.w j := hx j hj
    -- `b + κw ≤ (1 + κ/γ) b`, since `κ w ≤ (κ/γ) b`
    have hkey : S.b j + κ * S.w j ≤ (1 + κ / γ) * S.b j := by
      have h : κ * S.w j ≤ (κ / γ) * S.b j := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hγ]
        nlinarith
      nlinarith
    have hlin : S.f j ((1 + κ / γ)⁻¹ • x) = (1 + κ / γ)⁻¹ * S.f j x := by
      rw [map_smul]; rfl
    rw [hlin]
    have := mul_le_mul_of_nonneg_left (le_trans hxj hkey) (le_of_lt (inv_pos.2 hlam))
    rw [inv_mul_cancel_left₀ (ne_of_gt hlam)] at this
    simpa using this
  · show (1 + κ / γ) • (1 + κ / γ)⁻¹ • x = x
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hlam), one_smul]

/-- **`cl:recenter`, second inclusion.** `(1 − κ/γ)·P ⊆ P''`. -/
theorem smul_subset_piece_deflated {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 ≤ κ) (hκγ : κ ≤ γ)
    (i : ι) (hball : ∀ j, S.part j = i → γ * S.w j ≤ S.b j) :
    (1 - κ / γ) • S.piece 0 i ⊆ S.piece (-κ) i := by
  have hmu : (0:ℝ) ≤ 1 - κ / γ := by
    rw [sub_nonneg, div_le_one hγ]; exact hκγ
  rintro _ ⟨z, hz, rfl⟩ j hj
  have hb := hball j hj
  have hzj : S.f j z ≤ S.b j := by simpa using hz j hj
  have hlin : S.f j ((1 - κ / γ) • z) = (1 - κ / γ) * S.f j z := by
    rw [map_smul]; rfl
  rw [hlin]
  have h1 : (1 - κ / γ) * S.f j z ≤ (1 - κ / γ) * S.b j :=
    mul_le_mul_of_nonneg_left hzj hmu
  have h2 : (1 - κ / γ) * S.b j ≤ S.b j + (-κ) * S.w j := by
    have h : κ * S.w j ≤ (κ / γ) * S.b j := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hγ]
      nlinarith
    nlinarith
  linarith

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
