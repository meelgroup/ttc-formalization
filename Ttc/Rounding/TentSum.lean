/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Rounding.ProdKernel

/-!
# The rounding lands somewhere: `∑ₓ k p x ≤ 1`

`Ttc.RoundingKernel.normalised` is `∫ k p x dp = 1` — stochasticity in `p`, for
fixed lattice point `x`. The summation steps of `lem:nonconv`
(`Ttc.sum_lower_of_claim_a`) need the *other* direction: for fixed `p`, the total
probability over lattice points is at most `1`.

For the tent kernel this is a **partition of unity**: `∑_{m ∈ ℤ} tent(u − m) = 1`,
because only `⌊u⌋` and `⌊u⌋+1` contribute and their values are `1 − {u}` and `{u}`.
Taking products over coordinates gives the `n`-dimensional bound.
-/

namespace Ttc

open MeasureTheory

/-- Only `⌊u⌋` and `⌊u⌋+1` are within distance `1` of `u`. -/
theorem tent_eq_zero_of_ne_floor (u : ℝ) (m : ℤ) (h : m ≠ ⌊u⌋) (h2 : m ≠ ⌊u⌋ + 1) :
    tent (u - m) = 0 := by
  refine tent_eq_zero_of_one_le ?_
  rcases lt_or_gt_of_ne h with hm | hm
  · have : (m : ℝ) ≤ (⌊u⌋ : ℝ) - 1 := by exact_mod_cast Int.le_sub_one_of_lt hm
    have hfl : (⌊u⌋ : ℝ) ≤ u := Int.floor_le u
    rw [abs_of_nonneg (by linarith)]; linarith
  · have : (⌊u⌋ : ℝ) + 2 ≤ (m : ℝ) := by exact_mod_cast (by omega : ⌊u⌋ + 2 ≤ m)
    have hfl : u < (⌊u⌋ : ℝ) + 1 := Int.lt_floor_add_one u
    rw [abs_of_nonpos (by linarith)]; linarith

/-- The two contributing values sum to `1`: `(1 − {u}) + {u}`. -/
theorem tent_floor_add (u : ℝ) : tent (u - ⌊u⌋) + tent (u - (⌊u⌋ + 1 : ℤ)) = 1 := by
  have h1 : (0:ℝ) ≤ u - ⌊u⌋ := by linarith [Int.floor_le u]
  have h2 : u - ⌊u⌋ < 1 := by linarith [Int.lt_floor_add_one u]
  push_cast
  rw [tent_of_abs_le (by rw [abs_of_nonneg h1]; linarith),
    tent_of_abs_le (by rw [abs_of_nonpos (by linarith)]; linarith),
    abs_of_nonneg h1, abs_of_nonpos (by linarith : u - ((⌊u⌋:ℝ) + 1) ≤ 0)]
  ring

/-- **Partition of unity, one coordinate.** -/
theorem sum_tent_le_one (u : ℝ) (F : Finset ℤ) : ∑ m ∈ F, tent (u - m) ≤ 1 := by
  classical
  set G : Finset ℤ := {⌊u⌋, ⌊u⌋ + 1} with hG
  have hzero : ∀ m ∈ F, m ∉ F ∩ G → tent (u - m) = 0 := by
    intro m hmF hm
    have hmG : m ∉ G := fun hmG => hm (Finset.mem_inter.mpr ⟨hmF, hmG⟩)
    simp only [hG, Finset.mem_insert, Finset.mem_singleton, not_or] at hmG
    exact tent_eq_zero_of_ne_floor u m hmG.1 hmG.2
  rw [← Finset.sum_subset (Finset.inter_subset_left (s₁ := F) (s₂ := G)) hzero]
  calc ∑ m ∈ F ∩ G, tent (u - m)
      ≤ ∑ m ∈ G, tent (u - m) :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
          (fun i _ _ => tent_nonneg _)
    _ = 1 := by
        rw [hG, Finset.sum_insert (by simp), Finset.sum_singleton]
        exact tent_floor_add u

/-- A lattice point of `ℤⁿ`, as a point of `Space n`. -/
noncomputable def latPt {n : ℕ} (z : Fin n → ℤ) : Space n :=
  (WithLp.toLp 2 (fun i => (z i : ℝ)) : Space n)

@[simp] theorem latPt_apply {n : ℕ} (z : Fin n → ℤ) (i : Fin n) :
    (latPt z) i = (z i : ℝ) := rfl

/-- **Partition of unity, `n` coordinates.** For any finite set of lattice points
the total rounding probability at a fixed `p` is at most `1`. -/
theorem sum_prod_tent_le_one {n : ℕ} (p : Space n) (T : Finset (Fin n → ℤ)) :
    ∑ z ∈ T, ∏ i, tent (p i - z i) ≤ 1 := by
  classical
  have hsub : T ⊆ Fintype.piFinset (fun i => T.image (fun z => z i)) := by
    intro z hz
    simp only [Fintype.mem_piFinset, Finset.mem_image]
    exact fun i => ⟨z, hz, rfl⟩
  calc ∑ z ∈ T, ∏ i, tent (p i - z i)
      ≤ ∑ z ∈ Fintype.piFinset (fun i => T.image (fun z => z i)), ∏ i, tent (p i - z i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun z _ _ => Finset.prod_nonneg fun i _ => tent_nonneg _)
    _ = ∏ i, ∑ m ∈ T.image (fun z => z i), tent (p i - m) :=
        (Finset.prod_univ_sum (fun i => T.image (fun z => z i))
          (fun i m => tent (p i - (m : ℝ)))).symm
    _ ≤ 1 :=
        Finset.prod_le_one (fun i _ => Finset.sum_nonneg fun m _ => tent_nonneg _)
          (fun i _ => sum_tent_le_one _ _)

/-- **The exact partition of unity, one coordinate.** Needed for `claim:cl`(b),
where the mass landing *inside* `Q` is obtained as `1` minus the mass outside. -/
theorem tsum_tent_eq_one (u : ℝ) : ∑' m : ℤ, tent (u - m) = 1 := by
  classical
  rw [tsum_eq_sum (s := ({⌊u⌋, ⌊u⌋ + 1} : Finset ℤ)) ?_]
  · rw [Finset.sum_insert (by simp), Finset.sum_singleton]; exact tent_floor_add u
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    exact tent_eq_zero_of_ne_floor u m hm.1 hm.2

/-- **`htot`**: the total probability over any finite set of lattice points is at
most `1`. This is the hypothesis `Ttc.sum_lower_of_claim_a` consumes. -/
theorem sum_roundProb_le_one {n : ℕ} {S : Set (Space n)} (hS : MeasurableSet S)
    (T : Finset (Fin n → ℤ)) (hpos : 0 < (volume S).toReal) (hfin : volume S ≠ ⊤) :
    ∑ z ∈ T, roundProb (prodKernel n) S (latPt z) ≤ 1 := by
  have hint : ∀ z : Fin n → ℤ,
      IntegrableOn (fun p => (prodKernel n).k p (latPt z)) S :=
    fun z => ((prodKernel n).integrable (latPt z)).integrableOn
  have hsum : ∑ z ∈ T, roundProb (prodKernel n) S (latPt z)
      = (∫ p in S, ∑ z ∈ T, (prodKernel n).k p (latPt z)) / (volume S).toReal := by
    simp only [roundProb]
    rw [← Finset.sum_div, integral_finsetSum _ fun z _ => hint z]
  rw [hsum, div_le_one hpos]
  calc ∫ p in S, ∑ z ∈ T, (prodKernel n).k p (latPt z)
      ≤ ∫ _p in S, (1 : ℝ) := by
        refine setIntegral_mono_on
          (integrable_finsetSum _ fun z _ => hint z) (integrableOn_const hfin) hS ?_
        intro p _
        exact sum_prod_tent_le_one p T
    _ = (volume S).toReal := by
        rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]

end Ttc
