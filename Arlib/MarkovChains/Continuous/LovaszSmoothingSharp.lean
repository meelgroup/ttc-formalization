/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.LovaszSmoothing

/-!
# Lovász–Vempala's smoothing `f̂` at its true `1/16` normalisation

(docstring filled in at the end)
-/

namespace Arlib.MarkovChains

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

variable {n : ℕ}

/-! ## 1. Cutting a set by a hyperplane at a prescribed volume -/

/-- A nonzero functional is surjective. -/
theorem exists_apply_eq {φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} (hφ : φ ≠ 0) (s : ℝ) :
    ∃ z, φ z = s := by
  obtain ⟨z₀, hz₀⟩ : ∃ z, φ z ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ (ContinuousLinearMap.ext h)
  exact ⟨(s / φ z₀) • z₀, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hz₀]⟩

/-- Every level hyperplane of a nonzero functional is Lebesgue-null. -/
theorem volume_setOf_apply_eq {φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} (hφ : φ ≠ 0) (s : ℝ) :
    volume {z : EuclideanSpace ℝ (Fin n) | φ z = s} = 0 := by
  obtain ⟨x, hx⟩ := exists_apply_eq hφ s
  have h := volume_setOf_eq_apply hφ x
  rwa [hx] at h

/-- **The cut volume is continuous in the cut level.**  For a measurable set `S` of finite
volume and a nonzero functional `φ`, `t ↦ vol(S ∩ {φ ≤ t})` is continuous: the only
discontinuity could come from an atom of the pushforward, i.e. from a level hyperplane of
positive volume, and there are none. -/
theorem continuous_volume_cut {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S)
    (hSfin : volume S ≠ ⊤) {φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} (hφ : φ ≠ 0) :
    Continuous fun t : ℝ => (volume (S ∩ {z : EuclideanSpace ℝ (Fin n) | φ z ≤ t})).toReal := by
  have hmeas : ∀ t : ℝ, MeasurableSet (S ∩ {z : EuclideanSpace ℝ (Fin n) | φ z ≤ t}) := fun t =>
    hS.inter (measurableSet_le φ.continuous.measurable measurable_const)
  have hEq : ∀ t : ℝ, (volume (S ∩ {z : EuclideanSpace ℝ (Fin n) | φ z ≤ t})).toReal
      = ∫ z, (S ∩ {z : EuclideanSpace ℝ (Fin n) | φ z ≤ t}).indicator (fun _ => (1 : ℝ)) z := by
    intro t
    rw [integral_indicator_const _ (hmeas t)]
    simp [MeasureTheory.measureReal_def]
  simp only [hEq]
  rw [continuous_iff_continuousAt]
  intro s
  rw [ContinuousAt, Filter.tendsto_iff_seq_tendsto]
  intro u hu
  have hbound : Integrable (S.indicator fun _ => (1 : ℝ)) := by
    rw [integrable_indicator_iff hS]
    exact integrableOn_const (C := (1 : ℝ)) hSfin (by simp)
  refine tendsto_integral_of_dominated_convergence (S.indicator fun _ => (1 : ℝ))
    (fun k => ((measurable_const.indicator (hmeas (u k)))).aestronglyMeasurable) hbound
    (fun k => Filter.Eventually.of_forall fun z => ?_) ?_
  · by_cases hz : z ∈ S
    · rw [Set.indicator_of_mem hz]
      by_cases hz2 : z ∈ S ∩ {z : EuclideanSpace ℝ (Fin n) | φ z ≤ u k}
      · rw [Set.indicator_of_mem hz2]; simp
      · rw [Set.indicator_of_notMem hz2]; simp
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h => hz h.1)]
      simp
  · have hnull : volume {z : EuclideanSpace ℝ (Fin n) | φ z = s} = 0 := volume_setOf_apply_eq hφ s
    have hae : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), φ z ≠ s := by
      rw [MeasureTheory.ae_iff]
      simpa using hnull
    refine Filter.Eventually.mono hae ?_
    intro z hz
    by_cases hzS : z ∈ S
    · rcases lt_or_gt_of_ne (show φ z ≠ s from hz) with hlt | hgt
      · have h1 : ∀ᶠ k in Filter.atTop, φ z ≤ u k := by
          have := hu.eventually (eventually_gt_nhds hlt)
          exact this.mono fun k hk => hk.le
        have h2 : (S ∩ {z : EuclideanSpace ℝ (Fin n) | φ z ≤ s}).indicator
            (fun _ => (1 : ℝ)) z = 1 :=
          Set.indicator_of_mem (Set.mem_inter hzS hlt.le) _
        rw [h2]
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        exact h1.mono fun k hk =>
          (Set.indicator_of_mem (s := S ∩ {z : EuclideanSpace ℝ (Fin n) | φ z ≤ u k})
            (Set.mem_inter hzS hk) (fun _ => (1 : ℝ))).symm
      · have h1 : ∀ᶠ k in Filter.atTop, ¬ (φ z ≤ u k) := by
          have := hu.eventually (eventually_lt_nhds hgt)
          exact this.mono fun k hk => not_le.2 hk
        have h2 : (S ∩ {z : EuclideanSpace ℝ (Fin n) | φ z ≤ s}).indicator
            (fun _ => (1 : ℝ)) z = 0 :=
          Set.indicator_of_notMem (fun h => absurd h.2 (not_le.2 hgt)) _
        rw [h2]
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        exact h1.mono fun k hk => (Set.indicator_of_notMem (fun h => hk h.2) _).symm
    · have h2 : ∀ t : ℝ, (S ∩ {z : EuclideanSpace ℝ (Fin n) | φ z ≤ t}).indicator
          (fun _ => (1 : ℝ)) z = 0 := fun t => Set.indicator_of_notMem (fun h => hzS h.1) _
      simp only [h2]
      exact tendsto_const_nhds

/-- **Cutting at a prescribed volume.**  A bounded measurable set can be cut by a hyperplane
with prescribed normal `φ` so that the lower piece has any prescribed volume `v ≤ vol S`.
This is the intermediate value theorem applied to `continuous_volume_cut`. -/
theorem exists_volume_cut_eq {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S)
    {R : ℝ} (hSR : S ⊆ ball 0 R) {φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} (hφ : φ ≠ 0)
    {v : ℝ≥0∞} (hv : v ≤ volume S) :
    ∃ t : ℝ, volume (S ∩ {z : EuclideanSpace ℝ (Fin n) | φ z ≤ t}) = v := by
  have hSfin : volume S ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono hSR)
  have hvtop : v ≠ ⊤ := ne_top_of_le_ne_top hSfin hv
  set M : ℝ := ‖φ‖ * |R| + 1 with hM
  have hbdd : ∀ z ∈ S, |φ z| < M := by
    intro z hz
    have h1 : ‖z‖ < R := by simpa [mem_ball, dist_zero_right] using hSR hz
    have h2 : |φ z| ≤ ‖φ‖ * ‖z‖ := φ.le_opNorm z
    have h3 : ‖z‖ ≤ |R| := le_trans h1.le (le_abs_self R)
    have h4 : ‖φ‖ * ‖z‖ ≤ ‖φ‖ * |R| := by
      exact mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    rw [hM]
    linarith
  have hMpos : (0 : ℝ) ≤ M := by
    have : (0 : ℝ) ≤ ‖φ‖ * |R| := mul_nonneg (norm_nonneg _) (abs_nonneg _)
    rw [hM]; linarith
  have htop : S ∩ {z : EuclideanSpace ℝ (Fin n) | φ z ≤ M} = S := by
    refine Set.inter_eq_self_of_subset_left fun z hz => ?_
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _) (hbdd z hz))
  have hbot : S ∩ {z : EuclideanSpace ℝ (Fin n) | φ z ≤ -M} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hz, hz2⟩
    have h := hbdd z hz
    have : -M < φ z := by
      have := abs_lt.1 h
      exact this.1
    exact absurd hz2 (not_le.2 this)
  set G : ℝ → ℝ := fun t => (volume (S ∩ {z : EuclideanSpace ℝ (Fin n) | φ z ≤ t})).toReal with hG
  have hGcont : Continuous G := continuous_volume_cut hS hSfin hφ
  have hGbot : G (-M) = 0 := by simp [hG, hbot]
  have hGtop : G M = (volume S).toReal := by simp [hG, htop]
  have hmem : v.toReal ∈ Set.Icc (G (-M)) (G M) := by
    rw [hGbot, hGtop]
    exact ⟨ENNReal.toReal_nonneg, ENNReal.toReal_mono hSfin hv⟩
  obtain ⟨t, -, hteq⟩ :=
    intermediate_value_Icc (by linarith : (-M : ℝ) ≤ M) hGcont.continuousOn hmem
  refine ⟨t, ?_⟩
  have hfin : volume (S ∩ {z : EuclideanSpace ℝ (Fin n) | φ z ≤ t}) ≠ ⊤ :=
    ne_top_of_le_ne_top hSfin (measure_mono Set.inter_subset_left)
  rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_toReal hvtop]
  exact congrArg ENNReal.ofReal hteq

/-- **Parallel slicing.**  A bounded convex measurable set of volume `k · w` can be cut by
`k − 1` parallel hyperplanes into `k` pairwise disjoint convex measurable pieces, each of
volume exactly `w`.  This is the decomposition used in Lovász–Vempala's Lemma 6.1. -/
theorem exists_convex_partition {φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} (hφ : φ ≠ 0) {R : ℝ} :
    ∀ (k : ℕ) {S : Set (EuclideanSpace ℝ (Fin n))}, MeasurableSet S → S ⊆ ball 0 R →
      Convex ℝ S → ∀ {w : ℝ≥0∞}, volume S = k * w →
      ∃ P : Fin k → Set (EuclideanSpace ℝ (Fin n)),
        (∀ i, Convex ℝ (P i)) ∧ (∀ i, MeasurableSet (P i)) ∧ (∀ i, P i ⊆ S) ∧
        (∀ i, volume (P i) = w) ∧ Pairwise (Function.onFun Disjoint P) := by
  intro k
  induction k with
  | zero =>
      intro S _ _ _ w _
      exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
        fun i => i.elim0⟩
  | succ k ih =>
      intro S hS hSR hSconv w hvol
      have hSfin : volume S ≠ ⊤ :=
        ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono hSR)
      have hwtop : w ≠ ⊤ := by
        intro h
        rw [h, ENNReal.mul_top (by exact_mod_cast Nat.succ_ne_zero k)] at hvol
        exact hSfin hvol
      have hwle : w ≤ volume S := by
        rw [hvol, Nat.cast_succ]
        calc w = 1 * w := (one_mul w).symm
          _ ≤ ((k : ℝ≥0∞) + 1) * w := by
              exact mul_le_mul_right' (by simp) w
      obtain ⟨t, ht⟩ := exists_volume_cut_eq hS hSR hφ hwle
      set A : Set (EuclideanSpace ℝ (Fin n)) := S ∩ {z | φ z ≤ t} with hA
      set B : Set (EuclideanSpace ℝ (Fin n)) := S ∩ {z | t < φ z} with hB
      have hAmeas : MeasurableSet A :=
        hS.inter (measurableSet_le φ.continuous.measurable measurable_const)
      have hBmeas : MeasurableSet B :=
        hS.inter (measurableSet_lt measurable_const φ.continuous.measurable)
      have hAconv : Convex ℝ A := hSconv.inter
        (convex_halfSpace_le (f := fun z => φ z)
          ⟨fun a b => φ.map_add a b, fun c a => φ.map_smul c a⟩ t)
      have hBconv : Convex ℝ B := hSconv.inter
        (convex_halfSpace_gt (f := fun z => φ z)
          ⟨fun a b => φ.map_add a b, fun c a => φ.map_smul c a⟩ t)
      have hBeq : B = S \ A := by
        ext z
        simp only [hA, hB, Set.mem_inter_iff, Set.mem_diff, Set.mem_setOf_eq, not_and, not_le]
        exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 h.1⟩⟩
      have hBvol : volume B = k * w := by
        rw [hBeq, measure_diff Set.inter_subset_left hAmeas.nullMeasurableSet
          (ne_top_of_le_ne_top hSfin (measure_mono Set.inter_subset_left)), ht, hvol,
          Nat.cast_succ, add_mul, one_mul]
        exact ENNReal.add_sub_cancel_right hwtop
      obtain ⟨Q, hQconv, hQmeas, hQsub, hQvol, hQdisj⟩ :=
        ih hBmeas (hBeq ▸ (Set.diff_subset.trans hSR)) hBconv hBvol
      have hBsubS : B ⊆ S := by rw [hBeq]; exact Set.diff_subset
      have hABdisj : ∀ i, Disjoint A (Q i) := by
        intro i
        refine Set.disjoint_left.2 fun z hzA hzQ => ?_
        have h := hQsub i hzQ
        rw [hBeq] at h
        exact h.2 hzA
      obtain ⟨P, hP0, hPs⟩ : ∃ P : Fin (k + 1) → Set (EuclideanSpace ℝ (Fin n)),
          P 0 = A ∧ ∀ i : Fin k, P i.succ = Q i :=
        ⟨Fin.cons A Q, Fin.cons_zero _ _, fun i => Fin.cons_succ _ _ i⟩
      have hconv : ∀ i, Convex ℝ (P i) := by
        refine Fin.cases ?_ ?_
        · rw [hP0]; exact hAconv
        · intro i; rw [hPs]; exact hQconv i
      have hmeas : ∀ i, MeasurableSet (P i) := by
        refine Fin.cases ?_ ?_
        · rw [hP0]; exact hAmeas
        · intro i; rw [hPs]; exact hQmeas i
      have hsub : ∀ i, P i ⊆ S := by
        refine Fin.cases ?_ ?_
        · rw [hP0]; exact Set.inter_subset_left
        · intro i; rw [hPs]; exact (hQsub i).trans hBsubS
      have hvols : ∀ i, volume (P i) = w := by
        refine Fin.cases ?_ ?_
        · rw [hP0]; exact ht
        · intro i; rw [hPs]; exact hQvol i
      have hdisj : ∀ i j : Fin (k + 1), i ≠ j → Disjoint (P i) (P j) := by
        refine Fin.cases ?_ ?_
        · refine Fin.cases ?_ ?_
          · intro h; exact absurd rfl h
          · intro j' _
            rw [hP0, hPs]
            exact hABdisj j'
        · intro i'
          refine Fin.cases ?_ ?_
          · intro _
            rw [hP0, hPs]
            exact (hABdisj i').symm
          · intro j' hij
            rw [hPs, hPs]
            exact hQdisj (fun h => hij (by rw [h]))
      exact ⟨P, hconv, hmeas, hsub, hvols, fun i j hij => hdisj i j hij⟩

/-- In a family of `k > 0` nonnegative extended reals whose sum is at most `A`, some member
is at most `A/k`, in the multiplication-free form `k · aᵢ ≤ A`. -/
theorem exists_nsmul_le_of_sum_le {k : ℕ} (hk : 0 < k) (a : Fin k → ℝ≥0∞) {A : ℝ≥0∞}
    (h : ∑ i, a i ≤ A) : ∃ i, (k : ℝ≥0∞) * a i ≤ A := by
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin k)) a ⟨⟨0, hk⟩, by simp⟩
  refine ⟨i₀, le_trans ?_ h⟩
  have hcard : (Finset.univ : Finset (Fin k)).card • a i₀ ≤ ∑ i, a i :=
    Finset.card_nsmul_le_sum _ _ _ fun i _ => hi₀ i (Finset.mem_univ i)
  simpa [nsmul_eq_mul] using hcard

/-! ## 2. The smoothing at Lovász–Vempala's `1/16` normalisation -/

/-- `IsSixteenthBall δ D` says `D` is a convex measurable subset of `δBₙ` of exactly **one
sixteenth** of its volume.  This — not "half its volume" — is the index set of the minimum in
Lovász–Vempala §6.1:

> `f̂(x) = inf_C (1/vol C) ∫_C f(x+u) du`, where `C` ranges over all convex subsets of the
> ball `rB` with `vol(C) = ω_n rⁿ/16`.

Cousins–Vempala (`1409.6011/vol3_journal.tex:862`) transcribe this as "a convex subset `D` of
`δBₙ` of half its volume", which is a different function; see the module docstring. -/
structure IsSixteenthBall (δ : ℝ) (D : Set (EuclideanSpace ℝ (Fin n))) : Prop where
  convex : Convex ℝ D
  measurableSet : MeasurableSet D
  subset_ball : D ⊆ ball 0 δ
  sixteen_mul_volume : 16 * volume D = volume (ball (0 : EuclideanSpace ℝ (Fin n)) δ)

theorem IsSixteenthBall.volume_ne_top {δ : ℝ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (hD : IsSixteenthBall δ D) : volume D ≠ ⊤ :=
  ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono hD.subset_ball)

theorem IsSixteenthBall.volume_ne_zero {δ : ℝ} (hδ : 0 < δ)
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsSixteenthBall δ D) : volume D ≠ 0 := by
  intro h
  have h16 := hD.sixteen_mul_volume
  rw [h, mul_zero] at h16
  exact (Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) hδ).ne' h16.symm

/-- **The Lovász–Vempala smoothing** (RSA 30(3):307–358, §6.1),

    `f̂(x) = inf_C (∫_{y ∈ x+C} f(y) dy) / vol(C)`,

the infimum over convex **measurable** subsets `C ⊆ δBₙ` with `16·vol(C) = vol(δBₙ)`.

Two deviations from the printed formula, both recorded here rather than hidden in a name:

* the `inf` is a `⨅` — Lovász–Vempala speak of the convex set "attaining the minimum";
  nothing below needs attainment;
* the index set additionally requires `C` to be **measurable**, without which `∫_{x+C} f` and
  `vol(C)` are not the quantities the paper means.  This *shrinks* the index set, so
  `ballSmoothing16 f δ x ≥` the paper's `f̂(x)`: every upper bound proved here is a fortiori
  an upper bound for the paper's `f̂`, and every lower bound on `∫_K` of the paper's `f̂` is a
  fortiori one for `∫_K ballSmoothing16`.  Both consumers compose in the safe direction. -/
noncomputable def ballSmoothing16 (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (δ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ⨅ D ∈ {D : Set (EuclideanSpace ℝ (Fin n)) | IsSixteenthBall δ D},
    (∫⁻ y in x +ᵥ D, f y) / volume D

/-- Any single admissible `D` bounds `ballSmoothing16` from above. -/
theorem ballSmoothing16_le {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} {δ : ℝ}
    (x : EuclideanSpace ℝ (Fin n)) {D : Set (EuclideanSpace ℝ (Fin n))}
    (hD : IsSixteenthBall δ D) :
    ballSmoothing16 f δ x ≤ (∫⁻ y in x +ᵥ D, f y) / volume D :=
  iInf₂_le (f := fun D (_ : D ∈ {D : Set (EuclideanSpace ℝ (Fin n)) | IsSixteenthBall δ D}) =>
    (∫⁻ y in x +ᵥ D, f y) / volume D) D hD

/-- `ballSmoothing16` is bounded below by `c` as soon as every admissible `D` is. -/
theorem le_ballSmoothing16 {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} {δ : ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {c : ℝ≥0∞}
    (h : ∀ D : Set (EuclideanSpace ℝ (Fin n)), IsSixteenthBall δ D →
      c ≤ (∫⁻ y in x +ᵥ D, f y) / volume D) :
    c ≤ ballSmoothing16 f δ x :=
  le_iInf₂ h

/-- The multiplication-free form of `ballSmoothing16_le`. -/
theorem ballSmoothing16_mul_volume_le {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} {δ : ℝ}
    (hδ : 0 < δ) (x : EuclideanSpace ℝ (Fin n)) {D : Set (EuclideanSpace ℝ (Fin n))}
    (hD : IsSixteenthBall δ D) :
    ballSmoothing16 f δ x * volume D ≤ ∫⁻ y in x +ᵥ D, f y := by
  refine le_trans (mul_le_mul_right' (ballSmoothing16_le x hD) _) ?_
  rw [ENNReal.div_mul_cancel (hD.volume_ne_zero hδ) hD.volume_ne_top]

/-! ### Sixteenth-balls exist, and eight of them fill a half-ball -/

/-- **Eight sixteenths of the ball fill a half-ball.**  The half of `δBₙ` cut off by a
hyperplane through the centre splits, by seven parallel cuts, into eight pairwise disjoint
convex pieces, each an admissible index of `ballSmoothing16`.  Eight is the largest number of
disjoint `1/16`-pieces a half-ball can hold, and that is exactly why the half-ball route
cannot beat the constant `2`; see the module docstring. -/
theorem exists_eight_sixteenthBalls {δ : ℝ}
    {φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} (hφ : φ ≠ 0) :
    ∃ P : Fin 8 → Set (EuclideanSpace ℝ (Fin n)),
      (∀ i, IsSixteenthBall δ (P i)) ∧
      (∀ i, P i ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) δ ∩ {z | φ z ≤ 0}) ∧
      Pairwise (Function.onFun Disjoint P) := by
  set H : Set (EuclideanSpace ℝ (Fin n)) := ball 0 δ ∩ {z | φ z ≤ 0} with hH
  have hHhalf : IsHalfBall δ H := isHalfBall_ball_inter_halfSpace hφ
  have hHtop : volume H ≠ ⊤ := hHhalf.volume_ne_top
  have hcancel : 8 * (volume H / 8) = volume H :=
    ENNReal.mul_div_cancel' (by norm_num) (by norm_num)
  have h16 : 16 * (volume H / 8) = volume (ball (0 : EuclideanSpace ℝ (Fin n)) δ) := by
    rw [show (16 : ℝ≥0∞) = 2 * 8 by norm_num, mul_assoc, hcancel]
    exact hHhalf.two_mul_volume
  obtain ⟨P, hconv, hmeas, hsub, hvol, hdisj⟩ :=
    exists_convex_partition (φ := φ) hφ (R := δ) 8 hHhalf.measurableSet hHhalf.subset_ball
      hHhalf.convex (w := volume H / 8) (by simpa using hcancel.symm)
  refine ⟨P, fun i => ⟨hconv i, hmeas i, (hsub i).trans hHhalf.subset_ball, ?_⟩, hsub, hdisj⟩
  rw [hvol i]
  exact h16

/-- Sixteenth-balls exist as soon as `δ > 0` and the space is nontrivial. -/
theorem exists_isSixteenthBall (hn : 1 ≤ n) (δ : ℝ) :
    ∃ D : Set (EuclideanSpace ℝ (Fin n)), IsSixteenthBall δ D := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin n))
  obtain ⟨φ, hφ1, -⟩ := exists_dual_vector ℝ v (by simpa using hv)
  have hφ0 : φ ≠ 0 := by
    intro h
    rw [h] at hφ1
    simp at hφ1
  obtain ⟨P, hP, -, -⟩ := exists_eight_sixteenthBalls (δ := δ) hφ0
  exact ⟨P 0, hP 0⟩

end Arlib.MarkovChains
