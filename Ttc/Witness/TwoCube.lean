/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.Final

/-!
# `Witness/TwoCube`: a non-vacuity witness whose DNF has **two** cubes

Every other witness in this development is the box `[0,c]ⁿ` (`Ttc/Witness/Box.lean`,
`Ttc/Witness/BoxProb.lean`, the `Ttc.Box.*` sections of `Ttc/Exec/EndToEnd.lean` and
`Ttc/Exec/Budget.lean`).  Its DNF has **exactly one cube**, so the machinery that
handles several — `thm:decomposition`, the `m`-way union bound, the per-cube error
composition, and the `∑ s` over lattice points spanning more than one region — is
never exercised.  A theorem quantified over multi-cube DNFs could be vacuous or
wrong at arity two and every existing witness would still pass.

This file closes that gap: two **disjoint** axis-aligned boxes of the same side
`c`, presented as a positive DNF with two cubes, and `Ttc.ttc_volume_final` — the
development's strongest capstone (no oracle, no polytope description, conclusion
`1 − δ`) — instantiated on them.

## What is landed

| result | content |
| --- | --- |
| `Ttc.TwoCube.card_toDNF_eq_two` | the DNF has **exactly two** cubes — the anti-degeneracy fact the rest rests on |
| `Ttc.TwoCube.sol_eq_union_two`, `…_T` | `Sol(F)` is the union of two **distinct, nonempty, disjoint** regions |
| `Ttc.TwoCube.cenT_left_ne_right` | the two inscribed balls have **different centres** (`γ̂` is shared, `cen` is not constant) |
| `Ttc.TwoCube.almostUniform_T` | `eq:almostuniform` for the ball walk, at **each** of the two geometries |
| `Ttc.TwoCube.big_two` | the regime condition, with the `∑ s` running over lattice points of **both** regions |
| `Ttc.TwoCube.ttc_volume_final_two_cube` | `Ttc.ttc_volume_final` itself, at every `(ε, δ) ∈ (0,1]²` |
| `Ttc.TwoCube.ttc_volume_final_two_cube_at` | the same at two numeral pairs, bounds `1/10` (at `δ = 9/10 ∈ (4/5,1)`) and `3/4`, both proved positive |

Nothing is assumed anywhere: no `Prop` bundling a hypothesis is introduced, the
sampler is `Ttc.e2eSampler` (whose `law_tv` is a theorem), the volume estimates are
the Monte-Carlo oracle's own output, and the linear description of the two dilated
regions is the canonical one of `Exec/CanonPolytope`.

## Cost

Exponential in `n`, and paid twice — see the docstring of
`Ttc.TwoCube.ttc_volume_final_two_cube`.  Correctness, not efficiency, is what is
established.
-/

namespace Ttc

namespace TwoCube

open MeasureTheory Set Pointwise

variable {n : ℕ}

/-! ## Part 1.  The shifted box `[lo, lo+c]ⁿ`

`Ttc/Witness/Box.lean` is parametric in the side `c` but pinned to the corner `0`.
The second cube of the witness sits at a corner `lo > c`, so the geometry is
re-derived here at a general corner.  Nothing in this part mentions the DNF.
-/

/-- The box `[lo, lo+c]ⁿ ⊆ ℝⁿ`. -/
def sbx (n : ℕ) (lo c : ℝ) : Set (Space n) := {x : Space n | ∀ k, lo ≤ x k ∧ x k ≤ lo + c}

@[simp] theorem mem_sbx {lo c : ℝ} {x : Space n} :
    x ∈ sbx n lo c ↔ ∀ k, lo ≤ x k ∧ x k ≤ lo + c := Iff.rfl

/-- The `2n` linear atoms cutting out `[lo, lo+c]ⁿ`: `Sum.inl k` is `x k ≤ lo + c`
and `Sum.inr k` is `−x k ≤ −lo`, i.e. `lo ≤ x k`.  At `lo = 0` these are
`Ttc.boxAtoms` up to `−0 = 0`. -/
def sbAtoms (n : ℕ) (lo c : ℝ) : (Fin n ⊕ Fin n) → LinAtom n
  | .inl k => ⟨fun i => if i = k then 1 else 0, lo + c⟩
  | .inr k => ⟨fun i => if i = k then -1 else 0, -lo⟩

@[simp] theorem sbAtoms_inl_coeff (lo c : ℝ) (k i : Fin n) :
    (sbAtoms n lo c (.inl k)).coeff i = if i = k then 1 else 0 := rfl

@[simp] theorem sbAtoms_inl_bound (lo c : ℝ) (k : Fin n) :
    (sbAtoms n lo c (.inl k)).bound = lo + c := rfl

@[simp] theorem sbAtoms_inr_coeff (lo c : ℝ) (k i : Fin n) :
    (sbAtoms n lo c (.inr k)).coeff i = if i = k then -1 else 0 := rfl

@[simp] theorem sbAtoms_inr_bound (lo c : ℝ) (k : Fin n) :
    (sbAtoms n lo c (.inr k)).bound = -lo := rfl

theorem halfspace_sbAtoms_inl (lo c : ℝ) (k : Fin n) :
    (sbAtoms n lo c (.inl k)).halfspace = {x : Space n | x k ≤ lo + c} := by
  ext x
  simp only [LinAtom.halfspace, sbAtoms_inl_coeff, sbAtoms_inl_bound, Set.mem_setOf_eq,
    Box.sum_single_mul, one_mul]

theorem halfspace_sbAtoms_inr (lo c : ℝ) (k : Fin n) :
    (sbAtoms n lo c (.inr k)).halfspace = {x : Space n | lo ≤ x k} := by
  ext x
  simp only [LinAtom.halfspace, sbAtoms_inr_coeff, sbAtoms_inr_bound, Set.mem_setOf_eq,
    Box.sum_single_mul]
  constructor <;> intro h <;> linarith

/-- Every coefficient vector of `Ttc.TwoCube.sbAtoms` is a `±1` in one slot, so its
squared length is `1`. -/
theorem sbAtoms_coeff_sq_sum (lo c : ℝ) (j : Fin n ⊕ Fin n) :
    ∑ k, (sbAtoms n lo c j).coeff k ^ 2 = 1 := by
  obtain (k | k) := j <;> simp

/-- The centre of `[lo, lo+c]ⁿ`. -/
noncomputable def sbCentre (n : ℕ) (lo c : ℝ) : Space n :=
  WithLp.toLp 2 (fun _ => lo + c / 2)

@[simp] theorem sbCentre_apply (lo c : ℝ) (k : Fin n) :
    (sbCentre n lo c) k = lo + c / 2 := rfl

/-- **The inscribed ball of radius `c/2`**, at the shifted corner: `lem:nonconv`'s
hypothesis for the second cube, whose centre differs from the first's. -/
theorem ball_subset_sbx (n : ℕ) (lo c : ℝ) :
    Metric.ball (sbCentre n lo c) (c / 2) ⊆ sbx n lo c := by
  intro x hx k
  have hd : ‖x - sbCentre n lo c‖ < c / 2 := by rwa [Metric.mem_ball, dist_eq_norm] at hx
  have hxk : (x - sbCentre n lo c) k = x k - (lo + c / 2) := rfl
  have h1 := coord_le_norm (x - sbCentre n lo c) k
  have h2 := neg_coord_le_norm (x - sbCentre n lo c) k
  rw [hxk] at h1 h2
  constructor <;> linarith

/-- `[lo, lo+c]ⁿ` sits inside a closed ball about the origin. -/
theorem sbx_subset_closedBall (n : ℕ) (lo : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    sbx n lo c ⊆ Metric.closedBall (0 : Space n) (Real.sqrt (n * (|lo| + c) ^ 2)) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin n, (|lo| + c) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h := hx i
        have hlo : -|lo| ≤ lo := neg_abs_le lo
        have hlo' : lo ≤ |lo| := le_abs_self lo
        have h1 : -(|lo| + c) ≤ x i := by linarith [h.1]
        have h2 : x i ≤ |lo| + c := by linarith [h.2]
        rw [Real.norm_eq_abs, sq_abs]
        nlinarith
    _ = n * (|lo| + c) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The shifted box is bounded** — `Ttc.ttc_volume_final`'s `hbdd`, one half. -/
theorem isBounded_sbx (n : ℕ) (lo : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    Bornology.IsBounded (sbx n lo c) :=
  Metric.isBounded_closedBall.subset (sbx_subset_closedBall n lo hc)

/-- **The shifted box has volume `cⁿ`.**  It is the preimage of the product box
`∏ᵢ [lo, lo+c]` under the volume-preserving identification of `EuclideanSpace` with
`Fin n → ℝ`. -/
theorem volume_sbx (n : ℕ) (lo c : ℝ) :
    volume (sbx n lo c) = ENNReal.ofReal c ^ n := by
  have hpre : sbx n lo c
      = (WithLp.ofLp : Space n → (Fin n → ℝ)) ⁻¹'
        (Set.univ.pi fun _ : Fin n => Set.Icc lo (lo + c)) := by
    ext p
    simp only [sbx, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
      forall_const, Set.mem_Icc]
  rw [hpre, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
      (MeasurableSet.univ_pi fun _ => measurableSet_Icc).nullMeasurableSet,
    volume_pi_pi]
  have hfac : volume (Set.Icc lo (lo + c)) = ENNReal.ofReal c := by
    rw [Real.volume_Icc]
    congr 1
    ring
  rw [Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) => hfac)]
  simp

theorem volume_sbx_ne_top (n : ℕ) (lo c : ℝ) : volume (sbx n lo c) ≠ ⊤ := by
  rw [volume_sbx]
  exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top

/-- **The shifted box's volume, as a real number: `cⁿ`.** -/
theorem toReal_volume_sbx (n : ℕ) (lo : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    (volume (sbx n lo c)).toReal = c ^ n := by
  rw [volume_sbx, ← ENNReal.ofReal_pow hc, ENNReal.toReal_ofReal (by positivity)]

/-! ## Part 2.  The formula, and its **two**-cube DNF

The atom index type is two disjoint copies of the box's `2n` atom indices, and the
input formula is the *disjunction* of the two conjunctions.  `Ttc.toDNF` maps a
disjunction to the concatenation of the two DNFs, so the decomposition has exactly
two cubes — the fact the rest of the file rests on
(`Ttc.TwoCube.card_toDNF_eq_two`).
-/

/-- The atom index type of the witness: two disjoint copies of `Fin n ⊕ Fin n`. -/
abbrev A2 (n : ℕ) := (Fin n ⊕ Fin n) ⊕ (Fin n ⊕ Fin n)

/-- **The witness's atoms.**  The left copy cuts out `[0,c]ⁿ`, the right copy
`[lo, lo+c]ⁿ`. -/
def twoAtoms (n : ℕ) (lo c : ℝ) : A2 n → LinAtom n :=
  Sum.elim (sbAtoms n 0 c) (sbAtoms n lo c)

@[simp] theorem twoAtoms_inl (lo c : ℝ) (j : Fin n ⊕ Fin n) :
    twoAtoms n lo c (Sum.inl j) = sbAtoms n 0 c j := rfl

@[simp] theorem twoAtoms_inr (lo c : ℝ) (j : Fin n ⊕ Fin n) :
    twoAtoms n lo c (Sum.inr j) = sbAtoms n lo c j := rfl

/-- Every atom of the witness has a `±1` coordinate vector as its normal. -/
theorem twoAtoms_coeff_sq_sum (lo c : ℝ) (a : A2 n) :
    ∑ k, (twoAtoms n lo c a).coeff k ^ 2 = 1 := by
  obtain (j | j) := a <;> exact sbAtoms_coeff_sq_sum _ _ _

/-- The left cube: all `2n` atoms of the left copy, positively. -/
def cubeL (n : ℕ) : Cube (A2 n) := (boxAtomList n).map fun j => ⟨Sum.inl j, true⟩

/-- The right cube: all `2n` atoms of the right copy, positively. -/
def cubeR (n : ℕ) : Cube (A2 n) := (boxAtomList n).map fun j => ⟨Sum.inr j, true⟩

/-- **The input formula**: `(all left atoms) ∨ (all right atoms)`.  Negation-free,
so `Ttc.toDNF`'s output is positive. -/
def twoForm (n : ℕ) : BForm (A2 n) :=
  .or (conj ((boxAtomList n).map Sum.inl)) (conj ((boxAtomList n).map Sum.inr))

theorem twoForm_isPositive : (twoForm n).IsPositive :=
  ⟨isPositive_conj _, isPositive_conj _⟩

/-- **`ToDNF` returns exactly the two cubes.**  A disjunction converts to the
concatenation of the two DNFs, and each conjunct is a single cube. -/
theorem toDNF_twoForm (n : ℕ) : Ttc.toDNF (twoForm n) = [cubeL n, cubeR n] := by
  show Ttc.toDNF (conj ((boxAtomList n).map Sum.inl))
      ++ Ttc.toDNF (conj ((boxAtomList n).map Sum.inr)) = _
  rw [toDNF_conj, toDNF_conj, cubeL, cubeR, List.map_map, List.map_map]
  rfl

theorem mem_cubeL (j : Fin n ⊕ Fin n) : (⟨Sum.inl j, true⟩ : Lit (A2 n)) ∈ cubeL n :=
  List.mem_map_of_mem (mem_boxAtomList j)

theorem mem_cubeR (j : Fin n ⊕ Fin n) : (⟨Sum.inr j, true⟩ : Lit (A2 n)) ∈ cubeR n :=
  List.mem_map_of_mem (mem_boxAtomList j)

theorem exists_of_mem_cubeL {l : Lit (A2 n)} (hl : l ∈ cubeL n) :
    ∃ j, l = ⟨Sum.inl j, true⟩ := by
  rw [cubeL, List.mem_map] at hl
  obtain ⟨j, -, rfl⟩ := hl
  exact ⟨j, rfl⟩

theorem exists_of_mem_cubeR {l : Lit (A2 n)} (hl : l ∈ cubeR n) :
    ∃ j, l = ⟨Sum.inr j, true⟩ := by
  rw [cubeR, List.mem_map] at hl
  obtain ⟨j, -, rfl⟩ := hl
  exact ⟨j, rfl⟩

theorem cubeL_isPositive : Cube.IsPositive (cubeL n) := by
  intro l hl
  obtain ⟨j, rfl⟩ := exists_of_mem_cubeL hl
  rfl

theorem cubeR_isPositive : Cube.IsPositive (cubeR n) := by
  intro l hl
  obtain ⟨j, rfl⟩ := exists_of_mem_cubeR hl
  rfl

/-- **The two cubes are different cubes** — no literal of one occurs in the other.
This is what keeps the DNF from collapsing to arity one. -/
theorem cubeL_ne_cubeR (hn : 1 ≤ n) : cubeL n ≠ cubeR n := by
  intro h
  have hmem : (⟨Sum.inl (Sum.inl ⟨0, hn⟩), true⟩ : Lit (A2 n)) ∈ cubeR n := by
    rw [← h]; exact mem_cubeL _
  obtain ⟨j, hj⟩ := exists_of_mem_cubeR hmem
  simp at hj

theorem mem_toDNF_cubeL : cubeL n ∈ Ttc.toDNF (twoForm n) := by
  rw [toDNF_twoForm]; exact List.mem_cons_self

theorem mem_toDNF_cubeR : cubeR n ∈ Ttc.toDNF (twoForm n) := by
  rw [toDNF_twoForm]; exact List.mem_cons_of_mem _ List.mem_cons_self

/-- Membership in the witness's DNF is membership in the pair. -/
theorem eq_cubeL_or_cubeR {i : Cube (A2 n)} (hi : i ∈ Ttc.toDNF (twoForm n)) :
    i = cubeL n ∨ i = cubeR n := by
  rw [toDNF_twoForm] at hi
  simpa using hi

/-- **The DNF has exactly two cubes.**  Without this the file would prove nothing
new: it is the anti-degeneracy fact that the witness is not the one-cube box in
disguise. -/
theorem card_toDNF_eq_two (hn : 1 ≤ n) :
    Nat.card {c : Cube (A2 n) // c ∈ Ttc.toDNF (twoForm n)} = 2 := by
  have hiff : ∀ c : Cube (A2 n),
      c ∈ Ttc.toDNF (twoForm n) ↔ c ∈ ({cubeL n, cubeR n} : Set (Cube (A2 n))) := by
    intro c
    rw [toDNF_twoForm]
    simp
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff), Nat.card_coe_set_eq,
    Set.ncard_pair (cubeL_ne_cubeR hn)]

/-- **`2 ≤ m`**, the form `hm` takes on this witness: the capstone's `1 ≤ m` follows,
but the instance genuinely has two. -/
theorem two_le_card_cubes_two (hn : 1 ≤ n) :
    2 ≤ Nat.card {c : Cube (A2 n) // c ∈ Ttc.toDNF (twoForm n)} :=
  le_of_eq (card_toDNF_eq_two hn).symm

theorem one_le_card_cubes_two (hn : 1 ≤ n) :
    1 ≤ Nat.card {c : Cube (A2 n) // c ∈ Ttc.toDNF (twoForm n)} := by
  rw [card_toDNF_eq_two hn]; norm_num

theorem one_le_card_facets_two (hn : 1 ≤ n) :
    1 ≤ Nat.card (FacetIndex (Ttc.toDNF (twoForm n))) :=
  one_le_card_facets (c := cubeL n) mem_toDNF_cubeL
    (l := ⟨Sum.inl (Sum.inl ⟨0, hn⟩), true⟩) (mem_cubeL _)

/-- The main loop runs twice — the DNF is a two-element list. -/
theorem length_toDNF_twoForm (n : ℕ) : (Ttc.toDNF (twoForm n)).length = 2 := by
  rw [toDNF_twoForm]; rfl

/-! ## Part 3.  `Sol(F)` is the union of the two boxes

`thm:decomposition` (`Ttc.sol_eq_iUnion_region`) is a theorem of the development, so
nothing here needs to *assume* the decomposition; what is proved is that on this
instance the two regions are the two boxes, that they are **distinct**, **nonempty**
and **disjoint**, and that their union is `Sol(F)`.
-/

/-- The interpretation the witness runs at. -/
abbrev MT (n : ℕ) (lo c : ℝ) : A2 n → Set (Space n) := fun a => (twoAtoms n lo c a).halfspace

/-- Satisfying all `2n` atoms of one copy is exactly membership in that copy's box. -/
theorem forall_halfspace_iff (lo c lo' : ℝ) (f : (Fin n ⊕ Fin n) → A2 n)
    (hf : ∀ j, twoAtoms n lo c (f j) = sbAtoms n lo' c j) (x : Space n) :
    (∀ j : Fin n ⊕ Fin n, x ∈ MT n lo c (f j)) ↔ x ∈ sbx n lo' c := by
  constructor
  · intro h k
    have h1 : x ∈ (twoAtoms n lo c (f (Sum.inl k))).halfspace := h (Sum.inl k)
    have h2 : x ∈ (twoAtoms n lo c (f (Sum.inr k))).halfspace := h (Sum.inr k)
    rw [hf, halfspace_sbAtoms_inl] at h1
    rw [hf, halfspace_sbAtoms_inr] at h2
    exact ⟨h2, h1⟩
  · intro hx j
    show x ∈ (twoAtoms n lo c (f j)).halfspace
    obtain (k | k) := j
    · rw [hf, halfspace_sbAtoms_inl]; exact (hx k).2
    · rw [hf, halfspace_sbAtoms_inr]; exact (hx k).1

/-- **The left cube carves out `[0,c]ⁿ`.** -/
theorem region_cubeL (lo c : ℝ) : region (MT n lo c) (cubeL n) = sbx n 0 c := by
  ext x
  rw [← forall_halfspace_iff lo c 0 Sum.inl (fun _ => rfl) x]
  simp only [mem_region_iff]
  constructor
  · intro h j
    exact h ⟨Sum.inl j, true⟩ (mem_cubeL j)
  · intro h l hl
    obtain ⟨j, rfl⟩ := exists_of_mem_cubeL hl
    exact h j

/-- **The right cube carves out `[lo, lo+c]ⁿ`.** -/
theorem region_cubeR (lo c : ℝ) : region (MT n lo c) (cubeR n) = sbx n lo c := by
  ext x
  rw [← forall_halfspace_iff lo c lo Sum.inr (fun _ => rfl) x]
  simp only [mem_region_iff]
  constructor
  · intro h j
    exact h ⟨Sum.inr j, true⟩ (mem_cubeR j)
  · intro h l hl
    obtain ⟨j, rfl⟩ := exists_of_mem_cubeR hl
    exact h j

/-- The region of *any* cube of the DNF is one of the two boxes. -/
theorem region_eq_sbx {lo c : ℝ} {i : Cube (A2 n)} (hi : i ∈ Ttc.toDNF (twoForm n)) :
    region (MT n lo c) i = sbx n 0 c ∨ region (MT n lo c) i = sbx n lo c := by
  rcases eq_cubeL_or_cubeR hi with h | h
  · exact Or.inl (by rw [h, region_cubeL])
  · exact Or.inr (by rw [h, region_cubeR])

/-- **`Sol(F)` is the union of the two boxes.** -/
theorem sol_twoForm (lo c : ℝ) :
    sol (MT n lo c) (twoForm n) = sbx n 0 c ∪ sbx n lo c := by
  ext x
  show (conj ((boxAtomList n).map Sum.inl)).holds (induced (MT n lo c) x)
      ∨ (conj ((boxAtomList n).map Sum.inr)).holds (induced (MT n lo c) x) ↔ _
  rw [holds_conj, holds_conj, Set.mem_union,
    ← forall_halfspace_iff lo c 0 Sum.inl (fun _ => rfl) x,
    ← forall_halfspace_iff lo c lo Sum.inr (fun _ => rfl) x]
  constructor
  · rintro (h | h)
    · exact Or.inl fun j => h (Sum.inl j) (List.mem_map_of_mem (mem_boxAtomList j))
    · exact Or.inr fun j => h (Sum.inr j) (List.mem_map_of_mem (mem_boxAtomList j))
  · rintro (h | h)
    · refine Or.inl fun a ha => ?_
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 ha
      exact h j
    · refine Or.inr fun a ha => ?_
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 ha
      exact h j

/-- The origin lies in the left box. -/
theorem zero_mem_sbx_left {c : ℝ} (hc : 0 ≤ c) : (0 : Space n) ∈ sbx n 0 c :=
  fun _ => ⟨le_of_eq rfl, by simpa using hc⟩

/-- The corner lies in the right box. -/
theorem corner_mem_sbx (lo : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    (WithLp.toLp 2 (fun _ => lo) : Space n) ∈ sbx n lo c :=
  fun _ => ⟨le_of_eq rfl, by simpa using hc⟩

/-- **The two boxes are disjoint** once the second corner clears the first box. -/
theorem disjoint_sbx (hn : 1 ≤ n) {lo c : ℝ} (hlo : c < lo) :
    Disjoint (sbx n 0 c) (sbx n lo c) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have h1 := (hx ⟨0, hn⟩).2
  have h2 := (hx' ⟨0, hn⟩).1
  simp only [zero_add] at h1
  linarith

/-- **The anti-degeneracy statement for `thm:decomposition`.**  `Sol(F)` is the union
of the two cubes' regions, and those regions are two **distinct**, **nonempty**,
**disjoint** boxes — so the decomposition this witness exercises is genuinely of
arity two, not a two-fold repetition of one region. -/
theorem sol_eq_union_two (hn : 1 ≤ n) {lo c : ℝ} (hc : 0 ≤ c) (hlo : c < lo) :
    sol (MT n lo c) (twoForm n)
        = region (MT n lo c) (cubeL n) ∪ region (MT n lo c) (cubeR n)
      ∧ (region (MT n lo c) (cubeL n)).Nonempty
      ∧ (region (MT n lo c) (cubeR n)).Nonempty
      ∧ Disjoint (region (MT n lo c) (cubeL n)) (region (MT n lo c) (cubeR n))
      ∧ region (MT n lo c) (cubeL n) ≠ region (MT n lo c) (cubeR n) := by
  have hdisj : Disjoint (region (MT n lo c) (cubeL n)) (region (MT n lo c) (cubeR n)) := by
    rw [region_cubeL, region_cubeR]; exact disjoint_sbx hn hlo
  have hL : (region (MT n lo c) (cubeL n)).Nonempty := by
    rw [region_cubeL]; exact ⟨0, zero_mem_sbx_left hc⟩
  have hR : (region (MT n lo c) (cubeR n)).Nonempty := by
    rw [region_cubeR]; exact ⟨_, corner_mem_sbx lo hc⟩
  refine ⟨by rw [sol_twoForm, region_cubeL, region_cubeR], hL, hR, hdisj, ?_⟩
  intro h
  obtain ⟨x, hx⟩ := hL
  exact (Set.disjoint_left.1 hdisj hx) (h ▸ hx)

/-- **`Ttc.ttc_volume_final`'s `hbdd`** — a union of two bounded boxes is bounded. -/
theorem isBounded_sol_twoForm (lo : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    Bornology.IsBounded (sol (MT n lo c) (twoForm n)) := by
  rw [sol_twoForm]
  exact (isBounded_sbx n 0 hc).union (isBounded_sbx n lo hc)

/-- **`Ttc.ttc_volume_final`'s `hcoeff`** — every facet normal is a `±1` coordinate
vector, in either cube. -/
theorem coeff_ne_zero_two (lo c : ℝ) :
    ∀ j : FacetIndex (Ttc.toDNF (twoForm n)), (twoAtoms n lo c j.2.val.atom).coeff ≠ 0 := by
  refine coeff_ne_zero_of_normal_ne_zero fun j => ?_
  rw [twoAtoms_coeff_sq_sum]
  norm_num

/-! ## Part 4.  The parameter block, the side, and the second corner

The parameter block is `Ttc.ttcParams` at the witness's own DNF, so
`Ttc.ttc_volume_final`'s `hP` holds by `rfl`.  Note that `m = 2` and
`r = 4n` here, not `m = 1` and `r = 2n`: the block the algorithm computes really is
the two-cube one, and `Ttc.Params.deltaPrime = δ/(4m) = δ/8` is the per-call failure
probability of **two** `Vol_ED` calls.

The side is `max 1 Thresh`, as in `Ttc.Box.sideS`, so the instance grows as the
accuracy parameters shrink.  The second corner `loT` is chosen to be **a multiple of
the lattice spacing `10^(−ρ)` strictly beyond the first box**, which buys two things
at once: the boxes are disjoint, and the second box contains a lattice point.
-/

/-- **The computed parameter block** of the two-cube instance. -/
noncomputable def parT (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) : Params :=
  ttcParams (Ttc.toDNF (twoForm n)) n ε δ hε0 hε1 hn
    (one_le_card_cubes_two hn) (one_le_card_facets_two hn)

@[simp] theorem parT_eps (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (parT n hn ε δ hε0 hε1).ε = ε := rfl

@[simp] theorem parT_delta (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (parT n hn ε δ hε0 hε1).δ = δ := rfl

/-- **The block's cube count is `2`** — the whole point of the witness. -/
theorem parT_m (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (parT n hn ε δ hε0 hε1).m = 2 := card_toDNF_eq_two hn

theorem parT_epsPrime (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (parT n hn ε δ hε0 hε1).epsPrime = ε / 12 := rfl

theorem parT_eta (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (parT n hn ε δ hε0 hε1).eta = ε / 8 := rfl

theorem parT_epsPrime_pos (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    0 < (parT n hn ε δ hε0 hε1).epsPrime := by
  rw [parT_epsPrime]; linarith

theorem parT_epsPrime_le (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (parT n hn ε δ hε0 hε1).epsPrime ≤ 1 / 12 := by
  rw [parT_epsPrime]; linarith

theorem parT_epsPrime_lt_one (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (parT n hn ε δ hε0 hε1).epsPrime < 1 := by
  have := parT_epsPrime_le n hn ε δ hε0 hε1; linarith

/-- **`Thresh > 0`** at every `(ε, δ)` in range. -/
theorem parT_thresh_pos (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) : 0 < (parT n hn ε δ hε0 hε1).thresh := by
  refine lt_of_lt_of_le ?_ (le_max_right _ _)
  have hdiv : (1 : ℝ) < 6 / δ := (one_lt_div hδ0).2 (by linarith)
  have h6 : (0 : ℝ) < Real.log (6 / δ) := Real.log_pos hdiv
  have hm : (0 : ℝ) ≤ Real.log ((parT n hn ε δ hε0 hε1).m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (parT n hn ε δ hε0 hε1).hm)
  have hd : (parT n hn ε δ hε0 hε1).δ = δ := rfl
  rw [hd]
  linarith

/-- The common side of the two boxes: at least `1`, and at least `Thresh`. -/
noncomputable def sideT (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) : ℝ :=
  max 1 (parT n hn ε δ hε0 hε1).thresh

theorem one_le_sideT (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    1 ≤ sideT n hn ε δ hε0 hε1 := le_max_left _ _

theorem sideT_pos (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    0 < sideT n hn ε δ hε0 hε1 := lt_of_lt_of_le one_pos (one_le_sideT n hn ε δ hε0 hε1)

theorem thresh_le_sideT (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (parT n hn ε δ hε0 hε1).thresh ≤ sideT n hn ε δ hε0 hε1 := le_max_right _ _

/-- `γ̂`, the inscribed radius shared by the two cubes: half the common side.  The two
**centres differ**; the radius does not. -/
noncomputable def gamT (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) : ℝ :=
  sideT n hn ε δ hε0 hε1 / 2

theorem gamT_pos (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    0 < gamT n hn ε δ hε0 hε1 := half_pos (sideT_pos n hn ε δ hε0 hε1)

/-- The precision `GetPrecision` returns for this `γ̂`. -/
noncomputable def rhoT (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) : ℤ :=
  (parT n hn ε δ hε0 hε1).precision (gamT n hn ε δ hε0 hε1)

/-- **The second box's corner**: the smallest multiple of the lattice spacing
`10^(−ρ)` strictly beyond the first box.  Being a lattice multiple is what puts a
lattice point in the second box; being beyond `c` is what makes the two boxes
disjoint. -/
noncomputable def loT (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) : ℝ :=
  ((⌈sideT n hn ε δ hε0 hε1 * latticeScale (rhoT n hn ε δ hε0 hε1)⌉₊ : ℝ) + 1)
    / latticeScale (rhoT n hn ε δ hε0 hε1)

theorem sideT_lt_loT (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    sideT n hn ε δ hε0 hε1 < loT n hn ε δ hε0 hε1 := by
  have hr : (0 : ℝ) < latticeScale (rhoT n hn ε δ hε0 hε1) := latticeScale_pos _
  rw [loT, lt_div_iff₀ hr]
  have := Nat.le_ceil (sideT n hn ε δ hε0 hε1 * latticeScale (rhoT n hn ε δ hε0 hε1))
  linarith

/-- The corner is a lattice point of `𝕃ⁿ`. -/
theorem corner_mem_fineLattice (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (WithLp.toLp 2 (fun _ => loT n hn ε δ hε0 hε1) : Space n)
      ∈ fineLattice n (latticeScale (rhoT n hn ε δ hε0 hε1)) := by
  intro i
  refine ⟨(⌈sideT n hn ε δ hε0 hε1 * latticeScale (rhoT n hn ε δ hε0 hε1)⌉₊ : ℤ) + 1, ?_⟩
  show loT n hn ε δ hε0 hε1 = _
  rw [loT, div_eq_inv_mul]
  push_cast
  ring

/-! ## Part 5.  The instance's data, and its lattice points -/

/-- The witness's atom family, at the computed side and corner. -/
noncomputable def atomsT (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    A2 n → LinAtom n :=
  twoAtoms n (loT n hn ε δ hε0 hε1) (sideT n hn ε δ hε0 hε1)

/-- The witness's interpretation. -/
noncomputable abbrev MTT (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    A2 n → Set (Space n) :=
  fun a => (atomsT n hn ε δ hε0 hε1 a).halfspace

open scoped Classical in
/-- **The two ball centres.**  They *differ between the cubes* — the one thing the
single-cube box witness could never test. -/
noncomputable def cenT (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    {c : Cube (A2 n) // c ∈ Ttc.toDNF (twoForm n)} → Space n :=
  fun i => if i.val = cubeL n then sbCentre n 0 (sideT n hn ε δ hε0 hε1)
    else sbCentre n (loT n hn ε δ hε0 hε1) (sideT n hn ε δ hε0 hε1)

/-- **`Ttc.ttc_volume_final`'s `ball_subset`, at two different centres.** -/
theorem ball_subset_two (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ i : {c : Cube (A2 n) // c ∈ Ttc.toDNF (twoForm n)},
      Metric.ball (cenT n hn ε δ hε0 hε1 i) (gamT n hn ε δ hε0 hε1)
        ⊆ region (MTT n hn ε δ hε0 hε1) i.val := by
  classical
  intro i
  rcases eq_cubeL_or_cubeR i.property with h | h
  · rw [cenT, if_pos h, h, gamT]
    show Metric.ball _ _ ⊆ region (MT n _ _) (cubeL n)
    rw [region_cubeL]
    exact ball_subset_sbx n 0 _
  · have hne : ¬ (i.val = cubeL n) := by
      rw [h]; exact fun hc => cubeL_ne_cubeR hn hc.symm
    rw [cenT, if_neg hne, h, gamT]
    show Metric.ball _ _ ⊆ region (MT n _ _) (cubeR n)
    rw [region_cubeR]
    exact ball_subset_sbx n _ _

/-- The two regions, named. -/
theorem region_val_eq (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {i : Cube (A2 n)} (hi : i ∈ Ttc.toDNF (twoForm n)) :
    region (MTT n hn ε δ hε0 hε1) i = sbx n 0 (sideT n hn ε δ hε0 hε1)
      ∨ region (MTT n hn ε δ hε0 hε1) i = sbx n (loT n hn ε δ hε0 hε1) (sideT n hn ε δ hε0 hε1) :=
  region_eq_sbx hi

/-- **The witness's own decomposition, spelled out at the data it runs on.**
`Sol(F)` is the union of the two cubes' regions, and those are two distinct, nonempty,
disjoint boxes. -/
theorem sol_eq_union_two_T (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    sol (MTT n hn ε δ hε0 hε1) (twoForm n)
        = region (MTT n hn ε δ hε0 hε1) (cubeL n) ∪ region (MTT n hn ε δ hε0 hε1) (cubeR n)
      ∧ (region (MTT n hn ε δ hε0 hε1) (cubeL n)).Nonempty
      ∧ (region (MTT n hn ε δ hε0 hε1) (cubeR n)).Nonempty
      ∧ Disjoint (region (MTT n hn ε δ hε0 hε1) (cubeL n))
          (region (MTT n hn ε δ hε0 hε1) (cubeR n))
      ∧ region (MTT n hn ε δ hε0 hε1) (cubeL n) ≠ region (MTT n hn ε δ hε0 hε1) (cubeR n) :=
  sol_eq_union_two hn (sideT_pos n hn ε δ hε0 hε1).le (sideT_lt_loT n hn ε δ hε0 hε1)

/-- **The two inscribed balls have different centres.**  `γ̂` is shared, but `cen` is a
function of the cube and it is not constant — the branch of the analysis that the
single-cube witness leaves untouched. -/
theorem cenT_left_ne_right (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    cenT n hn ε δ hε0 hε1 ⟨cubeL n, mem_toDNF_cubeL⟩
      ≠ cenT n hn ε δ hε0 hε1 ⟨cubeR n, mem_toDNF_cubeR⟩ := by
  classical
  have hne : ¬ (cubeR n = cubeL n) := fun hc => cubeL_ne_cubeR hn hc.symm
  rw [cenT, cenT, if_pos rfl, if_neg hne]
  intro h
  have hk := congrArg (fun x : Space n => x ⟨0, hn⟩) h
  simp only [sbCentre_apply] at hk
  have h1 := sideT_pos n hn ε δ hε0 hε1
  have h2 := sideT_lt_loT n hn ε δ hε0 hε1
  linarith

theorem isBounded_sol_T (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    Bornology.IsBounded (sol (MTT n hn ε δ hε0 hε1) (twoForm n)) :=
  isBounded_sol_twoForm _ (sideT_pos n hn ε δ hε0 hε1).le

theorem hasLatticeEnum_T (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    HasLatticeEnum (MTT n hn ε δ hε0 hε1) (twoForm n) (rhoT n hn ε δ hε0 hε1) :=
  hasLatticeEnum_of_isBounded _ _ _ (isBounded_sol_T n hn ε δ hε0 hε1)

/-- Each cube's region has finitely many lattice points. -/
theorem finite_region_lat (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {i : Cube (A2 n)} (hi : i ∈ Ttc.toDNF (twoForm n)) :
    (region (MTT n hn ε δ hε0 hε1) i
      ∩ fineLattice n (latticeScale (rhoT n hn ε δ hε0 hε1))).Finite :=
  finite_region_lattice (toDNF_isDNFOf _) (hasLatticeEnum_T n hn ε δ hε0 hε1) hi

/-- **Each cube's region holds a lattice point** — the origin for the left box, the
corner for the right one, which is where the choice of `Ttc.TwoCube.loT` as a lattice
multiple pays off. -/
theorem nonempty_region_lat (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {i : Cube (A2 n)} (hi : i ∈ Ttc.toDNF (twoForm n)) :
    (region (MTT n hn ε δ hε0 hε1) i
      ∩ fineLattice n (latticeScale (rhoT n hn ε δ hε0 hε1))).Nonempty := by
  rcases region_val_eq n hn ε δ hε0 hε1 hi with h | h
  · refine ⟨0, ?_, ?_⟩
    · rw [h]; exact zero_mem_sbx_left (sideT_pos n hn ε δ hε0 hε1).le
    · intro k; exact ⟨0, by simp⟩
  · refine ⟨WithLp.toLp 2 (fun _ => loT n hn ε δ hε0 hε1), ?_, ?_⟩
    · rw [h]; exact corner_mem_sbx _ (sideT_pos n hn ε δ hε0 hε1).le
    · exact corner_mem_fineLattice n hn ε δ hε0 hε1

theorem ncard_region_lat_pos (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {i : Cube (A2 n)} (hi : i ∈ Ttc.toDNF (twoForm n)) :
    0 < (region (MTT n hn ε δ hε0 hε1) i
      ∩ fineLattice n (latticeScale (rhoT n hn ε δ hε0 hε1))).ncard :=
  (Set.ncard_pos (finite_region_lat n hn ε δ hε0 hε1 hi)).2
    (nonempty_region_lat n hn ε δ hε0 hε1 hi)

/-- **Each cube's lattice count is at most the total** — the count `N` the algorithm
enumerates runs over `Sol(F)`, which contains each region.  With two cubes this is a
strict inequality in general; the single-cube witness had it with equality. -/
theorem ncard_region_le_latticeCount (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) {i : Cube (A2 n)} (hi : i ∈ Ttc.toDNF (twoForm n)) :
    (region (MTT n hn ε δ hε0 hε1) i
        ∩ fineLattice n (latticeScale (rhoT n hn ε δ hε0 hε1))).ncard
      ≤ latticeCount (MTT n hn ε δ hε0 hε1) (twoForm n) (rhoT n hn ε δ hε0 hε1) :=
  Set.ncard_le_ncard
    (Set.inter_subset_inter_left _ (region_subset_sol (toDNF_isDNFOf _) hi))
    (finite_sol_lattice_of_hasLatticeEnum (hasLatticeEnum_T n hn ε δ hε0 hε1))

/-- Each cube's region has finite volume — it is a box of side `c`. -/
theorem volume_region_ne_top_T (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (i : {c : Cube (A2 n) // c ∈ Ttc.toDNF (twoForm n)}) :
    volume (region (MTT n hn ε δ hε0 hε1) i.val) ≠ ⊤ := by
  rcases region_val_eq n hn ε δ hε0 hε1 i.property with h | h <;> rw [h] <;>
    exact volume_sbx_ne_top _ _ _

/-- **Each cube's region has volume `cⁿ ≥ Thresh`** — both boxes are big enough for
the regime condition, at either corner. -/
theorem thresh_le_volume_region (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {i : Cube (A2 n)} (hi : i ∈ Ttc.toDNF (twoForm n)) :
    (parT n hn ε δ hε0 hε1).thresh
      ≤ (volume (region (MTT n hn ε δ hε0 hε1) i)).toReal := by
  have hs1 := one_le_sideT n hn ε δ hε0 hε1
  have hpow : sideT n hn ε δ hε0 hε1 ≤ sideT n hn ε δ hε0 hε1 ^ n := by
    calc sideT n hn ε δ hε0 hε1 = sideT n hn ε δ hε0 hε1 ^ 1 := (pow_one _).symm
      _ ≤ sideT n hn ε δ hε0 hε1 ^ n := pow_le_pow_right₀ hs1 hn
  have hts := thresh_le_sideT n hn ε δ hε0 hε1
  rcases region_val_eq n hn ε δ hε0 hε1 hi with h | h <;> rw [h] <;>
    rw [toReal_volume_sbx _ _ (sideT_pos n hn ε δ hε0 hε1).le] <;> linarith

/-! ## Part 6.  The ball-walk sampler, on the canonical description

`Ttc.ttc_volume_final` binds no polytope description: the linear system is the
canonical one read off `atoms` (`Exec/CanonPolytope`), and the sampler is the lazy
ball walk of `Ttc.e2eSampler` on top of it.  Both cubes get their own system, their
own inflated body, and their own warm start — the centres differ, so this is the
first time the construction is exercised at two distinct geometries.
-/

/-- The canonical row index type: one row per facet of the **whole** two-cube DNF. -/
abbrev JT (n : ℕ) := Fin (Nat.card (FacetIndex (Ttc.toDNF (twoForm n))))

theorem one_le_canonRfac (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ canonRfac (Ttc.toDNF (twoForm n)) := by
  rw [canonRfac]
  exact_mod_cast one_le_card_facets_two hn

theorem card_le_canonRfac (n : ℕ) :
    (Fintype.card (JT n) : ℝ) ≤ canonRfac (Ttc.toDNF (twoForm n)) := by
  rw [canonRfac, Fintype.card_fin]

/-- **The sampler's discrete law** — `Ttc.e2eSampD` at the witness's own data, i.e.
the rounding-then-rejection law of a lazy ball walk on the inflated dilated region of
each cube.  Nothing is assumed of it; `Ttc.TwoCube.samplerT` is the proof that a
`Ttc.KV97Sampler` for it exists. -/
noncomputable def sampT (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    Cube (A2 n) → Space n → ℝ :=
  e2eSampD (MTT n hn ε δ hε0 hε1) (Ttc.toDNF (twoForm n)) (rhoT n hn ε δ hε0 hε1)
    (parT n hn ε δ hε0 hε1).epsPrime (canonRfac (Ttc.toDNF (twoForm n)))
    (Jt := JT n)
    (canonAm (atomsT n hn ε δ hε0 hε1) (Ttc.toDNF (twoForm n)))
    (canonBv (atomsT n hn ε δ hε0 hε1) (Ttc.toDNF (twoForm n))
      (latticeScale (rhoT n hn ε δ hε0 hε1)))
    (cenT n hn ε δ hε0 hε1) (gamT n hn ε δ hε0 hε1)
    (canonDm (MTT n hn ε δ hε0 hε1) (Ttc.toDNF (twoForm n)) (rhoT n hn ε δ hε0 hε1))

/-- **The witness's ball-walk sampler, with no accuracy assumption.**  Its `law_tv`
is `Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope`, via
`Ttc.kv97SamplerOfBody`. -/
noncomputable def samplerT (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    KV97Sampler (A2 n) n (MTT n hn ε δ hε0 hε1) (Ttc.toDNF (twoForm n))
      (rhoT n hn ε δ hε0 hε1) (parT n hn ε δ hε0 hε1).epsPrime (sampT n hn ε δ hε0 hε1) :=
  e2eSampler hn (parT_epsPrime_pos n hn ε δ hε0 hε1) (JT n)
    (canonAm (atomsT n hn ε δ hε0 hε1) (Ttc.toDNF (twoForm n)))
    (canonBv (atomsT n hn ε δ hε0 hε1) (Ttc.toDNF (twoForm n))
      (latticeScale (rhoT n hn ε δ hε0 hε1)))
    (fun i => canon_smul_region_subset_body (atomsT n hn ε δ hε0 hε1)
      (toDNF_isPositive twoForm_isPositive) (latticeScale_pos _) i)
    (canonRfac (Ttc.toDNF (twoForm n))) (one_le_canonRfac n hn) (card_le_canonRfac n)
    (cenT n hn ε δ hε0 hε1) (gamT n hn ε δ hε0 hε1) (gamT_pos n hn ε δ hε0 hε1)
    (ball_subset_two n hn ε δ hε0 hε1)
    (canonDm (MTT n hn ε δ hε0 hε1) (Ttc.toDNF (twoForm n)) (rhoT n hn ε δ hε0 hε1))
    (canon_dist_le_canonDm (atomsT n hn ε δ hε0 hε1) (toDNF_isPositive twoForm_isPositive)
      (toDNF_isDNFOf _) (isBounded_sol_T n hn ε δ hε0 hε1) (rhoT n hn ε δ hε0 hε1))

/-- The dilated region of each cube has finitely many integer points. -/
theorem dilate_finite_T (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (i : {c : Cube (A2 n) // c ∈ Ttc.toDNF (twoForm n)}) :
    ((latticeScale (rhoT n hn ε δ hε0 hε1) • region (MTT n hn ε δ hε0 hε1) i.val)
      ∩ intLattice n : Set (Space n)).Finite := by
  have h : ((latticeScale (rhoT n hn ε δ hε0 hε1) • region (MTT n hn ε δ hε0 hε1) i.val)
        ∩ intLattice n : Set (Space n))
      = (fun x => latticeScale (rhoT n hn ε δ hε0 hε1) • x) ''
        (region (MTT n hn ε δ hε0 hε1) i.val
          ∩ fineLattice n (latticeScale (rhoT n hn ε δ hε0 hε1))) :=
    (Arlib.Lattice.image_smul_inter_fineLattice (latticeScale_pos _) _).symm
  rw [h]
  exact (finite_region_lat n hn ε δ hε0 hε1 i.property).image _

/-- …and at least one. -/
theorem dilate_nonempty_T (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (i : {c : Cube (A2 n) // c ∈ Ttc.toDNF (twoForm n)}) :
    ((latticeScale (rhoT n hn ε δ hε0 hε1) • region (MTT n hn ε δ hε0 hε1) i.val)
      ∩ intLattice n : Set (Space n)).Nonempty := by
  have h : ((latticeScale (rhoT n hn ε δ hε0 hε1) • region (MTT n hn ε δ hε0 hε1) i.val)
        ∩ intLattice n : Set (Space n))
      = (fun x => latticeScale (rhoT n hn ε δ hε0 hε1) • x) ''
        (region (MTT n hn ε δ hε0 hε1) i.val
          ∩ fineLattice n (latticeScale (rhoT n hn ε δ hε0 hε1))) :=
    (Arlib.Lattice.image_smul_inter_fineLattice (latticeScale_pos _) _).symm
  rw [h]
  exact (nonempty_region_lat n hn ε δ hε0 hε1 i.property).image _

/-- **`eq:almostuniform`, for each of the two cubes** — `Ttc.almostUniform_of_kv97Sampler`
at the constructed sampler.  The single-cube witness needed this at one geometry; here
it is needed at two, with different centres and different inflated bodies. -/
theorem almostUniform_T (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (i : {c : Cube (A2 n) // c ∈ Ttc.toDNF (twoForm n)}) :
    AlmostUniform (sampT n hn ε δ hε0 hε1 i.val)
      (region (MTT n hn ε δ hε0 hε1) i.val
        ∩ fineLattice n (latticeScale (rhoT n hn ε δ hε0 hε1)))
      (parT n hn ε δ hε0 hε1).epsPrime :=
  almostUniform_of_kv97Sampler (samplerT n hn ε δ hε0 hε1)
    (parT_epsPrime_pos n hn ε δ hε0 hε1)
    (by have := parT_epsPrime_le n hn ε δ hε0 hε1; linarith)
    i (dilate_finite_T n hn ε δ hε0 hε1 i) (dilate_nonempty_T n hn ε δ hε0 hε1 i)

/-! ## Part 7.  The regime condition `big`, at arity two

`big` asks that the total rate `∑ₛ θ s` — the sum over **all** enumerated lattice
points of `Sol(F)`, which here span *two* regions — clear `(1−ε')·Thresh/8`.

With one cube the sum is `N` copies of `V̂/N`, i.e. exactly `V̂`.  With two it is
not: the cube a point is assigned to varies with the point, the two per-cube
counts `N₁, N₂` differ (the boxes are congruent but their lattice sections need
not be), and the global count `N` is their sum.  The argument below is the one that
survives that: bound every rate below by the **smaller** of the two per-cube
uniform masses `q_i = (1−ε')·V̂ᵢ/Nᵢ`, and use `Nᵢ ≤ N` — whichever cube attains the
minimum, `N·q_i ≥ Nᵢ·q_i = (1−ε')·V̂ᵢ`, and `V̂ᵢ ≥ (1−ε')·Thresh` because *each* box
has volume `cⁿ ≥ Thresh`.
-/

/-- The volume oracle's own output at the witness's data. -/
noncomputable def volT (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (c : ℕ → Space n) : Cube (A2 n) → ℝ :=
  mcVol (MTT n hn ε δ hε0 hε1) (Ttc.toDNF (twoForm n)) (cenT n hn ε δ hε0 hε1)
    (gamT n hn ε δ hε0 hε1) (parT n hn ε δ hε0 hε1).epsPrime
    (parT n hn ε δ hε0 hε1).deltaPrime c

/-- The coins on which both `Vol_ED` calls landed inside their `(1±ε')` window. -/
noncomputable def goodT (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    Set (ℕ → Space n) :=
  mcGood (MTT n hn ε δ hε0 hε1) (Ttc.toDNF (twoForm n)) (cenT n hn ε δ hε0 hε1)
    (gamT n hn ε δ hε0 hε1) (parT n hn ε δ hε0 hε1).epsPrime
    (parT n hn ε δ hε0 hε1).deltaPrime

/-- The constructed level-`0` rates of the witness. -/
noncomputable def ratesT (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (c : ℕ → Space n) :
    Fin (latticeCount (MTT n hn ε δ hε0 hε1) (twoForm n) (rhoT n hn ε δ hε0 hε1)) → ℝ :=
  rates (MTT n hn ε δ hε0 hε1) (twoForm n) (Ttc.toDNF (twoForm n)) (rhoT n hn ε δ hε0 hε1)
    (sampT n hn ε δ hε0 hε1) (volT n hn ε δ hε0 hε1 c)

/-- `Nᵢ`: the number of lattice points of cube `i`'s region. -/
noncomputable def NT (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (i : Cube (A2 n)) : ℕ :=
  (region (MTT n hn ε δ hε0 hε1) i
    ∩ fineLattice n (latticeScale (rhoT n hn ε δ hε0 hε1))).ncard

/-- `qᵢ = (1−ε')·V̂ᵢ/Nᵢ`: the mass `eq:almostuniform` guarantees each lattice point of
cube `i` carries, times that cube's volume estimate. -/
noncomputable def qT (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (c : ℕ → Space n) (i : Cube (A2 n)) : ℝ :=
  (1 - (parT n hn ε δ hε0 hε1).epsPrime) / (NT n hn ε δ hε0 hε1 i : ℝ)
    * volT n hn ε δ hε0 hε1 c i

/-- **Each cube's volume estimate is at least `(1−ε')·Thresh`** — the two-sided
Monte-Carlo window applied at *each* of the two cubes, against the volume `cⁿ` of
that cube's box. -/
theorem thresh_le_volT (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {c : ℕ → Space n} (hc : c ∈ goodT n hn ε δ hε0 hε1)
    {i : Cube (A2 n)} (hi : i ∈ Ttc.toDNF (twoForm n)) :
    (1 - (parT n hn ε δ hε0 hε1).epsPrime) * (parT n hn ε δ hε0 hε1).thresh
      ≤ volT n hn ε δ hε0 hε1 c i := by
  have he := parT_epsPrime_le n hn ε δ hε0 hε1
  have hlo := (mcVol_mem_relErr (MTT n hn ε δ hε0 hε1) (Ttc.toDNF (twoForm n))
    (cenT n hn ε δ hε0 hε1) (gamT n hn ε δ hε0 hε1) (parT n hn ε δ hε0 hε1).epsPrime
    (parT n hn ε δ hε0 hε1).deltaPrime hc i hi).1
  have hvol := thresh_le_volume_region n hn ε δ hε0 hε1 hi
  have h1 : (1 - (parT n hn ε δ hε0 hε1).epsPrime) * (parT n hn ε δ hε0 hε1).thresh
      ≤ (1 - (parT n hn ε δ hε0 hε1).epsPrime)
        * (volume (region (MTT n hn ε δ hε0 hε1) i)).toReal :=
    mul_le_mul_of_nonneg_left hvol (by linarith)
  exact le_trans h1 hlo

/-- Each cube's volume estimate is strictly positive on a good coin. -/
theorem volT_pos (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {c : ℕ → Space n} (hc : c ∈ goodT n hn ε δ hε0 hε1) :
    ∀ i ∈ Ttc.toDNF (twoForm n), 0 < volT n hn ε δ hε0 hε1 c i :=
  mcVol_pos (MTT n hn ε δ hε0 hε1) (Ttc.toDNF (twoForm n)) (cenT n hn ε δ hε0 hε1)
    (gamT_pos n hn ε δ hε0 hε1) (parT_epsPrime_lt_one n hn ε δ hε0 hε1)
    (ball_subset_two n hn ε δ hε0 hε1) (volume_region_ne_top_T n hn ε δ hε0 hε1) hc

theorem qT_nonneg (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {c : ℕ → Space n} (hc : c ∈ goodT n hn ε δ hε0 hε1)
    {i : Cube (A2 n)} (hi : i ∈ Ttc.toDNF (twoForm n)) :
    0 ≤ qT n hn ε δ hε0 hε1 c i := by
  have he := parT_epsPrime_le n hn ε δ hε0 hε1
  have hv := (volT_pos n hn ε δ hε0 hε1 hc i hi).le
  exact mul_nonneg (div_nonneg (by linarith) (Nat.cast_nonneg _)) hv

/-- **`N·qᵢ` already clears the requirement**, for either cube: `Nᵢ ≤ N` and
`N·qᵢ ≥ (1−ε')·V̂ᵢ ≥ (1−ε')²·Thresh ≥ (1−ε')·Thresh/8`. -/
theorem thresh_le_count_mul_qT (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {c : ℕ → Space n} (hc : c ∈ goodT n hn ε δ hε0 hε1)
    {i : Cube (A2 n)} (hi : i ∈ Ttc.toDNF (twoForm n)) :
    (1 - (parT n hn ε δ hε0 hε1).epsPrime) * (parT n hn ε δ hε0 hε1).thresh / 8
      ≤ (latticeCount (MTT n hn ε δ hε0 hε1) (twoForm n) (rhoT n hn ε δ hε0 hε1) : ℝ)
        * qT n hn ε δ hε0 hε1 c i := by
  have he0 := parT_epsPrime_pos n hn ε δ hε0 hε1
  have he := parT_epsPrime_le n hn ε δ hε0 hε1
  have hT := parT_thresh_pos n hn ε δ hε0 hε1 hδ0 hδ1
  have hNpos : 0 < (NT n hn ε δ hε0 hε1 i : ℝ) := by
    have := ncard_region_lat_pos n hn ε δ hε0 hε1 hi
    exact_mod_cast this
  have hNle : (NT n hn ε δ hε0 hε1 i : ℝ)
      ≤ (latticeCount (MTT n hn ε δ hε0 hε1) (twoForm n) (rhoT n hn ε δ hε0 hε1) : ℝ) := by
    have := ncard_region_le_latticeCount n hn ε δ hε0 hε1 hi
    exact_mod_cast this
  have h1 : (NT n hn ε δ hε0 hε1 i : ℝ) * qT n hn ε δ hε0 hε1 c i
      = (1 - (parT n hn ε δ hε0 hε1).epsPrime) * volT n hn ε δ hε0 hε1 c i := by
    rw [qT]
    field_simp
  have h2 : (NT n hn ε δ hε0 hε1 i : ℝ) * qT n hn ε δ hε0 hε1 c i
      ≤ (latticeCount (MTT n hn ε δ hε0 hε1) (twoForm n) (rhoT n hn ε δ hε0 hε1) : ℝ)
        * qT n hn ε δ hε0 hε1 c i :=
    mul_le_mul_of_nonneg_right hNle (qT_nonneg n hn ε δ hε0 hε1 hc hi)
  have h3 := thresh_le_volT n hn ε δ hε0 hε1 hc hi
  have h4 : (1 - (parT n hn ε δ hε0 hε1).epsPrime)
        * ((1 - (parT n hn ε δ hε0 hε1).epsPrime) * (parT n hn ε δ hε0 hε1).thresh)
      ≤ (1 - (parT n hn ε δ hε0 hε1).epsPrime) * volT n hn ε δ hε0 hε1 c i :=
    mul_le_mul_of_nonneg_left h3 (by linarith)
  have h5 : (1 - (parT n hn ε δ hε0 hε1).epsPrime) * (parT n hn ε δ hε0 hε1).thresh / 8
      ≤ (1 - (parT n hn ε δ hε0 hε1).epsPrime)
        * ((1 - (parT n hn ε δ hε0 hε1).epsPrime) * (parT n hn ε δ hε0 hε1).thresh) := by
    have hu : (0 : ℝ) < 1 - (parT n hn ε δ hε0 hε1).epsPrime := by linarith
    have h18 : (0 : ℝ) ≤ 1 - (parT n hn ε δ hε0 hε1).epsPrime - 1 / 8 := by linarith
    nlinarith [mul_nonneg (mul_pos hu hT).le h18]
  rw [h1] at h2
  linarith

/-- **Every rate is at least the smaller of the two per-cube masses.**  The cube a
lattice point is assigned to is `Ttc.cubeAt`, which here can be *either* of the two —
the branch the single-cube witness never had. -/
theorem min_qT_le_ratesT (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {c : ℕ → Space n} (hc : c ∈ goodT n hn ε δ hε0 hε1)
    (s : Fin (latticeCount (MTT n hn ε δ hε0 hε1) (twoForm n) (rhoT n hn ε δ hε0 hε1))) :
    min (qT n hn ε δ hε0 hε1 c (cubeL n)) (qT n hn ε δ hε0 hε1 c (cubeR n))
      ≤ ratesT n hn ε δ hε0 hε1 c s := by
  obtain ⟨hmem, hreg⟩ :=
    cubeAt_spec (toDNF_isDNFOf (twoForm n)) (hasLatticeEnum_T n hn ε δ hε0 hε1) s
  set i := cubeAt (MTT n hn ε δ hε0 hε1) (twoForm n) (Ttc.toDNF (twoForm n))
    (rhoT n hn ε δ hε0 hε1) s with hi
  have hlower : (1 - (parT n hn ε δ hε0 hε1).epsPrime) / (NT n hn ε δ hε0 hε1 i : ℝ)
      ≤ sampT n hn ε δ hε0 hε1 i
        (latticeEnum (MTT n hn ε δ hε0 hε1) (twoForm n) (rhoT n hn ε δ hε0 hε1) s) :=
    (almostUniform_T n hn ε δ hε0 hε1 ⟨i, hmem⟩).lower
      ⟨hreg, (latticeEnum_mem (hasLatticeEnum_T n hn ε δ hε0 hε1) s).2⟩
  have hstep : qT n hn ε δ hε0 hε1 c i ≤ ratesT n hn ε δ hε0 hε1 c s :=
    mul_le_mul_of_nonneg_right hlower (volT_pos n hn ε δ hε0 hε1 hc i hmem).le
  refine le_trans ?_ hstep
  rcases eq_cubeL_or_cubeR hmem with h | h
  · rw [h]; exact min_le_left _ _
  · rw [h]; exact min_le_right _ _

/-- **`Ttc.ttc_volume_final`'s `big`, for the two-cube witness.**  The regime
condition is met at every coin on which the two `Vol_ED` calls landed well — and it
is met by the *constructed* ball-walk sampler, whose only route to the rates is
`eq:almostuniform`, i.e. mixing. -/
theorem big_two (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (c : ℕ → Space n) (hc : c ∈ goodT n hn ε δ hε0 hε1) :
    (1 - (parT n hn ε δ hε0 hε1).epsPrime) * (parT n hn ε δ hε0 hε1).thresh / 8
      ≤ ∑ s, ratesT n hn ε δ hε0 hε1 c s := by
  have hmin : (1 - (parT n hn ε δ hε0 hε1).epsPrime) * (parT n hn ε δ hε0 hε1).thresh / 8
      ≤ (latticeCount (MTT n hn ε δ hε0 hε1) (twoForm n) (rhoT n hn ε δ hε0 hε1) : ℝ)
        * min (qT n hn ε δ hε0 hε1 c (cubeL n)) (qT n hn ε δ hε0 hε1 c (cubeR n)) := by
    rcases le_total (qT n hn ε δ hε0 hε1 c (cubeL n)) (qT n hn ε δ hε0 hε1 c (cubeR n))
      with h | h
    · rw [min_eq_left h]
      exact thresh_le_count_mul_qT n hn ε δ hε0 hε1 hδ0 hδ1 hc mem_toDNF_cubeL
    · rw [min_eq_right h]
      exact thresh_le_count_mul_qT n hn ε δ hε0 hε1 hδ0 hδ1 hc mem_toDNF_cubeR
  refine le_trans hmin (le_trans (le_of_eq ?_)
    (Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => min_qT_le_ratesT n hn ε δ hε0 hε1 hc s))
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## Part 8.  The capstone, instantiated on a two-cube DNF

`Ttc.ttc_volume_final` is the development's strongest statement: it binds the
algorithm's inputs only — **no oracle** (the volume estimator is Monte Carlo, the
rates are constructed, the sampler is a lazy ball walk whose `law_tv` is proved) and
**no linear description of the input polytopes** (the system is read off `atoms` by
`Exec/CanonPolytope`) — and concludes a clean `1 − δ`.

Until now it had no witness at all; the witnesses in the development stop at
`Ttc.ttc_volume_endToEnd` / `Ttc.ttc_volume_clean`, and all of them are the
single-cube box.
-/

/-- The probability `Ttc.ttc_volume_final` bounds, on the two-cube witness: a pure
abbreviation for the integral, asserting nothing (`Ttc.TwoCube.twoProb_def`).  Its `δ`
argument is the **internal** failure parameter `δ₀ = 4δ/5`. -/
noncomputable def twoProb (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ENNReal :=
  ∫⁻ c, trajLaw (ratesT n hn ε δ hε0 hε1 c)
      {t : ℕ → Fin (latticeCount (MTT n hn ε δ hε0 hε1) (twoForm n)
          (rhoT n hn ε δ hε0 hε1)) → ℕ |
        ttcOutput (parT n hn ε δ hε0 hε1)
            (coveredOracles (MTT n hn ε δ hε0 hε1) (twoForm n) (rhoT n hn ε δ hε0 hε1)
              (volT n hn ε δ hε0 hε1 c))
            Ttc.toDNF (rhoT n hn ε δ hε0 hε1) (twoForm n) t
          ∈ relErr ε (volSol (MTT n hn ε δ hε0 hε1) (twoForm n))}
    ∂(MonteCarlo.coins n)

theorem twoProb_def (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    twoProb n hn ε δ hε0 hε1 =
      ∫⁻ c, trajLaw (ratesT n hn ε δ hε0 hε1 c)
          {t : ℕ → Fin (latticeCount (MTT n hn ε δ hε0 hε1) (twoForm n)
              (rhoT n hn ε δ hε0 hε1)) → ℕ |
            ttcOutput (parT n hn ε δ hε0 hε1)
                (coveredOracles (MTT n hn ε δ hε0 hε1) (twoForm n) (rhoT n hn ε δ hε0 hε1)
                  (volT n hn ε δ hε0 hε1 c))
                Ttc.toDNF (rhoT n hn ε δ hε0 hε1) (twoForm n) t
              ∈ relErr ε (volSol (MTT n hn ε δ hε0 hε1) (twoForm n))}
        ∂(MonteCarlo.coins n) := rfl

/-- The same quantity as a real number: the probability that the two-cube run's
output lands within `(1 ± ε)·Vol(F)`. -/
noncomputable def twoAcc (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) : ℝ :=
  (twoProb n hn ε δ hε0 hε1).toReal

/-- **`Ttc.ttc_volume_final`, instantiated on a DNF with two cubes**, at every
`(ε, δ) ∈ (0,1]²`.

The witness is the pair of disjoint boxes `[0,c]ⁿ` and `[lo, lo+c]ⁿ` with
`c = max 1 Thresh(ε, 4δ/5)` and `lo > c` a multiple of the lattice spacing.  Its DNF
has **two** cubes (`Ttc.TwoCube.card_toDNF_eq_two`), so `m = 2`: the per-cube error
composition, the two-call union bound behind `Ttc.Params.deltaPrime = δ/(4m)`, the
two-region `thm:decomposition`, and a `∑ s` running over lattice points of *two*
different regions with *different* ball centres are all exercised here, and by no
other witness in the development.

**Cost caveat — exponential in the dimension `n`, and now in the cube count too.**
Nothing about this witness makes the construction efficient.  The volume estimator
is hit-and-miss Monte Carlo at `Θ(Rⁿ/(ε'²δ'))` samples per cube, the ball walk's
certified step count is `2^Θ(n)·log(M·Vol(P′)/ε′)`, and the transcription enumerates
`Ttc.latticeCount` lattice points, which for these boxes is `Θ((c·10^ρ)ⁿ)` — all
exponential in `n`.  With `m = 2` every one of those costs is paid twice, and the
charged bound `m·(C_vol + C_sample·Thresh)` grows with `m`; `Thresh` itself carries a
`log m`.  What is established is *unconditional correctness*, not efficiency;
`thm:runtime` remains out of scope. -/
theorem ttc_volume_final_two_cube (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (1 - δ ≤ twoAcc n hn ε (4 * δ / 5) hε0 hε1)
    ∧
    (∀ (c : ℕ → Space n)
        (t : ℕ → Fin (latticeCount (MTT n hn ε (4 * δ / 5) hε0 hε1) (twoForm n)
          (rhoT n hn ε (4 * δ / 5) hε0 hε1)) → ℕ)
        (cVol cSample thr : ℕ),
      (thr : ℝ) = (parT n hn ε (4 * δ / 5) hε0 hε1).thresh →
      Terminates (parT n hn ε (4 * δ / 5) hε0 hε1)
          (coveredOracles (MTT n hn ε (4 * δ / 5) hε0 hε1) (twoForm n)
            (rhoT n hn ε (4 * δ / 5) hε0 hε1) (volT n hn ε (4 * δ / 5) hε0 hε1 c) t)
          (Ttc.toDNF (twoForm n)) →
      runCost (parT n hn ε (4 * δ / 5) hε0 hε1)
          (coveredOracles (MTT n hn ε (4 * δ / 5) hε0 hε1) (twoForm n)
            (rhoT n hn ε (4 * δ / 5) hε0 hε1) (volT n hn ε (4 * δ / 5) hε0 hε1 c) t)
          cVol cSample (rhoT n hn ε (4 * δ / 5) hε0 hε1) (Ttc.toDNF (twoForm n))
        ≤ (Ttc.toDNF (twoForm n)).length * (cVol + cSample * thr)) := by
  have h0 : (0 : ℝ) < 4 * δ / 5 := by linarith
  have h1 : (4 : ℝ) * δ / 5 ≤ 1 := by linarith
  exact ttc_volume_final (atomsT n hn ε (4 * δ / 5) hε0 hε1) (twoForm n) ε δ
    hε0 hε1 hδ0 hδ1 hn (MTT n hn ε (4 * δ / 5) hε0 hε1) rfl Ttc.toDNF
    (toDNF_isDNFOf _) (toDNF_isPositive twoForm_isPositive)
    (one_le_card_cubes_two hn) (one_le_card_facets_two hn)
    (parT n hn ε (4 * δ / 5) hε0 hε1) rfl
    (by rw [length_toDNF_twoForm, parT_m])
    (isBounded_sol_T n hn ε (4 * δ / 5) hε0 hε1)
    (coeff_ne_zero_two _ _)
    (cenT n hn ε (4 * δ / 5) hε0 hε1) (gamT n hn ε (4 * δ / 5) hε0 hε1)
    (gamT_pos n hn ε (4 * δ / 5) hε0 hε1) (ball_subset_two n hn ε (4 * δ / 5) hε0 hε1)
    (fun c hc => big_two n hn ε (4 * δ / 5) hε0 hε1 h0 h1 c hc)

/-- **The two-cube guarantee, restated on the named probability.** -/
theorem two_cube_acc_ge (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    1 - δ ≤ twoAcc n hn ε (4 * δ / 5) hε0 hε1 :=
  (ttc_volume_final_two_cube n hn ε δ hε0 hε1 hδ0 hδ1).1

/-- **`Ttc.ttc_volume_final` on a two-cube DNF, at two structurally different
parameter pairs, with the achieved bound as a positive numeral.**

* `(ε, δ) = (1/3, 9/10)`: the bound is `1/10 > 0`, and `δ = 9/10` lies in `(4/5, 1)`,
  the regime where `Ttc.ttc_volume_endToEnd`'s budget `1 − δ − δ/4 = −1/8` certifies
  nothing at all.
* `(ε, δ) = (1/2, 1/4)`: a different accuracy *and* a different confidence, so the
  parameters are not forced — the two runs have different sides
  `Ttc.TwoCube.sideT`, different precisions `Ttc.TwoCube.rhoT`, different corners
  `Ttc.TwoCube.loT` and different parameter blocks `Ttc.TwoCube.parT`.

Both numerals are proved strictly positive *in the statement*, so neither conclusion
is the vacuous `0 ≤ (…).toReal`.

The cost caveat of `Ttc.TwoCube.ttc_volume_final_two_cube` applies verbatim: both
runs are exponential in `n`, and pay every exponential cost twice. -/
theorem ttc_volume_final_two_cube_at (n : ℕ) (hn : 1 ≤ n)
    (hε₁ : (0 : ℝ) < 1/3) (hε₁' : (1/3 : ℝ) ≤ 1)
    (hε₂ : (0 : ℝ) < 1/2) (hε₂' : (1/2 : ℝ) ≤ 1) :
    ((0 : ℝ) < 1/10 ∧ (1/10 : ℝ) ≤ twoAcc n hn (1/3) (4 * (9/10) / 5) hε₁ hε₁'
      ∧ (4/5 : ℝ) < 9/10 ∧ (9/10 : ℝ) < 1)
    ∧ ((0 : ℝ) < 3/4 ∧ (3/4 : ℝ) ≤ twoAcc n hn (1/2) (4 * (1/4) / 5) hε₂ hε₂') := by
  refine ⟨⟨by norm_num, ?_, by norm_num, by norm_num⟩, ⟨by norm_num, ?_⟩⟩
  · have h := two_cube_acc_ge n hn (1/3) (9/10) hε₁ hε₁' (by norm_num) (by norm_num)
    linarith
  · have h := two_cube_acc_ge n hn (1/2) (1/4) hε₂ hε₂' (by norm_num) (by norm_num)
    linarith

/-- **The guarantee is a genuine number, not `ENNReal.toReal ⊤ = 0`.**  A positive
lower bound on the `toReal` forces the integral itself to be nonzero and finite. -/
theorem twoProb_pos_ne_top_at_nine_tenths (n : ℕ) (hn : 1 ≤ n)
    (hε0 : (0 : ℝ) < 1/3) (hε1 : (1/3 : ℝ) ≤ 1) :
    0 < twoProb n hn (1/3) (4 * (9/10) / 5) hε0 hε1
      ∧ twoProb n hn (1/3) (4 * (9/10) / 5) hε0 hε1 ≠ ⊤ := by
  have h := (ttc_volume_final_two_cube_at n hn hε0 hε1 (by norm_num) (by norm_num)).1.2.1
  have hpos : 0 < (twoProb n hn (1/3) (4 * (9/10) / 5) hε0 hε1).toReal :=
    lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/10) h
  exact ⟨(ENNReal.toReal_pos_iff.1 hpos).1, (ENNReal.toReal_pos_iff.1 hpos).2.ne⟩

end TwoCube

end Ttc

/-! ## Axiom profile

Every declaration of this file, checked transitively (`CLAUDE.md` §4).  Expect
`[propext, Classical.choice, Quot.sound]` throughout — no `sorry`, no custom axiom,
no `native_decide`. -/

#print axioms Ttc.TwoCube.sbx
#print axioms Ttc.TwoCube.mem_sbx
#print axioms Ttc.TwoCube.sbAtoms
#print axioms Ttc.TwoCube.sbAtoms_inl_coeff
#print axioms Ttc.TwoCube.sbAtoms_inl_bound
#print axioms Ttc.TwoCube.sbAtoms_inr_coeff
#print axioms Ttc.TwoCube.sbAtoms_inr_bound
#print axioms Ttc.TwoCube.halfspace_sbAtoms_inl
#print axioms Ttc.TwoCube.halfspace_sbAtoms_inr
#print axioms Ttc.TwoCube.sbAtoms_coeff_sq_sum
#print axioms Ttc.TwoCube.sbCentre
#print axioms Ttc.TwoCube.sbCentre_apply
#print axioms Ttc.TwoCube.ball_subset_sbx
#print axioms Ttc.TwoCube.sbx_subset_closedBall
#print axioms Ttc.TwoCube.isBounded_sbx
#print axioms Ttc.TwoCube.volume_sbx
#print axioms Ttc.TwoCube.volume_sbx_ne_top
#print axioms Ttc.TwoCube.toReal_volume_sbx
#print axioms Ttc.TwoCube.A2
#print axioms Ttc.TwoCube.twoAtoms
#print axioms Ttc.TwoCube.twoAtoms_inl
#print axioms Ttc.TwoCube.twoAtoms_inr
#print axioms Ttc.TwoCube.twoAtoms_coeff_sq_sum
#print axioms Ttc.TwoCube.cubeL
#print axioms Ttc.TwoCube.cubeR
#print axioms Ttc.TwoCube.twoForm
#print axioms Ttc.TwoCube.twoForm_isPositive
#print axioms Ttc.TwoCube.toDNF_twoForm
#print axioms Ttc.TwoCube.mem_cubeL
#print axioms Ttc.TwoCube.mem_cubeR
#print axioms Ttc.TwoCube.exists_of_mem_cubeL
#print axioms Ttc.TwoCube.exists_of_mem_cubeR
#print axioms Ttc.TwoCube.cubeL_isPositive
#print axioms Ttc.TwoCube.cubeR_isPositive
#print axioms Ttc.TwoCube.cubeL_ne_cubeR
#print axioms Ttc.TwoCube.mem_toDNF_cubeL
#print axioms Ttc.TwoCube.mem_toDNF_cubeR
#print axioms Ttc.TwoCube.eq_cubeL_or_cubeR
#print axioms Ttc.TwoCube.card_toDNF_eq_two
#print axioms Ttc.TwoCube.two_le_card_cubes_two
#print axioms Ttc.TwoCube.one_le_card_cubes_two
#print axioms Ttc.TwoCube.one_le_card_facets_two
#print axioms Ttc.TwoCube.length_toDNF_twoForm
#print axioms Ttc.TwoCube.MT
#print axioms Ttc.TwoCube.forall_halfspace_iff
#print axioms Ttc.TwoCube.region_cubeL
#print axioms Ttc.TwoCube.region_cubeR
#print axioms Ttc.TwoCube.region_eq_sbx
#print axioms Ttc.TwoCube.sol_twoForm
#print axioms Ttc.TwoCube.zero_mem_sbx_left
#print axioms Ttc.TwoCube.corner_mem_sbx
#print axioms Ttc.TwoCube.disjoint_sbx
#print axioms Ttc.TwoCube.sol_eq_union_two
#print axioms Ttc.TwoCube.isBounded_sol_twoForm
#print axioms Ttc.TwoCube.coeff_ne_zero_two
#print axioms Ttc.TwoCube.parT
#print axioms Ttc.TwoCube.parT_eps
#print axioms Ttc.TwoCube.parT_delta
#print axioms Ttc.TwoCube.parT_m
#print axioms Ttc.TwoCube.parT_epsPrime
#print axioms Ttc.TwoCube.parT_eta
#print axioms Ttc.TwoCube.parT_epsPrime_pos
#print axioms Ttc.TwoCube.parT_epsPrime_le
#print axioms Ttc.TwoCube.parT_epsPrime_lt_one
#print axioms Ttc.TwoCube.parT_thresh_pos
#print axioms Ttc.TwoCube.sideT
#print axioms Ttc.TwoCube.one_le_sideT
#print axioms Ttc.TwoCube.sideT_pos
#print axioms Ttc.TwoCube.thresh_le_sideT
#print axioms Ttc.TwoCube.gamT
#print axioms Ttc.TwoCube.gamT_pos
#print axioms Ttc.TwoCube.rhoT
#print axioms Ttc.TwoCube.loT
#print axioms Ttc.TwoCube.sideT_lt_loT
#print axioms Ttc.TwoCube.corner_mem_fineLattice
#print axioms Ttc.TwoCube.atomsT
#print axioms Ttc.TwoCube.MTT
#print axioms Ttc.TwoCube.cenT
#print axioms Ttc.TwoCube.ball_subset_two
#print axioms Ttc.TwoCube.region_val_eq
#print axioms Ttc.TwoCube.sol_eq_union_two_T
#print axioms Ttc.TwoCube.cenT_left_ne_right
#print axioms Ttc.TwoCube.isBounded_sol_T
#print axioms Ttc.TwoCube.hasLatticeEnum_T
#print axioms Ttc.TwoCube.finite_region_lat
#print axioms Ttc.TwoCube.nonempty_region_lat
#print axioms Ttc.TwoCube.ncard_region_lat_pos
#print axioms Ttc.TwoCube.ncard_region_le_latticeCount
#print axioms Ttc.TwoCube.volume_region_ne_top_T
#print axioms Ttc.TwoCube.thresh_le_volume_region
#print axioms Ttc.TwoCube.JT
#print axioms Ttc.TwoCube.one_le_canonRfac
#print axioms Ttc.TwoCube.card_le_canonRfac
#print axioms Ttc.TwoCube.sampT
#print axioms Ttc.TwoCube.samplerT
#print axioms Ttc.TwoCube.dilate_finite_T
#print axioms Ttc.TwoCube.dilate_nonempty_T
#print axioms Ttc.TwoCube.almostUniform_T
#print axioms Ttc.TwoCube.volT
#print axioms Ttc.TwoCube.goodT
#print axioms Ttc.TwoCube.ratesT
#print axioms Ttc.TwoCube.NT
#print axioms Ttc.TwoCube.qT
#print axioms Ttc.TwoCube.thresh_le_volT
#print axioms Ttc.TwoCube.volT_pos
#print axioms Ttc.TwoCube.qT_nonneg
#print axioms Ttc.TwoCube.thresh_le_count_mul_qT
#print axioms Ttc.TwoCube.min_qT_le_ratesT
#print axioms Ttc.TwoCube.big_two
#print axioms Ttc.TwoCube.twoProb
#print axioms Ttc.TwoCube.twoProb_def
#print axioms Ttc.TwoCube.twoAcc
#print axioms Ttc.TwoCube.ttc_volume_final_two_cube
#print axioms Ttc.TwoCube.two_cube_acc_ge
#print axioms Ttc.TwoCube.ttc_volume_final_two_cube_at
#print axioms Ttc.TwoCube.twoProb_pos_ne_top_at_nine_tenths
