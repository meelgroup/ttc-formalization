/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Nonconv.BallFacet
import Ttc.Dnf

/-!
# The box `[0,c]ⁿ`, as a non-degenerate witness

Geometric facts about the concrete polytope `[0,c]ⁿ ⊆ ℝⁿ`, collected so that a
*non-degenerate* non-vacuity witness for `Ttc.TtcProb` can be built from them.

The development's original witness (`trivialProb`, since **removed**) inhabited
`Ttc.TtcProb` with the empty DNF: every geometric field was vacuous because there
were no polytopes at all. That refuted vacuity of the headline theorem, but it
exercised none of the geometry — `Sol(F) = ∅`, `Vol(F) = 0`, and the count `0`.
The box is the
smallest instance that does exercise it: it is a genuine polytope, cut out by
`2n` linear atoms (`Ttc.boxAtoms`), it contains an `ℓ₂`-ball of radius `c/2`
(`Ttc.ball_subset_box`, the paper's `lem:nonconv` hypothesis), it has finite
volume (`Ttc.volume_box_ne_top`), and its lattice-point count is finite and
nonzero (`Ttc.box_lattice_finite`, `Ttc.box_lattice_nonempty`).

**The side length `c` is a parameter, not `1`.** `alg:ttc`'s `Thresh`
(`Model/Prelude`) is in the low ten-thousands at `ε = δ = 1`, and the estimate
needs the instance's normalised lattice count to clear roughly
`(1 − ε')·Thresh/8`; the *unit* box has count `≈ 1` and cannot. Carrying `c`
lets the witness be made as large as the parameter block demands — see
`Ttc.box_lattice_card_ge` for the count it delivers.

All statements are about the repo's own `Ttc.LinAtom.halfspace` / `Ttc.region` /
`Ttc.sol` / `Ttc.fineLattice`, not about a re-axiomatised copy of the box.
-/

namespace Ttc

open MeasureTheory Set

variable {n : ℕ}

/-! ## The `2n` atoms of the box -/

/-- The `2n` linear atoms cutting out `[0,c]ⁿ`: `Sum.inl k` is the constraint
`x k ≤ c`, and `Sum.inr k` is the constraint `-x k ≤ 0`, i.e. `0 ≤ x k`. Each is
a row `A x ≤ b` in the shape `Ttc.LinAtom` demands, so the box is an instance of
the paper's LRA fragment. -/
def boxAtoms (n : ℕ) (c : ℝ) : (Fin n ⊕ Fin n) → LinAtom n
  | .inl k => ⟨fun i => if i = k then 1 else 0, c⟩
  | .inr k => ⟨fun i => if i = k then -1 else 0, 0⟩

@[simp] theorem boxAtoms_inl_coeff (c : ℝ) (k i : Fin n) :
    (boxAtoms n c (.inl k)).coeff i = if i = k then 1 else 0 := rfl

@[simp] theorem boxAtoms_inl_bound (c : ℝ) (k : Fin n) :
    (boxAtoms n c (.inl k)).bound = c := rfl

@[simp] theorem boxAtoms_inr_coeff (c : ℝ) (k i : Fin n) :
    (boxAtoms n c (.inr k)).coeff i = if i = k then -1 else 0 := rfl

@[simp] theorem boxAtoms_inr_bound (c : ℝ) (k : Fin n) :
    (boxAtoms n c (.inr k)).bound = 0 := rfl

/-- The half-space of `Sum.inl k` is `{x | x k ≤ c}`: the linear form of a
coordinate atom evaluates to that coordinate. -/
theorem halfspace_boxAtoms_inl (c : ℝ) (k : Fin n) :
    (boxAtoms n c (.inl k)).halfspace = {x : Space n | x k ≤ c} := by
  ext x
  simp [LinAtom.halfspace]

/-- The half-space of `Sum.inr k` is `{x | 0 ≤ x k}`. -/
theorem halfspace_boxAtoms_inr (c : ℝ) (k : Fin n) :
    (boxAtoms n c (.inr k)).halfspace = {x : Space n | 0 ≤ x k} := by
  ext x
  simp [LinAtom.halfspace]

/-- **The box is the intersection of the `2n` half-spaces.** -/
theorem boxRegion_eq (n : ℕ) (c : ℝ) :
    (⋂ j : Fin n ⊕ Fin n, (boxAtoms n c j).halfspace)
      = {x : Space n | ∀ k, 0 ≤ x k ∧ x k ≤ c} := by
  ext x
  simp only [Set.mem_iInter, Set.mem_setOf_eq]
  constructor
  · intro h k
    exact ⟨by simpa [halfspace_boxAtoms_inr] using h (.inr k),
           by simpa [halfspace_boxAtoms_inl] using h (.inl k)⟩
  · rintro h (k | k)
    · simpa [halfspace_boxAtoms_inl] using (h k).2
    · simpa [halfspace_boxAtoms_inr] using (h k).1

/-! ## The inscribed ball

`lem:nonconv`'s hypothesis on each polytope is that it contains an `ℓ₂`-ball of
radius `γ`; for the box the largest such ball is the one of radius `c/2`
about the centre `(c/2, …, c/2)`. The argument is the same Cauchy–Schwarz step as
`Ttc.FacetSystem.ball_subset_piece`, specialised to a coordinate atom.
-/

/-- The centre of the box, `(c/2, …, c/2)`. -/
noncomputable def boxCentre (n : ℕ) (c : ℝ) : Space n := WithLp.toLp 2 (fun _ => c / 2)

@[simp] theorem boxCentre_apply (c : ℝ) (k : Fin n) : (boxCentre n c) k = c / 2 := rfl

/-- The squared Euclidean length of a coordinate atom's coefficient vector. -/
theorem sum_single_sq (k : Fin n) (a : ℝ) :
    ∑ i, (if i = k then a else 0) ^ 2 = a ^ 2 := by
  have h : ∀ i : Fin n, (if i = k then a else 0) ^ 2 = if i = k then a ^ 2 else 0 := by
    intro i; split <;> simp
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h i)]
  simp

/-- The Euclidean norm of a coordinate atom's coefficient vector. -/
theorem coeffNorm_single (k : Fin n) (a : ℝ) :
    coeffNorm (fun i => if i = k then a else 0) = |a| := by
  rw [coeffNorm, sum_single_sq, Real.sqrt_sq_eq_abs]

/-- Each coordinate is bounded by the Euclidean norm — Cauchy–Schwarz against the
coordinate atom `e_k`. -/
theorem coord_le_norm (y : Space n) (k : Fin n) : y k ≤ ‖y‖ := by
  have h := sum_mul_le_coeffNorm_mul (fun i => if i = k then (1 : ℝ) else 0) y
  rw [coeffNorm_single] at h
  simpa using h

/-- The same bound below: `−y k ≤ ‖y‖`, by Cauchy–Schwarz against `−e_k`. -/
theorem neg_coord_le_norm (y : Space n) (k : Fin n) : -y k ≤ ‖y‖ := by
  have h := sum_mul_le_coeffNorm_mul (fun i => if i = k then (-1 : ℝ) else 0) y
  rw [coeffNorm_single] at h
  simpa using h

/-- **The box contains the inscribed ball of radius `c/2` about its centre** —
the polytope is non-degenerate, which is exactly `lem:nonconv`'s hypothesis at
`γ = c/2`. -/
theorem ball_subset_box (n : ℕ) (c : ℝ) :
    Metric.ball (boxCentre n c) (c / 2) ⊆ {x : Space n | ∀ k, 0 ≤ x k ∧ x k ≤ c} := by
  intro x hx k
  have hd : ‖x - boxCentre n c‖ < c / 2 := by rwa [Metric.mem_ball, dist_eq_norm] at hx
  have hxk : (x - boxCentre n c) k = x k - c / 2 := rfl
  have h1 := coord_le_norm (x - boxCentre n c) k
  have h2 := neg_coord_le_norm (x - boxCentre n c) k
  rw [hxk] at h1 h2
  constructor <;> linarith

/-! ## Finite volume -/

/-- **The box has finite volume.** It is contained in the closed ball of radius
`√(n·c²)`, which is compact, and `volume` is finite on compacts. -/
theorem volume_box_ne_top (n : ℕ) (c : ℝ) :
    volume {x : Space n | ∀ k, 0 ≤ x k ∧ x k ≤ c} ≠ ⊤ := by
  have hsub : {x : Space n | ∀ k, 0 ≤ x k ∧ x k ≤ c}
      ⊆ Metric.closedBall (0 : Space n) (Real.sqrt (n * c ^ 2)) := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin n, c ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h := hx i
          rw [Real.norm_eq_abs, abs_of_nonneg h.1]
          nlinarith [h.1, h.2]
      _ = n * c ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact ne_top_of_le_ne_top
    (IsCompact.measure_lt_top (isCompact_closedBall (0 : Space n) (Real.sqrt (n * c ^ 2)))).ne
    (measure_mono hsub)

/-! ## Lattice points of the box

The count `|P ∩ 𝕃ⁿ|` the algorithm estimates must be finite (to be a `ℕ`) and,
for a non-degenerate witness, large. Finiteness holds at every refinement
`𝕃ⁿ = r⁻¹·ℤⁿ` with `r > 0`; the lower bound on the count is
`Ttc.box_lattice_card_ge` below.
-/

/-- On the lattice `r⁻¹·ℤⁿ` a coordinate is recovered from its scaled floor. -/
theorem coord_eq_of_mem_fineLattice {r : ℝ} (hr : 0 < r) {x : Space n}
    (hx : x ∈ fineLattice n r) (i : Fin n) : x i = r⁻¹ * (⌊r * x i⌋ : ℝ) := by
  obtain ⟨k, hk⟩ := hx i
  have hrx : r * x i = (k : ℝ) := by rw [hk]; field_simp
  rw [hrx, Int.floor_intCast]
  exact hk

/-- **The box holds only finitely many lattice points.** The scaled floor
`x ↦ (⌊r·x k⌋)ₖ` is injective on the lattice points of the box and lands in the
finite integer box `[0, ⌈r·c⌉]ⁿ`. -/
theorem box_lattice_finite (n : ℕ) (c : ℝ) {r : ℝ} (hr : 0 < r) :
    ({x : Space n | ∀ k, 0 ≤ x k ∧ x k ≤ c} ∩ fineLattice n r).Finite := by
  set S : Set (Space n) := {x : Space n | ∀ k, 0 ≤ x k ∧ x k ≤ c} ∩ fineLattice n r with hSdef
  set g : Space n → (Fin n → ℤ) := fun x i => ⌊r * x i⌋ with hgdef
  have hcoord : ∀ x ∈ S, ∀ i, x i = r⁻¹ * (g x i : ℝ) := fun x hx i =>
    coord_eq_of_mem_fineLattice hr hx.2 i
  refine Set.Finite.of_finite_image (f := g) ?_ ?_
  · refine Set.Finite.subset
      (Set.Finite.pi (fun _ : Fin n => Set.finite_Icc (0 : ℤ) ⌈r * c⌉)) ?_
    rintro z ⟨x, hx, rfl⟩
    rw [Set.mem_univ_pi]
    intro i
    have hb := hx.1 i
    refine ⟨Int.floor_nonneg.2 (mul_nonneg hr.le hb.1), ?_⟩
    exact le_trans (Int.floor_mono (mul_le_mul_of_nonneg_left hb.2 hr.le))
      (Int.floor_le_ceil (r * c))
  · intro x hx y hy hxy
    refine (WithLp.ext_iff 2).2 (funext fun i => ?_)
    show x i = y i
    rw [hcoord x hx i, hcoord y hy i, hxy]

/-- **The box holds at least one lattice point**, the origin — so the witness is
non-degenerate on the counting side too: `|P ∩ 𝕃ⁿ| ≥ 1`. -/
theorem box_lattice_nonempty (n : ℕ) {c : ℝ} (hc : 0 ≤ c) (r : ℝ) :
    ({x : Space n | ∀ k, 0 ≤ x k ∧ x k ≤ c} ∩ fineLattice n r).Nonempty :=
  ⟨0, fun k => by simpa using hc, fun i => ⟨0, by simp⟩⟩

/-- **The box holds at least `(⌊c·r⌋ + 1)ⁿ` lattice points.** Each coordinate can
independently be any of `0, 1/r, …, ⌊c·r⌋/r`, all of which lie in `[0,c]`; the map
`z ↦ (z k / r)ₖ` from `(Fin n → Fin (⌊c·r⌋+1))` is injective into the set. This is
what makes the witness *quantitatively* non-degenerate: the count grows like
`(c·r)ⁿ`, so a large enough `c` clears any threshold the parameter block imposes. -/
theorem box_lattice_card_ge (n : ℕ) {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    (⌊c * r⌋₊ + 1) ^ n
      ≤ ({x : Space n | ∀ k, 0 ≤ x k ∧ x k ≤ c} ∩ fineLattice n r).ncard := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  set N := ⌊c * r⌋₊ + 1 with hNdef
  set f : (Fin n → Fin N) → Space n :=
    fun z => WithLp.toLp 2 (fun k => ((z k : ℕ) : ℝ) / r) with hfdef
  have hfcoord : ∀ (z : Fin n → Fin N) (k : Fin n), (f z) k = ((z k : ℕ) : ℝ) / r :=
    fun _ _ => rfl
  have hmem : ∀ z : Fin n → Fin N,
      f z ∈ {x : Space n | ∀ k, 0 ≤ x k ∧ x k ≤ c} ∩ fineLattice n r := by
    intro z
    refine ⟨fun k => ⟨?_, ?_⟩, fun k => ⟨(z k : ℕ), ?_⟩⟩
    · rw [hfcoord]
      positivity
    · rw [hfcoord, div_le_iff₀ hr]
      have h1 : ((z k : ℕ) : ℝ) ≤ (⌊c * r⌋₊ : ℝ) := by
        exact_mod_cast Nat.lt_succ_iff.1 (z k).isLt
      have h2 : (⌊c * r⌋₊ : ℝ) ≤ c * r := Nat.floor_le (mul_pos hc hr).le
      linarith
    · rw [hfcoord]
      push_cast
      rw [div_eq_inv_mul]
  have hinj : Set.InjOn f Set.univ := by
    intro z _ w _ hzw
    funext k
    have hk : ((z k : ℕ) : ℝ) / r = ((w k : ℕ) : ℝ) / r :=
      congrFun ((WithLp.ext_iff 2).1 hzw) k
    have hval : ((z k : ℕ) : ℝ) = ((w k : ℕ) : ℝ) := by
      field_simp at hk
      exact hk
    exact Fin.val_injective (by exact_mod_cast hval)
  have hcard : Nat.card (Fin n → Fin N) = N ^ n := by
    simp [Nat.card_eq_fintype_card]
  calc (⌊c * r⌋₊ + 1) ^ n = Nat.card (Fin n → Fin N) := by rw [hcard]
    _ = (Set.univ : Set (Fin n → Fin N)).ncard := (Set.ncard_univ _).symm
    _ ≤ _ := Set.ncard_le_ncard_of_injOn f (fun z _ => hmem z) hinj
              (box_lattice_finite n c hr)

/-! ## The box as a cube of a positive DNF

`Ttc.TtcProb` does not talk about intersections of half-spaces: its geometric
fields (`ball_subset`, `volume_ne_top`, `isPositive`, `normal_ne_zero`) are stated
over `Ttc.region M c` for the cubes `c` of the DNF the AllSAT step returns. So the
box has to be presented as such a cube — all `2n` atoms as *positive* literals,
which is exactly what `Ttc.DNF.IsPositive` demands (a negated atom would denote an
*open* half-space; see the README, finding 5). The single-cube DNF `[boxCube n]`
is then the decomposition of `Sol(F)` for the formula "all `2n` atoms hold".

The cube and the DNF are about *atom indices* only, so the side length `c` does
not appear in them — it enters solely through the atom family `Ttc.boxAtoms n c`.
-/

/-- The list of all `2n` atoms. -/
def boxAtomList (n : ℕ) : List (Fin n ⊕ Fin n) :=
  (List.finRange n).map Sum.inl ++ (List.finRange n).map Sum.inr

/-- The list really does enumerate every atom. -/
theorem mem_boxAtomList (j : Fin n ⊕ Fin n) : j ∈ boxAtomList n := by
  obtain (k | k) := j <;> simp [boxAtomList]

/-- The box as a **cube**: every one of the `2n` atoms of `Ttc.boxAtoms`,
occurring positively. -/
def boxCube (n : ℕ) : Cube (Fin n ⊕ Fin n) :=
  (boxAtomList n).map fun j => ⟨j, true⟩

/-- Every atom really does occur in `Ttc.boxCube`, positively. -/
theorem mem_boxCube (j : Fin n ⊕ Fin n) :
    (⟨j, true⟩ : Lit (Fin n ⊕ Fin n)) ∈ boxCube n :=
  List.mem_map_of_mem (mem_boxAtomList j)

/-- The literals of `Ttc.boxCube` are exactly the positive ones. -/
theorem eq_of_mem_boxCube {l : Lit (Fin n ⊕ Fin n)} (hl : l ∈ boxCube n) :
    l = ⟨l.atom, true⟩ := by
  rw [boxCube, List.mem_map] at hl
  obtain ⟨j, -, rfl⟩ := hl
  rfl

/-- **The cube is positive** — `Ttc.TtcProb.isPositive`, for one cube. -/
theorem boxCube_isPositive : Cube.IsPositive (boxCube n) := fun _ hl =>
  congrArg Lit.pos (eq_of_mem_boxCube hl)

/-- **The cube carves out the box.** The reindexing from "every literal of the
cube holds" to "every atom's half-space contains `x`" is the content; the geometry
is `Ttc.boxRegion_eq`. -/
theorem region_boxCube (n : ℕ) (c : ℝ) :
    region (fun a => (boxAtoms n c a).halfspace) (boxCube n)
      = {x : Space n | ∀ k, 0 ≤ x k ∧ x k ≤ c} := by
  rw [← boxRegion_eq n c]
  ext x
  simp only [mem_region_iff, Set.mem_iInter]
  constructor
  · intro h j
    exact h ⟨j, true⟩ (mem_boxCube j)
  · intro h l hl
    have hpos : l.pos = true := boxCube_isPositive l hl
    simp only [Lit.holds, hpos, cond_true]
    exact h l.atom

/-- The single-cube DNF whose solution set is the box. -/
def boxDNF (n : ℕ) : DNF (Fin n ⊕ Fin n) := [boxCube n]

/-- **The DNF is positive** — `Ttc.TtcProb.isPositive` verbatim. -/
theorem boxDNF_isPositive : DNF.IsPositive (boxDNF n) := by
  intro c hc
  rw [boxDNF, List.mem_singleton] at hc
  subst hc
  exact boxCube_isPositive

/-- Every coefficient vector of `Ttc.boxAtoms` is a `±1` in one slot and `0`
elsewhere — independently of the side length — so its squared length is `1`. -/
theorem boxAtoms_coeff_sq_sum (c : ℝ) (j : Fin n ⊕ Fin n) :
    ∑ k, (boxAtoms n c j).coeff k ^ 2 = 1 := by
  obtain (k | k) := j <;> simp

/-- **Every facet is a genuine constraint** — `Ttc.TtcProb.normal_ne_zero`
verbatim, for the box's DNF. -/
theorem boxAtoms_normal_ne_zero (n : ℕ) (c : ℝ) :
    ∀ j : FacetIndex (boxDNF n), 0 < ∑ k, (boxAtoms n c j.2.val.atom).coeff k ^ 2 := by
  intro j
  rw [boxAtoms_coeff_sq_sum]
  norm_num

/-! ## The two geometric fields, in the shape `Ttc.TtcProb` wants them -/

/-- **`Ttc.TtcProb.ball_subset` for the box**: the cube's region contains the
`ℓ₂`-ball of radius `c/2` about `Ttc.boxCentre`. -/
theorem ball_subset_region_boxCube (n : ℕ) (c : ℝ) :
    Metric.ball (boxCentre n c) (c / 2)
      ⊆ region (fun a => (boxAtoms n c a).halfspace) (boxCube n) := by
  rw [region_boxCube]
  exact ball_subset_box n c

/-- **`Ttc.TtcProb.volume_ne_top` for the box**: the cube's region has finite
volume. -/
theorem volume_region_boxCube_ne_top (n : ℕ) (c : ℝ) :
    volume (region (fun a => (boxAtoms n c a).halfspace) (boxCube n)) ≠ ⊤ := by
  rw [region_boxCube]
  exact volume_box_ne_top n c

/-! ## The input formula, and `Sol(F)`

`Ttc.TtcProb.isDNF` demands a Boolean formula `φ` of which `boxDNF n` is a DNF
representation; the headline theorem is about `Sol(F) = Ttc.sol M φ`. For the box
that formula is the conjunction of all `2n` atoms.

**`Ttc.BForm` has no `true` constructor**, so a conjunction over an *empty* atom
list has nothing to be seeded with — and indeed `BForm (Fin 0 ⊕ Fin 0)` is
uninhabited, every term of `Ttc.BForm` bottoming out in an `atom`. So
`Ttc.boxForm` takes `1 ≤ n`, and the fold is seeded with the tautology
`a ∨ ¬a` at the atom `Sum.inl 0`. This costs nothing: `Ttc.Params` requires
`1 ≤ n` already (`Ttc.Params.hn`, tied to the ambient dimension by
`Ttc.TtcProb.dim_eq`), so any `Ttc.TtcProb` in dimension `n` already carries it.
-/

/-- Folding `BForm.and` over a list of atoms conjoins them onto the seed. -/
theorem holds_foldr_and {A : Type*} (L : List A) (ψ : BForm A) (v : A → Prop) :
    (L.foldr (fun j φ => BForm.and (.atom j) φ) ψ).holds v
      ↔ (∀ j ∈ L, v j) ∧ ψ.holds v := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.foldr_cons, BForm.holds, ih, List.mem_cons]
      constructor
      · rintro ⟨ha, hL, hψ⟩
        exact ⟨fun j hj => hj.elim (fun h => h ▸ ha) (hL j), hψ⟩
      · rintro ⟨hall, hψ⟩
        exact ⟨hall a (Or.inl rfl), fun j hj => hall j (Or.inr hj), hψ⟩

/-- **The input formula**: the conjunction of all `2n` atoms of `Ttc.boxAtoms`,
`Ttc.conj` over `Ttc.boxAtomList`. It is **negation-free**, which is what
`Ttc.TtcProb.φ_pos` asks of the input and what makes `Ttc.toDNF`'s output
positive. (The `hn` argument is kept so that every name in this section takes the
same arguments; the formula itself does not need it — an earlier version did,
because `Ttc.BForm` had no `tt` and the fold had to be seeded with the tautology
`a ∨ ¬a`, which is exactly the negation that is now gone.) -/
def boxForm (n : ℕ) (_hn : 1 ≤ n) : BForm (Fin n ⊕ Fin n) := conj (boxAtomList n)

/-- **The formula is negation-free** — `Ttc.TtcProb.φ_pos` verbatim. -/
theorem boxForm_isPositive (hn : 1 ≤ n) : (boxForm n hn).IsPositive :=
  isPositive_conj _

/-- **The formula says exactly "every atom holds".** -/
theorem boxForm_holds (hn : 1 ≤ n) (v : (Fin n ⊕ Fin n) → Prop) :
    (boxForm n hn).holds v ↔ ∀ j, v j := by
  rw [boxForm, holds_conj]
  exact ⟨fun h j => h j (mem_boxAtomList j), fun h j _ => h j⟩

/-- **`ToDNF` returns exactly `Ttc.boxDNF`** on the witness formula, so everything
proved about `Ttc.boxDNF` transfers to the DNF the algorithm actually builds. -/
theorem toDNF_boxForm (hn : 1 ≤ n) : toDNF (boxForm n hn) = boxDNF n :=
  toDNF_conj _

/-- **The cube says exactly the same thing.** -/
theorem boxCube_holds (v : (Fin n ⊕ Fin n) → Prop) :
    (boxCube n).holds v ↔ ∀ j, v j := by
  constructor
  · intro h j
    exact h ⟨j, true⟩ (mem_boxCube j)
  · intro h l hl
    have hpos : l.pos = true := boxCube_isPositive l hl
    simp only [Lit.holds, hpos, cond_true]
    exact h l.atom

/-- **`Ttc.TtcProb.isDNF` for the box**: the single-cube DNF really does represent
the formula, on every Boolean assignment. -/
theorem boxDNF_isDNFOf (hn : 1 ≤ n) : IsDNFOf (boxDNF n) (boxForm n hn) := by
  intro v
  rw [boxForm_holds hn v]
  constructor
  · rintro ⟨c, hc, hcv⟩
    rw [boxDNF, List.mem_singleton] at hc
    subst hc
    exact (boxCube_holds v).1 hcv
  · intro h
    exact ⟨boxCube n, by simp [boxDNF], (boxCube_holds v).2 h⟩

/-- **`Sol(F)` is the box.** The reindexing is the same one as
`Ttc.region_boxCube`: `Ttc.sol` evaluates `Ttc.BForm.holds` at the *induced*
valuation `a ↦ x ∈ M a`, so `Ttc.boxForm_holds` turns the formula into "`x` lies
in every atom's half-space", which is `Ttc.boxRegion_eq`. -/
theorem sol_boxForm (n : ℕ) (c : ℝ) (hn : 1 ≤ n) :
    sol (fun a => (boxAtoms n c a).halfspace) (boxForm n hn)
      = {x : Space n | ∀ k, 0 ≤ x k ∧ x k ≤ c} := by
  rw [← boxRegion_eq n c]
  ext x
  simp only [mem_sol_iff, Set.mem_iInter]
  exact boxForm_holds hn _

/-! ## The normalised lattice count of the witness

`Ttc.TtcProb.L` is `Ttc.normalisedCount`, i.e. `|Sol(F) ∩ 𝕃ⁿ| / 10^(ρ·n)` with
`𝕃ⁿ = (10^ρ)⁻¹·ℤⁿ` (`Ttc.fineLattice n (Ttc.latticeScale ρ)`,
`Ttc.latticeScale ρ = 10^ρ`). The normalisation is exactly the lattice spacing, so
the count of the box normalises to *at least its volume* `cⁿ` — at every
precision `ρ`, positive or negative. That is the quantitative statement the
witness needs: `alg:ttc`'s `Thresh` is a fixed number, and `cⁿ ≥ c` (for `n ≥ 1`,
`c ≥ 1`) exceeds it once `c` is chosen large enough.
-/

/-- **The witness's normalised lattice count is at least `cⁿ`**, at every
precision `ρ`. `⌊c·10^ρ⌋ + 1 > c·10^ρ`, so dividing the count by `10^(ρ·n)`
cannot lose the factor `cⁿ`. -/
theorem normalisedCount_box_ge (n : ℕ) {c : ℝ} (hc : 0 < c) (hn : 1 ≤ n) (ρ : ℤ) :
    c ^ n ≤ normalisedCount (fun a => (boxAtoms n c a).halfspace) (boxForm n hn) ρ := by
  have hscale : latticeScale ρ = (10 : ℝ) ^ ρ := rfl
  have hr : 0 < latticeScale ρ := by rw [hscale]; positivity
  have hcount : (⌊c * latticeScale ρ⌋₊ + 1) ^ n
      ≤ latticeCount (fun a => (boxAtoms n c a).halfspace) (boxForm n hn) ρ := by
    rw [latticeCount, sol_boxForm n c hn]
    exact box_lattice_card_ge n hc hr
  have hcountR : ((⌊c * latticeScale ρ⌋₊ : ℝ) + 1) ^ n
      ≤ (latticeCount (fun a => (boxAtoms n c a).halfspace) (boxForm n hn) ρ : ℝ) := by
    exact_mod_cast hcount
  have h0 : (0 : ℝ) ≤ c * latticeScale ρ := (mul_pos hc hr).le
  have hlt : c * latticeScale ρ < (⌊c * latticeScale ρ⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have h1 : (c * latticeScale ρ) ^ n ≤ ((⌊c * latticeScale ρ⌋₊ : ℝ) + 1) ^ n := by
    gcongr
  rw [normalisedCount, le_div_iff₀ (pow_pos hr n)]
  calc c ^ n * latticeScale ρ ^ n = (c * latticeScale ρ) ^ n := (mul_pow _ _ _).symm
    _ ≤ ((⌊c * latticeScale ρ⌋₊ : ℝ) + 1) ^ n := h1
    _ ≤ _ := hcountR

end Ttc
