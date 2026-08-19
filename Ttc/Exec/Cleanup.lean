/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.Inputs

/-!
# `Exec/Cleanup`: `hcoeff` discharged by deleting the degenerate literals

The headline used to carry, at the rung of the ladder this file was written for
(superseded 2026-08-19 by `Ttc.ttc_volume`, which has ten binders and none of them this),

```
hcoeff : ∀ j : FacetIndex (toDNFd φ), (atoms j.2.val.atom).coeff ≠ 0
```

— *no facet has a zero normal vector*.  It is needed because the KV97 rounding
argument divides by `‖A_ij‖`, and its tail bound `Pr[A·Y ≥ κ‖A‖]` degenerates to
`Pr[0 ≥ 0] = 1` when the normal is `0`.

## Why a zero normal is not a constraint

Write `M := Ttc.atomSet atoms`, so an atom `a` denotes
`{x | ∑ i, (atoms a).coeff i * x i ≤ (atoms a).bound}`.  If `(atoms a).coeff = 0`
the sum is `0` and the half-space is decided by the sign of the bound:

* `0 ≤ bound` — the half-space is **all of `Space n`**
  (`Ttc.halfspace_eq_univ_of_coeff_zero`).  A *positive* literal on such an atom is
  vacuous and can be deleted from its cube without changing that cube's `region`
  (`Ttc.region_cleanCube`).
* `bound < 0` — the half-space is **empty**
  (`Ttc.halfspace_eq_empty_of_coeff_zero`).  A cube containing a *positive* literal
  on such an atom has `region = ∅` (`Ttc.region_eq_empty_of_voidCube`) and can be
  deleted from the DNF without changing `⋃ᵢ region`.

Those two are exhaustive: `coeff = 0` forces one or the other.  So after the
cleanup **every surviving literal has a nonzero normal**, with no hypothesis at all
(`Ttc.coeff_ne_zero_cleanDNF`).

## Why this is a discharge and not a modelling change

Both rewrites preserve every surviving cube's `region` **exactly, as a set**, and
the deleted cubes have `region = ∅`; hence `⋃ᵢ region` — and therefore `Ttc.sol`,
`Ttc.volSol`, boundedness, the lattice count, everything downstream measures — is
literally the same set (`Ttc.sol_cleanDNF`).  The algorithm is handed a different
list of polytopes describing *the same body*.

Contrast `Exec/Rescaled.lean`, which discharges `hvol` by **dilating the input by
`c = scaleFactor …`**: there `Sol(F)` genuinely changes (to `c · Sol(F)`), the run
is a different run, and the estimate has to be divided by `cⁿ` afterwards to get
back.  Nothing of that kind happens here: no scalar is chosen, no estimate is
post-processed, and `Ttc.volSol (atomSet atoms) φ` is untouched.

## The one thing that is **not** true: `IsDNFOf` is not preserved

`Ttc.IsDNFOf D φ` quantifies over **all** Boolean assignments `v : A → Prop`, not
only over the ones induced by a point.  Deleting a vacuous literal is justified by
`M a = Set.univ`, i.e. by `induced M x a` being *true at every point* — which says
nothing about an arbitrary `v`.  And indeed the naive statement is **false**:
`Ttc.not_isDNFOf_cleanDNF` exhibits `atoms ≡ ⟨0, 1⟩` over `A = Unit`, `φ = atom ()`
and `D = [[⟨(), true⟩]]`, for which `IsDNFOf D φ` holds, `cleanDNF atoms D` contains
the empty cube, and `IsDNFOf (cleanDNF atoms D) φ` fails at `v = fun _ => False`.

The repair is to move the formula too.  A positive DNF is the DNF of its own
disjunction-of-conjunctions (`Ttc.toDNF_dnfForm`: `toDNF (dnfForm D) = D` for
nonempty positive `D`), so

```
cleanForm atoms φ := dnfForm (cleanDNF atoms (toDNFd φ))
```

is a **positive formula with the same solution set** (`Ttc.sol_cleanForm`) whose
own deduplicated DNF consists exactly of the cleaned cubes
(`Ttc.mem_toDNFd_cleanForm`) — so `hcoeff` holds for it outright
(`Ttc.coeff_ne_zero_toDNFd_cleanForm`).  Running `TTC` on `cleanForm atoms φ`
instead of `φ` is a preprocessing pass on the *formula* that preserves `Sol(F)` on
the nose; it is not a change to the body being measured.

## Hypotheses that had to be added

Everything about regions needs **positivity** (`Ttc.DNF.IsPositive D`, available in
the headline as `hφ`): a *negated* literal on a vacuous atom denotes `Set.univᶜ = ∅`
and deleting it would change the region, and a negated literal on a void atom
denotes `∅ᶜ = Set.univ` so its cube must *not* be dropped.  The formula-level
results additionally need `cleanDNF atoms (toDNFd φ) ≠ []`, which by
`Ttc.cleanDNF_ne_nil_iff` says some cube of `toDNFd φ` is not void, and which is
implied by `(sol (atomSet atoms) φ).Nonempty`
(`Ttc.cleanDNF_ne_nil_of_sol_nonempty`).  When it fails, every cube is void, `sol`
is empty, and `Ttc.dnfForm []` is the junk value `BForm.tt`.
-/

namespace Ttc

open Set

variable {A X : Type*} {n : ℕ}

/-! ## Degenerate half-spaces

The two half-space computations are **already in the development**, on a bare
`a : LinAtom n`: `Ttc.halfspace_eq_univ_of_coeff_zero` and
`Ttc.halfspace_eq_empty_of_coeff_zero` (`Exec/Geometry.lean`, where they are cited
as the meaning of the `normal_ne_zero` binder but not acted on).  All this file
adds is the atom-indexed phrasing, in terms of `Ttc.atomSet`, which is the shape
the region arguments below consume.
-/

/-- **A zero normal with a nonnegative bound denotes the whole space** — the
`Ttc.atomSet` phrasing of `Ttc.halfspace_eq_univ_of_coeff_zero`.  The constraint
reads `0 ≤ b`, which is true everywhere. -/
theorem atomSet_eq_univ_of_coeff_zero {atoms : A → LinAtom n} {a : A}
    (h0 : (atoms a).coeff = 0) (hb : 0 ≤ (atoms a).bound) :
    atomSet atoms a = Set.univ :=
  halfspace_eq_univ_of_coeff_zero h0 hb

/-- **A zero normal with a negative bound denotes the empty set** — the
`Ttc.atomSet` phrasing of `Ttc.halfspace_eq_empty_of_coeff_zero`.  The constraint
reads `0 ≤ b < 0`, which is false everywhere. -/
theorem atomSet_eq_empty_of_coeff_zero {atoms : A → LinAtom n} {a : A}
    (h0 : (atoms a).coeff = 0) (hb : (atoms a).bound < 0) :
    atomSet atoms a = ∅ :=
  halfspace_eq_empty_of_coeff_zero h0 hb

/-- Satisfaction of a **positive** literal at a point is membership in its atom's
set.  This is where positivity is used throughout the file: at `pos = false` the
literal denotes the *complement*, and the two rewrites below would go the wrong
way. -/
theorem lit_holds_pos {M : A → Set X} {l : Lit A} (hl : l.pos = true) {x : X} :
    l.holds (induced M x) ↔ x ∈ M l.atom := by
  unfold Lit.holds
  rw [hl]
  exact Iff.rfl

/-! ## The two degeneracies, named

`Ttc.VacuousLit` and `Ttc.VoidCube` — the `Vacuous` and `Void` predicates of lines
A5 and A4 of the preprocessing — are **defined in `Model/Pseudocode`**, with the
rest of the amended algorithm's vocabulary; only their theory is here. -/

/-- **The exhaustiveness fact.**  A literal with a zero normal is either vacuous or
lies in a void cube — there is no third case, because `0 ≤ b` and `b < 0` are
exhaustive. -/
theorem vacuous_or_void {atoms : A → LinAtom n} {c : Cube A} {l : Lit A} (hl : l ∈ c)
    (h0 : (atoms l.atom).coeff = 0) :
    VacuousLit atoms l ∨ VoidCube atoms c := by
  by_cases hb : 0 ≤ (atoms l.atom).bound
  · exact Or.inl ⟨h0, hb⟩
  · exact Or.inr ⟨l, hl, h0, not_le.1 hb⟩

/-! ## Cleaning one cube

`Ttc.cleanCube` — line A5 — is **defined in `Model/Pseudocode`**; only its theory is
here.  `Ttc.Cube A` is a `List`, and `A` carries no `DecidableEq`, so the filter's
predicate is decided classically — the idiom of `Ttc.toDNFd` (`Exec/Dedup`).
-/

@[simp] theorem mem_cleanCube {atoms : A → LinAtom n} {c : Cube A} {l : Lit A} :
    l ∈ cleanCube atoms c ↔ l ∈ c ∧ ¬ VacuousLit atoms l := by
  rw [cleanCube, List.mem_filter]
  exact and_congr_right fun _ => by simp

theorem cleanCube_subset {atoms : A → LinAtom n} {c : Cube A} {l : Lit A}
    (hl : l ∈ cleanCube atoms c) : l ∈ c := (mem_cleanCube.1 hl).1

/-- Cleaning a cube keeps it positive: it only removes literals. -/
theorem isPositive_cleanCube {atoms : A → LinAtom n} {c : Cube A} (hc : Cube.IsPositive c) :
    Cube.IsPositive (cleanCube atoms c) := fun _ hl => hc _ (cleanCube_subset hl)

/-- **Deleting the vacuous literals does not move the cube's region.**  Each of them
denotes `Set.univ` (`Ttc.halfspace_eq_univ_of_coeff_zero`), so the remaining
intersection is the same set — an equality of sets, not of measures. -/
theorem region_cleanCube (atoms : A → LinAtom n) {c : Cube A} (hc : Cube.IsPositive c) :
    region (atomSet atoms) (cleanCube atoms c) = region (atomSet atoms) c := by
  ext x
  simp only [mem_region_iff]
  constructor
  · intro h l hl
    by_cases hv : VacuousLit atoms l
    · rw [lit_holds_pos (hc l hl), atomSet_eq_univ_of_coeff_zero hv.1 hv.2]
      exact Set.mem_univ x
    · exact h l (mem_cleanCube.2 ⟨hl, hv⟩)
  · intro h l hl
    exact h l (cleanCube_subset hl)

/-- **A void cube carves out nothing.**  One of its literals denotes `∅`
(`Ttc.halfspace_eq_empty_of_coeff_zero`), so the intersection is empty. -/
theorem region_eq_empty_of_voidCube (atoms : A → LinAtom n) {c : Cube A}
    (hc : Cube.IsPositive c) (hv : VoidCube atoms c) :
    region (atomSet atoms) c = ∅ := by
  obtain ⟨l, hl, h0, hb⟩ := hv
  ext x
  constructor
  · intro hx
    have h1 := (mem_region_iff.1 hx) l hl
    rw [lit_holds_pos (hc l hl), atomSet_eq_empty_of_coeff_zero h0 hb] at h1
    exact h1
  · intro hx
    exact hx.elim

/-! ## Cleaning the DNF

`Ttc.cleanDNF` — lines A4–A5 — is **defined in `Model/Pseudocode`**; only its theory
is here. -/

theorem mem_cleanDNF {atoms : A → LinAtom n} {D : DNF A} {c : Cube A} :
    c ∈ cleanDNF atoms D ↔ ∃ c₀ ∈ D, ¬ VoidCube atoms c₀ ∧ c = cleanCube atoms c₀ := by
  rw [cleanDNF, List.mem_map]
  constructor
  · rintro ⟨c₀, hc₀, rfl⟩
    rw [List.mem_filter] at hc₀
    exact ⟨c₀, hc₀.1, by simpa using hc₀.2, rfl⟩
  · rintro ⟨c₀, hc₀, hv, rfl⟩
    exact ⟨c₀, by rw [List.mem_filter]; exact ⟨hc₀, by simpa using hv⟩, rfl⟩

/-- **Every cube of the cleaned DNF has the region of a cube of the original.**

Needs `Ttc.DNF.IsPositive D` — see the module docstring. -/
theorem region_cleanDNF_eq (atoms : A → LinAtom n) {D : DNF A} (hpos : DNF.IsPositive D)
    {c : Cube A} (hc : c ∈ cleanDNF atoms D) :
    ∃ c₀ ∈ D, region (atomSet atoms) c = region (atomSet atoms) c₀ := by
  obtain ⟨c₀, hc₀, _, rfl⟩ := mem_cleanDNF.1 hc
  exact ⟨c₀, hc₀, region_cleanCube atoms (hpos c₀ hc₀)⟩

/-- Cleaning keeps the DNF positive. -/
theorem isPositive_cleanDNF (atoms : A → LinAtom n) {D : DNF A} (h : DNF.IsPositive D) :
    DNF.IsPositive (cleanDNF atoms D) := by
  intro c hc
  obtain ⟨c₀, hc₀, _, rfl⟩ := mem_cleanDNF.1 hc
  exact isPositive_cleanCube (h c₀ hc₀)

/-- **The payoff at the level of sets**: the cleaned DNF covers exactly `Sol(F)`.

Needs `Ttc.DNF.IsPositive D` — see the module docstring. -/
theorem sol_cleanDNF (atoms : A → LinAtom n) {D : DNF A} {φ : BForm A}
    (hD : IsDNFOf D φ) (hpos : DNF.IsPositive D) :
    (⋃ c ∈ cleanDNF atoms D, region (atomSet atoms) c) = sol (atomSet atoms) φ := by
  ext x
  constructor
  · intro hx
    obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.1 hx
    obtain ⟨c₀, hc₀, heq⟩ := region_cleanDNF_eq atoms hpos hc
    rw [heq] at hxc
    exact region_subset_sol hD hc₀ hxc
  · intro hx
    obtain ⟨c₀, hc₀, hxc₀⟩ := Set.mem_iUnion₂.1 (sol_subset_iUnion_region hD hx)
    by_cases hv : VoidCube atoms c₀
    · rw [region_eq_empty_of_voidCube atoms (hpos c₀ hc₀) hv] at hxc₀
      exact hxc₀.elim
    · refine Set.mem_iUnion₂.2 ⟨cleanCube atoms c₀, mem_cleanDNF.2 ⟨c₀, hc₀, hv, rfl⟩, ?_⟩
      rw [region_cleanCube atoms (hpos c₀ hc₀)]
      exact hxc₀

/-- **`hcoeff`, for the cleaned DNF, with no hypothesis whatsoever.**  A surviving
literal is not vacuous and its cube is not void, and by `Ttc.vacuous_or_void` those
are the only two ways a zero normal can occur. -/
theorem coeff_ne_zero_cleanDNF (atoms : A → LinAtom n) (D : DNF A) :
    ∀ j : FacetIndex (cleanDNF atoms D), (atoms j.2.val.atom).coeff ≠ 0 := by
  rintro ⟨⟨c, hc⟩, ⟨l, hl⟩⟩ h0
  obtain ⟨c₀, hc₀, hv, rfl⟩ := mem_cleanDNF.1 hc
  obtain ⟨hlc, hlv⟩ := mem_cleanCube.1 hl
  rcases vacuous_or_void hlc h0 with h | h
  · exact hlv h
  · exact hv h

/-! ## When the cleaned DNF is empty

`Ttc.cleanDNF` can be `[]` while `D` is not: that is exactly the case where every
cube is void, i.e. where `Sol(F) = ∅`.
-/

/-- **`cleanDNF` is nonempty exactly when some cube is not void.** -/
theorem cleanDNF_ne_nil_iff (atoms : A → LinAtom n) (D : DNF A) :
    cleanDNF atoms D ≠ [] ↔ ∃ c ∈ D, ¬ VoidCube atoms c := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ h
    obtain ⟨c₀, hc₀, hv, _⟩ := mem_cleanDNF.1 hc
    exact ⟨c₀, hc₀, hv⟩
  · rintro ⟨c₀, hc₀, hv⟩
    exact List.ne_nil_of_mem (mem_cleanDNF.2 ⟨c₀, hc₀, hv, rfl⟩)

/-- **A nonempty solution set leaves at least one cube standing.**  The checkable
form of the side condition the formula-level results below need. -/
theorem cleanDNF_ne_nil_of_sol_nonempty (atoms : A → LinAtom n) {D : DNF A} {φ : BForm A}
    (hD : IsDNFOf D φ) (hpos : DNF.IsPositive D) (hne : (sol (atomSet atoms) φ).Nonempty) :
    cleanDNF atoms D ≠ [] := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨c₀, hc₀, hxc₀⟩ := Set.mem_iUnion₂.1 (sol_subset_iUnion_region hD hx)
  refine (cleanDNF_ne_nil_iff atoms D).2 ⟨c₀, hc₀, fun hv => ?_⟩
  rw [region_eq_empty_of_voidCube atoms (hpos c₀ hc₀) hv] at hxc₀
  exact hxc₀.elim

/-- **The empty case is the empty body.**  If every cube is void the cleaned DNF is
`[]` and `Sol(F) = ∅` — so nothing is lost, but there is also no formula left to
run the algorithm on, which is why `Ttc.sol_cleanForm` below takes
`cleanDNF … ≠ []`. -/
theorem sol_eq_empty_of_cleanDNF_eq_nil (atoms : A → LinAtom n) {D : DNF A} {φ : BForm A}
    (hD : IsDNFOf D φ) (hpos : DNF.IsPositive D) (h : cleanDNF atoms D = []) :
    sol (atomSet atoms) φ = ∅ := by
  by_contra hne
  exact (cleanDNF_ne_nil_of_sol_nonempty atoms hD hpos (Set.nonempty_iff_ne_empty.2 hne)) h

/-! ## `IsDNFOf` is **not** preserved

`Ttc.IsDNFOf` is a statement about *all* Boolean assignments, and the cleanup is
justified only at the assignments a point induces.  Here is the counterexample, in
full: one atom `0 · x ≤ 1`, whose literal is vacuous, so the single cube cleans to
the *empty* cube, which holds under every assignment while `φ` does not.
-/

/-- The counterexample's atom system: the single atom `0 · x ≤ 1`. -/
noncomputable def degenVacAtoms : Unit → LinAtom 1 := fun _ => ⟨0, 1⟩

/-- The counterexample's DNF: the one cube asserting the one atom. -/
def degenVacDNF : DNF Unit := [[⟨(), true⟩]]

theorem degenVacDNF_isDNFOf : IsDNFOf degenVacDNF (BForm.atom ()) := by
  intro v
  constructor
  · rintro ⟨c, hc, hcv⟩
    simp only [degenVacDNF, List.mem_singleton] at hc
    subst hc
    exact hcv _ (List.mem_singleton_self _)
  · intro h
    refine ⟨[⟨(), true⟩], List.mem_singleton_self _, ?_⟩
    intro l hl
    rw [List.mem_singleton] at hl
    subst hl
    exact h

theorem degenVacDNF_isPositive : DNF.IsPositive degenVacDNF := by
  intro c hc
  simp only [degenVacDNF, List.mem_singleton] at hc
  subst hc
  intro l hl
  rw [List.mem_singleton] at hl
  subst hl
  rfl

/-- The cleaned cube of the counterexample is empty: its only literal is vacuous. -/
theorem cleanCube_degenVac : cleanCube degenVacAtoms [⟨(), true⟩] = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro l hl
  obtain ⟨_, hv⟩ := mem_cleanCube.1 hl
  exact hv ⟨rfl, by norm_num [degenVacAtoms]⟩

/-- **`IsDNFOf` genuinely fails for the cleaned DNF.**  `cleanDNF` contains the
empty cube, which holds under `v = fun _ => False`, whereas `φ = atom ()` does
not. -/
theorem not_isDNFOf_cleanDNF :
    ¬ IsDNFOf (cleanDNF degenVacAtoms degenVacDNF) (BForm.atom ()) := by
  intro h
  have hmem : [] ∈ cleanDNF degenVacAtoms degenVacDNF := by
    refine mem_cleanDNF.2 ⟨[⟨(), true⟩], List.mem_singleton_self _, ?_, cleanCube_degenVac.symm⟩
    rintro ⟨l, _, _, hb⟩
    exact absurd hb (by norm_num [degenVacAtoms])
  have : (BForm.atom ()).holds (fun _ => False) :=
    (h (fun _ => False)).1 ⟨[], hmem, by intro l hl; exact absurd hl List.not_mem_nil⟩
  exact this

/-! ## Moving the formula with the DNF

The repair: a positive DNF is the `Ttc.toDNF` of its own disjunction of
conjunctions, so the cleaned cube list *is* a genuine DNF — of a new formula with
the same solution set.

`Ttc.cubeForm` and `Ttc.dnfForm` — lines A3 and A6, which both rewriting passes
use — are **defined in `Model/Pseudocode`**; only their theory is here.
-/

/-- Re-tagging a positive cube's literals with `pos = true` is the identity. -/
theorem map_mk_atom_true : ∀ {c : Cube A}, Cube.IsPositive c →
    (c.map fun l => (⟨l.atom, true⟩ : Lit A)) = c := by
  intro c
  induction c with
  | nil => intro _; rfl
  | cons l c ih =>
      intro hc
      have hl : l.pos = true := hc l List.mem_cons_self
      rw [List.map_cons, ih fun m hm => hc m (List.mem_cons_of_mem _ hm)]
      obtain ⟨a, p⟩ := l
      cases p
      · simp at hl
      · rfl

/-- **`toDNF` of a positive cube's formula is that cube.** -/
theorem toDNF_cubeForm {c : Cube A} (hc : Cube.IsPositive c) : toDNF (cubeForm c) = [c] := by
  rw [cubeForm, toDNF_conj, List.map_map]
  exact congrArg (fun l => [l]) (map_mk_atom_true hc)

theorem isPositive_cubeForm (c : Cube A) : (cubeForm c).IsPositive := isPositive_conj _

@[simp] theorem dnfForm_singleton (c : Cube A) : dnfForm [c] = cubeForm c := rfl

@[simp] theorem dnfForm_cons_cons (c c' : Cube A) (D : DNF A) :
    dnfForm (c :: c' :: D) = .or (cubeForm c) (dnfForm (c' :: D)) := rfl

/-- `Ttc.dnfForm` is always positive: it is built from `.or`, `.and`, `.atom` and
`.tt` only. -/
theorem isPositive_dnfForm : ∀ D : DNF A, (dnfForm D).IsPositive := by
  intro D
  induction D with
  | nil => exact trivial
  | cons c D ih =>
      cases D with
      | nil => exact isPositive_cubeForm c
      | cons c' D' => exact ⟨isPositive_cubeForm c, ih⟩

/-- **A nonempty positive DNF is the `ToDNF` of its own formula.**  This is what
makes the cleaned cube list a *bona fide* DNF rather than an ad-hoc list. -/
theorem toDNF_dnfForm : ∀ {D : DNF A}, D ≠ [] → DNF.IsPositive D → toDNF (dnfForm D) = D := by
  intro D
  induction D with
  | nil => intro h; exact absurd rfl h
  | cons c D ih =>
      intro _ hp
      cases D with
      | nil => exact toDNF_cubeForm (hp c List.mem_cons_self)
      | cons c' D' =>
          rw [dnfForm_cons_cons]
          show toDNF (cubeForm c) ++ toDNF (dnfForm (c' :: D')) = _
          rw [toDNF_cubeForm (hp c List.mem_cons_self),
            ih (List.cons_ne_nil _ _) fun d hd => hp d (List.mem_cons_of_mem _ hd)]
          rfl

/-- **A nonempty positive DNF represents its own formula**, on every Boolean
assignment — the genuine `Ttc.IsDNFOf`, not a semantic weakening. -/
theorem isDNFOf_dnfForm {D : DNF A} (hD : D ≠ []) (hp : DNF.IsPositive D) :
    IsDNFOf D (dnfForm D) := by
  have h := toDNF_dnfForm hD hp
  intro v
  conv_lhs => rw [← h]
  exact toDNF_isDNFOf (dnfForm D) v

/-! ## The cleaned formula, and `hcoeff` for it

`Ttc.cleanForm` — lines A4–A6 as one step — is **defined in `Model/Pseudocode`**;
only its theory is here. -/

/-- The cleaned formula is positive, so `hφ` survives it. -/
theorem isPositive_cleanForm (atoms : A → LinAtom n) (φ : BForm A) :
    (cleanForm atoms φ).IsPositive := isPositive_dnfForm _

/-- **The cleaned formula's DNF is exactly the cleaned cube list.** -/
theorem toDNF_cleanForm (atoms : A → LinAtom n) {φ : BForm A} (hφ : φ.IsPositive)
    (hne : cleanDNF atoms (toDNFd φ) ≠ []) :
    toDNF (cleanForm atoms φ) = cleanDNF atoms (toDNFd φ) :=
  toDNF_dnfForm hne (isPositive_cleanDNF atoms (toDNFd_isPositive hφ))

/-- …and so does its deduplicated DNF, up to membership — which is all that
`Ttc.FacetIndex` sees. -/
theorem mem_toDNFd_cleanForm (atoms : A → LinAtom n) {φ : BForm A} (hφ : φ.IsPositive)
    (hne : cleanDNF atoms (toDNFd φ) ≠ []) {c : Cube A} :
    c ∈ toDNFd (cleanForm atoms φ) ↔ c ∈ cleanDNF atoms (toDNFd φ) := by
  rw [mem_toDNFd, toDNF_cleanForm atoms hφ hne]

/-- **The solution set is untouched.**  This is the whole point: `cleanForm atoms φ`
denotes literally the same subset of `Space n` as `φ` does, so `Ttc.volSol`,
boundedness, the lattice count and every downstream measurement agree. -/
theorem sol_cleanForm (atoms : A → LinAtom n) {φ : BForm A} (hφ : φ.IsPositive)
    (hne : cleanDNF atoms (toDNFd φ) ≠ []) :
    sol (atomSet atoms) (cleanForm atoms φ) = sol (atomSet atoms) φ := by
  rw [cleanForm, ← sol_eq_iUnion_region
    (isDNFOf_dnfForm hne (isPositive_cleanDNF atoms (toDNFd_isPositive hφ)))]
  exact sol_cleanDNF atoms (toDNFd_isDNFOf φ) (toDNFd_isPositive hφ)

/-- **`hcoeff` in the shape the headline then asked for it**, for the cleaned
formula, with no degeneracy hypothesis: only `hφ` (already a binder of the headline)
and non-voidness of the DNF (`Ttc.cleanDNF_ne_nil_of_sol_nonempty`, i.e. `Sol(F) ≠
∅`). -/
theorem coeff_ne_zero_toDNFd_cleanForm (atoms : A → LinAtom n) {φ : BForm A}
    (hφ : φ.IsPositive) (hne : cleanDNF atoms (toDNFd φ) ≠ []) :
    ∀ j : FacetIndex (toDNFd (cleanForm atoms φ)), (atoms j.2.val.atom).coeff ≠ 0 := by
  rintro ⟨⟨c, hc⟩, ⟨l, hl⟩⟩
  exact coeff_ne_zero_cleanDNF atoms (toDNFd φ)
    ⟨⟨c, (mem_toDNFd_cleanForm atoms hφ hne).1 hc⟩, ⟨l, hl⟩⟩

/-- **The package, as one statement.**  For a positive `φ` with a nonempty solution
set there is a positive formula with *the same* solution set whose DNF has no
degenerate facet — `hcoeff` discharged, `Sol(F)` unchanged. -/
theorem exists_cleanForm (atoms : A → LinAtom n) {φ : BForm A} (hφ : φ.IsPositive)
    (hs : (sol (atomSet atoms) φ).Nonempty) :
    ∃ ψ : BForm A, ψ.IsPositive ∧ sol (atomSet atoms) ψ = sol (atomSet atoms) φ ∧
      ∀ j : FacetIndex (toDNFd ψ), (atoms j.2.val.atom).coeff ≠ 0 := by
  have hne : cleanDNF atoms (toDNFd φ) ≠ [] :=
    cleanDNF_ne_nil_of_sol_nonempty atoms (toDNFd_isDNFOf φ) (toDNFd_isPositive hφ) hs
  exact ⟨cleanForm atoms φ, isPositive_cleanForm atoms φ, sol_cleanForm atoms hφ hne,
    coeff_ne_zero_toDNFd_cleanForm atoms hφ hne⟩

end Ttc

/-! ## Axiom audit -/

#print axioms Ttc.atomSet_eq_univ_of_coeff_zero
#print axioms Ttc.atomSet_eq_empty_of_coeff_zero
#print axioms Ttc.lit_holds_pos
#print axioms Ttc.vacuous_or_void
#print axioms Ttc.mem_cleanCube
#print axioms Ttc.isPositive_cleanCube
#print axioms Ttc.region_cleanCube
#print axioms Ttc.region_eq_empty_of_voidCube
#print axioms Ttc.mem_cleanDNF
#print axioms Ttc.region_cleanDNF_eq
#print axioms Ttc.isPositive_cleanDNF
#print axioms Ttc.sol_cleanDNF
#print axioms Ttc.coeff_ne_zero_cleanDNF
#print axioms Ttc.cleanDNF_ne_nil_iff
#print axioms Ttc.cleanDNF_ne_nil_of_sol_nonempty
#print axioms Ttc.sol_eq_empty_of_cleanDNF_eq_nil
#print axioms Ttc.not_isDNFOf_cleanDNF
#print axioms Ttc.toDNF_cubeForm
#print axioms Ttc.isPositive_dnfForm
#print axioms Ttc.toDNF_dnfForm
#print axioms Ttc.isDNFOf_dnfForm
#print axioms Ttc.isPositive_cleanForm
#print axioms Ttc.toDNF_cleanForm
#print axioms Ttc.mem_toDNFd_cleanForm
#print axioms Ttc.sol_cleanForm
#print axioms Ttc.coeff_ne_zero_toDNFd_cleanForm
#print axioms Ttc.exists_cleanForm
