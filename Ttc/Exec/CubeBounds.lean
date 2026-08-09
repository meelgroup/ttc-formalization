/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.Params
import Ttc.Lattice.Decomposition

/-!
# `1 ≤ m` and `1 ≤ r`, derived rather than assumed

`Ttc.ttcParams` (`Exec/Params.lean`) demands two positivity facts about the
decomposition it reads its parameters off:

* `hm : 1 ≤ Nat.card {c : Cube A // c ∈ D}` — the DNF has at least one cube;
* `hr : 1 ≤ Nat.card (FacetIndex D)` — some cube of it has at least one literal.

`Exec/Params.lean` carries both as hypotheses, noting that neither is derivable
from nothing.  This file discharges both from hypotheses that the top-level
statement `Ttc.ttc_volume_estimate` already has, so that they need not appear as
binders there.

## What each derivation needs, and why

**`hm` needs positivity of the formula.**  `Ttc.BForm` has no `false`
constructor, so a `Ttc.BForm.IsPositive` formula is built from `tt`, `atom`,
`and`, `or` alone, and each of those clauses of `Ttc.dnfAux _ true` produces a
nonempty list from nonempty lists (`Ttc.DNF.cross` of two nonempty DNFs contains
`c ++ d`, and `++` of two lists one of which is nonempty is nonempty).  Hence
`Ttc.toDNF φ ≠ []`.  Positivity is genuinely needed: `dnfAux (.neg .tt) true =
dnfAux .tt false = []`, and indeed `Sol(¬⊤) = ∅` has no cubes.

**`hr` needs boundedness of the solution set.**  It is *false* without it, and
the counterexample is as small as it gets: for `φ = BForm.tt` we have
`toDNF φ = [[]]` — one cube, carrying no literals — so `FacetIndex (toDNF φ)` is
empty and `Nat.card` of it is `0`.  What rules this out is exactly `hbdd`:
a literal-free cube `c = []` has `Cube.holds v c` vacuously true, so
`Ttc.region M c = Set.univ`, and `Ttc.region_subset_sol` then forces
`sol M φ = Set.univ`, which is unbounded because `Ttc.Space n = EuclideanSpace ℝ
(Fin n)` is a nontrivial normed space once `1 ≤ n` (`NormedSpace.unbounded_univ`).
`Sol(tt) = ℝⁿ` is unbounded, so `hbdd` fails for `tt` — as it must.

`Ttc.one_le_card_facets_of_isBounded` is stated for an **arbitrary** `D` with
`IsDNFOf D φ`, not for `toDNF φ`, because the same conclusion is needed for
deduplicated variants of the DNF.
-/

namespace Ttc

open Set

variable {A : Type*}

/-! ## Part 1: a positive formula's DNF is nonempty -/

/-- **A positive formula's positive-polarity DNF has a cube.**  By structural
induction: `BForm` has no `false` constructor, and the `.neg` case is vacuous
because `Ttc.BForm.IsPositive` sends it to `False`. -/
theorem exists_mem_dnfAux_true {φ : BForm A} (h : φ.IsPositive) :
    ∃ c : Cube A, c ∈ dnfAux φ true := by
  induction φ with
  | tt => exact ⟨[], by simp [dnfAux]⟩
  | atom a => exact ⟨[⟨a, true⟩], by simp [dnfAux]⟩
  | neg φ _ => exact h.elim
  | and φ ψ ihφ ihψ =>
      obtain ⟨c, hc⟩ := ihφ h.1
      obtain ⟨d, hd⟩ := ihψ h.2
      refine ⟨c ++ d, ?_⟩
      simp only [dnfAux, DNF.cross, List.mem_flatMap, List.mem_map]
      exact ⟨c, hc, d, hd, rfl⟩
  | or φ ψ ihφ _ =>
      obtain ⟨c, hc⟩ := ihφ h.1
      exact ⟨c, by simpa [dnfAux] using Or.inl hc⟩

/-- **A positive formula's positive-polarity DNF is not the empty disjunction.** -/
theorem dnfAux_true_ne_nil {φ : BForm A} (h : φ.IsPositive) :
    dnfAux φ true ≠ [] := by
  obtain ⟨c, hc⟩ := exists_mem_dnfAux_true h
  exact List.ne_nil_of_mem hc

/-- **`Ttc.toDNF` of a positive formula is not the empty disjunction.**  This is
what discharges `Ttc.ttcParams`' `hm` for the DNF the algorithm actually
computes. -/
theorem toDNF_ne_nil {φ : BForm A} (h : φ.IsPositive) : toDNF φ ≠ [] :=
  dnfAux_true_ne_nil h

/-! ## Part 2: under a bounded solution set every cube carries a literal -/

/-- A cube with no literals denotes all of the ambient space: `Cube.holds` is a
bounded universal quantifier over the cube's literals, hence vacuously true. -/
theorem region_nil {X : Type*} {M : A → Set X} : region M ([] : Cube A) = univ :=
  eq_univ_of_forall fun _ _ h => absurd h (List.not_mem_nil)

/-- `ℝⁿ` is unbounded as soon as `1 ≤ n`.  Used to contradict `hbdd` in
`Ttc.exists_lit_of_isBounded`. -/
theorem not_isBounded_univ_space {n : ℕ} (hn : 1 ≤ n) :
    ¬ Bornology.IsBounded (univ : Set (Space n)) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nontrivial (Space n) := inferInstance
  exact NormedSpace.unbounded_univ ℝ (Space n)

/-- **Every cube of a DNF of a formula with bounded solution set has a literal.**

If some cube `c` were literal-free then `region M c = Set.univ`, and soundness of
the decomposition (`Ttc.region_subset_sol`) would give `Set.univ ⊆ sol M φ`,
making `sol M φ` unbounded — contradicting `hbdd`.  This is what discharges
`Ttc.ttcParams`' `hr` without assuming it. -/
theorem exists_lit_of_isBounded {n : ℕ} (hn : 1 ≤ n)
    {M : A → Set (Space n)} {φ : BForm A} {D : DNF A}
    (hD : IsDNFOf D φ) (hbdd : Bornology.IsBounded (sol M φ))
    {c : Cube A} (hc : c ∈ D) : ∃ l : Lit A, l ∈ c := by
  by_contra hno
  have hcnil : c = [] :=
    List.eq_nil_iff_forall_not_mem.mpr fun l hl => hno ⟨l, hl⟩
  subst hcnil
  have huniv : (univ : Set (Space n)) ⊆ sol M φ := by
    rw [← region_nil (M := M) (A := A)]
    exact region_subset_sol hD hc
  exact not_isBounded_univ_space hn (hbdd.subset huniv)

/-! ## Part 3: the two packaged conclusions -/

/-- **A nonempty DNF has at least one cube**, in the `Nat.card` form
`Ttc.ttcParams` wants for its `hm`. -/
theorem one_le_card_cubes_of_ne_nil {D : DNF A} (hne : D ≠ []) :
    1 ≤ Nat.card {c : Cube A // c ∈ D} := by
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil D hne
  exact one_le_card_cubes hc

/-- **`hm`, from positivity of the input formula.**  Combines
`Ttc.toDNF_ne_nil` with `Ttc.one_le_card_cubes`. -/
theorem one_le_card_cubes_of_isPositive {φ : BForm A} (h : φ.IsPositive) :
    1 ≤ Nat.card {c : Cube A // c ∈ toDNF φ} :=
  one_le_card_cubes_of_ne_nil (toDNF_ne_nil h)

/-- **`hr`, from boundedness of the solution set.**  Combines
`Ttc.exists_lit_of_isBounded` with `Ttc.one_le_card_facets`.  Stated for an
arbitrary DNF `D` of `φ`, so that it applies to deduplicated variants of
`Ttc.toDNF φ` as well. -/
theorem one_le_card_facets_of_isBounded {n : ℕ} (hn : 1 ≤ n)
    {M : A → Set (Space n)} {φ : BForm A} {D : DNF A}
    (hD : IsDNFOf D φ) (hbdd : Bornology.IsBounded (sol M φ)) (hne : D ≠ []) :
    1 ≤ Nat.card (FacetIndex D) := by
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil D hne
  obtain ⟨l, hl⟩ := exists_lit_of_isBounded hn hD hbdd hc
  exact one_le_card_facets hc hl

#print axioms exists_mem_dnfAux_true
#print axioms dnfAux_true_ne_nil
#print axioms toDNF_ne_nil
#print axioms region_nil
#print axioms not_isBounded_univ_space
#print axioms exists_lit_of_isBounded
#print axioms one_le_card_cubes_of_ne_nil
#print axioms one_le_card_cubes_of_isPositive
#print axioms one_le_card_facets_of_isBounded

end Ttc
