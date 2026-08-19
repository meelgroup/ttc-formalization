/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.Params
import Ttc.Lattice.Decomposition

/-!
# `1 ≤ m` and `1 ≤ r`, derived rather than assumed

`Ttc.ttcParams` (`Model/Pseudocode.lean`) demands two positivity facts about the
decomposition it reads its parameters off:

* `hm : 1 ≤ Nat.card {c : Cube A // c ∈ D}` — the DNF has at least one cube;
* `hr : 1 ≤ Nat.card (FacetIndex D)` — some cube of it has at least one literal.

Neither is derivable from nothing.  Both are discharged from hypotheses that the
top-level statement `Ttc.ttc_volume` already has, so that they need not
appear as binders there — `hr` and the two packaged conclusions in
`Model/Pseudocode`, where the parameter block is built, and `hm`'s positivity
route here.

## What each derivation needs, and why

**`hm` needs positivity of the formula.**  `Ttc.BForm` has no `false`
constructor, so a `Ttc.BForm.IsPositive` formula is built from `tt`, `atom`,
`and`, `or` alone, and each of those clauses of `Ttc.dnfAux _ true` produces a
nonempty list from nonempty lists (`Ttc.DNF.cross` of two nonempty DNFs contains
`c ++ d`, and `++` of two lists one of which is nonempty is nonempty).  Hence
`Ttc.toDNF φ ≠ []`.  Positivity is genuinely needed: `dnfAux (.neg .tt) true =
dnfAux .tt false = []`, and indeed `Sol(¬⊤) = ∅` has no cubes.

**`hr` needs boundedness of the solution set**, and that half of the argument now
sits in `Model/Pseudocode` (`Ttc.exists_lit_of_isBounded`), because the parameter
block cannot be constructed without it.  It is *false* without boundedness, and the
counterexample is as small as it gets: for `φ = BForm.tt` we have `toDNF φ = [[]]`
— one cube, carrying no literals — so `FacetIndex (toDNF φ)` is empty and
`Nat.card` of it is `0`.

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

/-! ## Part 2: what moved to `Model/Pseudocode`

The bounded-solution-set half of this file — `Ttc.region_nil`,
`Ttc.not_isBounded_univ_space`, `Ttc.exists_lit_of_isBounded` — together with the
two packaged conclusions `Ttc.one_le_card_cubes_of_ne_nil` and
`Ttc.one_le_card_facets_of_isBounded` now live in `Model/Pseudocode.lean`, next to
`Ttc.ttcParams` and `Ttc.inputParams`: a `Ttc.Params` cannot be *constructed*
without them, so the parameter block could not otherwise be part of the algorithm.
The reasoning is unchanged and is documented there.  What stays here is the
positivity route to a nonempty raw DNF, which the block does not need.
-/

/-! ## Part 3: `hm` from positivity

`Ttc.one_le_card_cubes_of_ne_nil` moved to `Model/Pseudocode`; this specialises it
to the DNF a positive formula produces.
-/

/-- **`hm`, from positivity of the input formula.**  Combines
`Ttc.toDNF_ne_nil` with `Ttc.one_le_card_cubes`. -/
theorem one_le_card_cubes_of_isPositive {φ : BForm A} (h : φ.IsPositive) :
    1 ≤ Nat.card {c : Cube A // c ∈ toDNF φ} :=
  one_le_card_cubes_of_ne_nil (toDNF_ne_nil h)

#print axioms exists_mem_dnfAux_true
#print axioms dnfAux_true_ne_nil
#print axioms toDNF_ne_nil
#print axioms one_le_card_cubes_of_isPositive

end Ttc
