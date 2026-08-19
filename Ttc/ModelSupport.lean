/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Model.ProblemSetting
import Ttc.Geometry.CanonPolytope

/-!
# `ModelSupport`: the derived facts `Model/Pseudocode` uses but should not prove

`Model/Pseudocode` is not proof-free — `Ttc.Oracles` has two *proof* fields and two
of the file's definitions are a `Classical.choose` — so some proofs have to be in
scope where the algorithm is written down.  Not all of them have to be *stated*
there.  This file holds the ones that are not about the model at all: four facts of
`Multiset` and `Set` bookkeeping, generic in the carrier type, with nothing of
`alg:ttc` in their statements.  `Model/Pseudocode` imports it, and so does
`Probability/Trajectory`, which holds the trajectory read-offs and the two oracle
contracts proved from the dictionary below.

## What is here, and what it replaced

* `Ttc.count_toMultiset`, `Ttc.count_toMultiset_of_notMem`,
  `Ttc.toMultiset_le_of_count_le` — the count-vector dictionary.  They used to be
  stated in `Model/Pseudocode` at `Ttc.toMultiset`; they are stated here at the sum
  `Ttc.toMultiset pt k = ∑ s, Multiset.replicate (k s) (pt s)` **is**, generic in the
  carrier type.  Every *term-mode* use therefore still elaborates unchanged, by
  unfolding a definition; the one `rw` that matched `Ttc.toMultiset` syntactically
  (`Ttc.count_of_coupledAt`, `Coupling/Run`) became an `exact`.  They are what
  `Ttc.trajThin_le` (`Probability/Trajectory`) — `Ttc.Oracles.thin_le` for the run's
  own bundle — is proved from, which is why `Probability/Trajectory` imports this
  file.
* `Ttc.exists_finEnum_of_finite` — a finite set is listed bijectively by `Fin` of
  its `Set.ncard`.  It used to be `Ttc.hasLatticeEnum_of_finite`, stated at
  `Ttc.HasLatticeEnum`; `Ttc.exists_latticeEnum` (still in `Model/Pseudocode`,
  because `Ttc.latticeEnum` is `Classical.choose`n from it and is therefore in the
  audited closure) now gets its `Set.Infinite` step from this instead.

## The cost, stated rather than glossed

**`Model/Pseudocode` now imports a file that is not under `Model/`.**  Before this
file it imported exactly one thing of ours, `Model/ProblemSetting`; a reader who
opens the `Model/` files now finds an import pointing outside them.  That is a real
change and it should not be waved away.

Two things bound how large a change it is, and both are checkable rather than
rhetorical.  Read the `import` lines rather than this paragraph — they move.

*It is not the only such import, and it is the smallest of them.*  `Model/` is not a
closed system and `Ttc.lean` says so.  `Model/Theorem` imports `Monadic/MeasurePr`
and `Monadic/Program`, hence transitively most of the development, for the notation
it is stated in.  `Model/Pseudocode` itself imports `Ttc/Probability/` — the ambient
randomness the algorithm's law is built from — which is a whole directory and is part
of the audited surface in its own right (see `Ttc/Audit/ClosureCheck.lean`'s
`Ttc.Audit.auditSurface`).  Against those, `Model/Pseudocode → ModelSupport →
Model/ProblemSetting` — and `Probability/Trajectory → ModelSupport`, the same edge
one directory over — adds one module holding four theorems and no definitions.

*The machine check does not move.*  `Ttc/Audit/ClosureCheck.lean`'s `#modelClosure`
walks the definitional closure of `Ttc.ttcAlgOutput` — the specification, the one thing
still checked since the headline moved to the constructed oracles on 2026-08-19 — and
demands every `Ttc` constant in it be defined inside `Ttc.Audit.auditSurface`.  **Nothing in
this file is in that closure**, so this file neither joins the surface nor needs to: a
theorem is entered only through its type (`ConstantInfo.value? = none` for theorems in this
Lean version), and the oracle bundle's two proof fields are lifted into anonymous
`_proof_1/_2`, which are themselves theorems.  The count and its "0 outside the surface"
verdict are exactly what they were before the move — re-measure with `#closureReport` rather
than trusting this sentence.

The honest summary: *what the headline means* is checked to be defined inside a named
surface, and the build fails the moment that stops being true; *what the files in
that surface need in order to elaborate* is a strictly larger set, and this file is
now one more member of it.

## Why only four theorems came, and not the ten

The reason the rest of `Model/Pseudocode`'s theorems stayed is **not** the audit
check — `#modelClosure` cannot see a theorem unless a `def`'s body names it, and only
`Ttc.exists_latticeEnum` is named that way (`Ttc.latticeEnum` is `Classical.choose` of
it, so it must stay inside the audit surface).  The reason is their **statements**.
`Ttc.trajThin_le`, `Ttc.card_trajGen`, `Ttc.latticeEnum_injective` and
`Ttc.cubeOf_spec` each mention a definition that is itself in the measured closure
(`Ttc.trajThin`, `Ttc.trajGen`, `Ttc.latticeEnum`, `Ttc.cubeOf`), so each is pinned
to wherever that definition is filed — upstream of nothing and downstream of nothing.
For the first two that turned out to be a *filing* answer rather than a fixed one:
the read-offs moved to `Probability/Trajectory`, which is in the audit surface too,
and the two contracts went with them, so `Model/Pseudocode` is down to four theorems.
The four facts here are the ones whose statements survive having that vocabulary
taken away altogether: three become facts about `∑ Multiset.replicate`, one about
`Set.ncard`.
-/

namespace Ttc

/-! ## Count vectors as multisets

`Ttc.toMultiset pt k` (`Probability/Trajectory`) is `∑ s, Multiset.replicate (k s) (pt s)`:
the multiset holding `k s` copies of `pt s`.  These are the three facts that make it
a dictionary between count vectors and multisets, stated at the sum itself so that
they say nothing about `alg:ttc`.  Each applies to `Ttc.toMultiset` by unfolding a
definition. -/

section CountVectors

variable {α : Type*} [DecidableEq α] {L : ℕ}

/-- **The multiplicities are the ones prescribed** — the point of the dictionary.
Needs `pt` injective, so that distinct indices contribute to distinct points.
Applies to `Ttc.toMultiset pt k` (`Probability/Trajectory`) by unfolding it. -/
theorem count_toMultiset {pt : Fin L → α} (hpt : Function.Injective pt)
    (k : Fin L → ℕ) (s : Fin L) :
    Multiset.count (pt s) (∑ t, Multiset.replicate (k t) (pt t)) = k s := by
  rw [Multiset.count_sum']
  rw [Finset.sum_eq_single s]
  · rw [Multiset.count_replicate_self]
  · intro t _ hts
    rw [Multiset.count_replicate, if_neg (fun h => hts (hpt h))]
  · intro h
    exact absurd (Finset.mem_univ s) h

/-- Points outside the enumeration do not occur. -/
theorem count_toMultiset_of_notMem (pt : Fin L → α) (k : Fin L → ℕ)
    {x : α} (hx : ∀ s, pt s ≠ x) :
    Multiset.count x (∑ t, Multiset.replicate (k t) (pt t)) = 0 := by
  rw [Multiset.count_sum']
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [Multiset.count_replicate, if_neg (hx t)]

/-- **A count-bounded multiset is a sub-multiset** — the form `Ttc.Oracles.thin_le`
needs, where the ambient multiset is arbitrary rather than another `Ttc.toMultiset`.
This is what `Ttc.trajThin_le` (`Probability/Trajectory`) is proved from. -/
theorem toMultiset_le_of_count_le {pt : Fin L → α}
    (hpt : Function.Injective pt) {k : Fin L → ℕ} {X : Multiset α}
    (h : ∀ s, k s ≤ Multiset.count (pt s) X) :
    (∑ t, Multiset.replicate (k t) (pt t)) ≤ X := by
  rw [Multiset.le_iff_count]
  intro x
  by_cases hx : ∃ s, pt s = x
  · obtain ⟨s, rfl⟩ := hx
    rw [count_toMultiset hpt]
    exact h s
  · simp only [not_exists] at hx
    rw [count_toMultiset_of_notMem pt k hx]
    exact Nat.zero_le _

end CountVectors

/-! ## Listing a finite set by `Fin` of its `Set.ncard`

`Ttc.HasLatticeEnum M φ ρ` (`Model/Pseudocode`) asks for a bijective listing of
`Sol(F) ∩ 𝕃ⁿ` by `Fin (Ttc.latticeCount M φ ρ)`, and `Ttc.latticeCount` is that
set's `Set.ncard`.  So the only content of "finiteness is enough" is the `Nat.card`
bookkeeping below, which mentions neither.  The *geometric* fact that boundedness of
`Sol(F)` gives finiteness is `Ttc.exists_lattice_enum_of_isBounded`
(`Exec/Geometry`) and is not needed here. -/

/-- **A finite set is listed bijectively by `Fin` of its `Set.ncard`**: injectively,
into the set, and onto it.  `Ttc.exists_latticeEnum` (`Model/Pseudocode`) uses this
to turn "no enumeration exists" into "the set is infinite", which is what makes
`Ttc.latticeEnum` total. -/
theorem exists_finEnum_of_finite {α : Type*} {S : Set α} (hfin : S.Finite) :
    ∃ e : Fin S.ncard → α, Function.Injective e ∧ (∀ s, e s ∈ S) ∧
      (∀ x ∈ S, ∃ s, e s = x) := by
  have _ : Finite S := hfin.to_subtype
  have hcard : Nat.card S = S.ncard := Nat.card_coe_set_eq _
  obtain e := Finite.equivFinOfCardEq hcard
  refine ⟨fun s => (e.symm s : α), fun a b hab => ?_, fun s => (e.symm s).property,
    fun x hx => ⟨e ⟨x, hx⟩, ?_⟩⟩
  · exact e.symm.injective (Subtype.ext hab)
  · simp

end Ttc
