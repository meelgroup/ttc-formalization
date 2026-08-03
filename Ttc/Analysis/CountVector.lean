/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Analysis.LatticeAssembled
import Ttc.Analysis.SketchProcess

/-!
# The run's state as a count vector

`lem:numlattice`'s invariant is about the *multiplicities* of `𝒳`: "the multiset
`𝒳` contains `k` copies of each lattice point of `S`, `k ∼ Pois(p̃)`". To state
that in Lean the run's `𝒳 : Multiset (Space n)` has to be read as a vector of
counts indexed by a fixed finite set — and two facts make that legitimate, both
now proved rather than assumed:

* `Ttc.TtcProb.run_state_mem` — `𝒳` never leaves `Sol(F) ∩ 𝕃ⁿ`;
* `Ttc.TtcProb.sol_lattice_finite` — that set is finite (a consequence of
  `claim:cl`(a), not an assumption).

So `Ttc.TtcProb.latPts` enumerates it, and `Ttc.TtcProb.cnt` reads a multiset as a
`Fin latCard → ℕ`. The lemma that matters is
`Ttc.TtcProb.card_eq_sum_cnt`: the algorithm's `|𝒳|` — the numerator of its output
— is the *total* of the count vector, which is exactly the quantity the level
process controls (`Ttc.map_sum_levelLaw`).
-/

namespace Ttc

open MeasureTheory Multiset

namespace TtcProb

variable {A : Type*} {n : ℕ} (T : TtcProb A n)

/-! ## Enumerating the lattice points -/

/-- **`Sol(F) ∩ 𝕃ⁿ`, as a `Finset`** — the index set of the invariant. -/
noncomputable def latPts : Finset (Space n) := T.sol_lattice_finite.toFinset

@[simp] theorem mem_latPts {s : Space n} :
    s ∈ T.latPts ↔ s ∈ sol T.M T.φ ∩ fineLattice n (latticeScale T.ρ) := by
  rw [latPts, Set.Finite.mem_toFinset]

/-- **`|Q ∩ 𝕃ⁿ|`**, the paper's lattice-point count. -/
noncomputable def latCard : ℕ := T.latPts.card

/-- The lattice point at index `i`. -/
noncomputable def latPtAt (i : Fin T.latCard) : Space n :=
  (T.latPts.equivFin.symm i).val

theorem latPtAt_mem (i : Fin T.latCard) : T.latPtAt i ∈ T.latPts :=
  (T.latPts.equivFin.symm i).property

theorem latPtAt_injective : Function.Injective T.latPtAt := fun _ _ h =>
  T.latPts.equivFin.symm.injective (Subtype.ext h)

/-- The enumeration is onto the lattice points. -/
theorem exists_latPtAt {s : Space n} (hs : s ∈ T.latPts) : ∃ i, T.latPtAt i = s := by
  refine ⟨T.latPts.equivFin ⟨s, hs⟩, ?_⟩
  rw [latPtAt, Equiv.symm_apply_apply]

/-- **The count is the paper's `|Q ∩ 𝕃ⁿ|`** — the `Finset` card and the `Set.ncard`
of `Ttc.latticeCount` agree. -/
theorem latCard_eq : (T.latCard : ℝ) = (latticeCount T.M T.φ T.ρ : ℝ) := by
  rw [latCard, latticeCount, latPts, Set.ncard_eq_toFinset_card _ T.sol_lattice_finite]

/-! ## The count vector -/

/-- **The count vector of a sample multiset**: how many copies of each lattice
point it holds. -/
noncomputable def cnt (X : Multiset (Space n)) (i : Fin T.latCard) : ℕ :=
  X.count (T.latPtAt i)

/-- **`|𝒳|` is the total of the count vector**, for any multiset supported on the
lattice points. This is the bridge from the algorithm's output — whose numerator
is `card 𝒳` — to the quantity the level process controls. -/
theorem card_eq_sum_cnt (X : Multiset (Space n)) (hX : ∀ s ∈ X, s ∈ T.latPts) :
    (card X : ℕ) = ∑ i, T.cnt X i := by
  classical
  have hreindex : ∑ i, T.cnt X i = ∑ s ∈ T.latPts, X.count s := by
    have h1 : ∑ i, T.cnt X i = ∑ x : {x // x ∈ T.latPts}, X.count x.val :=
      Equiv.sum_comp T.latPts.equivFin.symm (fun x : {x // x ∈ T.latPts} => X.count x.val)
    rw [h1]
    exact Finset.sum_attach T.latPts (fun s => X.count s)
  rw [hreindex, ← Multiset.toFinset_sum_count_eq X]
  refine Finset.sum_subset ?_ ?_
  · intro s hs
    exact hX s (Multiset.mem_toFinset.1 hs)
  · intro s _ hs
    rw [Multiset.count_eq_zero]
    exact fun h => hs (Multiset.mem_toFinset.2 h)

/-- The run's state is supported on the lattice points, so its cardinality is the
total of its count vector. -/
theorem card_run_eq_sum_cnt (ω : T.Ω) :
    (card (T.D.foldl (step T.P (T.O ω) T.fuel T.ρ) ⟨0, 1, 0, 0⟩).X : ℕ)
      = ∑ i, T.cnt (T.D.foldl (step T.P (T.O ω) T.fuel T.ρ) ⟨0, 1, 0, 0⟩).X i :=
  T.card_eq_sum_cnt _ fun s hs => T.mem_latPts.2 (T.run_state_mem ω s hs)

end TtcProb

end Ttc
