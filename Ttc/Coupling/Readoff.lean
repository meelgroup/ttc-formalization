/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Model.Prelude

/-!
# The trajectory read-offs

`Ttc.trajOracles` (`Coupling/Family`) is an `Ttc.Oracles` bundle whose four random
fields are *read off* a trajectory `ω : ℕ → Fin L → ℕ` of the coupled level family.
Two of its six fields — `thin_le` and `gen_card` — are **contracts**: proof
obligations, discharged in `Coupling/Family` by `Ttc.toMultiset_le_of_count_le` and
`Multiset.card_replicate`. The other four are **values**: plain arithmetic on `ω`.

This file holds the values, and nothing else. It is deliberately positioned
*upstream* of `Ttc.Oracles`: its only `Ttc` import is `Model/Prelude` (for
`Ttc.Space`), so `Model/Pseudocode` can import it without a cycle, and a `Ttc.run`
that reads the trajectory directly needs no oracle bundle and hence no contract.

Nothing here is a `Prop`, and nothing here is assumed: every declaration is a
definition whose body is the arithmetic the paper's pseudocode performs. The facts
*about* these definitions — that `Ttc.trajThin` produces a sub-multiset, that
`Ttc.trajGen` produces exactly `N` points — stay with the theorems that prove them,
in `Coupling/Family`, and are what `Ttc.trajOracles`' two contract fields are built
from.

## Why the read-offs take a *row*, not a table

`trajPois` takes the membership row `mem i : Fin L → Bool` and the level slice
`ω j : Fin L → ℕ`, not the table `mem` and the trajectory `ω` with indices `i`, `j`.
That is the honest granularity: the value depends on the table only at the cube
being processed and on the trajectory only at the level being read, which is
precisely what `Ttc.trajOracles_pois_congr` and `Ttc.trajOracles_gen_congr`
(`Monadic/EventMeasurable`) and the congruence lemmas of `Exec/Coverage` say. Taking
rows makes those facts visible in the signature instead of provable from it.
-/

namespace Ttc

variable {L : ℕ}

/-! ## Count vectors as multisets

The run's state is a `Multiset (Space n)`; the family is a count vector. This is the
dictionary between them, given an injective enumeration `pt` of the lattice points.
`Ttc.toMultiset` builds the multiset with prescribed multiplicities; that it *has*
those multiplicities (`Ttc.count_toMultiset`) is a theorem, and lives with the other
theorems in `Coupling/Family`. -/

/-- The multiset holding `k s` copies of the lattice point `pt s`. -/
noncomputable def toMultiset {n : ℕ} (pt : Fin L → Space n) (k : Fin L → ℕ) :
    Multiset (Space n) :=
  ∑ s, Multiset.replicate (k s) (pt s)

/-! ## The four read-offs

`vol` and `covered` are read off nothing — `Ttc.trajOracles` returns the functions it
was handed — so they need no definition here. The three that read `ω` do. -/

/-- **`thin`, read off the trajectory** (`alg:ttc` lines 33, 40): what survives of
`X` at a level whose count vector is `ωj`.

Capped at what `X` actually holds, so that the sub-multiset contract
(`Ttc.Oracles.thin_le`, discharged in `Coupling/Family`) holds for *every* multiset
and not only for the ones the run produces. On the states the run does reach the
multiplicities *are* the level's counts, so the `min` is inert — see `Coupling/Run`. -/
noncomputable def trajThin {n : ℕ} (pt : Fin L → Space n) (ωj : Fin L → ℕ)
    (X : Multiset (Space n)) : Multiset (Space n) :=
  toMultiset pt fun s => min (ωj s) (Multiset.count (pt s) X)

/-- **`Pois(λ)`, read off the trajectory** (`alg:ttc` lines 38, 41): the family's
total over the cube whose membership row is `m`, at a level whose count vector is
`ωj`. The rate `λ` is not read — the trajectory already carries it. -/
def trajPois (m : Fin L → Bool) (ωj : Fin L → ℕ) : ℕ :=
  ∑ s ∈ Finset.univ.filter fun s => m s = true, ωj s

/-- **`GenerateSamples`, read off the trajectory** (`alg:ttc` line 43): the family
restricted to the cube whose membership row is `m`, at a level whose count vector is
`ωj`.

`gen` must return exactly `N` points for **every** `N` (`Ttc.Oracles.gen_card`,
discharged in `Coupling/Family`), but the family's size is whatever `pois` returned.
So this falls back to `N` copies of `pad` when the two disagree — a branch the run
never takes, since it always passes the `N` that `trajPois` produced. The caller
supplies `pad` from the cube's own lattice points where it has any
(`Ttc.padPoint`), so that the membership contract still holds. -/
noncomputable def trajGen {n : ℕ} (pt : Fin L → Space n) (m : Fin L → Bool)
    (ωj : Fin L → ℕ) (N : ℕ) (pad : Space n) : Multiset (Space n) :=
  open Classical in
  if Multiset.card (toMultiset pt fun s => if m s then ωj s else 0) = N then
    toMultiset pt fun s => if m s then ωj s else 0
  else Multiset.replicate N pad

/-- A lattice point of the cube whose membership row is `m`, if it has one. Used only
as `Ttc.trajGen`'s `pad`, i.e. only on the branch the run never takes.
`Ttc.padPoint` (`Coupling/Family`) is this at the row `mem i`. -/
noncomputable def padRow {n : ℕ} (pt : Fin L → Space n) (m : Fin L → Bool) : Space n :=
  open Classical in
  if h : ∃ s, m s = true then pt h.choose else 0

end Ttc
