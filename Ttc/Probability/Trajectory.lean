/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Ttc.ModelSupport

/-!
# The ½-thinning and the coupled trajectory law

`alg:ttc`'s sample coins are a trajectory of the coupled level family: a level-`0`
vector of independent Poisson counts, thinned by a fair coin at every level.  Ionescu–
Tulcea (`ProbabilityTheory.Kernel.trajMeasure`) turns the one-step thinning kernel into
the law of the *whole* trajectory on one space, which is what makes every level's event
unconditional.

**What is here.**  The trajectory law itself — four definitions and the two
Markov-kernel instances the Ionescu–Tulcea construction takes as instance arguments,
which import Mathlib and nothing of ours — and, below, the five **read-offs** of a
trajectory that `alg:ttc`'s `thin`, `Pois` and `GenerateSamples` return
(`Ttc.toMultiset`, `Ttc.trajThin`, `Ttc.trajPois`, `Ttc.trajGen`, `Ttc.padRow`)
together with the two **contracts** the oracle bundle demands of them
(`Ttc.trajThin_le`, `Ttc.card_trajGen`).  The read-offs need `Ttc.Space`, so the file
imports `Ttc.ModelSupport` — which is also where the count-vector dictionary the two
contracts are proved from lives, stated at the sum `Ttc.toMultiset` unfolds to and so
mentioning nothing of this file.

Those two contracts are the *only* `Prop`s in `Ttc/Probability/`.  They are here
rather than in `Model/Pseudocode` because they say nothing about `TTC` — they are
facts about the read-offs of a trajectory, beside the trajectory law — and because
neither is reachable by `Ttc/Audit/ClosureCheck.lean`'s walk: both are `_proof_`
fields of `Ttc.algOracles`, so moving them changed no closure count.  Nothing else
here is a `Prop` and nothing is assumed.  Every *other* property of these objects —
that the thinning is the paper's `lem:process`, that the loops terminate almost
surely — is still proved downstream (`Process/Thinning`, `Process/Truncation`,
`Coupling/Family`).

The trajectory-law half of this file used to be the second half of `Model/Prelude`;
see `Ttc/Audit/ClosureCheck.lean` for why the audit surface is `Ttc/Model/`
**together with** `Ttc/Probability/`.
-/

namespace Ttc

open MeasureTheory ProbabilityTheory

/-- The thinning probability `½`, as an element of `unitInterval`. -/
noncomputable def half : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

/-- **One thinning step, as a Markov kernel.** Each coordinate is thinned
`Binomial(·, ½)`, independently across lattice points. -/
noncomputable def thinKernel (L : ℕ) : Kernel (Fin L → ℕ) (Fin L → ℕ) where
  toFun k := Measure.pi fun s => binomial (k s) half
  measurable' := Measurable.of_discrete

instance isMarkovKernel_thinKernel (L : ℕ) : IsMarkovKernel (thinKernel L) :=
  ⟨fun k => by
    show IsProbabilityMeasure (Measure.pi fun s => binomial (k s) half)
    infer_instance⟩

/-- The chain's kernel at step `n`: thin the state at time `n`. The history is
available but only its last coordinate is read — the chain is Markov. -/
noncomputable def chainKernel (L n : ℕ) :
    Kernel ((_i : ↥(Finset.Iic n)) → (Fin L → ℕ)) (Fin L → ℕ) :=
  Kernel.comap (thinKernel L) (fun h => h ⟨n, Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

instance isMarkovKernel_chainKernel (L n : ℕ) : IsMarkovKernel (chainKernel L n) := by
  rw [chainKernel]; infer_instance

/-- **The coupled family, as one measure on trajectories.** Start from the
level-`0` product of Poissons and thin forever. -/
noncomputable def trajLaw {L : ℕ} (θ : Fin L → ℝ) : Measure (ℕ → (Fin L → ℕ)) :=
  Kernel.trajMeasure (Measure.pi fun s => poissonMeasure (θ s).toNNReal) (chainKernel L)

/-! # The trajectory read-offs

`Ttc.trajOracles` (`Coupling/Family`) is an `Ttc.Oracles` bundle whose four random
fields are *read off* a trajectory `ω : ℕ → Fin L → ℕ` of the coupled level family.
Two of its six fields — `thin_le` and `gen_card` — are **contracts**: proof
obligations, discharged by `Ttc.toMultiset_le_of_count_le` and
`Multiset.card_replicate`. The other four are **values**: plain arithmetic on `ω`.

This section holds the values; the two contracts are the section after it. Both are
deliberately positioned *upstream* of `Ttc.Oracles`: they need nothing beyond
`Model/Prelude` (for `Ttc.Space`) and `ModelSupport` (for the count-vector
dictionary), and a `Ttc.run` that reads the trajectory directly reaches them without
an oracle bundle.

Nothing in *this* section is a `Prop`, and nothing here is assumed: every declaration
is a definition whose body is the arithmetic the paper's pseudocode performs. The two
facts *about* these definitions that `Ttc.trajOracles`' contract fields are built from
— that `Ttc.trajThin` produces a sub-multiset, that `Ttc.trajGen` produces exactly `N`
points — are below.

## Why the read-offs take a *row*, not a table

`trajPois` takes the membership row `mem i : Fin L → Bool` and the level slice
`ω j : Fin L → ℕ`, not the table `mem` and the trajectory `ω` with indices `i`, `j`.
That is the honest granularity: the value depends on the table only at the cube
being processed and on the trajectory only at the level being read, which is
precisely what `Ttc.trajOracles_pois_congr` and `Ttc.trajOracles_gen_congr`
(`Monadic/EventMeasurable`) and the congruence lemmas of `Exec/Coverage` say. Taking
rows makes those facts visible in the signature instead of provable from it.

These definitions live here, rather than in `Coupling/`, because they are part of
the audit surface: `Ttc/Audit/ClosureCheck.lean` requires the algorithm's output to
be defined entirely under `Ttc/Model/` or `Ttc/Probability/`, and a `Ttc.run` that
reads a trajectory directly reaches them.  They were in `Model/Pseudocode` until the
two contracts below made that file carry theorems it did not want; read-offs of a
trajectory belong beside the trajectory law, which is here. -/

variable {L : ℕ}

/-! ## Count vectors as multisets

The run's state is a `Multiset (Space n)`; the family is a count vector. This is the
dictionary between them, given an injective enumeration `pt` of the lattice points.
`Ttc.toMultiset` builds the multiset with prescribed multiplicities; that it *has*
those multiplicities (`Ttc.count_toMultiset`) is a theorem, and is in `ModelSupport`
— stated at the sum this definition unfolds to, so that it mentions nothing of this
file — together with the rest of the dictionary.  The two oracle contracts it is
there to prove are below.  Its cardinality lemma `Ttc.card_toMultiset`, which no
contract needs, is in `Coupling/Family`. -/

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

/-! ## The two oracle contracts

`Ttc.toMultiset` (above) turns a count vector into the run's `Multiset (Space n)`
state.  The facts that make it a dictionary — that the multiplicities are the
prescribed ones — are `Ttc.count_toMultiset`, `Ttc.count_toMultiset_of_notMem` and
`Ttc.toMultiset_le_of_count_le` (`ModelSupport`), stated there at the sum
`Ttc.toMultiset` is and so mentioning nothing of this file.  What is here is the two
contracts `Ttc.Oracles` demands of any bundle, which mention `Ttc.trajThin` and
`Ttc.trajGen` and therefore have to be stated wherever those two are defined.

These are the only two `Prop`s in `Ttc/Probability/`, and they are the reason the
read-offs came here from `Model/Pseudocode` rather than the other way round: a
theorem cannot be stated upstream of the definition it is about, and `Ttc.algOracles`
(`Model/Pseudocode`) needs both at elaboration time, so they cannot go downstream
either.  Neither is visible to `Ttc/Audit/ClosureCheck.lean` — a theorem is entered
only through its type, and these two are reached as `_proof_` fields of
`Ttc.algOracles` — so the move changed no closure count. -/

section Dictionary

/-- **The `thin` contract**: `Ttc.trajThin` removes elements, it never invents them.
This is `Ttc.Oracles.thin_le` for the bundle `Ttc.ttcRun` builds. -/
theorem trajThin_le {n : ℕ} {pt : Fin L → Space n} (hpt : Function.Injective pt)
    (ωj : Fin L → ℕ) (X : Multiset (Space n)) : trajThin pt ωj X ≤ X :=
  toMultiset_le_of_count_le hpt fun _ => min_le_right _ _

/-- **The `gen` contract**: `Ttc.trajGen` returns exactly `N` points.  This is
`Ttc.Oracles.gen_card` for the bundle `Ttc.ttcRun` builds. -/
theorem card_trajGen {n : ℕ} (pt : Fin L → Space n) (m : Fin L → Bool) (ωj : Fin L → ℕ)
    (N : ℕ) (pad : Space n) : Multiset.card (trajGen pt m ωj N pad) = N := by
  classical
  rw [trajGen]
  by_cases h : Multiset.card (toMultiset pt fun s => if m s then ωj s else 0) = N
  · simp only [h, if_pos]
  · simp only [h, if_false]
    exact Multiset.card_replicate _ _

end Dictionary

end Ttc
