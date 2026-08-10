/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Dnf
import Ttc.Model.Pseudocode
import Ttc.Exec.Params

/-!
# A duplicate-free `ToDNF`

`Ttc.ttc_volume_final` (`Exec/Final.lean`) carries the hypothesis

```
hlen : ((toDNF φ).length : ℝ) ≤ P.m      with  P.m = Nat.card {c : Cube A // c ∈ toDNF φ}
```

which is a `Nodup` condition on the cube list in disguise: the length of a list is
at most the number of its *distinct* elements exactly when it has no repeats.  The
development's own converter does **not** satisfy it, and provably so —
`Ttc.toDNF_length_gt_card_cubes` (`Exec/Statement.lean`) exhibits the positive
formula `a ∨ a`, whose DNF is `[[a], [a]]`: length `2`, one distinct cube, so
`hlen` would read `(2 : ℝ) ≤ 1`.

This file supplies the fix's proofs: `Ttc.length_toDNFd_le_card`, which is `hlen`
for `Ttc.toDNFd` — **discharged, not assumed** — and the lemmas that make `toDNFd` a
drop-in replacement for `Ttc.toDNF`.

The **definition** `Ttc.toDNFd` is not here.  It is line A1 of the preprocessing
transcription, so it lives in `Model/Pseudocode` with the other twelve lines, and
this file imports it; that is what keeps `Model/` free of any `Exec/` import.

## Definition used

`toDNFd φ := (toDNF φ).dedup`, with the `DecidableEq (Cube A)` instance supplied
classically (`Classical.decEq`) and written **explicitly** in the definition.  The
`List.pwFilter` route would work equally well — `List.dedup` is *defined* as
`pwFilter (· ≠ ·)` — but `dedup` has the richer API (`List.card_toFinset`,
`List.Nodup.dedup`), so `dedup` it is.

The one wrinkle is the usual one: `Cube A` has no `DecidableEq` instance to
synthesize, so `List.mem_dedup` and `List.nodup_dedup` cannot be applied by
`exact`/`rw` — their instance argument has to be handed over by hand
(`@List.mem_dedup _ (Classical.decEq (Cube A)) …`).  That is done once each, in
`Ttc.mem_toDNFd` (now in `Model/Pseudocode`) and `Ttc.toDNFd_nodup` below; every
later proof goes through those two and never mentions an instance again.  In particular the counting lemmas
(`Ttc.natCard_mem_list`, `Ttc.natCard_mem_list_of_nodup`) take `[DecidableEq α]` as an
ordinary instance binder and are discharged by `classical`, since `Nat.card` does not
depend on the instance at all.

## What deduplication does and does not change

* **It does not change the semantics.**  `Ttc.mem_toDNFd` says `toDNFd φ` and
  `toDNF φ` have exactly the same members.  `IsDNFOf` and `DNF.IsPositive` are both
  statements about the *members* of the list — `DNF.holds v D = ∃ c ∈ D, c.holds v`
  and `DNF.IsPositive D = ∀ c ∈ D, Cube.IsPositive c` — so both transfer verbatim
  (`Ttc.toDNFd_isDNFOf`, `Ttc.toDNFd_isPositive`).  Downstream, the region `P(cᵢ)`
  of each cube and the union `⋃ᵢ P(cᵢ)` are unchanged, so the solution set the
  algorithm is estimating is literally the same set.
* **It does change the cost, and honestly so — not for free.**  `m` is the number of
  cubes, so removing duplicates *shrinks* `m`, and `Params.deltaPrime = δ / (4m)`
  therefore *grows*: each surviving cube is estimated at a **looser** confidence
  than it would have been in the duplicated run.  This is sound — the union bound is
  over the cubes that actually exist — but it is a different run of the algorithm
  with different per-cube parameters, not a cosmetic rewrite of the same one.  The
  charged running time `m · (C_vol + C_sample · Thresh)` drops for the same reason.
  A caller who wants the duplicated cost profile must keep `Ttc.toDNF` and supply
  `hlen` some other way; `Ttc.toDNF_length_gt_card_cubes` says it cannot always be
  supplied at all.
-/

namespace Ttc

variable {A : Type*}

/-! ## Counting the members of a list

Two general-purpose steps, kept separate so the `Nodup` case below is one rewrite.
`Nat.card` does not depend on the `DecidableEq` instance, so the instance binder in
the first lemma is free to be instantiated classically at the use site.
-/

/-- **The subtype of a list's members is counted by its `toFinset`.**  The proof is
the evident equivalence `{x // x ∈ l} ≃ {x // x ∈ l.toFinset}`; no `Finite` instance
is needed, since `Nat.card` of a `Finset` coercion is its `card` outright. -/
theorem natCard_mem_list {α : Type*} [DecidableEq α] (l : List α) :
    Nat.card {x : α // x ∈ l} = l.toFinset.card := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun _ => List.mem_toFinset.symm),
    Nat.card_eq_finsetCard]

/-- **A duplicate-free list has exactly `length` distinct members.**  This is the
content of `hlen`: for a `Nodup` list the bound `length ≤ card` holds with equality,
and for a list with repeats it fails. -/
theorem natCard_mem_list_of_nodup {α : Type*} {l : List α} (h : l.Nodup) :
    Nat.card {x : α // x ∈ l} = l.length := by
  classical
  rw [natCard_mem_list l, List.card_toFinset, h.dedup]

/-! ## The converter

`Ttc.toDNFd` itself is **not** defined here: it is line A1 of the preprocessing, so
it lives with the rest of the transcription in `Model/Pseudocode`, which this file
imports.  **Everything proved about it is here**, including the four basic
properties `Ttc.mem_toDNFd`, `Ttc.toDNFd_isDNFOf`, `Ttc.exists_mem_toDNF` and
`Ttc.toDNFd_ne_nil` that `Ttc.inputParams` needs: none of them is in the
definitional closure of `Ttc.ttc` or of `Ttc.ttc_volume_estimate`'s statement, so
none of them belongs in the audit surface (`Ttc/Audit/ClosureCheck.lean` measures
exactly that).  `Ttc.inputParams` itself is here too, for the same reason — the run
reads the *total* block `Ttc.inputParamsTotal`, which is a function of the data
alone and needs no lemma.
-/

/-- **Deduplication preserves the cubes.**  Everything the development asks of a DNF
is a statement about its members, so this single lemma is what makes `toDNFd` a
drop-in replacement for `toDNF`.

`Ttc.Cube A` has no `DecidableEq` to synthesize, so `List.mem_dedup`'s instance
argument is handed over by hand, matching `Ttc.toDNFd`'s own `Classical.decEq`. -/
theorem mem_toDNFd {φ : BForm A} {c : Cube A} : c ∈ toDNFd φ ↔ c ∈ toDNF φ :=
  @List.mem_dedup _ (Classical.decEq (Cube A)) c (toDNF φ)

/-- **`toDNFd` is still a correct DNF of `φ`.**  `DNF.holds v D = ∃ c ∈ D, c.holds v`
depends on `D` only through its members, and `Ttc.mem_toDNFd` says those are
unchanged; `Ttc.toDNF_isDNFOf` does the rest. -/
theorem toDNFd_isDNFOf (φ : BForm A) : IsDNFOf (toDNFd φ) φ := by
  intro v
  rw [← toDNF_isDNFOf φ v]
  constructor
  · rintro ⟨c, hc, hcv⟩
    exact ⟨c, mem_toDNFd.1 hc, hcv⟩
  · rintro ⟨c, hc, hcv⟩
    exact ⟨c, mem_toDNFd.2 hc, hcv⟩

/-- **A positive formula has at least one cube.**  Structural induction: `BForm` has
no `false` constructor, `neg` is excluded by positivity, `or` appends and `and`
crosses, and both operations preserve "has a member". -/
theorem exists_mem_toDNF : ∀ (φ : BForm A), φ.IsPositive → ∃ c, c ∈ toDNF φ := by
  intro φ
  induction φ with
  | tt => intro _; exact ⟨[], List.mem_singleton_self _⟩
  | atom a => intro _; exact ⟨[⟨a, true⟩], List.mem_singleton_self _⟩
  | neg φ _ => intro h; exact absurd h id
  | and φ ψ ihφ ihψ =>
      rintro ⟨hφ, hψ⟩
      obtain ⟨c, hc⟩ := ihφ hφ
      obtain ⟨d, hd⟩ := ihψ hψ
      refine ⟨c ++ d, ?_⟩
      show c ++ d ∈ (toDNF φ).cross (toDNF ψ)
      rw [DNF.cross, List.mem_flatMap]
      exact ⟨c, hc, List.mem_map_of_mem hd⟩
  | or φ ψ ihφ ihψ =>
      rintro ⟨hφ, _⟩
      obtain ⟨c, hc⟩ := ihφ hφ
      exact ⟨c, List.mem_append_left _ hc⟩

/-- **A positive formula has a non-empty deduplicated DNF.**  Together with
`Ttc.one_le_card_cubes_of_ne_nil` this discharges `hm` for `toDNFd`. -/
theorem toDNFd_ne_nil {φ : BForm A} (h : φ.IsPositive) : toDNFd φ ≠ [] := by
  obtain ⟨c, hc⟩ := exists_mem_toDNF φ h
  exact List.ne_nil_of_mem (mem_toDNFd.2 hc)

/-- **The output is duplicate-free** — the property `Ttc.toDNF` provably lacks. -/
theorem toDNFd_nodup (φ : BForm A) : (toDNFd φ).Nodup :=
  @List.nodup_dedup _ (Classical.decEq (Cube A)) (toDNF φ)

/-! ## Positivity transfers -/

/-- **`toDNFd` is still positive on a positive formula.**  `DNF.IsPositive D`
quantifies over the members of `D`, and deduplication only removes members. -/
theorem toDNFd_isPositive {φ : BForm A} (h : φ.IsPositive) :
    DNF.IsPositive (toDNFd φ) :=
  fun _ hc => toDNF_isPositive h _ (mem_toDNFd.1 hc)

/-! ## `hlen`, discharged -/

/-- **The cube count of `toDNFd φ` is its length** — the equality `hlen` only asks
for as an inequality.  Immediate from `Ttc.toDNFd_nodup`. -/
theorem card_toDNFd (φ : BForm A) :
    Nat.card {c : Cube A // c ∈ toDNFd φ} = (toDNFd φ).length :=
  natCard_mem_list_of_nodup (toDNFd_nodup φ)

/-- **`hlen` for `toDNFd`**, in the exact form `Ttc.ttc_volume_final` asks it:
`((toDNFd φ).length : ℝ) ≤ P.m` with `P.m = Nat.card {c // c ∈ toDNFd φ}`.  It holds
with equality, so no slack is being claimed. -/
theorem length_toDNFd_le_card (φ : BForm A) :
    ((toDNFd φ).length : ℝ) ≤ (Nat.card {c : Cube A // c ∈ toDNFd φ} : ℝ) :=
  le_of_eq (by rw [card_toDNFd])

/-! ## Non-emptiness

`hm : 1 ≤ Nat.card {c // c ∈ toDNFd φ}` is the other side condition a caller must
meet; it follows from any member, hence from non-emptiness.  `Ttc.toDNFd_ne_nil`
above derives it from positivity; the conditional version below assumes
non-emptiness of the raw DNF instead.
-/

/-- **Deduplication does not empty a non-empty DNF** — the conditional form, which
depends on nothing but `Ttc.mem_toDNFd`. -/
theorem toDNFd_ne_nil_of {φ : BForm A} (h : toDNF φ ≠ []) : toDNFd φ ≠ [] := by
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ h
  exact List.ne_nil_of_mem (mem_toDNFd.2 hc)

/-! ## The preprocessed formula is positive

`Ttc.inputParams` needs `φ.IsPositive`, and the formula the algorithm is handed is
`Ttc.preprocess atoms φ`, which is a `Ttc.dnfForm` — built from `.and`, `.or`,
`.atom` and `.tt` only, hence positive with no hypothesis at all.

(`Exec/Cleanup` proves the same thing under the name `Ttc.isPositive_dnfForm`; that
module imports this one, so the two-line induction is repeated there rather than
imported.  Neither is an assumption — both are proofs.) -/

/-- A cube's formula is positive: it is a `Ttc.conj` of atoms. -/
theorem cubeForm_isPositive (c : Cube A) : (cubeForm c).IsPositive := isPositive_conj _

/-- **`Ttc.dnfForm` is always positive** — it is built from `.or`, `.and`, `.atom`
and `.tt` only, and `Ttc.BForm.IsPositive` is exactly "no `.neg`". -/
theorem dnfForm_isPositive : ∀ D : DNF A, (dnfForm D).IsPositive := by
  intro D
  induction D with
  | nil => exact trivial
  | cons c D ih =>
      cases D with
      | nil => exact cubeForm_isPositive c
      | cons c' D' => exact ⟨cubeForm_isPositive c, ih⟩

/-- **The formula the algorithm is handed is positive**, unconditionally: lines
A3 and A6 both rebuild it with `Ttc.dnfForm`. -/
theorem preprocess_isPositive {n : ℕ} (atoms : A → LinAtom n) (φ : BForm A) :
    (preprocess atoms φ).IsPositive := dnfForm_isPositive _

/-! ## The parameter block at the algorithm's own inputs

`Ttc.inputParamsTotal` (`Model/Pseudocode`) is what the run reads; it is a total
function of `(atoms, φ, ε, δ)` and needs no proof.  `Ttc.inputParams` is the same
block built the other way, out of `Ttc.ttcParams` and the side conditions above, and
`Ttc.inputParamsTotal_eq_inputParams` says the two agree wherever the headline's
hypotheses hold — so every theorem stated about `Ttc.inputParams` transfers to the
block the algorithm actually uses.  Neither the `def` nor the lemma is in the
definitional closure of `Ttc.ttc`, which is why both are here rather than in
`Model/`. -/

/-- **The parameter block `TTC` computes** (`alg:ttc` lines 17–20), with `hm` and
`hr` supplied by `Ttc.one_le_card_cubes_of_ne_nil` and
`Ttc.one_le_card_facets_of_isBounded` rather than assumed.  The headline used to
carry `P` as a binder with `hP : P = ttcParams …`; this is that right-hand side,
named, so that both are discharged by `rfl`.

The internal failure parameter is `δ₀ = 4δ/5`, so that the conclusion is a clean
`1 − δ` — see `Exec/Final.lean` for what that reprices. -/
noncomputable def inputParams {n : ℕ} (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hbdd : Bornology.IsBounded (sol (atomSet atoms) φ)) : Params :=
  ttcParams (toDNFd φ) n ε (4 * δ / 5) hε0 hε1 hn
    (one_le_card_cubes_of_ne_nil (toDNFd_ne_nil hφ))
    (one_le_card_facets_of_isBounded hn (toDNFd_isDNFOf φ) hbdd (toDNFd_ne_nil hφ))

/-- **The agreement lemma at the algorithm's inputs.**  Under the four hypotheses
the headline already carries — three plain inequalities and boundedness — the total
block is `Ttc.inputParams`. -/
theorem inputParamsTotal_eq_inputParams {n : ℕ} (atoms : A → LinAtom n) (φ : BForm A)
    (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hbdd : Bornology.IsBounded (sol (atomSet atoms) φ)) :
    inputParamsTotal atoms φ ε δ = inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd :=
  ttcParamsTotal_eq _ _ _ _ hε0 hε1 hn _ _

/-! ## Axiom audit -/

#print axioms mem_toDNFd
#print axioms toDNFd_isDNFOf
#print axioms exists_mem_toDNF
#print axioms toDNFd_ne_nil
#print axioms cubeForm_isPositive
#print axioms dnfForm_isPositive
#print axioms preprocess_isPositive
#print axioms inputParams
#print axioms inputParamsTotal_eq_inputParams
#print axioms natCard_mem_list
#print axioms natCard_mem_list_of_nodup
#print axioms toDNFd_nodup
#print axioms toDNFd_isPositive
#print axioms card_toDNFd
#print axioms length_toDNFd_le_card
#print axioms toDNFd_ne_nil_of

end Ttc
