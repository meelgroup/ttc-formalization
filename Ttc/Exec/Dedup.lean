/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Dnf
import Ttc.Model.Pseudocode

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
`Ttc.mem_toDNFd` and `Ttc.toDNFd_nodup`; every later proof goes through those two and
never mentions an instance again.  In particular the counting lemmas
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
imports.  What is here is everything *proved* about it.
-/

/-- **Deduplication preserves the cubes.**  Everything the development asks of a DNF
is a statement about its members, so this single lemma is what makes `toDNFd` a
drop-in replacement for `toDNF`. -/
theorem mem_toDNFd {φ : BForm A} {c : Cube A} : c ∈ toDNFd φ ↔ c ∈ toDNF φ :=
  @List.mem_dedup _ (Classical.decEq (Cube A)) c (toDNF φ)

/-- **The output is duplicate-free** — the property `Ttc.toDNF` provably lacks. -/
theorem toDNFd_nodup (φ : BForm A) : (toDNFd φ).Nodup :=
  @List.nodup_dedup _ (Classical.decEq (Cube A)) (toDNF φ)

/-! ## The two correctness properties transfer -/

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
meet; it follows from any member, hence from non-emptiness.
-/

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

/-- **Deduplication does not empty a non-empty DNF** — the conditional form, which
depends on nothing but `Ttc.mem_toDNFd`. -/
theorem toDNFd_ne_nil_of {φ : BForm A} (h : toDNF φ ≠ []) : toDNFd φ ≠ [] := by
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ h
  exact List.ne_nil_of_mem (mem_toDNFd.2 hc)

/-- **A positive formula has a non-empty deduplicated DNF.**  Together with
`Ttc.one_le_card_cubes` this discharges `hm` for `toDNFd`. -/
theorem toDNFd_ne_nil {φ : BForm A} (h : φ.IsPositive) : toDNFd φ ≠ [] := by
  obtain ⟨c, hc⟩ := exists_mem_toDNF φ h
  exact List.ne_nil_of_mem (mem_toDNFd.2 hc)

/-! ## Axiom audit -/

#print axioms natCard_mem_list
#print axioms natCard_mem_list_of_nodup
#print axioms mem_toDNFd
#print axioms toDNFd_nodup
#print axioms toDNFd_isDNFOf
#print axioms toDNFd_isPositive
#print axioms card_toDNFd
#print axioms length_toDNFd_le_card
#print axioms exists_mem_toDNF
#print axioms toDNFd_ne_nil_of
#print axioms toDNFd_ne_nil

end Ttc
