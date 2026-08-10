/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Model.Prelude

/-!
# `ToDNF` is correct

`alg:ttc` line 16 calls circuit AllSAT to turn the Boolean abstraction `F_bool`
into a DNF. `Ttc.toDNF` (`Model/Prelude`) is that call, written as a function, and
this file proves the two things the rest of the development needs of it:

* `Ttc.toDNF_isDNFOf` — its output represents the formula, on every Boolean
  assignment.
* `Ttc.toDNF_isPositive` — on a **positive** input formula (no negation anywhere,
  `Ttc.BForm.IsPositive`) the output has no negated literal, so each `P(cᵢ)` is an
  intersection of closed half-spaces.

**What these do and do not buy.**  `isDNF` and `isPositive` are **still fields** of
`Ttc.TtcProb` (`Model/ProblemSetting.lean`), so the headline *does* still assume
that the external AllSAT call at line 16 got it right.  What this file establishes
is that those assumptions are **satisfiable** — `Ttc.toDNF` is a witness meeting
both — which is the §11 non-vacuity check, not an elimination.

An earlier version of this docstring claimed the two fields had become theorems and
that "the headline assumes nothing about line 16".  That was false; the fields are
at `ProblemSetting.lean:376` and `:381`.

The recursion carries a polarity (`Ttc.dnfAux`), so negation is handled by
flipping a flag instead of rewriting the formula — which is what makes the whole
thing structural, and the proof a plain induction.

**Scope.** This is a *correct* `ToDNF`, not the paper's. `TTC` runs an optimised
circuit-AllSAT whose output is a different, generally much smaller DNF; the
guarantee proved here is for the DNF this converter returns. The analysis never
looks at which correct DNF it was handed — see `Ttc.TtcProb.sol_eq_union` — so the
argument is unchanged either way, but the number of cubes `m`, and hence the
running-time claim the paper makes, are about AllSAT's output and not this one.
-/

namespace Ttc

variable {A : Type*}

/-! ## `cross` -/

@[simp] theorem DNF.holds_cross (v : A → Prop) (D E : DNF A) :
    (D.cross E).holds v ↔ D.holds v ∧ E.holds v := by
  classical
  constructor
  · rintro ⟨c, hc, hcv⟩
    rw [DNF.cross, List.mem_flatMap] at hc
    obtain ⟨d, hd, hc⟩ := hc
    rw [List.mem_map] at hc
    obtain ⟨e, he, rfl⟩ := hc
    exact ⟨⟨d, hd, fun l hl => hcv l (List.mem_append_left _ hl)⟩,
           ⟨e, he, fun l hl => hcv l (List.mem_append_right _ hl)⟩⟩
  · rintro ⟨⟨d, hd, hdv⟩, ⟨e, he, hev⟩⟩
    refine ⟨d ++ e, ?_, ?_⟩
    · rw [DNF.cross, List.mem_flatMap]
      exact ⟨d, hd, List.mem_map_of_mem he⟩
    · intro l hl
      rcases List.mem_append.1 hl with h | h
      exacts [hdv l h, hev l h]

@[simp] theorem DNF.holds_append (v : A → Prop) (D E : DNF A) :
    (D ++ E).holds v ↔ D.holds v ∨ E.holds v := by
  constructor
  · rintro ⟨c, hc, hcv⟩
    rcases List.mem_append.1 hc with h | h
    exacts [Or.inl ⟨c, h, hcv⟩, Or.inr ⟨c, h, hcv⟩]
  · rintro (⟨c, hc, hcv⟩ | ⟨c, hc, hcv⟩)
    exacts [⟨c, List.mem_append_left _ hc, hcv⟩, ⟨c, List.mem_append_right _ hc, hcv⟩]

/-! ## Correctness -/

/-- **The polarity-carrying converter is correct**: at polarity `true` it
represents the formula, at `false` its negation. Induction on the formula; the
`neg` case is where the polarity earns its keep, and the `false` cases are De
Morgan. Classical, for the `¬¬` step. -/
theorem holds_dnfAux (v : A → Prop) :
    ∀ (φ : BForm A) (p : Bool),
      (dnfAux φ p).holds v ↔ (if p then φ.holds v else ¬ φ.holds v) := by
  classical
  intro φ
  induction φ with
  | tt =>
      intro p
      cases p
      · simp [dnfAux, DNF.holds, BForm.holds]
      · simp only [dnfAux, if_true]
        exact ⟨fun _ => trivial, fun _ => ⟨[], List.mem_singleton_self _, by simp [Cube.holds]⟩⟩
  | atom a =>
      intro p
      have : (dnfAux (.atom a) p).holds v ↔ (Lit.mk a p).holds v := by
        constructor
        · rintro ⟨c, hc, hcv⟩
          rw [dnfAux, List.mem_singleton] at hc
          subst hc
          exact hcv _ (List.mem_singleton_self _)
        · intro h
          exact ⟨[⟨a, p⟩], by simp [dnfAux], by
            intro l hl; rw [List.mem_singleton] at hl; subst hl; exact h⟩
      rw [this, Lit.holds]
      cases p <;> simp [BForm.holds]
  | neg φ ih =>
      intro p
      rw [dnfAux, ih]
      cases p
      · simp [BForm.holds]
      · simp [BForm.holds]
  | and φ ψ ihφ ihψ =>
      intro p
      cases p
      · rw [dnfAux, DNF.holds_append, ihφ, ihψ]
        simp only [Bool.false_eq_true, if_false, BForm.holds]; tauto
      · rw [dnfAux, DNF.holds_cross, ihφ, ihψ]
        simp [BForm.holds]
  | or φ ψ ihφ ihψ =>
      intro p
      cases p
      · rw [dnfAux, DNF.holds_cross, ihφ, ihψ]
        simp only [Bool.false_eq_true, if_false, BForm.holds]; tauto
      · rw [dnfAux, DNF.holds_append, ihφ, ihψ]
        simp [BForm.holds]

/-- **`ToDNF` is correct** — what used to be `Ttc.TtcProb`'s `isDNF` field. -/
theorem toDNF_isDNFOf (φ : BForm A) : IsDNFOf (toDNF φ) φ := by
  intro v
  rw [toDNF]
  simpa using holds_dnfAux v φ true

/-! ## Positivity -/

/-- On a positive formula the converter never emits a negative literal — at
polarity `true`. (At polarity `false` it must: a DNF of `¬φ` needs them.) -/
theorem isPositive_dnfAux :
    ∀ (φ : BForm A), φ.IsPositive → DNF.IsPositive (dnfAux φ true) := by
  intro φ
  induction φ with
  | tt =>
      intro _ c hc
      rw [dnfAux, List.mem_singleton] at hc
      subst hc
      intro l hl
      exact absurd hl (List.not_mem_nil)
  | atom a =>
      intro _ c hc
      rw [dnfAux, List.mem_singleton] at hc
      subst hc
      intro l hl
      rw [List.mem_singleton] at hl
      subst hl
      rfl
  | neg φ _ => intro h; exact absurd h id
  | and φ ψ ihφ ihψ =>
      rintro ⟨hφ, hψ⟩ c hc
      rw [dnfAux, DNF.cross, List.mem_flatMap] at hc
      obtain ⟨d, hd, hc⟩ := hc
      rw [List.mem_map] at hc
      obtain ⟨e, he, rfl⟩ := hc
      intro l hl
      rcases List.mem_append.1 hl with h | h
      exacts [ihφ hφ d hd l h, ihψ hψ e he l h]
  | or φ ψ ihφ ihψ =>
      rintro ⟨hφ, hψ⟩ c hc
      rw [dnfAux] at hc
      rcases List.mem_append.1 hc with h | h
      exacts [ihφ hφ c h, ihψ hψ c h]

/-- **A positive formula yields a positive DNF** — what used to be
`Ttc.TtcProb`'s `isPositive` field, now a consequence of a condition on the input
formula. -/
theorem toDNF_isPositive {φ : BForm A} (h : φ.IsPositive) :
    DNF.IsPositive (toDNF φ) :=
  isPositive_dnfAux φ h

/-! ## Conjunctions of atoms

The shape the non-vacuity witness needs: a conjunction of positive atoms converts
to the single cube holding exactly those atoms. `BForm.tt` is what lets such a
conjunction be written without a tautology seed, and hence stay positive.

`Ttc.conj` itself is defined in `Model/Prelude`, because `Ttc.cubeForm` (lines A3
and A6 of `Model/Pseudocode`) folds it and so it is part of the algorithm's own
vocabulary; everything proved *about* it stays here.
-/

/-- **`ToDNF` of a conjunction of atoms is the one cube holding them.** -/
theorem toDNF_conj (L : List A) :
    toDNF (conj L) = [L.map fun a => ⟨a, true⟩] := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      show (dnfAux (.atom a) true).cross (toDNF (conj L)) = _
      rw [ih]
      rfl

/-- A conjunction of atoms is positive. -/
theorem isPositive_conj (L : List A) : (conj L).IsPositive := by
  induction L with
  | nil => exact trivial
  | cons a L ih => exact ⟨trivial, ih⟩

/-- A conjunction of atoms holds exactly when all of them do. -/
theorem holds_conj (v : A → Prop) (L : List A) :
    (conj L).holds v ↔ ∀ a ∈ L, v a := by
  induction L with
  | nil => simp [conj, BForm.holds]
  | cons a L ih =>
      show (v a ∧ (conj L).holds v) ↔ _
      rw [ih]
      constructor
      · rintro ⟨h, hL⟩ b hb
        rcases List.mem_cons.1 hb with rfl | hb
        exacts [h, hL b hb]
      · intro h
        exact ⟨h a List.mem_cons_self, fun b hb => h b (List.mem_cons_of_mem _ hb)⟩

end Ttc
