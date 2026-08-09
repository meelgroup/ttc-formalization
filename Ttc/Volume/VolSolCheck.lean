/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Model.Prelude
import Ttc.Lattice.Decomposition
import Ttc.TtcProb
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# `Volume/VolSolCheck`: is `Ttc.volSol` the volume of the right set?

The capstone (`Ttc.TtcProb.volume_estimate`) bounds the algorithm's output against
`Ttc.volSol T.M T.φ`. This module is the **audit surface for that one symbol**: it
answers, without reference to any other part of the development, the two questions
a sceptical reader asks.

## 1. What set, and what measure?

`Ttc.volSol M φ` unfolds to `(MeasureTheory.volume (Ttc.sol M φ)).toReal`, and
`Ttc.sol M φ` unfolds to `{x | φ.holds (fun a => x ∈ M a)}`. Both are **`rfl`**:
`Ttc.VolSolCheck.volSol_eq_toReal_volume_setOf` records that fact, and it is worth
exactly what a `rfl` is worth. The measure is Mathlib's `MeasureTheory.volume` on
`EuclideanSpace ℝ (Fin n)` — no bespoke measure is defined anywhere.

The non-trivial cross-check is therefore of the *semantics*, not of the plumbing:
`Ttc.BForm.holds` is a `Prop`-valued recursion, and nothing forces it to be the
usual truth tables. `Ttc.VolSolCheck.evalBool` re-implements the semantics as an
independent `Bool`-valued evaluator (whose truth tables a reader checks by eye),
and

* `Ttc.VolSolCheck.sol_eq_evalBool` — `Sol(F)` is the set on which that evaluator
  returns `true`;
* `Ttc.VolSolCheck.volSol_eq_lra` — for the LRA instantiation
  (`M = fun a => (atoms a).halfspace`, which is what `Ttc.TtcProb.M_eq` forces),
  `volSol` is the Lebesgue measure of an explicitly written set of points of
  `EuclideanSpace ℝ (Fin n)`, described using only `∑ i, coeff i * x i ≤ bound`,
  `Bool` connectives, and `MeasureTheory.volume`. That statement mentions no `Ttc`
  definition other than `BForm` itself.

The DNF decomposition `⋃ c ∈ D, region M c = sol M φ` is **already proved**
elsewhere (`Ttc.sol_eq_iUnion_region`, and for the bundle
`Ttc.TtcProb.sol_eq_union` in `Ttc/Capstone.lean`); it is not restated here.

## 2. Can `volSol` be junk?

`ENNReal.toReal ⊤ = 0`, so if `Sol(F)` had infinite volume the capstone would read
"the output is within `(1±ε)` of `0`" — true and vacuous. This is a real hazard:
`Ttc.VolSolCheck.volSol_tt_eq_zero` exhibits it, `volSol M .tt = 0` for every
interpretation `M` in dimension `n ≥ 1`, even though `Sol(⊤) = ℝⁿ`.

What rules it out is `Ttc.TtcProb.volume_ne_top`, which asserts finiteness of each
`region M c` **separately**, not of `sol M φ`. That it suffices is
`Ttc.VolSolCheck.volume_sol_ne_top`: a DNF is a `List`, hence finite, and measures
are countably subadditive (no measurability needed). The consequence worth quoting
is `Ttc.VolSolCheck.ofReal_volSol`: under that hypothesis `volSol` loses no
information, `ENNReal.ofReal (volSol M φ) = volume (sol M φ)`.

## 3. Measurability

`volSol` is defined with the outer measure, so measurability is not needed for it
to be well defined — but it is needed for `Sol(F)` to be a genuine measurable set
rather than an outer-measure value. `Ttc.VolSolCheck.measurableSet_sol_lra` proves
it unconditionally in the LRA fragment: every atom denotes a closed half-space, and
the Boolean connectives preserve measurability.

## Provenance note

Everything up to and including `volSol_nonneg` depends only on
`Ttc.Model.Prelude` and `Ttc.Lattice.Decomposition` — the audit of the *symbol*
does not need the bundle. The final section (`Ttc.TtcProb.volume_sol_ne_top`,
`Ttc.TtcProb.ofReal_volSol`) is the only part that uses
`Ttc.Model.ProblemSetting`, and it does so only to apply the general lemmas to
`Ttc.TtcProb`'s `isDNF` and `volume_ne_top` fields.
-/

namespace Ttc.VolSolCheck

open MeasureTheory Set

variable {A X : Type*} {n : ℕ}

/-! ## An independent, `Bool`-valued semantics for `Ttc.BForm`

`Ttc.BForm.holds` is `Prop`-valued and defined by recursion; a reader who wants to
know that it *is* propositional logic has to trust that recursion. `evalBool` is a
second, syntactically independent implementation whose clauses are the ordinary
`Bool` truth tables, and `holds_iff_evalBool` says the two agree.
-/

/-- The truth value of a `Ttc.BForm` under a `Bool`-valued assignment, by the
ordinary truth tables. Independent of `Ttc.BForm.holds`. -/
def evalBool (v : A → Bool) : BForm A → Bool
  | .tt => true
  | .atom a => v a
  | .neg φ => !(evalBool v φ)
  | .and φ ψ => evalBool v φ && evalBool v ψ
  | .or φ ψ => evalBool v φ || evalBool v ψ

@[simp] theorem evalBool_tt (v : A → Bool) : evalBool v (.tt : BForm A) = true := rfl
@[simp] theorem evalBool_atom (v : A → Bool) (a : A) : evalBool v (.atom a) = v a := rfl
@[simp] theorem evalBool_neg (v : A → Bool) (φ : BForm A) :
    evalBool v φ.neg = !(evalBool v φ) := rfl
@[simp] theorem evalBool_and (v : A → Bool) (φ ψ : BForm A) :
    evalBool v (φ.and ψ) = (evalBool v φ && evalBool v ψ) := rfl
@[simp] theorem evalBool_or (v : A → Bool) (φ ψ : BForm A) :
    evalBool v (φ.or ψ) = (evalBool v φ || evalBool v ψ) := rfl

/-- **The two semantics agree.** `Ttc.BForm.holds` really is propositional
satisfaction: it matches the `Bool` truth tables of `evalBool`. -/
theorem holds_iff_evalBool (v : A → Bool) (φ : BForm A) :
    φ.holds (fun a => v a = true) ↔ evalBool v φ = true := by
  induction φ with
  | tt => simp [BForm.holds]
  | atom a => simp [BForm.holds]
  | neg φ ih => simp [BForm.holds, ih]
  | and φ ψ ihφ ihψ => simp [BForm.holds, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp [BForm.holds, ihφ, ihψ]

/-! ## `Sol(F)` described through the independent semantics -/

/-- **`Sol(F)` is the true-set of the independent evaluator.** For any `Bool`-valued
indicator `v` of the atoms (`v x a = true ↔ x ∈ M a`), `Ttc.sol M φ` is exactly the
set of points at which `evalBool` returns `true`. No `Ttc` machinery beyond
`Ttc.BForm` appears on the right. -/
theorem sol_eq_evalBool (M : A → Set X) (φ : BForm A) (v : X → A → Bool)
    (hv : ∀ x a, v x a = true ↔ x ∈ M a) :
    sol M φ = {x : X | evalBool (v x) φ = true} := by
  ext x
  rw [mem_sol_iff, mem_setOf_eq, ← holds_iff_evalBool (v x) φ]
  have hfun : induced M x = fun a => v x a = true := by
    funext a; exact propext (hv x a).symm
  rw [hfun]

/-- **The LRA instantiation, written out.** With atoms interpreted as the closed
half-spaces they denote — which is what `Ttc.TtcProb.M_eq` forces — `Sol(F)` is the
set of `x : EuclideanSpace ℝ (Fin n)` at which the Boolean formula, evaluated with
each atom `a` sent to the truth value of `∑ i, (atoms a).coeff i * x i ≤ (atoms a).bound`,
comes out `true`. -/
theorem sol_eq_lra (atoms : A → LinAtom n) (φ : BForm A) :
    sol (fun a => (atoms a).halfspace) φ
      = {x : Space n |
          evalBool (fun a => decide (∑ i, (atoms a).coeff i * x i ≤ (atoms a).bound)) φ = true} :=
  sol_eq_evalBool _ φ _ (by intro x a; simp [LinAtom.halfspace])

/-! ## `volSol` itself

The first statement is `rfl` — `Ttc.volSol` is *literally* `toReal ∘ volume ∘ sol`
and `Ttc.sol` is *literally* that set-builder. It is recorded because a reader is
entitled to see it, not because it carries information. The second statement is the
one with content: it routes the set through `evalBool`.
-/

/-- **`volSol` is `MeasureTheory.volume`, `toReal`'d, of the naive solution set.**
This is `rfl`: `Ttc.volSol` and `Ttc.sol` are definitionally this. Its value is that
it pins the *measure* — Mathlib's `MeasureTheory.volume` on `EuclideanSpace ℝ (Fin n)`
— and shows no intermediate definition (`region`, `toDNF`, a bespoke measure) is
interposed. -/
theorem volSol_eq_toReal_volume_setOf (M : A → Set (Space n)) (φ : BForm A) :
    volSol M φ = (volume {x : Space n | φ.holds fun a => x ∈ M a}).toReal := rfl

/-- **The cross-check with content.** In the LRA fragment, `volSol` is the Lebesgue
measure of a set of points of `EuclideanSpace ℝ (Fin n)` written entirely in terms
of real inequalities `∑ i, coeff i * x i ≤ bound` combined by `Bool` connectives.
Nothing of `Ttc` other than the syntax type `BForm` occurs in the statement. -/
theorem volSol_eq_lra (atoms : A → LinAtom n) (φ : BForm A) :
    volSol (fun a => (atoms a).halfspace) φ
      = (volume {x : Space n |
          evalBool (fun a => decide (∑ i, (atoms a).coeff i * x i ≤ (atoms a).bound)) φ
            = true}).toReal := by
  rw [volSol, sol_eq_lra]

/-! ## Measurability -/

@[simp] theorem sol_tt (M : A → Set X) : sol M (.tt : BForm A) = univ := rfl
@[simp] theorem sol_atom (M : A → Set X) (a : A) : sol M (.atom a) = M a := rfl
@[simp] theorem sol_neg (M : A → Set X) (φ : BForm A) : sol M φ.neg = (sol M φ)ᶜ := rfl
@[simp] theorem sol_and (M : A → Set X) (φ ψ : BForm A) :
    sol M (φ.and ψ) = sol M φ ∩ sol M ψ := rfl
@[simp] theorem sol_or (M : A → Set X) (φ ψ : BForm A) :
    sol M (φ.or ψ) = sol M φ ∪ sol M ψ := rfl

/-- **`Sol(F)` is measurable whenever the atoms are.** By induction on the formula:
the connectives are complement, intersection and union. -/
theorem measurableSet_sol [MeasurableSpace X] {M : A → Set X}
    (hM : ∀ a, MeasurableSet (M a)) (φ : BForm A) : MeasurableSet (sol M φ) := by
  induction φ with
  | tt => simp
  | atom a => simpa using hM a
  | neg φ ih => simpa using ih.compl
  | and φ ψ ihφ ihψ => simpa using ihφ.inter ihψ
  | or φ ψ ihφ ihψ => simpa using ihφ.union ihψ

/-- A linear atom's half-space is closed. -/
theorem isClosed_halfspace (a : LinAtom n) : IsClosed a.halfspace := by
  have hc : Continuous fun x : Space n => ∑ i, a.coeff i * x i := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact continuous_const.mul ((EuclideanSpace.proj i).continuous)
  exact isClosed_le hc continuous_const

/-- A linear atom's half-space is measurable. -/
theorem measurableSet_halfspace (a : LinAtom n) : MeasurableSet a.halfspace :=
  (isClosed_halfspace a).measurableSet

/-- **`Sol(F)` is measurable in the LRA fragment, unconditionally.** So the
`MeasureTheory.volume` in `Ttc.volSol` is the measure of an honest measurable set,
not merely an outer-measure value. -/
theorem measurableSet_sol_lra (atoms : A → LinAtom n) (φ : BForm A) :
    MeasurableSet (sol (fun a => (atoms a).halfspace) φ) :=
  measurableSet_sol (fun a => measurableSet_halfspace (atoms a)) φ

/-! ## Is `volSol` junk? The `⊤` question

`ENNReal.toReal ⊤ = 0`. An unbounded solution set therefore makes `volSol = 0`
silently, and the capstone would say "the algorithm returns approximately `0`".
-/

/-- **The hazard, stated.** If `Sol(F)` has infinite volume then `volSol` is `0`. -/
theorem volSol_eq_zero_of_volume_eq_top {M : A → Set (Space n)} {φ : BForm A}
    (h : volume (sol M φ) = ⊤) : volSol M φ = 0 := by
  rw [volSol, h, ENNReal.toReal_top]

/-- **The hazard is real, not hypothetical.** In dimension `n ≥ 1`, the tautology
`⊤` has `Sol(⊤) = ℝⁿ`, and `volSol M .tt = 0` — a formula whose solution set is all
of space is assigned volume zero. Any reading of the capstone must therefore be
guarded by a finiteness hypothesis; see `volume_sol_ne_top`. -/
theorem volSol_tt_eq_zero (hn : 1 ≤ n) (M : A → Set (Space n)) :
    volSol M (.tt : BForm A) = 0 := by
  refine volSol_eq_zero_of_volume_eq_top ?_
  rw [sol_tt]
  have hmp := PiLp.volume_preserving_ofLp (ι := Fin n)
  have hu : volume (univ : Set (Space n)) = volume (univ : Set (Fin n → ℝ)) := by
    rw [← hmp.map_eq, Measure.map_apply hmp.measurable MeasurableSet.univ, preimage_univ]
  have hpi : (univ : Set (Fin n → ℝ)) = Set.pi univ fun _ => (univ : Set ℝ) :=
    (Set.pi_univ _).symm
  rw [hu, hpi, volume_pi_pi]
  simp only [Real.volume_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact ENNReal.top_pow (by omega)

/-! ### What rules the hazard out

`Ttc.TtcProb.volume_ne_top` asserts `volume (region M c) ≠ ⊤` for each cube `c` of
the DNF **separately**; it says nothing directly about `sol M φ`. The following
shows it is enough. Note that no measurability is required: measures are countably
subadditive on arbitrary sets, and a `Ttc.DNF` is a `List`, hence finite.
-/

/-- **`Sol(F)` has finite volume.** Exactly the two `Ttc.TtcProb` fields `isDNF` and
`volume_ne_top`, discharging the `⊤` hazard for the capstone: a finite union of
finite-volume sets has finite volume. -/
theorem volume_sol_ne_top {M : A → Set (Space n)} {φ : BForm A} {D : DNF A}
    (hD : IsDNFOf D φ) (hfin : ∀ c ∈ D, volume (region M c) ≠ ⊤) :
    volume (sol M φ) ≠ ⊤ := by
  rw [← sol_eq_iUnion_region hD]
  exact measure_biUnion_ne_top (List.finite_toSet D) hfin

/-- **Under that hypothesis `volSol` loses no information.** `ENNReal.ofReal` sends
it back to the measure it came from, so `volSol M φ = 0` really does mean
`Sol(F)` is null — never the `toReal ⊤ = 0` artefact. -/
theorem ofReal_volSol {M : A → Set (Space n)} {φ : BForm A} {D : DNF A}
    (hD : IsDNFOf D φ) (hfin : ∀ c ∈ D, volume (region M c) ≠ ⊤) :
    ENNReal.ofReal (volSol M φ) = volume (sol M φ) :=
  ENNReal.ofReal_toReal (volume_sol_ne_top hD hfin)

/-- `volSol M φ = 0` iff `Sol(F)` is Lebesgue-null, given finiteness. -/
theorem volSol_eq_zero_iff {M : A → Set (Space n)} {φ : BForm A} {D : DNF A}
    (hD : IsDNFOf D φ) (hfin : ∀ c ∈ D, volume (region M c) ≠ ⊤) :
    volSol M φ = 0 ↔ volume (sol M φ) = 0 := by
  rw [volSol, ENNReal.toReal_eq_zero_iff]
  simp [volume_sol_ne_top hD hfin]

/-- `volSol` is nonnegative. -/
theorem volSol_nonneg (M : A → Set (Space n)) (φ : BForm A) : 0 ≤ volSol M φ :=
  ENNReal.toReal_nonneg

end Ttc.VolSolCheck

/-! ## The capstone is not vacuous by `toReal ⊤ = 0`

`Ttc.TtcProb.volume_ne_top` is stated per-cube. These two corollaries close the
last step: they apply `Ttc.VolSolCheck.volume_sol_ne_top` to the bundle's own
fields, so `Ttc.volSol T.M T.φ` — the quantity `Ttc.TtcProb.volume_estimate`
bounds — is the `toReal` of a *finite* measure, never the `⊤` artefact. Without
this, `volume_estimate` would have been consistent with "the algorithm returns
approximately `0`" for every unbounded input formula.
-/

namespace Ttc

open MeasureTheory

/-- **`Sol(F)` has finite volume for every `Ttc.TtcProb`.** The per-cube field
`Ttc.TtcProb.volume_ne_top` does cover the set the capstone is about. -/
theorem TtcProb.volume_sol_ne_top {A : Type*} {n : ℕ} (T : TtcProb A n) :
    volume (sol T.M T.φ) ≠ ⊤ :=
  VolSolCheck.volume_sol_ne_top T.isDNF fun c hc => T.volume_ne_top ⟨c, hc⟩

/-- **`Ttc.volSol T.M T.φ` is a faithful real.** `ENNReal.ofReal` recovers the
measure, so `Ttc.TtcProb.volume_estimate`'s right-hand side is the genuine
Lebesgue volume of `Sol(F)` and not `ENNReal.toReal ⊤ = 0`. -/
theorem TtcProb.ofReal_volSol {A : Type*} {n : ℕ} (T : TtcProb A n) :
    ENNReal.ofReal (volSol T.M T.φ) = volume (sol T.M T.φ) :=
  VolSolCheck.ofReal_volSol T.isDNF fun c hc => T.volume_ne_top ⟨c, hc⟩

end Ttc

section AxiomCheck

open Ttc Ttc.VolSolCheck

#print axioms holds_iff_evalBool
#print axioms sol_eq_evalBool
#print axioms sol_eq_lra
#print axioms volSol_eq_toReal_volume_setOf
#print axioms volSol_eq_lra
#print axioms measurableSet_sol
#print axioms measurableSet_sol_lra
#print axioms volSol_tt_eq_zero
#print axioms volume_sol_ne_top
#print axioms ofReal_volSol
#print axioms volSol_eq_zero_iff
#print axioms Ttc.TtcProb.volume_sol_ne_top
#print axioms Ttc.TtcProb.ofReal_volSol

end AxiomCheck
