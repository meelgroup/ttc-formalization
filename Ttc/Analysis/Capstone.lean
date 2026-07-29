/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Model.Pseudocode

/-!
# The capstone: combining `lem:lattice` and `lem:numlattice`

The proof content behind `Model/Theorem`. Everything here is proved from the
fields of `Ttc.TtcAnalysis` (`Model/Prelude`) and nothing else.

The two halves are the paper's two chains:

* `(1−ε)·vol ≤ (1−ε)(1+ε/8)·L ≤ (1−ε/3)·L ≤ est`  (`Ttc.TtcAnalysis.le_est`)
* `est ≤ (1+ε/3)·L ≤ (1+ε)(1−ε/8)·L ≤ (1+ε)·vol`  (`Ttc.TtcAnalysis.est_le`)

so the `ε/8` of `lem:lattice` and the `ε/3` of `lem:numlattice` compose to the
`ε` of `thm:volumettc` with slack. `Model/Theorem` pairs them.

Also here: `Ttc.TtcAnalysis.ideal`, the non-vacuity witness — the *exact*
instance, with every error term zero. A capstone quantified over a structure is
worthless if the structure is uninhabited, so this is load-bearing; see the
README, and `Ttc.nonempty_ttcAnalysis` in `Model/Theorem`.
-/

namespace Ttc

open MeasureTheory Set

namespace TtcAnalysis

variable {A : Type*} {n : ℕ} (T : TtcAnalysis A n)

/-- **`thm:volumettc`, lower bound.** -/
theorem le_est : (1 - T.ε) * volSol T.M T.φ ≤ T.est := by
  have hv := T.lattice_hi
  have hL := T.hL
  have h0 := T.hε0
  have h1 := T.hε1
  -- `(1−ε)·vol ≤ (1−ε)(1+ε/8)·L ≤ (1−ε/3)·L ≤ est`
  have step1 : (1 - T.ε) * volSol T.M T.φ ≤ (1 - T.ε) * ((1 + T.ε / 8) * T.L) :=
    mul_le_mul_of_nonneg_left hv (by linarith)
  have harith : (1 - T.ε) * (1 + T.ε / 8) ≤ 1 - T.ε / 3 := by nlinarith
  have step2 : (1 - T.ε) * ((1 + T.ε / 8) * T.L) ≤ (1 - T.ε / 3) * T.L := by
    nlinarith [mul_le_mul_of_nonneg_right harith hL]
  linarith [T.sketch_lo]

/-- **`thm:volumettc`, upper bound.** -/
theorem est_le : T.est ≤ (1 + T.ε) * volSol T.M T.φ := by
  have hv := T.lattice_lo
  have hL := T.hL
  have h0 := T.hε0
  have h1 := T.hε1
  -- `est ≤ (1+ε/3)·L ≤ (1+ε)(1−ε/8)·L ≤ (1+ε)·vol`
  have harith : (1 + T.ε / 3) ≤ (1 + T.ε) * (1 - T.ε / 8) := by nlinarith
  have step1 : (1 + T.ε / 3) * T.L ≤ ((1 + T.ε) * (1 - T.ε / 8)) * T.L :=
    mul_le_mul_of_nonneg_right harith hL
  have step2 : ((1 + T.ε) * (1 - T.ε / 8)) * T.L ≤ (1 + T.ε) * volSol T.M T.φ := by
    have h := mul_le_mul_of_nonneg_left hv (by linarith : (0:ℝ) ≤ 1 + T.ε)
    linarith [h]
  linarith [T.sketch_hi]

end TtcAnalysis

/-! ## Non-vacuity

A capstone quantified over a structure is worthless if the structure is
uninhabited. The *ideal* instance — exact lattice count and exact estimate —
inhabits `TtcAnalysis` for **every** formula with a DNF representation and every
admissible `ε`, so the theorem is not vacuous.
-/

/-- **Non-vacuity of `Ttc.TtcAnalysis`.** For any formula, any DNF representation
of it, and any `ε ∈ (0,1]`, the ideal instance (`L = est = Vol(F)`, i.e. all error
terms zero) satisfies every field. -/
noncomputable def TtcAnalysis.ideal {A : Type*} {n : ℕ} {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (M : A → Set (Space n)) (φ : BForm A) (D : DNF A) (hD : IsDNFOf D φ) :
    TtcAnalysis A n where
  ε := ε
  hε0 := hε0
  hε1 := hε1
  M := M
  φ := φ
  D := D
  isDNF := hD
  L := volSol M φ
  hL := volSol_nonneg M φ
  est := volSol M φ
  lattice_lo := by nlinarith [volSol_nonneg M φ]
  lattice_hi := by nlinarith [volSol_nonneg M φ]
  sketch_lo := by nlinarith [volSol_nonneg M φ]
  sketch_hi := by nlinarith [volSol_nonneg M φ]

/-! ## The faithfulness bridge is satisfiable

`Ttc.TtcAnalysis.run_volume_estimate` (`Model/Theorem`) is a guarantee about
`Ttc.run` under the hypothesis `Ttc.TtcAnalysis.IsOutputOf`. If that hypothesis
were unsatisfiable the theorem would be vacuous, so we exhibit a witness: the
everywhere-false interpretation, whose solution set is empty and whose volume is
`0`, together with a degenerate run that outputs `0`.

This is a *satisfiability* witness only. It says the bridge is not self-
contradictory; it does not say the bridge holds of the real algorithm — that is
`lem:numlattice`, which is assumed. -/

/-- A degenerate oracle bundle: `Vol_ED` returns `1`, nothing is ever covered,
thinning is the identity, every Poisson draw is `0`, and `GenerateSamples`
returns `N` copies of the origin. It satisfies both constraints `Ttc.Oracles`
imposes. -/
def trivialOracles (n : ℕ) (ι : Type*) : Oracles n ι where
  vol := fun _ => 1
  covered := fun _ _ => false
  halve := id
  halve_card_le := fun _ => le_rfl
  pois := fun _ => 0
  gen := fun _ N => Multiset.replicate N 0
  gen_card := fun _ N => by simp

/-- A degenerate parameter block, to have some `Ttc.Params` to run at. -/
noncomputable def trivialParams : Params where
  ε := 1
  δ := 1
  n := 1
  m := 1
  r := 1
  hε0 := one_pos
  hε1 := le_rfl
  hn := le_rfl
  hm := le_rfl
  hr := le_rfl

/-- **The bridge is satisfiable.** With no fuel and the degenerate oracle bundle
`Ttc.run` outputs `0`, which is `Vol(F)` for the everywhere-false interpretation
— so the ideal instance at that formula really is the output of a run. -/
theorem exists_isOutputOf {A : Type*} {n : ℕ} (a : A) :
    ∃ (T : TtcAnalysis A n) (P : Params) (O : Oracles n (Cube A)) (fuel : ℕ),
      T.IsOutputOf P O fuel := by
  refine ⟨TtcAnalysis.ideal (ε := 1) one_pos le_rfl (fun _ => ∅) (.atom a) [[⟨a, true⟩]]
      (by intro v; simp [DNF.holds, Cube.holds, Lit.holds, BForm.holds]),
    trivialParams, trivialOracles n (Cube A), 0, ?_⟩
  show volSol (fun _ => (∅ : Set (Space n))) (.atom a)
      = run trivialParams (trivialOracles n (Cube A)) 0 [[⟨a, true⟩]]
  have hsol : sol (fun _ => (∅ : Set (Space n))) (.atom a) = ∅ := rfl
  simp [volSol, hsol, run, step, dropCovered, trivialOracles]

end Ttc
