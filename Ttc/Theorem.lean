/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Internal.Lattice
import Ttc.Internal.Rounding
import Ttc.Internal.Poisson
import Ttc.Problem

/-!
# `thm:volumettc`: the accuracy guarantee of `TTC`

This module states and proves the paper's headline theorem:

> Given `F` and `ε, δ ∈ (0,1]`, `TTC` returns an estimate `est` of `Vol(F)` such
> that with probability at least `1 − δ`,
> `est ∈ [(1−ε)·Vol(F), (1+ε)·Vol(F)]`.

## Architecture (interface → instance → capstone)

`Ttc.TtcAnalysis` is the *abstract interface*: a bundle of the facts the
correctness proof consumes, namely

* the formula `φ`, its interpretation `M`, and a DNF representation `D`;
* the **normalised lattice count** `L = |Q ∩ 𝕃ⁿ| / 10^(ρ·n)`;
* **`lem:lattice`** at `η = ε/8`: `L` two-sidedly approximates
  `vol (Sol F)`;
* **`lem:numlattice`**: the streaming sketch's output `est`
  two-sidedly approximates `L` to within `ε/3`.

`Ttc.TtcAnalysis.volume_estimate` is the *abstract theorem*, proved in full from
those fields; the arithmetic core sits in `Ttc.lower_combine` / `Ttc.upper_combine`.

The capstone is **about the real object**: the two-sided bound is stated for
`(volume (Ttc.sol T.M T.φ)).toReal`, the Lebesgue volume of the solution set of
the actual SMT(LRA) formula, not of a surrogate. `Ttc.TtcAnalysis.sol_eq_union`
records that this set is exactly the union of the cubes' regions (`thm:decomposition`), so the
quantity the algorithm targets and the quantity the theorem bounds are the same
set.

## Proved versus assumed

Everything in this file is proved from the interface. Of the interface's fields:

* `thm:decomposition` is proved outright (`Ttc.sol_eq_iUnion_region`).
* `lem:lattice`'s *derivation* from `lem:nonconv` is proved (`Ttc.lattice_of_scaled`,
  `Ttc.ncard_inter_lattice_smul`, `Ttc.volume_smul_body`).
* `lem:nonconv`'s deductive skeleton and its geometric input are proved
  (`Ttc.nonconv_lower`, `Ttc.FacetSystem.volume_inflated_le_helper`, `claim:helper`).
* **`claim:cl`** (`claim:cl`, the Azuma bound on randomized rounding) and **`lem:numlattice`**
  (`lem:numlattice`, the Poisson/Chernoff analysis of the sketch) are *not*
  formalised; they enter as interface fields. See the README.

## Probability, `δ`, and scope

`Ttc.TtcAnalysis` fixes one run of the algorithm and asserts `lem:numlattice`'s conclusion
*deterministically*; the `1 − δ` failure probability of the paper is therefore
carried by the fields `sketch_lo`/`sketch_hi` being assumed to hold, rather than
being re-derived. Consequently what is proved here is: **on the event that
`lem:numlattice`'s guarantee holds, the output is an `(1±ε)`-approximation of the true
volume.** Combining that event with `Pr ≥ 1 − δ` is exactly `lem:numlattice`'s content and
is out of scope, as is the runtime claim (`thm:runtime`).
-/

namespace Ttc

open MeasureTheory Set

/-- The Lebesgue volume of the solution set of an SMT(LRA) formula, as a real
number. This is the paper's `Vol(F)`. -/
noncomputable def volSol {A : Type*} {n : ℕ} (M : A → Set (Space n)) (φ : BForm A) : ℝ :=
  (volume (sol M φ)).toReal

theorem volSol_nonneg {A : Type*} {n : ℕ} (M : A → Set (Space n)) (φ : BForm A) :
    0 ≤ volSol M φ := ENNReal.toReal_nonneg

/-- **The abstract interface for `thm:volumettc`.**

A bundle of the modelling facts the correctness argument consumes. `L` is the
normalised lattice count `|Q ∩ 𝕃ⁿ| / 10^(ρ·n)`; the two `lattice_*` fields are
`lem:lattice` at `η = ε/8`; the two `sketch_*` fields are `lem:numlattice`. -/
structure TtcAnalysis (A : Type*) (n : ℕ) where
  /-- The multiplicative accuracy parameter. -/
  ε : ℝ
  /-- `ε` is positive. -/
  hε0 : 0 < ε
  /-- `ε` is at most one, as required by `thm:volumettc`. -/
  hε1 : ε ≤ 1
  /-- The interpretation of atoms as sets of points (half-spaces, in the LRA case). -/
  M : A → Set (Space n)
  /-- The Boolean abstraction of the input formula. -/
  φ : BForm A
  /-- The DNF produced by circuit AllSAT. -/
  D : DNF A
  /-- `D` really is a DNF representation of `φ`. -/
  isDNF : IsDNFOf D φ
  /-- The normalised lattice count `|Q ∩ 𝕃ⁿ| / 10^(ρ·n)`. -/
  L : ℝ
  /-- A count is nonnegative. -/
  hL : 0 ≤ L
  /-- The estimate the algorithm outputs, `|X|/p`. -/
  est : ℝ
  /-- `lem:lattice`, lower half, at `η = ε/8`. -/
  lattice_lo : (1 - ε / 8) * L ≤ volSol M φ
  /-- `lem:lattice`, upper half, at `η = ε/8`. -/
  lattice_hi : volSol M φ ≤ (1 + ε / 8) * L
  /-- `lem:numlattice`, lower half. -/
  sketch_lo : (1 - ε / 3) * L ≤ est
  /-- `lem:numlattice`, upper half. -/
  sketch_hi : est ≤ (1 + ε / 3) * L

namespace TtcAnalysis

variable {A : Type*} {n : ℕ} (T : TtcAnalysis A n)

/-- **`thm:decomposition` inside the interface.** The set whose volume `thm:volumettc` bounds is
exactly the union of the polytopes the algorithm enumerates. -/
theorem sol_eq_union : ⋃ c ∈ T.D, region T.M c = sol T.M T.φ :=
  sol_eq_iUnion_region T.isDNF

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

/-- **`thm:volumettc`.** On the event that `lem:numlattice`'s guarantee holds,
`TTC`'s output is a relative `ε`-approximation of the Lebesgue volume of the
solution set of the input SMT(LRA) formula. -/
theorem volume_estimate :
    T.est ∈ Set.Icc ((1 - T.ε) * volSol T.M T.φ) ((1 + T.ε) * volSol T.M T.φ) :=
  ⟨T.le_est, T.est_le⟩

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

/-- `Ttc.TtcAnalysis` is inhabited: the single-atom formula with the ideal
instance. -/
theorem nonempty_ttcAnalysis {A : Type*} {n : ℕ} (a : A) : Nonempty (TtcAnalysis A n) :=
  ⟨TtcAnalysis.ideal (ε := 1) one_pos le_rfl (fun _ => ∅) (.atom a) [[⟨a, true⟩]]
    (by intro v; simp [DNF.holds, Cube.holds, Lit.holds, BForm.holds])⟩

end Ttc
