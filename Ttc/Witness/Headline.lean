/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Model.Theorem
import Ttc.Witness.Inputs
import Ttc.Witness.TwoCubeVol

/-!
# `Witness/Headline`: `Ttc.ttc_volume_estimate` is not vacuous

`Ttc.ttc_volume_estimate` (`Model/Theorem`) is a `∀` over a formula, a centre map
and a radius, under seven side conditions.  A `∀` with unsatisfiable hypotheses is
vacuously true (`CLAUDE.md` §11), so the statement is worth nothing until
something satisfies them.

The witness is the two-cube instance of `Ttc/Witness/TwoCube.lean` — the pair of
disjoint boxes `[0,c]ⁿ` and `[lo, lo+c]ⁿ` — at every `(ε, δ) ∈ (0,1]²` and every
`n ≥ 1`.  The **machine-checked application** of the 17-binder theorem to that data
is `Ttc.TwoCube.ttc_volume_inputs_two_cube` (`Ttc/Witness/Inputs.lean`), which
discharges all seventeen hypotheses; this file records the numeric consequences.

**Why that is a witness for `Ttc.ttc_volume_estimate` too.**  The Model-layer
theorem *is* `Ttc.ttc_volume_inputs` — identical binder list, in the same order,
proof one application — restated through the definitional wrappers
`Ttc.runOracles`, `Ttc.ttcRunOutput`, `Ttc.runRates` and `Ttc.runPrec`.  So a set of
arguments satisfying the one satisfies the other by construction; there is no gap
between the two statements for a witness to fall into.  (Applying the Model-layer
name here directly is possible but requires rewriting `Ttc.inputParams` underneath
those wrappers, where the cube-index and lattice-index types depend on it — a
dependent rewrite that buys nothing.)

`Ttc.TwoCube.ttc_volume_estimate_two_cube_at` pins two structurally different
parameter pairs with the achieved bound proved **strictly positive inside the
statement**, so neither conclusion is the vacuous `0 ≤ (…).toReal`
(`ENNReal.toReal ⊤ = 0`).

**Cost.**  Exponential in `n`, and paid twice: hit-and-miss Monte Carlo at
`Θ(Rⁿ/(ε'²δ'))` samples per cube, `2^Θ(n)·log(M·Vol(P′)/ε′)` certified ball-walk
steps, and `Θ((c·10^ρ)ⁿ)` lattice points enumerated, for each of the two cubes.
-/

namespace Ttc

namespace TwoCube

open MeasureTheory Set

/-- **`Ttc.ttc_volume_estimate` on a DNF with two cubes**, at every
`(ε, δ) ∈ (0,1]²` and every `n ≥ 1`.

The accuracy half of `Ttc.TwoCube.ttc_volume_inputs_two_cube`, on the named
probability `Ttc.TwoCube.twoAccD`.  Every one of the seven side conditions is met by
the two-cube data there: `hφ` is
`Ttc.TwoCube.twoForm_isPositive`, `hbdd` is `Ttc.TwoCube.isBounded_sol_T`,
`hcoeff` and `ball_subset` are `Ttc.TwoCube.coeff_ne_zero_two_d` and
`Ttc.TwoCube.ball_subset_two_d`, the inscribed ball is the two distinct box centres
`Ttc.TwoCube.cenD` at the shared radius `Ttc.TwoCube.gamT`, and `big` is
`Ttc.TwoCube.big_two_d` — the regime condition holds here because the witness sizes
its boxes at `max 1 Thresh`, which is exactly what `Ttc.Box.big_not_derivable` shows
cannot be dispensed with.

`m = 2`, so the per-cube error composition, the union bound behind
`Ttc.Params.deltaPrime`, and a `∑ s` over the lattice points of two different
regions with two different centres are all exercised. -/
theorem ttc_volume_estimate_two_cube (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    1 - δ ≤ twoAccD n hn ε (4 * δ / 5) hε0 hε1 :=
  two_cube_inputs_acc_ge n hn ε δ hε0 hε1 hδ0 hδ1

/-- **The two-cube guarantee at two structurally different parameter pairs, with the
achieved bound a positive numeral.**

* `(ε, δ) = (1/3, 9/10)`: bound `1/10 > 0`, at a `δ ∈ (4/5, 1)` where the earlier
  budget `1 − δ − δ/4 = −1/8` certified nothing.
* `(ε, δ) = (1/2, 1/4)`: a different accuracy *and* confidence, hence different
  sides `Ttc.TwoCube.sideT`, precisions `Ttc.TwoCube.rhoT`, corners
  `Ttc.TwoCube.loT` and parameter blocks — two instances, not one instance twice.

Both bounds are proved strictly positive **in the statement**, so neither is the
vacuous `0 ≤ (…).toReal`. -/
theorem ttc_volume_estimate_two_cube_at (n : ℕ) (hn : 1 ≤ n)
    (hε₁ : (0 : ℝ) < 1/3) (hε₁' : (1/3 : ℝ) ≤ 1)
    (hε₂ : (0 : ℝ) < 1/2) (hε₂' : (1/2 : ℝ) ≤ 1) :
    ((0 : ℝ) < 1/10 ∧ (1/10 : ℝ) ≤ twoAccD n hn (1/3) (4 * (9/10) / 5) hε₁ hε₁'
      ∧ (4/5 : ℝ) < 9/10 ∧ (9/10 : ℝ) < 1)
    ∧ ((0 : ℝ) < 3/4 ∧ (3/4 : ℝ) ≤ twoAccD n hn (1/2) (4 * (1/4) / 5) hε₂ hε₂') := by
  refine ⟨⟨by norm_num, ?_, by norm_num, by norm_num⟩, ⟨by norm_num, ?_⟩⟩
  · have h := ttc_volume_estimate_two_cube n hn (1/3) (9/10) hε₁ hε₁'
      (by norm_num) (by norm_num)
    linarith
  · have h := ttc_volume_estimate_two_cube n hn (1/2) (1/4) hε₂ hε₂'
      (by norm_num) (by norm_num)
    linarith

/-- **The bound is a genuine number, not `ENNReal.toReal ⊤ = 0`.**  A strictly
positive lower bound on the `toReal` forces the measure itself to be nonzero and
finite. -/
theorem twoProbD_pos_ne_top_of_estimate (n : ℕ) (hn : 1 ≤ n)
    (hε0 : (0 : ℝ) < 1/3) (hε1 : (1/3 : ℝ) ≤ 1) :
    0 < twoProbD n hn (1/3) (4 * (9/10) / 5) hε0 hε1
      ∧ twoProbD n hn (1/3) (4 * (9/10) / 5) hε0 hε1 ≠ ⊤ := by
  have h := (ttc_volume_estimate_two_cube_at n hn hε0 hε1 (by norm_num) (by norm_num)).1.2.1
  have hpos : 0 < (twoProbD n hn (1/3) (4 * (9/10) / 5) hε0 hε1).toReal :=
    lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/10) h
  exact ⟨(ENNReal.toReal_pos_iff.1 hpos).1, (ENNReal.toReal_pos_iff.1 hpos).2.ne⟩

/-! ## The Model-layer theorem, applied

`Ttc.ttc_volume_estimate` carries `hvol : Thresh/4 ≤ Vol(F)` rather than the
sampler-level `big`, and the two-cube instance satisfies it
(`Ttc.TwoCube.two_cube_thresh_le_volSol_atomSet` — the witness sizes its boxes at
`max 1 Thresh` precisely so that it does).  So the Model-layer name can be applied
here directly, with no transport: `Ttc.Params.thresh` is a real number, not a type
index, so `Ttc.TwoCube.inputParams_eq` rewrites under it. -/

/-- **`Ttc.ttc_volume_estimate` itself, on the two-cube witness.**

All seven side conditions discharged, at every `(ε, δ) ∈ (0,1]²` and every `n ≥ 1`,
with the conclusion in the Model layer's own vocabulary (`Ttc.runRates`,
`Ttc.ttcRunOutput`).  The runtime half is the second conjunct of
`Ttc.TwoCube.ttc_volume_inputs_two_cube`. -/
theorem ttc_volume_estimate_two_cube_direct (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    1 - δ ≤
      (∫⁻ c, trajLaw (runRates (atomsT n hn ε (4 * δ / 5) hε0 hε1) (twoForm n) ε δ
            hε0 hε1 hn twoForm_isPositive (isBounded_sol_T n hn ε (4 * δ / 5) hε0 hε1)
            (cenD n hn ε (4 * δ / 5) hε0 hε1 (Ttc.toDNFd (twoForm n)))
            (gamT n hn ε (4 * δ / 5) hε0 hε1) c)
          {t | ttcRunOutput (atomsT n hn ε (4 * δ / 5) hε0 hε1) (twoForm n) ε δ
              hε0 hε1 hn twoForm_isPositive (isBounded_sol_T n hn ε (4 * δ / 5) hε0 hε1)
              (cenD n hn ε (4 * δ / 5) hε0 hε1 (Ttc.toDNFd (twoForm n)))
              (gamT n hn ε (4 * δ / 5) hε0 hε1) c t
            ∈ relErr ε (volSol (atomSet (atomsT n hn ε (4 * δ / 5) hε0 hε1)) (twoForm n))}
        ∂(MonteCarlo.coins n)).toReal := by
  have h0 : (0 : ℝ) < 4 * δ / 5 := by linarith
  have h1 : (4 : ℝ) * δ / 5 ≤ 1 := by linarith
  exact (ttc_volume_estimate (atomsT n hn ε (4 * δ / 5) hε0 hε1) (twoForm n) ε δ
    hε0 hε1 hδ0 hδ1 hn twoForm_isPositive
    (isBounded_sol_T n hn ε (4 * δ / 5) hε0 hε1)
    (coeff_ne_zero_two_d n hn ε (4 * δ / 5) hε0 hε1)
    (cenD n hn ε (4 * δ / 5) hε0 hε1 (Ttc.toDNFd (twoForm n)))
    (gamT n hn ε (4 * δ / 5) hε0 hε1) (gamT_pos n hn ε (4 * δ / 5) hε0 hε1)
    (ball_subset_two_d n hn ε (4 * δ / 5) hε0 hε1)
    (by
      rw [inputParams_eq n hn ε δ hε0 hε1]
      exact two_cube_thresh_le_volSol_atomSet n hn ε (4 * δ / 5) hε0 hε1 h0 h1)).1

end TwoCube

end Ttc

/-! ## Axiom profile -/

#print axioms Ttc.TwoCube.ttc_volume_estimate_two_cube
#print axioms Ttc.TwoCube.ttc_volume_estimate_two_cube_at
#print axioms Ttc.TwoCube.twoProbD_pos_ne_top_of_estimate
#print axioms Ttc.TwoCube.ttc_volume_estimate_two_cube_direct
