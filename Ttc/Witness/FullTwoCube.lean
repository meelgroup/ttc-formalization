/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Model.Theorem
import Ttc.Exec.EnvelopeFinite
import Ttc.Witness.Inputs

/-!
# `Witness/FullTwoCube`: `Ttc.ttc_volume` is not vacuous

`Ttc.ttc_volume` (`Model/Theorem`) — the repository's one headline — is a `∀` under ten
binders

```
A n atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos
```

and a `∀` whose hypotheses nothing satisfies is worth nothing (`CLAUDE.md` §11).  This file
exhibits data satisfying all of them, at **every** `n ≥ 21` and **every** `(ε, δ) ∈ (0,1]²`,
and then checks the two ways the conclusion could still say nothing.

## The data

The **two-cube** instance of `Ttc/Witness/TwoCube.lean`: the pair of disjoint axis-aligned
boxes `[0,c]ⁿ` and `[lo, lo+c]ⁿ` with side `c = Ttc.TwoCube.sideT = max 1 Thresh` and
`lo > c` a multiple of the lattice spacing.  The shape binders are lemmas that file already
proves, used unchanged:

| binder | discharged by |
| --- | --- |
| `atoms` | `Ttc.TwoCube.atomsT` |
| `φ` | `Ttc.TwoCube.twoForm` |
| `hφ` | `Ttc.TwoCube.twoForm_isPositive` |
| `hpos` | `Ttc.TwoCube.twoVolPos`, proved here |

`Ttc.atomSet (Ttc.TwoCube.atomsT …) = Ttc.TwoCube.MTT …` by `rfl`, which is why the
applications below need no rewriting.  Nothing is supplied for the inscribed ball, for
full-dimensionality, for nondegenerate facets or for boundedness of `Sol(F)`: the headline
prunes and cleans the formula itself, constructs the ball (`Ttc.autoCen`, `Ttc.autoGamma`)
and dilates by `Ttc.runScale`, dividing the estimate back down.

`hn : 21 ≤ n` is the one binder the two-cube data does not *produce* — it is a constraint on
the dimension, met by taking `n ≥ 21`, and `Ttc.TwoCube.ttc_volume_two_cube_at` pins it at
`n = 21` so that a concrete instance exists rather than a schema.

## The two ways the conclusion could still be empty, and why it is not

1. **The accuracy conjunct** reads `1 - δ ≤ Pr[…]`.  A probability is at most `1`, so this
   is a real constraint exactly when `1 - δ > 0`, i.e. `δ < 1`.  At the pinned `δ = 9/10` it
   demands probability at least `1/10`, and `Ttc.TwoCube.ttc_volume_two_cube_at` carries that
   numeral in its statement.
2. **The cost conjunct** reads `∫⁻ r, r.2 ≤ B` in `ℝ≥0∞`, where *everything* is `≤ ⊤`.
   `Ttc.ttc_volume_bound_ne_top` proves the bound finite — but it now needs a `B` bounding
   the loop's charges in expectation, which this file cannot supply.  See the caveat on
   `Ttc.TwoCube.ttc_volume_two_cube`.

## Cost caveat

**Not runnable, and not polynomial.**  Until 2026-08-19 the sampler branch below dimension
1100 was the lazy ball walk, whose certified transition bound carries `4 ^ n` and a
`(radius ratio) ^ (4 n)`.  The spherical-cap estimate now holds from `n ≥ 21`, so the run
witnessed here takes the hit-and-run branch and its **per-endpoint** bound is polynomial — at
a constant of `2 ^ 66 · n² · R²/r²`.  The endpoint **count** is a separate matter: it is the
dilated cube volume (`Ttc.polyGoodRateCap`), exponential in `n` through the
body-to-inscribed-ball volume ratio even after the 2026-08-20 `n`-th root in
`Ttc.scaleFactor`.  What this file establishes is that the headline *applies* to something,
not that running it at `n = 21` is feasible.
-/

namespace Ttc

namespace TwoCube

open MeasureTheory Set Pointwise
open scoped ENNReal Classical
open Ttc.Monadic

/-! ## `hpos`: the two-cube body has positive volume -/

/-- **Each of the two regions is full-dimensional.**  Each is an axis-aligned box of side
`Ttc.TwoCube.sideT > 0`, and `Ttc/Witness/TwoCube.lean` already exhibits an open ball of
radius `Ttc.TwoCube.gamT > 0` inside it (`Ttc.TwoCube.ball_subset_two_d`).  An open subset of
a set lies in its interior, and a ball of positive radius is nonempty, so the interior is
nonempty.  No box geometry is recomputed.

This is not a binder of the headline — pruning makes it true rather than assuming it — but it
is what `Ttc.volSol_pos_of_interior` consumes to give the binder that *is* there,
`Ttc.TwoCube.twoVolPos`. -/
theorem interior_region_nonempty_two_d (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ i : {c : Cube (A2 n) // c ∈ Ttc.toDNFd (twoForm n)},
      (interior (Ttc.region (Ttc.atomSet (atomsT n hn ε δ hε0 hε1)) i.val)).Nonempty := by
  intro i
  have hsub : Metric.ball (cenD n hn ε δ hε0 hε1 (Ttc.toDNFd (twoForm n)) i)
      (gamT n hn ε δ hε0 hε1)
      ⊆ interior (Ttc.region (MTT n hn ε δ hε0 hε1) i.val) :=
    interior_maximal (ball_subset_two_d n hn ε δ hε0 hε1 i) Metric.isOpen_ball
  exact (Metric.nonempty_ball.2 (gamT_pos n hn ε δ hε0 hε1)).mono hsub

/-- **`hpos` at the two-cube witness**: the body has strictly positive volume.  One
application of `Ttc.volSol_pos_of_interior` to the full-dimensionality above and the
boundedness `Ttc.TwoCube.isBounded_sol_T`; no volume is computed. -/
theorem twoVolPos (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    0 < volSol (Ttc.atomSet (atomsT n hn ε δ hε0 hε1)) (twoForm n) :=
  volSol_pos_of_interior (atomsT n hn ε δ hε0 hε1) twoForm_isPositive
    (isBounded_sol_T n hn ε δ hε0 hε1) (interior_region_nonempty_two_d n hn ε δ hε0 hε1)

/-! ## `Ttc.TtcInputs` is inhabited -/

/-- **The two-cube data satisfies `Ttc.TtcInputs`** — the side condition `Ttc.ttc` is defined
under, so `Ttc.ttc` is the constructed law here and not its junk value. -/
theorem ttcInputs_two_cube (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    Ttc.TtcInputs (atomsT n hn ε δ hε0 hε1) (twoForm n) ε :=
  ⟨hε0, hε1, hn, twoForm_isPositive, twoVolPos n hn ε δ hε0 hε1⟩

/-! ## The witness -/

/-- **`Ttc.ttc_accuracy` on a DNF with two cubes**, at every `n ≥ 21` and every
`(ε, δ) ∈ (0,1]²`.

Both binders that are about the *formula* are met by the two-cube data; the rest are the
numeric ranges the headline is stated over.  Nothing is weakened: this is
`Ttc.ttc_accuracy` itself, applied.

⚠ **The cost conjunct has no witness here yet, and that is a real gap.**  Since 2026-08-20
`Ttc.ttc_volume`'s cost half carries a hypothesis `B` bounding the loop's own charges in
expectation, and this file has no way to produce one — so applying `Ttc.ttc_volume` at the
two-cube data would need a `B` that nothing yet supplies.  The witness returns when
`Cthin`/`Cpass` are discharged and the hypothesis comes off; until then only accuracy is
witnessed, and saying so is better than instantiating `B := ⊤`, which would satisfy the
binder and certify nothing (`CLAUDE.md` §11). -/
theorem ttc_volume_two_cube (n : ℕ) (hn : 21 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    let hn1 : 1 ≤ n := le_trans (by norm_num) hn
    let atoms := atomsT n hn1 ε δ hε0 hε1
    1 - δ ≤ Pr[r ← Ttc.ttc atoms (twoForm n) ε δ;
      r.1 ∈ relErr ε (volSol (Ttc.atomSet atoms) (twoForm n))] :=
  Ttc.ttc_accuracy _ (twoForm n) ε δ hε0 hε1 hδ0 hδ1 hn twoForm_isPositive
    (twoVolPos n (le_trans (by norm_num) hn) ε δ hε0 hε1)

/-- **The accuracy conjunct at a numeral, with the numeral proved positive in the
statement.**

At `n = 21`, `ε = 1/3`, `δ = 9/10` the headline asserts that the estimate lands within a
factor `1 ± 1/3` of `Vol(F)` with probability at least `1/10`, and `0 < 1/10` is part of what
is stated — so this is not the empty assertion `0 ≤ (…).toReal` that `ENNReal.toReal ⊤ = 0`
would otherwise permit. -/
theorem ttc_volume_two_cube_at :
    let hn1 : (1 : ℕ) ≤ 21 := by norm_num
    let hε0 : (0 : ℝ) < 1 / 3 := by norm_num
    let hε1 : (1 : ℝ) / 3 ≤ 1 := by norm_num
    let atoms := atomsT 21 hn1 (1 / 3) (9 / 10) hε0 hε1
    (0 : ℝ) < 1 / 10 ∧
    (1 : ℝ) / 10 ≤ Pr[r ← Ttc.ttc atoms (twoForm 21) (1 / 3) (9 / 10);
      r.1 ∈ relErr (1 / 3) (volSol (Ttc.atomSet atoms) (twoForm 21))] := by
  intro hn1 hε0 hε1 atoms
  exact ⟨by norm_num,
    le_trans (by norm_num)
      (ttc_volume_two_cube 21 (by norm_num) (1 / 3) (9 / 10) hε0 hε1
        (by norm_num) (by norm_num))⟩

#print axioms Ttc.TwoCube.twoVolPos
#print axioms Ttc.TwoCube.ttcInputs_two_cube
#print axioms Ttc.TwoCube.ttc_volume_two_cube
#print axioms Ttc.TwoCube.ttc_volume_two_cube_at

end TwoCube

end Ttc
