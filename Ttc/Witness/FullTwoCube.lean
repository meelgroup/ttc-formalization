/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Model.Theorem
import Ttc.Witness.Inputs

/-!
# `Witness/FullTwoCube`: `Ttc.ttc_volume_estimate` is not vacuous

`Ttc.ttc_volume_estimate` (`Model/Theorem.lean`) is a `∀` under **twelve**
hypotheses

```
atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hbdd hint
```

and a `∀` whose hypotheses nothing satisfies is worth nothing (`CLAUDE.md` §11).
This file exhibits data satisfying all twelve, at **every** `n ≥ 1` and **every**
`(ε, δ) ∈ (0,1]²`, and then pins the conclusion at two parameter numerals where the
achieved bound is proved **strictly positive inside the statement** — so neither
conclusion is the vacuous `0 ≤ (…).toReal` that `ENNReal.toReal ⊤ = 0` would
otherwise permit.

The data is the **two-cube** instance of `Ttc/Witness/TwoCube.lean`: the pair of
disjoint axis-aligned boxes `[0,c]ⁿ` and `[lo, lo+c]ⁿ` with side
`c = Ttc.TwoCube.sideT = max 1 Thresh` and `lo > c` a multiple of the lattice
spacing.  Eleven of the twelve arguments are lemmas that file (or
`Ttc/Witness/Inputs.lean`) already proves, used unchanged:

| binder | discharged by |
| --- | --- |
| `atoms` | `Ttc.TwoCube.atomsT` |
| `φ` | `Ttc.TwoCube.twoForm` |
| `hφ` | `Ttc.TwoCube.twoForm_isPositive` |
| `hbdd` | `Ttc.TwoCube.isBounded_sol_T` |
| `hint` | `Ttc.TwoCube.interior_region_nonempty_two_d`, new here |

(`Ttc.atomSet (Ttc.TwoCube.atomsT …) = Ttc.TwoCube.MTT …` by `rfl` —
`Ttc.TwoCube.atomSet_atomsT`.)  The former thirteenth binder `hcoeff` —
*no facet of the DNF has a zero normal* — is **no longer passed**: it was discharged
upstream by running the algorithm on the cleaned formula `Ttc.cleanForm atoms φ`
(`Ttc/Exec/CleanInput.lean`), so `Ttc.TwoCube.coeff_ne_zero_two_d` is no longer
needed here.

## Why `hint` holds: each region contains an open ball of positive radius

`hint` asks that every polytope of the decomposition be **full-dimensional**:

```
∀ i, (interior (region (atomSet atoms) i.val)).Nonempty
```

No box geometry is computed here.  `Ttc/Witness/TwoCube.lean` already proves
`Metric.ball (cenT …) (gamT …) ⊆ region (MTT …) i.val`
(`Ttc.TwoCube.ball_subset_two`, transported to the deduplicated cube list as
`Ttc.TwoCube.ball_subset_two_d`) with `gamT = sideT/2 > 0`
(`Ttc.TwoCube.gamT_pos`, `Ttc.TwoCube.sideT_pos`).  An **open** subset of a set is
contained in its interior (`interior_maximal` with `Metric.isOpen_ball`), and a ball
of positive radius is nonempty (`Metric.nonempty_ball`), so the interior is nonempty.
That is the whole proof.

## What the run is, and what it is not

The twelve-binder statement no longer takes the inscribed ball as data: the ball is
*constructed* (`Ttc.autoCen`, `Ttc.autoGamma`), and — see `Ttc/Exec/Rescaled.lean`'s
module docstring — the run is on the input **dilated** by `Ttc.runScale`, with the
estimate divided by `cⁿ`, which is how the volume hypothesis `hvol` is discharged
rather than assumed.  On top of that, the formula the algorithm is handed is the
**cleaned** one, `Ttc.cleanForm atoms φ` (`Ttc/Exec/CleanInput.lean`): every
occurrence of the formula in the conclusion — the constructed ball `Ttc.autoCen` /
`Ttc.autoGamma`, the dilation `Ttc.runScale`, the dilated atoms `Ttc.scaledAtoms`
and the boundedness proof `Ttc.scaledBdd` — is at `Ttc.cleanForm atoms φ`, and only
the accuracy *target* `Ttc.volSol` is at the original `φ` (the two solution sets are
equal, `Ttc.sol_cleanForm`).

So the probability bounded here, `Ttc.TwoCube.twoProbFull`, is the law of a run on
the *dilated* body of the *cleaned* formula under the *constructed* ball, and it is
**not** `Ttc.TwoCube.twoAccD` (`Ttc/Witness/Inputs.lean`), which is the undilated run
on the raw formula under the *supplied* ball `(cenD, gamT)`.  They are different runs
and no attempt is made here to relate them; nothing about `Ttc.cleanForm`,
`Ttc.runScale`, `Ttc.scaledAtoms`, `Ttc.autoCen` or `Ttc.autoGamma` is computed or
simplified.

`Ttc.TwoCube.twoProbFull` and its four helper `def`s (`gamFull`, `scaleFull`,
`atomsFull`, `cenFull`) are pure abbreviations for the terms
`Ttc.ttc_volume_estimate` puts in its own slots; none of them asserts anything, and
`Ttc.TwoCube.twoProbFull_def` writes the abbreviation out in full, by `rfl`, in
exactly the shape the main theorem's conclusion has.

## What is landed

| result | content |
| --- | --- |
| `Ttc.TwoCube.interior_region_nonempty_two_d` | `hint`: both regions are full-dimensional |
| `Ttc.TwoCube.twoProbFull_def` | the named probability **is** `Ttc.ttc_volume_estimate`'s integral, here |
| `Ttc.TwoCube.ttc_volume_estimate_two_cube_full` | `Ttc.ttc_volume_estimate` itself, at every `(ε, δ) ∈ (0,1]²` |
| `Ttc.TwoCube.ttc_volume_estimate_two_cube_full_at` | the same at `(1/3, 9/10)` and `(1/2, 1/4)`, bounds `1/10` and `3/4`, both proved positive |
| `Ttc.TwoCube.twoProbFull_pos_ne_top` | the bound is a real number, not `ENNReal.toReal ⊤ = 0` |

## Cost caveat

**Exponential in `n` on both oracle routes, paid twice, and now on a dilated body.**
The volume estimator is hit-and-miss Monte Carlo at `Θ(Rⁿ/(ε'²δ'))` samples, the ball
walk's certified step count is `2^Θ(n)·log(M·Vol(P′)/ε′)`, and the lattice
transcription enumerates `Ttc.latticeCount ≈ Θ((c·10^ρ)ⁿ)` points; with `m = 2` each
of those costs is paid **once per cube**.  On top of that, the dilation step of
`Ttc/Exec/Rescaled.lean` inflates the body by `Ttc.runScale ≥ 1` *before* the lattice
is enumerated, so the enumerated lattice is that of the dilated body — a further
`Ttc.runScale ^ n` factor in the point count.  What is established is unconditional
*correctness*; `thm:runtime` remains out of scope.
-/

namespace Ttc

namespace TwoCube

open MeasureTheory Set Pointwise

/-! ## `hint`: both regions are full-dimensional -/

/-- **`hint` at the two-cube witness.**  Each of the two regions is an axis-aligned
box of side `Ttc.TwoCube.sideT > 0`, and `Ttc/Witness/TwoCube.lean` already exhibits
an open ball of radius `Ttc.TwoCube.gamT > 0` inside it
(`Ttc.TwoCube.ball_subset_two_d`).  An open subset of a set lies in its interior, and
a ball of positive radius is nonempty, so the interior is nonempty.  No box geometry
is recomputed. -/
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

/-! ## The run, named

Pure abbreviations for the terms `Ttc.ttc_volume_estimate` computes from
`(atoms, φ, ε, δ)` on this witness — all of them at the **cleaned** formula
`Ttc.cleanForm (Ttc.TwoCube.atomsT …) (Ttc.TwoCube.twoForm n)`, which is what the
algorithm is handed.  They assert nothing; `Ttc.TwoCube.twoProbFull_def` identifies
the last of them.
-/

/-- The inscribed radius `GetPrecision` **constructs** at the two-cube instance, on
the cleaned formula — `Ttc.autoGamma`, not the supplied `Ttc.TwoCube.gamT`. -/
noncomputable def gamFull (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) : ℝ :=
  autoGamma (atomsT n hn ε δ hε0 hε1) (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n))

/-- The dilation factor `Ttc.runScale` the run applies to its (cleaned) input. -/
noncomputable def scaleFull (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) : ℝ :=
  runScale (atomsT n hn ε δ hε0 hε1) (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n))
    ε δ hε0 hε1 hn
    (isPositive_cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n))
    (cleanBdd (atomsT n hn ε δ hε0 hε1) twoForm_isPositive
      (isBounded_sol_T n hn ε δ hε0 hε1) (interior_region_nonempty_two_d n hn ε δ hε0 hε1))
    (gamFull n hn ε δ hε0 hε1)

/-- The **dilated** atoms the run is actually performed on. -/
noncomputable def atomsFull (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    A2 n → LinAtom n :=
  scaledAtoms (atomsT n hn ε δ hε0 hε1) (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n))
    ε δ hε0 hε1 hn
    (isPositive_cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n))
    (cleanBdd (atomsT n hn ε δ hε0 hε1) twoForm_isPositive
      (isBounded_sol_T n hn ε δ hε0 hε1) (interior_region_nonempty_two_d n hn ε δ hε0 hε1))
    (gamFull n hn ε δ hε0 hε1)

/-- The dilated ball centres: `Ttc.autoCen` at the cleaned formula, scaled by
`Ttc.runScale`. -/
noncomputable def cenFull (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    {c : Cube (A2 n) //
        c ∈ Ttc.toDNFd (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n))} → Space n :=
  fun i => scaleFull n hn ε δ hε0 hε1 •
    autoCen (atomsT n hn ε δ hε0 hε1) (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n)) i

/-- **The probability `Ttc.ttc_volume_estimate` bounds on this witness.**  An
abbreviation for the integral, asserting nothing
(`Ttc.TwoCube.twoProbFull_def`).  Note this is a run on the *dilated* body of the
*cleaned* formula under the *constructed* ball; it is not `Ttc.TwoCube.twoProbD`. -/
noncomputable def twoProbFull (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ENNReal :=
  ∫⁻ c, trajLaw
      (runRates (atomsFull n hn ε δ hε0 hε1)
        (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n)) ε δ hε0 hε1 hn
        (isPositive_cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n))
        (scaledBdd (atomsT n hn ε δ hε0 hε1)
          (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n)) ε δ hε0 hε1 hn
          (isPositive_cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n))
          (cleanBdd (atomsT n hn ε δ hε0 hε1) twoForm_isPositive
            (isBounded_sol_T n hn ε δ hε0 hε1)
            (interior_region_nonempty_two_d n hn ε δ hε0 hε1))
          (gamFull n hn ε δ hε0 hε1))
        (cenFull n hn ε δ hε0 hε1)
        (scaleFull n hn ε δ hε0 hε1 * gamFull n hn ε δ hε0 hε1) c)
      {t | ttcRunOutput (atomsFull n hn ε δ hε0 hε1)
              (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n)) ε δ hε0 hε1 hn
              (isPositive_cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n))
              (scaledBdd (atomsT n hn ε δ hε0 hε1)
                (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n)) ε δ hε0 hε1 hn
                (isPositive_cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n))
                (cleanBdd (atomsT n hn ε δ hε0 hε1) twoForm_isPositive
                  (isBounded_sol_T n hn ε δ hε0 hε1)
                  (interior_region_nonempty_two_d n hn ε δ hε0 hε1))
                (gamFull n hn ε δ hε0 hε1))
              (cenFull n hn ε δ hε0 hε1)
              (scaleFull n hn ε δ hε0 hε1 * gamFull n hn ε δ hε0 hε1) c t
            / (scaleFull n hn ε δ hε0 hε1) ^ n
          ∈ relErr ε (volSol (Ttc.atomSet (atomsT n hn ε δ hε0 hε1)) (twoForm n))}
    ∂(MonteCarlo.coins n)

/-- **The abbreviation, written out.**  This is verbatim the integral in
`Ttc.ttc_volume_estimate`'s conclusion with `atoms := Ttc.TwoCube.atomsT …` and
`φ := Ttc.TwoCube.twoForm n`; the four helper `def`s above are folded into it and
nothing else changes.  Every occurrence of the formula is at the cleaned formula
`Ttc.cleanForm (Ttc.TwoCube.atomsT …) (Ttc.TwoCube.twoForm n)` except the accuracy
target `Ttc.volSol`, which is at the original `Ttc.TwoCube.twoForm n`. -/
theorem twoProbFull_def (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    twoProbFull n hn ε δ hε0 hε1 =
      ∫⁻ c, trajLaw
          (runRates
            (scaledAtoms (atomsT n hn ε δ hε0 hε1)
              (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n)) ε δ hε0 hε1 hn
              (isPositive_cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n))
              (cleanBdd (atomsT n hn ε δ hε0 hε1) twoForm_isPositive
                (isBounded_sol_T n hn ε δ hε0 hε1)
                (interior_region_nonempty_two_d n hn ε δ hε0 hε1))
              (autoGamma (atomsT n hn ε δ hε0 hε1)
                (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n))))
            (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n)) ε δ hε0 hε1 hn
            (isPositive_cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n))
            (scaledBdd (atomsT n hn ε δ hε0 hε1)
              (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n)) ε δ hε0 hε1 hn
              (isPositive_cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n))
              (cleanBdd (atomsT n hn ε δ hε0 hε1) twoForm_isPositive
                (isBounded_sol_T n hn ε δ hε0 hε1)
                (interior_region_nonempty_two_d n hn ε δ hε0 hε1))
              (autoGamma (atomsT n hn ε δ hε0 hε1)
                (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n))))
            (fun i =>
              runScale (atomsT n hn ε δ hε0 hε1)
                  (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n)) ε δ hε0 hε1 hn
                  (isPositive_cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n))
                  (cleanBdd (atomsT n hn ε δ hε0 hε1) twoForm_isPositive
                    (isBounded_sol_T n hn ε δ hε0 hε1)
                    (interior_region_nonempty_two_d n hn ε δ hε0 hε1))
                  (autoGamma (atomsT n hn ε δ hε0 hε1)
                    (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n)))
                • autoCen (atomsT n hn ε δ hε0 hε1)
                    (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n)) i)
            (runScale (atomsT n hn ε δ hε0 hε1)
                  (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n)) ε δ hε0 hε1 hn
                  (isPositive_cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n))
                  (cleanBdd (atomsT n hn ε δ hε0 hε1) twoForm_isPositive
                    (isBounded_sol_T n hn ε δ hε0 hε1)
                    (interior_region_nonempty_two_d n hn ε δ hε0 hε1))
                  (autoGamma (atomsT n hn ε δ hε0 hε1)
                    (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n)))
              * autoGamma (atomsT n hn ε δ hε0 hε1)
                  (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n))) c)
          {t | ttcRunOutput
                  (scaledAtoms (atomsT n hn ε δ hε0 hε1)
                    (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n)) ε δ hε0 hε1 hn
                    (isPositive_cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n))
                    (cleanBdd (atomsT n hn ε δ hε0 hε1) twoForm_isPositive
                      (isBounded_sol_T n hn ε δ hε0 hε1)
                      (interior_region_nonempty_two_d n hn ε δ hε0 hε1))
                    (autoGamma (atomsT n hn ε δ hε0 hε1)
                      (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n))))
                  (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n)) ε δ hε0 hε1 hn
                  (isPositive_cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n))
                  (scaledBdd (atomsT n hn ε δ hε0 hε1)
                    (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n)) ε δ hε0 hε1 hn
                    (isPositive_cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n))
                    (cleanBdd (atomsT n hn ε δ hε0 hε1) twoForm_isPositive
                      (isBounded_sol_T n hn ε δ hε0 hε1)
                      (interior_region_nonempty_two_d n hn ε δ hε0 hε1))
                    (autoGamma (atomsT n hn ε δ hε0 hε1)
                      (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n))))
                  (fun i =>
                    runScale (atomsT n hn ε δ hε0 hε1)
                        (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n)) ε δ hε0 hε1 hn
                        (isPositive_cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n))
                        (cleanBdd (atomsT n hn ε δ hε0 hε1) twoForm_isPositive
                          (isBounded_sol_T n hn ε δ hε0 hε1)
                          (interior_region_nonempty_two_d n hn ε δ hε0 hε1))
                        (autoGamma (atomsT n hn ε δ hε0 hε1)
                          (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n)))
                      • autoCen (atomsT n hn ε δ hε0 hε1)
                          (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n)) i)
                  (runScale (atomsT n hn ε δ hε0 hε1)
                        (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n)) ε δ hε0 hε1 hn
                        (isPositive_cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n))
                        (cleanBdd (atomsT n hn ε δ hε0 hε1) twoForm_isPositive
                          (isBounded_sol_T n hn ε δ hε0 hε1)
                          (interior_region_nonempty_two_d n hn ε δ hε0 hε1))
                        (autoGamma (atomsT n hn ε δ hε0 hε1)
                          (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n)))
                    * autoGamma (atomsT n hn ε δ hε0 hε1)
                        (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n))) c t
                / (runScale (atomsT n hn ε δ hε0 hε1)
                    (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n)) ε δ hε0 hε1 hn
                    (isPositive_cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n))
                    (cleanBdd (atomsT n hn ε δ hε0 hε1) twoForm_isPositive
                      (isBounded_sol_T n hn ε δ hε0 hε1)
                      (interior_region_nonempty_two_d n hn ε δ hε0 hε1))
                    (autoGamma (atomsT n hn ε δ hε0 hε1)
                      (cleanForm (atomsT n hn ε δ hε0 hε1) (twoForm n)))) ^ n
              ∈ relErr ε (volSol (Ttc.atomSet (atomsT n hn ε δ hε0 hε1)) (twoForm n))}
        ∂(MonteCarlo.coins n) := rfl

/-- The same quantity as a real number — the left-hand side of the guarantee. -/
noncomputable def twoAccFull (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) : ℝ :=
  (twoProbFull n hn ε δ hε0 hε1).toReal

/-! ## The witness -/

/-- **`Ttc.ttc_volume_estimate` on a DNF with two cubes**, at every
`(ε, δ) ∈ (0,1]²` and every `n ≥ 1`.

All twelve binders are met by the two-cube data of `Ttc/Witness/TwoCube.lean`:
`hφ` is `Ttc.TwoCube.twoForm_isPositive`, `hbdd` is `Ttc.TwoCube.isBounded_sol_T`,
and `hint` is `Ttc.TwoCube.interior_region_nonempty_two_d` — the two regions are
boxes of side `Ttc.TwoCube.sideT > 0`, hence full-dimensional.  Nothing is supplied
for the inscribed ball: at twelve binders the ball is constructed by the statement
itself (`Ttc.autoCen`, `Ttc.autoGamma`), the run is on the body dilated by
`Ttc.runScale` with the estimate divided by `cⁿ`, and the formula handed to the
algorithm is the cleaned one `Ttc.cleanForm atoms φ` — which is why the former
`hcoeff` binder (`Ttc.TwoCube.coeff_ne_zero_two_d`) is no longer passed.

`Ttc.ttc_volume_estimate` now concludes a conjunction (accuracy ∧ runtime); this is
its accuracy half, `Pr[ output ∈ (1±ε)·Vol(F) ] ≥ 1 − δ` in the **user's** `δ`, about
the **original** `Vol(Sol F)`.  `Ttc.TwoCube.twoProbFull_def` writes the probability
out.  It is a *different run* from `Ttc.TwoCube.twoAccD` (`Ttc/Witness/Inputs.lean`),
which is undilated, uncleaned and takes the ball as data; the two are not claimed
equal.

**Cost — exponential in `n`, paid twice, on a dilated body.**  See this module's
docstring.  Unconditional correctness, not efficiency. -/
theorem ttc_volume_estimate_two_cube_full (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    1 - δ ≤ twoAccFull n hn ε δ hε0 hε1 :=
  (ttc_volume_estimate (atomsT n hn ε δ hε0 hε1) (twoForm n) ε δ hε0 hε1 hδ0 hδ1 hn
    twoForm_isPositive (isBounded_sol_T n hn ε δ hε0 hε1)
    (interior_region_nonempty_two_d n hn ε δ hε0 hε1)).1

/-- **`Ttc.ttc_volume_estimate` on a two-cube DNF at two structurally different
parameter pairs, with the achieved bound a positive numeral.**

* `(ε, δ) = (1/3, 9/10)`: bound `1/10 > 0`, at a `δ ∈ (4/5, 1)` where
  `Ttc.ttc_volume_endToEnd`'s budget `1 − δ − δ/4 = −1/8` certifies nothing.
* `(ε, δ) = (1/2, 1/4)`: a different accuracy *and* confidence, so the two runs have
  different sides `Ttc.TwoCube.sideT`, different corners `Ttc.TwoCube.loT`, different
  cleaned formulas `Ttc.cleanForm`, different constructed radii `Ttc.autoGamma` and
  different dilations `Ttc.runScale` — two instances, not one instance twice.

Both numerals are proved strictly positive **in the statement**, so neither conclusion
is the vacuous `0 ≤ (…).toReal`.  Both runs carry the exponential cost recorded in
this module's docstring. -/
theorem ttc_volume_estimate_two_cube_full_at (n : ℕ) (hn : 1 ≤ n)
    (hε₁ : (0 : ℝ) < 1/3) (hε₁' : (1/3 : ℝ) ≤ 1)
    (hε₂ : (0 : ℝ) < 1/2) (hε₂' : (1/2 : ℝ) ≤ 1) :
    ((0 : ℝ) < 1/10 ∧ (1/10 : ℝ) ≤ twoAccFull n hn (1/3) (9/10) hε₁ hε₁'
      ∧ (4/5 : ℝ) < 9/10 ∧ (9/10 : ℝ) < 1)
    ∧ ((0 : ℝ) < 3/4 ∧ (3/4 : ℝ) ≤ twoAccFull n hn (1/2) (1/4) hε₂ hε₂') := by
  refine ⟨⟨by norm_num, ?_, by norm_num, by norm_num⟩, ⟨by norm_num, ?_⟩⟩
  · have h := ttc_volume_estimate_two_cube_full n hn (1/3) (9/10) hε₁ hε₁'
      (by norm_num) (by norm_num)
    linarith
  · have h := ttc_volume_estimate_two_cube_full n hn (1/2) (1/4) hε₂ hε₂'
      (by norm_num) (by norm_num)
    linarith

/-- **The bound is a genuine number, not `ENNReal.toReal ⊤ = 0`.**  A strictly
positive lower bound on the `toReal` forces the measure itself to be nonzero and
finite. -/
theorem twoProbFull_pos_ne_top (n : ℕ) (hn : 1 ≤ n)
    (hε0 : (0 : ℝ) < 1/3) (hε1 : (1/3 : ℝ) ≤ 1) :
    0 < twoProbFull n hn (1/3) (9/10) hε0 hε1
      ∧ twoProbFull n hn (1/3) (9/10) hε0 hε1 ≠ ⊤ := by
  have h := (ttc_volume_estimate_two_cube_full_at n hn hε0 hε1 (by norm_num)
    (by norm_num)).1.2.1
  have hpos : 0 < (twoProbFull n hn (1/3) (9/10) hε0 hε1).toReal :=
    lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/10) h
  exact ⟨(ENNReal.toReal_pos_iff.1 hpos).1, (ENNReal.toReal_pos_iff.1 hpos).2.ne⟩

end TwoCube

end Ttc

/-! ## Axiom profile

Every declaration of this file, checked transitively (`CLAUDE.md` §4).  Expect
`[propext, Classical.choice, Quot.sound]` throughout — no `sorry`, no custom axiom,
no `native_decide`. -/

#check @Ttc.TwoCube.ttc_volume_estimate_two_cube_full

#print axioms Ttc.TwoCube.interior_region_nonempty_two_d
#print axioms Ttc.TwoCube.gamFull
#print axioms Ttc.TwoCube.scaleFull
#print axioms Ttc.TwoCube.atomsFull
#print axioms Ttc.TwoCube.cenFull
#print axioms Ttc.TwoCube.twoProbFull
#print axioms Ttc.TwoCube.twoProbFull_def
#print axioms Ttc.TwoCube.twoAccFull
#print axioms Ttc.TwoCube.ttc_volume_estimate_two_cube_full
#print axioms Ttc.TwoCube.ttc_volume_estimate_two_cube_full_at
#print axioms Ttc.TwoCube.twoProbFull_pos_ne_top
