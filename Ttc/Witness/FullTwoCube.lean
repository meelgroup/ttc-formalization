/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.Api
import Ttc.Model.Theorem
import Ttc.Witness.Inputs

/-!
# `Witness/FullTwoCube`: `Ttc.ttc_volume_estimate_parametric` is not vacuous

`Ttc.ttc_volume_estimate_parametric` (`Exec/PricedHeadline.lean`) — the price-parametric
form of the headline, and the repo's unconditional result — is a `∀` under **eleven**
binders

```
atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos
```

and a `∀` whose hypotheses nothing satisfies is worth nothing (`CLAUDE.md` §11).
This file exhibits data satisfying all eleven, at **every** `n ≥ 1` and **every**
`(ε, δ) ∈ (0,1]²`, and then pins the conclusion at two parameter numerals where the
achieved bound is proved **strictly positive inside the statement** — so neither
conclusion is the vacuous `0 ≤ (…).toReal` that `ENNReal.toReal ⊤ = 0` would
otherwise permit.

The data is the **two-cube** instance of `Ttc/Witness/TwoCube.lean`: the pair of
disjoint axis-aligned boxes `[0,c]ⁿ` and `[lo, lo+c]ⁿ` with side
`c = Ttc.TwoCube.sideT = max 1 Thresh` and `lo > c` a multiple of the lattice
spacing.  The shape binders are lemmas that file (or `Ttc/Witness/Inputs.lean`)
already proves, used unchanged:

| binder | discharged by |
| --- | --- |
| `atoms` | `Ttc.TwoCube.atomsT` |
| `φ` | `Ttc.TwoCube.twoForm` |
| `hφ` | `Ttc.TwoCube.twoForm_isPositive` |
| `hpos` | `Ttc.TwoCube.twoVolPos`, new here |

(`Ttc.atomSet (Ttc.TwoCube.atomsT …) = Ttc.TwoCube.MTT …` by `rfl` —
`Ttc.TwoCube.atomSet_atomsT`.)  Three binders the statement used to carry are **no
longer passed**: `hcoeff` — *no facet of the DNF has a zero normal* — because the
run is on the **cleaned** formula (`Ttc/Exec/Cleanup.lean`); `hint` — *every cube is
full-dimensional* — because the run is on the **pruned** formula
(`Ttc/Exec/Prune.lean`), which makes that condition true rather than assuming it;
and `hbdd` — *`Sol(F)` is bounded* — because at the pruned formula it is *derived*
from `hφ` and `hpos` (`Ttc.isBounded_sol_pruneForm_of_volSol_pos`,
`Ttc/Exec/BddFromPos.lean`).

`Ttc.TwoCube.isBounded_sol_T` is still used here, but only *inside* the proof of
`hpos`: `Ttc.volSol_pos_of_interior` runs the other direction (full-dimensionality
plus boundedness give positive volume) and needs its own boundedness proof.

## Why `hpos` holds: one region contains an open ball of positive radius

The last binder is `0 < Ttc.volSol (Ttc.atomSet atoms) φ`, and it is *not*
proved from box geometry here.  `Ttc.volSol_pos_of_interior` (`Ttc/Exec/Prune.lean`)
turns per-cube full-dimensionality into positive volume for a bounded body, so all
that is needed is the old `hint`, which this file still proves as
`Ttc.TwoCube.interior_region_nonempty_two_d`: `Ttc/Witness/TwoCube.lean` already
exhibits `Metric.ball (cenT …) (gamT …) ⊆ region (MTT …) i.val`
(`Ttc.TwoCube.ball_subset_two`, transported to the deduplicated cube list as
`Ttc.TwoCube.ball_subset_two_d`) with `gamT = sideT/2 > 0` (`Ttc.TwoCube.gamT_pos`,
`Ttc.TwoCube.sideT_pos`).  An **open** subset of a set is contained in its interior
(`interior_maximal` with `Metric.isOpen_ball`), and a ball of positive radius is
nonempty (`Metric.nonempty_ball`), so the interior is nonempty.  `hpos` is then one
application of `Ttc.volSol_pos_of_interior`.

Note the implication runs one way only: `Ttc.hint_not_derivable` refutes the
converse, which is exactly why the headline could drop `hint` for the weaker `hpos`.

## What the run is, and what it is not

The eleven-binder statement takes neither the inscribed ball, nor full-dimensionality,
nor boundedness as data.  What `Ttc.ttc_volume_estimate` measures is a run on the input
with its

* **degenerate cubes pruned** (`Ttc.pruneForm`, `Ttc/Exec/Prune.lean`),
* **zero-normal atoms cleaned** (`Ttc.cleanForm`, `Ttc/Exec/Cleanup.lean`) — the
  composite of the two is `Ttc.ttcInput`,
* inscribed ball **constructed** on that (`Ttc.autoCen`, `Ttc.autoGamma`,
  `Model/Pseudocode` lines A7–A9), and the whole body then **dilated** by
  `Ttc.runScale` (line A10), with the estimate divided by `cⁿ` (line A13);

and only the accuracy *target* `Ttc.volSol` is at the user's original
`Ttc.TwoCube.twoForm n` (the preprocessing moves no volume:
`Ttc.volSol_pruneForm`, `Ttc.volSol_cleanForm`).

None of that is spelled out below, because `Ttc/Exec/Api.lean` names it:
`Ttc.ttcLaw` (`Monadic/Program`) and `Ttc.ttcEstimate` take exactly
`atoms φ ε δ hε0 hε1 hn hφ hpos` and compose the preprocessing, the ball and the
dilation internally.  So `Ttc.TwoCube.twoProbFull` is a five-line abbreviation for the
**single measure** in the headline's conclusion — the run law of the good event, no
iterated integral; it asserts nothing, and `Ttc.TwoCube.twoProbFull_def` writes it out
by `rfl`.

`Ttc.ttc_volume_estimate` states that measure over `Model/Pseudocode`'s
`Ttc.ttcAlgOutput`, at the constructed bundle `Ttc.ttcOracleBundle`, rather than over
`Ttc.ttcEstimate`; the two are the same term (`Ttc.ttcAlgOutput_eq_ttcEstimate`, by
`rfl`), which is why the applications below need no rewriting.

It is **not** `Ttc.TwoCube.twoAccD` or `Ttc.TwoCube.twoAcc` (`Ttc/Witness/Inputs.lean`),
which are undilated, unpruned, uncleaned runs under a *supplied* ball.  Those are
different runs; nothing here is computed, simplified, or claimed to relate to them.

## What is landed

| result | content |
| --- | --- |
| `Ttc.TwoCube.interior_region_nonempty_two_d` | both regions are full-dimensional |
| `Ttc.TwoCube.twoVolPos` | `hpos`: `0 < Vol(Sol F)`, from the line above |
| `Ttc.TwoCube.twoProbFull_def` | the named probability **is** the headline's measure, here |
| `Ttc.TwoCube.ttc_volume_estimate_two_cube_full` | `Ttc.ttc_volume_estimate_parametric` itself, at every `(ε, δ) ∈ (0,1]²` |
| `Ttc.TwoCube.ttc_volume_estimate_two_cube_full_at` | the same at `(1/3, 9/10)` and `(1/2, 1/4)`, bounds `1/10` and `3/4`, both proved positive |
| `Ttc.TwoCube.twoProbFull_pos_ne_top` | the bound is a real number, not `ENNReal.toReal ⊤ = 0` |

## Cost caveat

**Exponential in `n` on both oracle routes, paid twice, and on a dilated body.**
The volume estimator is hit-and-miss Monte Carlo at `Θ(Rⁿ/(ε'²δ'))` samples, the ball
walk's certified step count is `2^Θ(n)·log(M·Vol(P′)/ε′)`, and the lattice
transcription enumerates `Ttc.latticeCount ≈ Θ((c·10^ρ)ⁿ)` points; with `m = 2` cubes
surviving the pruning, each of those costs is paid **once per cube**.  On top of that,
the dilation inflates the body by `Ttc.runScale ≥ 1` *before* the lattice is
enumerated, so the enumerated lattice is that of the dilated body — a further
`Ttc.runScale ^ n` factor in the point count.  What is established is unconditional
*correctness*; `thm:runtime`'s efficiency claim remains out of scope.
-/

namespace Ttc

namespace TwoCube

open MeasureTheory Set Pointwise

/-! ## `hpos`: the two-cube body has positive volume -/

/-- **Each of the two regions is full-dimensional.**  Each is an axis-aligned box of
side `Ttc.TwoCube.sideT > 0`, and `Ttc/Witness/TwoCube.lean` already exhibits an open
ball of radius `Ttc.TwoCube.gamT > 0` inside it (`Ttc.TwoCube.ball_subset_two_d`).  An
open subset of a set lies in its interior, and a ball of positive radius is nonempty,
so the interior is nonempty.  No box geometry is recomputed.

This is no longer a binder of the headline — pruning makes it true rather
than assuming it — but it is what `Ttc.volSol_pos_of_interior` consumes to give the
binder that *is* there, `Ttc.TwoCube.twoVolPos`. -/
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

/-! ## The run, named -/

/-- **The probability the headline bounds on this witness.**  A pure
abbreviation for the measure in the headline's conclusion, asserting nothing
(`Ttc.TwoCube.twoProbFull_def`): the run law `Ttc.ttcLaw` (`Monadic/Program`) of the
good event, at a point `p = (volume coins, sample trajectory)`.

Everything the run does to the input — pruning, cleaning, constructing the inscribed
ball, dilating, and dividing the estimate back down — is inside `Ttc.ttcLaw` and
`Ttc.ttcEstimate` (`Ttc/Exec/Api.lean`).  Only the accuracy target `Ttc.volSol` is at
the original `Ttc.TwoCube.twoForm n`.  This is *not* `Ttc.TwoCube.twoProbD`. -/
noncomputable def twoProbFull (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (cVol cSample : ℕ) : ENNReal :=
  ttcCharged (atomsT n hn ε δ hε0 hε1) (twoForm n) ε δ cVol cSample
    {r | r.1 ∈ relErr ε (volSol (Ttc.atomSet (atomsT n hn ε δ hε0 hε1)) (twoForm n))}

/-- **The abbreviation, written out**, with `Ttc.TwoCube.twoVolPos` folded in.  This is
the measure in `Ttc.ttc_volume_estimate_parametric`'s conclusion at
`atoms := Ttc.TwoCube.atomsT …` and `φ := Ttc.TwoCube.twoForm n` — the headline writes
the measured quantity as `Ttc.ttcAlgOutput … (Ttc.ttcOracleBundle …)`, which is
`Ttc.ttcEstimate` by `rfl` (`Ttc.ttcAlgOutput_eq_ttcEstimate`) — and nothing else
changes. -/
theorem twoProbFull_def (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (cVol cSample : ℕ) :
    twoProbFull n hn ε δ hε0 hε1 cVol cSample =
      ttcCharged (atomsT n hn ε δ hε0 hε1) (twoForm n) ε δ cVol cSample
        {r | r.1 ∈ relErr ε (volSol (Ttc.atomSet (atomsT n hn ε δ hε0 hε1)) (twoForm n))} := rfl

/-- The same quantity as a real number — the left-hand side of the guarantee. -/
noncomputable def twoAccFull (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (cVol cSample : ℕ) : ℝ :=
  (twoProbFull n hn ε δ hε0 hε1 cVol cSample).toReal

/-! ## The witness -/

/-- **`Ttc.ttc_volume_estimate_parametric` on a DNF with two cubes**, at every
`(ε, δ) ∈ (0,1]²` and every `n ≥ 1`.

⚠ The witnessed statement is the **price-parametric** headline
(`Exec/PricedHeadline`), not `Ttc.ttc_volume_estimate` (`Model/Theorem`), whose two
prices are fixed.  The nine binders of the latter are a sub-list of these eleven, so the
same two-cube data meets them and its accuracy conjunct follows by instantiation; no
declaration here states that instance.

All eleven binders are met by the two-cube data of `Ttc/Witness/TwoCube.lean`: `hφ` is
`Ttc.TwoCube.twoForm_isPositive` and `hpos` is `Ttc.TwoCube.twoVolPos`.  Nothing is
supplied for the inscribed ball, for full-dimensionality, for nondegenerate facets or
for boundedness of `Sol(F)`: at eleven binders the statement
prunes and cleans the formula itself, constructs the ball (`Ttc.autoCen`,
`Ttc.autoGamma`) and dilates by `Ttc.runScale`, dividing the estimate by `cⁿ`.

`Ttc.ttc_volume_estimate_parametric` concludes a conjunction (accuracy ∧ runtime); this
is its accuracy half, `Pr[ output ∈ (1±ε)·Vol(F) ] ≥ 1 − δ` in the **user's** `δ`, about the
**original** `Vol(Sol F)`.  `Ttc.TwoCube.twoProbFull_def` writes the probability out.
It is a *different run* from `Ttc.TwoCube.twoAccD` (`Ttc/Witness/Inputs.lean`), which
is undilated, unpruned, uncleaned and takes the ball as data; the two are not claimed
equal.

**Cost — exponential in `n`, paid twice, on a dilated body.**  See this module's
docstring.  Unconditional correctness, not efficiency. -/
theorem ttc_volume_estimate_two_cube_full (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (cVol cSample : ℕ) :
    1 - δ ≤ twoAccFull n hn ε δ hε0 hε1 cVol cSample :=
  (ttc_volume_estimate_parametric (atomsT n hn ε δ hε0 hε1) (twoForm n) ε δ hε0 hε1 hδ0 hδ1 hn
    twoForm_isPositive (twoVolPos n hn ε δ hε0 hε1) cVol cSample).1

/-- **`Ttc.ttc_volume_estimate_parametric` on a two-cube DNF at two structurally
different parameter pairs, with the achieved bound a positive numeral.**

* `(ε, δ) = (1/3, 9/10)`: bound `1/10 > 0`, at a `δ ∈ (4/5, 1)` where
  `Ttc.ttc_volume_endToEnd`'s budget `1 − δ − δ/4 = −1/8` certifies nothing.
* `(ε, δ) = (1/2, 1/4)`: a different accuracy *and* confidence, so the two runs have
  different sides `Ttc.TwoCube.sideT`, different corners `Ttc.TwoCube.loT`, different
  preprocessed formulas `Ttc.ttcInput`, different constructed radii `Ttc.ttcRadius`
  and different dilations `Ttc.ttcScale` — two instances, not one instance twice.

Both numerals are proved strictly positive **in the statement**, so neither conclusion
is the vacuous `0 ≤ (…).toReal`.  Both runs carry the exponential cost recorded in
this module's docstring. -/
theorem ttc_volume_estimate_two_cube_full_at (n : ℕ) (hn : 1 ≤ n)
    (hε₁ : (0 : ℝ) < 1/3) (hε₁' : (1/3 : ℝ) ≤ 1)
    (hε₂ : (0 : ℝ) < 1/2) (hε₂' : (1/2 : ℝ) ≤ 1) (cVol cSample : ℕ) :
    ((0 : ℝ) < 1/10 ∧ (1/10 : ℝ) ≤ twoAccFull n hn (1/3) (9/10) hε₁ hε₁' cVol cSample
      ∧ (4/5 : ℝ) < 9/10 ∧ (9/10 : ℝ) < 1)
    ∧ ((0 : ℝ) < 3/4 ∧ (3/4 : ℝ) ≤ twoAccFull n hn (1/2) (1/4) hε₂ hε₂' cVol cSample) := by
  refine ⟨⟨by norm_num, ?_, by norm_num, by norm_num⟩, ⟨by norm_num, ?_⟩⟩
  · have h := ttc_volume_estimate_two_cube_full n hn (1/3) (9/10) hε₁ hε₁'
      (by norm_num) (by norm_num) cVol cSample
    linarith
  · have h := ttc_volume_estimate_two_cube_full n hn (1/2) (1/4) hε₂ hε₂'
      (by norm_num) (by norm_num) cVol cSample
    linarith

/-- **The bound is a genuine number, not `ENNReal.toReal ⊤ = 0`.**  A strictly
positive lower bound on the `toReal` forces the measure itself to be nonzero and
finite. -/
theorem twoProbFull_pos_ne_top (n : ℕ) (hn : 1 ≤ n)
    (hε0 : (0 : ℝ) < 1/3) (hε1 : (1/3 : ℝ) ≤ 1) (cVol cSample : ℕ) :
    0 < twoProbFull n hn (1/3) (9/10) hε0 hε1 cVol cSample
      ∧ twoProbFull n hn (1/3) (9/10) hε0 hε1 cVol cSample ≠ ⊤ := by
  have h := (ttc_volume_estimate_two_cube_full_at n hn hε0 hε1 (by norm_num)
    (by norm_num) cVol cSample).1.2.1
  have hpos : 0 < (twoProbFull n hn (1/3) (9/10) hε0 hε1 cVol cSample).toReal :=
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
#print axioms Ttc.TwoCube.twoVolPos
#print axioms Ttc.TwoCube.twoProbFull
#print axioms Ttc.TwoCube.twoProbFull_def
#print axioms Ttc.TwoCube.twoAccFull
#print axioms Ttc.TwoCube.ttc_volume_estimate_two_cube_full
#print axioms Ttc.TwoCube.ttc_volume_estimate_two_cube_full_at
#print axioms Ttc.TwoCube.twoProbFull_pos_ne_top
