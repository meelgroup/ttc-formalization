/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Monadic.MeasurePr
import Ttc.Monadic.Program

/-!
# The main theorem: `thm:volumettc` + `thm:runtime` for `TTC(F, ε, δ)`

The **statement layer**, and nothing else: this file contains one theorem,
`Ttc.ttc_volume_estimate`, and no definition, no auxiliary lemma and no proof to work
through — the accuracy half is `Ttc.ttc_accuracy_single_measure` (`Monadic/EventMeasurable`)
and the running-time half is the second component of `Ttc.ttc_volume_api` (`Exec/Api`),
read at `p.1` and `p.2`.

Audit path — `Model/`, then stop, **four files**: `Model/Prelude` (the vocabulary),
`Model/ProblemSetting` (what `Vol(F)` is and what `(1 ± ε)` means),
`Model/Pseudocode` (`alg:ttc` and its preprocessing, transcribed line by line, ending
in the algorithm's output `Ttc.ttcAlgOutput`), this file.

`TTC` takes three inputs, so three inputs is what this statement takes: the formula
`F = (atoms, φ)`, the accuracy `ε`, the confidence `δ`.  **Eleven binders**

```
atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos
```

and among them there is no interpretation, no parameter block, no converter, no
oracle, no precision, no inscribed-ball data — and no boundedness hypothesis.

## What the guarantee is stated over: one law, one point, both halves

    ttcLaw atoms φ ε δ hε0 hε1 hn hφ hpos
      : Measure ((ℕ → Space n) × (ℕ → Fin (ttcIndex …) → ℕ))

— **the law of one run of `TTC(F, ε, δ)`**, defined and documented in `Monadic/Program`
as the composition–product of the volume oracle's coin law with the coin-indexed
trajectory kernel: draw the volume coins `c`, then draw the sample trajectory `t` from
the coupled family at the rates *that* draw produced.  A point of its space is a whole
run `p = (c, t)`, and **both conjuncts below speak about the same `p`** — the accuracy
half about the output `Ttc.ttcAlgOutput … (ttcOracleBundle … p.1 p.2)`, the running-time
half about the charged cost `Ttc.ttcCost … p.1 p.2`.

**There is no iterated integral.**  Earlier versions of this statement carried
`∫⁻ c, trajLaw (ttcRates … c) {t | …} ∂(MonteCarlo.coins n)` — outer over the volume
coins, inner the trajectory law at the rates that run produced — and so quantified the
two coin sequences separately, in two different places, in the two conjuncts.  Folding
it into one measure is `Ttc.lintegral_good_event_eq_compProd`, and it is not free: it
needs the good event measurable **jointly** in `c` and `t`, which is what
`Monadic/EventMeasurable` establishes (`Ttc.CountablyDetermined`, since `Ttc.run` folds
through a `Multiset (Space n)` state that carries no measurable structure and
`Ttc.absorbLevel` is an unbounded `Nat.sInf` search).

### Why a `Measure` and not a `PMF`

nfalean's `ApproxNFA.countNFAM` is an honest `PMF (ℝ × ℕ)` — its randomness is a finite
coin sequence — and its headline is stated in the `PMF` monad.  `Ttc.ttcLaw` cannot be:
`Ttc.MonteCarlo.coins` is `MeasureTheory.Measure.infinitePi` of the uniform law on a
Euclidean ball, an **atomless** measure on an uncountable space, so there is no `PMF`
whose `toOuterMeasure` it is.  This is a fact about the object, not a stylistic choice;
`Monadic/MeasurePr`'s docstring works through the consequences.  What does survive is
the Giry-monad structure: `Ttc.ttcTrajKernel` is a Markov kernel, `⊗ₘ` is the monadic
bind, and `Ttc.ttcLaw` is a probability measure.

`Pr[p ← μ; E p]` below is `Monadic/MeasurePr`'s notation for `(μ {p | E p}).toReal` —
Mathlib's measure at Mathlib's `setOf`, read as a real.  Nothing of ours is named by it.

### Why the running-time half is `∀ p` and not `All[p ← ttcLaw; …]`

Deliberate, and it is the **stronger** statement.  nfalean writes its running-time half
as `All[r ← countNFAM …; …]`, where `All` is `PMF.support p ⊆ {x | E x}` — *no*
exceptional outcome exists at all — which is the natural notion for a `PMF`.  Ours
cannot be that: for a general measure Mathlib's support is topological, would drag a
`[TopologicalSpace]` instance into this statement, and does not carry full mass, so our
`All[p ← μ; E p]` is `∀ᵐ p ∂μ, E p` (`Monadic/MeasurePr`).  That permits an exceptional
set, provided `μ` cannot see it — and the cost bound we can actually prove has **no**
exceptional set at all: it holds at *every* point of the space, null or not.  Writing it
as `All[…]` would throw that strength away to look more like nfalean.  So it is a plain
`∀ p`, and it is a strictly stronger claim than the a.e. form.

## What is measured: `Model/Pseudocode`'s own `Ttc.ttcAlgOutput`

The accuracy conjunct says, in one term,

```
Pr[ p ← ttcLaw …;
    ttcAlgOutput atoms φ ε δ … (ttcOracleBundle … p.1 p.2) ∈ relErr ε (volSol (atomSet atoms) φ) ]
  ≥ 1 − δ
```

`Ttc.ttcAlgOutput` is **the algorithm**: `Model/Pseudocode` defines it as `Ttc.run` —
the fold of `alg:ttc` lines 22–46 — over the preprocessed formula's cubes
`Ttc.toDNFd (Ttc.preprocess atoms φ)`, at the computed parameter block
`Ttc.inputParams` (lines 17–20) and the computed precision `Ttc.runPrec` (line 17),
with the estimate divided by `qⁿ` for the dilation `q = Ttc.runScale` (lines
A10–A13).  Its last argument is the **oracle bundle**, because `alg:ttc` line 24's
`Vol_ED` and line 43's `GenerateSamples` are calls into one — exactly as the paper
prints them.

The bundle supplied here, `Ttc.ttcOracleBundle` (`Exec/Api`), is *constructed*, not
assumed: `Vol_ED` is the Monte-Carlo estimator `Ttc.mcVol` at the run's volume coins
`p.1`, and `GenerateSamples` is the ball-walk sampler at the run's sample coins `p.2`.
The target is the **user's own** `Vol(F)`, at the original `φ`: neither preprocessing
pass moves it.

The runtime conjunct is stated in the folded vocabulary of `Exec/Api` —
`Ttc.ttcTerminates`, `Ttc.ttcCost`, `Ttc.ttcNumCubes`, `Ttc.ttcThresh` — each of
which unfolds by `rfl` to the corresponding term of `Runtime.lean`
(`Ttc.ttcTerminates_def`, `Ttc.ttcCost_def`, `Ttc.ttcNumCubes_def`,
`Ttc.ttcThresh_def`).

## What the statement names

This file is *one declaration* — no `def`, no auxiliary lemma — and the theorem's
type names, outside `Model/`, only

```
ttcLaw  ttcIndex  ttcOracleBundle
preprocess_bdd
ttcTerminates  ttcCost  ttcThresh  ttcNumCubes
```

The first line is **the run and its law**: the law of a single run of the algorithm,
the index the sample coins range over, and the oracle bundle the run reads.  `ttcLaw`
absorbs what used to be three separate names in this statement (`Ttc.trajLaw`,
`Ttc.ttcRates`, `Ttc.MonteCarlo.coins`) — those are now inside `Monadic/Program`'s
definition, which is where the probability space belongs: `alg:ttc` treats `Vol_ED`
and `GenerateSamples` as oracle calls, so the *construction* that discharges them is
proof content, not statement content.  The last line is the runtime conjunct's four
folded names, each with its `rfl` lemma in `Exec/Api`.

`Ttc.preprocess_bdd` is the odd one out, and it is a **proof term**, not a quantity:
`Bornology.IsBounded (sol (atomSet atoms) (preprocess atoms φ))`, derived from `hφ`
and `hpos` alone (`Exec/BddFromPos`).  It appears because `Ttc.Params` bundles five
*proof* fields, so `Ttc.inputParams` — and hence `Ttc.ttcAlgOutput` — cannot be
applied without it.  `Model/Pseudocode`'s docstring, "The divergence from the
reference layout", states this plainly and says what removing it would cost.

The property is machine-checkable in one `run_cmd`: walk
`Ttc.ttc_volume_estimate`'s type past its binders, collect
`Expr.getUsedConstants`, and keep those whose defining module starts with `Ttc`
but not `Ttc.Model`.  `Ttc.ttcAlgOutput_eq_ttcEstimate` (`Exec/Api`, by `rfl`) is the
bridge in the other direction, identifying the measured term with the run's estimate;
`Ttc.ttcLaw_def` (`Monadic/Program`, by `rfl`) is the corresponding bridge for the law.

The fact that this theorem's proof is a pair of bare applications, with no rewriting,
is the structural check that the names above name what they claim to name: a wrong
abbreviation is a build error, not a silent divergence.

## What is assumed

Four things an auditor needs and this file deliberately does **not** restate, so
that it stays the statement:

* the **definitional closure** — what the named terms unfold to outside `Model/`
  (the `Exec/Api` auxiliaries, the constructed oracle bundle, the constructed
  sampler, the parameter block, and the run's probability space, now reached through
  `Ttc.ttcLaw`);
* the **three preprocessing steps** the headline certifies `alg:ttc` *plus*, and
  which of them change the algorithm's behaviour;
* the **two residual hypotheses** `hφ` and `hpos`, and what is known about each;
* that **`hbdd` was derived**, not dropped.

All four are in [`AUDIT.md`](../../AUDIT.md) §1h, which is written to be read
alongside this file.  `Model/Pseudocode`'s `A1`–`A13` block is the pseudocode for
the preprocessing itself.
-/

namespace Ttc

open MeasureTheory Set
open Ttc.Monadic

/-- **`thm:volumettc` + `thm:runtime`.**  `TTC` is run on `F = (atoms, φ)` at accuracy
`ε` and confidence `δ`, and **both halves speak about the same run** `p = (c, t)` drawn
from the same law `Ttc.ttcLaw` — the volume coins, then the sample trajectory at the
rates that draw produced.  No iterated integral.

* **Accuracy.**  `Pr[ TTC(F, ε, δ) ∈ (1 ± ε)·Vol(F) ] ≥ 1 − δ`, the probability being
  the one `Ttc.ttcLaw` assigns.  The output is `Model/Pseudocode`'s own
  `Ttc.ttcAlgOutput` — the fold of `alg:ttc` lines 22–46 at the computed parameter
  block and precision, rescaled by `1/qⁿ` — evaluated at the constructed oracle bundle
  `Ttc.ttcOracleBundle` on that same run, and the target is the **user's own** `Vol(F)`.
* **Running time.**  For **every** point `p` of the run space — not merely almost every
  one; see the module docstring on why this is deliberately `∀ p` and not `All[…]` —
  `alg:ttc`'s charged cost `Ttc.ttcCost` (one `Vol_ED` call plus one `GenerateSamples`
  draw per returned point) is at most `Ttc.ttcNumCubes · (C_vol + C_sample · Ttc.ttcThresh)`,
  that is `m · (C_vol + C_sample · Thresh)`, under `Ttc.ttcTerminates`.

Eleven binders, all conditions on the input; only `hφ` and `hpos` are shape
hypotheses.  `AUDIT.md` §1h has the three preprocessing steps, what is known about
`hφ`/`hpos`, why `hbdd` is derived, and the definitional closure.  Correctness, not
efficiency: both oracle routes are exponential in `n`. -/
theorem ttc_volume_estimate {A : Type*} {n : ℕ}
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    -- (accuracy) `alg:ttc`'s own output on the run `p`, at the constructed oracle
    -- bundle, is within `(1 ± ε)·Vol(F)` with probability `≥ 1 − δ`
    (1 - δ ≤
      Pr[p ← ttcLaw atoms φ ε δ hε0 hε1 hn hφ hpos;
        ttcAlgOutput atoms φ ε δ hε0 hε1 hn (preprocess_bdd atoms φ hφ hpos)
              (ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos p.1 p.2)
            ∈ relErr ε (volSol (atomSet atoms) φ)])
    ∧
    -- (running time) `alg:ttc`'s charged cost, on **every** run `p`, under
    -- `Ttc.ttcTerminates` — pointwise, not almost everywhere
    (∀ p : (ℕ → Space n) × (ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ),
      ∀ cVol cSample thr : ℕ,
      (thr : ℝ) = ttcThresh atoms φ ε δ hε0 hε1 hn hφ hpos →
      ttcTerminates atoms φ ε δ hε0 hε1 hn hφ hpos p.1 p.2 →
      ttcCost atoms φ ε δ hε0 hε1 hn hφ hpos p.1 p.2 cVol cSample
        ≤ ttcNumCubes atoms φ * (cVol + cSample * thr)) :=
  ⟨ttc_accuracy_single_measure atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1,
    fun p => (ttc_volume_api atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos).2 p.1 p.2⟩

#print axioms ttc_volume_estimate

end Ttc
