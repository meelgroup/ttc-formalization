/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.Api

/-!
# The main theorem: `thm:volumettc` + `thm:runtime` for `TTC(F, ε, δ)`

The **statement layer**, and nothing else: this file contains one theorem,
`Ttc.ttc_volume_estimate`, and no definition, no auxiliary lemma and no proof to work
through — the proof is one application of `Ttc.ttc_volume_api` (`Exec/Api`).

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

## What is measured: `Model/Pseudocode`'s own `Ttc.ttcAlgOutput`

The accuracy conjunct says, in one term,

```
Pr[ ttcAlgOutput atoms φ ε δ … (the run's oracle bundle) ∈ relErr ε (volSol (atomSet atoms) φ) ] ≥ 1 − δ
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
assumed: `Vol_ED` is the Monte-Carlo estimator `Ttc.mcVol` at the volume coins `c`,
and `GenerateSamples` is the ball-walk sampler at the sample coins `t`.  The target
is the **user's own** `Vol(F)`, at the original `φ`: neither preprocessing pass moves
it.

The runtime conjunct is stated in the folded vocabulary of `Exec/Api` —
`Ttc.ttcTerminates`, `Ttc.ttcCost`, `Ttc.ttcNumCubes`, `Ttc.ttcThresh` — each of
which unfolds by `rfl` to the corresponding term of `Runtime.lean`
(`Ttc.ttcTerminates_def`, `Ttc.ttcCost_def`, `Ttc.ttcNumCubes_def`,
`Ttc.ttcThresh_def`).

## What the statement names

This file is *one declaration* — no `def`, no auxiliary lemma — and the theorem's
type names, outside `Model/`, only

```
ttcRates  ttcIndex  ttcOracleBundle  trajLaw  MonteCarlo.coins
preprocess_bdd
ttcTerminates  ttcCost  ttcThresh  ttcNumCubes
```

The first line is **the constructed oracle bundle and the run's probability space**:
the rate vector the sample coins are drawn at, the index they range over, the bundle
itself, its law, and the volume coins' law.  These are outside `Model/` on purpose —
`alg:ttc` treats `Vol_ED` and `GenerateSamples` as oracle calls, so the *construction*
that discharges them is proof content, not statement content.  The last line is the
runtime conjunct's four folded names, each with its `rfl` lemma in `Exec/Api`.

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
bridge in the other direction, identifying the measured term with the run's estimate.

The fact that this theorem's proof is a bare application, with no rewriting, is the
structural check that the names above name what they claim to name: a wrong
abbreviation is a build error, not a silent divergence.

## What is assumed

Four things an auditor needs and this file deliberately does **not** restate, so
that it stays the statement:

* the **definitional closure** — what the named terms unfold to outside `Model/`
  (the `Exec/Api` auxiliaries, the constructed oracle bundle, the constructed
  sampler, the parameter block, and the run's probability space);
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

/-- **`thm:volumettc` + `thm:runtime`.**  `TTC` is run on `F = (atoms, φ)` at accuracy
`ε` and confidence `δ`.

* **Accuracy.**  `Pr[ TTC(F, ε, δ) ∈ (1 ± ε)·Vol(F) ] ≥ 1 − δ`, over the volume coins
  (law `Ttc.MonteCarlo.coins n`) and the sample coins (law `Ttc.trajLaw`).  The output
  is `Model/Pseudocode`'s own `Ttc.ttcAlgOutput` — the fold of `alg:ttc` lines 22–46
  at the computed parameter block and precision, rescaled by `1/qⁿ` — evaluated at the
  constructed oracle bundle `Ttc.ttcOracleBundle`, and the target is the **user's own**
  `Vol(F)`.
* **Running time.**  On every run, `alg:ttc`'s charged cost `Ttc.ttcCost` — one
  `Vol_ED` call plus one `GenerateSamples` draw per returned point — is at most
  `Ttc.ttcNumCubes · (C_vol + C_sample · Ttc.ttcThresh)`, that is
  `m · (C_vol + C_sample · Thresh)`, under `Ttc.ttcTerminates`.

Eleven binders, all conditions on the input; only `hφ` and `hpos` are shape
hypotheses.  `AUDIT.md` §1h has the three preprocessing steps, what is known about
`hφ`/`hpos`, why `hbdd` is derived, and the definitional closure.  Correctness, not
efficiency: both oracle routes are exponential in `n`. -/
theorem ttc_volume_estimate {A : Type*} {n : ℕ}
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    -- (accuracy) `alg:ttc`'s own output, at the constructed oracle bundle, is within
    -- `(1 ± ε)·Vol(F)` with probability `≥ 1 − δ`
    (1 - δ ≤
      (∫⁻ c, trajLaw (ttcRates atoms φ ε δ hε0 hε1 hn hφ hpos c)
          {t | ttcAlgOutput atoms φ ε δ hε0 hε1 hn (preprocess_bdd atoms φ hφ hpos)
                    (ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos c t)
                ∈ relErr ε (volSol (atomSet atoms) φ)}
        ∂(MonteCarlo.coins n)).toReal)
    ∧
    -- (running time) `alg:ttc`'s charged cost, on every run, under `Ttc.ttcTerminates`
    (∀ (c : ℕ → Space n) (t : ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ)
        (cVol cSample thr : ℕ),
      (thr : ℝ) = ttcThresh atoms φ ε δ hε0 hε1 hn hφ hpos →
      ttcTerminates atoms φ ε δ hε0 hε1 hn hφ hpos c t →
      ttcCost atoms φ ε δ hε0 hε1 hn hφ hpos c t cVol cSample
        ≤ ttcNumCubes atoms φ * (cVol + cSample * thr)) :=
  ttc_volume_api atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos

#print axioms ttc_volume_estimate

end Ttc
