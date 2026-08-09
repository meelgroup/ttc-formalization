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

Audit path — `Model/`, then stop: `Model/Prelude` (the vocabulary),
`Model/ProblemSetting` (what `Vol(F)` is and what `(1 ± ε)` means),
`Model/Pseudocode` (`alg:ttc`, transcribed line by line), this file.

`TTC` takes three inputs, so three inputs is what this statement takes: the formula
`F = (atoms, φ)`, the accuracy `ε`, the confidence `δ`.  **Eleven binders**

```
atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos
```

and among them there is no interpretation, no parameter block, no converter, no
oracle, no precision, no inscribed-ball data — and no boundedness hypothesis.

## What is measured: `Model/Pseudocode`'s own `Ttc.ttcOutput`

The accuracy conjunct is about `Ttc.ttcOutput` — the transcription of `alg:ttc` in
`Model/Pseudocode`, run on `Ttc.ttcInput atoms φ` (which is `Ttc.preprocess atoms φ`,
by `Ttc.ttcInput_eq_preprocess`) — divided by `Ttc.ttcScale ^ n`, the dilation factor
that lines A12–A13 of the preprocessing put in and this division takes back out.  So a
reader of the statement sees the transcribed algorithm being measured, not a wrapper
around it.  The runtime conjunct is likewise about `Ttc.runCost` and `Ttc.Terminates`
(`Runtime.lean`) directly.

**This trades away a property the file used to have.**  Previously every quantity
named by the headline — `Ttc.ttcEstimate`, `Ttc.ttcCost` and their five companions —
was *defined in this file*, so nothing the headline named had to be chased outside
`Model/`.  Those seven definitions now live in `Exec/Api.lean` (section `Measured`,
each with its identifying `rfl` lemma `Ttc.ttcEstimate_def` and friends), and the
statement below names `Exec/Api` abbreviations: `Ttc.ttcBlock`,
`Ttc.ttcOracleBundle`, `Ttc.ttcPrec`, `Ttc.ttcInput`, `Ttc.ttcScale`, plus the two
whose unfolding is a five-line wall of proof terms, `Ttc.ttcRates` and `Ttc.ttcIndex`.
What is bought with that is the paragraph above: the measured object is
`Model/Pseudocode`'s `Ttc.ttcOutput` itself.  `Ttc.ttcEstimate_eq_ttcOutput`
(`Exec/Api`, by `rfl`) is the bridge in the other direction, for anyone who prefers
the wrapper.

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

* **Accuracy.**  `Pr[ output ∈ (1 ± ε)·Vol(F) ] ≥ 1 − δ`, over the volume coins (law
  `Ttc.MonteCarlo.coins n`) and the sample coins (law `Ttc.trajLaw`).  The output is
  `Model/Pseudocode`'s `Ttc.ttcOutput` on the preprocessed input, divided by the
  dilation factor `Ttc.ttcScale ^ n`, and the target is the **user's own** `Vol(F)`.
* **Running time.**  On every run, `alg:ttc`'s charged cost `Ttc.runCost` — one
  `Vol_ED` call plus one `GenerateSamples` draw per returned point — is at most
  `m · (C_vol + C_sample · Thresh)`, under `Ttc.Terminates`.

Eleven binders, all conditions on the input; only `hφ` and `hpos` are shape
hypotheses.  `AUDIT.md` §1h has the three preprocessing steps, what is known about
`hφ`/`hpos`, why `hbdd` is derived, and the definitional closure.  Correctness, not
efficiency: both oracle routes are exponential in `n`. -/
theorem ttc_volume_estimate {A : Type*} {n : ℕ}
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    -- (accuracy) `alg:ttc`'s own output, rescaled, is within `(1 ± ε)·Vol(F)` with
    -- probability `≥ 1 − δ`
    (1 - δ ≤
      (∫⁻ c, trajLaw (ttcRates atoms φ ε δ hε0 hε1 hn hφ hpos c)
          {t | ttcOutput (ttcBlock atoms φ ε δ hε0 hε1 hn hφ hpos)
                    (ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos c) toDNFd
                    (ttcPrec atoms φ ε δ hε0 hε1 hn hφ hpos) (ttcInput atoms φ) t
                  / (ttcScale atoms φ ε δ hε0 hε1 hn hφ hpos) ^ n
                ∈ relErr ε (volSol (atomSet atoms) φ)}
        ∂(MonteCarlo.coins n)).toReal)
    ∧
    -- (running time) `alg:ttc`'s charged cost, on every run, under `Ttc.Terminates`
    (∀ (c : ℕ → Space n) (t : ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ)
        (cVol cSample thr : ℕ),
      (thr : ℝ) = (ttcBlock atoms φ ε δ hε0 hε1 hn hφ hpos).thresh →
      Terminates (ttcBlock atoms φ ε δ hε0 hε1 hn hφ hpos)
          (ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos c t)
          (toDNFd (ttcInput atoms φ)) →
      runCost (ttcBlock atoms φ ε δ hε0 hε1 hn hφ hpos)
          (ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos c t) cVol cSample
          (ttcPrec atoms φ ε δ hε0 hε1 hn hφ hpos) (toDNFd (ttcInput atoms φ))
        ≤ (toDNFd (ttcInput atoms φ)).length * (cVol + cSample * thr)) :=
  ttc_volume_api atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos

#print axioms ttc_volume_estimate

end Ttc
