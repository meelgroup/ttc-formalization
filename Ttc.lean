/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

# Ttc — Lean formalisation of the `TTC` volume-estimation algorithm

Formalisation of the accuracy analysis of `TTC` from *Efficient Volume
Computation for SMT Formulas* (Shaw, Sarkar, Meel).

Importing `Ttc` pulls in the whole development. See `README.md` for how to build
and audit it, and for the statement-by-statement map from the paper to the Lean
declarations.

## Layout

* `Model/`    — **the audit surface** (see below): the vocabulary, the problem,
                the pseudocode, the assumptions, the statement. Read this and stop.
* `Analysis/` — the proof content, one file per piece of the paper's analysis:
                the arithmetic toolbox (`Arith`), `thm:decomposition`
                (`Decomposition`), what the constants buy (`Parameters`), the
                `lem:nonconv` chain (`Geometry`, `Recentred`, `Nonconv`,
                `Repair`), `claim:cl`'s concentration core (`Rounding`),
                `lem:lattice` (`Lattice`), `lem:process` (`Poisson`),
                `lem:numlattice`'s epoch skeleton (`Sketch`), the structural
                invariants of the modelled loop (`Invariants`), and the
                assembly (`Capstone`).

## The audit surface (`Model/`)

`Model/` is kept deliberately small and self-contained: nothing in it refers to a
definition outside `Model/` except Mathlib. A referee who wants to trust the
*statement* reads exactly these four files and stops:

* `Model/Prelude`        — the vocabulary (the ambient space `ℝⁿ`, formula syntax
                           and semantics, the parameter block `Params`), what
                           `Vol(F)` is (`volSol`), and **every assumption of the
                           result** as a field of `Ttc.TtcAnalysis`.
* `Model/ProblemSetting` — `thm:decomposition`: the set the algorithm enumerates
                           is the set the theorem bounds.
* `Model/Pseudocode`     — `alg:ttc`, transcribed line by line from `algo.tex`
                           over an oracle bundle, plus the faithfulness bridge
                           `Ttc.TtcAnalysis.IsOutputOf`; **no proofs**.
* `Model/Theorem`        — the headline `Ttc.TtcAnalysis.volume_estimate`: one
                           theorem, no proof to work through.

The headline is `sorry`-free and axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

**One scope caveat, stated here because it is the thing an auditor is most
likely to assume wrongly.** The link between `Ttc.run` (`Model/Pseudocode`) and
the `est` field of `Ttc.TtcAnalysis` (`Model/Prelude`) is a *hypothesis*,
`Ttc.TtcAnalysis.IsOutputOf` — proving it **is** `lem:numlattice`, which this
development assumes. `Ttc.TtcAnalysis.run_volume_estimate` states the guarantee
for `run` under that hypothesis, and `Ttc.exists_isOutputOf` shows it is
satisfiable; but nothing here shows it holds of the real algorithm. So
`Model/Pseudocode` documents the algorithm; it is not yet part of the trusted
base of the unconditional headline. See the README, "What is assumed".
-/

-- The audit surface (statement layer)
import Ttc.Model.Prelude
import Ttc.Model.ProblemSetting
import Ttc.Model.Pseudocode
import Ttc.Model.Theorem

-- The proof content
import Ttc.Analysis.Arith
import Ttc.Analysis.Decomposition
import Ttc.Analysis.Parameters
import Ttc.Analysis.Geometry
import Ttc.Analysis.Recentred
import Ttc.Analysis.Nonconv
import Ttc.Analysis.Repair
import Ttc.Analysis.Rounding
import Ttc.Analysis.Lattice
import Ttc.Analysis.Poisson
import Ttc.Analysis.Sketch
import Ttc.Analysis.Invariants
import Ttc.Analysis.Capstone
