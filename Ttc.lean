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
                `lem:lattice` (`Lattice`, `LatticeAssembled`), `lem:process`
                (`Poisson`, `PoissonLaws`, `Thinning`), `lem:numlattice`'s epoch
                skeleton (`Sketch`, `SketchProcess`, `Chernoff`), the coupled
                Poisson family and its identification with the run (`Coupling`,
                `RunCoupling`), `lem:numlattice` itself (`NumLatticeModel`,
                `NumLattice`), the structural invariants of the modelled loop
                (`Invariants`), the non-degenerate witness (`Witness`,
                `BoxProb`), and the assembly (`Capstone`).

## The audit surface (`Model/`)

`Model/` is kept deliberately small and self-contained: nothing in it refers to a
definition outside `Model/` except Mathlib. A referee who wants to trust the
*statement* reads exactly these four files and stops:

* `Model/Prelude`        — the vocabulary: the ambient space `ℝⁿ`, formula syntax
                           and semantics, the parameter block `Params`, `volSol`
                           (= `Vol(F)`) and `relErr` (= the `(1±ε)` interval).
* `Model/Pseudocode`     — `alg:ttc`, transcribed line by line from `algo.tex`
                           over an oracle bundle, and its output
                           `Ttc.ttcOutput`; **no proofs**.
* `Model/ProblemSetting` — `Ttc.TtcProb`, **every assumption** of the result as
                           fields: the input, the run, the probability space, and
                           the description of the sampler. That the set the
                           algorithm enumerates is the set the theorem bounds is
                           `thm:decomposition`, *proved* in
                           `Analysis/Capstone` (`Ttc.TtcProb.sol_eq_union`).
* `Model/Theorem`        — the headline `Ttc.TtcProb.volume_estimate`: one
                           theorem, no proof to work through.

The headline is `sorry`-free and axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

**One scope caveat, stated here because it is the thing an auditor is most
likely to assume wrongly.** `Ttc.TtcProb.volume_estimate` really does conclude
`Pr[ output ∈ (1±ε)·Vol(F) ] ≥ 1 − δ` about `Ttc.run`, with no side hypothesis —
`lem:lattice` *is* proved (`Ttc.TtcProb.lattice_lo`/`lattice_hi`) from the
geometric fields of `Ttc.TtcProb`, and `lem:numlattice` is **now proved too**
(`Ttc.TtcProb.numlattice`, via `Ttc.TtcProb.numlattice_union`) — it is no longer a
field. What it is proved *from* is the sampler description the structure now
carries: `law_eq`, `oracle_eq`, `rate_eq_L` and the epoch conditions, which say
the algorithm's randomness is the Poisson/thinning family of `Analysis/Coupling`.
So what remains assumed is a description of the sampler, not a bound on its
failure probability. `Ttc.Box.nonempty_ttcProb` shows the fields are jointly
satisfiable, and **non-degenerately**: the witness has a nonempty solution set and
`L ≥ Thresh`, so the headline is not vacuous in the weak sense the old degenerate
witness allowed. See the README, "What is assumed", and `AUDIT.md` §4. Running
time (`thm:runtime`) is out of scope throughout.
-/

-- The audit surface (statement layer)
import Ttc.Model.Prelude
import Ttc.Model.Pseudocode
import Ttc.Model.ProblemSetting
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
import Ttc.Analysis.Tent
import Ttc.Analysis.FacetOfDNF
import Ttc.Analysis.Lattice
import Ttc.Analysis.Poisson
import Ttc.Analysis.Chernoff
import Ttc.Analysis.PoissonLaws
import Ttc.Analysis.Thinning
import Ttc.Analysis.Coupling
import Ttc.Analysis.RunCoupling
import Ttc.Analysis.NumLatticeModel
import Ttc.Analysis.Witness
import Ttc.Analysis.BoxProb
import Ttc.Analysis.SketchProcess
import Ttc.Analysis.Sketch
import Ttc.Analysis.Invariants
import Ttc.Analysis.Cl
import Ttc.Analysis.PiLintegral
import Ttc.Analysis.ProdKernel
import Ttc.Analysis.ProdLaw
import Ttc.Analysis.TentSum
import Ttc.Analysis.RoundLaw
import Ttc.Analysis.RoundMoments
import Ttc.Analysis.ClB
import Ttc.Analysis.BallFacet
import Ttc.Analysis.NonconvAssembled
import Ttc.Analysis.LatticeAssembled
import Ttc.Analysis.CountVector
import Ttc.Analysis.Capstone
import Ttc.Analysis.OracleLaws
import Ttc.Analysis.NumLattice
