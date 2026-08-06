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

`Model/` is **the audit surface**: the vocabulary, the pseudocode, the
assumptions, the statement. Read it and stop. Everything else is the proof
content, one directory per object of the paper it discharges:

```
Ttc/
  Model/         the statement — read this and stop            (4 files)
  Invariants     structural facts about the modelled loop      (1)
  Constants/     what ε', κ, γ are chosen to satisfy           (2)
  Rounding/      claim:cl, over the rounding that realises it (10)
  Nonconv/       lem:nonconv                                   (6)
  Lattice/       thm:decomposition and lem:lattice             (3)
  Process/       lem:process, lem:chernoff, the level process  (6)
  Coupling/      the run realises the family; lem:numlattice   (4)
  Witness/       non-vacuity: the box [0,c]ⁿ                    (2)
  Capstone       the two chains combined                       (1)
  Findings/      off the path: findings about the paper        (2)
```

### `Model/` — the statement

* `Ttc.Model.Prelude`        — the vocabulary: `ℝⁿ`, formula syntax and
  semantics, the parameter block `Params`, `volSol` (= `Vol(F)`), `relErr`.
* `Ttc.Model.Pseudocode`     — `alg:ttc`, transcribed line by line, and its
  output `Ttc.ttcOutput`. **No proofs.**
* `Ttc.Model.ProblemSetting` — `Ttc.TtcProb`: every assumption, as fields.
* `Ttc.Model.Theorem`        — the one theorem, `Ttc.TtcProb.volume_estimate`.

### `Constants/` — what the algorithm's constants buy

* `Ttc.Constants.Arith` — `claim:helper` and every `ε`/`η` inequality the rest
  consumes.
* `Ttc.Constants.Parameters` — what `ε'`, `κ`, `γ` are chosen to satisfy.

### `Rounding/` — `claim:cl`, over the rounding that realises it

* `Ttc.Rounding.Hoeffding` — the concentration core, Hoeffding at the paper's `κ`.
* `Ttc.Rounding.Tent`, `Ttc.Rounding.TentSum`, `Ttc.Rounding.PiLintegral`,
  `Ttc.Rounding.ProdKernel`, `Ttc.Rounding.ProdLaw`, `Ttc.Rounding.RoundLaw`,
  `Ttc.Rounding.RoundMoments` — independent coordinatewise randomized rounding,
  built from the displacement density `1 − |u|` up to its law on `ℤⁿ`.
* `Ttc.Rounding.Cl`, `Ttc.Rounding.ClB` — `claim:cl` (a), (b), (c) discharged.

### `Nonconv/` — `lem:nonconv`, volume versus lattice count for one polytope

* `Ttc.Nonconv.Geometry`, `Ttc.Nonconv.BallFacet`, `Ttc.Nonconv.FacetOfDNF` —
  facet systems, the inscribed-ball ↔ facet correspondence, and the facet system
  of a positive-literal DNF.
* `Ttc.Nonconv.Recentred`, `Ttc.Nonconv.Core`, `Ttc.Nonconv.Assembled` — the
  recentring, the chain, and the chain over an actual facet system.

### `Lattice/` — `thm:decomposition` and `lem:lattice`, for `Sol(F)`

* `Ttc.Lattice.Decomposition` — `thm:decomposition`.
* `Ttc.Lattice.Transport`, `Ttc.Lattice.Assembled` — the transport
  `ℤⁿ ↔ 𝕃ⁿ`, and `lem:lattice` for `Sol(F)`, where `GetPrecision` becomes
  load-bearing.

### `Process/` — `lem:process`, `lem:chernoff`, and the level process

* `Ttc.Process.Poisson`, `Ttc.Process.PoissonLaws`, `Ttc.Process.Thinning` —
  Poisson splitting, thinning and superposition, as identities of measures.
* `Ttc.Process.Chernoff`, `Ttc.Process.SketchProcess`, `Ttc.Process.Sketch` —
  the tail bound, the level-`j` process, and `lem:numlattice`'s epoch skeleton.

### `Invariants` and `Coupling/` — the run, and `lem:numlattice`

* `Ttc.Invariants` — the structural facts about the modelled loop: the
  exit levels, and what `𝒳` can contain.
* `Ttc.Coupling.Family` — the coupled level family, its law, and the oracle
  bundle that reads a trajectory.
* `Ttc.Coupling.Run` — the run **is** the family, pathwise; the halving
  triggers; `lem:numlattice`'s bound proved for the coupled run.
* `Ttc.Coupling.Transfer`, `Ttc.Coupling.NumLattice` — that bound
  transported to an arbitrary `Ω`/`μ`/`O`, and `lem:numlattice` as a theorem.

### `Capstone` and `Witness/` — assembly and non-vacuity

* `Ttc.Capstone` — the two chains combined.
* `Ttc.Witness.Box`, `Ttc.Witness.BoxProb` — the box `[0,c]ⁿ` and the
  non-degenerate `Ttc.TtcProb` built on it, `Ttc.Box.nonempty_ttcProb`.

### `Findings/` — off the path to the theorem

Nothing the headline or the non-vacuity witness depends on imports these two;
they are the formalisation acting as a referee on the paper, and are kept
deliberately and out of the audit surface.

* `Ttc.Findings.Repair` — `lem:nonconv` holds as the paper *states* it once the
  construction runs at internal parameter `θ = η/2`, at a cost of at most one
  decimal digit of precision (README finding 2).
* `Ttc.Findings.CubeLattice` — the paper's own per-polytope phrasing of
  `lem:lattice`, recovered from the global one proved here.

Every other module is on the path, checked mechanically against the import graph
rather than by eye; the recipe is in `README.md`.

## The audit surface (`Model/`)

`Model/` is kept deliberately small. A referee who wants to trust the *statement*
reads exactly these four files and stops. One caveat, since it used to be untrue
and no longer is: `Model/ProblemSetting` now imports `Coupling/Family` and
`Process/SketchProcess`, because the sampler fields name the coupled Poisson
family (`Ttc.trajLaw`, `Ttc.trajOracles`, `Ttc.totalRate`) directly. Those three
definitions are therefore part of the audit surface too.

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
                           `Capstone` (`Ttc.TtcProb.sol_eq_union`).
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
the algorithm's randomness is the Poisson/thinning family of `Coupling/Family`.
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

-- The modelled loop, and what a run costs
import Ttc.Invariants
import Ttc.Runtime
import Ttc.Dnf

-- What the constants buy
import Ttc.Constants.Arith
import Ttc.Constants.Parameters

-- claim:cl, and the rounding that realises it
import Ttc.Rounding.Hoeffding
import Ttc.Rounding.Tent
import Ttc.Rounding.TentSum
import Ttc.Rounding.PiLintegral
import Ttc.Rounding.ProdKernel
import Ttc.Rounding.ProdLaw
import Ttc.Rounding.RoundLaw
import Ttc.Rounding.RoundMoments
import Ttc.Rounding.Cl
import Ttc.Rounding.ClB

-- lem:nonconv
import Ttc.Nonconv.Geometry
import Ttc.Nonconv.BallFacet
import Ttc.Nonconv.FacetOfDNF
import Ttc.Nonconv.Recentred
import Ttc.Nonconv.Core
import Ttc.Nonconv.Assembled

-- thm:decomposition and lem:lattice
import Ttc.Lattice.Decomposition
import Ttc.Lattice.Transport
import Ttc.Lattice.Assembled

-- lem:process, lem:chernoff, the level process
import Ttc.Process.Poisson
import Ttc.Process.PoissonLaws
import Ttc.Process.Chernoff
import Ttc.Process.Thinning
import Ttc.Process.SketchProcess
import Ttc.Process.Sketch

-- the coupling, and lem:numlattice
import Ttc.Coupling.Family
import Ttc.Coupling.Run
import Ttc.Coupling.Transfer
import Ttc.Coupling.NumLattice

-- assembly and non-vacuity
import Ttc.Capstone
import Ttc.Witness.Box
import Ttc.Witness.BoxProb

-- off the path to the theorem: findings about the paper
import Ttc.Findings.Repair
import Ttc.Findings.CubeLattice
