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
  Model/         the statement — read this and stop            (5 files)
  Exec/          the oracle-free capstone, and its plumbing    (9)
  Sampler/       GenerateSamples, constructed                  (4)
  Volume/        Vol_ED, constructed                           (4)
  Invariants     structural facts about the modelled loop      (1)
  Constants/     what ε', κ, γ are chosen to satisfy           (2)
  Rounding/      claim:cl, over the rounding that realises it (11)
  Nonconv/       lem:nonconv                                   (6)
  Lattice/       thm:decomposition and lem:lattice             (4)
  Process/       lem:process, lem:chernoff, the level process  (6)
  Coupling/      the run realises the family; lem:numlattice   (5)
  Witness/       non-vacuity: the box [0,c]ⁿ                    (3)
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
* `Ttc.Model.Endgoal`        — the same result restated in the nfalean template:
  `Ttc.ttc_volume` takes `(atoms, φ, ε, δ)` — the algorithm's own inputs — with
  the probability space, the parameters, `ρ`, `L` and the oracle bundle all
  *constructed*, and both halves of the guarantee in one conjunction. The
  residual obligations are visible `∀`-binders rather than invisible fields.

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
* `Ttc.Witness.TwoCube` — **the witness for `Ttc.ttc_volume_final`**, and the only
  one whose DNF has more than one cube: `Ttc.TwoCube.card_toDNF_eq_two` proves it
  has *exactly* two. Two disjoint boxes `[0,c]ⁿ` and `[lo, lo+c]ⁿ`, with `lo` a
  lattice multiple so the second box contains a lattice point. It matters because
  every other witness in the development is the single-cube box, which never
  exercises `thm:decomposition`, the union bound across cubes, or the
  `cubeAt`-varies-with-the-point branch — a multi-cube statement could have been
  vacuous or wrong there and every single-cube witness would still have passed.
  `Ttc.TwoCube.sol_eq_union_two` proves the two regions distinct, nonempty and
  disjoint, and `Ttc.TwoCube.cenT_left_ne_right` that the inscribed-ball centres
  genuinely differ. **Not** proved, and not needed: additivity
  `volSol = Vol₁ + Vol₂`.

### `Exec/` — the oracle-free capstone

* `Ttc.Exec.Params`, `Ttc.Exec.Canonical`, `Ttc.Exec.Geometry`,
  `Ttc.Exec.Coverage` — the parameter block, the canonical probability space,
  and the geometric and covering data, all *constructed* rather than assumed.
* `Ttc.Exec.VolDischarge` — `Ttc.ttc_volume_monteCarlo`: the volume oracle
  eliminated, its coins integrated out against `Ttc.MonteCarlo.coins`.
* `Ttc.Exec.EndToEnd` — `Ttc.ttc_volume_endToEnd`: `thm:volumettc` with *no oracle
  hypothesis of any kind*. None of `volAlg`, `volCoins`, `vol`, `θ`, `theta_eq`,
  `gen_mem`, `sampD` or `sampler` is a binder. What remains are the algorithm's
  inputs, the input conditions, and a linear description of the input polytopes.
* `Ttc.Exec.CanonPolytope` — `Ttc.ttc_volume_endToEnd_canon`: that description
  discharged too. `M_eq` already says each `region M c` *is* a polytope presented
  by the rows `atoms l`, `l ∈ c`, so `Jt`, `Am`, `bv`, `hdil`, `rfac`, `hr1`,
  `hcard`, `Dm`, `hDbody` are all redundant. What is proved is stronger than
  `hdil` asks for — `Ttc.canon_body_eq_smul_region` is an **equality**, the
  described body *is* the dilated region — and `hcard` holds with equality, so no
  slack enters `Ttc.Params.gamma` or `Ttc.Params.thresh`.
* `Ttc.Exec.CanonicalPolytope` — **a second, independent derivation of the same
  elimination**, landed in parallel with `Exec/CanonPolytope` and kept because it
  is the one that carries a non-vacuity witness: `Ttc.ttc_volume_endToEnd_canonical`
  plus `Ttc.Box.exists_two_ttc_volume_endToEnd_canonical_instances`. Its
  `canonNormal`/`canonOffset`/`canonDiam` are renamed away from
  `Exec/CanonPolytope`'s `canonAm`/`canonBv`/`canonDm` so the two co-import; the
  key lemma `Ttc.body_canon_eq` is again an equality. **This duplication is debt**
  — an auditor should read `Exec/CanonPolytope` for the critical path (it is what
  `Exec/Final` consumes) and this file for the witness, and the two should be
  consolidated.
* `Ttc.Exec.Budget` — `Ttc.ttc_volume_endToEnd_delta`: the `δ`-repricing that
  turns `1 − δ − δ/4` into a clean `1 − δ`, by running at internal `δ₀ = 4δ/5`.
* `Ttc.Exec.Final` — **`Ttc.ttc_volume_final`**, the strongest result in the
  development and the one to read first: the two preceding steps composed. It
  takes `(atoms, φ, ε, δ)` and the input conditions, binds **no oracle and no
  polytope description**, and concludes `1 − δ` together with `alg:ttc`'s charged
  cost. 28 raw binders, every one an input or an input condition.

The two oracles are discharged by construction, not assumed:

* `Vol_ED` (`alg:ttc` line 24) — `Ttc.VolumeAlgorithm.monteCarlo`
  (`Ttc/Volume/MonteCarlo.lean`), a `VolumeAlgorithm n` with no hypotheses.
* `GenerateSamples` (`alg:ttc` line 43) — `Ttc.kv97SamplerOfBody`
  (`Ttc/Sampler/Construct.lean`), whose `law_tv` field is a *theorem*, proved
  from the ball walk's mixing time via
  `Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope`. The chain
  isoperimetry → conductance → Cheeger → L² decay → TV mixing is load-bearing,
  checked by a transitive dependency walk, not merely imported.

**Two scope caveats, stated here because they are what an auditor is most likely
to assume wrongly.**

*Cost.* Both constructions are **exponential in the dimension** — the Monte
Carlo volume estimator and the ball walk's step count alike. Unconditional and
efficient are independent claims; what is established is the first. `thm:runtime`
remains out of scope, as it is throughout.

*The sampler.* What is proved is that no *accuracy assumption* about the sampler
is made. It is **not** proved that the finite-time ball-walk iterate differs from
the uniform law on the inflated body; that needs an `L²`/aperiodicity argument
which is not in the development.

Non-vacuity is witnessed at two structurally different parameter pairs by
`Ttc.Box.exists_two_ttc_volume_endToEnd_instances`, with achieved bounds `3/8`
and `11/16`, both proved positive inside the statement — so the conclusion is not
the vacuously-true one. Note that `1 − δ − δ/4` is vacuous for `δ > 4/5`
(README finding 13a).

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

**A hazard worth stating, because a green build does not reveal it.** The `Ttc`
lake library declares no `globs`: it is built by walking the imports of this
file. A `.lean` file under `Ttc/` that nothing imports is therefore **never
compiled at all**, so `lake build` reporting success says nothing whatever about
it — including whether it contains `sorry`. Any file added under `Ttc/` must be
imported here before its "green" means anything. The audit recipe in `AUDIT.md`
lists the current orphans; the `grep` sweep for `sorry` covers the whole tree
precisely because the build does not.

## The audit surface (`Model/`)

`Model/` is kept deliberately small. A referee who wants to trust the *statement*
reads exactly these five files and stops. One caveat, since it used to be untrue
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
import Ttc.Model.Endgoal
import Ttc.Exec.Params
import Ttc.Exec.Canonical
import Ttc.Exec.Geometry
import Ttc.Exec.Coverage
import Ttc.Exec.VolDischarge
import Ttc.Exec.EndToEnd
import Ttc.Exec.Budget
import Ttc.Exec.CanonPolytope
import Ttc.Exec.CanonicalPolytope
import Ttc.Exec.Final
import Ttc.Coupling.Product
import Ttc.Volume.Bridge
import Ttc.Volume.VolSolCheck
import Ttc.Volume.CousinsVempala
import Ttc.Volume.MonteCarlo

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
import Ttc.Lattice.PerCube

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
import Ttc.Witness.BoxSharp
import Ttc.Witness.TwoCube

-- off the path to the theorem: findings about the paper
import Ttc.Findings.Repair
import Ttc.Findings.CubeLattice
import Ttc.Sampler.Contract
import Ttc.Sampler.Bridge
import Ttc.Sampler.Rates
import Ttc.Sampler.Construct
import Ttc.Rounding.ArlibBridge
