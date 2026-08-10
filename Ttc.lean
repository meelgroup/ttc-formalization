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
  Exec/          the oracle-free capstones, and their plumbing (32)
  Rounding/      claim:cl, over the rounding that realises it  (11)
  Witness/       non-vacuity: the box, and the two-cube DNF     (8)
  Process/       lem:process, lem:chernoff, the level process   (7)
  Nonconv/       lem:nonconv                                    (6)
  Sampler/       GenerateSamples, interface and construction     (6)
  Volume/        Vol_ED, interface and construction              (6)
  Coupling/      the run realises the family; lem:numlattice     (5)
  Findings/      off the path: findings about the paper          (5)
  Monadic/       the run as one law on one space                 (5)
  Lattice/       thm:decomposition and lem:lattice               (4)
  Constants/     what ε', κ, γ are chosen to satisfy             (2)
  Audit/         the machine-checked audit-surface probes         (1)
  TtcProb, Access, Estimate, Invariants, Runtime, Dnf, Capstone,
  ModelSupport                                                    (8)
```

**Recount rather than quote.** These counts have drifted repeatedly and are a
snapshot (`find Ttc -name '*.lean' | sed 's|/[^/]*$||' | sort | uniq -c`, 109
files at the commit this paragraph was written). Only the `Model/` count is an
invariant; the rest are description.

### `Model/` — the statement

* `Ttc.Model.Prelude`        — the vocabulary: `ℝⁿ`, formula syntax and
  semantics, `sol` (= `Sol(F)`), the parameter block `Params`.
* `Ttc.Model.ProblemSetting` — the problem: `volSol` (= `Vol(F)`, what is
  estimated) and `relErr` (= the `(1±ε)` interval, how accurately). **Two
  definitions, no assumption.**
* `Ttc.Model.Pseudocode`     — `alg:ttc` and its preprocessing, transcribed line
  by line, ending in the algorithm's **output** `Ttc.ttcAlgOutput` over an oracle
  bundle and in `Ttc.ttcRun`, the same term with that bundle filled in from the
  run.  **The algorithm carries no proof binder**: `Ttc.Params` does bundle five
  proof fields, but `Ttc.ttcParamsTotal` decides all five side conditions
  classically, so `Ttc.ttcAlgOutput` and `Ttc.ttcRun` are closed functions of the
  data.  Not proof-free, though.  The criterion, which is stable in a way a count
  is not: a theorem stays here exactly when something the file *defines* cannot be
  written down without it — the run's own oracle bundle, whose `Ttc.Oracles`
  structure has two proof fields, or a `Classical.choose` the file then names.
  Such theorems are mostly invisible to `#modelClosure` (`closureAux` does not walk
  a theorem's value; the exception is `Ttc.exists_latticeEnum`, which a `def`'s body
  names) but load-bearing for elaboration, which is why they cannot move
  downstream.  What keeps the rest of them here is their *statements*: each mentions
  a definition of the file, and those definitions are in the measured closure.  The
  four whose statements survived losing that vocabulary — the count-vector
  dictionary and the `Set.ncard` enumeration lemma — are in `Ttc/ModelSupport.lean`,
  which `Model/Pseudocode` imports and whose docstring states what that import
  costs.  Everything else has been pushed out, and the residue is small and
  still shrinking — 6 theorems and no instance when this was last measured, down
  from 27; count it with
  `grep -cE '^(private )?theorem ' Ttc/Model/Pseudocode.lean` rather than quoting
  this sentence.  `AUDIT.md` §1h-iv lists them by group.

  **`Model/` is not a closed system, and no claim here should be read as saying
  so.**  `Model/Theorem` imports `Monadic/MeasurePr` and `Monadic/Program`, hence
  transitively the development, for the `Pr[…]`/`All[…]` notation it is stated in
  and for the bridge lemma its proof applies; `Model/Prelude` imports `Arlib`; and
  the exact set of files `Model/Pseudocode` pulls in has been re-cut more than once
  in a day.  Read the import lines, not this docstring.  What *is* machine-checked,
  and is the stronger claim anyway because it is about the **statement** rather
  than about imports: every `Ttc` constant the headline's type transitively unfolds
  to is defined under `Ttc/Model/` (see "the audit surface" below).
* `Ttc.Model.Theorem`        — the one theorem, `Ttc.ttc_volume_estimate`: the
                              guarantee over `TTC`'s own inputs `(atoms, φ, ε, δ)`
                              at **eleven binders** — `atoms φ ε δ hε0 hε1 hδ0 hδ1
                              hn hφ hpos`, the count every docstring here uses —
                              plus the two per-call cost constants `cVol cSample`,
                              so 13 explicit and 15 raw. Say which convention you
                              are quoting. No interpretation,
                              no parameter block, no converter, no oracle argument
                              and no precision argument (the precision is
                              `GetPrecision`'s output `P.precision gammaHat`).  Both
                              conjuncts are stated over **one law on one space** —
                              `Ttc.ttc` (`Model/Pseudocode`), the algorithm's own
                              law on runs `p = (volume coins, trajectory)`, with no
                              iterated integral — the accuracy one about the pair's
                              first component, which is `Model/Pseudocode`'s
                              transcription `Ttc.ttcRun` of `alg:ttc` at the
                              bundle the run itself supplies.  The
                              bundle version `Ttc.TtcProb.volume_estimate`, whose
                              type names the *assumed* `T.O` and `T.ρ`, is
                              `Ttc.Estimate`.  Which lemma discharged which former
                              binder is tabulated in `Ttc.Exec.Inputs`; why the last
                              one, `big`, **cannot** be discharged is proved in
                              `Ttc.Exec.Regime`.

Four files, and the count is an invariant rather than a description: `Model/` is
what a referee reads to trust the *statement* and the *algorithm*, so anything
that is neither belongs elsewhere. The test that has settled every borderline case
is declaration mix, not subject matter — a file carrying tactic proofs and a
witness chain fails it however relevant its contents are.

`Model/ProblemSetting` is held to a sharper form of the same rule, modelled on
`nfalean/ApproxNFA/Model/ProblemSetting.lean`: it states the **problem** — the
quantity the algorithm estimates and what "approximately" means — and carries no
hypothesis bundle at all. Everything that used to sit there has moved out,
unchanged in name, type and docstring:

* `structure Ttc.TtcProb` → **`Ttc/TtcProb.lean`**. 59 fields of hypotheses.
  It is the *abstract interface* (`CLAUDE.md` §1's layer 1), not the problem, so
  it is no longer in the audit surface; `Model/Theorem` quantifies over it.
* `Ttc.VolumeAlgorithm` and `Ttc.volGood` → `Ttc.Volume.Oracle`. Cousins–Vempala
  Theorem 1.1 as an interface, and the good event of the `m` `Vol_ED` calls —
  another paper's assumption bundle.
* `Ttc.KV97Sampler` → `Ttc.Sampler.Interface`. Kannan–Vempala's sampler as a
  construction — likewise another paper's.
* `Ttc.TtcProb.D`, `numCubes`, `cubeAt`, `volEvent` → `Ttc.Access`. Proof
  support: `def`s that *read* a `Ttc.TtcProb` rather than assume anything of it.

`volSol` and `relErr` moved the other way, *in* from `Model/Prelude`, since they
are the problem rather than vocabulary. The resulting order is
`Model/Prelude → Model/ProblemSetting → Volume/Oracle, Sampler/Interface →
Ttc/TtcProb → Ttc/Access`, and `Model/ProblemSetting` imports nothing but
`Model/Prelude`.

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
  bundle that reads a trajectory: the read-offs of `Model/Pseudocode`
  (`Ttc.trajThin`, `Ttc.trajPois`, `Ttc.trajGen`) packaged with the two
  *contracts* `thin_le` and `gen_card`.
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

* `Ttc.Exec.Endgoal` — `Ttc.ttc_volume`: `thm:volumettc` restated in the nfalean
  template, taking `(atoms, φ, ε, δ)` — the algorithm's own inputs — with the
  probability space, the parameters, `ρ`, `L` and the oracle bundle all
  *constructed*, and both halves of the guarantee in one conjunction. The residual
  obligations are visible `∀`-binders rather than invisible fields. This is the
  first rung of the chain the rest of `Exec/` climbs.
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
  slack enters `Ttc.Params.gamma` or `Ttc.Params.thresh`. It also carries the
  non-vacuity chain for its own capstone, ending in
  `Ttc.Box.exists_two_ttc_volume_endToEnd_canon_instances`.
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

Nothing the headline or the non-vacuity witness depends on imports these;
they are the formalisation acting as a referee on the paper, and are kept
deliberately and out of the audit surface.

* `Ttc.Findings.Repair` — `lem:nonconv` holds as the paper *states* it once the
  construction runs at internal parameter `θ = η/2`, at a cost of at most one
  decimal digit of precision (README finding 2).
* `Ttc.Findings.CubeLattice` — the paper's own per-polytope phrasing of
  `lem:lattice`, recovered from the global one proved here.
* `Ttc.Findings.Independence` — `hφ` and `hbdd` are logically independent, in both
  directions. This is why neither could be dropped in favour of the other while
  `hbdd` was still a binder; `hbdd` has since been *derived*, not weakened.
* `Ttc.Findings.OpenHalfspace` — what `hφ` is actually buying, and what removing it
  would cost: the negated-atom trade is exact for the volume and **not** for the
  lattice count or for boundedness (README finding 5).
* `Ttc.Findings.SmallBody` — on a body too small for the printed algorithm, the run
  returns `0`; the machine-checked half of the `hvol` story (§1g's dilation round).

`Findings/` is not the whole of what sits off the headline's import closure — the
audit companions, the two undischarged Cousins–Vempala files, the sibling
statements and `Audit/ClosureCheck` itself are off it too, each for a stated
reason. `README.md` carries the mechanical check and the annotated list; run it
rather than assuming this section is exhaustive.

**A hazard worth stating, because a green build does not reveal it.** The `Ttc`
lake library declares no `globs`: it is built by walking the imports of this
file. A `.lean` file under `Ttc/` that nothing imports is therefore **never
compiled at all**, so `lake build` reporting success says nothing whatever about
it — including whether it contains `sorry`. Any file added under `Ttc/` must be
imported here before its "green" means anything. The audit recipe in `AUDIT.md`
lists the current orphans; the `grep` sweep for `sorry` covers the whole tree
precisely because the build does not.

## The audit surface (`Model/`)

`Model/` is kept deliberately small: a referee who wants to trust the *statement*
reads the four files listed above and stops. Two things make that more than a
filing convention.

**It is machine-checked, for the statement.** `Ttc/Audit/ClosureCheck.lean`
defines `#modelClosure`/`#modelClosureOfType`, which walk a declaration's
definitional closure — through `def` bodies, through theorem *types* only — and
**throw** if any `Ttc` constant in it is defined outside `Ttc/Model/`. Four
invocations are live at the foot of that file, so a definition drifting out of
`Model/` fails `lake build`: `Ttc.ttcAlgOutput`, `Ttc.ttcRun`, `Ttc.ttc`, and the
headline's own type, `#modelClosureOfType Ttc.ttc_volume_estimate`. That last is
the reader-facing one — open `Model/`, and every constant the headline *means* is
defined in front of you. Sizes are reported by the non-failing `#closureReport`
variants; treat them as an alarm bell for the "outside `Model/`" tally beside
them, never as a size the files should be judged by.

**What it does not check.** Two things, and both matter:

* *Imports are not the closure.* `Model/Theorem` imports `Monadic/MeasurePr` and
  `Monadic/Program`, and so transitively the development, for the `Pr[…]`/`All[…]`
  notation the statement is written in and for the bridge lemma its proof applies.
  Notation is not a constant, which is why the closure is clean while the import
  graph is not.
* *Theorem values are invisible.* `closureAux` never walks a theorem's value
  (`ConstantInfo.value?` is `none` for theorems), so no proof term is in any
  closure report. That is the right notion for auditing a *statement* — a proof
  may use the product measure space; a statement that *names* it means something
  else — but it does mean the reports say nothing about what the proofs use.

`#closure`/`#closureOfType`, the stricter checks that forbid the statement naming
this development's own probability spaces, stay disabled — by construction rather
than by filing. `Ttc.ttc` **is** a measure, so its statement names measures; every
constant those checks flag is nonetheless defined under `Model/`.

Two per-file points not implied by the above: that `volSol` is the volume of the
right set is checked, for that symbol alone, in `Volume/VolSolCheck`; and
`Model/Theorem` binds **no oracle and no precision** — the bundle the run reads is
the closed term `Ttc.algOracles` (`Model/Pseudocode`) and every precision is
`P.precision gammaHat`, i.e. `GetPrecision`, `alg:ttc` line 17.

**The assumptions are not in `Model/`.** `Ttc.ttc_volume_estimate` quantifies
over inputs, not over a bundle; what it rests on *through the proof* are the 59
fields of `Ttc.TtcProb` (`Ttc/TtcProb.lean`), which the bundle-level
`Ttc.TtcProb.volume_estimate` (`Ttc/Estimate.lean`) quantifies over, plus
the two *other papers'* assumption bundles two of those fields name —
`Ttc.VolumeAlgorithm` (`Volume/Oracle`, Cousins–Vempala Theorem 1.1) and
`Ttc.KV97Sampler` (`Sampler/Interface`, Kannan–Vempala's sampler). Reading the
statement and reading the hypotheses are therefore two separate acts; `AUDIT.md`
§2 tabulates the fields with the `file:line` at which each is discharged.
`Ttc/TtcProb.lean` imports `Coupling/Family` and `Process/SketchProcess`, because
the sampler fields name the coupled Poisson family (`Ttc.trajLaw`,
`Ttc.trajOracles`, `Ttc.totalRate`) directly; those three definitions are part of
the hypothesis surface too.

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
import Ttc.Model.ProblemSetting
import Ttc.ModelSupport
import Ttc.Model.Pseudocode
import Ttc.Volume.Oracle
import Ttc.Sampler.Interface
import Ttc.TtcProb
import Ttc.Access
import Ttc.Estimate
import Ttc.Model.Theorem
import Ttc.Witness.Inputs
import Ttc.Witness.TwoCubeVol
import Ttc.Exec.Inscribed
import Ttc.Exec.Cleanup
import Ttc.Exec.Degenerate
import Ttc.Exec.CleanInput
import Ttc.Exec.Prune
import Ttc.Exec.BddFromPos
import Ttc.Exec.BddPrep
import Ttc.Exec.Api
import Ttc.Exec.Complexity
import Ttc.Witness.FullTwoCube
import Ttc.Witness.Headline
import Ttc.Exec.Endgoal
import Ttc.Exec.Params
import Ttc.Exec.Canonical
import Ttc.Exec.Geometry
import Ttc.Exec.Coverage
import Ttc.Exec.VolDischarge
import Ttc.Exec.EndToEnd
import Ttc.Exec.OracleFree
import Ttc.Exec.Budget
import Ttc.Exec.CanonPolytope
import Ttc.Exec.Final
import Ttc.Exec.CubeBounds
import Ttc.Exec.Dedup
import Ttc.Exec.Inputs
import Ttc.Exec.Regime
import Ttc.Exec.RegimeCube
import Ttc.Exec.RegimeSum
import Ttc.Exec.RegimeInputs
import Ttc.Exec.RegimeMain
import Ttc.Exec.Scale
import Ttc.Exec.ScaleFactor
import Ttc.Exec.Rescaled
import Ttc.Coupling.Product
import Ttc.Volume.Bridge
import Ttc.Volume.VolSolCheck
import Ttc.Volume.CousinsVempala
import Ttc.Volume.CVInstantiate
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
import Ttc.Process.Truncation

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
import Ttc.Exec.Statement

-- off the path to the theorem: findings about the paper
import Ttc.Findings.Repair
import Ttc.Findings.Independence
import Ttc.Findings.OpenHalfspace
import Ttc.Findings.SmallBody
import Ttc.Monadic.MeasurePr
import Ttc.Monadic.Kernel
import Ttc.Monadic.EventMeasurable
import Ttc.Monadic.Program
import Ttc.Audit.ClosureCheck
import Ttc.Findings.CubeLattice
import Ttc.Sampler.Contract
import Ttc.Sampler.Bridge
import Ttc.Sampler.Rates
import Ttc.Sampler.Construct
import Ttc.Sampler.RatesNonneg
import Ttc.Rounding.ArlibBridge
