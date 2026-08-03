# How to audit this formalisation

`lake build` being green and `#print axioms` returning
`[propext, Classical.choice, Quot.sound]` proves that the development has **no
holes**. Neither proves that it states the **right theorem about the right
object**. That check is human-only, and this file is designed to let you make it
in a few minutes without reading a single hard proof.

Everything you need is in [`Ttc/Model/`](Ttc/Model/) — four files, no proofs
worth the name. Nothing in `Model/` refers to a definition outside `Model/`
except Mathlib, so you never have to follow a name into `Analysis/` to find out
what it means.

---

## 1. Is the capstone about the real object?

Read only the **type** of one declaration — everything before the `:=`.

**[`Ttc.TtcProb.volume_estimate`](Ttc/Model/Theorem.lean#L41)** — `thm:volumettc`:

```lean
theorem Ttc.TtcProb.volume_estimate (T : TtcProb A n) :
    1 - T.δ ≤
      (T.μ {ω | ttcOutput T.P T.O T.fuel T.ρ T.D ω ∈ relErr T.ε (volSol T.M T.φ)}).toReal
```

*With probability at least `1 − δ`*, the algorithm's output lies in
`(1 ± ε)·Vol(F)`. Four things make that a claim rather than a shape:

* **The measured thing is the algorithm — with three deviations, listed below.**
  [`ttcOutput`](Ttc/Model/Pseudocode.lean#L152) is
  [`Ttc.run`](Ttc/Model/Pseudocode.lean#L146), the line-by-line transcription of
  `alg:ttc`, with the oracles drawn at `ω`. Read `Model/Pseudocode` against
  `sections/algo.tex`; the control flow is the whole algorithm and there is no
  second model it is quietly swapped for. **But the sampling interface is not
  verbatim**, and this is the one place where "the measured thing is the
  algorithm" needs qualifying:

  | Deviation | `algo.tex` | Here | Content? |
  | --- | --- | --- | --- |
  | `halve` indexed by level | line 33, 40 | `halve c j X` | **No.** `p` only decreases, so each level is halved at most once per run; indexing by level is a bijection with indexing by call. |
  | `pois` told the cube and level | line 38, 41 | `pois c i j λ` | **Yes.** |
  | `gen` told the cube and level | line 43 | `gen c i j N ρ` | **Yes.** |

  The last two are genuine: `GenerateSamples(P(cᵢ), Nᵢ, ρ)` and `Pois(t·p)` are
  *rate-blind* in the paper. They are level-aware here because `lem:numlattice`'s
  `Err(j)` must be an event about a level-`j` process coupled to the run, and a
  rate-blind sampler provably cannot realise that coupling — README finding 15.
  This is no longer a hypothetical: the coupling is now built, it uses the extra
  arguments, and — unlike in the previous version of this file — it is
  **load-bearing for the headline**.
  [`Ttc.trajOracles`](Ttc/Analysis/Coupling.lean#L393) is an `Ttc.Oracles` bundle
  answering every call by reading a trajectory of the level family,
  [`Ttc.card_run_eq_sum_traj`](Ttc/Analysis/RunCoupling.lean#L263) proves the run
  driven by it satisfies `|𝒳| = ∑ₛ ω(J)ₛ` pathwise, and the `oracle_eq` field of
  `Ttc.TtcProb` asserts that the instance's own oracles *are* that bundle.
  **An auditor should read the headline as being about a version of `TTC` whose
  sampler knows which epoch it is in, and whose randomness is the coupled
  Poisson/thinning family.** Whether that is the same algorithm is a judgement
  the reader must make; it is not a difference the machine can see.
* **The target is `Vol(F)`, not a surrogate.**
  [`Ttc.volSol M φ = (volume (sol M φ)).toReal`](Ttc/Model/Prelude.lean#L173) —
  Mathlib's Lebesgue measure of the set of real points satisfying the formula. No
  discretisation, no rational grid.
* **That set is what the algorithm enumerates.**
  [`Ttc.TtcProb.sol_eq_union`](Ttc/Analysis/Capstone.lean#L112) says
  `⋃ c ∈ T.D, region T.M c = sol T.M T.φ` — `thm:decomposition`, *proved* from the
  `isDNF` field via
  [`Ttc.sol_eq_iUnion_region`](Ttc/Analysis/Decomposition.lean#L112).
* **The interval is the paper's.**
  [`relErr ε b = Set.Icc ((1−ε)b) ((1+ε)b)`](Ttc/Model/Prelude.lean#L181), and
  `T.μ` is a probability measure (field `isProb`).

---

## 2. What is assumed? Read the fields of `TtcProb`

Every global hypothesis is a field of
[`Ttc.TtcProb`](Ttc/Model/ProblemSetting.lean#L39). There are no others: the
theorem quantifies over the structure and adds nothing — no side hypothesis, no
`variable`, no instance argument carrying content.

**No lemma of the paper is assumed outright any more.** `lem:lattice` used to be
two fields; it is now *proved*
([`Ttc.TtcProb.lattice_lo`](Ttc/Analysis/LatticeAssembled.lean#L222),
[`lattice_hi`](Ttc/Analysis/LatticeAssembled.lean#L227)) from the geometric
fields below, which are hypotheses about the **input**, not about the analysis.
`lem:numlattice` used to be one more; it is now *proved* too
([`Ttc.TtcProb.numlattice`](Ttc/Analysis/NumLattice.lean#L51)). What is still
assumed in its place is the strictly weaker `numlattice_union` — the *epoch
covering*, last row of the table, which mentions no accuracy and no `1 − δ`.

Each field's line number is a link; the whole structure is 100 lines of
declarations and docstrings, so reading it end to end is also an option.

| Field | Line | What it asserts | Status |
| --- | --- | --- | --- |
| `ε`, `δ`, `hε0`, `hε1`, `hδ0`, `hδ1` | [40](Ttc/Model/ProblemSetting.lean#L40)–[50](Ttc/Model/ProblemSetting.lean#L50) | `ε, δ ∈ (0,1]` | the theorem's own parameters |
| `atoms`, `M`, `M_eq` | [52](Ttc/Model/ProblemSetting.lean#L52)–[57](Ttc/Model/ProblemSetting.lean#L57) | each atom is a linear constraint `A x ≤ b`, and `M` interprets it as that half-space | **assumed of the input** — this is what "SMT(LRA)" means |
| `φ`, `D` | [59](Ttc/Model/ProblemSetting.lean#L59), [61](Ttc/Model/ProblemSetting.lean#L61) | the formula and its DNF | inputs |
| `isDNF` | [63](Ttc/Model/ProblemSetting.lean#L63) | `D` and `φ` agree on every Boolean assignment | **assumed** of the external `ToDNF`/AllSAT tool. `thm:decomposition` is *proved* from it |
| `isPositive` | [66](Ttc/Model/ProblemSetting.lean#L66) | no literal of `D` is negated | **assumed of the input** — see §4 and README finding 5 |
| `Ω`, `mΩ`, `μ`, `isProb` | [68](Ttc/Model/ProblemSetting.lean#L68)–[74](Ttc/Model/ProblemSetting.lean#L74) | a probability space for the algorithm's randomness | structure, not an assumption |
| `P`, `eps_eq`, `delta_eq`, `dim_eq` | [76](Ttc/Model/ProblemSetting.lean#L76)–[82](Ttc/Model/ProblemSetting.lean#L82) | the parameter block, run at the theorem's own `ε` and `δ` and in the ambient dimension | inputs + three ties that used to be missing |
| `cubes_le`, `facets_le` | [84](Ttc/Model/ProblemSetting.lean#L84), [86](Ttc/Model/ProblemSetting.lean#L86) | `m` bounds the number of cubes, `r` the number of facets | **assumed of the input**; the paper's `m`, `r` |
| `normal_ne_zero` | [88](Ttc/Model/ProblemSetting.lean#L88) | every facet's normal vector is nonzero | **assumed of the input**; a zero normal is not a facet |
| `O`, `fuel` | [90](Ttc/Model/ProblemSetting.lean#L90), [92](Ttc/Model/ProblemSetting.lean#L92) | the `ω`-indexed oracle bundle, the loop budget | inputs; see §4 on `O` and on `fuel` |
| `cen`, `gammaHat`, `hgammaHat`, `ball_subset` | [94](Ttc/Model/ProblemSetting.lean#L94)–[102](Ttc/Model/ProblemSetting.lean#L102) | each `P(cᵢ)` contains an `ℓ₂`-ball of radius `γ̂ > 0` about its own centre | **assumed of the input** — `lem:nonconv`'s own hypothesis, in the paper's words. The LP of `alg:prec` that computes `γ̂` is **not modelled** |
| `volume_ne_top` | [104](Ttc/Model/ProblemSetting.lean#L104) | each `P(cᵢ)` has finite volume | **assumed of the input** — the paper leaves it implicit |
| `ρ`, `rho_eq` | [107](Ttc/Model/ProblemSetting.lean#L107), [109](Ttc/Model/ProblemSetting.lean#L109) | the precision is `GetPrecision`'s output, `ρ = ⌈log₁₀(γ/γ̂)⌉` | `alg:prec` line 91, transcribed — and now **load-bearing**, see §4 |
| `gen_mem` | [114](Ttc/Model/ProblemSetting.lean#L114) | `GenerateSamples` returns points of `P(cᵢ) ∩ 𝕃ⁿ` | **assumed of the external sampler** — `Ttc.Oracles` fixes only *how many* it returns. Not distributional |
| `L`, `L_eq` | [117](Ttc/Model/ProblemSetting.lean#L117), [119](Ttc/Model/ProblemSetting.lean#L119) | `L` **is** `\|Sol(F) ∩ 𝕃ⁿ\|/10^(ρn)` ([`normalisedCount`](Ttc/Model/Prelude.lean#L166)) | definition, not an assumption |
| `numlattice_union` | [133](Ttc/Model/ProblemSetting.lean#L133) | the *epoch covering*: the failure event is covered by the `Err` epochs, the `Noise` overflow and the `m` `Vol_ED` calls, at some `j*` and `λ*` | **assumed** — the one remaining field of its kind, and the whole of §4. It asserts no accuracy and no `1 − δ`; those are *derived* (`Ttc.TtcProb.numlattice`). The bound it asserts is **proved** for the run driven by the coupled family ([`Ttc.traj_numlattice_le`](Ttc/Analysis/RunCoupling.lean#L685)), but not for an arbitrary `Ω`/`μ`/`O` |

The README's [What is assumed](README.md#what-is-assumed) says the same at
length, with the exact list of what *is* proved about each.

**Where the `δ` comes from.** It is not hand-waved. The covering plus the *proved*
sizes of the three contributions ([`Ttc.numlattice_failure_le`](Ttc/Analysis/SketchProcess.lean#L246),
at the algorithm's own `Thresh` and `δ'`) gives
`Pr[ output ∈ (1±ε/3)·L ] ≥ 1 − δ` ([`Ttc.TtcProb.numlattice`](Ttc/Analysis/NumLattice.lean#L51));
the deterministic chain shows that event is *contained in* the `(1±ε)·Vol(F)`
event; measure monotonicity does the rest. So the `δ` is earned — given the
covering, which is assumed.

Nothing anywhere here is about running time (`thm:runtime` is out of scope).

---

## 3. Is the theorem non-vacuous?

A `∀ (T : TtcProb A n), …` proves nothing if `TtcProb` is uninhabited.

[`Ttc.nonempty_ttcProb`](Ttc/Analysis/Capstone.lean#L252), witnessed by
[`Ttc.trivialProb`](Ttc/Analysis/Capstone.lean#L181): the empty DNF over an
unsatisfiable formula, on the one-point sample space with the Dirac measure —
`Vol(F) = 0`, `L = 0`, output `0`, so the failure event of `numlattice_union` is
*empty* ([`Analysis/Capstone.lean:229`](Ttc/Analysis/Capstone.lean#L229)) and the
covering holds with everything on the right to spare. It needs `1 ≤ n`, because
`Ttc.Params` requires a positive dimension and `dim_eq` ties it to the ambient
one.

`TtcProb` is the only hypothesis-bundling structure the capstone quantifies over.
(`Ttc.TtcAnalysis` in [`Analysis/Capstone`](Ttc/Analysis/Capstone.lean#L44) is an
internal device for the arithmetic, not part of the statement.) One further
hypothesis bundle exists but is **not** reached by the capstone — the
distributional contract [`Ttc.OracleLaws`](Ttc/Analysis/OracleLaws.lean#L63),
which nothing yet consumes; it too has a witness
([`Ttc.oracleLaws_trivialProb`](Ttc/Analysis/OracleLaws.lean#L96)), and it too is
the degenerate instance, where both fields hold vacuously because the run
consumes no draws at all
([`clockBound_trivialProb`](Ttc/Analysis/OracleLaws.lean#L89)).

**Read that witness before trusting it — it is DEGENERATE.** `trivialProb` has
the empty DNF: no cubes, no facets, no polytopes, `Sol(F) = ∅`, `Vol(F) = 0`,
`L = 0`, output `0`, `fuel = 0`, and a one-point sample space. Every geometric
field is therefore vacuously true, and the run it describes does nothing. It
establishes exactly one thing — that the fields are *mutually consistent*, so
the headline is not vacuous — and it must not be read as evidence that the
assumptions are satisfiable in an interesting case. **A non-degenerate witness is
outstanding**, and would be the natural next thing an auditor should ask for: a
genuine polytope (say the unit box) with a positive lattice count, exercising
`ball_subset`, `volume_ne_top` and `isPositive` non-trivially. §4 says why that
matters.

---

## 4. Where a name stands in for a proof

`#print axioms` cannot see a definition whose *name* claims more than its body
proves. These are the residual assumptions of that kind. None is hidden — each is
stated in the file that introduces it — but they are collected here because they
are exactly what a green build does not certify.

**The `numlattice_union` field is the one remaining assumption of this kind, and
it is STILL PRESENT.** It has not been deleted. What it asserts is the *epoch
covering* of `lem:numlattice`'s union bound — that the failure event is contained
in the `Err` epochs plus the `Noise` overflow plus the `Vol_ED` calls — and
nothing about accuracy or `δ`. The theorem is therefore *conditional*: what it
proves is that the covering, plus proved estimates, upgrades to a `(1±ε)`
guarantee about `Vol(F)` with the `δ` carried across intact. That upgrade is
proved end to end — `lem:lattice`, `lem:nonconv`, `claim:cl` and now
`lem:numlattice` itself ([`Ttc.TtcProb.numlattice`](Ttc/Analysis/NumLattice.lean#L51))
included.

**What is still missing is model identification, not mathematics.** Every
*estimate* the proof invokes is a theorem here, including the one the paper
imports from Soos et al.: `lem:chernoff` is proved from the Poisson moment
generating function upwards
([`Analysis/Chernoff`](Ttc/Analysis/Chernoff.lean)), as are both of its
applications, `lem:process`, the epoch series, and the `Vol_ED` failure budget
the paper omits. All four original obstacles to composing them into a statement
about `Ttc.run` are now cleared:

* ~~`Ttc.Oracles` cannot express independence.~~ **Fixed** — calls are now
  clock-indexed (see the note above), so independence is statable.
* ~~`lem:process` is only a pmf identity.~~ **Fixed** —
  [`Ttc.countLaw_eq_pi`](Ttc/Analysis/PoissonLaws.lean#L91) gives it as an
  identity of measures, with independence, thinning and superposition as
  corollaries.
* ~~The halvings form a stopping time.~~ **Resolved** — and reading the paper's
  invariant as conditioning turns out to be *false* (README finding 14). The
  correct non-adaptive reading is
  [`Ttc.levelLaw`](Ttc/Analysis/SketchProcess.lean#L55), and both branch
  estimates plus the whole `δ` budget are proved over it
  ([`numlattice_failure_le`](Ttc/Analysis/SketchProcess.lean#L246)).
* ~~The coupling is missing.~~ **Built** — README finding 15's construction now
  exists. [`Ttc.trajOracles`](Ttc/Analysis/Coupling.lean#L393) is an honest
  `Ttc.Oracles` bundle (both interface contracts discharged; `gen_card` holds
  unconditionally, via a never-taken filler branch) whose answers are read off a
  trajectory of the coupled level family
  ([`Ttc.trajLaw`](Ttc/Analysis/Coupling.lean#L209)). Driving the *real*
  `Ttc.run` off it, [`Ttc.card_run_eq_sum_traj`](Ttc/Analysis/RunCoupling.lean#L263)
  proves `|𝒳| = ∑ₛ ω(J)ₛ` **pathwise**, at the run's own stopping level `J`, on
  every nested trajectory — and nestedness holds almost surely
  ([`Ttc.trajLaw_ae_nested`](Ttc/Analysis/RunCoupling.lean#L592)). That is
  equality of random variables, which is strictly stronger than the equality in
  law `lem:process` supplies and is what the union bound actually needs.
  Assembling it with the transported level estimates,
  [`Ttc.traj_numlattice_le`](Ttc/Analysis/RunCoupling.lean#L685) proves
  `lem:numlattice`'s bound for that run outright, with a *smaller* right-hand
  side than the paper's (no `+ δ/2`, no factor `m`). **No probability claim is
  assumed in it**: its hypotheses are `hlo`/`hhi` (supplied by the already-proved
  `lem:lattice`), `hsmall`/`hrate` (conditions on `Thresh` and `vol`), and
  `hall`/`hcov` (the cubes cover the lattice points; the oracle's coverage test
  agrees with cube membership).

**So why does the field survive?** Because `traj_numlattice_le` is about the
trajectory model — the measure `trajLaw θ` on `ℕ → (Fin L → ℕ)`, and the oracle
bundle `trajOracles` — whereas `numlattice_union` quantifies over the arbitrary
`Ω`, `μ` and `O` a `Ttc.TtcProb` carries. Nothing yet says that a given problem
instance's randomness *is* that model. Discharging the field means adding
model-identification fields to `Ttc.TtcProb` and rebuilding the non-vacuity
witness (§3) against them. Until that lands, an auditor should read the headline
as conditional on the covering, exactly as before — the difference is that the
mathematics behind the covering is now proved rather than promised.

Two further things an auditor should not skip:

* **The oracle contract is stated but not consumed.**
  [`Ttc.OracleLaws`](Ttc/Analysis/OracleLaws.lean#L63) says what the primitives
  are supposed to do distributionally (`pois` is Poisson; `halve` thins each
  point's multiplicity `Binomial(·,½)`, independently across points), asserted
  only for the draws the run can reach
  ([`clockBound`](Ttc/Analysis/OracleLaws.lean#L44), justified by
  [`run_eq_of_agree_below`](Ttc/Analysis/OracleLaws.lean#L48)). No theorem here
  consumes it yet. Its only witness is the degenerate instance, where it holds
  because there are no draws.
* **Fuel adequacy.** Both loops return the current state when the budget runs
  out. `traj_numlattice_le` needs no hypothesis on `fuel`, because the coupling
  makes the output a function of whatever level the run reached and the `Err`
  estimate covers every level below the cap; the work is done instead by
  `hsmall`, that no cube's rate still triggers a halving at level `j*−1`. Any
  *other* route to discharging the field will need a fuel hypothesis, and the
  paper addresses neither.

**The geometric fields are hypotheses about the input, and they are real.**
`ball_subset`, `volume_ne_top`, `normal_ne_zero`, `isPositive`, `cubes_le`,
`facets_le` are not consequences of anything here; they are what the paper
assumes of the decomposition (`ball_subset` verbatim, the rest implicitly).
Two are worth staring at:
* `isPositive` **excludes negated atoms**, which the paper's algorithm does not.
  A negated atom denotes an *open* half-space, and on a facet hyperplane the
  lattice count of a set and of its closure differ — so this is not a technicality
  volume arguments wash out. See README finding 5. Concretely: `lem:lattice` is
  proved here for positive DNFs only.
* `volume_ne_top` is implied by `ball_subset` plus boundedness, which the paper
  never states. It is assumed rather than derived.

**`L` is now the lattice count, not a bare real.** The `L_eq` field pins it to
[`Ttc.normalisedCount`](Ttc/Model/Prelude.lean#L166) `= |Sol(F) ∩ 𝕃ⁿ|/10^(ρn)`,
and `lem:lattice` is proved about *that*. (Previously `L` was a free real related
to `Vol(F)` only by assumption; that gap is closed.)

**The non-vacuity witness is degenerate.** `trivialProb` has no cubes at all, so
`Vol(F) = 0`, `L = 0`, the output is `0`, and every geometric field holds
vacuously. It shows the fields are mutually consistent — it does *not* exhibit a
non-trivial formula on which the algorithm provably works. Do not read it as
evidence that the assumptions are satisfiable in an interesting case. A
non-degenerate witness is **outstanding**; see §3.

**The oracle bundle constrains almost nothing.**
[`Ttc.Oracles`](Ttc/Model/Pseudocode.lean#L76) has four external calls as fields.
Only two carry any hypothesis — [`halve_le`](Ttc/Model/Pseudocode.lean#L87)
(thinning returns a sub-multiset) and
[`gen_card`](Ttc/Model/Pseudocode.lean#L101) (`GenerateSamples` returns exactly
`N` points, for every precision `ρ`). Nothing in the *bundle* states that `vol`
is an `(1±ε')`-accurate volume estimate, that `pois c λ` is Poisson-distributed,
or that `halve c` keeps each element independently with probability ½. That is
deliberate: it is what makes the bundle inhabitable by
[`Ttc.trajOracles`](Ttc/Analysis/Coupling.lean#L393), the coupling. The
distributional statements live separately, in
[`Ttc.OracleLaws`](Ttc/Analysis/OracleLaws.lean#L63), which no theorem consumes
yet — so the invariants in `Analysis/Invariants` remain structural facts about
the modelled execution, not statements about the real algorithm's behaviour.

**The sampling interface is level-aware; the paper's is not.** §1 tabulates the
three deviations. Two of them (`pois`, `gen` receiving the cube and level) are
real: they change what the modelled algorithm is allowed to do. They are there
because README finding 15 shows the union bound over epochs needs a *pathwise*
coupling between the run and a level-`j` process, `lem:process` supplies only
equality *in law*, and a rate-blind sampler cannot bridge the two. The coupling
that consumes them now exists (above), which settles that the extra arguments are
*used*, not that a rate-blind version would be false. This is the single most
important thing on this page for a reader deciding how much the headline claims.

**The `clock` is not in the pseudocode.** `Ttc.SketchState` carries a counter of
oracle draws, and `halve`/`pois`/`gen` take it as their first argument. An
auditor comparing against `algo.tex` will not find it there. It is present
because an *unindexed* oracle cannot model fresh randomness: `halve` applied
twice to the same multiset would return the same answer, so a thinning that
happened to be a no-op would freeze `𝒳` forever. Read it as naming the draw, not
as algorithm state — `X` and `p` are the paper's state, `clock` is bookkeeping.

**The coupling's definitions carry proving lemmas, not just names.** This is the
part of the development most exposed to the "a `def` whose name claims more than
its body proves" failure, so each of the new names is listed here with the lemma
that earns it:

| `def` | What the name promises | Proved by |
| --- | --- | --- |
| [`Ttc.levelLaw`](Ttc/Analysis/SketchProcess.lean#L55) | the law of the level-`j` process | [`chainLaw_eq_levelLaw`](Ttc/Analysis/SketchProcess.lean#L105) — nested thinning from level `0` reproduces it at every `j` |
| [`Ttc.totalRate`](Ttc/Analysis/SketchProcess.lean#L63) | the total rate at level `j` | definitionally `(∑ θ)/2ʲ`; used only through that |
| [`Ttc.famCount`](Ttc/Analysis/Coupling.lean#L80), [`Ttc.trajLaw`](Ttc/Analysis/Coupling.lean#L209) | the coupled family and its law | [`map_trajLaw_eval`](Ttc/Analysis/Coupling.lean#L274) — coordinate `j` carries exactly `levelLaw θ j`; [`trajLaw_ae_nested`](Ttc/Analysis/RunCoupling.lean#L592) — it is a *nested* thinning |
| [`Ttc.trajOracles`](Ttc/Analysis/Coupling.lean#L393) | oracles that read the family | it is an `Ttc.Oracles`, so both interface contracts are discharged in the definition; that the *run* it drives realises the family is [`card_run_eq_sum_traj`](Ttc/Analysis/RunCoupling.lean#L263) |
| [`Ttc.CoupledAt`](Ttc/Analysis/RunCoupling.lean#L31), [`Ttc.PoisAt`](Ttc/Analysis/RunCoupling.lean#L150) | "the state is the family here" | preserved by every loop operation ([`coupledAt_step`](Ttc/Analysis/RunCoupling.lean#L183), [`coupledAt_foldl`](Ttc/Analysis/RunCoupling.lean#L241)) and read off by [`count_of_coupledAt`](Ttc/Analysis/RunCoupling.lean#L43) |
| [`Ttc.TtcProb.clockBound`](Ttc/Analysis/OracleLaws.lean#L44) | the draws the run can consume | [`run_eq_of_agree_below`](Ttc/Analysis/OracleLaws.lean#L48), from [`run_congr`](Ttc/Analysis/Invariants.lean#L395) |

The one place a name is doing work no lemma checks is
[`Ttc.padPoint`](Ttc/Analysis/Coupling.lean#L387), the filler `trajOracles.gen`
returns when asked for a count the family cannot supply. That branch is never
taken by the run — `gen` is always passed the `N` that `pois` produced — and
nothing downstream depends on what it contains; it exists so that `gen_card`
holds unconditionally.

**`GetPrecision` is a formula, not an algorithm — but it is no longer inert.**
`γ̂` is still an input: the LP of `alg:prec` that computes the largest inscribed
ball, and the loop taking the max over polytopes, are **not modelled**. What *is*
now proved is that the precision it returns is exactly what the accuracy proof
needs: [`Ttc.gamma_le_latticeScale_mul`](Ttc/Analysis/LatticeAssembled.lean#L69)
shows `ρ = ⌈log₁₀(γ/γ̂)⌉` makes `10^ρ·γ̂ ≥ γ`, which is what gives the *dilated*
polytopes the inscribed radius `lem:nonconv` requires. So `rho_eq` is
load-bearing: delete it and `lem:lattice` no longer goes through.

**The parameter block is a transcription, checkable only by eye.** The constants
in [`Ttc.Params`](Ttc/Model/Prelude.lean#L191) — `η`, `ε'`, `Thresh`, `κ`, `γ`,
`ρ` — assert by their definitions that they are what `alg:ttc` (lines 17–20) and
`alg:prec` (line 86) compute. Read them beside `sections/algo.tex`. Unlike
before, the *results about* them are now reached by the headline: `κ` and `γ`
enter `lem:lattice` through [`Ttc.Params.shell_factor_bound`](Ttc/Analysis/Parameters.lean#L102)
and [`shell_factor_bound_deflated`](Ttc/Analysis/Parameters.lean#L144), so
"the constants are verified" and "the main theorem holds" meet for `η`, `κ`, `γ`,
`ρ`. They now meet for `ε'` and `Thresh` as well: `Ttc.TtcProb.numlattice` reads
both off the parameter block and feeds them to
[`Ttc.numlattice_failure_le`](Ttc/Analysis/SketchProcess.lean#L246), which is what
turns the assumed covering into `1 − δ` — so that lemma, and with it the two
`Thresh` branches, is on the headline's dependency path. Re-check with the probe
in §5 rather than taking this on trust.

**Fuel, not termination.** Both `while` loops in `Model/Pseudocode` take an
explicit iteration budget and return the current state when it runs out. No
termination theorem is claimed, and claiming one would be false: the second loop
terminates only with high probability.

---

## 5. Re-checking the machine-checkable part

```bash
lake exe cache get && lake build     # zero "declaration uses 'sorry'" warnings
```

```lean
import Ttc
#print axioms Ttc.TtcProb.volume_estimate
-- [propext, Classical.choice, Quot.sound]
#print axioms Ttc.TtcProb.lattice_lo
-- [propext, Classical.choice, Quot.sound]
#print axioms Ttc.TtcProb.numlattice
-- [propext, Classical.choice, Quot.sound]
#print axioms Ttc.traj_numlattice_le
-- [propext, Classical.choice, Quot.sound]
```

```bash
# nothing (the `grep -v` drops the phrase "`sorry`-free" from two docstrings)
grep -rn "sorry\|admit\|native_decide\|sorryAx\|^axiom " Ttc.lean Ttc/ | grep -v '`sorry`'
```

See the README's [Verifying the claim](README.md#verifying-the-claim) for the
full-development axiom sweep.

**Checking §4's "which results does the headline actually reach" claim.** Paste
this into a file and `lake env lean` it; it walks the headline's transitive
constant set and reports membership.

```lean
import Ttc
open Lean in
run_cmd do
  let env ← Lean.getEnv
  let mut seen : Lean.NameSet := {}
  let mut todo := [`Ttc.TtcProb.volume_estimate]
  while !todo.isEmpty do
    let n := todo.head!; todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      for c in ci.getUsedConstantsAsSet do todo := c :: todo
  for t in [`Ttc.Params.shell_factor_bound, `Ttc.Params.shell_factor_bound_deflated,
            `Ttc.Params.kappa_div_gamma_le, `Ttc.gamma_le_latticeScale_mul,
            `Ttc.prodKernel_claim_cl_b, `Ttc.Params.epsPrime_window,
            `Ttc.numlattice_failure_le, `Ttc.traj_numlattice_le] do
    Lean.logInfo m!"{t} reached: {seen.contains t}"
```

Two of these answers matter for reading this page honestly.

* `Ttc.numlattice_failure_le` comes back **`true`**: it is what
  `Ttc.TtcProb.numlattice` uses to turn the assumed covering into `1 − δ`, so
  `Thresh` and `ε'` are on the headline's path.
* `Ttc.traj_numlattice_le` comes back **`false`**, and that is the honest
  statement of where things stand. `Analysis/RunCoupling` is not among
  `Model/Theorem`'s transitive imports at all: the coupling and the
  `lem:numlattice` bound proved over it are *not* consumed by the capstone. They
  are what will let `numlattice_union` be deleted, once `Ttc.TtcProb` carries the
  fields identifying its `Ω`/`μ`/`O` with the trajectory model. Until then, a
  reader must not read "the coupling is proved" as "the headline rests on it".
