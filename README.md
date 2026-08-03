# A Lean 4 formalisation of *Efficient Volume Computation for SMT Formulas*

Machine-checked, `sorry`-free, axiom-clean formalisation of the analysis of the
`TTC` algorithm (Shaw, Sarkar, Meel), following the methodology in
[`CLAUDE.md`](CLAUDE.md).

**Every declaration in this development is proved.** There is no `sorry`, no
custom `axiom`, and no `native_decide` (see
[Verifying the claim](#verifying-the-claim)). **No lemma of the paper is assumed
outright any more.** `lem:lattice` used to be two fields of `Ttc.TtcProb` and is
now proved from hypotheses about the *input*
([`lattice_lo`](Ttc/Analysis/LatticeAssembled.lean#L222),
[`lattice_hi`](Ttc/Analysis/LatticeAssembled.lean#L227)); `lem:numlattice` used
to be one field, then a weaker `numlattice_union` field, and **both are now
theorems** ([`Ttc.TtcProb.numlattice`](Ttc/Analysis/NumLattice.lean#L53),
[`Ttc.TtcProb.numlattice_union`](Ttc/Analysis/NumLatticeModel.lean#L267) — the
latter with the deleted field's statement verbatim).

**What is assumed in their place is a description of the sampler, not a bound on
its failure probability.** `Ttc.TtcProb` carries 19 fields
([`Model/ProblemSetting.lean:133`](Ttc/Model/ProblemSetting.lean#L133) onwards)
saying *what the algorithm's randomness is*: the lattice points are enumerated
(`Lidx`, `ptE`, `ptE_inj`) with rates `θ`, each `ω` reads as a trajectory
(`toTraj`) whose law **is** the coupled Poisson/thinning family
(`law_eq : μ.map toTraj = trajLaw θ`), the oracles read that trajectory
(`oracle_eq : O ω = trajOracles …`), the cubes cover the enumerated points
(`cover_eq`, `cover_all`), each cube's rate is the total level-`0` rate of the
points that cube covers ([`vol_eq`](Ttc/Model/ProblemSetting.lean#L165),
[`vol_pos`](Ttc/Model/ProblemSetting.lean#L167)), the instance is big enough for
the sketch to be worth running ([`big`](Ttc/Model/ProblemSetting.lean#L172)), and
the rates reproduce the count (`rate_eq_L : ∑θ = L`). That is a real reduction —
an assumed *conclusion* about probabilities has been replaced by an assumed
*description* of the algorithm's randomness, and everything quantitative is now
derived from it — but it is **not zero**: a reader who doubts that the modelled
sampler is the implemented one doubts the headline. See §[What is
assumed](#what-is-assumed).

**The epoch index `j*` is no longer assumed either.** It used to be a *field*:
an instance had to hand over a chosen epoch together with both ends of its rate
window (`jstar`, `hjstar`, `rate_small`, `rate_le`, `lamStar_ge` — five fields,
all now deleted). `j*` is now **constructed** inside
[`Ttc.TtcProb.numlattice_union`](Ttc/Analysis/NumLatticeModel.lean#L267) by
[`Ttc.exists_epoch`](Ttc/Analysis/NumLatticeModel.lean#L140), which proves such
an index always exists: the window `[(1−ε')·Thresh/8, Thresh/2]` has ratio at
least `4`, so halving from `∑θ` cannot step over it. Removing a *chosen
existential* from a hypothesis bundle is a stronger move than removing an
inequality — the instance no longer gets to pick the epoch the estimate is run
at. Two theorems make that possible and are new:
[`Ttc.TtcProb.thresh_pos`](Ttc/Analysis/NumLatticeModel.lean#L242), which derives
`Thresh > 0` from the algorithm's own formula rather than leaving it implicit
(`δ ≤ 1` forces `log(24/δ) ≥ log 24 > 0`, and `ε' = ε/12 ∈ (0, 1/12]` keeps
`(1−ε')ε'²` positive), and
[`Ttc.TtcProb.vol_le_total`](Ttc/Analysis/NumLatticeModel.lean#L260), which says
each cube's rate is at most the total because `vol_eq` sums a subset of
nonnegative rates. The old `rate_small` field is then *derived* from `vol_pos`
plus `vol_le_total` plus the epoch bound, via
[`Ttc.rate_small_of_epoch`](Ttc/Analysis/NumLatticeModel.lean#L180) (generalised
to take a cube rate merely *bounded by* the total rather than equal to it).

**And `vol` is no longer a free function.** Before, nothing tied the volume
estimates the run consumes to anything — `rate_small` was the only field standing
between `vol` and nonsense.
[`vol_eq`](Ttc/Model/ProblemSetting.lean#L165) now pins each cube's rate to the
total level-`0` rate of the points that cube covers, which is what the algorithm
actually means by it. That is a gap the simplification **closed**, not a rename.

The construction those fields point at is README
[finding 15](#15-genuine-gap--errj-is-not-a-well-defined-event)'s missing
coupling, which the paper never builds: for the epoch union bound to *mean*
anything, the run and the level process must agree **pathwise**, and
`lem:process` gives only equality in law.
[`Ttc.trajOracles`](Ttc/Analysis/Coupling.lean#L393) drives the real `Ttc.run` off
a trajectory of the level family, [`Ttc.card_run_eq_sum_traj`](Ttc/Analysis/RunCoupling.lean#L263)
proves `|𝒳| = ∑ₛ ω(J)ₛ` pathwise at the run's own stopping level `J` (with
[`trajLaw_ae_nested`](Ttc/Analysis/RunCoupling.lean#L592) discharging its one
hypothesis almost surely), and
[`Ttc.traj_numlattice_le`](Ttc/Analysis/RunCoupling.lean#L685) proves
`lem:numlattice`'s bound outright for that run. **That coupling is now
load-bearing for the headline**, not a side development:
[`Ttc.numlattice_union_of_model`](Ttc/Analysis/NumLatticeModel.lean#L35)
transports it off the trajectory space onto an arbitrary `Ω`/`μ`/`O` given the
sampler fields, and that is what proves `numlattice_union`.

Formalising also acted as a referee: it turned up **two genuine errors** and
**three genuine gaps** in the published proofs, all of them machine-checked —
three repaired, one closed by an added hypothesis, one shown to be absorbed by
existing slack, and the last (finding 15) closed by the construction above.
See [Findings](#findings-the-formalisation-as-a-referee).

**Auditing this in a few minutes:** read [`AUDIT.md`](AUDIT.md), then the four
files of [`Ttc/Model/`](Ttc/Model/). That is the whole trusted surface — what is
claimed, about what object, under what assumptions — and nothing in it refers to
a definition outside `Model/` except Mathlib. `Ttc/Analysis/` holds the proofs.

## Build

```bash
lake exe cache get     # do not compile Mathlib from source
lake build
```

Pinned to `leanprover/lean4:v4.32.0` and Mathlib `v4.32.0`
(`lean-toolchain`, `lakefile.toml`).

> This checkout reuses a sibling project's Mathlib package directory via a
> symlink at `.lake/packages` (see `CLAUDE.md` §13). If you clone it standalone,
> delete that symlink and run `lake update && lake exe cache get`.

## Verifying the claim

`#print axioms` is authoritative — `grep` is not (`sorry` elaborates to the
`sorryAx` axiom, and only `#print axioms` walks the transitive dependency tree).

```lean
import Ttc
#print axioms Ttc.TtcProb.volume_estimate
-- 'Ttc.TtcProb.volume_estimate' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
```

The declarations worth checking individually — the headline, the two statements
that used to be assumed fields, and the non-degenerate witness — all return
exactly those three:

```lean
#print axioms Ttc.TtcProb.volume_estimate
#print axioms Ttc.TtcProb.numlattice
#print axioms Ttc.TtcProb.numlattice_union
#print axioms Ttc.TtcProb.thresh_pos
#print axioms Ttc.TtcProb.vol_le_total
#print axioms Ttc.Box.boxProb
#print axioms Ttc.Box.nonempty_ttcProb
```

Those three are Mathlib's standard foundational axioms. A sweep over **every**
declaration in the development (upwards of 600 of them: theorems, definitions and
structures) shows that **no declaration depends on anything else** — no `sorryAx`,
no custom `axiom`. (The per-profile counts previously tabulated here are omitted:
the declaration set changes with every landed lemma and the numbers went stale.
Re-derive them with the sweep below rather than trusting a table.)

To reproduce the sweep:

```bash
{ echo "import Ttc"; \
  grep -h "^theorem \|^noncomputable def \|^def " Ttc/Model/*.lean Ttc/Analysis/*.lean \
  | sed 's/^[a-z ]*def /#print axioms Ttc./; s/^theorem /#print axioms Ttc./' \
  | cut -d" " -f1-3; } > /tmp/Ax.lean
lake env lean /tmp/Ax.lean | grep -v "Classical.choice"
```

(The one-liner above misses declarations inside `namespace FacetSystem` /
`namespace Params` / `namespace TtcProb`; prefix those by hand, or just trust
`lake build`, which emits **zero** `declaration uses 'sorry'` warnings.)

As a cheap third check:

```bash
grep -rn "sorry\|admit\|native_decide\|sorryAx\|^axiom " Ttc.lean Ttc/ | grep -v '`sorry`'
```

returns nothing.

## Module map

A small, self-contained **audit surface** (`Ttc/Model/`) plus the proofs it rests
on (`Ttc/Analysis/`). To check *what is claimed* you read only `Model/`; nothing
in it refers to a definition outside `Model/` except Mathlib.

```
Ttc.lean                      -- imports everything; layout docstring
Ttc/
  Model/                      -- THE AUDIT SURFACE — read this and stop
    Prelude.lean              -- definitions only: ℝⁿ, formula syntax/semantics, the Params
                              --   block, volSol (= Vol(F)), relErr (= the (1±ε) interval)
    Pseudocode.lean           -- alg:ttc line by line, and its output ttcOutput
    ProblemSetting.lean       -- TtcProb: the problem, the run, every assumption as fields
    Theorem.lean              -- thm:volumettc: Pr[out ∈ (1±ε)Vol(F)] ≥ 1−δ — one theorem
  Analysis/                   -- the proof content
    Arith.lean                -- claim:helper and every ε/η inequality
    Decomposition.lean        -- thm:decomposition; convexity of a cube's region
    Parameters.lean           -- what ε', κ, γ are chosen to satisfy
    Geometry.lean             -- facet systems; which facet attains k
    Recentred.lean            -- cl:recenter, the shell bound (instantiated), lem:nonconv
                              --   without a common ball
    Nonconv.lean              -- lem:nonconv skeleton + the summation steps consuming claim:cl
    Repair.lean               -- lem:nonconv at internal parameter θ = η/2
    Rounding.lean             -- claim:cl's concentration core (Hoeffding at the paper's κ)
    FacetOfDNF.lean           -- the facet system of a positive-literal DNF; Q = Sol(F)
    Cl.lean                   -- claim:cl (a),(b),(c) over an abstract rounding kernel
    -- the rounding, constructed: independent coordinatewise randomized rounding
    Tent.lean                 -- the displacement density 1−|u|: mass 1, mean 0, support [−1,1]
    TentSum.lean              -- ∑_{m∈ℤ} tent(u−m) = 1, and the n-fold partition of unity
    PiLintegral.lean          -- a product of withDensity measures is a withDensity product
    ProdKernel.lean           -- prodKernel: the kernel ∏ᵢ tent(pᵢ−xᵢ); double stochasticity
    ProdLaw.lean              -- its displacement law is a product ⇒ claim:cl (a) discharged
    RoundLaw.lean             -- the law of rnd p on ℤⁿ (the fixed-p side, for (b))
    RoundMoments.lean         -- that law is two-point ⇒ bounded, mean zero, independent
    ClB.lean                  -- claim:cl (b) discharged: the Q''-direction covering + averaging
    -- lem:lattice, assembled
    BallFacet.lean            -- inscribed ball ↔ facet form; finiteness of Q ∩ ℤⁿ; ℤⁿ ↪ ℝⁿ
    NonconvAssembled.lean     -- lem:nonconv over an actual facet system, nothing assumed
    Lattice.lean              -- lem:lattice: transport ℤⁿ ↔ 𝕃ⁿ = 10⁻ᵖ·ℤⁿ
    LatticeAssembled.lean     -- lem:lattice for Sol(F); where GetPrecision becomes load-bearing
    Poisson.lean              -- lem:process: Poisson splitting
    Chernoff.lean             -- lem:chernoff: the Poisson tail bound, from the MGF up
    PoissonLaws.lean          -- lem:process as an identity of measures: splitting, thinning
    Thinning.lean             -- Poisson thinning as a kernel, and on a whole count vector
    CountVector.lean          -- 𝒳 read as a count vector over the finite set Sol(F) ∩ 𝕃ⁿ
    SketchProcess.lean        -- the level-j process; Err and Noise branches; the δ budget
    Sketch.lean               -- lem:numlattice's epoch skeleton
    Invariants.lean           -- structural invariants of the modelled main loop
    Coupling.lean             -- the coupled level family 𝒳ⱼ, its law, and the oracle
                              --   bundle that reads a trajectory (trajOracles)
    RunCoupling.lean          -- the run IS the family: |𝒳| = ∑ₛ ω(J)ₛ pathwise, the
                              --   halving triggers, and lem:numlattice's bound proved
    NumLatticeModel.lean      -- that bound transported to an arbitrary Ω/μ/O, and
                              --   TtcProb.numlattice_union — the ex-field, as a theorem;
                              --   also exists_epoch (j* is constructed, not assumed),
                              --   TtcProb.thresh_pos and TtcProb.vol_le_total
    Witness.lean              -- the box [0,c]ⁿ: its atoms, cube, DNF, formula, inscribed
                              --   ball, finite volume, and lattice count ≥ cⁿ
    BoxProb.lean              -- Box.boxProb: the non-degenerate TtcProb built on it,
                              --   and Box.nonempty_ttcProb
    OracleLaws.lean           -- an alternative distributional contract on the bundle;
                              --   nothing consumes it and it has NO witness (⚠️ §3)
    Capstone.lean             -- the two chains combining lem:lattice with lem:numlattice
    NumLattice.lean           -- lem:numlattice as a theorem, from the epoch covering
```

**Reading order for an auditor: `Model/`, in this order, then stop.**
[`Model/Prelude`](Ttc/Model/Prelude.lean) fixes what every name means, including
`Vol(F)` and the `(1±ε)` interval.
[`Model/Pseudocode`](Ttc/Model/Pseudocode.lean) is the code — read it against
`sections/algo.tex`. [`Model/ProblemSetting`](Ttc/Model/ProblemSetting.lean) is
`Ttc.TtcProb`: **every hypothesis the result rests on**, as fields.
[`Model/Theorem`](Ttc/Model/Theorem.lean) states what is proved.
Anything you still doubt is a named lemma in `Analysis/`.

| Surface module | Contains | Status |
| --- | --- | --- |
| [`Model/Prelude.lean`](Ttc/Model/Prelude.lean) | `Ttc.Space n`, `BForm`/`Lit`/`Cube`/`DNF`, `sol`, `region`, `Ttc.Params`: `η`, `ε'`, `Thresh`, `κ`, `γ`, `ρ`, [`volSol`](Ttc/Model/Prelude.lean#L173) (= `Vol(F)`), [`relErr`](Ttc/Model/Prelude.lean#L181) | definitions only |
| [`Model/Pseudocode.lean`](Ttc/Model/Pseudocode.lean) | `SketchState`, [`Oracles`](Ttc/Model/Pseudocode.lean#L76), `dropCovered`, `halveDown`, `absorb`, `step`, [`run`](Ttc/Model/Pseudocode.lean#L146), [`ttcOutput`](Ttc/Model/Pseudocode.lean#L152) | modelled; see caveats |
| [`Model/ProblemSetting.lean`](Ttc/Model/ProblemSetting.lean) | [`TtcProb`](Ttc/Model/ProblemSetting.lean#L43) — the complete list of assumptions, as fields | the whole hypothesis surface |
| [`Model/Theorem.lean`](Ttc/Model/Theorem.lean) | [**`TtcProb.volume_estimate`**](Ttc/Model/Theorem.lean#L41) (`Pr ≥ 1−δ`) — one theorem, nothing else | proved from the `TtcProb` fields |

### What `Ttc/Model/Pseudocode.lean` does and does not do

It is a line-by-line model of `alg:ttc` lines 22–46: the state `(X, p)`, the
order of operations, both `while` guards, the coverage filter, and the output
`|X|/p`. Read it beside the pseudocode.

Four external calls are **fields of `Ttc.Oracles`** rather than definitions —
`Vol_ED`, the Poisson draw, `GenerateSamples`, and the fair-coin thinning. So the
state evolution is deterministic *given the oracle's answers*, and all the
randomness sits at that boundary. That is deliberate, and it is what makes the
coupling constructible: [`Ttc.trajOracles`](Ttc/Analysis/Coupling.lean#L393)
inhabits the bundle with oracles that read a trajectory of the level family, and
the run driven by *those* is provably the family
([`Ttc.card_run_eq_sum_traj`](Ttc/Analysis/RunCoupling.lean#L263)). What the
bundle itself constrains is only the *shape* of the calls plus two contracts
below; what the draws are *distributed* like is said by the `law_eq`/`oracle_eq`
fields of `Ttc.TtcProb`, which name the coupled family directly. (An alternative,
primitive-by-primitive contract [`Ttc.OracleLaws`](Ttc/Analysis/OracleLaws.lean#L63)
is also stated, but nothing consumes it and it has **no witness** — see
[`AUDIT.md`](AUDIT.md) §3.)

**Two contracts were missing and are now stated.** `halve` returns a
*sub-multiset* (`halve_le`), not merely one of no greater cardinality — the loop
deletes elements, it never invents them; and `GenerateSamples` returns points of
`P(cᵢ) ∩ 𝕃ⁿ` ([`TtcProb.gen_mem`](Ttc/Model/ProblemSetting.lean#L119)), where
before only the *count* was fixed. Both are needed before `𝒳` can be treated as a
count vector over a fixed finite set, which
[`TtcProb.run_state_mem`](Ttc/Analysis/LatticeAssembled.lean#L211) now proves.

**Every randomised call is indexed by a `clock`.** `Ttc.SketchState` carries a
counter of draws consumed, and `halve`, `pois` and `gen` take it as their first
argument. The pseudocode has no such counter; it is here because without it the
model *cannot express what the algorithm does*. An unindexed
`halve : Multiset → Multiset` is a function, so applying it twice to the same
multiset gives the same answer — once a thinning happens to be a no-op (which has
probability `2^(−|X|) > 0`), every later thinning of that multiset is forced to be
the same no-op and `𝒳` can never shrink again, which is not the algorithm's
behaviour. Indexing fixes that, and it is also what lets a distributional
hypothesis say the draws are *independent*: distinct call sites provably get
distinct indices ([`halveDown_clock`](Ttc/Analysis/Invariants.lean#L111),
[`absorb_clock`](Ttc/Analysis/Invariants.lean#L122),
[`step_clock`](Ttc/Analysis/Invariants.lean#L139)).

The precision `ρ` is threaded properly: `GenerateSamples` is
[`gen : ℕ → ι → ℕ → ℕ → ℤ → Multiset (Space n)`](Ttc/Model/Pseudocode.lean#L99), `ρ` is
fixed before the loop (`alg:ttc` line 17) and passed at every call, and the
`rho_eq` field of `Ttc.TtcProb` pins it to `⌈log₁₀(γ/γ̂)⌉` (`alg:prec` line 91).
The LP computing `γ̂` is still not modelled — `gammaHat` is an input.

Both `while` loops run on **explicit fuel**. Termination is *not* claimed and
would be false to claim: the second loop terminates because repeated thinning
brings `Nᵢ + |X|` under `Thresh` with high probability, and there is no
deterministic bound. What is proved is structural, and lives in
[`Analysis/Invariants.lean`](Ttc/Analysis/Invariants.lean) so that `Model/` stays
proof-free — `p` never increases and stays nonnegative (`halveDown_p`,
`absorb_p`), the filter only removes points (`card_dropCovered_le`), a settled
state is a fixpoint (`absorb_of_settled`).

### The output, and what is assumed about it

A completed formalisation of an algorithm carries **two** models — a
paper-faithful transcription, and the operational one the analysis actually
reasons about — joined by a *proved* bridge saying they compute the same thing.
That bridge is what puts the operational model outside the trusted base.

This development needs no such bridge, because it has only the transcription.
[`Ttc.ttcOutput`](Ttc/Model/Pseudocode.lean#L152) *is* `Ttc.run` with the oracles
drawn at a sample point, so the headline measures the algorithm directly:

```lean
noncomputable def Ttc.ttcOutput (P : Params) (O : Ω → Oracles n ι) (fuel : ℕ)
    (ρ : ℤ) (cubes : List ι) (ω : Ω) : ℝ :=
  run P (O ω) fuel ρ cubes
```

`lem:numlattice` itself is **not** assumed any more: it is
[`Ttc.TtcProb.numlattice`](Ttc/Analysis/NumLattice.lean#L53), a theorem about that
same output. Nor is the epoch covering it is derived from: that used to be a
`numlattice_union` field, and is now
[`Ttc.TtcProb.numlattice_union`](Ttc/Analysis/NumLatticeModel.lean#L267), a
theorem with the deleted field's statement verbatim:

```lean
theorem Ttc.TtcProb.numlattice_union (T : TtcProb A n) :
    ∃ (jstar : ℕ) (lamStar : ℝ),
      (1 - T.P.epsPrime) * T.P.thresh / 8 ≤ lamStar ∧
      (T.μ {ω | ¬ ((1 - T.ε/3) * T.L ≤ ttcOutput T.P T.O T.fuel T.ρ T.D ω ∧
                 ttcOutput T.P T.O T.fuel T.ρ T.D ω ≤ (1 + T.ε/3) * T.L)}).toReal
        ≤ (∑ t ∈ Finset.range jstar,
              2 * Real.exp (-(T.P.epsPrime ^ 2 * (lamStar * 2 ^ t) / 3)))
            + T.P.m * Real.exp (-(T.P.thresh / 6)) + T.δ / 2
```

That the three terms total at most `δ`, at the algorithm's own `Thresh` and `δ'`,
is [`Ttc.numlattice_failure_le`](Ttc/Analysis/SketchProcess.lean#L246); the
per-epoch sizes are [`levelLaw_err_le`](Ttc/Analysis/SketchProcess.lean#L130) and
[`levelLaw_noise_le`](Ttc/Analysis/SketchProcess.lean#L194). So the headline needs
**no side hypothesis**. And `L` is no longer a bare real: the field
[`L_eq`](Ttc/Model/ProblemSetting.lean#L124) pins it to
[`normalisedCount M φ ρ`](Ttc/Model/Prelude.lean#L166) `= |Sol(F) ∩ 𝕃ⁿ|/10^(ρn)`,
the actual lattice count of the actual solution set — which is what makes
`lem:lattice` a theorem about it rather than an assumption.

What the proof of `numlattice_union` consumes are the **sampler fields**
([`Model/ProblemSetting.lean:133`](Ttc/Model/ProblemSetting.lean#L133) onwards).
It is [`Ttc.numlattice_union_of_model`](Ttc/Analysis/NumLatticeModel.lean#L35)
applied to them: the run's failure event is the `toTraj`-preimage of the
trajectory-space one (`oracle_eq`), `Measure.le_map_apply` pushes its measure
forward along `law_eq`, and
[`Ttc.traj_numlattice_le`](Ttc/Analysis/RunCoupling.lean#L685) bounds it there.
The accuracy window comes from `rate_eq_L` through
[`Ttc.window_of_exact`](Ttc/Analysis/NumLatticeModel.lean#L121). The epoch index
`j*` the bound is stated at is **not** taken from the instance: it is produced by
[`Ttc.exists_epoch`](Ttc/Analysis/NumLatticeModel.lean#L140) from `big` and
[`Ttc.TtcProb.thresh_pos`](Ttc/Analysis/NumLatticeModel.lean#L242), and the
`halveDown` cut-off it needs at that index comes from `vol_pos` and
[`Ttc.TtcProb.vol_le_total`](Ttc/Analysis/NumLatticeModel.lean#L260) through
[`Ttc.rate_small_of_epoch`](Ttc/Analysis/NumLatticeModel.lean#L180).

The structure is inhabited **non-degenerately**
([`Ttc.Box.nonempty_ttcProb`](Ttc/Analysis/BoxProb.lean#L349), witness
[`Ttc.Box.boxProb`](Ttc/Analysis/BoxProb.lean#L271)): the box `[0,c]ⁿ` with
`c ≥ Thresh`, sampled by the coupled family. Its solution set is nonempty, its
`L` is at least `cⁿ ≥ Thresh`, and its `numlattice_union` obligation is
discharged **by proof**, not by an empty failure event. The old degenerate
witness `Ttc.trivialProb` has been deleted: with `D = []` it forces `Lidx = 0`,
which contradicts `θ_pos`.

## Paper ↔ Lean map

Keyed by `\label`, not by number — numbers shift whenever a `\begin{lemma}` is
added or uncommented. (At the time of writing the counter runs
`thm:decomposition` = Lemma 1, `lem:chernoff` = 2, `lem:process` = 3,
`lem:integerlattice` = 4, `lem:nonconv` = 5, `claim:cl` = 6, `lem:lattice` = 7,
`lem:numlattice` = 8; `claim:helper` = Claim 1. Note `claim:cl` uses a `lemma`
environment, so it renders as a *Lemma*, not a Claim.)

| `\label` | Statement | Lean | Status |
| --- | --- | --- | --- |
| `thm:decompose` | decomposition takes exponential time | — | out of scope (runtime) |
| `thm:runtime` | `O(mn⁴)` runtime | — | out of scope (runtime) |
| `thm:decomposition` | `⋃ᵢ P(cᵢ) = Sol(F)` | [`sol_eq_iUnion_region`](Ttc/Analysis/Decomposition.lean#L112), [`region_subset_sol`](Ttc/Analysis/Decomposition.lean#L96), [`sol_subset_iUnion_region`](Ttc/Analysis/Decomposition.lean#L103) | **proved** |
| `lem:chernoff` | Poisson tail bound (Soos et al.) | [`poisson_tail`](Ttc/Analysis/Chernoff.lean#L238), [`poisson_lower_tail`](Ttc/Analysis/Chernoff.lean#L260), [`poisson_tail_two_sided`](Ttc/Analysis/Chernoff.lean#L321); engine [`mgf_poissonMeasure`](Ttc/Analysis/Chernoff.lean#L181), [`bennett_le`](Ttc/Analysis/Chernoff.lean#L102) | **proved** — no longer external |
| ↳ its two uses | `Pr[N > Thresh] ≤ e^(−Thresh/6)` and `Pr[\|N−λ\| ≥ ε'λ] ≤ 2e^(−ε'²λ/3)` | [`poisson_overflow`](Ttc/Analysis/Chernoff.lean#L341), [`poisson_relative`](Ttc/Analysis/Chernoff.lean#L362) | **proved** — both constants confirmed exact |
| `lem:process` | three sampling procedures are equivalent | [`poisson_splitting`](Ttc/Analysis/Poisson.lean#L60), [`poisson_splitting_paper`](Ttc/Analysis/Poisson.lean#L107), [`rate_mem_interval`](Ttc/Analysis/Poisson.lean#L123) | **proved** |
| `lem:integerlattice` | KV97 Thm 3, single polytope | — | external; superseded by `lem:nonconv` |
| `lem:nonconv` | `vol Q ∈ [(1−η)\|Q∩ℤⁿ\|, (1+η)\|Q∩ℤⁿ\|]` | skeleton [`nonconv_lower`](Ttc/Analysis/Nonconv.lean#L101), [`nonconv_upper_deflated`](Ttc/Analysis/Nonconv.lean#L124), [`nonconv_upper_repaired`](Ttc/Analysis/Nonconv.lean#L140); geometry [`FacetSystem.inflated_subset_smul_deflated`](Ttc/Analysis/Geometry.lean#L102), [`volume_inflated_le`](Ttc/Analysis/Geometry.lean#L124) | proved from `claim:cl` — **see findings 1 & 2** |
| ↳ repaired | same statement, internal `θ = η/2` | [`nonconv_repaired`](Ttc/Analysis/Repair.lean#L75), [`repair_upper_arith`](Ttc/Analysis/Repair.lean#L52), [`repair_lower_arith`](Ttc/Analysis/Repair.lean#L58) | **proved** |
| ↳ shell bound, instantiated | `vol Q' ≤ (1+m(K−1))·vol Q` and `vol Q ≤ (1+m(K−1))·vol Q''`, from the actual sets | [`piece_inflated_subset_homothety_zero`](Ttc/Analysis/Recentred.lean#L211), [`volume_shell_le`](Ttc/Analysis/Recentred.lean#L284), [`volume_body_inflated_le`](Ttc/Analysis/Recentred.lean#L476), [`volume_body_deflated_le`](Ttc/Analysis/Recentred.lean#L531) | **proved** — both sides; `shell_bound`'s three hypotheses discharged from geometry |
| ↳ `Q = Sol(F)` | the facet system of a positive DNF | [`facetSystem`](Ttc/Analysis/FacetOfDNF.lean#L57), [`region_eq_piece`](Ttc/Analysis/FacetOfDNF.lean#L67), [`body_eq_sol`](Ttc/Analysis/FacetOfDNF.lean#L88) | **proved** for `DNF.IsPositive` — see finding 5 |
| ↳ without common ball | per-polytope homothety + shell bound | [`piece_inflated_subset_homothety`](Ttc/Analysis/Recentred.lean#L69), [`volume_piece_inflated_le`](Ttc/Analysis/Recentred.lean#L100), [`body_subset_union_shells`](Ttc/Analysis/Recentred.lean#L183), [`shell_bound`](Ttc/Analysis/Recentred.lean#L457) | **proved** |
| ↳ **assembled, nothing assumed** | `lem:nonconv` for an actual facet system against its own `\|Q∩ℤⁿ\|` | [`FacetSystem.nonconv_of_ball`](Ttc/Analysis/NonconvAssembled.lean#L216), summed forms [`card_le_of_claim_a`](Ttc/Analysis/NonconvAssembled.lean#L126), [`deflated_le_card`](Ttc/Analysis/NonconvAssembled.lean#L160), arithmetic [`nonconv_recentred_general`](Ttc/Analysis/NonconvAssembled.lean#L49) | **proved** from the ball hypothesis alone |
| ↳ `Q ∩ ℤⁿ` is finite | not assumed — it follows from `claim:cl`(a) | [`finite_of_forall_finset_card_le`](Ttc/Analysis/BallFacet.lean#L135), [`ncard_inter_intLattice`](Ttc/Analysis/BallFacet.lean#L170) | **proved** |
| ↳ inscribed ball ↔ facet form | `B(cᵢ,γ) ⊆ Pᵢ  ⟺  γ‖A_ij‖ ≤ b_ij − A_ij·cᵢ` | [`FacetSystem.ball_subset_piece`](Ttc/Analysis/BallFacet.lean#L70), [`FacetSystem.facet_of_ball_subset`](Ttc/Analysis/BallFacet.lean#L90) | **proved** both ways |
| `claim:cl` | rounding hits/misses `Q` w.p. `1 ± η/2` | **all three discharged for the actual rounding** — (a) [`prodKernel_claim_cl_a`](Ttc/Analysis/ProdLaw.lean#L232), (b) [`prodKernel_claim_cl_b`](Ttc/Analysis/ClB.lean#L180), (c) [`claim_cl_c`](Ttc/Analysis/Cl.lean#L114), over [`prodKernel`](Ttc/Analysis/ProdKernel.lean#L110); core [`rounding_tail_bound`](Ttc/Analysis/Rounding.lean#L107) | **proved**, no residual hypothesis — see finding 3 |
| ↳ the rounding itself | `rnd p = ⌊p⌋ + Bernoulli(p−⌊p⌋)`, coordinatewise | density [`tent`](Ttc/Analysis/Tent.lean#L34), kernel [`prodKernel`](Ttc/Analysis/ProdKernel.lean#L110), normalisation [`integral_prod_tent`](Ttc/Analysis/ProdKernel.lean#L42) | **constructed** — the paper only cites KV97 |
| ↳ (a)/(c), the `p`-side | independence of the displacement's coordinates | [`iIndepFun_disp`](Ttc/Analysis/ProdLaw.lean#L117), [`ae_disp_mem_Icc`](Ttc/Analysis/ProdLaw.lean#L106), [`integral_disp_eq_zero`](Ttc/Analysis/ProdLaw.lean#L146), [`prodKernel_escape_bound`](Ttc/Analysis/ProdLaw.lean#L213) | **proved** |
| ↳ (b), the `z`-side | the law of `rnd p` on `ℤⁿ` is a two-point product | [`roundLaw`](Ttc/Analysis/RoundLaw.lean#L50), [`tentInt_eq_two_point`](Ttc/Analysis/RoundMoments.lean#L34), [`integral_tentInt_disp`](Ttc/Analysis/RoundMoments.lean#L72), [`iIndepFun_latDisp`](Ttc/Analysis/RoundMoments.lean#L153), [`roundLaw_escape_bound`](Ttc/Analysis/ClB.lean#L69) | **proved**; the crossing uses `−A_j` ([`cover_of_notMem_body_deflated`](Ttc/Analysis/ClB.lean#L42)) |
| `claim:helper` | `kⁿ ≤ (1+η/4)/(1−η/4)` | [`claim_helper`](Ttc/Analysis/Arith.lean#L162), [`claim_helper_of`](Ttc/Analysis/Arith.lean#L133), [`exp_two_mul_le_div`](Ttc/Analysis/Arith.lean#L78) | **proved** — see finding 4 |
| `lem:lattice` | `Vol(F) ∈ (1±η)·\|Sol(F) ∩ 𝕃ⁿ\|/10^(ρn)` | [`lattice_of_dnf`](Ttc/Analysis/LatticeAssembled.lean#L91), and for the problem instance [`TtcProb.lattice_lo`](Ttc/Analysis/LatticeAssembled.lean#L222)/[`lattice_hi`](Ttc/Analysis/LatticeAssembled.lean#L227) | **proved** — formerly two fields of `TtcProb` |
| ↳ transport `ℤⁿ ↔ 𝕃ⁿ = 10⁻ᵖ·ℤⁿ` | | [`lattice_of_scaled`](Ttc/Analysis/Lattice.lean#L91), [`ncard_inter_lattice_smul`](Ttc/Analysis/Lattice.lean#L57), [`volume_smul_body`](Ttc/Analysis/Lattice.lean#L63), [`lattice_bounds`](Ttc/Analysis/Lattice.lean#L144) | **proved** |
| `lem:numlattice` | sketch output within `(1±ε/3)` w.p. `1−δ` | [`TtcProb.numlattice`](Ttc/Analysis/NumLattice.lean#L53), from `TtcProb.numlattice_union` plus [`numlattice_failure_le`](Ttc/Analysis/SketchProcess.lean#L246); skeleton [`epoch_series_le`](Ttc/Analysis/Sketch.lean#L87), [`err_sum_le_delta`](Ttc/Analysis/Sketch.lean#L106), [`noise_bound_le_delta`](Ttc/Analysis/Sketch.lean#L126), [`numlattice_failure_bound`](Ttc/Analysis/Sketch.lean#L142), [`sketch_interval`](Ttc/Analysis/Sketch.lean#L181), [`sketch_window`](Ttc/Analysis/Sketch.lean#L196) | **theorem** — and so is the epoch covering it consumes, [`TtcProb.numlattice_union`](Ttc/Analysis/NumLatticeModel.lean#L267) (see [What is assumed](#assumed-about-the-algorithm)) |
| ↳ **the covering, from the sampler description** | the ex-field, proved: transport the coupled-run bound to an arbitrary `Ω`/`μ`/`O` | [`numlattice_union_of_model`](Ttc/Analysis/NumLatticeModel.lean#L35), self-coupled form [`numlattice_union_of_traj`](Ttc/Analysis/NumLatticeModel.lean#L190), window [`window_of_two_sided`](Ttc/Analysis/NumLatticeModel.lean#L104)/[`window_of_exact`](Ttc/Analysis/NumLatticeModel.lean#L121), epoch index [`exists_epoch`](Ttc/Analysis/NumLatticeModel.lean#L140), [`rate_small_of_epoch`](Ttc/Analysis/NumLatticeModel.lean#L180), and the two facts that let `j*` be *constructed* rather than assumed — [`TtcProb.thresh_pos`](Ttc/Analysis/NumLatticeModel.lean#L242), [`TtcProb.vol_le_total`](Ttc/Analysis/NumLatticeModel.lean#L260) | **proved** — this is what deleted the last assumed field, and then the assumed epoch index too |
| ↳ the coupled level family | `𝒳ⱼ` for **all** `j` on one space, nested thinning from level `0` | [`famCount`](Ttc/Analysis/Coupling.lean#L80), [`famLaw`](Ttc/Analysis/Coupling.lean#L125), [`trajLaw`](Ttc/Analysis/Coupling.lean#L209), marginals [`map_trajLaw_eval`](Ttc/Analysis/Coupling.lean#L274), nesting [`trajLaw_ae_nested`](Ttc/Analysis/RunCoupling.lean#L592) | **constructed** — the object finding 15 says the paper never builds |
| ↳ the coupling to the run | the oracles read the family; `\|𝒳\| = ∑ₛ ω(J)ₛ` **pathwise** | [`trajOracles`](Ttc/Analysis/Coupling.lean#L393), [`CoupledAt`](Ttc/Analysis/RunCoupling.lean#L31), [`coupledAt_step`](Ttc/Analysis/RunCoupling.lean#L183), [`coupledAt_foldl`](Ttc/Analysis/RunCoupling.lean#L241), [`card_run_eq_sum_traj`](Ttc/Analysis/RunCoupling.lean#L263), [`run_eq_traj`](Ttc/Analysis/RunCoupling.lean#L281) | **proved** — equality of random variables, not of laws |
| ↳ the halving trigger | every level the run crosses had a large rate or an overflow | [`card_add_pois_le`](Ttc/Analysis/RunCoupling.lean#L345), [`absorb_trigger`](Ttc/Analysis/RunCoupling.lean#L356), [`halveDown_trigger`](Ttc/Analysis/RunCoupling.lean#L391), [`step_trigger`](Ttc/Analysis/RunCoupling.lean#L411), [`foldl_trigger`](Ttc/Analysis/RunCoupling.lean#L441), [`level_cap_subset`](Ttc/Analysis/RunCoupling.lean#L471) | **proved** — what bounds `Pr[⋃_{j≥j*} Nois(j)]` |
| ↳ **`lem:numlattice` for the coupled run** | the paper's three-term bound, for `Ttc.run` driven by the family | [`traj_numlattice_le`](Ttc/Analysis/RunCoupling.lean#L685), via [`traj_failure_le`](Ttc/Analysis/RunCoupling.lean#L614), [`trajLaw_err_le`](Ttc/Analysis/RunCoupling.lean#L511), [`trajLaw_noise_le`](Ttc/Analysis/RunCoupling.lean#L527), [`epoch_reindex`](Ttc/Analysis/RunCoupling.lean#L665), [`totalRate_reindex`](Ttc/Analysis/RunCoupling.lean#L672) | **proved**, nothing probabilistic assumed — and with a *smaller* right-hand side than the paper's (no `+ δ/2`) |
| ↳ the alternative oracle contract | `pois` is Poisson, `halve` is a fair independent thinning | [`OracleLaws`](Ttc/Analysis/OracleLaws.lean#L63), reachable draws [`clockBound`](Ttc/Analysis/OracleLaws.lean#L44), [`run_eq_of_agree_below`](Ttc/Analysis/OracleLaws.lean#L48) | **stated only** — nothing consumes it and it has **no witness** ([`AUDIT.md`](AUDIT.md) §3) |
| ↳ the non-degenerate witness | the box `[0,c]ⁿ`, `c ≥ Thresh`, sampled by the coupled family | [`Box.boxProb`](Ttc/Analysis/BoxProb.lean#L271), [`Box.nonempty_ttcProb`](Ttc/Analysis/BoxProb.lean#L349); geometry [`boxAtoms`](Ttc/Analysis/Witness.lean#L47), [`boxCube`](Ttc/Analysis/Witness.lean#L270), [`boxDNF`](Ttc/Analysis/Witness.lean#L307), [`boxForm`](Ttc/Analysis/Witness.lean#L387), [`sol_boxForm`](Ttc/Analysis/Witness.lean#L429), [`normalisedCount_box_ge`](Ttc/Analysis/Witness.lean#L451) | **constructed** — replaces the deleted `trivialProb` |
| `alg:ttc` line 18 (`ε' ← ε/12`) | | [`sketch_interval`](Ttc/Analysis/Sketch.lean#L181) | constant **verified** |
| `alg:ttc` line 18 (`δ' ← δ/(2m)`) | the `Vol_ED` failure budget | [`Params.deltaPrime`](Ttc/Model/Prelude.lean#L225), [`Params.vol_failure_eq`](Ttc/Analysis/Sketch.lean#L159), [`numlattice_failure_bound_with_vol`](Ttc/Analysis/Sketch.lean#L168) | **verified** — and the paper omits it from its union bound; see finding 13 |
| `alg:ttc` line 20 (`Thresh`) | | [`err_sum_le_delta`](Ttc/Analysis/Sketch.lean#L106), [`noise_bound_le_delta`](Ttc/Analysis/Sketch.lean#L126) | both branches **verified** |
| `alg:ttc` line 17 (`η ← ε/8`) | | [`Params.eta`](Ttc/Model/Prelude.lean#L218) | definition |
| `κ` (`lem:nonconv`) | `√(2log(8/η)) + √(2log r)` | [`Params.kappa`](Ttc/Model/Prelude.lean#L234), [`kappa_le`](Ttc/Analysis/Parameters.lean#L62) | **proved** `κ ≤ 2√(log(8r/η))` |
| ↳ deflated shell factor | `(1 + κ/(γ−κ))ⁿ ≤ 1 + η/(8m)` | [`kappa_le_gamma_half`](Ttc/Analysis/Parameters.lean#L124), [`shell_factor_bound_deflated`](Ttc/Analysis/Parameters.lean#L144) | **proved** — the deflated companion of `shell_factor_bound` |
| ↳ dilation of a facet system | `c·{x \| f x ≤ b} = {y \| f y ≤ c·b}` | [`FacetSystem.scale`](Ttc/Analysis/Recentred.lean#L345), [`scale_body_zero`](Ttc/Analysis/Recentred.lean#L380) | **proved** — connects `body_eq_sol` to `lem:lattice`'s dilate |
| `γ` / `κ/γ ≤ η/(32mn)` | the shell bound's input | [`Params.gamma`](Ttc/Model/Prelude.lean#L240), [`kappa_div_gamma_le`](Ttc/Analysis/Parameters.lean#L81), [`shell_factor_bound`](Ttc/Analysis/Parameters.lean#L102) | **proved** — see finding 2 |
| `alg:ttc` lines 22–46 (main loop) | the sketch loop itself | [`run`](Ttc/Model/Pseudocode.lean#L146), [`step`](Ttc/Model/Pseudocode.lean#L139), [`absorb`](Ttc/Model/Pseudocode.lean#L120), [`halveDown`](Ttc/Model/Pseudocode.lean#L111) | modelled over an oracle bundle; structural invariants proved, termination not |
| ↳ the output as a random variable | `run` with oracles drawn at `ω` | [`ttcOutput`](Ttc/Model/Pseudocode.lean#L152) | definition |
| `thm:volumettc` | `Pr[ output ∈ (1±ε)·Vol(F) ] ≥ 1−δ` | [`TtcProb.volume_estimate`](Ttc/Model/Theorem.lean#L41) | **proved** from the [`TtcProb`](Ttc/Model/ProblemSetting.lean#L43) fields |
| `alg:prec` (`GetPrecision`) | `ρ ← ⌈log₁₀(γ/γ̂)⌉` ([`Params.precision`](Ttc/Model/Prelude.lean#L247), used via `TtcProb.rho_eq`) | **load-bearing**: [`gamma_le_latticeScale_mul`](Ttc/Analysis/LatticeAssembled.lean#L69) is what makes the *dilated* polytopes contain a ball of radius `γ`, which is what the shell bound needs; also [`ball_radius_scales`](Ttc/Analysis/Lattice.lean#L70), [`gamma_half_le`](Ttc/Analysis/Repair.lean#L116), [`precision_increase_le_one`](Ttc/Analysis/Repair.lean#L154), [`gamma_scale_cost`](Ttc/Analysis/Recentred.lean#L576) | mathematical content **proved**; LP implementation not modelled |

Results with no counterpart in the paper, produced by the formalisation:

| Lean | What it establishes |
| --- | --- |
| [`convex_region`](Ttc/Analysis/Decomposition.lean#L76), [`convex_litSet`](Ttc/Analysis/Decomposition.lean#L53) | each cube's region is convex — and *not* closed (finding 5) |
| [`ratio_antitone`](Ttc/Analysis/Geometry.lean#L156), [`facet_ratio_fails`](Ttc/Analysis/Geometry.lean#L170) | `k` is attained at the facet **nearest** the origin, so the ball hypothesis is needed at every facet (finding 2) |
| [`claim12_factor_le`](Ttc/Analysis/Nonconv.lean#L155) | the `claim:helper` factor is `≤ 5/3` on `0 < η ≤ 1` |
| [`Box.boxProb`](Ttc/Analysis/BoxProb.lean#L271), [`Box.nonempty_ttcProb`](Ttc/Analysis/BoxProb.lean#L349) | the hypothesis bundle is inhabited **non-degenerately**, so `thm:volumettc` is not vacuous; see [`AUDIT.md`](AUDIT.md) §3 |
| [`box_lattice_card_ge`](Ttc/Analysis/Witness.lean#L215), [`normalisedCount_box_ge`](Ttc/Analysis/Witness.lean#L451) | the witness's normalised lattice count is at least `cⁿ`, at *every* precision — what lets `c` be chosen from `Thresh` |
| [`trajOracles`](Ttc/Analysis/Coupling.lean#L393) + [`card_run_eq_sum_traj`](Ttc/Analysis/RunCoupling.lean#L263) | the coupling finding 15 says `lem:numlattice`'s proof needs and the paper never constructs |
| [`traj_numlattice_le`](Ttc/Analysis/RunCoupling.lean#L685) | `lem:numlattice`'s bound for the coupled run, with no probabilistic hypothesis |
| [`numlattice_union_of_model`](Ttc/Analysis/NumLatticeModel.lean#L35) | that bound transported to an arbitrary probability space that *is* the family — what turned the last assumed field into a theorem |
| [`exists_epoch`](Ttc/Analysis/NumLatticeModel.lean#L140) | the epoch window `[(1−ε')·Thresh/8, Thresh/2]` has ratio ≥ 4, so a power of two always lands in it — `j*` need not be handed to the proof |
| [`TtcProb.thresh_pos`](Ttc/Analysis/NumLatticeModel.lean#L242) | `Thresh > 0`, from `alg:ttc` line 20's own formula: `δ ≤ 1` forces `log(24/δ) ≥ log 24 > 0`, and `ε' = ε/12 ∈ (0, 1/12]` keeps `(1−ε')ε'²` positive. The paper leaves it implicit |
| [`TtcProb.vol_le_total`](Ttc/Analysis/NumLatticeModel.lean#L260) | each cube's rate is at most the total, because `vol_eq` sums a subset of nonnegative rates — what makes the `halveDown` cut-off derivable |

`Ttc.lean` re-exports everything, so `import Ttc` and a bare `lake build` expose
the headline theorem.

## The headline theorem

```lean
theorem Ttc.TtcProb.volume_estimate (T : TtcProb A n) :
    1 - T.δ ≤
      (T.μ {ω | ttcOutput T.P T.O T.fuel T.ρ T.D ω ∈ relErr T.ε (volSol T.M T.φ)}).toReal
```

`ttcOutput` is `Ttc.run` — the transcription of `alg:ttc` — with the oracles
drawn at `ω`, so the measured quantity is the algorithm's own output.
`volSol M φ = (volume (sol M φ)).toReal` is the **Lebesgue volume of the solution
set of the actual SMT(LRA) formula** — not a surrogate. That the set in question
is exactly the union of the polytopes the algorithm enumerates is
`Ttc.TtcProb.sol_eq_union` (`thm:decomposition`), so the object the algorithm
targets and the object the theorem bounds coincide.

**Non-vacuity.** `Ttc.TtcProb` is inhabited by
[`Ttc.Box.boxProb`](Ttc/Analysis/BoxProb.lean#L271)
([`Ttc.Box.nonempty_ttcProb`](Ttc/Analysis/BoxProb.lean#L349)), the box `[0,c]ⁿ`
with `c ≥ Thresh` sampled by the coupled family — so the theorem is not
vacuously quantified, and not by a degenerate instance either; see
[`AUDIT.md`](AUDIT.md) §3.

## What is assumed

Everything in the tree is proved, and **no lemma of the paper is a hypothesis any
more**. What remains assumed about the algorithm is a *description of its
sampler* — 19 fields saying the randomness is the Poisson/thinning family, not a
bound on how often it fails. Two contracts on the external samplers sit beside
them (`Oracles.gen_card` and `Oracles.halve_le` in the bundle itself, and
[`gen_mem`](Ttc/Model/ProblemSetting.lean#L119), that `GenerateSamples` returns
points of `P(cᵢ) ∩ 𝕃ⁿ`). And `Ttc.TtcProb` carries hypotheses about the *input*,
which is a different kind of assumption again: properties of the formula handed
to `TTC`, checkable before it runs, not claims about what `TTC` does.

### Proved, and previously assumed

**`lem:lattice` is now a theorem** ([`Ttc.TtcProb.lattice_lo`](Ttc/Analysis/LatticeAssembled.lean#L222),
[`lattice_hi`](Ttc/Analysis/LatticeAssembled.lean#L227)), where it used to be two
fields of `Ttc.TtcProb`. With it, `claim:cl` and `lem:nonconv` are discharged end
to end:

* **`claim:cl`, all three parts, for a concrete rounding.** The paper cites `rnd`
  to KV97 without a construction; we supply the standard one — independent
  coordinatewise rounding `xₖ = ⌊pₖ⌋ + Bernoulli(pₖ − ⌊pₖ⌋)`, whose displacement
  density is the tent `1−|u|` ([`Analysis/Tent`](Ttc/Analysis/Tent.lean)) — and
  prove every property the analysis uses. Reading it in the `p` variable gives
  double stochasticity ([`integral_prod_tent`](Ttc/Analysis/ProdKernel.lean#L42))
  and parts **(a)** ([`prodKernel_claim_cl_a`](Ttc/Analysis/ProdLaw.lean#L232))
  and **(c)** ([`claim_cl_c`](Ttc/Analysis/Cl.lean#L114)); reading the *same*
  kernel in the lattice variable gives the law of `rnd p` on `ℤⁿ`
  ([`roundLaw`](Ttc/Analysis/RoundLaw.lean#L50)), which is a two-point product
  ([`tentInt_eq_two_point`](Ttc/Analysis/RoundMoments.lean#L34)) — hence bounded,
  mean-zero ([`integral_tentInt_disp`](Ttc/Analysis/RoundMoments.lean#L72)) and
  independent ([`iIndepFun_latDisp`](Ttc/Analysis/RoundMoments.lean#L153)), so
  Hoeffding applies on that side too and yields **(b)**
  ([`prodKernel_claim_cl_b`](Ttc/Analysis/ClB.lean#L180)). The geometry differs
  between the two directions: in (a) the escaping point crosses a facet outward,
  in (b) inward, so (b) applies the tail bound to `−A_j`
  ([`cover_of_notMem_body_deflated`](Ttc/Analysis/ClB.lean#L42)).
* **`lem:nonconv` over an actual facet system**
  ([`FacetSystem.nonconv_of_ball`](Ttc/Analysis/NonconvAssembled.lean#L216)) — no
  free reals, no abstract kernel. Its one hypothesis is the paper's: each `Pᵢ`
  contains an `ℓ₂`-ball of radius `γ` about its own centre.
* **Finiteness of `Q ∩ ℤⁿ` is not assumed.** It follows from `claim:cl`(a), which
  bounds `|T|` for *every* finite `T ⊆ Q ∩ ℤⁿ`
  ([`finite_of_forall_finset_card_le`](Ttc/Analysis/BallFacet.lean#L135)).
* **`GetPrecision` became load-bearing.** `ρ = ⌈log₁₀(γ/γ̂)⌉` is exactly what makes
  the dilated polytopes contain a ball of radius `γ`
  ([`gamma_le_latticeScale_mul`](Ttc/Analysis/LatticeAssembled.lean#L69)), which is
  what the shell bound stands on. In the previous version `rho_eq` was inert.

### Assumed about the input

Fields of [`Ttc.TtcProb`](Ttc/Model/ProblemSetting.lean#L43), all of them
hypotheses `lem:nonconv` needs and the paper states (or silently uses):

| Field | Assumption |
| --- | --- |
| [`M_eq`](Ttc/Model/ProblemSetting.lean#L62) | the atoms really are linear constraints `A x ≤ b` — the formula is in the LRA fragment |
| [`isPositive`](Ttc/Model/ProblemSetting.lean#L71) | no literal of the DNF is negated, so each `P(cᵢ)` is *closed* (finding 5) |
| [`ball_subset`](Ttc/Model/ProblemSetting.lean#L107) | each `P(cᵢ)` contains an `ℓ₂`-ball of radius `γ̂` about `cen i` — the paper's own hypothesis, with the common-centre gap of finding 2 removed |
| [`volume_ne_top`](Ttc/Model/ProblemSetting.lean#L109) | each `P(cᵢ)` has finite volume |
| [`normal_ne_zero`](Ttc/Model/ProblemSetting.lean#L93) | every facet has a nonzero normal vector — implicit in the paper, and false only for a degenerate "constraint" `0 ≤ b` |
| [`cubes_le`](Ttc/Model/ProblemSetting.lean#L89), [`facets_le`](Ttc/Model/ProblemSetting.lean#L91) | `m` and `r` really do bound the number of cubes and of facets |
| [`eps_eq`](Ttc/Model/ProblemSetting.lean#L83), [`delta_eq`](Ttc/Model/ProblemSetting.lean#L85), [`dim_eq`](Ttc/Model/ProblemSetting.lean#L87) | the parameter block is the one for *this* `ε`, *this* `δ` and *this* dimension |
| [`isDNF`](Ttc/Model/ProblemSetting.lean#L68) | `ToDNF`/AllSAT is correct (unchanged) |

None of these says anything about the algorithm's behaviour.

### Assumed about the algorithm

**Not a probability bound any more — a description of the sampler.** The last
field asserting a *conclusion* about probabilities (`numlattice_union`, the epoch
covering) has been **deleted**. In its place `Ttc.TtcProb` carries 19 fields,
starting at [`Model/ProblemSetting.lean:133`](Ttc/Model/ProblemSetting.lean#L133),
that say what the algorithm's randomness *is*. Read them as one paragraph: *the
solution set's lattice points are enumerated injectively, each carries a
nonnegative Poisson rate, every sample point reads as a trajectory of the coupled
thinning family, the oracles answer by reading that trajectory, the cubes cover
the enumerated points, each cube's rate is the total rate of the points it
covers, the instance is big enough to be worth sketching, and the rates sum to
the lattice count.*

| Field(s) | Line | What it says |
| --- | --- | --- |
| `Lidx`, `ptE`, `ptE_inj` | [133](Ttc/Model/ProblemSetting.lean#L133), [135](Ttc/Model/ProblemSetting.lean#L135), [137](Ttc/Model/ProblemSetting.lean#L137) | the lattice points the family is indexed by, and an injective enumeration of them |
| `θ`, `θ_nonneg`, `θ_pos` | [139](Ttc/Model/ProblemSetting.lean#L139), [141](Ttc/Model/ProblemSetting.lean#L141), [143](Ttc/Model/ProblemSetting.lean#L143) | each point's level-`0` rate, nonnegative, with positive total — the instance is not empty |
| `vol`, `cover`, `memPt` | [145](Ttc/Model/ProblemSetting.lean#L145), [147](Ttc/Model/ProblemSetting.lean#L147), [149](Ttc/Model/ProblemSetting.lean#L149) | the rate the run draws each cube with, its coverage test, and cube membership on the enumerated points |
| `toTraj`, `toTraj_meas` | [151](Ttc/Model/ProblemSetting.lean#L151), [153](Ttc/Model/ProblemSetting.lean#L153) | how a sample point is read as a trajectory `ℕ → Fin Lidx → ℕ`, measurably |
| **`law_eq`** | [155](Ttc/Model/ProblemSetting.lean#L155) | **`μ.map toTraj = trajLaw θ`** — the randomness *is* the coupled family |
| **`oracle_eq`** | [157](Ttc/Model/ProblemSetting.lean#L157) | **`O ω = trajOracles …`** — the oracles answer by reading it |
| `cover_eq`, `cover_all` | [159](Ttc/Model/ProblemSetting.lean#L159), [161](Ttc/Model/ProblemSetting.lean#L161) | the coverage test agrees with cube membership on the lattice, and the cubes cover every enumerated point |
| **`vol_eq`**, `vol_pos` | [165](Ttc/Model/ProblemSetting.lean#L165), [167](Ttc/Model/ProblemSetting.lean#L167) | **`∑_{s : memPt i s} θ s = vol i`** — each cube's rate *is* the total level-`0` rate of the points it covers, and it is positive. This is what makes `vol` a description of the instance instead of a free function |
| **`big`** | [172](Ttc/Model/ProblemSetting.lean#L172) | **`(1−ε')·Thresh/8 ≤ ∑θ`** — the instance is large enough for the sketch to be worth running. The paper's own regime, and what [`Ttc.Box.boxProb`](Ttc/Analysis/BoxProb.lean#L271) arranges by choosing the box side from `Thresh` |
| **`rate_eq_L`** | [175](Ttc/Model/ProblemSetting.lean#L175) | **`∑θ = L`** — the rates reproduce the lattice count; the only place the geometry meets the probability |

Five fields that used to sit between `cover_all` and `rate_eq_L` — `jstar`,
`hjstar`, `rate_small`, `rate_le`, `lamStar_ge` — are **gone**. They handed the
proof a chosen epoch index together with both ends of its rate window; `j*` is
now built by [`Ttc.exists_epoch`](Ttc/Analysis/NumLatticeModel.lean#L140) inside
[`Ttc.TtcProb.numlattice_union`](Ttc/Analysis/NumLatticeModel.lean#L267), and
`rate_small` is derived from `vol_pos` and
[`Ttc.TtcProb.vol_le_total`](Ttc/Analysis/NumLatticeModel.lean#L260) by
[`Ttc.rate_small_of_epoch`](Ttc/Analysis/NumLatticeModel.lean#L180). The
positivity of `Thresh` that both need is
[`Ttc.TtcProb.thresh_pos`](Ttc/Analysis/NumLatticeModel.lean#L242) — proved from
the algorithm's own formula, not assumed.

**How honest is this trade?** It is a real reduction, and it is not zero.

* *Real*: nothing in the list mentions `ε`, `δ`, accuracy, or a failure
  probability. Everything quantitative — the per-epoch `Err` estimate, the
  `Noise` overflow, the epoch series, the `Vol_ED` budget, the `1 − δ` — is now
  **derived** from them
  ([`TtcProb.numlattice_union`](Ttc/Analysis/NumLatticeModel.lean#L267) →
  [`TtcProb.numlattice`](Ttc/Analysis/NumLattice.lean#L53) →
  [`TtcProb.volume_estimate`](Ttc/Model/Theorem.lean#L41)). Previously the
  conclusion of the paper's hardest lemma was an input.
* *Not zero*: `law_eq` and `oracle_eq` are strong. They do not merely say the
  primitives are Poisson and fair-coin — they name one specific construction
  ([`Ttc.trajLaw`](Ttc/Analysis/Coupling.lean#L209),
  [`Ttc.trajOracles`](Ttc/Analysis/Coupling.lean#L393)) and assert the
  implementation is it. Whether a real `TTC` implementation matches is a
  modelling judgement no machine check can settle. `rate_eq_L` likewise assumes
  the family's rates are *exactly* the lattice count rather than an estimate of
  it — the general two-sided case is available
  ([`Ttc.window_of_two_sided`](Ttc/Analysis/NumLatticeModel.lean#L104)) but the
  field commits to the exact one. `big` is a genuine assumption too — it says
  `∑θ` clears `(1−ε')·Thresh/8`, i.e. that the instance is in the regime the
  sketch is for. It is not an artifact of the formalisation: it is the paper's
  own regime, and the witness satisfies it by construction
  ([`Ttc.Box.epsPrime_thresh_le_Lval`](Ttc/Analysis/BoxProb.lean#L210)). What is
  *no longer* assumed is the epoch index: `jstar` and its window used to be four
  more existence assumptions about the instance, and `Ttc.exists_epoch` now
  proves them for every input that satisfies `big`. (`Ttc.Box.exists_jstar`
  survives at [BoxProb:221](Ttc/Analysis/BoxProb.lean#L221) but is **unused** —
  nothing needs it now.)
* Also note the sampling interface is **level-aware** where the paper's is not
  (`pois` and `gen` receive the cube and level). That deviation is what makes the
  coupling constructible at all; see [`AUDIT.md`](AUDIT.md) §1 and finding 15.

*Proved*, and no longer merely cited:

* **`lem:chernoff` itself** ([`Analysis/Chernoff`](Ttc/Analysis/Chernoff.lean)),
  which the paper takes from Soos et al. and Mathlib does not carry. Built from
  the ground up: the Poisson moment generating function
  `E[e^{tN}] = exp(λ(eᵗ−1))` (`Ttc.mgf_poissonMeasure`), the Chernoff bound at
  the optimal `t = log(1+ζ/λ)` giving Bennett's form (`Ttc.poisson_bennett`),
  and the scalar step `h(u) ≥ u²/(2+u)` (`Ttc.bennett_le`) that turns Bennett
  into the paper's `exp(−ζ²/(2λ+ζ))` — plus the lower tail
  (`Ttc.poisson_lower_tail`) and the two-sided form
  (`Ttc.poisson_tail_two_sided`).
* **Both of the paper's uses of it**, with the constants confirmed exact:
  `Pr[N > Thresh] ≤ e^(−Thresh/6)` when the rate is at most `Thresh/2`
  (`Ttc.poisson_overflow`), and `Pr[|N−λ| ≥ ε'λ] ≤ 2e^(−ε'²λ/3)`
  (`Ttc.poisson_relative`).
* Its engine `lem:process` (Poisson splitting, `Ttc.poisson_splitting`); the
  whole epoch union-bound skeleton — the doubly-exponential series
  `∑ 2e^{−a·2ᵗ} ≤ 4e^{−a}` (`Ttc.epoch_series_le`), the `Err` branch
  (`Ttc.err_sum_le_delta`), the `Noise` branch (`Ttc.noise_bound_le_delta`),
  their combination (`Ttc.numlattice_failure_bound`); the interval arithmetic
  behind `ε' = ε/12` (`Ttc.sketch_interval`, `Ttc.sketch_window`,
  `Ttc.Params.epsPrime_window`); and the `Vol_ED` failure budget the paper omits
  (`Ttc.Params.vol_failure_eq`, `Ttc.numlattice_failure_bound_with_vol`; finding 13).

*How the probabilistic model got built.* Every estimate the proof invokes is a
theorem, and they are now composed into a statement about `Ttc.run` — first for
the run driven by the *coupled family*, and then, via the sampler fields above,
for the arbitrary `Ω`/`μ`/`O` a `Ttc.TtcProb` carries. All four of the original
obstacles are cleared:

1. ~~`Ttc.Oracles` cannot express independence.~~ **Fixed.** Oracle calls are now
   indexed by a clock, and distinct call sites provably get distinct indices, so
   "the draws are independent" is statable. This also repaired a real
   distributional defect in the old model — see
   [the `Pseudocode` notes](#what-ttcmodelpseudocodelean-does-and-does-not-do).
2. ~~`lem:process` is only a pmf identity.~~ **Fixed.**
   [`Ttc.countLaw_eq_pi`](Ttc/Analysis/PoissonLaws.lean#L91) proves it as an
   identity of *measures*, which yields independence of the cell counts
   ([`iIndepFun_countLaw`](Ttc/Analysis/PoissonLaws.lean#L106)), Poisson thinning
   ([`poisson_thinning`](Ttc/Analysis/PoissonLaws.lean#L204)) and superposition
   ([`poisson_add`](Ttc/Analysis/PoissonLaws.lean#L217)) — exactly the three
   operations the loop performs on the invariant.
3. ~~The number of halvings is a stopping time.~~ **Resolved, and it turned up a
   genuine error** — see finding 14. Conditioning on the rate is not merely hard,
   it is *wrong*; the invariant has to be read non-adaptively. The level-`j`
   process ([`Ttc.levelLaw`](Ttc/Analysis/SketchProcess.lean#L55)) is that
   reading, and **both branch estimates and the whole `δ` budget are now proved
   over it**: [`levelLaw_err_le`](Ttc/Analysis/SketchProcess.lean#L130),
   [`err_branch_sum`](Ttc/Analysis/SketchProcess.lean#L179),
   [`levelLaw_noise_le`](Ttc/Analysis/SketchProcess.lean#L194), assembled in
   [`numlattice_failure_le`](Ttc/Analysis/SketchProcess.lean#L246) — the paper's
   `δ/6 + δ/6 + δ/2 ≤ δ`, with the algorithm's own `Thresh` and `δ'`.
4. ~~The coupling is missing.~~ **Built.** On the event that the run stops at
   level `J`, the run's final `𝒳` must *be* the level-`J` process. It now is,
   pathwise: [`Ttc.trajOracles`](Ttc/Analysis/Coupling.lean#L393) is an
   `Ttc.Oracles` bundle that answers every call by reading a trajectory `ω` of
   the family, and
   [`Ttc.card_run_eq_sum_traj`](Ttc/Analysis/RunCoupling.lean#L263) proves
   `|𝒳| = ∑ₛ ω(J)ₛ` on every nested trajectory —
   [`run_eq_traj`](Ttc/Analysis/RunCoupling.lean#L281) turns that into
   `|𝒳|/p = 2^J·∑ₛ ω(J)ₛ`, the output itself. See finding 15 for the details;
   the structural half that made it possible was the two missing contracts,
   both added: `Oracles.halve_le` (thinning returns a *sub*-multiset, not merely
   a smaller one) and [`TtcProb.gen_mem`](Ttc/Model/ProblemSetting.lean#L119)
   (`GenerateSamples` returns points of `P(cᵢ) ∩ 𝕃ⁿ` — previously only their
   *number* was constrained). Together they give
   [`TtcProb.run_state_mem`](Ttc/Analysis/LatticeAssembled.lean#L211): the run's
   `𝒳` never leaves `Sol(F) ∩ 𝕃ⁿ`, so it *is* a count vector over a fixed finite
   set.

   The **two operations on the invariant** are now proved, in the exact form the
   induction consumes:
   * *thinning* (line 33/40's `halve`) —
     [`pi_poisson_bind_binomial_half`](Ttc/Analysis/Thinning.lean#L207): a product
     of `Pois(θᵢ)` binomially thinned coordinatewise is a product of `Pois(θᵢ/2)`.
     In **kernel** form (`Measure.bind`), not as a marginal, since that is what a
     loop step actually does. Needs Tonelli for a finite product of series in
     `ℝ≥0∞`, which Mathlib lacks — [`tsum_pi_prod`](Ttc/Analysis/Thinning.lean#L177);
   * *block replacement* (`dropCovered` then `GenerateSamples`) —
     [`pi_poisson_replace`](Ttc/Analysis/Thinning.lean#L252).

   And a simplification worth recording: because `dropCovered` deletes **every**
   point of `P(cᵢ)` before `gen` re-adds them, each point's count comes from
   exactly one insertion — *the last cube containing it*. The invariant therefore
   never needs Poisson **superposition**, only these two operations.

   The **past-measurability layer** is also done, and purely structurally — no
   probability in it. Each loop reads only its own window of clocks
   ([`halveDown_congr`](Ttc/Analysis/Invariants.lean#L174),
   [`absorb_congr`](Ttc/Analysis/Invariants.lean#L194)), one iteration reads only
   `[st.clock, st.clock + 3·fuel + 2)`
   ([`step_congr`](Ttc/Analysis/Invariants.lean#L289)), and hence the whole run
   reads only clocks below `|D|·(3·fuel + 2)`
   ([`run_congr`](Ttc/Analysis/Invariants.lean#L395)). That is exactly what says the
   state is a function of the draws *strictly before* its clock, which is what
   makes their independence usable.

   It also has a useful corollary: the run depends on only **finitely many**
   draws, so the randomness can be modelled by a *finite* product measure — no
   infinite-product machinery is needed. It is what lets the oracle contract
   ([`Ttc.OracleLaws`](Ttc/Analysis/OracleLaws.lean#L63)) be asserted only for
   the draws below [`clockBound`](Ttc/Analysis/OracleLaws.lean#L44), via
   [`run_eq_of_agree_below`](Ttc/Analysis/OracleLaws.lean#L48).

5. **And the bound itself is proved for the coupled run.**
   [`Ttc.traj_numlattice_le`](Ttc/Analysis/RunCoupling.lean#L685) bounds
   ```
   Pr[ ¬( (1−ε/3)·L ≤ run P (trajOracles …) fuel ρ l ≤ (1+ε/3)·L ) ]
   ```
   by `∑_{t<j*} 2exp(−ε'²·λ*·2ᵗ/3) + exp(−Thresh/6)` — the paper's expression,
   and in fact **smaller than the paper's**: the covering statement carries an
   extra `+ δ/2` and a factor `m` on the overflow term that the proof does not
   need.
   Its hypotheses are `hlo`/`hhi` (the window relating `∑θ` to `L`, supplied by
   the already-proved `lem:lattice`), `hsmall` and `hrate` (conditions on
   `Thresh` and `vol`), and `hall`/`hcov` (the cubes cover every lattice point,
   and the oracle's coverage test agrees with cube membership). **No probability
   claim is assumed.** The pieces are
   [`traj_failure_le`](Ttc/Analysis/RunCoupling.lean#L614) (the epoch union
   bound), [`trajLaw_err_le`](Ttc/Analysis/RunCoupling.lean#L511) and
   [`trajLaw_noise_le`](Ttc/Analysis/RunCoupling.lean#L527) (the level estimates
   transported to the trajectory space along
   [`map_trajLaw_eval`](Ttc/Analysis/Coupling.lean#L274)),
   [`level_cap_subset`](Ttc/Analysis/RunCoupling.lean#L471) (reaching `j*` forces
   an overflow), and [`trajLaw_ae_nested`](Ttc/Analysis/RunCoupling.lean#L592)
   (nestedness, the one hypothesis every pathwise result carries, holds almost
   surely).

6. **And the field is gone.** `traj_numlattice_le` is about the trajectory model
   — `trajLaw θ` on `ℕ → (Fin L → ℕ)`, with the oracles `trajOracles` — whereas
   `Ttc.TtcProb` carries an arbitrary `Ω`, `μ` and `O`. The sampler fields close
   that last gap, and
   [`Ttc.numlattice_union_of_model`](Ttc/Analysis/NumLatticeModel.lean#L35) is
   the transport: the failure event is the `toTraj`-preimage of the
   trajectory-space one (by `oracle_eq`), `Measure.le_map_apply` bounds its
   measure by the pushforward, and `law_eq` identifies that pushforward as
   `trajLaw θ`. (No measurability of the failure event is needed — the
   inequality only runs one way.) Feeding it the fields gives
   [`Ttc.TtcProb.numlattice_union`](Ttc/Analysis/NumLatticeModel.lean#L267),
   which is the deleted field's statement, verbatim, as a theorem.

**No fuel-adequacy hypothesis is needed.** Both `while` loops return the current
state when the budget runs out, so one might expect the result to need a lower
bound on `fuel`; it does not. `traj_numlattice_le` holds for *every* `fuel`,
because the coupling makes the output a function of whatever level the run
actually reached, and the `hsmall` hypothesis — no cube's rate still triggers a
halving at level `j*−1` — does the work the paper leaves to termination. That
hypothesis used to be the `rate_small` field; it is now *derived*, from `vol_pos`
and [`Ttc.TtcProb.vol_le_total`](Ttc/Analysis/NumLatticeModel.lean#L260) via
[`Ttc.rate_small_of_epoch`](Ttc/Analysis/NumLatticeModel.lean#L180). The witness
runs at `fuel = 0`. The paper addresses none of this.

**These proofs confirm the algorithm's constants.** `ε' ← ε/12` (`alg:ttc` line
18) is exactly what makes the two-sided `(1±ε')` loss fit inside `(1±ε/3)`; each
branch of `Thresh` (line 20) is exactly what makes its failure branch `δ/6`
(total `δ/3`, so there is slack); `γ` is exactly what makes
`κ/γ ≤ η/(32mn)` — with no slack at all, which is why `γ` and `κ` must use the
same logarithm argument (`Ttc.Params.kappa_div_gamma_le`,
`Ttc.Params.shell_factor_bound`); and `ρ ← ⌈log₁₀(γ/γ̂)⌉` is exactly what lifts the
input's inscribed radius `γ̂` to the `γ` the shell bound needs, after dilating to
`ℤⁿ` (`Ttc.gamma_le_latticeScale_mul`).

## Scope, stated precisely

* **This is an accuracy guarantee, not an FPRAS claim.** `thm:runtime` (the `O(mn⁴)`
  runtime) and `thm:decompose` (the exponential decomposition cost) are **not**
  formalised. Nothing here says anything about running time.
* **The `δ` is derived, end to end.** `Ttc.TtcProb.volume_estimate` really does
  conclude `Pr[ output ∈ (1±ε)·Vol(F) ] ≥ 1 − δ`: `Ttc.TtcProb.numlattice` gives
  `Pr[ output ∈ (1±ε/3)·L ] ≥ 1 − δ` — *proved*, from
  `Ttc.TtcProb.numlattice_union` plus the algorithm's own `Thresh` and `δ'` — and
  the deterministic chain shows the first event *contains* the second, so measure
  monotonicity carries the bound. The covering is itself proved
  ([`Ttc.numlattice_union_of_model`](Ttc/Analysis/NumLatticeModel.lean#L35), from
  [`Ttc.traj_numlattice_le`](Ttc/Analysis/RunCoupling.lean#L685)). **What the
  chain rests on is the sampler description**, not a probability bound: if the
  implemented sampler is not `Ttc.trajOracles` reading `Ttc.trajLaw`, the theorem
  says nothing about it.
* **`GetPrecision` is not verified as an algorithm.** Its *mathematical
  content* — that dilation scales inscribed-ball radii (`Ttc.ball_radius_scales`)
  and volumes (`Ttc.volume_smul_body`), and that the resulting `γ` satisfies
  `claim:helper` (`Ttc.claim_helper`) — is proved; the LP-based implementation is not
  modelled.

## Findings: the formalisation as a referee

Formalising forced hypotheses the paper does not state. Line references are to
the **current** working tree; statuses reflect edits already applied to
`sections/analysis.tex`.

### 1. Genuine error — `lem:nonconv`'s upper bound. *Partially fixed; residual gap.*

**Originally:** the chain ended `… ≤ |Q∩ℤⁿ|/vol Q`, justified by "the last
inequality follows from `Q ⊆ Q''`". But `Q''` is the family **deflated** by
`κ‖A_ij‖` (`analysis.tex:140`), so `Q'' ⊆ Q` — the opposite containment.

**Now:** the chain correctly ends `= |Q∩ℤⁿ|/vol Q''` and the false justification
is gone. What remains is the final step at **`analysis.tex:222`**:

> "And using `vol Q ≤ vol Q' ≤ kⁿ vol Q'' ≤ ((1+η/4)/(1−η/4))·vol Q''` gives
> `vol Q ≤ (1+η)|Q∩ℤⁿ|`."

This still does not follow. Combined with `vol Q'' ≤ |Q∩ℤⁿ|/(1−η/2)` it needs

`(1+η/4) / ((1−η/4)(1−η/2)) ≤ 1+η`,

and `(1+η/4) − (1+η)(1−η/4)(1−η/2) = η²(5−η)/8 > 0` for every `η ∈ (0,1]` — so
the inequality fails throughout the range. At `η = 1` the chain gives `3.33·N`,
not `2·N`.

**The fix** (proved, `Ttc/Analysis/Repair.lean`): run the construction with internal
parameter `θ = η/2`. Then the stated conclusion holds verbatim:

```lean
theorem Ttc.nonconv_repaired (hη : 0 < η) (hη1 : η ≤ 1) (hN : 0 ≤ N)
    (hA  : (1 - η/4) * N      ≤ volQ')                -- claim:cl(a)   at η/2
    (hBC : (1 - η/4) * volQ'' ≤ N)                    -- claim:cl(b,c) at η/2
    (hK  : volQ' ≤ ((1 + η/8) / (1 - η/8)) * volQ'')  -- claim:helper  at η/2
    (hsub : volQ'' ≤ volQ) (hsup : volQ ≤ volQ') :
    (1 - η) * N ≤ volQ ∧ volQ ≤ (1 + η) * N
```

Enabling inequalities: `1 + η/8 ≤ (1+η)(1−η/8)(1−η/4)` (`repair_upper_arith`)
and `(1−η)(1+η/8) ≤ (1−η/8)(1−η/4)` (`repair_lower_arith`).

**Cost: ≤ one decimal digit.** `γ` goes from `(16n/η)√(log(4r/η))` to
`(32n/η)√(log(8r/η))`, and `γ(η/2) ≤ 3γ(η)` (`gamma_half_le`); since
`log₁₀ 3 < 1`, `ρ` rises by at most one (`precision_increase_le_one`).

**Still to change:** `sections/algo.tex:86` (`γ ← (16n/η)√(log(4r/η))` →
`γ ← (32n/η)√(log(8r/η))`) and the hypothesis at `analysis.tex:122`.

### 2. Genuine gap — the inscribed ball must be about a *common* centre. *Solved.*

`sections/analysis.tex:212`: from "each `P_i` contains an `ℓ₂`-ball of radius at
least `γ`" the paper concludes `b_ij ≥ γ‖A_ij‖`. That needs the ball centred at
the **origin** — a ball at `c` only gives `b_ij − A_ij c ≥ γ‖A_ij‖` — and since
`p ↦ p/k` is a homothety about the origin, a *union* needs one common centre for
all `P_i`. That is strictly stronger than the stated hypothesis and is
unsatisfiable when the DNF cubes' polytopes are disjoint.

Two sub-slips in the same sentence: "for the pair `i,j` at which `k` is attained"
— the bound is needed at **every** facet, and in fact `k` is attained at the facet
*nearest* the origin, since `t ↦ (t+κ)/(t−κ)` is decreasing (`ratio_antitone`);
a single facet with `b < γw` breaks the step (`facet_ratio_fails`). And
"`A_ij p ≤ b'_ij` for all `i,j`" — `p ∈ Q'` only gives membership in *some* `P'_i`.

**Resolution** (proved, `Ttc/Analysis/Recentred.lean`) — the assumption is *removed*, not
assumed away:

1. Use `AffineMap.homothety cᵢ k` about each polytope's **own** centre
   (`piece_inflated_subset_homothety`, `volume_piece_inflated_le`). No relation
   between the `cᵢ` is needed.
2. Compare *shells*, not bodies: `Q' ⊆ Q ∪ ⋃ᵢ (P'ᵢ \ Pᵢ)`
   (`body_subset_union_shells`), giving `vol Q' ≤ (1 + m(kⁿ−1))·vol Q`
   (`shell_bound`).

Cost: the internal parameter must be `θ ∼ η/m`, so `γ` grows by `O(m²)`
(`gamma_scale_cost`) and `ρ` by `O(log m)` digits — benign, since `ρ` enters only
as a coordinate bit-length. *Caveat:* the `m` is not shown to be necessary; the
shell union bound is visibly loose when the `Pᵢ` nest.

### 3. Genuine error — a missing square in `claim:cl`'s Azuma exponent

`sections/analysis.tex:177` (now an active proof, no longer commented) displays

> `Pr(A_ij Y ≥ κ) ≤ 2 exp(−κ²‖A_ij‖ / (2 ∑_{k'} |A_ijk'|²))`.

Since `∑_{k'} |A_ijk'|² = ‖A_ij‖²`, the exponent as written is `−κ²/(2‖A_ij‖)`,
which is not scale-invariant — rescaling a facet's `(A_ij, b_ij)` changes it
though the event does not — and does not yield the claimed `η/(2r)`. The
numerator needs `‖A_ij‖²`.

With the square restored, Hoeffding gives exactly the right thing for the event
`A_ij·Y ≥ κ‖A_ij‖`:

```lean
theorem Ttc.rounding_tail_bound … :
    μ.real {ω | κ * coeffNorm A ≤ ∑ k, A k * Y k ω} ≤ Real.exp (-κ ^ 2 / 2)
```

At the paper's `κ = √(2 log(4/η)) + √(2 log r)` this is `≤ η/(4r)`
(`rounding_tail_bound_kappa`), so the union bound over `r` facets gives `η/4` —
inside the `η/2` needed. **The claim is true as used; only the exponent is wrong.**

Two further slips in the same line: the event is `A_ij Y ≥ κ‖A_ij‖` but the
display writes `Pr(A_ij Y ≥ κ)`; and `|Z_k − Z_{k−1}| ≤ A_ijk` should be
`≤ |A_ijk|`. The leading factor `2` is also unnecessary (the event is one-sided)
— that is where the slack between `η/4` and `η/2` comes from.

*(The earlier mismatch between `Y ∈ [−1,1]ⁿ` and a side-1 cube `C(x)` is now
fixed — `analysis.tex:171` says side length 2.)*

### 4. Boundary imprecision — `claim:helper` is false at `n = 0`

Statement at `sections/analysis.tex:216` ("For `n ∈ ℕ`"); the proof at
`sections/proof-appendix.tex:139` displays `((n + η/8)/(n − η/8))ⁿ`, whose base is
**negative** at `n = 0`, and `proof-appendix.tex:143` ("since `η < n` …") silently
assumes `n ≥ 1`. Harmless — `n` is the ambient dimension — but unstated. Carried
explicitly as `1 ≤ n` in `Ttc.claim_helper`.

### 5. Fine, implicit — negative literals give *open* half-spaces

`sections/algo.tex:51` says a cube's conjunction "defines a (possibly empty)
convex polytope". A negated atom `¬(A_ij x ≤ b_ij)` denotes the **open**
half-space `{x | b_ij < A_ij x}`. The region is convex (`Ttc.convex_region`,
proved) but in general **not closed**, hence not a polytope in the standard
`Ax ≤ b` sense that `lem:integerlattice` (KV97, Theorem 3) is stated for.

For the **volume** side this is harmless — the boundary is Lebesgue-null, so
`vol P(c)` is unaffected. But `lem:nonconv` and `lem:lattice` also count **lattice
points**, and the boundary is exactly where a set and its closure differ for
counting: in one dimension, `¬(x ≤ 0)` denotes `{x | 0 < x}`, whose closure gains
the lattice point `0`, and on the fine lattice `𝕃ⁿ = 10^(−ρ)·ℤⁿ` a facet
hyperplane can carry many such points. Since `L` is *defined* as
`|Q ∩ 𝕃ⁿ|/10^(ρn)`, "volumes agree so nothing breaks" covers only half the claim.

This is why [`Ttc.facetSystem`](Ttc/Analysis/FacetOfDNF.lean#L57) is built only
for DNFs whose literals are all positive
([`Ttc.DNF.IsPositive`](Ttc/Model/Prelude.lean#L129)): a
`Ttc.FacetSystem.piece` is an intersection of closed half-spaces, so no facet
system can denote a region with a negated atom.

### 6. Fine, implicit — `thm:decomposition`'s soundness argument is misphrased

`sections/analysis.tex:71`: "By construction, we have `ℓ_ij ⊨ F_dnf`. Therefore,
by the property of Boolean abstraction, if `⋀ M(ℓ_ij)` can be satisfied, then `F`
is satisfied." An individual literal does not entail the DNF, and the direction
needed is that the *cube* entails the formula. The correct sufficient hypothesis
is that DNF and formula agree on every Boolean assignment (`Ttc.IsDNFOf`) — what a
correct AllSAT/`ToDNF` delivers. Under it both inclusions are one line
(`region_subset_sol`, `sol_subset_iUnion_region`).

### 7. Fine, implicit — two side conditions are unnecessary

`Ttc.lower_combine` (`(1−ε/3)/(1+ε/8) ≥ 1−ε`) and `Ttc.nonconv_lower_arith`
(`((1−η/4)/(1+η/4))(1−η/2) ≥ 1−η`) hold for **all** positive `ε`, `η`; the
paper's `≤ 1` side conditions are not needed.

### 8. Presentational — `lem:process`'s first display conflates `ζ` and `ζᵢ`

`sections/proof-appendix.tex:99` derives the single-coordinate case treating `ζ`
as one scalar shared by all elements, then reintroduces per-element `ζᵢ` at
`proof-appendix.tex:112`. Only the second computation is needed.
`Ttc.poisson_splitting` proves the general statement (arbitrary probability
vector `q`), strictly stronger than either display; neither `η`-closeness nor
`α|S| ≤ sz ≤ β|S|` is needed for the *identity* — they only place the resulting
rate in the required interval (`Ttc.rate_mem_interval`).

### 9. Editorial — duplicated sentence

`sections/analysis.tex:222` contains the sentence "Using Claim …, we can upper
bound `vol Q'` … we have `vol Q ≥ (1−η)|Q ∩ ℤⁿ|`." **twice**, verbatim, before the
final clause. Introduced by a recent edit.

### 10. Genuine gap — `lem:nonconv` needs each `Pᵢ` to have finite volume

Nowhere does the paper require the polytopes to be bounded, and `lem:nonconv` is
**false** without something in that direction: a half-space contains an inscribed
ball of every radius, has infinite volume, and contains infinitely many lattice
points, so `vol Q ∈ [(1−η)|Q∩ℤⁿ|, (1+η)|Q∩ℤⁿ|]` degenerates to `∞ ∈ [∞, ∞]` at
best and, with Lean's `Set.ncard`-of-an-infinite-set convention, to `∞ ≤ 0` at
worst. Both summation steps also divide by `vol Q'` and `vol Q''`, which must
therefore be finite and nonzero.

Carried explicitly as [`volume_ne_top`](Ttc/Model/ProblemSetting.lean#L109). It is
the one hypothesis here with no counterpart at all in the paper. (Positivity is
*not* assumed: it follows from the inscribed ball, via
[`FacetSystem.volume_piece_pos`](Ttc/Analysis/NonconvAssembled.lean#L104).)

### 11. Fine, implicit — a facet needs a nonzero normal, and finiteness of `Q ∩ ℤⁿ` needs an argument

Two more things the proof uses without saying so.

* **`A_ij ≠ 0`.** The Azuma/Hoeffding step divides by `‖A_ij‖`, and the crossing
  event `A_ij·Y ≥ κ‖A_ij‖` is *certain* when `A_ij = 0`, so the tail bound is
  false for a degenerate "constraint" `0 ≤ b`. Carried as
  [`normal_ne_zero`](Ttc/Model/ProblemSetting.lean#L93).
* **`|Q ∩ ℤⁿ|` is a finite number.** The paper writes it throughout without
  remark. It is *not* assumed here: `claim:cl`(a) bounds `|T|` for every finite
  `T ⊆ Q ∩ ℤⁿ` by `vol Q'/(1−θ/2)`, and a set all of whose finite subsets have
  bounded cardinality is finite
  ([`finite_of_forall_finset_card_le`](Ttc/Analysis/BallFacet.lean#L135)). So the
  gap is real but self-closing.

### 12. Fine, implicit — the deflated shell loses twice what the inflated one does

The shell argument is run once and applied in both directions, as if the inflated
and deflated bodies cost the same factor. They do not: the deflated side compares
against a ball of radius `γ − κ`, not `γ`, so its factor is `(1 + κ/(γ−κ))ⁿ`
rather than `(1 + κ/γ)ⁿ` — a factor `2` worse once `κ ≤ γ/2`
([`Ttc.Params.shell_factor_bound`](Ttc/Analysis/Parameters.lean#L102) gives
`1 + η/(16m)`, [`shell_factor_bound_deflated`](Ttc/Analysis/Parameters.lean#L144)
only `1 + η/(8m)`).

Harmless — the two-sided bound still closes with the two losses kept apart
([`nonconv_recentred_general`](Ttc/Analysis/NonconvAssembled.lean#L49): the lower
bound consumes only the inflated loss and the upper bound only the deflated one) —
but a proof that equalises them silently is off by a factor of two.

### 14. Genuine error — the sketch invariant is false if read as conditioning

`sections/analysis.tex:262` states the invariant as

> "For any `i ∈ [m]` and `j ≥ 0` the multiset `𝒳⁽ⁱ⁾ⱼ` contains `k` copies of each
> lattice point inside `S⁽ⁱ⁾`, where `k` is drawn from `Pois(p̃ⱼ)`"

with `𝒳⁽ⁱ⁾ⱼ` defined at `analysis.tex:259` as "the state of `𝒳` after consuming
`Pⁱ` **when the value of `p` is `1/2ʲ`**". Read literally — conditioning on the
rate being `2^(−j)` — this is **false**. Halting is a stopping time, and
conditioning on it distorts the law.

**Counterexample.** Two lattice points, rule "while `|𝒳| > 1`, halve", starting
from both present. Conditioned on stopping at `p = ½` (i.e. one halving
sufficed), the state is `Bernoulli(½)²` conditioned on `|𝒳| ≤ 1`: it puts mass
`0` on both points surviving, where the claimed product law puts `¼`. The same
happens for Poisson counts.

**The proof still works, but only under the other reading.** What the union bound
actually uses is `Pr[Nois(j) ∧ Err(j)] ≤ Pr[Err(j)]` — the conditioning is
*discarded*, so `Err(j)` only ever needs to be an unconditional event about the
**non-adaptive** level-`j` process, in which every lattice point independently
carries `Pois(θ/2ʲ)` copies whether or not the run stops there. That is how it is
formalised here ([`Ttc.levelLaw`](Ttc/Analysis/SketchProcess.lean#L55)), and both
branch estimates are proved over it
([`levelLaw_err_le`](Ttc/Analysis/SketchProcess.lean#L130),
[`levelLaw_noise_le`](Ttc/Analysis/SketchProcess.lean#L194)).

So the defect is in the *statement* of the invariant, not in the result — but a
reader who takes the invariant at face value is proving something false.

### 15. Genuine gap — `Err(j)` is not a well-defined event. *Repaired here: the coupling is now constructed.*

This is the sharper form of finding 14. It is a defect in the paper, and the
repair is a construction rather than a rewording — that construction now exists
in this development.

`analysis.tex:277` defines the two events

> `Nois(j)`: after consuming the last polytope `Pᵐ`, the value of `p` is `1/2ʲ`;
> `Err(j)`: at the end of the algorithm `𝒳⁽ᵐ⁾ⱼ ∉ [(1−ε')p̃ⱼ|Q∩𝕃ⁿ|, (1+ε')p̃ⱼ|Q∩𝕃ⁿ|]`

and then bounds `∑_{j<j*} Pr[Err(j)] + Pr[⋃_{j≥j*} Nois(j)]`. For that sum to
mean anything, **`Err(j)` must be an event for every `j`** — but `𝒳⁽ᵐ⁾ⱼ` is
defined as the state "when `p` is `1/2ʲ`", and the run has exactly *one* final
rate. On any given execution `𝒳⁽ᵐ⁾ⱼ` exists for one `j` only; for the others the
event has no referent. Reading it instead as *conditioned* on `Nois(j)` is
finding 14, and false.

**What is needed, and what the paper never constructs**, is a family `𝒳ⱼ` defined
*simultaneously for all `j`* on one probability space, such that

* each `𝒳ⱼ` has the level-`j` law (`Ttc.levelLaw`), and
* the run's final state equals `𝒳_J` where `J` is its actual stopping level.

**Both halves are now proved.** The family is
[`Ttc.famCount`](Ttc/Analysis/Coupling.lean#L80): a level-`0` count `A s` per
lattice point, plus a fair coin per (point, *rank*, level), thinned recursively.
Indexing the coins by rank among the current survivors rather than by original
copy is what makes the recursion implementable from a count alone — which is all
the `halve` oracle gets to see. Its law is
[`Ttc.trajLaw`](Ttc/Analysis/Coupling.lean#L209), a measure on whole trajectories
`ℕ → (Fin L → ℕ)` built by iterating
[`thinKernel`](Ttc/Analysis/Coupling.lean#L164), and its marginals are right:

* [`Ttc.map_trajLaw_eval`](Ttc/Analysis/Coupling.lean#L274) — coordinate `j` of a
  trajectory carries exactly `Ttc.levelLaw θ j`, so *every* branch estimate
  already proved for a single level transports to an event of one measure
  ([`trajLaw_err_le`](Ttc/Analysis/RunCoupling.lean#L511),
  [`trajLaw_noise_le`](Ttc/Analysis/RunCoupling.lean#L527)). Underneath is
  [`chainLaw_eq_levelLaw`](Ttc/Analysis/SketchProcess.lean#L105): nested thinning
  from level `0` reproduces `levelLaw θ j` at every `j`.
* [`Ttc.trajLaw_ae_nested`](Ttc/Analysis/RunCoupling.lean#L592) — thinning only
  removes copies, so `ω(j+1)ₛ ≤ ω(j)ₛ` almost surely. Every pathwise result below
  is stated for nested trajectories; this is where that hypothesis is discharged.

The second half — the *coupling to the run* — is
[`Ttc.trajOracles`](Ttc/Analysis/Coupling.lean#L393): an honest `Ttc.Oracles`
bundle, satisfying both of the interface's contracts, whose `halve` returns the
family's next level, whose `pois` returns the family's total over the cube, and
whose `gen` returns the family restricted to the cube. (`gen` must return exactly
`N` points for *every* `N`, so it has a never-taken filler branch — the run only
ever passes it the `N` that `pois` produced — which is what discharges `gen_card`
unconditionally; see [`Ttc.padPoint`](Ttc/Analysis/Coupling.lean#L387).) Driving
the real `Ttc.run` off that bundle,

* [`Ttc.CoupledAt`](Ttc/Analysis/RunCoupling.lean#L31) — the state holds the
  family's counts at the current level, at the points seen so far and nowhere
  else — is preserved by every operation of the loop
  ([`coupledAt_halve`](Ttc/Analysis/RunCoupling.lean#L52),
  [`coupledAt_dropCovered`](Ttc/Analysis/RunCoupling.lean#L104),
  [`coupledAt_halveDown`](Ttc/Analysis/RunCoupling.lean#L132),
  [`coupledAt_absorb`](Ttc/Analysis/RunCoupling.lean#L156),
  [`coupledAt_step`](Ttc/Analysis/RunCoupling.lean#L183),
  [`coupledAt_foldl`](Ttc/Analysis/RunCoupling.lean#L241));
* so [`Ttc.card_run_eq_sum_traj`](Ttc/Analysis/RunCoupling.lean#L263) gives
  `|𝒳| = ∑ₛ ω(J)ₛ` **pathwise**, at the run's own stopping level `J`, on every
  nested trajectory, and [`run_eq_traj`](Ttc/Analysis/RunCoupling.lean#L281)
  gives the output itself as `2^J · ∑ₛ ω(J)ₛ`.

That is equality of *random variables*, not of laws — which is the point:
`lem:process` supplies only equality in law, and the union bound needs the run
and the level process to agree on each path. The halving triggers close the other
branch: every level the run crosses had either a cube whose rate was still large
or a family total above `Thresh`
([`foldl_trigger`](Ttc/Analysis/RunCoupling.lean#L441)), so reaching the cap `j*`
forces an overflow ([`level_cap_subset`](Ttc/Analysis/RunCoupling.lean#L471)) —
which is what `Pr[⋃_{j≥j*} Nois(j)]` was supposed to mean. Assembling,
[`Ttc.traj_numlattice_le`](Ttc/Analysis/RunCoupling.lean#L685) proves
`lem:numlattice`'s bound outright for the coupled run, with a *smaller*
right-hand side than the paper's.

The paper cites `lem:process` for the *equivalence* of its three procedures but
never builds the coupled family, and without it the union bound has nothing to
range over. So `lem:numlattice`'s proof as written is not merely imprecise: the
object its main estimate is about does not exist.

**And the repair is now wired into the headline.** `traj_numlattice_le` is about
the trajectory model specifically, while `Ttc.TtcProb` carries an arbitrary `Ω`,
`μ` and `O`; the sampler fields
([`Model/ProblemSetting.lean:133`](Ttc/Model/ProblemSetting.lean#L133) onwards)
identify the two, and
[`Ttc.numlattice_union_of_model`](Ttc/Analysis/NumLatticeModel.lean#L35)
transports the bound across. The `numlattice_union` field is **deleted**; the
same statement is now [a theorem](Ttc/Analysis/NumLatticeModel.lean#L267). So
the coupling is not a side construction the capstone ignores — a transitive
dependency walk from `Ttc.TtcProb.volume_estimate` reaches
`Ttc.traj_numlattice_le` and `Ttc.trajLaw` (see [`AUDIT.md`](AUDIT.md) §5).
What remains is the modelling judgement the fields encode, not a missing
estimate.

### 13. Genuine gap — the `Vol_ED` failures are never union-bounded

`alg:ttc` line 18 sets `δ' ← δ/(2m)` and line 24 calls `Vol_ED(P(cᵢ), ε', δ')`
once per polytope, so the `m` calls fail with total probability up to `δ/2`. The
proof of `lem:numlattice` uses their output as if it were exact —
`analysis.tex:269`: "by the accuracy guarantee of `Vol_ED`, the call returns `t`
such that `t ∈ [(1−ε')vol Pⁱ, (1+ε')vol Pⁱ]`" — and then bounds only
`δ/6 + δ/6`. The `δ/2` never enters the union bound.

**It is harmless, but only because of the slack**: `δ/2 + δ/6 + δ/6 = 5δ/6 ≤ δ`
([`Ttc.numlattice_failure_bound_with_vol`](Ttc/Analysis/Sketch.lean#L168), with
[`Ttc.Params.vol_failure_eq`](Ttc/Analysis/Sketch.lean#L159) showing
`m·δ' = δ/2` exactly). Had `Thresh` been chosen to make each branch `δ/2` rather
than `δ/6`, the stated conclusion would be false. `δ'` was also missing from the
parameter block entirely; it is now
[`Ttc.Params.deltaPrime`](Ttc/Model/Prelude.lean#L225).

**The main result stands.** Finding 1 changes constants, not the shape of the
theorem, and finding 2 is now closed by a different proof; finding 3 is a typo in
an exponent whose corrected form is stronger than needed; finding 14 is a false
*statement* of a true step; findings 10 and 13 are gaps the paper genuinely needs
closing (one by an added hypothesis, one absorbed by existing slack); 4–9, 11 and
12 are presentational or self-closing. **Finding 15 is the one that needed a
construction, and it now has one**: the coupled family and its pathwise
identification with the run are built here
([`Analysis/Coupling`](Ttc/Analysis/Coupling.lean),
[`Analysis/RunCoupling`](Ttc/Analysis/RunCoupling.lean)), `lem:numlattice`'s
bound is proved for the run they drive, and
[`Analysis/NumLatticeModel`](Ttc/Analysis/NumLatticeModel.lean) transports it to
any problem instance whose randomness *is* that construction — which is what
deleted the last assumed field. What is left is not mathematics but the
modelling judgement: whether a real `TTC` implementation's sampler is the one
`law_eq` and `oracle_eq` describe.
