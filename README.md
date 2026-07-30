# A Lean 4 formalisation of *Efficient Volume Computation for SMT Formulas*

Machine-checked, `sorry`-free, axiom-clean formalisation of the analysis of the
`TTC` algorithm (Shaw, Sarkar, Meel), following the methodology in
[`CLAUDE.md`](CLAUDE.md).

**Every declaration in this development is proved.** There is no `sorry`, no
custom `axiom`, and no `native_decide` — verified across all 139 declarations
(see [Verifying the claim](#verifying-the-claim)). Two ingredients of the paper
are *not* formalised and instead enter as explicit hypotheses of a bundling
structure; they are named precisely in [What is assumed](#what-is-assumed).

Formalising also acted as a referee: it turned up **two genuine errors** and one
genuine gap in the published proofs, with machine-checked repairs for all three.
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

Those three are Mathlib's standard foundational axioms. A sweep over **every**
declaration in the development (139 of them: theorems, definitions and
structures) gives:

| Axiom profile | Count |
| --- | --- |
| `[propext, Classical.choice, Quot.sound]` | 120 |
| `[propext, Quot.sound]` (weaker) | 2 — `region_eq_iInter`, `sol_subset_iUnion_region` |
| *does not depend on any axioms* | 17 |
| **anything involving `sorryAx` or a custom `axiom`** | **0** |

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
    Cl.lean                   -- claim:cl (a),(b),(c) over the rounding kernel
    Lattice.lean              -- lem:lattice: transport ℤⁿ ↔ 𝕃ⁿ = 10⁻ᵖ·ℤⁿ, and its instantiation
    Poisson.lean              -- lem:process: Poisson splitting
    Sketch.lean               -- lem:numlattice's epoch skeleton
    Invariants.lean           -- structural invariants of the modelled main loop
    Capstone.lean             -- the two chains combining lem:lattice with lem:numlattice
```

**Reading order for an auditor: `Model/`, in this order, then stop.**
[`Model/Prelude`](Ttc/Model/Prelude.lean) fixes what every name means, including
`Vol(F)` and the `(1±ε)` interval. [`Model/ProblemSetting`](Ttc/Model/ProblemSetting.lean)
records that the set the algorithm enumerates is the set the theorem bounds.
[`Model/Pseudocode`](Ttc/Model/Pseudocode.lean) is the code — read it against
`sections/algo.tex` — and ends with `Ttc.TtcProb`, **every hypothesis the result
rests on**, as fields. [`Model/Theorem`](Ttc/Model/Theorem.lean) states what is
proved.
Anything you still doubt is a named lemma in `Analysis/`.

| Surface module | Contains | Status |
| --- | --- | --- |
| [`Model/Prelude.lean`](Ttc/Model/Prelude.lean) | `Ttc.Space n`, `BForm`/`Lit`/`Cube`/`DNF`, `sol`, `region`, `Ttc.Params`: `η`, `ε'`, `Thresh`, `κ`, `γ`, `ρ`, [`volSol`](Ttc/Model/Prelude.lean#L120) (= `Vol(F)`), [`relErr`](Ttc/Model/Prelude.lean#L128) | definitions only |
| [`Model/Pseudocode.lean`](Ttc/Model/Pseudocode.lean) | `SketchState`, `Oracles`, `dropCovered`, `halveDown`, `absorb`, `step`, [`run`](Ttc/Model/Pseudocode.lean#L101), [`ttcOutput`](Ttc/Model/Pseudocode.lean#L107), and [`TtcProb`](Ttc/Model/ProblemSetting.lean#L31) — the complete list of assumptions | modelled; see caveats |
| [`Model/Theorem.lean`](Ttc/Model/Theorem.lean) | [**`TtcProb.volume_estimate`**](Ttc/Model/Theorem.lean#L40) (`Pr ≥ 1−δ`) — one theorem, nothing else | proved from the `TtcProb` fields |

### What `Ttc/Model/Pseudocode.lean` does and does not do

It is a line-by-line model of `alg:ttc` lines 22–46: the state `(X, p)`, the
order of operations, both `while` guards, the coverage filter, and the output
`|X|/p`. Read it beside the pseudocode.

Four external calls are **fields of `Ttc.Oracles`** rather than definitions —
`Vol_ED`, the Poisson draw, `GenerateSamples`, and the fair-coin thinning. So the
state evolution is deterministic *given the oracle's answers*, and all the
randomness sits at that boundary. That is deliberate: the distribution of the
output is `lem:numlattice`, which this development assumes.

The precision `ρ` is threaded properly: `GenerateSamples` is
[`gen : ι → ℕ → ℤ → Multiset (Space n)`](Ttc/Model/Pseudocode.lean#L64), `ρ` is
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
[`Ttc.ttcOutput`](Ttc/Model/Pseudocode.lean#L107) *is* `Ttc.run` with the oracles
drawn at a sample point, so the headline measures the algorithm directly:

```lean
noncomputable def Ttc.ttcOutput (P : Params) (O : Ω → Oracles n ι) (fuel : ℕ)
    (cubes : List ι) (ω : Ω) : ℝ :=
  run P (O ω) fuel cubes
```

What *is* assumed is `lem:numlattice` — but stated about that same output, as a
field of [`Ttc.TtcProb`](Ttc/Model/ProblemSetting.lean#L31):

```lean
numlattice : 1 - δ ≤ (μ {ω | (1-ε/3)*L ≤ ttcOutput P O fuel D ω ∧
                             ttcOutput P O fuel D ω ≤ (1+ε/3)*L}).toReal
```

so the headline needs **no side hypothesis**. The structure is inhabited
([`Ttc.nonempty_ttcProb`](Ttc/Analysis/Capstone.lean#L220), witness
[`Ttc.trivialProb`](Ttc/Analysis/Capstone.lean#L175)), so this is not vacuous —
but that witness is degenerate (`Vol(F) = 0`, output `0`), and **nothing here
shows `numlattice` holds of the real algorithm**. Proving it is the main
remaining work.

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
| `lem:chernoff` | Poisson tail bound (Soos et al.) | — | **assumed** (external) |
| `lem:process` | three sampling procedures are equivalent | [`poisson_splitting`](Ttc/Analysis/Poisson.lean#L60), [`poisson_splitting_paper`](Ttc/Analysis/Poisson.lean#L107), [`rate_mem_interval`](Ttc/Analysis/Poisson.lean#L123) | **proved** |
| `lem:integerlattice` | KV97 Thm 3, single polytope | — | external; superseded by `lem:nonconv` |
| `lem:nonconv` | `vol Q ∈ [(1−η)\|Q∩ℤⁿ\|, (1+η)\|Q∩ℤⁿ\|]` | skeleton [`nonconv_lower`](Ttc/Analysis/Nonconv.lean#L101), [`nonconv_upper_deflated`](Ttc/Analysis/Nonconv.lean#L124), [`nonconv_upper_repaired`](Ttc/Analysis/Nonconv.lean#L140); geometry [`FacetSystem.inflated_subset_smul_deflated`](Ttc/Analysis/Geometry.lean#L102), [`volume_inflated_le`](Ttc/Analysis/Geometry.lean#L124) | proved from `claim:cl` — **see findings 1 & 2** |
| ↳ repaired | same statement, internal `θ = η/2` | [`nonconv_repaired`](Ttc/Analysis/Repair.lean#L75), [`repair_upper_arith`](Ttc/Analysis/Repair.lean#L52), [`repair_lower_arith`](Ttc/Analysis/Repair.lean#L58) | **proved** |
| ↳ shell bound, instantiated | `vol Q' ≤ (1+m(K−1))·vol Q` and `vol Q ≤ (1+m(K−1))·vol Q''`, from the actual sets | [`piece_inflated_subset_homothety_zero`](Ttc/Analysis/Recentred.lean#L211), [`volume_shell_le`](Ttc/Analysis/Recentred.lean#L284), [`volume_body_inflated_le`](Ttc/Analysis/Recentred.lean#L476), [`volume_body_deflated_le`](Ttc/Analysis/Recentred.lean#L531) | **proved** — both sides; `shell_bound`'s three hypotheses discharged from geometry |
| ↳ `Q = Sol(F)` | the facet system of a positive DNF | [`facetSystem`](Ttc/Analysis/FacetOfDNF.lean#L66), [`region_eq_piece`](Ttc/Analysis/FacetOfDNF.lean#L76), [`body_eq_sol`](Ttc/Analysis/FacetOfDNF.lean#L97) | **proved** for `DNF.IsPositive` — see finding 5 |
| ↳ without common ball | per-polytope homothety + shell bound | [`piece_inflated_subset_homothety`](Ttc/Analysis/Recentred.lean#L69), [`volume_piece_inflated_le`](Ttc/Analysis/Recentred.lean#L100), [`body_subset_union_shells`](Ttc/Analysis/Recentred.lean#L183), [`shell_bound`](Ttc/Analysis/Recentred.lean#L457) | **proved** |
| `claim:cl` | rounding hits/misses `Q` w.p. `1 ± η/2` | (a) [`claim_cl_a`](Ttc/Analysis/Cl.lean#L126), (b) [`claim_cl_b`](Ttc/Analysis/Cl.lean#L147), (c) [`claim_cl_c`](Ttc/Analysis/Cl.lean#L114) over [`RoundingKernel`](Ttc/Analysis/Cl.lean#L65); core [`rounding_tail_bound`](Ttc/Analysis/Rounding.lean#L107), [`rounding_tail_bound_kappa`](Ttc/Analysis/Rounding.lean#L132), [`rounding_union_bound`](Ttc/Analysis/Rounding.lean#L165); consumed via [`sum_lower_of_claim_a`](Ttc/Analysis/Nonconv.lean#L58), [`sum_upper_of_claim_bc`](Ttc/Analysis/Nonconv.lean#L77) | (a),(b),(c) **proved** from the kernel; concentration **proved** — see finding 3; residual gap is the escape bound |
| `claim:helper` | `kⁿ ≤ (1+η/4)/(1−η/4)` | [`claim_helper`](Ttc/Analysis/Arith.lean#L162), [`claim_helper_of`](Ttc/Analysis/Arith.lean#L133), [`exp_two_mul_le_div`](Ttc/Analysis/Arith.lean#L78) | **proved** — see finding 4 |
| `lem:lattice` | transport `ℤⁿ ↔ 𝕃ⁿ = 10⁻ᵖ·ℤⁿ` | [`lattice_of_scaled`](Ttc/Analysis/Lattice.lean#L105), [`ncard_inter_lattice_smul`](Ttc/Analysis/Lattice.lean#L71), [`volume_smul_body`](Ttc/Analysis/Lattice.lean#L77) | **proved** |
| `lem:numlattice` | sketch output within `(1±ε/3)` w.p. `1−δ` | [`epoch_series_le`](Ttc/Analysis/Sketch.lean#L86), [`err_sum_le_delta`](Ttc/Analysis/Sketch.lean#L105), [`noise_bound_le_delta`](Ttc/Analysis/Sketch.lean#L125), [`numlattice_failure_bound`](Ttc/Analysis/Sketch.lean#L141), [`sketch_interval`](Ttc/Analysis/Sketch.lean#L154), [`sketch_window`](Ttc/Analysis/Sketch.lean#L169) | epoch skeleton **proved**; `lem:chernoff` assumed |
| `alg:ttc` line 18 (`ε' ← ε/12`) | | [`sketch_interval`](Ttc/Analysis/Sketch.lean#L154) | constant **verified** |
| `alg:ttc` line 20 (`Thresh`) | | [`err_sum_le_delta`](Ttc/Analysis/Sketch.lean#L105), [`noise_bound_le_delta`](Ttc/Analysis/Sketch.lean#L125) | both branches **verified** |
| `alg:ttc` line 17 (`η ← ε/8`) | | [`Params.eta`](Ttc/Model/Prelude.lean#L165) | definition |
| `κ` (`lem:nonconv`) | `√(2log(8/η)) + √(2log r)` | [`Params.kappa`](Ttc/Model/Prelude.lean#L177), [`kappa_le`](Ttc/Analysis/Parameters.lean#L62) | **proved** `κ ≤ 2√(log(8r/η))` |
| ↳ deflated shell factor | `(1 + κ/(γ−κ))ⁿ ≤ 1 + η/(8m)` | [`kappa_le_gamma_half`](Ttc/Analysis/Parameters.lean#L124), [`shell_factor_bound_deflated`](Ttc/Analysis/Parameters.lean#L144) | **proved** — the deflated companion of `shell_factor_bound` |
| ↳ dilation of a facet system | `c·{x \| f x ≤ b} = {y \| f y ≤ c·b}` | [`FacetSystem.scale`](Ttc/Analysis/Recentred.lean#L345), [`scale_body_zero`](Ttc/Analysis/Recentred.lean#L380) | **proved** — connects `body_eq_sol` to `lem:lattice`'s dilate |
| `γ` / `κ/γ ≤ η/(32mn)` | the shell bound's input | [`Params.gamma`](Ttc/Model/Prelude.lean#L183), [`kappa_div_gamma_le`](Ttc/Analysis/Parameters.lean#L81), [`shell_factor_bound`](Ttc/Analysis/Parameters.lean#L102) | **proved** — see finding 2 |
| `alg:ttc` lines 22–46 (main loop) | the sketch loop itself | [`run`](Ttc/Model/Pseudocode.lean#L101), [`step`](Ttc/Model/Pseudocode.lean#L91), [`absorb`](Ttc/Model/Pseudocode.lean#L82), [`halveDown`](Ttc/Model/Pseudocode.lean#L75) | modelled over an oracle bundle; structural invariants proved, termination and distribution not |
| ↳ the output as a random variable | `run` with oracles drawn at `ω` | [`ttcOutput`](Ttc/Model/Pseudocode.lean#L107) | definition |
| `thm:volumettc` | `Pr[ output ∈ (1±ε)·Vol(F) ] ≥ 1−δ` | [`TtcProb.volume_estimate`](Ttc/Model/Theorem.lean#L40) | **proved** from the [`TtcProb`](Ttc/Model/ProblemSetting.lean#L31) fields |
| `alg:prec` (`GetPrecision`) | `ρ ← ⌈log₁₀(γ/γ̂)⌉` ([`Params.precision`](Ttc/Model/Prelude.lean#L190), used via `TtcProb.rho_eq`) | [`ball_radius_scales`](Ttc/Analysis/Lattice.lean#L84), [`claim_helper`](Ttc/Analysis/Arith.lean#L162), [`gamma_half_le`](Ttc/Analysis/Repair.lean#L116), [`precision_increase_le_one`](Ttc/Analysis/Repair.lean#L154), [`gamma_scale_cost`](Ttc/Analysis/Recentred.lean#L576) | mathematical content **proved**; LP implementation not modelled |

Results with no counterpart in the paper, produced by the formalisation:

| Lean | What it establishes |
| --- | --- |
| [`convex_region`](Ttc/Analysis/Decomposition.lean#L76), [`convex_litSet`](Ttc/Analysis/Decomposition.lean#L53) | each cube's region is convex — and *not* closed (finding 5) |
| [`ratio_antitone`](Ttc/Analysis/Geometry.lean#L156), [`facet_ratio_fails`](Ttc/Analysis/Geometry.lean#L170) | `k` is attained at the facet **nearest** the origin, so the ball hypothesis is needed at every facet (finding 2) |
| [`claim12_factor_le`](Ttc/Analysis/Nonconv.lean#L155) | the `claim:helper` factor is `≤ 5/3` on `0 < η ≤ 1` |
| [`trivialProb`](Ttc/Analysis/Capstone.lean#L175), [`nonempty_ttcProb`](Ttc/Analysis/Capstone.lean#L220) | the hypothesis bundle is inhabited, so `thm:volumettc` is not vacuous |

`Ttc.lean` re-exports everything, so `import Ttc` and a bare `lake build` expose
the headline theorem.

## The headline theorem

```lean
theorem Ttc.TtcProb.volume_estimate (T : TtcProb A n) :
    1 - T.δ ≤
      (T.μ {ω | ttcOutput T.P T.O T.fuel T.D ω ∈ relErr T.ε (volSol T.M T.φ)}).toReal
```

`ttcOutput` is `Ttc.run` — the transcription of `alg:ttc` — with the oracles
drawn at `ω`, so the measured quantity is the algorithm's own output.
`volSol M φ = (volume (sol M φ)).toReal` is the **Lebesgue volume of the solution
set of the actual SMT(LRA) formula** — not a surrogate. That the set in question
is exactly the union of the polytopes the algorithm enumerates is
`Ttc.TtcProb.sol_eq_union` (`thm:decomposition`), so the object the algorithm
targets and the object the theorem bounds coincide.

**Non-vacuity.** `Ttc.TtcProb` is inhabited (`Ttc.nonempty_ttcProb`, witness
`Ttc.trivialProb`), so the theorem is not vacuously quantified — though that
witness is degenerate; see [`AUDIT.md`](AUDIT.md) §4.

## What is assumed

Everything in the tree is proved. Two ingredients of the paper enter as
*hypotheses* — fields of `Ttc.TtcProb` — rather than being derived. Both have
been reduced to a single residual item each; everything else about them is proved.

1. **`claim:cl`** — the three statements about the randomized rounding `rnd`.
   * *Proved*: its entire probabilistic content — the tail bound
     `Pr[κ‖A‖ ≤ A·Y] ≤ exp(−κ²/2)` for any independent mean-zero displacement in
     `[−1,1]ⁿ` (`Ttc.rounding_tail_bound`), its value `η/(4r)` at the paper's `κ`
     (`Ttc.rounding_tail_bound_kappa`), the union bound over the `r` facets
     (`Ttc.rounding_union_bound`), and the two summation steps by which
     `lem:nonconv` consumes it (`Ttc.sum_lower_of_claim_a`,
     `Ttc.sum_upper_of_claim_bc`).
     Also proved: **(a), (b) and (c) themselves**
     ([`Ttc.claim_cl_a`](Ttc/Analysis/Cl.lean#L126),
     [`_b`](Ttc/Analysis/Cl.lean#L147), [`_c`](Ttc/Analysis/Cl.lean#L114)),
     over [`Ttc.RoundingKernel`](Ttc/Analysis/Cl.lean#L65) — the density
     `k p x = Pr[rnd p = x]` carrying the properties the paper's proof uses, the
     substantive one being double stochasticity `∫ k p x dp = 1`. The paper
     defines `rnd` only by citation to KV97, so there is no construction to
     transcribe; the structure is inhabited
     ([`Ttc.nonempty_roundingKernel`](Ttc/Analysis/Cl.lean#L197)), so (a)–(c) are
     not vacuous.
   * *Residual assumption*: the **escape bound** — hypothesis `hesc` of
     `Ttc.claim_cl_a`, that `∫_{C(x)∖Q'} k p x dp ≤ η/4`. Its value is exactly
     what `Ttc.rounding_union_bound` gives; closing it means identifying the
     displacement law under `k(·,x)` with the independent mean-zero `[−1,1]`-valued
     `Y` of `Ttc.rounding_tail_bound`. That is one measure-theoretic step, not the
     whole reduction as before.

2. **`lem:numlattice`** — the Poisson/Chernoff analysis of the streaming sketch.
   * *Proved*: its engine `lem:process` (Poisson splitting,
     `Ttc.poisson_splitting`); the whole epoch union-bound skeleton — the
     doubly-exponential series `∑ 2e^{−a·2ᵗ} ≤ 4e^{−a}` (`Ttc.epoch_series_le`),
     the `Err` branch (`Ttc.err_sum_le_delta`), the `Noise` branch
     (`Ttc.noise_bound_le_delta`), their combination
     (`Ttc.numlattice_failure_bound`); and the interval arithmetic behind
     `ε' = ε/12` (`Ttc.sketch_interval`, `Ttc.sketch_window`,
     `Ttc.Params.epsPrime_window`).
   * *Residual assumption*: the Poisson–Chernoff estimate itself (`lem:chernoff`,
     cited to Soos et al.), which Mathlib does not carry. Mathlib has
     `poissonMeasure` and `charFun` but no moment generating function for it, so
     closing this means deriving `mgf = exp(λ(eᵗ−1))` from
     `hasSum_integral_poissonMeasure`, applying
     `ProbabilityTheory.measure_ge_le_exp_mul_mgf`, and then the
     Bennett→Bernstein step to reach `exp(−ζ²/(2λ+ζ))`. That is a self-contained
     but substantial development; it is the single largest remaining gap.

**These proofs confirm the algorithm's constants.** `ε' ← ε/12` (`alg:ttc` line
18) is exactly what makes the two-sided `(1±ε')` loss fit inside `(1±ε/3)`; each
branch of `Thresh` (line 20) is exactly what makes its failure branch `δ/6`
(total `δ/3`, so there is slack); and `γ` is exactly what makes
`κ/γ ≤ η/(32mn)` — with no slack at all, which is why `γ` and `κ` must use the
same logarithm argument (`Ttc.Params.kappa_div_gamma_le`,
`Ttc.Params.shell_factor_bound`).

## Scope, stated precisely

* **This is an accuracy guarantee, not an FPRAS claim.** `thm:runtime` (the `O(mn⁴)`
  runtime) and `thm:decompose` (the exponential decomposition cost) are **not**
  formalised. Nothing here says anything about running time.
* **The `δ` is derived from `lem:numlattice`, which is assumed.**
  `Ttc.TtcProb.volume_estimate` really does conclude
  `Pr[ output ∈ (1±ε)·Vol(F) ] ≥ 1 − δ`: its `numlattice` field gives
  `Pr[ output ∈ (1±ε/3)·L ] ≥ 1 − δ`, and the deterministic chain shows the
  first event *contains* the second, so measure monotonicity carries the bound.
  The `δ` is not invented — but it enters through an assumed field, so the
  guarantee is only as good as `lem:numlattice`, which this development does not
  prove.
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

This is why [`Ttc.facetSystem`](Ttc/Analysis/FacetOfDNF.lean#L66) is built only
for DNFs whose literals are all positive
([`Ttc.DNF.IsPositive`](Ttc/Analysis/FacetOfDNF.lean#L44)): a
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

**The main result stands.** Finding 1 changes constants, not the shape of the
theorem, and finding 2 is now closed by a different proof; finding 3 is a typo in
an exponent whose corrected form is stronger than needed; 4–9 are presentational.
