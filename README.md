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
#print axioms Ttc.TtcAnalysis.volume_estimate
-- 'Ttc.TtcAnalysis.volume_estimate' depends on axioms:
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
  grep -h "^theorem \|^noncomputable def \|^def " Ttc/*.lean \
  | sed 's/^[a-z ]*def /#print axioms Ttc./; s/^theorem /#print axioms Ttc./' \
  | cut -d" " -f1-3; } > /tmp/Ax.lean
lake env lean /tmp/Ax.lean | grep -v "Classical.choice"
```

(The one-liner above misses declarations inside `namespace FacetSystem` /
`namespace TtcAnalysis`; prefix those by hand, or just trust `lake build`, which
emits **zero** `declaration uses 'sorry'` warnings.)

As a cheap third check:

```bash
grep -rn "sorry\|admit\|native_decide\|sorryAx\|^axiom " Ttc.lean Ttc/*.lean
```

returns nothing.

## Module map

A small **audit surface** plus supporting lemmas. To check what is claimed you
only need the five surface modules; `Ttc/Internal/` holds the proofs they rest on.

```
Ttc.lean                      -- imports the five surface modules
Ttc/
  Prelude.lean                -- the ambient space ℝⁿ (ℓ₂ norm, Lebesgue measure)
  Problem.lean                -- SMT(LRA) syntax/semantics, Sol(F), thm:decomposition
  Parameters.lean             -- the scalars ε', Thresh, κ, γ, ρ + what each is chosen to satisfy
  Algorithm.lean              -- alg:ttc's main loop, line by line, over an oracle bundle
  Theorem.lean                -- the TtcAnalysis interface and thm:volumettc
  Internal/
    Arith.lean                -- claim:helper and every ε/η inequality
    Geometry.lean             -- facet systems; which facet attains k
    Recentred.lean            -- cl:recenter, the shell bound, lem:nonconv without a common ball
    Nonconv.lean              -- lem:nonconv skeleton + the summation steps consuming claim:cl
    Repair.lean               -- lem:nonconv at internal parameter θ = η/2
    Rounding.lean             -- claim:cl's concentration core (Hoeffding at the paper's κ)
    Lattice.lean              -- lem:lattice: transport ℤⁿ ↔ 𝕃ⁿ = 10⁻ᵖ·ℤⁿ
    Poisson.lean              -- lem:process: Poisson splitting
    Sketch.lean               -- lem:numlattice's epoch skeleton
```

**Reading order for an auditor.** `Algorithm.lean` is the code — read it against
`sections/algo.tex` and check the control flow matches. `Parameters.lean` says
where every constant comes from and what it buys. `Problem.lean` fixes what
`Vol(F)` means. `Theorem.lean` states what is proved and lists its hypotheses as
structure fields. Anything you still doubt is a named lemma in `Internal/`.

| Surface module | Contains | Status |
| --- | --- | --- |
| `Ttc/Prelude.lean` | `Ttc.Space n = EuclideanSpace ℝ (Fin n)` | definitions only |
| `Ttc/Problem.lean` | `BForm`/`Lit`/`Cube`/`DNF`, `sol`, `region`, convexity, **`thm:decomposition`** | proved |
| `Ttc/Parameters.lean` | `Ttc.Params`: `η`, `ε'`, `Thresh`, `κ`, `γ`, `ρ`, with `kappa_div_gamma_le`, `shell_factor_bound`, `epsPrime_window` | proved |
| `Ttc/Algorithm.lean` | `SketchState`, `Oracles`, `dropCovered`, `halveDown`, `absorb`, `step`, `run` + structural invariants | modelled; see caveats |
| `Ttc/Theorem.lean` | `Ttc.TtcAnalysis`, **`thm:volumettc`**, non-vacuity | proved from the interface |

### What `Ttc/Algorithm.lean` does and does not do

It is a line-by-line model of `alg:ttc` lines 22–46: the state `(X, p)`, the
order of operations, both `while` guards, the coverage filter, and the output
`|X|/p`. Read it beside the pseudocode.

Four external calls are **fields of `Ttc.Oracles`** rather than definitions —
`Vol_ED`, the Poisson draw, `GenerateSamples`, and the fair-coin thinning. So the
state evolution is deterministic *given the oracle's answers*, and all the
randomness sits at that boundary. That is deliberate: the distribution of the
output is `lem:numlattice`, which this development assumes.

Both `while` loops run on **explicit fuel**. Termination is *not* claimed and
would be false to claim: the second loop terminates because repeated thinning
brings `Nᵢ + |X|` under `Thresh` with high probability, and there is no
deterministic bound. What is proved is structural — `p` never increases and stays
nonnegative (`halveDown_p`, `absorb_p`), the filter only removes points
(`card_dropCovered_le`), a settled state is a fixpoint (`absorb_of_settled`).

**There is no theorem linking `Ttc.run` to `Ttc.TtcAnalysis.est`.** The capstone
takes `est` as a field satisfying `lem:numlattice`'s conclusion; proving that
`run` satisfies it is exactly `lem:numlattice`, which is assumed. Closing that
link is the main remaining work.

## Paper ↔ Lean map

Keyed by `\label`, not by number — numbers shift whenever a `\begin{lemma}` is
added or uncommented. (At the time of writing the counter runs
`thm:decomposition` = Lemma 1, `lem:chernoff` = 2, `lem:process` = 3,
`lem:integerlattice` = 4, `lem:nonconv` = 5, `claim:cl` = 6, `lem:lattice` = 7,
`lem:numlattice` = 8; `claim:helper` = Claim 1. Note `claim:cl` uses a `lemma`
environment, so it renders as a *Lemma*, not a Claim.)

| `\label` | Statement | Lean | Status |
| --- | --- | --- | --- |
| `thm:volumettc` | `est ∈ [(1−ε)vol F, (1+ε)vol F]` w.p. `1−δ` | [`TtcAnalysis.volume_estimate`](Ttc/Theorem.lean#L151) | proved from the interface |
| `thm:decompose` | decomposition takes exponential time | — | out of scope (runtime) |
| `thm:runtime` | `O(mn⁴)` runtime | — | out of scope (runtime) |
| `thm:decomposition` | `⋃ᵢ P(cᵢ) = Sol(F)` | [`sol_eq_iUnion_region`](Ttc/Problem.lean#L57), [`region_subset_sol`](Ttc/Problem.lean#L42), [`sol_subset_iUnion_region`](Ttc/Problem.lean#L49), [`sol_eq_iUnion_convex`](Ttc/Problem.lean#L66) | **proved** |
| `lem:chernoff` | Poisson tail bound (Soos et al.) | — | **assumed** (external) |
| `lem:process` | three sampling procedures are equivalent | [`poisson_splitting`](Ttc/Internal/Poisson.lean#L60), [`poisson_splitting_paper`](Ttc/Internal/Poisson.lean#L107), [`rate_mem_interval`](Ttc/Internal/Poisson.lean#L123) | **proved** |
| `lem:integerlattice` | KV97 Thm 3, single polytope | — | external; superseded by `lem:nonconv` |
| `lem:nonconv` | `vol Q ∈ [(1−η)\|Q∩ℤⁿ\|, (1+η)\|Q∩ℤⁿ\|]` | skeleton [`nonconv_lower`](Ttc/Internal/Nonconv.lean#L101), [`nonconv_upper_deflated`](Ttc/Internal/Nonconv.lean#L124), [`nonconv_upper_repaired`](Ttc/Internal/Nonconv.lean#L140); geometry [`FacetSystem.inflated_subset_smul_deflated`](Ttc/Internal/Geometry.lean#L104), [`volume_inflated_le`](Ttc/Internal/Geometry.lean#L125) | proved from `claim:cl` — **see findings 1 & 2** |
| ↳ repaired | same statement, internal `θ = η/2` | [`nonconv_repaired`](Ttc/Internal/Repair.lean#L75), [`repair_upper_arith`](Ttc/Internal/Repair.lean#L52), [`repair_lower_arith`](Ttc/Internal/Repair.lean#L58) | **proved** |
| ↳ without common ball | per-polytope homothety + shell bound | [`piece_inflated_subset_homothety`](Ttc/Internal/Recentred.lean#L69), [`volume_piece_inflated_le`](Ttc/Internal/Recentred.lean#L100), [`body_subset_union_shells`](Ttc/Internal/Recentred.lean#L127), [`shell_bound`](Ttc/Internal/Recentred.lean#L162) | **proved** |
| `claim:cl` | rounding hits/misses `Q` w.p. `1 ± η/2` | core [`rounding_tail_bound`](Ttc/Internal/Rounding.lean#L107), [`rounding_tail_bound_kappa`](Ttc/Internal/Rounding.lean#L132), [`rounding_union_bound`](Ttc/Internal/Rounding.lean#L165); consumed via [`sum_lower_of_claim_a`](Ttc/Internal/Nonconv.lean#L58), [`sum_upper_of_claim_bc`](Ttc/Internal/Nonconv.lean#L77) | concentration **proved** — see finding 3; measure-theoretic reduction **assumed** |
| `claim:helper` | `kⁿ ≤ (1+η/4)/(1−η/4)` | [`claim_helper`](Ttc/Internal/Arith.lean#L162), [`claim_helper_of`](Ttc/Internal/Arith.lean#L133), [`exp_two_mul_le_div`](Ttc/Internal/Arith.lean#L78) | **proved** — see finding 4 |
| `lem:lattice` | transport `ℤⁿ ↔ 𝕃ⁿ = 10⁻ᵖ·ℤⁿ` | [`lattice_of_scaled`](Ttc/Internal/Lattice.lean#L105), [`ncard_inter_lattice_smul`](Ttc/Internal/Lattice.lean#L71), [`volume_smul_body`](Ttc/Internal/Lattice.lean#L77) | **proved** |
| `lem:numlattice` | sketch output within `(1±ε/3)` w.p. `1−δ` | [`epoch_series_le`](Ttc/Internal/Sketch.lean#L86), [`err_sum_le_delta`](Ttc/Internal/Sketch.lean#L105), [`noise_bound_le_delta`](Ttc/Internal/Sketch.lean#L125), [`numlattice_failure_bound`](Ttc/Internal/Sketch.lean#L141), [`sketch_interval`](Ttc/Internal/Sketch.lean#L154), [`sketch_window`](Ttc/Internal/Sketch.lean#L169) | epoch skeleton **proved**; `lem:chernoff` assumed |
| `alg:ttc` line 18 (`ε' ← ε/12`) | | [`sketch_interval`](Ttc/Internal/Sketch.lean#L154) | constant **verified** |
| `alg:ttc` line 20 (`Thresh`) | | [`err_sum_le_delta`](Ttc/Internal/Sketch.lean#L105), [`noise_bound_le_delta`](Ttc/Internal/Sketch.lean#L125) | both branches **verified** |
| `alg:ttc` line 17 (`η ← ε/8`) | | [`Params.eta`](Ttc/Parameters.lean#L73) | definition |
| `κ` (`lem:nonconv`) | `√(2log(8/η)) + √(2log r)` | [`Params.kappa`](Ttc/Parameters.lean#L87), [`kappa_le`](Ttc/Parameters.lean#L128) | **proved** `κ ≤ 2√(log(8r/η))` |
| `γ` / `κ/γ ≤ η/(32mn)` | the shell bound's input | [`Params.gamma`](Ttc/Parameters.lean#L95), [`kappa_div_gamma_le`](Ttc/Parameters.lean#L147), [`shell_factor_bound`](Ttc/Parameters.lean#L169) | **proved** — see finding 2 |
| `alg:ttc` lines 22–46 (main loop) | the sketch loop itself | [`run`](Ttc/Algorithm.lean#L127), [`step`](Ttc/Algorithm.lean#L118), [`absorb`](Ttc/Algorithm.lean#L110), [`halveDown`](Ttc/Algorithm.lean#L104) | modelled over an oracle bundle; structural invariants proved, termination and distribution not |
| `alg:prec` (`GetPrecision`) | `ρ ← ⌈log₁₀(γ/γ̂)⌉` | [`ball_radius_scales`](Ttc/Internal/Lattice.lean#L84), [`claim_helper`](Ttc/Internal/Arith.lean#L162), [`gamma_half_le`](Ttc/Internal/Repair.lean#L116), [`precision_increase_le_one`](Ttc/Internal/Repair.lean#L154), [`gamma_scale_cost`](Ttc/Internal/Recentred.lean#L199) | mathematical content **proved**; LP implementation not modelled |

Results with no counterpart in the paper, produced by the formalisation:

| Lean | What it establishes |
| --- | --- |
| [`convex_region`](Ttc/Problem.lean#L190), [`convex_litSet`](Ttc/Problem.lean#L167) | each cube's region is convex — and *not* closed (finding 5) |
| [`ratio_antitone`](Ttc/Internal/Geometry.lean#L156), [`facet_ratio_fails`](Ttc/Internal/Geometry.lean#L170) | `k` is attained at the facet **nearest** the origin, so the ball hypothesis is needed at every facet (finding 2) |
| [`claim12_factor_le`](Ttc/Internal/Nonconv.lean#L155) | the `claim:helper` factor is `≤ 5/3` on `0 < η ≤ 1` |
| [`TtcAnalysis.ideal`](Ttc/Theorem.lean#L168), [`nonempty_ttcAnalysis`](Ttc/Theorem.lean#L188) | the interface is inhabited, so `thm:volumettc` is not vacuous |

`Ttc.lean` re-exports everything, so `import Ttc` and a bare `lake build` expose
the headline theorem.

## The headline theorem

```lean
theorem Ttc.TtcAnalysis.volume_estimate (T : TtcAnalysis A n) :
    T.est ∈ Set.Icc ((1 - T.ε) * volSol T.M T.φ) ((1 + T.ε) * volSol T.M T.φ)
```

where `volSol M φ = (volume (sol M φ)).toReal` is the **Lebesgue volume of the
solution set of the actual SMT(LRA) formula** — not of a surrogate. That the set
in question is exactly the union of the polytopes the algorithm enumerates is
`Ttc.TtcAnalysis.sol_eq_union` (`thm:decomposition`), so the object the algorithm targets and
the object the theorem bounds coincide.

**Non-vacuity.** `Ttc.TtcAnalysis` is inhabited (`Ttc.nonempty_ttcAnalysis`), and
more usefully `Ttc.TtcAnalysis.ideal` builds an instance for *any* formula, *any*
DNF representation of it, and *any* `ε ∈ (0,1]` — so the theorem is not vacuously
quantified.

## What is assumed

Everything in the tree is proved. Two ingredients of the paper enter as
*hypotheses* — fields of `Ttc.TtcAnalysis` — rather than being derived. Both have
been reduced to a single residual item each; everything else about them is proved.

1. **`claim:cl`** — the three statements about the randomized rounding `rnd`.
   * *Proved*: its entire probabilistic content — the tail bound
     `Pr[κ‖A‖ ≤ A·Y] ≤ exp(−κ²/2)` for any independent mean-zero displacement in
     `[−1,1]ⁿ` (`Ttc.rounding_tail_bound`), its value `η/(4r)` at the paper's `κ`
     (`Ttc.rounding_tail_bound_kappa`), the union bound over the `r` facets
     (`Ttc.rounding_union_bound`), and the two summation steps by which
     `lem:nonconv` consumes it (`Ttc.sum_lower_of_claim_a`,
     `Ttc.sum_upper_of_claim_bc`).
   * *Residual assumption*: the measure-theoretic reduction of (a)/(b)/(c) to that
     tail bound — the identities `Pr[rnd p = x] = (1/vol Q')∫_{Q'} Pr(x+Y=p)dp`
     and `∫_{C(x)} Pr(x+Y=p)dp = 1`. These need a formal model of `rnd` as a
     kernel and carry no content the paper's argument depends on.

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
* **The `δ` is carried, not re-derived.** `Ttc.TtcAnalysis` fixes one run and
  asserts `lem:numlattice`'s conclusion deterministically. What is proved is: *on the
  event that `lem:numlattice`'s guarantee holds, the output is a relative
  `ε`-approximation of the true volume.* Combining that event with
  `Pr ≥ 1 − δ` is exactly `lem:numlattice`'s content, which is assumed.
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

**The fix** (proved, `Ttc/Repair.lean`): run the construction with internal
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

**Resolution** (proved, `Ttc/Recentred.lean`) — the assumption is *removed*, not
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
`Ax ≤ b` sense that `lem:integerlattice` (KV97, Theorem 3) is stated for. Volumes
agree (the boundary is null), so nothing breaks — but the appeal to KV97 is to a
statement about closed polytopes.

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
