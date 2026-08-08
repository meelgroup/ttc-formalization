# How to audit the Kannan–Vempala formalisation

Companion to [`AUDIT.md`](AUDIT.md), for a *different* paper.

> **Ravi Kannan and Santosh Vempala, "Sampling Lattice Points."**
> STOC '97, pp. 696–700. DOI `10.1145/258533.258665`.
> Local copy: [`../258533.258665.pdf`](../258533.258665.pdf).

`TTC` calls `GenerateSamples(P(cᵢ), Nᵢ, ρ, ε', δ')` at `alg:ttc` line 43 and
assumes only that it meets `eq:almostuniform` (`sections/related.tex:21`):

```
∀ x ∈ K ∩ 𝕃ⁿ,   (1−ε)/|K ∩ 𝕃ⁿ|  ≤  Pr[x]  ≤  (1+ε)/|K ∩ 𝕃ⁿ|
```

**This development exists to turn that assumption into a theorem**, by the route
the paper itself sketches at
[`sections/proof-appendix.tex:149–185`](../sections/proof-appendix.tex):
KV97 Theorem 2 → `cor:linf` → `eq:almostuniform`.

**As of this writing that route is wired up and load-bearing.** What is left is
one oracle, named in §2.

No line numbers appear on this page; use go-to-definition or `grep -n` on the
declaration names, all of which were checked to exist in the compiled
environment.

---

## 0. Status — read this first

**`eq:almostuniform` is no longer assumed by `Ttc.TtcProb`.** It is
[`Ttc.TtcProb.samp_unif`](Ttc/Sampler/Bridge.lean), a theorem, and so are
[`Ttc.TtcProb.theta_lo`](Ttc/Sampler/Bridge.lean) and `theta_hi`. All three used
to be fields; `AUDIT.md` §2 has the current 59-field list, and none of them is on
it.

> **This reverses what this page said before.** It used to open
> "`theta_lo` and `theta_hi` are still fields of `Ttc.TtcProb`, and nothing under
> `Arlib/` is on the headline's dependency path." **Both halves are now false.**
> Running `AUDIT.md` §5's transitive walk from `Ttc.TtcProb.volume_estimate`
> reaches ~137 `Arlib.*` declarations, 29 of them under `Arlib.KV97`, including
> `Arlib.KV97.theorem2`. Re-run the walk; do not trust this paragraph over it.

**But the oracle is NOT discharged, and this page must not be read as saying it
is.** The assumption moved down one level rather than disappearing. What
`Ttc.TtcProb` now carries is the field `sampler : Ttc.KV97Sampler …`, whose one
quantitative field is

```lean
law_tv : ∀ i, Arlib.TVLe (contLaw i)
  (Arlib.uniformOn volume (Arlib.KV97.inflated (Amat i) (bvec i) (cOf ε') facetBound))
  (ENNReal.ofReal (ε' / (4 * contVol i)))
```

— **a continuous almost-uniform sampler on the inflated dilated polytope, at
tolerance `ε'/(4·Vol(P'))`. Nothing in this development constructs one.** That is
the whole of the residual debt on this axis, and §2 is about it.

So the honest one-line summary is: *KV97's mathematics is done and is being used;
the continuous sampler it converts is still assumed.*

| KV97 result | Status | Where |
| --- | --- | --- |
| **Theorem 2, unconditional** — `(1−ε)(1−e^{−c²/2})/V ≤ Pr[rnd p = x] ≤ (1+ε)/V` | **PROVED**, no escape hypothesis | [`Arlib.KV97.theorem2_of_body`](Arlib/Lattice/KV97/Theorem2.lean) |
| Theorem 2, parametric in the escape mass `E` | **PROVED** (the reusable half; §4c) — and this is the form the headline actually reaches | [`Arlib.KV97.theorem2`](Arlib/Lattice/KV97/Theorem2.lean) |
| the escape tail `Pr[x + Y ∉ P'] ≤ r·e^{−κ²/2}` | **PROVED** for any independent, `[−1,1]`-supported, mean-zero displacement | [`Arlib.KV97.escape_prob_le`](Arlib/Lattice/KV97/Escape.lean) |
| the same at the *continuous* tent density, and `∫_{P'ᶜ} prodTent ≤ e^{−c²/2}` | **PROVED** — this is what made Theorem 2 unconditional | [`Arlib.Lattice.Rounding.setIntegral_prodTent_compl_inflate_le_exp`](Arlib/Lattice/Rounding/ContTent.lean) |
| **Lemma 1** — acceptance probability bounded below | **PROVED**, at `9/(20e) ≈ 0.1655`, which **beats** the paper's `1/8 = 0.125` (§4h) | [`Arlib.KV97.acceptance_ge_const`](Arlib/Lattice/KV97/Lemma1.lean) |
| Theorem 1 — the sampling algorithm | **PROVED, in substance.** Theorem 1 is the packaging claim "there is a polynomial-time nearly-uniform sampler for `P ∩ ℤⁿ`"; its *correctness* content is exactly `cor:linf` (the output law) plus Lemma 1 (the loop terminates, in `O(1)` expected draws). Both are proved. Its *running-time* content is not formalised and is out of scope, exactly as `thm:runtime` is for the main development | [`Arlib.KV97.cor_linf_tuned`](Arlib/Lattice/KV97/Corollary.lean) + [`acceptance_ge_const`](Arlib/Lattice/KV97/Lemma1.lean) |
| **`cor:linf` — `eq:almostuniform`** | **PROVED**, and the printed statement is **false for `ε > (7−√33)/2 ≈ 0.628`** (§4g). `TTC` uses `ε' = ε/12 ≤ 1/12`, so its own use is safe | [`Arlib.KV97.cor_linf_tuned`](Arlib/Lattice/KV97/Corollary.lean) |
| Theorem 3 — `Vol(P) ≍ \|P ∩ ℤⁿ\|` | **proved**, as `lem:lattice` | [`Ttc.TtcProb.lattice_lo`](Ttc/Lattice/Assembled.lean), [`lattice_hi`](Ttc/Lattice/Assembled.lean) |
| §3 (contingency tables, integral flows, b-matchings), Theorem 4 (NP-hardness) | **out of scope** — they discharge no oracle here | — |

**Which of these the headline actually uses.** The walk reports
`Arlib.KV97.theorem2` **`true`** and `Arlib.KV97.theorem2_of_body`,
`cor_linf_tuned`, `acceptance_ge_const` all **`false`**. That is not a defect:
the `Ttc` side re-derives the escape mass at `E = 0` and routes through the
parametric `theorem2` and its own
[`Ttc.almostUniform_of_kv97_law`](Ttc/Sampler/Bridge.lean) /
`almostUniform_of_kv97_window` / `uniformOn_prodTent_window` /
`prodTent_window_of_tvLe` backbone. Lemma 1 is about the rejection loop's
*termination*, which `Ttc` does not need because `sampD_eq` defines the sampler as
the already-normalised conditional law. Both facts are worth knowing before
citing a KV97 theorem as load-bearing.

### What the foundation supplies today

All of it is in [`Arlib/`](Arlib/), the staging area for material with no
kr-25-ssm content (see [`Arlib.lean`](Arlib.lean) for why it is staged in this
repo rather than in the shared `arlib`). Every item below is `sorry`-free with
axioms `[propext, Classical.choice, Quot.sound]`.

| Piece of Theorem 2's proof | Lean | Module |
| --- | --- | --- |
| the rounding `xₖ = ⌊pₖ⌋ + Bernoulli(pₖ−⌊pₖ⌋)`, whose displacement density is the tent `1−\|u\|` | `tent`, `integral_tent`, `integral_id_mul_tent` | [`Arlib/Lattice/Rounding/Tent.lean`](Arlib/Lattice/Rounding/Tent.lean) |
| `Pr[rnd p = x ∣ p] = ∏ᵢ tent(pᵢ−xᵢ)`, and **double stochasticity** `∫_{ℝⁿ} ∏ tent = 1` — this is the **upper** bound of Theorem 2 | `prodTent`, `integral_prodTent` | [`Arlib/Lattice/Rounding/ProdKernel.lean`](Arlib/Lattice/Rounding/ProdKernel.lean) |
| the law of `rnd p` on `ℤⁿ`: two-point, bounded, mean-zero, independent across coordinates | `roundLaw`, `tentInt_eq_two_point`, `integral_latDisp_eq_zero`, `iIndepFun_latDisp` | [`Arlib/Lattice/Rounding/RoundLaw.lean`](Arlib/Lattice/Rounding/RoundLaw.lean) |
| the Azuma step: `Pr[⟨A,Y⟩ ≥ κ‖A‖] ≤ exp(−κ²/2)`, and the union bound over facets — this is the **lower** bound of Theorem 2 | `rounding_tail_bound`, `rounding_tail_bound_kappa`, `rounding_union_bound` | [`Arlib/Probability/SubgaussianTail.lean`](Arlib/Probability/SubgaussianTail.lean) |
| total variation, and the *additive* transfer `\|∫f dμ − ∫f dν\| ≤ ε` for `0 ≤ f ≤ 1` — **and §4b is why this is the right hypothesis, not a weaker one** | `TVLe`, `TVLe.integral_le` | [`Arlib/Probability/TV.lean`](Arlib/Probability/TV.lean) |
| the TV → Theorem 2 route at tolerance `θ/V` | `window_of_tvLe`, `ratio_bounds_of_tvLe`, `theorem2_of_tvLe_inv_volume` | [`Arlib/MarkovChains/Continuous/PointwiseRoute.lean`](Arlib/MarkovChains/Continuous/PointwiseRoute.lean) |
| `cor:linf`'s arithmetic: `(1−θ)/V ≤ wᵢ ≤ 1/V` ⟹ `(1−θ)/N ≤ wᵢ/∑w ≤ (1+2θ)/N` | `Arlib.Rejection.ratio_mem_relErr`, `ratio_mem_relErr_of_eps` | [`Arlib/Probability/Rejection.lean`](Arlib/Probability/Rejection.lean) |
| the inflated polytope `P' = {x : Ax ≤ b + κ‖A‖}` and `Vol(P') ≤ (1+κ/γ)ⁿ·Vol(P)` — Lemma 1's engine | `Polytope.inflate`, `volume_inflate_le` | [`Arlib/Convexity/Polytope.lean`](Arlib/Convexity/Polytope.lean) |
| the transport `ℤⁿ → 𝕃ⁿ = 10^(−ρ)·ℤⁿ` (the paper's "isomorphism `φ`") | `ncard_inter_fineLattice` | [`Arlib/Lattice/Basic.lean`](Arlib/Lattice/Basic.lean) |

---

## 1. Is the capstone about the real object?

**There is no single `Arlib.Lattice.KV97.corollary` capstone, and there will not
be one** — the wiring landed as a bridge on the `Ttc` side instead. The
declaration to read is
[`Ttc.TtcProb.samp_unif`](Ttc/Sampler/Bridge.lean), and its *type* is:

```lean
theorem Ttc.TtcProb.samp_unif {A : Type u_1} {n : ℕ} (T : Ttc.TtcProb A n) :
    ∀ i ∈ T.toDNF T.φ,
      ∀ x ∈ Ttc.region T.M i ∩ Ttc.fineLattice n (Ttc.latticeScale T.ρ),
        (1 - T.P.epsPrime) / (Ttc.region T.M i ∩ Ttc.fineLattice n (Ttc.latticeScale T.ρ)).ncard
            ≤ T.sampD i x
          ∧ T.sampD i x
            ≤ (1 + T.P.epsPrime) / (Ttc.region T.M i ∩ Ttc.fineLattice n (Ttc.latticeScale T.ρ)).ncard
```

Check these four things on it — they are the four this page has always asked for,
and all four now hold:

* the conclusion is `eq:almostuniform` — a **two-sided** pointwise bound
  `(1−ε')/N ≤ Pr ≤ (1+ε')/N`, not a TV bound and not a one-sided bound. A
  one-sided `Pr ≤ (1+ε')/N` would be useless downstream: `AUDIT.md` §2 explains
  that it leaves `theta_lo` unprovable and with it the lower half of the headline;
* `N` is `(region M i ∩ fineLattice n (latticeScale ρ)).ncard` — the count of the
  **real** lattice points of the real cube, not a parameter;
* the measure is `T.sampD`, and `sampD` is pinned by the `sampD_eq` field of
  `Ttc.KV97Sampler` to the *rejection-normalised rounding law* — `∫ prodTent` at
  the dilated point, divided by the same sum over all lattice points of the
  dilated cube. That is "`roundLaw` conditioned on landing in `P`", not the law of
  `rnd p` unconditioned;
* **the hypothesis on the continuous draw is a total-variation bound at tolerance
  `ε'/(4·Vol(P'))`** — the `law_tv` field. §4b is the long story of why that, and
  not a pointwise bound, is the right hypothesis. If a future version of this
  theorem appears with a *pointwise density* hypothesis, that is a regression, not
  a strengthening: §4b shows the pointwise hypothesis is unattainable for any real
  ball-walk sampler.

---

## 2. What is assumed?

Exactly one thing, and it is the same thing Cousins–Vempala Theorem 1.1 needs,
which is why one stack would discharge both oracles:

> **A continuous almost-uniform sampler.** KV97 Theorem 2 does not sample; it
> *converts* a continuous draw into a lattice draw. Its hypothesis, as this
> development states it, is the `law_tv` field of `Ttc.KV97Sampler`: the
> continuous law is within total variation `ε'/(4·Vol(P'))` of uniform on the
> inflated dilated polytope. **Nothing in Mathlib or in this repo constructs such
> a law.**

Note the `1/Vol(P')` scaling of the tolerance. **Neither paper states it**, and
§4b is where it comes from. It is affordable — mixing time is *logarithmic* in the
TV tolerance, so `Arlib.PointwiseRoute.conductanceMixingTime_inv_volume_le` bounds
the step count by `(log M + 2 log V + 2 log(1/θ))/φ² + 1`, linear in `log V` — but
it is a real requirement and it is invisible in both papers.

### Phase 4 progress: the stack that would build the sampler

[`END-TO-END-PLAN.md`](END-TO-END-PLAN.md) Phase 4 builds this for the **ball
walk**. Everything below is `sorry`-free. **None of it is on the headline's
dependency path**, and none of it closes the oracle above.

**Convexity.** This section used to say `PrekopaLeindler.lean` was "partial, and
honestly so … the layer-cake integration and the AM–GM finish are not declared at
all, and therefore no 1-D Prékopa–Leindler yet", and that Mathlib and this repo
lack Brunn–Minkowski in any form. **That is now badly stale — all of it landed:**

* [`Arlib/Convexity/PrekopaLeindler.lean`](Arlib/Convexity/PrekopaLeindler.lean) —
  **1-D Prékopa–Leindler is proved** (`Arlib.prekopa_leindler_one_dim`, with
  `prekopa_leindler_one_dim_lintegral`, `_of_lub`, `_of_bddAbove`,
  `_of_same_levels`), on top of `Arlib.volume_add_volume_le_volume_add` (1-D
  Brunn–Minkowski).
* [`Arlib/Convexity/PrekopaLeindlerN.lean`](Arlib/Convexity/PrekopaLeindlerN.lean)
  — **`ℝⁿ` Prékopa–Leindler is proved** (`Arlib.prekopa_leindler_pi`,
  `prekopa_leindler_lintegral_pi`), and with it multiplicative Brunn–Minkowski
  (`Arlib.brunn_minkowski_pi`).
* [`Arlib/Convexity/BrunnSharp.lean`](Arlib/Convexity/BrunnSharp.lean) — **sharp
  (`1/n`-concave) Brunn–Minkowski is proved** (`Arlib.brunn_minkowski_sharp`,
  `_toReal`, `_finrank`, `_inv`), and Brunn's theorem in sharp form
  (`Arlib.brunn_slice_sharp`, `Arlib.brunn_slice_concaveOn`). Mathlib v4.32 still
  has no Brunn–Minkowski in any form.
* [`Arlib/Convexity/Localization.lean`](Arlib/Convexity/Localization.lean) — the
  **marginal theorem** (`Arlib.isLogConcave_marginal_pi`, `_real`,
  `isLogConcave_snoc_marginal`) and `Arlib.isLogConcave_convolution`.
* [`Arlib/Convexity/LocalizationLemma.lean`](Arlib/Convexity/LocalizationLemma.lean)
  and
  [`LocalizationLimit.lean`](Arlib/Convexity/LocalizationLimit.lean) — **the
  Localization Lemma is NOT proved for `n ≥ 2`, and deliberately not assumed
  either.** Both files are explicit that they declare no `def`/`structure`/`Prop`
  asserting it. `LocalizationLimit` closes the Blaschke-selection ingredient
  (`Arlib.exists_subseq_tendsto_hausdorffDist_convex`,
  `Arlib.convex_of_tendsto_hausdorffDist`) and settles the shape of the remaining
  convergence step **negatively**. Read those two docstrings before assuming this
  line of attack is close.
* [`Arlib/Convexity/LogConcave.lean`](Arlib/Convexity/LogConcave.lean) — the
  log-concavity API.
* [`Arlib/Convexity/DyerFrieze.lean`](Arlib/Convexity/DyerFrieze.lean) — **towards**
  the Dyer–Frieze / Lovász–Simonovits isoperimetric inequality. Its docstring is
  explicit: *nothing in the file assumes it*; the bisection step's hypothesis is
  written inline. **This is the open end of the entire stack.**
* [`Arlib/Convexity/GaussianCooling/`](Arlib/Convexity/GaussianCooling/) —
  `Estimator`, `Variance` (Cousins–Vempala §5.1; the Localization Lemma is carried
  as the explicit hypothesis `Arlib.GaussianCooling.LocalizationHypothesis`, not
  assumed silently), and `ZLogconcave`, which **discharges**
  `Arlib.GaussianCooling.ZLogconcaveHypothesis` for indicators of convex
  measurable sets (`zLogconcaveHypothesis_indicator`, `_indicator_const`,
  `_closedBall`) using the new Prékopa–Leindler.

**Markov chains**, in [`Arlib/MarkovChains/Continuous/`](Arlib/MarkovChains/Continuous/):

* `Conductance.lean` — `flow`, `IsReversible`, `conductanceOn`, `conductance`,
  with a **non-vacuity witness** `Arlib.MarkovChains.conductance_const_piHalf`:
  the instantly-mixing kernel on a two-point space has conductance exactly `1/2`,
  so "conductance ≥ φ" is not vacuously unsatisfiable.
* `Cheeger.lean` — the `L²` layer: real Dirichlet form, variance, and
  `Arlib.MarkovChains.spectralGap`, with Cheeger's inequality in both directions
  (`sq_conductance_div_two_le_spectralGap_const_piHalf`,
  `spectralGap_le_two_mul_conductanceOn`).
* `L2Mixing.lean` — spectral gap → TV decay
  (`Arlib.MarkovChains.varianceReal_markovIter_le`), assembled into
  `mixesWithin_of_conductance`, which discharges the `hdecay` hypothesis that
  `mixesWithin_of_conductance_decay` leaves to its caller.
* `Warmness.lean`, `MixingFromConductance.lean`, `BallWalk.lean` — the supporting
  layers. (This page used to say `MixingFromConductance` was "a Phase 4 target,
  deliberately not imported as a hypothesis". It is now a landed module.)
* `BallWalkConductance.lean` —
  `Arlib.MarkovChains.mixesWithin_lazy_ballWalk_unitBall` instantiates the whole
  chain for the lazy ball walk on the unit ball, **except the isoperimetric
  inequality**, which remains a visible `∀`-binder (`hiso`). That binder is the
  oracle; see `DyerFrieze.lean`.
* `PointwiseMixing.lean`, `PointwiseRoute.lean` — §4b's subject matter.

  > ⚠ `PointwiseMixing.lean`'s **module docstring still states the conclusion that
  > §4b retracts** ("Under the additive reading the corollary is false … So
  > `Arlib.KV97.theorem2` takes a **pointwise** hypothesis"). The theorems in the
  > file are fine; the prose above them is stale. Read `PointwiseRoute.lean` and
  > §4b instead, and treat that docstring as a known defect.

---

## 3. Is it non-vacuous?

Three witnesses exist. **Each is weaker than its name suggests, and the gaps
matter more than the existence.**

* `Arlib.MarkovChains.conductance_const_piHalf` — the two-point instantly-mixing
  kernel has conductance `1/2`. Honest, and genuinely rules out a vacuous
  "conductance ≥ φ".
* [`Arlib.PointwiseRoute.exists_theorem2_of_tvLe_witness`](Arlib/MarkovChains/Continuous/PointwiseRoute.lean)
  — the Theorem 2 hypothesis bundle (a set `S`, a law `μ`, a volume `V`, an escape
  mass `E`, the `TVLe`, and both halves of the window) is satisfiable. **But only
  in the degenerate `ε = 0` corner**: the `μ` it produces *is* the uniform measure
  on `S`, and the `TVLe` is discharged by `Arlib.TVLe.refl`. It meets CLAUDE.md
  §11 and it is a real check — but it exhibits no *approximately* uniform sampler,
  only an exactly uniform one, so it says nothing about whether a tolerance
  `θ/V > 0` is achievable.
* [`Arlib.KV97.exp_neg_one_le_acceptance_cube`](Arlib/Lattice/KV97/Lemma1.lean) —
  Lemma 1's witness. It takes `pt` **constant** (`fun _ => 0`). Under the
  injectivity requirement that §4h *proves*, `acceptance` at a constant `pt` is
  not a probability, so this certifies only that the **bounds'** hypothesis bundle
  is inhabited. See §4h.

`Ttc.KV97Sampler` itself — the structure that now carries the oracle — is
inhabited: [`Ttc.Box.boxProb`](Ttc/Witness/BoxProb.lean) builds one, so
`AUDIT.md` §3a's box witness covers it. As with everything else about that
witness, it is the *ideal* corner.

Note the trap specific to this development: a rejection-sampling statement is
vacuous whenever the acceptance probability is zero, i.e. whenever
`P ∩ 𝕃ⁿ = ∅`. Lemma 1 is what rules that out, so `cor:linf` carries
`P ∩ 𝕃ⁿ ≠ ∅` (or Lemma 1's hypothesis) rather than quietly dividing by zero —
Mathlib's `x / 0 = 0` would otherwise make the lower bound `0 ≤ 0` and true for
the wrong reason.

---

## 4. Where the paper and the provable statement differ

The formalisation is being used as a referee (`CLAUDE.md` §5).

### 4a. Theorem 2's exponent is printed two different ways

KV97's own Theorem 2 reads, in the scan, `1 − 2e^{−c}` over `Vol(P̄)`. The proof
directly below it applies **Azuma's inequality** to the martingale
`Zⱼ = ∑_{k≤j} A_{ik}Yₖ` with `|Zⱼ − Z_{j−1}| ≤ |A_{ij}|`, which yields
`exp(−c²/2)`, not `exp(−c)`. The `c` in the printed statement is missing a square.

The kr-25-ssm paper's restatement (`sections/proof-appendix.tex:155`,
`claim:linf`) writes `1 − 2e^{−c²} − ε` — i.e. it **silently corrects** the
exponent, and folds the facet count into the displacement `κ = c + √(2 log r)`
rather than carrying a factor `r` out front. This is the same class of defect as
README finding 3 (a missing square in `claim:cl`'s Azuma exponent) — almost
certainly the same erratum, inherited.

**Settled by proof, and the paper's pairing is wrong.**
`Arlib.Probability.rounding_tail_bound_kappa` gives `exp(−κ²/2)` per facet.
Feeding it the paper's own inflation `κ = c + √(2·log r)` and union-bounding over
`r` facets, [`Arlib.KV97.mul_exp_kappaOf_le`](Arlib/Lattice/KV97/Escape.lean)
proves

```
r · exp(−κ²/2) ≤ exp(−c²/2),     κ = c + √(2 log r)
```

using `(a+b)² ≥ a² + b²`. So **the escape probability at the paper's inflation is
`exp(−c²/2)`, not `exp(−c²)`.** To reach `exp(−c²)` one must inflate by
`√2·c + √(2 log r)` — also proved, as `Arlib.KV97.mul_exp_kappaOf_sqrt_two_le`.

The paper pairs an inflation of `c + √(2 log r)` with a loss of `2e^{−c²}`; those
two are inconsistent, and the discrepancy is a full factor of `2` in the exponent.
[`Arlib/Lattice/KV97/Defs.lean`](Arlib/Lattice/KV97/Defs.lean) was corrected to
match what is provable: `lossOf c ε = e^{−c²/2} + ε` and `cOf ε = √(2·log(4/ε))`,
so that `Arlib.KV97.exp_cOf` still delivers the tuned `ε/4`. The leading `2` of
the paper's `2e^{−c²}` is also unnecessary here — the escape event is one-sided
per facet and the union bound over `r` facets already accounts for multiplicity.

### 4b. Theorem 2 divides `ε` by `Vol(P')`, but its own proof produces `ε` additively

**This is the sharpest discrepancy found, and this section has been wrong once
already. Read the correction box before acting on anything above it.**

Theorem 2 is stated as

```
(1 − 2e^{−c²} − ε)/Vol(P')  ≤  Pr[rnd p = x]  ≤  1/Vol(P')
```

so the `ε` sits *inside* the numerator — a **relative** error. But the proof
immediately below derives

```
Pr[rnd p = x]  =  (1/Vol(P'))·∫_{p ∈ P'} Pr[rnd p = x ∣ p] dp  +  c,   |c| ≤ ε
```

where the `c` comes from swapping the sampler's density for the uniform one. That
is an **additive** `ε`, and it is what a total-variation hypothesis buys: the
integrand `Pr[rnd p = x ∣ p] = ∏ᵢ tent(pᵢ−xᵢ)` lies in `[0,1]`, so
`|∫f dν − ∫f dunif| ≤ TV(ν, unif)` and no better.

The discrepancy between the printed statement and the printed proof is real, and
the printed upper bound `≤ 1/Vol(P')` is wrong under the additive reading — it
should read `≤ 1/Vol(P') + ε`. That much stands.

> ## ⚠ CORRECTION — the conclusion previously drawn here was wrong
>
> This section used to conclude that the additive reading "makes the theorem
> useless as stated" because "`ε ≪ 1/Vol(P')` … no sampler delivers", and
> therefore that **the hypothesis must be pointwise rather than total-variation**.
> That conclusion is **false**, and is refuted by machine-checked proof in
> [`Arlib/MarkovChains/Continuous/PointwiseRoute.lean`](Arlib/MarkovChains/Continuous/PointwiseRoute.lean).
>
> **An additive error `ε` *is* a relative error `ε·V`.** Ask the sampler for
> tolerance `θ/V` rather than `θ`, and
> `Arlib.PointwiseRoute.theorem2_of_tvLe_inv_volume` delivers exactly the window
> Theorem 2 needs:
>
> ```
> TVLe μ (uniformOn volume S) (ofReal (θ/V))
>   ⟹  (1 − (E+θ))/V ≤ ∫ prodTent x p ∂μ ≤ (1 + θ)/V
> ```
>
> The objection in the old second bullet — "summing over the `N` lattice points
> contributes `N·ε`, which does not cancel" — evaporates at `ε = θ/V`: the sum
> contributes `Nθ/V` against a total of order `N/V`, i.e. a *relative* `θ`. That
> is `Arlib.PointwiseRoute.ratio_bounds_of_tvLe`.
>
> **And it is affordable**, which is what the old argument missed: mixing time is
> *logarithmic* in the TV tolerance.
> `Arlib.PointwiseRoute.conductanceMixingTime_inv_volume_le` bounds the step count
> for tolerance `θ/V` by `(log M + 2 log V + 2 log(1/θ))/φ² + 1` — **linear in
> `log V`**. For the `10^ρ`-dilated polytope `log V = Θ(nρ)`, polynomial in the
> description size. The old reasoning confused `ε` being exponentially small *as a
> number* with its being expensive *to achieve*.
>
> **Worse for the old conclusion: the pointwise hypothesis is not merely harder,
> it is unattainable for the actual chain.** `Arlib.MarkovChains.PointwiseClose`
> and `PointwiseAlmostUniform` presuppose the law has a density, and a ball-walk
> law started at a point never does — the `(1−ℓ(x))·δ_x` holding term keeps an
> atom forever. One atom defeats pointwise closeness for **every** `ε`, `⊤`
> included (`Arlib.PointwiseRoute.not_pointwiseClose_of_atom`), while a TV bound
> tolerates it (`Arlib.PointwiseRoute.exists_tvLe_with_atom`). So the route this
> section recommended cannot work for the sampler we actually intend to build, and
> the route it dismissed can.
>
> Both KV97 ("variational distance to the uniform density") and the consuming
> paper ("`ε`-close to uniform over `P'` in TV distance") say total variation.
> **They were right to; this audit was wrong to second-guess them.** What the
> papers do owe is the `1/V` scaling of the tolerance, which neither states.

### 4b′. The recommendation was acted on — what changed in the interface

The correction box above ended with a recommendation: that `Ttc.KV97Sampler`
should carry `contLaw` and a `law_tv : TVLe …` in place of
`contDensity`/`density_au`. **That has now been done.** The old text that followed
— "Theorem 2 will be stated with the **pointwise relative** hypothesis, because
that is what makes `cor:linf` true, and the module docstring will say so", and the
pull-quote "the continuous sampler this development must eventually construct has
to be almost-uniform **pointwise**, not merely close in total variation" — was
still asserting the retracted conclusion two paragraphs after retracting it. It is
**deleted**, not softened.

The interface today (`AUDIT.md` §2 has the full 15-field table):

* **Out:** `contDensity`, `density_au`, `density_int`.
* **In:** `contLaw`, `isProbContLaw`, `contVol_eq`, `law_tv`.

Three consequences an auditor should check rather than take on trust:

1. **`contVol` stopped being a free gauge.** Under the density formulation the
   normaliser cancelled out of `sampD`, so any positive value worked —
   `Ttc.KV97Sampler.reNormalise` proved exactly that, and is now deleted. Under TV
   it is **determined**: the tolerance is `ε'/(4·contVol i)`, so shrinking
   `contVol` strictly *strengthens* `law_tv` and no rescaling compensates.
   `contVol_eq` therefore pins it to `Vol(P')`. This costs **no new assumption**:
   `contVol_pos` already forces `Vol(P') ∉ {0, ⊤}`, since `0 < x.toReal` does.
2. **The window is weaker on the low side, by exactly `θE`.** The TV route gives
   `1 − (E+θ)`; the pointwise route gave `(1−θ)(1−E) = 1 − θ − E + θE`. Negligible,
   but it is a real loss and not a wash.
3. **The tuning constant moved from `5/8` to `1/2`.** The consuming bound needs
   `Ttc.TtcProb.epsPrime_le_one_half` where it used to need
   `epsPrime_le_five_eighths`. Both are proved from
   `Ttc.TtcProb.epsPrime_le_one_twelfth`; the `5/8` one is retained for the now
   off-path pointwise route. `TTC` runs at `ε' ≤ 1/12`, so neither threshold binds.

**What is *not* proved for the ball walk.** Every result in the TV route consumes
a `TVLe`/`MixesWithin` hypothesis. The conductance/isoperimetry bound
`φ ≥ 1/poly` remains open, and this correction neither helps nor hinders it. The
migration changed which hypothesis is *stated*; it did not discharge one.

`Arlib.TVLe` and `TVLe.integral_le` are the honest total-variation object and the
honest *additive* transfer; both are proved and neither is going away. Note
`TVLe.integral_le` is itself **not** reached by the headline — the `Ttc` bridge
routes through `Arlib.PointwiseRoute.window_of_tvLe`, which uses it.

This section has still not been double-checked against a non-scanned copy of
KV97; treat the reading of the source as a finding to confirm, not a settled
erratum. The *mathematics* of the correction is machine-checked regardless.

### 4c. Theorem 2's escape mass is a hypothesis here, and deliberately so

[`Arlib.KV97.theorem2`](Arlib/Lattice/KV97/Theorem2.lean) takes the escape mass
`∫_{P'ᶜ} prodTent x p dp ≤ E` as an explicit real hypothesis rather than inlining
the tail bound. That is a modelling choice an auditor should weigh:

* **In favour.** The two halves of Theorem 2 — averaging against the sampler's
  law, and bounding the escape — are mathematically independent, and each is
  checkable alone.
* **Against.** A reader could instantiate it at a vacuous `E ≥ 1` (where
  `1 − E ≤ 0` and the lower bound says nothing). **The theorem is not false there,
  but it is empty**, so the discharge is what gives it content.

`Arlib/Lattice/KV97/Escape.lean` proves the tail for *any* independent,
`[−1,1]`-supported, mean-zero displacement, but instantiated it only at the
**discrete** rounding law on `ℤⁿ`, whereas Theorem 2's escape term is under the
**continuous** tent density on `ℝⁿ` — the `Y` of KV97's own proof. Those are
different objects, and the gap was real.
[`Arlib/Lattice/Rounding/ContTent.lean`](Arlib/Lattice/Rounding/ContTent.lean)
closes it: it builds the continuous tent product measure, proves coordinatewise
independence, instantiates `escape_prob_le` there, and — the step that matters —
proves the change of variables `∫_{T} prodTent x p dp = Pr[x + Y ∈ T]`
(`setIntegral_prodTent_eq_tentPi_real`).

So `Arlib.KV97.theorem2_of_body` carries no `E`. **The `Ttc` bridge nevertheless
routes through the parametric `theorem2`** (the walk reports `theorem2` `true`,
`theorem2_of_body` `false`), discharging `E` on its own side. An auditor reading
the parametric form should still note the `E ≥ 1` degeneracy above.

### 4d. KV97's `r` is a *local* facet count; the consuming paper's is *global*

KV97 §2 defines

> "Let `r` be the maximum number of facets of `P` that intersect any `C(z,1)` for
> `z` an integral point."

— a **local** quantity. `cor:linf` in `sections/proof-appendix.tex:155` uses
`r = facet(P)`, the **total** number of facets, and `Ttc.Params.r` /
`Ttc.TtcProb.facets_le` / `Ttc.KV97Sampler.facetBound` likewise bound the total.

The total upper-bounds the local one, so substituting it is *sound* (it only
weakens the bound), but the two are not the same number and neither paper says so.
Using the global count is the conservative choice and is what this development
does; the local refinement is where KV97's stated bounds are sharper than what is
proved here.

### 4e. Is `A` nonnegative?

The introduction says `P = {x ∈ ℝⁿ : Ax ≤ b}` "where `A` is an `m × n` matrix of
**nonnegative** reals and `b` is an `m`-vector of nonnegative reals." §2 restates
it as "`A` is an `m × n` matrix of **reals** and `b` is an `m × 1` of nonnegative
reals" — nonnegativity of `A` is dropped without comment. The proof does not use
it. [`Arlib/Convexity/Polytope.lean`](Arlib/Convexity/Polytope.lean) assumes
neither, and even drops the `‖Aᵢ‖ > 0` side condition (the degenerate row `0 ≤ bᵢ`
is handled directly), so this is a non-issue mathematically — but an auditor
comparing statements should know the source is internally inconsistent.

### 4f. Constants cannot be read off the scan

The PDF is a 1997 scan with an OCR text layer. It renders `1 − 2re^{−c²/2}` as
`1-ze-c`, `Vol(P̄)` as `VOI(P)`, "polytopes" as "polytopea", and Lemma 1's
`8n√(log r)|Aᵢ|` bound is only partly legible. **No constant in this development
may be transcribed from the OCR.** Every one must be re-derived from the argument
and cross-checked against `sections/proof-appendix.tex`, which states `claim:linf`
and `cor:linf` cleanly. The extracted text is kept only as a navigation aid.

### 4g. `cor:linf`'s upper bound is FALSE for large `ε`

`sections/proof-appendix.tex:157` states `cor:linf` for **any** `0 < ε ≤ 1`:

```
(1−ε)/|P ∩ 𝕃ⁿ|  ≤  Pr[rnd p = x ∣ rnd p ∈ P]  ≤  (1+ε)/|P ∩ 𝕃ⁿ|
```

Under the corrected Theorem 2, **the upper half does not hold on that whole
range.** The printed proof divides by an upper bound of `1/Vol(P')`, but the
honest two-sided window carries `(1+ε/4)/Vol(P')`, and that extra factor is
exactly the gap. Working it out, the requirement is `(1+ε/4)/((1−ε/4)²) ≤ 1 + ε`,
i.e.

```
ε² − 7ε + 4 ≥ 0     ⟺     ε ≤ (7 − √33)/2 ≈ 0.62771.
```

* [`Arlib.KV97.ratio_bounds_tuned_sharp`](Arlib/Lattice/KV97/Corollary.lean)
  recovers the paper's `(1 ± ε)/N` **verbatim**, under `ε ≤ 5/8 = 0.625`.
* [`Arlib.KV97.ratio_bounds_tuned`](Arlib/Lattice/KV97/Corollary.lean) is the
  unrestricted version, and its upper bound is `(1 + 2ε)/N` — **twice** the
  paper's.
* The claim is not merely unproven above the threshold, it is **false**. At
  `ε = 1` the true constant is `(1+¼)/(1−¼)² = 20/9 = 2.22…`, against the paper's
  `1 + ε = 2`. This is machine-checked: `(1 + 1/4)/((1 − 1/4)*(1 − 1/4)) > 2` by
  `norm_num`.

**Does this break the main result? No.** `TTC` invokes `eq:almostuniform` at
`ε' = Ttc.Params.epsPrime = ε/12` with `ε ≤ 1` (`Ttc.TtcProb.hε1`), so
`ε' ≤ 1/12 ≈ 0.083`, comfortably inside the valid range. The paper's own usage
never approaches the threshold. What is wrong is the *generality* of the printed
corollary, not the instance this project needs.

> Note that after the §4b′ migration `ratio_bounds_tuned_sharp` is **no longer on
> the headline's dependency path** (the walk reports `false`) — it belonged to the
> pointwise route. The finding above still stands as a finding about the paper; it
> is simply no longer a step of this proof. The live threshold is
> `Ttc.TtcProb.epsPrime_le_one_half`.

The lower half is unaffected: `(1−ε/4)²/(1+ε/4) ≥ 1 − ε` holds unconditionally
for `ε ≥ 0` (it reduces to `0 ≤ ε/4 + 5ε²/16`), so the paper's lower constant is
exactly right.

Note also the *abstract* form: with a pointwise deviation `ε` and escape mass `E`,
the honest two-sided window is `(1 ± 4(ε+E))/N`
([`Arlib.KV97.ratio_bounds_of_loss`](Arlib/Lattice/KV97/Corollary.lean), valid for
`ε + E ≤ 1/2`), and the `4` is **not** slack — the upper half is an *equality* at
`ε = 1/2`, `E = 0`.

### 4h. Lemma 1's constant is better than claimed — and `acceptance` is a semantic `def`

Two notes, one benign and one that an auditor must not skip.

**The constant.** At `ε, E, η ≤ 1/4` and `κ/γ ≤ 1/n`, the acceptance probability
is bounded below by `(¾·¾)/((5/4)·e) = 9/(20e) ≈ 0.16555`, proved as
[`Arlib.KV97.acceptance_ge_exp`](Arlib/Lattice/KV97/Lemma1.lean). That is
**larger** than the paper's `1/8 = 0.125`, so the paper's claim follows
(`Arlib.KV97.acceptance_ge_one_eighth`) — it is simply not sharp. Machine-checked:
`1/8 < 9/(20·e)` reduces to `20e < 72`. Unlike §4a and §4g this is a discrepancy
in the paper's *favour*, and nothing depends on it.

**`Arlib.KV97.acceptance` was a `def` whose name claimed more than its body proved
— now closed, and the closing turned up more than expected.**

> Earlier versions of this page called it `Ttc.acceptance`. There is no such
> declaration; the name is `Arlib.KV97.acceptance`, in
> [`Arlib/Lattice/KV97/Lemma1.lean`](Arlib/Lattice/KV97/Lemma1.lean).

```lean
def acceptance (pt : ι → EuclideanSpace ℝ (Fin n)) (w : … → ℝ) : ℝ := ∑ i, w (pt i)
```

The name says "the probability that the rejection loop accepts". The body says "a
finite sum of weights". The identification is now **proved**, not assumed:

* `Arlib.KV97.acceptance_eq_measure_apply` —
  `(μ P).toReal = acceptance pt (fun x => (μ {x}).toReal)`.
* `Arlib.KV97.roundedLaw` — the law of the rounded draw, **built as an actual
  measure**; it did not previously exist in `Arlib`, which only ever manipulated
  the conditional kernel `roundLaw` and the weight function. Building it needed
  `Arlib.KV97.measurable_roundLaw` (Giry-measurability), also absent.
* `Arlib.KV97.toReal_roundedLaw_eq_acceptance` — the weight is *literally* Theorem
  2's `w`, so the Theorem 2 → Lemma 1 chain is closed against a real measure; and
  `toReal_roundedLaw_ge_one_eighth` restates the headline about that measure.

**The docstring had been under-hypothesised, not merely unproved.** The
identification needs **three** substantive hypotheses where the docstring named
one and dismissed it as unnecessary ("injectivity is used only by
`acceptance_eq_sum_image`. None of the bounds below need it"):

1. `pt` **injective** — true of the bounds, false of the identification.
   Counterexample, machine-checked:
   `Arlib.KV97.measure_range_lt_acceptance_of_not_injective` — a Dirac measure
   with constant `pt : Fin 2 → ℝⁿ` has mass `1` but `acceptance = 2`.
2. `pt` **exhaustive** (`P ∩ 𝕃 = Set.range pt`) — never mentioned; without it the
   sum misses mass.
3. **the law is carried by the lattice** (`μ 𝕃ᶜ = 0`) — never mentioned; without
   it `{rnd p ∈ P}` has non-lattice mass no singleton accounts for.

(There is a fourth, `hfin : ∀ i, μ {pt i} ≠ ⊤`, but that is a finiteness guard of
the kind `ENNReal.toReal` always needs, not a modelling assumption.)

**Consequence for the non-vacuity witness.** `Arlib.KV97.exp_neg_one_le_acceptance_cube`,
this file's §3 witness, takes `pt` **constant** — its old docstring called this
"harmless". Under (1) it is not harmless: for that witness `acceptance` is
`⌈Vol(P)⌉` copies of one weight, not a probability. The witness certifies that the
*bounds'* hypothesis bundle is inhabited, and nothing more. That is still a real
check — the bounds are what Lemma 1 asserts — but it is a weaker check than it
appeared to be.

**One further hypothesis worth naming.** `acceptance_ge_const` carries
`hlattice_nonconv : Vol(P).toReal ≤ (1+η)·N`. That is `lem:nonconv`/`lem:lattice`,
which **is** proved — but in the `Ttc` project
([`Ttc/Nonconv/Assembled.lean`](Ttc/Nonconv/Assembled.lean),
[`Ttc/Lattice/Assembled.lean`](Ttc/Lattice/Assembled.lean)), not in `Arlib`, which
may not import it. It is carried as an explicit, long-named hypothesis so nobody
mistakes it for an `Arlib` theorem.

---

## 5. Re-checking the machine-checkable part

```bash
cd lean
lake exe cache get && lake build          # zero "declaration uses 'sorry'"

# the staging rule that keeps Arlib portable back into the shared arlib repo
grep -rn "^import Ttc" Arlib/             # must return nothing

# must return nothing (the greps drop three docstrings that discuss the words)
grep -rnE "\bsorry\b|\badmit\b|native_decide|sorryAx|^axiom " \
  Ttc.lean Ttc/ Arlib.lean Arlib/ | grep -v '`sorry`' | grep -v '`sorryAx`'
```

> The previous version of this recipe used `grep -rn "sorry\|admit\|…"` without
> word boundaries and without the second filter. It reported **two** hits — the
> word "admits" in a `Cheeger.lean` docstring, and a literal `` `sorryAx` `` in a
> `LocalizationLemma.lean` docstring — while the page claimed it "must return
> nothing". The form above returns nothing.

`Arlib/` orphans do not show up in a `lake build` sweep the way `Ttc/` orphans do
— see the note in [`AUDIT.md`](AUDIT.md) §5, which has the orphan-detection
command. Under `Arlib`'s `globs` an unwired file still *builds*, so an `.olean` is
not evidence that `import Arlib` reaches it.

```lean
import Arlib
-- the foundation Theorem 2 consumes
#print axioms Arlib.Lattice.Rounding.integral_prodTent   -- double stochasticity
#print axioms Arlib.Lattice.Rounding.iIndepFun_latDisp
#print axioms Arlib.Probability.rounding_tail_bound_kappa -- the Azuma step
#print axioms Arlib.TVLe.integral_le                      -- the ε term
#print axioms Arlib.Rejection.ratio_mem_relErr            -- cor:linf's arithmetic
#print axioms Arlib.Polytope.volume_inflate_le            -- Lemma 1's engine
#print axioms Arlib.Lattice.ncard_inter_fineLattice       -- the 𝕃ⁿ transport
-- KV97 proper
#print axioms Arlib.KV97.theorem2
#print axioms Arlib.KV97.theorem2_of_body
#print axioms Arlib.KV97.cor_linf_tuned
#print axioms Arlib.KV97.acceptance_ge_const
#print axioms Arlib.KV97.toReal_roundedLaw_eq_acceptance  -- §4h, the closed def
-- the TV route (§4b)
#print axioms Arlib.PointwiseRoute.theorem2_of_tvLe_inv_volume
#print axioms Arlib.PointwiseRoute.not_pointwiseClose_of_atom
#print axioms Arlib.PointwiseRoute.exists_theorem2_of_tvLe_witness  -- non-vacuity
-- Phase 4 so far
#print axioms Arlib.prekopa_leindler_one_dim              -- 1-D Prékopa–Leindler
#print axioms Arlib.prekopa_leindler_pi                   -- ℝⁿ Prékopa–Leindler
#print axioms Arlib.brunn_minkowski_sharp                 -- sharp Brunn–Minkowski
#print axioms Arlib.MarkovChains.conductance_const_piHalf      -- non-vacuity
#print axioms Arlib.MarkovChains.mixesWithin_lazy_ballWalk_unitBall
```

All report `[propext, Classical.choice, Quot.sound]`.

**The check that actually matters.** Run the transitive dependency walk of
[`AUDIT.md`](AUDIT.md) §5 from `Ttc.TtcProb.volume_estimate`. An import only says
a file is *visible*, not that any of its results is *used* — and a KV97
development that the headline does not reach discharges nothing, however green it
is. At the time of writing it reports:

| Name | Reached | Reading |
| --- | --- | --- |
| `Ttc.TtcProb.samp_unif`, `theta_lo`, `theta_hi` | **true** | the ex-fields are genuinely derived |
| `Arlib.KV97.theorem2`, `Arlib.TVLe` | **true** | **KV97 is load-bearing** |
| `Ttc.almostUniform_of_kv97_law`, `_window`, `Ttc.uniformOn_prodTent_window`, `Ttc.prodTent_window_of_tvLe` | **true** | the `Ttc`-side bridge |
| `Ttc.almostUniform_of_kv97_density` | **false** | proved, **not** load-bearing — its hypothesis is a density and the interface no longer has one. The two routes are provably incomparable (§4b′), so this name *cannot* be in the cone |
| `Arlib.KV97.theorem2_of_body`, `cor_linf_tuned`, `acceptance_ge_const`, `ratio_bounds_tuned_sharp`, `Arlib.TVLe.integral_le`, `Arlib.Polytope.volume_inflate_le` | **false** | proved, off the path — see §0 and §4g for why each is off it |

Roughly 137 `Arlib.*` declarations are reached in total, 29 of them under
`Arlib.KV97`. If those counts drop to zero, the wiring has regressed.
