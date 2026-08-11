/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.Bridge
import Arlib.Convexity.GaussianCooling.Estimator
import Arlib.Convexity.GaussianCooling.ZLogconcave
import Arlib.Convexity.GaussianCooling.PhaseMean
import Arlib.Convexity.GaussianCooling.PhaseVar
import Arlib.Convexity.GaussianCooling.PhaseSchedule
import Arlib.Convexity.GaussianCooling.TerminalPhase
import Arlib.Convexity.GaussianCooling.Unblock
import Mathlib.Analysis.Convex.Measure

/-!
# `Volume/CousinsVempala`: §5.2 assembled, and what the volume oracle still owes

`Ttc.VolumeAlgorithm` (`Volume/Oracle`) is Cousins–Vempala Theorem 1.1 as an
*assumption*. This file is the assembly step towards making it a *theorem*: it puts
together §5.2 of

> Ben Cousins, Santosh Vempala, *Gaussian Cooling and O\*(n³) Algorithms for Volume and
> Gaussian Volume* (arXiv:1409.6011)

— the telescoping product, Chebyshev, and the median boost — and then builds a
`Ttc.VolumeAlgorithm` out of it, carrying every input that is **not** yet proved as an
explicit, named hypothesis of the construction.

**The volume oracle is not constructible today.** `Ttc.VolumeAlgorithm.cousinsVempala`
below is a genuine construction of the structure, but it takes as arguments the four
facts about the per-phase ratio estimators that only a *sampler* can supply
(`hphase_mean`, `hphase_var`, `hphase_indep`, and the endpoint `hchain_end`). Those are
the ones blocked on the isoperimetric inequality for logconcave densities, which is not
proved anywhere in this development: without it there is no mixing bound for the ball
walk, hence no sampler, hence no way to know that the average of the per-phase scores has
the mean `G(σᵢ₊₁²)/G(σᵢ²)` that the telescope needs. Nothing here declares that gap
closed; it is visible in the type of the construction.

`Ttc.VolumeAlgorithm.cousinsVempalaOfSampler` **moves the boundary**: it takes an explicit
enclosing radius and a *total-variation* guarantee for the phase sample, and derives
`hphase_mean` and `hphase_var` from them rather than assuming them. That converts the two
sampler hypotheses into one hypothesis about the sampler's mixing — which is still the open
problem — and makes the quantitative price visible: the tolerable TV error carries the
factor `e^{−R²/σᵢ²}`. **It is a reduction, not an algorithm**, and nothing in this file
bounds any running time or implies a polynomial one; the conductance constants available in
this repository are exponentially small in `n`.

What *is* proved here, unconditionally:

## §5.2, the parts that do not need a sampler

* `Ttc.CV.mem_relErr_iff` — `x ∈ relErr ε b ↔ |x − b| ≤ ε·b`.
* `Ttc.CV.relErr_trans` — relative errors compose: `x ∈ relErr ε b` and
  `b ∈ relErr η c` give `x ∈ relErr (ε + η + ε·η) c`. (The tool for absorbing an
  endpoint bias into the accuracy; the assembly below is stated with exact endpoints,
  so it is not used there.)
* `Ttc.CV.measure_notMem_relErr_le` — **Chebyshev in relative-error form**: a
  second-moment ratio `E(X²) ≤ c·E(X)²` gives `P(X ∉ (1±ε)E(X)) ≤ (c−1)/ε²`.
* `Ttc.CV.prod_range_ratio`, `Ttc.CV.prod_fin_ratio` — **the telescoping product**
  `∏_{i<m} A(i+1)/A(i) = A(m)/A(0)`.
* `Ttc.CV.prod_relErr_ge` — the product estimator's accuracy: independent factors each
  with relative second moment `1 + κ/m` give
  `P(∏ Wᵢ ∈ (1±ε)·E(∏ Wᵢ)) ≥ 1 − (e^κ − 1)/ε²`, uniformly in the number of phases.
  This is `Arlib.GaussianCooling.prod_sq_div_le_exp` fed into Chebyshev.
* `Ttc.CV.run_relErr_ge` — **one run of the algorithm**: with `A i = G(σᵢ²)` the cooling
  chain and `Wᵢ` an unbiased estimator of `A(i+1)/A(i)`, the output `A(0)·∏ Wᵢ` lands
  within `(1±ε)` of `A(m)` with probability `≥ 1 − (e^κ − 1)/ε²`.
* `Ttc.CV.run_relErr_four_fifths` — the paper's constant-confidence form: a variance
  budget `e^κ − 1 ≤ ε²/5` makes that probability `≥ 4/5`.
* `Ttc.CV.median_relErr_ge` — **the `4/5 → 1 − p` median boost**, at the `O(log 1/p)`
  repetition rate, specialized to a relative-error target from
  `Arlib.GaussianCooling.median_boost`.
* `Ttc.CV.G_indicator_le`, `Ttc.CV.G_indicator_ge` — **the hot end of the telescope**:
  for a convex body `K ⊆ R·Bₙ`, `e^{−R²/(2s)}·Vol(K) ≤ G(s) ≤ Vol(K)`, so the last
  Gaussian in the schedule is within a controlled factor of the volume.
* `Ttc.CV.G_indicator_mem_relErr` — the same two bounds as the single relative-error
  statement `G(s) ∈ (1 ± (1 − e^{−R²/(2s)}))·Vol(K)`. **This is the honest `hchain_end`**,
  and it is what the biased-endpoint pipeline below consumes.
* `Ttc.CV.run_relErr_four_fifths_biasedEnd`, `Ttc.CV.gaussianCooling_accuracy_biasedEnd`
  — §5.2 with the endpoint idealization removed: a chain whose endpoint is only within a
  relative `η` of `Vol(K)` still gives the `1 − δ` guarantee, at accuracy `ε + η + εη`
  (`relErr_trans`). No sampler is needed for this step.

## The construction, and the debt it carries

* `Ttc.VolumeAlgorithm.ofRuns` — **the median-boost construction.** Given a family of
  independent runs that are each correct with probability `4/5` and a (measurable)
  median of them, this builds a `Ttc.VolumeAlgorithm n` outright: every field is
  discharged. The mathematical content spent here is `median_boost`.
* `Ttc.VolumeAlgorithm.cousinsVempalaOfBiasedEnd` — the same construction with the exact
  endpoint replaced by the relative-error one `G_indicator_mem_relErr` actually proves,
  plus the accuracy-splitting side condition `hcompose`. Both constructions carry
  non-vacuity witnesses (`cousinsVempalaWitness`, `cousinsVempalaBiasedWitness`).
* `Ttc.VolumeAlgorithm.cousinsVempala` — **§5.2 in full**, built on `ofRuns` by taking
  each run to be `chain 0 · ∏ᵢ Wᵢ`. Its hypotheses are the residual debt, and they are
  spelled out inline in its type rather than hidden behind a predicate. Four of them are
  mathematical:
  - `hchain_end` — the last Gaussian integrates to `Vol(K)`. **Discharged, in its honest
    approximate form**: `Ttc.VolumeAlgorithm.cousinsVempalaOfBiasedEnd` is the same
    construction with `hchain_end` weakened to
    `chain (phases) ∈ relErr (endBias ε) Vol(K)`, which is exactly what
    `Ttc.CV.G_indicator_mem_relErr` proves for a body inside `R·Bₙ`, with
    `endBias ε = 1 − e^{−R²/(2σ_m²)}`. The price is the scheduling side condition
    `hcompose`. (The equality version is presumably *not* attainable by a genuine Gaussian
    endpoint — the weight `e^{−‖x‖²/(2s)}` is `< 1` off the origin, so `G(s) < Vol(K)`
    strictly for a body of positive volume in dimension `≥ 1`. That strictness is **not**
    formalized here; only the two-sided bound above is.)
  - `hphase_mean` — each phase's score has mean `G(σᵢ₊₁²)/G(σᵢ²)`. **This is the
    sampler.** Blocked on isoperimetry → conductance → mixing.
  - `hphase_var` — each phase's score has relative second moment `1 + κ/m`. This is
    §5.1, and is *available*: `Arlib.GaussianCooling.fixed_var_bound_ratio_indicator`
    proves exactly `E(Y²)/E(Y)² ≤ 1 + 2/n` for the indicator of a convex body, with no
    assumed input — but only for a score computed at an *exact* sample, so it too is
    consumed through the sampler.
  - `hphase_indep` — the `m` phases use independent randomness.

  and the rest (`hreps`, `hbudget`, measurability, `hmed`, `hindep_runs`,
  `hphase_prodLp`) are scheduling and admissibility guards.

* `Ttc.VolumeAlgorithm.cousinsVempalaOfApproxMean` — the same construction with
  `hphase_mean` weakened from an equality to a two-sided relative bound, which is the only
  shape a sampled score can have. Witness: `cousinsVempalaApproxMeanWitness`.
* `Ttc.VolumeAlgorithm.cousinsVempalaOfSampler` — **`hphase_mean` and `hphase_var` derived,
  not assumed.** New inputs: an explicit radius (`Ttc.CV.cvRadius` supplies one from
  `cousinsVempala`'s own hypotheses) and a `TVLe` guarantee between the law of the phase
  sample and `Arlib.GaussianCooling.coolLaw`. It also derives `hchain_pos`, `hchain_end`
  and `hW_meas`, by running the whole pipeline on the *open* body `interior K` — a convex
  set need not be Borel measurable, and `Ttc.CV.volume_interior_eq` is what makes the
  substitution free.
* `Ttc.VolumeAlgorithm.cousinsVempalaOfSamplerFixedRate` — **`hvar_exact` derived too.** The
  same construction with the exact-law second moment supplied at *every* phase by
  `Ttc.CV.hvar_exact_of_fixedRate_all`, at `varConst = 1 + 2/n`. It costs the fixed rate
  (`hrate`), `3 ≤ n`, and the terminal flatness inequality (`hflat`); it costs **no new
  radius** — `cousinsVempalaOfSampler`'s own `radius` parameter, composed with
  `interior_subset`, is exactly the enclosure the terminal bound needs. After it, `hTV` —
  the sampler — is the only mathematical debt left in the bundle. **But the schedule it
  admits does no cooling at all** — see the finding below.
* `Ttc.VolumeAlgorithm.cousinsVempalaOfSamplerCooling` — **the same on the general-`α`
  schedule of `Arlib/Convexity/GaussianCooling/PhaseSchedule.lean`**, which provably
  anneals. The phase count and rate are determined by the required cooling `e^L` and the
  budget slice `κ`: `m = coolPhases n L κ`, `α = coolRate n L κ`; `varConst = 1 + κ/m`,
  `varSlack = (varBudget ε − κ)/m > 0` when `κ < varBudget ε`; flatness is at the matching
  constant `log(1 + κ/m)`; and `3 ≤ n` is no longer needed. `hTV` is still the only
  mathematical debt.

## THE FINDING: the fixed-rate construction's cold start already is the answer

`Ttc.CV.chain_zero_mem_relErr_of_flat` (and `Ttc.CV.cold_start_mem_relErr_of_flat`, stated
on `interior K` so its target is `Vol(K)` itself):

  under `hflat` and `2m ≤ n·varBudget ε`, `chain m σsq K 0 ∈ (1 ± 11/(5n))·Vol(K)`.

Three elementary steps, all machine-checked: `hflat` at `j = m − 1` with
`log(1 + 2/n) ≤ 2/n` forces `σ_{m−1}² ≥ nR²/4` (`Ttc.CV.sigmaSq_ge_of_flat`); `hvarSum`
with `varSlack ≥ 0` plus `hbudget` force `2m ≤ n·varBudget ε`, hence
`(1 + 1/n)^m < 11/10` (`Arlib.GaussianCooling.geomSchedule_total_cooling_lt`); so
`σ₀² > 5nR²/22` (`Ttc.CV.sigmaSq_zero_gt_of_flat_of_meet`) and the phase-`0` Gaussian is
within `e^{−11/(5n)}` of `1` on all of `K`.

So `Ttc.VolumeAlgorithm.cousinsVempalaOfSamplerFixedRate` is consistent
(`Ttc.CV.flat_slacks_satisfiable`) and non-vacuous, but the telescope it drives has nothing
left to telescope: its first factor alone estimates `Vol(K)` to relative error `O(1/n)`. It
is the observation "a Gaussian of variance `Ω(nR²)` is flat on `R·Bₙ`" wearing an
algorithm's clothes.

**The general-`α` schedule escapes this, at a price that is quantified rather than hidden.**
`Ttc.CV.cool_schedule_anneals` proves `e^L·σ₀² ≤ σ_m²` — no `11/10` cap —, and
`Ttc.CV.cool_flat_slacks_satisfiable` proves `hflat`, the annealing and both slack
conditions hold *simultaneously* at a strictly positive TV error, so the crux question of
joint satisfiability answers **yes**. But the flatness threshold now scales with the phase
count, and `Ttc.CV.cold_start_exponent_ge_of_coolRate` shows the cold-start exponent is
`log(1 + κ/m)·(1+α)^{m−1} ≈ κ²e^{2L}/(8(n+1)L²)`, which beats the fixed rate's `11/(5n)`
ceiling only once `e^{2L} ≳ 17.6·L²/κ²` — a dimension-free crossover at `L ≈ 7.2` for
`κ = log(21/20)/2`. Below it, the general schedule is exactly as empty as the fixed one.
**Nothing here bounds any running time**, in either direction.

## The sampler-side lemmas added for that

* `Ttc.CV.run_relErr_four_fifths_approxMean` — one run, with approximately unbiased phases.
* `Ttc.CV.volume_interior_eq` — `Vol(interior K) = Vol(K)` for convex `K`, from
  `Convex.addHaar_frontier`. The reason no `MeasurableSet K` hypothesis is needed.
* `Ttc.CV.cvRadius`, `Ttc.CV.subset_closedBall_cvRadius` — the enclosing radius, from
  convexity + inscribed unit ball + finite volume alone.
* `Ttc.CV.integral_map_mem_relErr_of_tvLe`, `Ttc.CV.sampledPhase_mean_mem_relErr` — the TV
  transport of the phase mean, through the sampling map.
* `Ttc.CV.tv_slacks_satisfiable`, `Ttc.CV.tv_slack_threshold_pos`,
  `Ttc.CV.exists_pos_tvErr` — the satisfiability check: both slack conditions are upper
  bounds on one positive quantity, so a **strictly positive** TV error meets both.
* `Ttc.CV.hvar_exact_of_fixedRate` — the exact-law second moment at an interior phase of
  the fixed-rate schedule, from `Arlib.GaussianCooling.coolLaw_sq_moment_le`. Its docstring
  records the two things it does *not* cover: the terminal phase, and the fact that meeting
  the variance budget at rate `1/n` caps the schedule's total cooling below `11/10`
  (`Arlib.GaussianCooling.geomSchedule_total_cooling_lt`) — so the fixed-rate schedule
  cannot anneal, and the general-`α` replacement is not constructed anywhere here.
* `Ttc.CV.hvar_exact_of_fixedRate_all` — **the same at *every* phase**, interior and
  terminal, from `Arlib.GaussianCooling.coolLaw_sq_moment_le_all`. The terminal phase costs
  a radius and the flatness inequality `R² ≤ 2σⱼ² log(1 + 2/n)`, and neither is optional:
  `Arlib.GaussianCooling.terminal_sq_moment_unbounded` proves that on `K = B₁` — which
  satisfies every hypothesis the interior theorem places on the body — no constant depending
  on `n` alone bounds the terminal ratio. `Ttc.CV.flat_of_sigmaSq_ge` (the condition holds
  once `σⱼ² ≥ nR²/2`), `Ttc.CV.flat_of_fixedRate_terminal` (it need only be checked at
  `j = m − 1`) and `Ttc.CV.one_div_le_log_one_add_two_div` are the supporting arithmetic.
* `Ttc.CV.flat_slacks_satisfiable` — the numeric consistency check: at `ε = 1`, `m = 2`,
  `n ≥ 100`, `innerAcc = 1/2`, `meanBias = 1/3`, `phaseBias = 1/12`,
  `varBudget = log(21/20)` and `σⱼ² = (nR²/2 + 1)(1 + 1/n)ʲ`, the flatness condition holds
  at every index *simultaneously* with `hcompose`, `hphaseBudget`, `hbudget`, a strictly
  positive `varSlack`, and both slack conditions at a strictly positive TV error. `hflat`
  pushes the variance up, which makes both slack thresholds larger — the conditions pull the
  same way. The dimension threshold `n ≥ 82` visible there comes from `hvarSum`+`hbudget`
  (`2m ≤ n·varBudget`), not from `hflat`.
* `Ttc.CV.log_one_add_two_div_le`, `Ttc.CV.sigmaSq_ge_of_flat`, `Ttc.CV.sigmaSq_eq_pow`,
  `Ttc.CV.sigmaSq_zero_gt_of_flat_of_meet`, `Ttc.CV.coolWeight_zero_ge_of_flat` — the
  arithmetic behind the finding above.
* `Ttc.CV.varBudget_param_le`, `Ttc.CV.meet_of_fixedRate_fields`,
  `Ttc.CV.cold_start_mem_relErr_of_fixedRate_fields` — the finding stated over
  `cousinsVempalaOfSamplerFixedRate`'s *own fields* (`hvarSum`, `hvarSlack_nonneg`,
  `hbudget`, `hcompose`, `hrate`, `hflat`), with nothing assumed beyond them.
* `Ttc.CV.sigmaSq_mono_of_rate`, `Ttc.CV.flat_of_rate_of_le` — the general-rate successors
  of `Arlib.GaussianCooling.sigmaSq_mono_of_fixedRate` / `flat_of_fixedRate_of_le`: `hflat`
  need only be checked at `j = m − 1` on any geometric schedule.
* `Ttc.CV.hvar_exact_of_coolRate_all` — the exact-law second moment at **every** phase of
  the annealing schedule, constant `1 + κ/m`. Interior phases are
  `Arlib.GaussianCooling.coolLaw_sq_moment_le_budget`; terminal phases go through
  `Arlib.GaussianCooling.coolLaw_sq_moment_le_terminal` (constant `e^{R²/(2σᵢ²)}`, needing
  only a radius) plus flatness at the matching constant. No `3 ≤ n`.
* `Ttc.CV.cool_flat_slacks_satisfiable`, `Ttc.CV.cool_budgets_at_numbers` — the
  satisfiability check for the annealing construction: a schedule meeting `hflat` at every
  index, cooling by `e^L`, with `varSlack = (V − κ)/m > 0` and both slack conditions at a
  strictly positive TV error; and the arithmetic budgets at `ε = 1`, `innerAcc = 1/2`,
  `meanBias = 1/3`, `varBudget = log(21/20)`, `κ = log(21/20)/2`, `phaseBias = 1/(6m)`.
  **There is no lower bound on `n` here**: the `n ≥ 82` of the fixed-rate check came from
  the constant `1 + 2/n`, which no longer appears.

## Two honesty notes

**Non-vacuity IS established for both hypothesis bundles** (`CLAUDE.md` §11).
`Ttc.VolumeAlgorithm.cousinsVempalaWitness` instantiates every argument of
`cousinsVempala` — `Ω = Unit`, `μ = dirac ()`, one phase, the chain `2Vol(K), Vol(K), …`,
the deterministic score `1/2`, `κ = 0` — and proves all fourteen hypotheses, so the bundle
is satisfiable and the construction is not a statement about nothing.
`Ttc.VolumeAlgorithm.cousinsVempalaBiasedWitness` does the same for
`cousinsVempalaOfBiasedEnd`, with a strictly positive endpoint bias `ε/(2+ε)`. The
ingredient Mathlib does not supply ready-made is `Ttc.CV.iIndepFun_of_subsingleton`:
*every* family of random variables on a one-point probability space is `iIndepFun` (each
conditioning event is null or everything). What the witnesses do **not** certify is that
the paper's Gaussian schedule satisfies the bundle: they are degenerate schedules, and the
estimator they produce is `Ttc.VolumeAlgorithm.exact` in disguise
(`cousinsVempalaWitness_est`).

**`hphase_mean`'s equality idealization has been removed — twice over.**
`Ttc.VolumeAlgorithm.cousinsVempalaOfApproxMean` replaces it by the two-sided relative
bound `∫ W ∈ (1 ± phaseBias)·(chain(i+1)/chain i)`, at the per-phase budget
`2·m·phaseBias ≤ meanBias ε` (`Arlib.GaussianCooling.phaseBias_le`), and carries its own
non-vacuity witness with a *strictly positive* bias
(`Ttc.VolumeAlgorithm.cousinsVempalaApproxMeanWitness`).
`Ttc.VolumeAlgorithm.cousinsVempalaOfSampler` then *derives* that bound from a
total-variation guarantee on the sampler. The *other* idealization, the exact endpoint
`hchain_end`, has been removed too: see `Ttc.CV.G_indicator_mem_relErr` and
`Ttc.VolumeAlgorithm.cousinsVempalaOfBiasedEnd`.

**`cousinsVempalaOfSampler` has no non-vacuity witness, and cannot have a degenerate one.**
Its `hTV` hypothesis, at the TV error its own slack conditions force, *is* the statement
that an exponentially accurate sampler for the Gaussian phase law exists; a one-point or
otherwise degenerate instantiation cannot satisfy it (a `TVLe … 1` bound is free but fails
the slack conditions, since the chain ratio itself is at most `e^{R²/(2σᵢ²)}`). What *is*
machine-checked is that the bundle's arithmetic side is consistent:
`Ttc.CV.exists_pos_tvErr` exhibits a **strictly positive** TV error meeting both slack
conditions at the real radius, the real variance and the real chain ratio. The residual
hypothesis is therefore the sampler itself and nothing else — which is the honest state of
this development, and is flagged rather than papered over.

**No `Prop` introduced here assumes its conclusion.** The two `def`s are constructions of
`Ttc.VolumeAlgorithm`, and every hypothesis they take is a statement about the *inputs*
(scores, chains, schedules), never about the estimate being correct at the accuracy the
conclusion asserts — except `ofRuns`' `hgood`, which asserts correctness at the fixed
confidence `4/5` and is amplified to `1 − p`; that amplification is the theorem, and it
is `median_boost`.
-/

namespace Ttc

open MeasureTheory Set ProbabilityTheory Arlib.GaussianCooling
open scoped ENNReal

namespace CV

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Relative error, as an absolute deviation -/

/-- **`relErr` is a deviation bound.** `x ∈ (1±ε)·b` exactly when `|x − b| ≤ ε·b`. This is
the form Chebyshev's inequality delivers. -/
theorem mem_relErr_iff {ε b x : ℝ} : x ∈ relErr ε b ↔ |x - b| ≤ ε * b := by
  simp only [relErr, Set.mem_Icc, abs_le]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith

/-- **Relative errors compose.** An `ε`-accurate estimate of an `η`-accurate proxy is an
`(ε + η + εη)`-accurate estimate of the truth. Needed to absorb the bias of the telescope's
endpoints (`G_indicator_ge` below) into the accuracy parameter. -/
theorem relErr_trans {ε η b c x : ℝ} (hε : 0 ≤ ε) (_hη : 0 ≤ η) (_hc : 0 ≤ c)
    (hx : x ∈ relErr ε b) (hb : b ∈ relErr η c) :
    x ∈ relErr (ε + η + ε * η) c := by
  simp only [relErr, Set.mem_Icc] at hx hb ⊢
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hb1, hb2⟩ := hb
  constructor <;> nlinarith

/-- **Relative error is monotone in the accuracy.** On a nonnegative target, an estimate
good to `ε₁` is good to any `ε₂ ≥ ε₁`. This is what lets a run computed at an *inner*
accuracy be reported at the requested accuracy once the endpoint bias has been absorbed by
`relErr_trans`. -/
theorem relErr_mono {ε₁ ε₂ b : ℝ} (h : ε₁ ≤ ε₂) (hb : 0 ≤ b) :
    relErr ε₁ b ⊆ relErr ε₂ b := by
  intro x hx
  simp only [relErr, Set.mem_Icc] at hx ⊢
  obtain ⟨h1, h2⟩ := hx
  constructor <;> nlinarith

/-! ## Chebyshev, in relative-error form

The estimator's *relative* second moment is what §5.1 controls, so this is the shape the
tail bound has to take: a bound `E(X²) ≤ c·E(X)²` turns directly into a bound on the
probability of a relative-error failure, with no reference to the scale of `X`. -/

/-- **Chebyshev's inequality for a relative-error target.** If `X` has positive mean and
relative second moment at most `c`, then

  `P(X ∉ (1 ± ε)·E(X)) ≤ (c − 1)/ε²`.

Proof: `Var(X) = E(X²) − E(X)² ≤ (c−1)E(X)²`, and Chebyshev at deviation `ε·E(X)`. -/
theorem measure_notMem_relErr_le [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ)
    {c ε : ℝ} (hε : 0 < ε) (hpos : 0 < ∫ ω, X ω ∂μ)
    (hc : ∫ ω, (X ω) ^ 2 ∂μ ≤ c * (∫ ω, X ω ∂μ) ^ 2) :
    μ {ω | X ω ∉ relErr ε (∫ ω, X ω ∂μ)} ≤ ENNReal.ofReal ((c - 1) / ε ^ 2) := by
  set E : ℝ := ∫ ω, X ω ∂μ with hE
  have hsq : ∫ ω, (X ^ 2) ω ∂μ = ∫ ω, (X ω) ^ 2 ∂μ := by simp
  have hvar : variance X μ ≤ (c - 1) * E ^ 2 := by
    rw [variance_eq_sub hX, hsq, ← hE]
    linarith
  have hsub : {ω | X ω ∉ relErr ε E} ⊆ {ω | ε * E ≤ |X ω - E|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, mem_relErr_iff, not_le] at hω
    exact hω.le
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (meas_ge_le_variance_div_sq hX (by positivity : (0:ℝ) < ε * E)) ?_
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hE2 : (0:ℝ) < E ^ 2 := by positivity
  nlinarith [sq_nonneg ε, sq_nonneg E]

/-! ## The telescoping product

The algorithm's cooling schedule is a chain `A 0, …, A m` of Gaussian integrals
`A i = G(σᵢ²)`, and phase `i` estimates the single ratio `A(i+1)/A(i)`. The product of the
`m` ratios collapses to `A m / A 0`, so multiplying the product estimator by the *known*
`A 0` estimates `A m`. -/

/-- **The telescoping identity**, over `Finset.range`. -/
theorem prod_range_ratio {A : ℕ → ℝ} (hA : ∀ i, A i ≠ 0) (m : ℕ) :
    ∏ i ∈ Finset.range m, A (i + 1) / A i = A m / A 0 := by
  induction m with
  | zero => simp [div_self (hA 0)]
  | succ k ih =>
      have h0 := hA 0
      have hk := hA k
      rw [Finset.prod_range_succ, ih]
      field_simp

/-- **The telescoping identity**, indexed by `Fin m` — the form the product estimator of
`Arlib.GaussianCooling.prod_sq_div_le_exp` is written in. -/
theorem prod_fin_ratio {A : ℕ → ℝ} (hA : ∀ i, A i ≠ 0) (m : ℕ) :
    ∏ i : Fin m, A ((i : ℕ) + 1) / A (i : ℕ) = A m / A 0 := by
  rw [Fin.prod_univ_eq_prod_range (fun i => A (i + 1) / A i) m]
  exact prod_range_ratio hA m

/-! ## The product estimator's accuracy

`Arlib.GaussianCooling.prod_sq_div_le_exp` says a per-phase relative second moment
`1 + κ/m` gives the *product* a relative second moment at most `e^κ`, uniformly in `m`.
Feeding that into `measure_notMem_relErr_le` is §5.2's accuracy statement for one run. -/

/-- **The product estimator lands within `(1 ± ε)` of its mean with probability
`1 − (e^κ − 1)/ε²`.**

The bound does not degrade with the number of phases: that is the whole point of the
`1 + κ/m` per-phase budget. No measurability of the good event is needed — the two
complementary events are bounded against each other by subadditivity. -/
theorem prod_relErr_ge [IsProbabilityMeasure μ] {m : ℕ} {W : Fin m → Ω → ℝ} {κ ε : ℝ}
    (hκ : 0 ≤ κ) (hε : 0 < ε) (hindep : iIndepFun W μ)
    (hmeas : ∀ i, AEStronglyMeasurable (W i) μ)
    (hprod : MemLp (fun ω => ∏ i, W i ω) 2 μ)
    (hvar : ∀ i, ∫ ω, (W i ω) ^ 2 ∂μ ≤ (1 + κ / m) * (∫ ω, W i ω ∂μ) ^ 2)
    (hpos : 0 < ∫ ω, ∏ i, W i ω ∂μ) :
    1 - (Real.exp κ - 1) / ε ^ 2
      ≤ μ.real {ω | (∏ i, W i ω) ∈ relErr ε (∫ ω, ∏ i, W i ω ∂μ)} := by
  have hcard : Fintype.card (Fin m) = m := Fintype.card_fin m
  have hvar' : ∀ i, ∫ ω, (W i ω) ^ 2 ∂μ
      ≤ (1 + κ / Fintype.card (Fin m)) * (∫ ω, W i ω ∂μ) ^ 2 := by
    rw [hcard]; exact hvar
  have hsq : ∫ ω, (∏ i, W i ω) ^ 2 ∂μ ≤ Real.exp κ * (∫ ω, ∏ i, W i ω ∂μ) ^ 2 :=
    prod_sq_div_le_exp hκ hindep hmeas hvar'
  have hbad := measure_notMem_relErr_le (μ := μ) (X := fun ω => ∏ i, W i ω) hprod hε hpos hsq
  -- transfer to reals
  have hnn : (0:ℝ) ≤ (Real.exp κ - 1) / ε ^ 2 := by
    have : (1:ℝ) ≤ Real.exp κ := Real.one_le_exp hκ
    positivity
  set G : Set Ω := {ω | (∏ i, W i ω) ∈ relErr ε (∫ ω, ∏ i, W i ω ∂μ)} with hG
  set B : Set Ω := {ω | (∏ i, W i ω) ∉ relErr ε (∫ ω, ∏ i, W i ω ∂μ)} with hB
  have hbadR : μ.real B ≤ (Real.exp κ - 1) / ε ^ 2 := by
    rw [measureReal_def]
    refine le_trans (ENNReal.toReal_mono (by finiteness) hbad) ?_
    rw [ENNReal.toReal_ofReal hnn]
  have hcov : (1:ℝ) ≤ μ.real G + μ.real B := by
    have hsub : (Set.univ : Set Ω) ⊆ G ∪ B := by
      intro ω _
      by_cases h : (∏ i, W i ω) ∈ relErr ε (∫ ω, ∏ i, W i ω ∂μ)
      · exact Or.inl h
      · exact Or.inr h
    have h1 : μ Set.univ ≤ μ G + μ B :=
      le_trans (measure_mono hsub) (measure_union_le _ _)
    have h2 : (μ Set.univ).toReal ≤ (μ G + μ B).toReal :=
      ENNReal.toReal_mono (by finiteness) h1
    rw [measure_univ, ENNReal.toReal_one,
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h2
    exact h2
  linarith

/-! ## One run of the algorithm

The run's output is `A 0 · ∏ᵢ Wᵢ`, with `A 0` the deterministic cold-start value. Its
mean is `A 0 · (A m / A 0) = A m`, and relative error is scale invariant
(`Ttc.mem_relErr_smul`), so the accuracy statement transfers unchanged. -/

/-- **One run of the Gaussian-cooling estimator.** With `A` the cooling chain, `Wᵢ` an
unbiased estimator of the ratio `A(i+1)/A(i)` with relative second moment `1 + κ/m`, and
the `m` phases independent, the output `A 0 · ∏ Wᵢ` lies within `(1 ± ε)` of `A m` with
probability at least `1 − (e^κ − 1)/ε²`. -/
theorem run_relErr_ge [IsProbabilityMeasure μ] {m : ℕ} {W : Fin m → Ω → ℝ} {A : ℕ → ℝ}
    {κ ε : ℝ} (hκ : 0 ≤ κ) (hε : 0 < ε) (hindep : iIndepFun W μ)
    (hmeas : ∀ i, AEStronglyMeasurable (W i) μ)
    (hprod : MemLp (fun ω => ∏ i, W i ω) 2 μ)
    (hApos : ∀ i, 0 < A i)
    (hmean : ∀ i : Fin m, ∫ ω, W i ω ∂μ = A ((i : ℕ) + 1) / A (i : ℕ))
    (hvar : ∀ i, ∫ ω, (W i ω) ^ 2 ∂μ ≤ (1 + κ / m) * (∫ ω, W i ω ∂μ) ^ 2) :
    1 - (Real.exp κ - 1) / ε ^ 2
      ≤ μ.real {ω | A 0 * ∏ i, W i ω ∈ relErr ε (A m)} := by
  have hAne : ∀ i, A i ≠ 0 := fun i => ne_of_gt (hApos i)
  have hEprod : ∫ ω, ∏ i, W i ω ∂μ = A m / A 0 := by
    rw [integral_prod_eq_prod_integral' hindep hmeas]
    calc ∏ i : Fin m, ∫ ω, W i ω ∂μ
        = ∏ i : Fin m, A ((i : ℕ) + 1) / A (i : ℕ) := Finset.prod_congr rfl fun i _ => hmean i
      _ = A m / A 0 := prod_fin_ratio hAne m
  have hpos : 0 < ∫ ω, ∏ i, W i ω ∂μ := by
    rw [hEprod]; exact div_pos (hApos m) (hApos 0)
  have hmain := prod_relErr_ge hκ hε hindep hmeas hprod hvar hpos
  have hcancel : A 0 * (A m / A 0) = A m := by
    rw [mul_comm, div_mul_cancel₀ _ (hAne 0)]
  have hset : {ω | A 0 * ∏ i, W i ω ∈ relErr ε (A m)}
      = {ω | (∏ i, W i ω) ∈ relErr ε (∫ ω, ∏ i, W i ω ∂μ)} := by
    ext ω
    simp only [Set.mem_setOf_eq, hEprod]
    have hiff := mem_relErr_smul (ε := ε) (b := A m / A 0) (y := ∏ i, W i ω) (hApos 0)
    rwa [hcancel] at hiff
  rw [hset]
  exact hmain

/-- **The paper's constant-confidence form.** A per-run variance budget of
`e^κ − 1 ≤ ε²/5` puts the success probability of one run at `4/5`, the value the median
boost is applied at. -/
theorem run_relErr_four_fifths [IsProbabilityMeasure μ] {m : ℕ} {W : Fin m → Ω → ℝ}
    {A : ℕ → ℝ} {κ ε : ℝ} (hκ : 0 ≤ κ) (hε : 0 < ε) (hindep : iIndepFun W μ)
    (hmeas : ∀ i, AEStronglyMeasurable (W i) μ)
    (hprod : MemLp (fun ω => ∏ i, W i ω) 2 μ)
    (hApos : ∀ i, 0 < A i)
    (hmean : ∀ i : Fin m, ∫ ω, W i ω ∂μ = A ((i : ℕ) + 1) / A (i : ℕ))
    (hvar : ∀ i, ∫ ω, (W i ω) ^ 2 ∂μ ≤ (1 + κ / m) * (∫ ω, W i ω ∂μ) ^ 2)
    (hbudget : Real.exp κ - 1 ≤ ε ^ 2 / 5) :
    4 / 5 ≤ μ.real {ω | A 0 * ∏ i, W i ω ∈ relErr ε (A m)} := by
  have hmain := run_relErr_ge hκ hε hindep hmeas hprod hApos hmean hvar
  have hstep : (Real.exp κ - 1) / ε ^ 2 ≤ 1 / 5 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  linarith

/-! ## The median boost, at a relative-error target

`Arlib.GaussianCooling.median_boost` is stated for an arbitrary interval `Icc L U`;
`relErr ε b` *is* such an interval, so the specialization is immediate. The repetition
count is `O(log (1/p))` — the exponential (Hoeffding) rate, not the Chebyshev one. -/

/-- **The `4/5 → 1 − p` amplification.** The median of `r` independent runs, each correct
to relative error `ε` with probability `4/5`, is correct to relative error `ε` with
probability `1 − p`, provided

  `r ≥ log (1/p) / (2 (4/5 − 1/2)²) = (50/9)·log (1/p)`. -/
theorem median_relErr_ge [IsProbabilityMeasure μ] {r : ℕ} (hr : 0 < r)
    {v : Fin r → Ω → ℝ} {z : Ω → ℝ} {ε b p : ℝ}
    (hv : ∀ i, Measurable (v i)) (hindep : iIndepFun v μ)
    (hmed : ∀ ω, IsMedian (fun i => v i ω) (z ω))
    (hq : ∀ i, 4 / 5 ≤ μ.real {ω | v i ω ∈ relErr ε b})
    (hp : 0 < p)
    (hrp : Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2) ≤ (r : ℝ)) :
    1 - p ≤ μ.real {ω | z ω ∈ relErr ε b} :=
  median_boost hr hv hindep hmed hq (by norm_num) hp hrp

/-! ## The hot end of the telescope

The last Gaussian of the cooling schedule is supposed to *be* the volume. It is not, quite:
`G(s) = ∫_K e^{−‖x‖²/(2s)}` is always below `Vol(K)`, and above it by the factor
`e^{−R²/(2s)}` once `K ⊆ R·Bₙ`. Both bounds are proved here. They are the piece of
`lem:accuracy` that `Ttc.VolumeAlgorithm.cousinsVempala`'s `hchain_end` idealizes to an
equality; combining them with `Ttc.CV.relErr_trans` is what would remove that
idealization. -/

section HotEnd

variable {n : ℕ}

/-- The Gaussian weight against an indicator is the indicator of the Gaussian weight. -/
theorem gW_indicator (K : Set (Space n)) (s : ℝ) (x : Space n) :
    gW (Set.indicator K (1 : Space n → ℝ)) s x
      = Set.indicator K (fun y => Real.exp (-(‖y‖ ^ 2) / (2 * s))) x := by
  by_cases hx : x ∈ K <;>
    simp [gW, Set.indicator_of_mem, Set.indicator_of_notMem, hx]

/-- `G` of an indicator is the Gaussian integral over the body. -/
theorem G_indicator_eq (K : Set (Space n)) (hKm : MeasurableSet K) (s : ℝ) :
    G (Set.indicator K (1 : Space n → ℝ)) s
      = ∫ x in K, Real.exp (-(‖x‖ ^ 2) / (2 * s)) := by
  simp only [G]
  rw [show (fun x => gW (Set.indicator K (1 : Space n → ℝ)) s x)
      = Set.indicator K (fun y => Real.exp (-(‖y‖ ^ 2) / (2 * s))) from
    funext (gW_indicator K s)]
  exact integral_indicator hKm

/-- The Gaussian weight's exponent is nonpositive. -/
theorem gaussExponent_nonpos {s : ℝ} (hs : 0 < s) (x : Space n) :
    -(‖x‖ ^ 2) / (2 * s) ≤ 0 := by
  rw [div_le_iff₀ (by linarith : (0:ℝ) < 2 * s)]
  nlinarith [sq_nonneg ‖x‖]

/-- A constant is integrable on a body of finite volume. -/
theorem integrableOn_const' {K : Set (Space n)} (hfin : volume K ≠ ⊤) (c : ℝ) :
    IntegrableOn (fun _ : Space n => c) K volume := by
  refine Measure.integrableOn_of_bounded (M := ‖c‖) hfin aestronglyMeasurable_const ?_
  filter_upwards with x using le_rfl

/-- The Gaussian weight is integrable on a body of finite volume: it is bounded by `1`. -/
theorem integrableOn_gaussWeight {K : Set (Space n)} (hfin : volume K ≠ ⊤) {s : ℝ}
    (hs : 0 < s) :
    IntegrableOn (fun x : Space n => Real.exp (-(‖x‖ ^ 2) / (2 * s))) K volume := by
  have hcont : Continuous fun x : Space n => Real.exp (-(‖x‖ ^ 2) / (2 * s)) := by fun_prop
  refine Measure.integrableOn_of_bounded (M := 1) hfin hcont.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (gaussExponent_nonpos hs x)

/-- **The hot end, upper half.** `G(s) ≤ Vol(K)`: the Gaussian weight never exceeds `1`. -/
theorem G_indicator_le {K : Set (Space n)} (hKm : MeasurableSet K) (hfin : volume K ≠ ⊤)
    {s : ℝ} (hs : 0 < s) :
    G (Set.indicator K (1 : Space n → ℝ)) s ≤ (volume K).toReal := by
  rw [G_indicator_eq K hKm]
  have hle : ∫ x in K, Real.exp (-(‖x‖ ^ 2) / (2 * s)) ≤ ∫ _x in K, (1 : ℝ) :=
    setIntegral_mono_on (integrableOn_gaussWeight hfin hs) (integrableOn_const' hfin 1) hKm
      (fun x _ => Real.exp_le_one_iff.mpr (gaussExponent_nonpos hs x))
  have hconst : ∫ _x in K, (1 : ℝ) = (volume K).toReal := by
    rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  linarith [hle, hconst.le, hconst.ge]

/-- **The hot end, lower half.** For `K ⊆ R·Bₙ`, `e^{−R²/(2s)}·Vol(K) ≤ G(s)`: on a
bounded body the Gaussian weight is bounded below by its value at the far end. Together
with `G_indicator_le` this pins the last Gaussian of the schedule to `Vol(K)` within a
factor that `s → ∞` drives to `1`. -/
theorem G_indicator_ge {K : Set (Space n)} (hKm : MeasurableSet K) (hfin : volume K ≠ ⊤)
    {s R : ℝ} (hs : 0 < s) (hR : K ⊆ Metric.closedBall (0 : Space n) R) :
    Real.exp (-(R ^ 2) / (2 * s)) * (volume K).toReal
      ≤ G (Set.indicator K (1 : Space n → ℝ)) s := by
  rw [G_indicator_eq K hKm]
  have h2s : (0:ℝ) < 2 * s := by linarith
  have hpt : ∀ x ∈ K, Real.exp (-(R ^ 2) / (2 * s)) ≤ Real.exp (-(‖x‖ ^ 2) / (2 * s)) := by
    intro x hx
    have hxR : ‖x‖ ≤ R := by
      have := hR hx
      rwa [mem_closedBall_zero_iff] at this
    have hsq : ‖x‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg x]
    refine Real.exp_le_exp.mpr ?_
    rw [div_le_div_iff₀ h2s h2s]
    nlinarith
  have hle : ∫ _x in K, Real.exp (-(R ^ 2) / (2 * s))
      ≤ ∫ x in K, Real.exp (-(‖x‖ ^ 2) / (2 * s)) :=
    setIntegral_mono_on (integrableOn_const' hfin _) (integrableOn_gaussWeight hfin hs)
      hKm hpt
  have hconst : ∫ _x in K, Real.exp (-(R ^ 2) / (2 * s))
      = Real.exp (-(R ^ 2) / (2 * s)) * (volume K).toReal := by
    rw [setIntegral_const, smul_eq_mul, measureReal_def, mul_comm]
  linarith [hle, hconst.le, hconst.ge]

/-- **The hot end, as a relative error — the honest form of `hchain_end`.**

For a convex body `K ⊆ R·Bₙ` and any variance `s > 0`, the last Gaussian of the cooling
schedule is a *relatively accurate* proxy for the volume:

  `G(s) ∈ (1 ± (1 − e^{−R²/(2s)}))·Vol(K)`.

This is `G_indicator_ge` (lower half) and `G_indicator_le` (upper half) packaged into the
one statement the rest of §5.2 consumes, via `Ttc.CV.relErr_trans`. The bias
`η(s) = 1 − e^{−R²/(2s)}` is what `Ttc.VolumeAlgorithm.cousinsVempala`'s `hchain_end`
idealizes to `0`; it tends to `0` as `s → ∞`, so any target bias is reachable by taking
the last Gaussian flat enough. `Ttc.VolumeAlgorithm.cousinsVempalaOfBiasedEnd` is the
construction that takes this statement instead of the equality. -/
theorem G_indicator_mem_relErr {K : Set (Space n)} (hKm : MeasurableSet K)
    (hfin : volume K ≠ ⊤) {s R : ℝ} (hs : 0 < s)
    (hR : K ⊆ Metric.closedBall (0 : Space n) R) :
    G (Set.indicator K (1 : Space n → ℝ)) s
      ∈ relErr (1 - Real.exp (-(R ^ 2) / (2 * s))) (volume K).toReal := by
  have hb : (0:ℝ) ≤ (volume K).toReal := ENNReal.toReal_nonneg
  have hexp_le : Real.exp (-(R ^ 2) / (2 * s)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < 2 * s)]
      nlinarith [sq_nonneg R])
  have hlo := G_indicator_ge hKm hfin hs hR
  have hhi := G_indicator_le hKm hfin hs
  simp only [relErr, Set.mem_Icc]
  constructor
  · have : (1 - (1 - Real.exp (-(R ^ 2) / (2 * s)))) * (volume K).toReal
        = Real.exp (-(R ^ 2) / (2 * s)) * (volume K).toReal := by ring
    rw [this]; exact hlo
  · nlinarith

end HotEnd

/-! ## §5.2 assembled: telescope + Chebyshev + median boost, in one statement -/

/-- **Cousins–Vempala §5.2, assembled.** The Gaussian-cooling estimator returns a value
within relative error `ε` of `Vol(K)` with probability at least `1 − δ`.

The estimator is the median `z` of `r` independent runs, each run being the cold-start
value `chain 0` times the product of the `m` per-phase ratio estimators `W j i`. The
hypotheses are, in order:

* `hbudget` — the per-phase variance budget `κ`, chosen so that `e^κ − 1 ≤ ε²/5`; this is
  what makes a single run correct with probability `4/5` (`run_relErr_four_fifths`);
* `hrδ` — the `O(log 1/δ)` repetition count of the median boost;
* `hchain_end` — the last Gaussian of the cooling schedule integrates to `Vol(K)`;
* `hmean` — each phase's score is an unbiased estimator of the ratio
  `chain (i+1) / chain i` of consecutive Gaussian integrals. **This is the sampler**, and
  it is the hypothesis this development cannot yet discharge: it requires sampling from
  the density `∝ e^{−‖x‖²/(2σᵢ²)}` restricted to `K`, hence a mixing bound for the ball
  walk, hence the isoperimetric inequality for logconcave densities — which is not proved
  anywhere here;
* `hvar` — each phase's score has relative second moment `1 + κ/m`. This is §5.1, which
  *is* proved: `Arlib.GaussianCooling.fixed_var_bound_ratio_indicator` gives exactly
  `E(Y²)/E(Y)² ≤ 1 + 2/n` for the indicator of a convex body with nothing assumed. It is
  stated here at the level of the score's moments because the identification of those
  moments with `G`-ratios again goes through the sampler;
* `hphase_indep`, `hrun_indep`, `hprod`, `hW_meas`, `hmed` — independence, integrability
  and measurability guards. -/
theorem gaussianCooling_accuracy [IsProbabilityMeasure μ] {n m r : ℕ} {K : Set (Space n)}
    {chain : ℕ → ℝ} {W : Fin r → Fin m → Ω → ℝ} {z : Ω → ℝ} {κ ε δ : ℝ}
    (hκ : 0 ≤ κ) (hε : 0 < ε) (hδ : 0 < δ) (hr : 0 < r)
    (hbudget : Real.exp κ - 1 ≤ ε ^ 2 / 5)
    (hrδ : Real.log (1 / δ) / (2 * (4 / 5 - 1 / 2) ^ 2) ≤ (r : ℝ))
    (hW_meas : ∀ j i, Measurable (W j i))
    (hprod : ∀ j, MemLp (fun ω => ∏ i, W j i ω) 2 μ)
    (hphase_indep : ∀ j, iIndepFun (W j) μ)
    (hrun_indep : iIndepFun (fun (j : Fin r) (ω : Ω) => chain 0 * ∏ i, W j i ω) μ)
    (hmed : ∀ ω, IsMedian (fun j => chain 0 * ∏ i, W j i ω) (z ω))
    (hchain_pos : ∀ i, 0 < chain i)
    (hchain_end : chain m = (volume K).toReal)
    (hmean : ∀ j (i : Fin m), ∫ ω, W j i ω ∂μ = chain ((i : ℕ) + 1) / chain (i : ℕ))
    (hvar : ∀ j (i : Fin m),
      ∫ ω, (W j i ω) ^ 2 ∂μ ≤ (1 + κ / m) * (∫ ω, W j i ω ∂μ) ^ 2) :
    1 - δ ≤ μ.real {ω | z ω ∈ relErr ε (volume K).toReal} := by
  have hrunmeas : ∀ j : Fin r, Measurable (fun ω => chain 0 * ∏ i, W j i ω) := fun j =>
    measurable_const.mul (Finset.measurable_prod _ fun i _ => hW_meas j i)
  have hgood : ∀ j : Fin r,
      4 / 5 ≤ μ.real {ω | chain 0 * ∏ i, W j i ω ∈ relErr ε (volume K).toReal} := by
    intro j
    have h := run_relErr_four_fifths (μ := μ) (W := W j) (A := chain) (κ := κ) (ε := ε)
      hκ hε (hphase_indep j) (fun i => (hW_meas j i).aestronglyMeasurable) (hprod j)
      hchain_pos (hmean j) (hvar j) hbudget
    rwa [hchain_end] at h
  exact median_relErr_ge hr hrunmeas hrun_indep hmed hgood hδ hrδ

/-! ## §5.2 with a *biased* endpoint — removing the `hchain_end` idealization

The cooling schedule's last Gaussian is not the volume: `G_indicator_mem_relErr` says it is
the volume up to a relative bias `η`. The statements above are all phrased against the
chain's own endpoint `A m`, so composing them with that bias is exactly one application of
`relErr_trans`, at the cost of degrading the accuracy from `ε` to `ε + η + εη`. Everything
below is the same mathematics as above with that composition performed; nothing new is
assumed. -/

/-- **One run, with a biased endpoint.** If the chain's endpoint `A m` is only within a
relative `η` of the true target `b`, a run that is `ε`-accurate for `A m` is
`(ε + η + εη)`-accurate for `b` — hence `ε₀`-accurate for any `ε₀ ≥ ε + η + εη`.

Taking `η = 0` and `ε₀ = ε` recovers `run_relErr_four_fifths` (with `A m = b`); taking
`b = Vol(K)` and `η = 1 − e^{−R²/(2σ_m²)}` is `G_indicator_mem_relErr`, i.e. the real
Cousins–Vempala endpoint. -/
theorem run_relErr_four_fifths_biasedEnd [IsProbabilityMeasure μ] {m : ℕ} {W : Fin m → Ω → ℝ}
    {A : ℕ → ℝ} {κ ε ε₀ η b : ℝ} (hκ : 0 ≤ κ) (hε : 0 < ε) (hη : 0 ≤ η) (hb : 0 ≤ b)
    (hindep : iIndepFun W μ)
    (hmeas : ∀ i, AEStronglyMeasurable (W i) μ)
    (hprod : MemLp (fun ω => ∏ i, W i ω) 2 μ)
    (hApos : ∀ i, 0 < A i)
    (hmean : ∀ i : Fin m, ∫ ω, W i ω ∂μ = A ((i : ℕ) + 1) / A (i : ℕ))
    (hvar : ∀ i, ∫ ω, (W i ω) ^ 2 ∂μ ≤ (1 + κ / m) * (∫ ω, W i ω ∂μ) ^ 2)
    (hbudget : Real.exp κ - 1 ≤ ε ^ 2 / 5)
    (hend : A m ∈ relErr η b)
    (hcomp : ε + η + ε * η ≤ ε₀) :
    4 / 5 ≤ μ.real {ω | A 0 * ∏ i, W i ω ∈ relErr ε₀ b} := by
  have h := run_relErr_four_fifths hκ hε hindep hmeas hprod hApos hmean hvar hbudget
  have hsub : {ω | A 0 * ∏ i, W i ω ∈ relErr ε (A m)}
      ⊆ {ω | A 0 * ∏ i, W i ω ∈ relErr ε₀ b} := fun ω hω =>
    relErr_mono hcomp hb (relErr_trans hε.le hη hb hω hend)
  exact le_trans h (measureReal_mono hsub)

/-- **Cousins–Vempala §5.2 with the real endpoint.** Identical to
`gaussianCooling_accuracy` except that the last Gaussian of the schedule is only assumed
to be within a relative `η` of `Vol(K)` — which is what `G_indicator_mem_relErr` proves,
with `η = 1 − e^{−R²/(2σ_m²)}` for a body inside `R·Bₙ` — and the conclusion is
correspondingly at accuracy `ε + η + εη` rather than `ε`.

This is the statement `hchain_end` was idealizing. It is *not* blocked on the sampler:
`hmean` still is. -/
theorem gaussianCooling_accuracy_biasedEnd [IsProbabilityMeasure μ] {n m r : ℕ}
    {K : Set (Space n)} {chain : ℕ → ℝ} {W : Fin r → Fin m → Ω → ℝ} {z : Ω → ℝ}
    {κ ε δ η : ℝ}
    (hκ : 0 ≤ κ) (hε : 0 < ε) (hδ : 0 < δ) (hr : 0 < r) (hη : 0 ≤ η)
    (hbudget : Real.exp κ - 1 ≤ ε ^ 2 / 5)
    (hrδ : Real.log (1 / δ) / (2 * (4 / 5 - 1 / 2) ^ 2) ≤ (r : ℝ))
    (hW_meas : ∀ j i, Measurable (W j i))
    (hprod : ∀ j, MemLp (fun ω => ∏ i, W j i ω) 2 μ)
    (hphase_indep : ∀ j, iIndepFun (W j) μ)
    (hrun_indep : iIndepFun (fun (j : Fin r) (ω : Ω) => chain 0 * ∏ i, W j i ω) μ)
    (hmed : ∀ ω, IsMedian (fun j => chain 0 * ∏ i, W j i ω) (z ω))
    (hchain_pos : ∀ i, 0 < chain i)
    (hchain_end : chain m ∈ relErr η (volume K).toReal)
    (hmean : ∀ j (i : Fin m), ∫ ω, W j i ω ∂μ = chain ((i : ℕ) + 1) / chain (i : ℕ))
    (hvar : ∀ j (i : Fin m),
      ∫ ω, (W j i ω) ^ 2 ∂μ ≤ (1 + κ / m) * (∫ ω, W j i ω ∂μ) ^ 2) :
    1 - δ ≤ μ.real {ω | z ω ∈ relErr (ε + η + ε * η) (volume K).toReal} := by
  have hrunmeas : ∀ j : Fin r, Measurable (fun ω => chain 0 * ∏ i, W j i ω) := fun j =>
    measurable_const.mul (Finset.measurable_prod _ fun i _ => hW_meas j i)
  have hgood : ∀ j : Fin r, 4 / 5 ≤
      μ.real {ω | chain 0 * ∏ i, W j i ω ∈ relErr (ε + η + ε * η) (volume K).toReal} :=
    fun j => run_relErr_four_fifths_biasedEnd (μ := μ) (W := W j) (A := chain) (κ := κ)
      (ε := ε) hκ hε hη ENNReal.toReal_nonneg (hphase_indep j)
      (fun i => (hW_meas j i).aestronglyMeasurable) (hprod j) hchain_pos (hmean j) (hvar j)
      hbudget hchain_end le_rfl
  exact median_relErr_ge hr hrunmeas hrun_indep hmed hgood hδ hrδ

/-! ## §5.2 with an *approximately unbiased* phase estimator

The remaining idealization of `run_relErr_four_fifths` is `hmean`: it asks for
`∫ W i dμ = A (i+1)/A i` **exactly**. No sampler supplies that — a chain run for finitely
many steps is at positive total-variation distance from its target, so its score's mean is
off by a corresponding amount.

`Arlib.GaussianCooling.integral_prod_mem_relErr_of_budget` is the replacement: per-phase
relative bias `η` with `2mη ≤ τ ≤ 1` gives the telescoped product a relative bias `τ`
around `A m / A 0`. Composing that with the Chebyshev step through `relErr_trans` is the
only work below; the arithmetic budget is `ε + τ + ε·τ ≤ ε₀`. -/

/-- **One run, with approximately unbiased phase estimators.** Each phase's score is only
required to have mean within a relative `η` of the chain ratio `A(i+1)/A(i)`, with the
per-phase budget `2mη ≤ τ` and `τ < 1`. The run's output is then `ε₀`-accurate for `A m`
with probability `4/5`, for any `ε₀ ≥ ε + τ + ε·τ`.

Taking `η = τ = 0` and `ε₀ = ε` recovers `run_relErr_four_fifths`. -/
theorem run_relErr_four_fifths_approxMean [IsProbabilityMeasure μ] {m : ℕ}
    {W : Fin m → Ω → ℝ} {A : ℕ → ℝ} {κ ε ε₀ η τ : ℝ}
    (hm : 0 < m) (hκ : 0 ≤ κ) (hε : 0 < ε) (hη : 0 ≤ η) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hmeanBudget : 2 * (m : ℝ) * η ≤ τ)
    (hindep : iIndepFun W μ)
    (hmeas : ∀ i, AEStronglyMeasurable (W i) μ)
    (hprod : MemLp (fun ω => ∏ i, W i ω) 2 μ)
    (hApos : ∀ i, 0 < A i)
    (hmean : ∀ i : Fin m, ∫ ω, W i ω ∂μ ∈ relErr η (A ((i : ℕ) + 1) / A (i : ℕ)))
    (hvar : ∀ i, ∫ ω, (W i ω) ^ 2 ∂μ ≤ (1 + κ / m) * (∫ ω, W i ω ∂μ) ^ 2)
    (hbudget : Real.exp κ - 1 ≤ ε ^ 2 / 5)
    (hcompose : ε + τ + ε * τ ≤ ε₀) :
    4 / 5 ≤ μ.real {ω | A 0 * ∏ i, W i ω ∈ relErr ε₀ (A m)} := by
  have hR : 0 < A m / A 0 := div_pos (hApos m) (hApos 0)
  have hmeanProd : ∫ ω, ∏ i, W i ω ∂μ ∈ relErr τ (A m / A 0) :=
    integral_prod_mem_relErr_of_budget hm hη hτ1.le hmeanBudget hindep hmeas hApos hmean
  have hpos : 0 < ∫ ω, ∏ i, W i ω ∂μ := integral_prod_pos hτ1 hR hmeanProd
  have hmain := prod_relErr_ge hκ hε hindep hmeas hprod hvar hpos
  have hstep : (Real.exp κ - 1) / ε ^ 2 ≤ 1 / 5 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hsub : {ω | (∏ i, W i ω) ∈ relErr ε (∫ ω, ∏ i, W i ω ∂μ)}
      ⊆ {ω | A 0 * ∏ i, W i ω ∈ relErr ε₀ (A m)} := by
    intro ω hω
    have h2 : (∏ i, W i ω) ∈ relErr ε₀ (A m / A 0) :=
      relErr_mono hcompose hR.le (relErr_trans hε.le hτ0 hR.le hω hmeanProd)
    have h3 := (mem_relErr_smul (ε := ε₀) (b := A m / A 0) (y := ∏ i, W i ω) (hApos 0)).mpr h2
    rwa [mul_comm (A 0), div_mul_cancel₀ _ (hApos 0).ne'] at h3
  have := measureReal_mono (μ := μ) hsub
  linarith [hmain, this]

/-! ## The radius, the measurable core, and the sampler's guarantee

Three ingredients are needed before the two sampler hypotheses of `cousinsVempala` can be
*derived* rather than assumed.

**A radius.** `Ttc.VolumeAlgorithm.correct` quantifies over every convex `K` with
`ball 0 1 ⊆ K` and `volume K ≠ ⊤`, and exposes no enclosing radius. One is needed: the
phase score `Arlib.GaussianCooling.coolRatio` is `e^{‖x‖²/2·(1/σᵢ² − 1/σᵢ₊₁²)}`, which is
*unbounded on an unbounded body*, and every total-variation transport needs a bound `B` on
the observable. `Arlib.Convexity.exists_closedBall_superset_of_convex` supplies one from
exactly `cousinsVempala`'s own hypotheses, and `cvRadius` names it.

**A measurable core.** A convex set need *not* be Borel measurable: the union of an open
ball with an arbitrary subset of its bounding sphere is convex, and such a subset need not
be Borel. So a hypothesis `∀ K, Convex ℝ K → … → MeasurableSet K` would be **false**, and a
construction carrying it would be vacuous. `interior K` is the fix: it is open (hence
measurable), convex, contains the unit ball whenever `K` does, and has the *same volume* as
`K` because a convex set's frontier is Haar-null (`Convex.addHaar_frontier`). Everything
below runs on `interior K` and reports about `volume K`; `volume_interior_eq` is the bridge.

**The sampler's guarantee.** A `TVLe` bound between the law of the phase sample and the
exact phase law `Arlib.GaussianCooling.coolLaw`. This is an *input*: nothing here asserts
that any ball walk achieves it. -/

section Sampler

variable {n : ℕ}

/-- **A convex set has the volume of its interior.** The frontier of a convex set is
Haar-null (`Convex.addHaar_frontier`) and `closure K ⊆ interior K ∪ frontier K`, so the
three sets `interior K ⊆ K ⊆ closure K` all have the same volume.

This is what lets the whole Gaussian-cooling pipeline run on the open — hence *measurable*
— body `interior K` while still reporting about `volume K`. Without it one would need
`MeasurableSet K`, which does not follow from convexity. -/
theorem volume_interior_eq {K : Set (Space n)} (hK : Convex ℝ K) :
    volume (interior K) = volume K := by
  refine le_antisymm (measure_mono interior_subset) ?_
  have hsub : closure K ⊆ interior K ∪ frontier K := by
    intro x hx
    by_cases h : x ∈ interior K
    · exact Or.inl h
    · exact Or.inr ⟨hx, h⟩
  have h2 : volume (closure K) ≤ volume (interior K) + volume (frontier K) :=
    le_trans (measure_mono hsub) (measure_union_le _ _)
  rw [Convex.addHaar_frontier volume hK, add_zero] at h2
  exact le_trans (measure_mono subset_closure) h2

/-- `interior K` inherits everything the cooling chain needs. -/
theorem volume_interior_ne_top {K : Set (Space n)} (hfin : volume K ≠ ⊤) :
    volume (interior K) ≠ ⊤ :=
  ne_of_lt (lt_of_le_of_lt (measure_mono interior_subset) (lt_top_iff_ne_top.mpr hfin))

theorem ball_subset_interior {K : Set (Space n)}
    (hball : Metric.ball (0 : Space n) 1 ⊆ K) :
    Metric.ball (0 : Space n) 1 ⊆ interior K :=
  interior_maximal hball Metric.isOpen_ball

/-- **The enclosing radius `cousinsVempala` does not carry**, in closed form:
`max 1 (2·Vol(K)/Vol(B(0,½)))`. For a convex body containing the unit ball and of finite
volume this really does enclose `K` (`subset_closedBall_cvRadius`, which is
`Arlib.Convexity.norm_le_of_mem_of_convex`: an unbounded convex set containing a ball has
infinite volume). It is `≥ 1 > 0` for *every* set, with no hypotheses.

It is exponentially bad in the dimension in the worst case — `Vol(B(0,½)) = 2⁻ⁿ Vol(B₁)` —
and that is the honest size of the radius the transport's bound `B = e^{R²/(2σᵢ²)}` is
computed from. -/
noncomputable def cvRadius (K : Set (Space n)) : ℝ :=
  max 1 (2 * (volume K).toReal
    / (volume (Metric.ball (0 : Space n) (1 / 2))).toReal)

theorem one_le_cvRadius (K : Set (Space n)) : 1 ≤ cvRadius K := le_max_left _ _

theorem cvRadius_pos (K : Set (Space n)) : 0 < cvRadius K :=
  lt_of_lt_of_le one_pos (one_le_cvRadius K)

/-- **The radius hypothesis is satisfiable**, from `cousinsVempala`'s own hypotheses on `K`
and nothing else. -/
theorem subset_closedBall_cvRadius {K : Set (Space n)} (hK : Convex ℝ K)
    (hball : Metric.ball (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤) :
    K ⊆ Metric.closedBall (0 : Space n) (cvRadius K) := fun x hx => by
  rw [mem_closedBall_zero_iff]
  exact le_trans (Arlib.Convexity.norm_le_of_mem_of_convex hK hball hfin hx)
    (le_max_right _ _)

/-- **The sampler's guarantee, transported to a relative bias on a phase mean.** If the law
of the sample `X` is within total variation `e` of the intended law `ν`, the score `f` takes
values in `[0, B]`, and `∫ f dν = r`, then the *realised* mean `∫ f(X) dμ` is within a
relative `η` of `r` as soon as `B·e ≤ η·r`.

This is `Arlib.GaussianCooling.integral_mem_Icc_of_tvLe` pushed through the sampling map,
and it is the exact shape `run_relErr_four_fifths_approxMean`'s `hmean` consumes
(`relErr η r` *is* the interval `Icc ((1−η)r) ((1+η)r)`). -/
theorem integral_map_mem_relErr_of_tvLe {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ν : Measure (Space n)} [IsProbabilityMeasure ν]
    {X : Ω → Space n} (hX : Measurable X) {e : ℝ≥0∞} (hTV : Arlib.TVLe (μ.map X) ν e)
    (he : e ≠ ⊤) {f : Space n → ℝ} (hf : Measurable f) {B r η : ℝ} (hB : 0 < B)
    (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B) (hr : ∫ x, f x ∂ν = r)
    (hslack : B * e.toReal ≤ η * r) :
    ∫ ω, f (X ω) ∂μ ∈ relErr η r := by
  haveI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hmap : ∫ x, f x ∂(μ.map X) = ∫ ω, f (X ω) ∂μ :=
    integral_map hX.aemeasurable hf.aestronglyMeasurable
  have h := integral_mem_Icc_of_tvLe hTV he hf hB hf0 hfB hr hslack
  rwa [hmap] at h

/-- **`hphase_mean`, derived.** With `B = e^{R²/(2σᵢ²)}` the bound on the phase score on a
body inside `R·Bₙ` (`Arlib.GaussianCooling.phaseScore_le`) and the exact-law mean identity
`E_π(W) = chain(i+1)/chain(i)` (`Arlib.GaussianCooling.integral_phaseScore_coolLaw`), a
sampler within total variation `e` of the phase law has phase mean within a relative `η` of
the chain ratio, provided `e^{R²/(2σᵢ²)}·e ≤ η·chain(i+1)/chain(i)`.

The chain ratio on the right is a *positive* explicit quantity (`chain_pos`), so the
condition is satisfiable at every positive `η` by a small enough `e`; see
`Ttc.CV.tv_slacks_satisfiable`. -/
theorem sampledPhase_mean_mem_relErr {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    {K : Set (Space n)} (hKm : MeasurableSet K)
    (hball : Metric.ball (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : ℝ} (hKR : K ⊆ Metric.closedBall (0 : Space n) R) {i : ℕ}
    {X : Ω → Space n} (hX : Measurable X)
    {e : ℝ≥0∞} (hTV : Arlib.TVLe (μ.map X) (coolLaw m σsq K i) e) (he : e ≠ ⊤) {η : ℝ}
    (hslack : Real.exp (R ^ 2 / (2 * σsq i)) * e.toReal
        ≤ η * (chain m σsq K (i + 1) / chain m σsq K i)) :
    ∫ ω, phaseScore m σsq K i (X ω) ∂μ
      ∈ relErr η (chain m σsq K (i + 1) / chain m σsq K i) := by
  haveI := coolLaw_isProbabilityMeasure (m := m) hσ hball hfin i
  exact integral_map_mem_relErr_of_tvLe hX hTV he (measurable_phaseScore hKm i)
    (Real.exp_pos _) (phaseScore_nonneg m σsq K i) (phaseScore_le hσ hKR i)
    (integral_phaseScore_coolLaw hKm (chain_pos hσ hball hfin i)) hslack

/-- **The two slack conditions are simultaneously satisfiable, at a strictly positive TV
error.** This is the non-vacuity check for the pair (radius, sampler guarantee): the mean
condition `B·e ≤ η·r` and the variance condition `e·B²·(1 + 2(C+s)) ≤ s·r²` are *both*
upper bounds on the single quantity `e`, with strictly positive right-hand sides whenever
the radius, the variance, the chain ratio `r`, the per-phase bias `η` and the variance
slack `s` are positive. So every `e` below the (positive) minimum of the two thresholds
meets both, and the bundle is not vacuous.

`B = e^{R²/(2σ)}` is written out so that the dependence on the radius is visible: the
threshold degrades like `e^{−R²/σ}`, which is what "the tolerable TV error is
`ε ≲ s·E(W)²·e^{−R²/σᵢ²}`" means quantitatively. -/
theorem tv_slacks_satisfiable {R σ r η s C e : ℝ} (hr : 0 < r) (hη : 0 < η) (hs : 0 < s)
    (hC : 0 ≤ C) (he0 : 0 ≤ e)
    (hmean : e ≤ η * r / Real.exp (R ^ 2 / (2 * σ)))
    (hvar : e ≤ s * r ^ 2 / (Real.exp (R ^ 2 / (2 * σ)) ^ 2 * (1 + 2 * (C + s)))) :
    Real.exp (R ^ 2 / (2 * σ)) * e ≤ η * r ∧
      e * (Real.exp (R ^ 2 / (2 * σ)) ^ 2 * (1 + 2 * (C + s))) ≤ s * r ^ 2 := by
  have hB : (0 : ℝ) < Real.exp (R ^ 2 / (2 * σ)) := Real.exp_pos _
  have hD : (0 : ℝ) < Real.exp (R ^ 2 / (2 * σ)) ^ 2 * (1 + 2 * (C + s)) := by positivity
  constructor
  · rw [mul_comm]
    exact (le_div_iff₀ hB).1 hmean
  · exact (le_div_iff₀ hD).1 hvar

/-- **The thresholds in `tv_slacks_satisfiable` are strictly positive**, so a strictly
positive `e` meeting both exists. (Together with `tv_slacks_satisfiable` this is the
statement that the radius hypothesis and the sampler hypothesis can hold *at the same
time*.) -/
theorem tv_slack_threshold_pos {R σ r η s C : ℝ} (hr : 0 < r) (hη : 0 < η) (hs : 0 < s)
    (hC : 0 ≤ C) :
    0 < min (η * r / Real.exp (R ^ 2 / (2 * σ)))
      (s * r ^ 2 / (Real.exp (R ^ 2 / (2 * σ)) ^ 2 * (1 + 2 * (C + s)))) := by
  have hB : (0 : ℝ) < Real.exp (R ^ 2 / (2 * σ)) := Real.exp_pos _
  refine lt_min (by positivity) ?_
  have : (0 : ℝ) < Real.exp (R ^ 2 / (2 * σ)) ^ 2 * (1 + 2 * (C + s)) := by positivity
  positivity

/-- **The satisfiability check for (radius) + (sampler guarantee), at the real parameters.**

For a positive schedule, a body containing the unit ball and of finite volume, a positive
per-phase mean bias `η` and a positive variance slack `s`, there is a **strictly positive**
total-variation error `e` meeting *both* slack conditions of
`Ttc.VolumeAlgorithm.cousinsVempalaOfSampler` at phase `i` — with the actual radius `R`,
the actual variance `σᵢ²` and the actual chain ratio, not with idealized stand-ins.

So the two new inputs are **simultaneously satisfiable**, and the construction's slack
conditions do not silently force `e = 0`. What they *do* force is a genuinely small `e`:
the threshold carries the factor `e^{−R²/(2σᵢ²)}` (mean side) and `e^{−R²/σᵢ²}` (variance
side), so the sampler must be exponentially accurate in `R²/σᵢ²`. That is a real cost, and
it is the reason the radius had to become an explicit parameter. -/
theorem exists_pos_tvErr {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    {K : Set (Space n)} (hball : Metric.ball (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R η s C : ℝ} (hη : 0 < η) (hs : 0 < s) (hC : 0 ≤ C) (i : ℕ) :
    ∃ e : ℝ, 0 < e ∧
      Real.exp (R ^ 2 / (2 * σsq i)) * e
          ≤ η * (chain m σsq K (i + 1) / chain m σsq K i) ∧
      e * (Real.exp (R ^ 2 / (2 * σsq i)) ^ 2 * (1 + 2 * (C + s)))
          ≤ s * (chain m σsq K (i + 1) / chain m σsq K i) ^ 2 := by
  have hr : 0 < chain m σsq K (i + 1) / chain m σsq K i :=
    div_pos (chain_pos hσ hball hfin (i + 1)) (chain_pos hσ hball hfin i)
  refine ⟨min (η * (chain m σsq K (i + 1) / chain m σsq K i)
        / Real.exp (R ^ 2 / (2 * σsq i)))
      (s * (chain m σsq K (i + 1) / chain m σsq K i) ^ 2
        / (Real.exp (R ^ 2 / (2 * σsq i)) ^ 2 * (1 + 2 * (C + s)))),
    tv_slack_threshold_pos hr hη hs hC, ?_, ?_⟩
  · exact (tv_slacks_satisfiable hr hη hs hC
      (tv_slack_threshold_pos hr hη hs hC).le (min_le_left _ _) (min_le_right _ _)).1
  · exact (tv_slacks_satisfiable hr hη hs hC
      (tv_slack_threshold_pos hr hη hs hC).le (min_le_left _ _) (min_le_right _ _)).2

/-- **`hvar_exact` is a theorem at an interior phase of the fixed-rate schedule**, on the
measurable core `interior K`. This is `Arlib.GaussianCooling.coolLaw_sq_moment_le`, whose
`ZLogconcaveHypothesis` input is discharged for the indicator of a convex set, so nothing
is assumed here.

**But it is only available where it is available.** Two restrictions, both real:

* `hi : i + 1 < m` — the *terminal* phase (`i + 1 = m`) is not covered. There the phase
  weight is the constant `1` and `coolRatio` is `e^{+‖x‖²/(2σᵢ²)}`; no second-moment bound
  for it is proved anywhere in this development.
* the constant is `1 + 2/n`, and
  `Arlib.GaussianCooling.cousinsVempalaOfSampler`'s `hvarSum` then demands
  `2m ≤ n·varBudget ε`, which by
  `Arlib.GaussianCooling.geomSchedule_total_cooling_lt` forces the schedule's total cooling
  factor `(1 + 1/n)^m` below `11/10`. A schedule meeting the variance budget at this rate
  therefore **cannot anneal**. Replacing the fixed rate `α = 1/n` by a general `α` is the
  open piece; it is not constructed here, and no claim about running time follows from
  anything in this file. -/
theorem hvar_exact_of_fixedRate {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    {K : Set (Space n)} (hK : Convex ℝ K)
    (hball : Metric.ball (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤) {i : ℕ}
    (hi : i + 1 < m) (hn : 3 ≤ n) (hrate : σsq (i + 1) = σsq i * (1 + 1 / (n : ℝ))) :
    ∫ x, phaseScore m σsq (interior K) i x ^ 2
        ∂(coolLaw m σsq (interior K) i)
      ≤ (1 + 2 / (n : ℝ))
        * (∫ x, phaseScore m σsq (interior K) i x
            ∂(coolLaw m σsq (interior K) i)) ^ 2 :=
  coolLaw_sq_moment_le hσ hK.interior isOpen_interior.measurableSet
    (ball_subset_interior hball) (volume_interior_ne_top hfin) hi hn hrate

/-! ### The flatness condition, and when it holds

`Arlib.GaussianCooling.coolLaw_sq_moment_le_all` asks for
`R² ≤ 2σⱼ² log(1 + 2/n)` at the terminal indices. Two elementary facts make that
checkable: it propagates forward along the fixed rate (so only `j = m − 1` matters), and
it follows from the explicit variance lower bound `σⱼ² ≥ n R²/2`. -/

/-- `e^x ≤ 1/(1 − x)` for `x < 1`, from `1 + y ≤ e^y` at `y = −x`. -/
theorem exp_le_inv_one_sub {x : ℝ} (hx : x < 1) : Real.exp x ≤ (1 - x)⁻¹ := by
  have h1 : (0:ℝ) < 1 - x := by linarith
  have hE : (0:ℝ) < Real.exp x := Real.exp_pos x
  have h2 : 1 - x ≤ (Real.exp x)⁻¹ := by
    have h := Real.add_one_le_exp (-x)
    rw [Real.exp_neg] at h
    linarith
  have h3 : (1 - x) * Real.exp x ≤ (Real.exp x)⁻¹ * Real.exp x :=
    mul_le_mul_of_nonneg_right h2 hE.le
  rw [inv_mul_cancel₀ hE.ne'] at h3
  rw [inv_eq_one_div, le_div_iff₀ h1]
  linarith

/-- **`log(1 + 2/n) ≥ 1/n` for `n ≥ 2`.** Equivalently `e^{1/n} ≤ 1 + 2/n`, which follows
from `e^x ≤ 1/(1−x)` and `(1 + 2/n)(1 − 1/n) = 1 + 1/n − 2/n² ≥ 1`. This is the only
quantitative fact needed to turn the flatness condition into a variance lower bound. -/
theorem one_div_le_log_one_add_two_div {n : ℕ} (hn : 2 ≤ n) :
    1 / (n : ℝ) ≤ Real.log (1 + 2 / (n : ℝ)) := by
  have hN : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hN0 : (0:ℝ) < (n:ℝ) := by linarith
  have ht0 : (0:ℝ) < 1 / (n:ℝ) := by positivity
  have ht2 : 1 / (n:ℝ) ≤ 1/2 := by
    rw [div_le_div_iff₀ hN0 (by norm_num)]; linarith
  have hsplit : 2 / (n:ℝ) = 2 * (1 / (n:ℝ)) := by ring
  rw [hsplit]
  have hpos : (0:ℝ) < 1 + 2 * (1 / (n:ℝ)) := by linarith
  rw [Real.le_log_iff_exp_le hpos]
  refine (exp_le_inv_one_sub (by linarith : 1 / (n:ℝ) < 1)).trans ?_
  rw [inv_eq_one_div, div_le_iff₀ (by linarith : (0:ℝ) < 1 - 1 / (n:ℝ))]
  nlinarith

/-- **The flatness condition from a variance lower bound.** `σ ≥ n R²/2` gives
`R² ≤ 2σ log(1 + 2/n)`, for every dimension `n ≥ 2`. So the terminal phase is covered as
soon as the schedule's last variance is `Ω(n R²)` — which is the honest price recorded in
`Arlib/Convexity/GaussianCooling/TerminalPhase.lean` (`σᵢ² ≳ nR²/4`; the constant here is
`1/2` rather than `1/4` because `log(1 + 2/n)` is bounded below by `1/n`, not `2/n`). -/
theorem flat_of_sigmaSq_ge {n : ℕ} (hn : 2 ≤ n) {R σ : ℝ} (h : (n : ℝ) * R ^ 2 / 2 ≤ σ) :
    R ^ 2 ≤ 2 * σ * Real.log (1 + 2 / (n : ℝ)) := by
  have hN : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hN0 : (0:ℝ) < (n:ℝ) := by linarith
  have hlog := one_div_le_log_one_add_two_div hn
  have hσ0 : (0:ℝ) ≤ σ := le_trans (by positivity) h
  have hR : R ^ 2 ≤ 2 * σ * (1 / (n:ℝ)) := by
    rw [mul_one_div, le_div_iff₀ hN0]
    nlinarith
  nlinarith

/-- **The flatness condition only has to be checked at the last index.** Along the
fixed-rate schedule the variance is nondecreasing, so
`Arlib.GaussianCooling.flat_of_fixedRate_of_le` propagates `hflat` from `j = m − 1` to
every terminal index. -/
theorem flat_of_fixedRate_terminal {m : ℕ} {σsq : ℕ → ℝ} {R : ℝ} (hσ : ∀ j, 0 < σsq j)
    (hn : 0 < n) (hrate : ∀ j, σsq (j + 1) = σsq j * (1 + 1 / (n : ℝ)))
    (hlast : R ^ 2 ≤ 2 * σsq (m - 1) * Real.log (1 + 2 / (n : ℝ))) :
    ∀ j, m ≤ j + 1 → R ^ 2 ≤ 2 * σsq j * Real.log (1 + 2 / (n : ℝ)) := fun _ hj =>
  flat_of_fixedRate_of_le hσ hn hrate (by omega) hlast

/-- **`hvar_exact` at *every* phase of the fixed-rate schedule**, on the measurable core
`interior K` — the `∀ i` successor of `hvar_exact_of_fixedRate`.

This is `Arlib.GaussianCooling.coolLaw_sq_moment_le_all`: interior phases (`i + 1 < m`) are
the Brascamp–Lieb/logconcavity bound `coolLaw_sq_moment_le`, terminal phases (`m ≤ i + 1`)
are the elementary bounded-observable bound `coolLaw_sq_moment_le_terminal_flat`. The
constant is the same `1 + 2/n` in both regimes, so the two glue into the single `∀ i`
statement `Ttc.VolumeAlgorithm.cousinsVempalaOfSampler`'s `hvar_exact` field asks for.

**The price of the terminal phase is two new inputs, and neither can be dropped.**

* a radius `hKR : interior K ⊆ R·Bₙ`. At the terminal step the next phase weight is the
  constant `1`, so the score is `e^{+‖x‖²/(2σᵢ²)}` — a *growing* Gaussian weight — and the
  only thing that bounds it is the diameter of the body.
* the flatness inequality `hflat : R² ≤ 2σⱼ² log(1 + 2/n)` at the terminal indices, i.e.
  `e^{R²/(2σⱼ²)} ≤ 1 + 2/n`. By `Arlib.GaussianCooling.flat_of_fixedRate_of_le` it need
  only be checked at `j = m − 1` (see `flat_of_fixedRate_terminal` below), and by
  `flat_of_sigmaSq_ge` it holds as soon as `σⱼ² ≥ n R²/2`.

**Not an artefact of the proof.** `Arlib.GaussianCooling.terminal_sq_moment_unbounded`
proves that *no* constant depending on `n` alone works at a terminal phase: on `K = B₁`
— convex, measurable, containing the unit ball, of finite volume, i.e. satisfying every
hypothesis `coolLaw_sq_moment_le` places on `K` — and for every proposed `C` there is a
variance at which `E(W²) > C·E(W)²`. So the unconditional `∀ i` form of this statement is
**false**, and the radius/flatness pair is the minimum that repairs it.

The other restriction recorded on `hvar_exact_of_fixedRate` is untouched: meeting the
variance budget at rate `1/n` still caps the schedule's total cooling below `11/10`
(`Arlib.GaussianCooling.geomSchedule_total_cooling_lt`), so the fixed-rate schedule cannot
anneal, no general-`α` replacement is constructed here, and no running-time claim follows
from anything below. -/
theorem hvar_exact_of_fixedRate_all {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    {K : Set (Space n)} (hK : Convex ℝ K)
    (hball : Metric.ball (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : ℝ} (hKR : interior K ⊆ Metric.closedBall (0 : Space n) R) (hn : 3 ≤ n)
    (hrate : ∀ j, σsq (j + 1) = σsq j * (1 + 1 / (n : ℝ)))
    (hflat : ∀ j, m ≤ j + 1 → R ^ 2 ≤ 2 * σsq j * Real.log (1 + 2 / (n : ℝ)))
    (i : ℕ) :
    ∫ x, phaseScore m σsq (interior K) i x ^ 2
        ∂(coolLaw m σsq (interior K) i)
      ≤ (1 + 2 / (n : ℝ))
        * (∫ x, phaseScore m σsq (interior K) i x
            ∂(coolLaw m σsq (interior K) i)) ^ 2 :=
  coolLaw_sq_moment_le_all hσ hK.interior isOpen_interior.measurableSet
    (ball_subset_interior hball) (volume_interior_ne_top hfin) hKR hn hrate hflat i

/-- **The flatness condition does not conflict with the slack conditions or the budgets —
checked at real parameters.**

`hflat` forces the schedule's variance *up* (`σⱼ² ≥ n R²/2`), and the two slack conditions
of `Ttc.VolumeAlgorithm.cousinsVempalaOfSampler` carry the factors `e^{−R²/(2σᵢ²)}` and
`e^{−R²/σᵢ²}`, which increase with `σᵢ²`. So the new hypothesis and the old ones pull in the
*same* direction; there is no tension to resolve. This theorem checks that concretely, at

  `ε = 1`, `m = 2` phases, `innerAcc = 1/2`, `meanBias = 1/3`, `phaseBias = 1/12`,
  `varBudget = log(21/20)`, `n ≥ 100`, `σⱼ² = (n·R²/2 + 1)(1 + 1/n)ʲ`, `R = cvRadius K`,

with everything else the construction demands verified simultaneously:

* `hflat` at **every** index (not just the terminal ones), via `flat_of_sigmaSq_ge`;
* `hbudget`: `e^{log(21/20)} − 1 = 1/20 = (1/2)²/5`, with equality;
* `hcompose`: `1/2 + 1/3 + (1/2)(1/3) = 1 = ε`, with equality;
* `hphaseBudget`: `2·2·(1/12) = 1/3 = meanBias`, with equality;
* `hvarSum` with a **strictly positive** `varSlack = log(21/20)/2 − 2/n`. This is where the
  dimension bound comes from: `varSlack > 0` needs `n > 4/log(21/20) = 81.99…`, so `n ≥ 82`
  is the true threshold and `n ≥ 100` is the round number at which the rational bound
  `log(21/20) > 1/25` (from `e^{1/25} ≤ 25/24 < 21/20`) suffices;
* both slack conditions, at a strictly positive TV error (`exists_pos_tvErr`).

**Two honest caveats.** (i) The TV error is produced per phase index, exactly as
`exists_pos_tvErr` supplies it; the construction wants a single `tvErr K ε p` valid for all
`i`, and closing that quantifier is a pre-existing gap of `exists_pos_tvErr`, untouched by
`hflat`. (ii) The dimension bound `n ≥ 82` here is the *variance-budget* constraint
`2m ≤ n·varBudget ε` that `hvarSum` and `hbudget` already imposed — `hflat` contributes no
constraint on `n`, `m` or `ε` at all, only a lower bound on the variances, which the
schedule is free to meet. Meeting it does make the *first* Gaussian nearly flat, so the
cold start is no longer a cheaply computable integral; that is a statement about the
schedule's usefulness, not about consistency, and no running-time claim is made anywhere. -/
theorem flat_slacks_satisfiable (hn : 100 ≤ n) {K : Set (Space n)}
    (hball : Metric.ball (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤) :
    ∃ (σsq : ℕ → ℝ) (varSlack : ℝ),
      (∀ j, 0 < σsq j) ∧
      (∀ j, σsq (j + 1) = σsq j * (1 + 1 / (n : ℝ))) ∧
      (∀ j, cvRadius K ^ 2 ≤ 2 * σsq j * Real.log (1 + 2 / (n : ℝ))) ∧
      Real.exp (Real.log (21 / 20)) - 1 = (1 / 2 : ℝ) ^ 2 / 5 ∧
      (1 / 2 : ℝ) + 1 / 3 + 1 / 2 * (1 / 3) ≤ 1 ∧
      2 * (2 : ℝ) * (1 / 12) ≤ 1 / 3 ∧
      0 < varSlack ∧
      1 + 2 / (n : ℝ) + varSlack = 1 + Real.log (21 / 20) / 2 ∧
      ∀ i : ℕ, ∃ e : ℝ, 0 < e ∧
        Real.exp (cvRadius K ^ 2 / (2 * σsq i)) * e
            ≤ (1 / 12 : ℝ)
              * (chain 2 σsq (interior K) (i + 1) / chain 2 σsq (interior K) i) ∧
        e * (Real.exp (cvRadius K ^ 2 / (2 * σsq i)) ^ 2
              * (1 + 2 * (1 + Real.log (21 / 20) / 2)))
            ≤ varSlack
              * (chain 2 σsq (interior K) (i + 1) / chain 2 σsq (interior K) i) ^ 2 := by
  have hN : (100 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hn2 : 2 ≤ n := by omega
  -- the schedule: the fixed rate started just above the flatness threshold `n R²/2`
  have hq0 : (0 : ℝ) < 1 + 1 / (n : ℝ) := by positivity
  have hq1 : (1 : ℝ) ≤ 1 + 1 / (n : ℝ) := by
    have : (0 : ℝ) < 1 / (n : ℝ) := by positivity
    linarith
  set c : ℝ := (n : ℝ) * cvRadius K ^ 2 / 2 + 1 with hc
  have hc0 : (0 : ℝ) < c := by
    have : (0 : ℝ) ≤ (n : ℝ) * cvRadius K ^ 2 / 2 := by positivity
    rw [hc]; linarith
  have hσpos : ∀ j, (0 : ℝ) < c * (1 + 1 / (n : ℝ)) ^ j := fun j =>
    mul_pos hc0 (pow_pos hq0 j)
  -- `varSlack > 0`, from `log(21/20) > 1/25 ≥ 4/n`
  have hlog : (1 : ℝ) / 25 < Real.log (21 / 20) := by
    have h1 : Real.exp ((1 : ℝ) / 25) < 21 / 20 :=
      lt_of_le_of_lt (exp_le_inv_one_sub (by norm_num)) (by norm_num)
    rw [← Real.exp_log (show (0 : ℝ) < 21 / 20 by norm_num)] at h1
    exact Real.exp_lt_exp.mp h1
  have h4n : 4 / (n : ℝ) ≤ 1 / 25 := by
    rw [div_le_div_iff₀ hN0 (by norm_num)]; linarith
  have h2n : 2 * (2 / (n : ℝ)) = 4 / (n : ℝ) := by ring
  have hslack_pos : (0 : ℝ) < Real.log (21 / 20) / 2 - 2 / (n : ℝ) := by linarith
  refine ⟨fun j => c * (1 + 1 / (n : ℝ)) ^ j, Real.log (21 / 20) / 2 - 2 / (n : ℝ),
    hσpos, fun j => by simp only [pow_succ]; ring, fun j => ?_, ?_, by norm_num, by norm_num,
    hslack_pos, by ring, fun i => ?_⟩
  · refine flat_of_sigmaSq_ge hn2 ?_
    have hp : (1 : ℝ) ≤ (1 + 1 / (n : ℝ)) ^ j := one_le_pow₀ hq1
    nlinarith [hc0]
  · rw [Real.exp_log (show (0 : ℝ) < 21 / 20 by norm_num)]; norm_num
  · obtain ⟨e, he0, hmean, hvar⟩ :=
      exists_pos_tvErr (m := 2) (σsq := fun j => c * (1 + 1 / (n : ℝ)) ^ j) hσpos
        (ball_subset_interior hball) (volume_interior_ne_top hfin)
        (R := cvRadius K) (η := 1 / 12)
        (s := Real.log (21 / 20) / 2 - 2 / (n : ℝ)) (C := 1 + 2 / (n : ℝ))
        (by norm_num) hslack_pos (by positivity) i
    have hCs : 1 + 2 / (n : ℝ) + (Real.log (21 / 20) / 2 - 2 / (n : ℝ))
        = 1 + Real.log (21 / 20) / 2 := by ring
    rw [hCs] at hvar
    exact ⟨e, he0, hmean, hvar⟩

/-! ### What the fixed-rate construction is actually worth

`flat_slacks_satisfiable` shows the fixed-rate bundle is *consistent*. This subsection
shows what that consistency costs, and it is the sharpest statement available about
`Ttc.VolumeAlgorithm.cousinsVempalaOfSamplerFixedRate`: **the schedule it admits does no
cooling, and its cold start already is the answer.** Three elementary steps:

1. `hflat` at `j = m − 1`, with `log(1 + 2/n) ≤ 2/n`, forces `σ_{m−1}² ≥ n R²/4`
   (`sigmaSq_ge_of_flat`);
2. `hvarSum` (through `varSlack ≥ 0`) and `hbudget` force `2m ≤ n·varBudget ε`, hence
   `(1 + 1/n)^m < 11/10` — that is `Arlib.GaussianCooling.geomSchedule_total_cooling_lt`,
   already proved;
3. therefore `σ₀² = σ_{m−1}²/(1 + 1/n)^{m−1} > 5nR²/22`, so on `K ⊆ R·Bₙ` the phase-`0`
   Gaussian weight is at least `e^{−11/(5n)}` pointwise and the cold endpoint of the chain
   is within relative error `11/(5n)` of `Vol(K)` (`chain_zero_mem_relErr_of_flat`).

The telescope has nothing left to telescope: its *starting* value is already an
`O(1/n)`-accurate estimate of the quantity it is trying to compute. This is a statement
about the fixed rate only; the general-`α` schedule of
`Arlib/Convexity/GaussianCooling/PhaseSchedule.lean` escapes it, and
`cold_start_exponent_ge_of_coolRate` below is its quantitative counterpart. -/

/-- `log(1 + 2/n) ≤ 2/n`, from `log x ≤ x − 1`. The companion of
`one_div_le_log_one_add_two_div` in the other direction, and the only quantitative input to
`sigmaSq_ge_of_flat`. -/
theorem log_one_add_two_div_le {n : ℕ} (hn : 0 < n) :
    Real.log (1 + 2 / (n : ℝ)) ≤ 2 / (n : ℝ) := by
  have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hx : (0 : ℝ) < 1 + 2 / (n : ℝ) := by positivity
  linarith [Real.log_le_sub_one_of_pos hx]

/-- **The converse of `flat_of_sigmaSq_ge`: `hflat` *forces* a large variance.**
`R² ≤ 2σ log(1 + 2/n)` and `σ > 0` give `σ ≥ n R²/4`. Together with `flat_of_sigmaSq_ge`
(`σ ≥ nR²/2 ⟹ hflat`) this pins the flatness condition to `σ = Θ(nR²)`, so nothing about
the constant `4` is an artefact. -/
theorem sigmaSq_ge_of_flat {n : ℕ} (hn : 0 < n) {R σ : ℝ} (hσ : 0 < σ)
    (hflat : R ^ 2 ≤ 2 * σ * Real.log (1 + 2 / (n : ℝ))) :
    (n : ℝ) * R ^ 2 / 4 ≤ σ := by
  have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog := log_one_add_two_div_le hn
  have h : R ^ 2 ≤ 2 * σ * (2 / (n : ℝ)) := hflat.trans (by nlinarith)
  have h4 : 2 * σ * (2 / (n : ℝ)) = 4 * σ / (n : ℝ) := by ring
  rw [h4, le_div_iff₀ hN] at h
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 4)]
  nlinarith

/-- A geometric rate integrates to a power: `hrate` determines the whole schedule from
`σ₀²`. -/
theorem sigmaSq_eq_pow {σsq : ℕ → ℝ} {α : ℝ}
    (hrate : ∀ j, σsq (j + 1) = σsq j * (1 + α)) (j : ℕ) :
    σsq j = σsq 0 * (1 + α) ^ j := by
  induction j with
  | zero => simp
  | succ k ih => rw [hrate k, ih]; ring

/-- **Step 3: the fixed-rate flat schedule starts hot.** Under
`hflat` at `j = m − 1` and the budget relation `2m ≤ n·varBudget ε` that `hvarSum` and
`hbudget` impose, the *initial* variance already satisfies `σ₀² > 5nR²/22`. So the phase-`0`
Gaussian barely varies over `K ⊆ R·Bₙ`. -/
theorem sigmaSq_zero_gt_of_flat_of_meet {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    (hn : 0 < n) {R : ℝ}
    (hrate : ∀ j, σsq (j + 1) = σsq j * (1 + 1 / (n : ℝ)))
    (hflat : R ^ 2 ≤ 2 * σsq (m - 1) * Real.log (1 + 2 / (n : ℝ)))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmeet : 2 * (m : ℝ) ≤ (n : ℝ) * varBudget ε) :
    5 * (n : ℝ) * R ^ 2 / 22 < σsq 0 := by
  have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hq1 : (1 : ℝ) ≤ 1 + 1 / (n : ℝ) := by
    have : (0 : ℝ) < 1 / (n : ℝ) := by positivity
    linarith
  have hcool : (1 + 1 / (n : ℝ)) ^ m < 11 / 10 :=
    geomSchedule_total_cooling_lt hn hε1 hε0 hmeet
  have hmono : (1 + 1 / (n : ℝ)) ^ (m - 1) ≤ (1 + 1 / (n : ℝ)) ^ m :=
    pow_le_pow_right₀ hq1 (Nat.sub_le m 1)
  have hbig := sigmaSq_ge_of_flat hn (hσ (m - 1)) hflat
  rw [sigmaSq_eq_pow hrate (m - 1)] at hbig
  nlinarith [hσ 0, pow_nonneg (by linarith : (0:ℝ) ≤ 1 + 1 / (n:ℝ)) (m - 1)]

/-- **The finding, in its pointwise form.** Under the fixed rate, `hflat` and the variance
budget, the phase-`0` cooling weight is within `e^{−11/(5n)}` of `1` everywhere on
`K ⊆ R·Bₙ`. -/
theorem coolWeight_zero_ge_of_flat {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    (hn : 0 < n) (hm : 0 < m) {K : Set (Space n)} {R : ℝ}
    (hKR : K ⊆ Metric.closedBall (0 : Space n) R)
    (hrate : ∀ j, σsq (j + 1) = σsq j * (1 + 1 / (n : ℝ)))
    (hflat : R ^ 2 ≤ 2 * σsq (m - 1) * Real.log (1 + 2 / (n : ℝ)))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmeet : 2 * (m : ℝ) ≤ (n : ℝ) * varBudget ε)
    {x : Space n} (hx : x ∈ K) :
    Real.exp (-(11 / (5 * (n : ℝ)))) ≤ coolWeight m σsq 0 x := by
  have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h0 := sigmaSq_zero_gt_of_flat_of_meet hσ hn hrate hflat hε0 hε1 hmeet
  have hxR : ‖x‖ ≤ R := mem_closedBall_zero_iff.1 (hKR hx)
  have hxR2 : ‖x‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg x]
  rw [coolWeight_of_lt hm]
  refine Real.exp_le_exp.2 ?_
  have h2s : (0 : ℝ) < 2 * σsq 0 := by linarith [hσ 0]
  have hquot : ‖x‖ ^ 2 / (2 * σsq 0) ≤ 11 / (5 * (n : ℝ)) := by
    rw [div_le_div_iff₀ h2s (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hxR2 hN.le]
  have hrw : -(‖x‖ ^ 2) / (2 * σsq 0) = -(‖x‖ ^ 2 / (2 * σsq 0)) := neg_div _ _
  rw [hrw]
  linarith

/-- **THE FINDING (Part 1): the cold start of the fixed-rate construction already is the
volume, to relative error `11/(5n)`.**

For a positive schedule at the fixed rate `σⱼ₊₁² = σⱼ²(1 + 1/n)`, a measurable body
`B₁ ⊆ K ⊆ R·Bₙ` of finite volume, the flatness condition `hflat` at `j = m − 1` (the
construction's `hflat` field instantiated at that index — and by `flat_of_fixedRate_terminal`
that single index is also all it needs), and the budget relation `2m ≤ n·varBudget ε` (which its
`hvarSum` + `hbudget` + `hcompose` fields force, by
`Arlib.GaussianCooling.fixedRate_meets_budget_iff`):

  `chain m σsq K 0 ∈ (1 ± 11/(5n))·Vol(K)`.

**What this means.** The Cousins–Vempala telescope computes `Vol(K)` as
`chain 0 · ∏ᵢ (chain (i+1)/chain i)`, and the whole apparatus — sampler, phases, median
boost — exists to estimate the product. This theorem says that under the hypotheses the
fixed-rate construction actually carries, the *first factor alone* is already an
`O(1/n)`-accurate estimate of the answer, so the product it multiplies by is `1 ± O(1/n)`.
The construction is consistent (`flat_slacks_satisfiable`) and it is not vacuous, but it
anneals nothing: it is the observation "a Gaussian of variance `Ω(nR²)` is flat on `R·Bₙ`"
dressed as an algorithm.

**This is a statement about the fixed rate, not about Gaussian cooling.** The general-`α`
schedule of `Arlib/Convexity/GaussianCooling/PhaseSchedule.lean` cools by `e^L` and is not
subject to step 2; `cold_start_exponent_ge_of_coolRate` gives its (non-degenerate)
counterpart. No running-time claim of any kind is made here, in either direction. -/
theorem chain_zero_mem_relErr_of_flat {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    (hn : 0 < n) (hm : 0 < m) {K : Set (Space n)} (hKm : MeasurableSet K)
    (hfin : volume K ≠ ⊤) {R : ℝ} (hKR : K ⊆ Metric.closedBall (0 : Space n) R)
    (hrate : ∀ j, σsq (j + 1) = σsq j * (1 + 1 / (n : ℝ)))
    (hflat : R ^ 2 ≤ 2 * σsq (m - 1) * Real.log (1 + 2 / (n : ℝ)))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmeet : 2 * (m : ℝ) ≤ (n : ℝ) * varBudget ε) :
    chain m σsq K 0 ∈ relErr (11 / (5 * (n : ℝ))) (volume K).toReal := by
  have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hvol : (0 : ℝ) ≤ (volume K).toReal := ENNReal.toReal_nonneg
  have hlow : Real.exp (-(11 / (5 * (n : ℝ)))) * (volume K).toReal ≤ chain m σsq K 0 := by
    have h1 : ∫ _x in K, Real.exp (-(11 / (5 * (n : ℝ)))) ≤ ∫ x in K, coolWeight m σsq 0 x :=
      setIntegral_mono_on (integrableOn_const' hfin _)
        (integrableOn_coolWeight (hσ 0) hfin) hKm
        (fun x hx => coolWeight_zero_ge_of_flat hσ hn hm hKR hrate hflat hε0 hε1 hmeet hx)
    have h3 : ∫ _x in K, Real.exp (-(11 / (5 * (n : ℝ))))
        = Real.exp (-(11 / (5 * (n : ℝ)))) * (volume K).toReal := by
      rw [setIntegral_const, smul_eq_mul, measureReal_def]; ring
    rw [chain_def]
    linarith [h3.le, h3.ge]
  have hhigh : chain m σsq K 0 ≤ (volume K).toReal := chain_le_volume (hσ 0) hfin
  have hexp : (1 : ℝ) - 11 / (5 * (n : ℝ)) ≤ Real.exp (-(11 / (5 * (n : ℝ)))) := by
    linarith [Real.add_one_le_exp (-(11 / (5 * (n : ℝ))))]
  have hslack : (0 : ℝ) ≤ 11 / (5 * (n : ℝ)) := by positivity
  refine ⟨?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_right hexp hvol]
  · nlinarith

/-- **The finding, on the object the construction actually runs on.**
`Ttc.VolumeAlgorithm.cousinsVempalaOfSamplerFixedRate` runs the whole telescope on
`interior K` (a convex set need not be Borel, so `MeasurableSet K` is unavailable and
would be a vacuity trap). `interior K` is open, hence measurable, and has the same volume
as `K` (`volume_interior_eq`), so the cold-start estimate is an estimate of `Vol(K)`
itself. -/
theorem cold_start_mem_relErr_of_flat {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    (hn : 0 < n) (hm : 0 < m) {K : Set (Space n)} (hK : Convex ℝ K)
    (hfin : volume K ≠ ⊤) {R : ℝ}
    (hKR : interior K ⊆ Metric.closedBall (0 : Space n) R)
    (hrate : ∀ j, σsq (j + 1) = σsq j * (1 + 1 / (n : ℝ)))
    (hflat : R ^ 2 ≤ 2 * σsq (m - 1) * Real.log (1 + 2 / (n : ℝ)))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmeet : 2 * (m : ℝ) ≤ (n : ℝ) * varBudget ε) :
    chain m σsq (interior K) 0 ∈ relErr (11 / (5 * (n : ℝ))) (volume K).toReal := by
  have h := chain_zero_mem_relErr_of_flat hσ hn hm isOpen_interior.measurableSet
    (volume_interior_ne_top hfin) hKR hrate hflat hε0 hε1 hmeet
  rwa [volume_interior_eq hK] at h

/-- **The construction's budget parameter is inside the canonical `varBudget`.**
`cousinsVempalaOfSamplerFixedRate` carries `varBudget` as *data* constrained by
`hbudget : e^{V} − 1 ≤ innerAcc²/5` and `hcompose : innerAcc + meanBias + innerAcc·meanBias
≤ ε`. Since `meanBias ≥ 0` and `innerAcc > 0` force `innerAcc ≤ ε`, this gives
`V ≤ log(1 + ε²/5) = varBudget ε`. -/
theorem varBudget_param_le {V innerAcc meanBias ε : ℝ} (hinner : 0 < innerAcc)
    (hmean : 0 ≤ meanBias)
    (hcompose : innerAcc + meanBias + innerAcc * meanBias ≤ ε)
    (hbudget : Real.exp V - 1 ≤ innerAcc ^ 2 / 5) :
    V ≤ varBudget ε := by
  have hprod : 0 ≤ innerAcc * meanBias := mul_nonneg hinner.le hmean
  have hle : innerAcc ≤ ε := by linarith
  refine Real.exp_le_exp.1 ?_
  rw [exp_varBudget]
  nlinarith

/-- **Step 2, derived from `cousinsVempalaOfSamplerFixedRate`'s own fields.**
`hvarSum` (with `hvarSlack_nonneg`), `hbudget` and `hcompose` together force
`2m ≤ n·varBudget ε`, i.e. exactly the hypothesis
`Arlib.GaussianCooling.geomSchedule_total_cooling_lt` consumes. Nothing extra is assumed:
this is the construction's arithmetic, read off. -/
theorem meet_of_fixedRate_fields {m : ℕ} {V varSlack innerAcc meanBias ε : ℝ}
    (hn : 0 < n) (hm : 0 < m) (hinner : 0 < innerAcc) (hmean : 0 ≤ meanBias)
    (hslack : 0 ≤ varSlack)
    (hvarSum : (1 + 2 / (n : ℝ)) + varSlack = 1 + V / (m : ℝ))
    (hcompose : innerAcc + meanBias + innerAcc * meanBias ≤ ε)
    (hbudget : Real.exp V - 1 ≤ innerAcc ^ 2 / 5) :
    2 * (m : ℝ) ≤ (n : ℝ) * varBudget ε := by
  have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h2 := (fixedRate_meets_budget_iff hn hm V).1 (by linarith)
  have h3 := varBudget_param_le hinner hmean hcompose hbudget
  nlinarith

/-- **THE FINDING, assembled from `cousinsVempalaOfSamplerFixedRate`'s own fields.**

Given exactly what that construction is handed — a positive schedule at the fixed rate, the
radius, the flatness condition at `j = m − 1`, `hvarSum` with a nonnegative `varSlack`,
`hbudget` and `hcompose` — its cold endpoint already estimates `Vol(K)` to relative error
`11/(5n)`:

  `chain m σsq (interior K) 0 ∈ (1 ± 11/(5n))·Vol(K)`.

No hypothesis here is stronger than a field of the construction; `varBudget` is its own
data, not the canonical one (`varBudget_param_le` bridges them). This is the honest
statement of what the fixed-rate construction is worth. -/
theorem cold_start_mem_relErr_of_fixedRate_fields {m : ℕ} {σsq : ℕ → ℝ}
    {V varSlack innerAcc meanBias ε R : ℝ} (hσ : ∀ j, 0 < σsq j) (hn : 0 < n) (hm : 0 < m)
    {K : Set (Space n)} (hK : Convex ℝ K) (hfin : volume K ≠ ⊤)
    (hKR : interior K ⊆ Metric.closedBall (0 : Space n) R)
    (hrate : ∀ j, σsq (j + 1) = σsq j * (1 + 1 / (n : ℝ)))
    (hflat : R ^ 2 ≤ 2 * σsq (m - 1) * Real.log (1 + 2 / (n : ℝ)))
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hinner : 0 < innerAcc) (hmean : 0 ≤ meanBias)
    (hslack : 0 ≤ varSlack)
    (hvarSum : (1 + 2 / (n : ℝ)) + varSlack = 1 + V / (m : ℝ))
    (hcompose : innerAcc + meanBias + innerAcc * meanBias ≤ ε)
    (hbudget : Real.exp V - 1 ≤ innerAcc ^ 2 / 5) :
    chain m σsq (interior K) 0 ∈ relErr (11 / (5 * (n : ℝ))) (volume K).toReal :=
  cold_start_mem_relErr_of_flat hσ hn hm hK hfin hKR hrate hflat hε0.le hε1
    (meet_of_fixedRate_fields hn hm hinner hmean hslack hvarSum hcompose hbudget)

/-! ### Part 2: the general-`α` schedule, which does anneal

`Arlib/Convexity/GaussianCooling/PhaseSchedule.lean` replaces the fixed rate `α = 1/n` by

  `m = coolPhases n L κ = ⌈8(n+1)L²/κ⌉`,   `α = coolRate n L κ = √(κ/(2m(n+1)))`,

and proves both halves at once: `coolRate_meets_budget` — the per-phase factor
`(1-α²)^{-(n+1)}` is at most `1 + κ/m` — and `coolSchedule_total_cooling` — the total
cooling factor is at least `e^L`. Step 2 of Part 1 therefore does not apply: the budget is
met *by construction*, not by shrinking `m`.

What has to be redone here is the **terminal** phase. `coolLaw_sq_moment_le_terminal_flat`
is hard-wired to the constant `1 + 2/n`; at the cooling rate the interior constant is
`1 + κ/m` instead, so the flatness condition must be re-stated at that constant:

  `R² ≤ 2σⱼ² · log(1 + κ/m)`   instead of   `R² ≤ 2σⱼ² · log(1 + 2/n)`.

The route is `coolLaw_sq_moment_le_terminal`, which is hypothesis-free apart from the
radius and delivers the constant `e^{R²/(2σᵢ²)}`.

**Is that jointly satisfiable with the slack conditions?**  Yes, and there is no tension:
`hflat` is a *lower* bound on the variances, the two slack thresholds carry `e^{−R²/(2σᵢ²)}`
and `e^{−R²/σᵢ²}` and therefore *increase* with the variance, and nothing in
`cousinsVempalaOfSampler` bounds any `σᵢ²` from above. `cool_flat_slacks_satisfiable`
checks this at explicit numbers.

**What the general schedule does cost, honestly.** The flatness threshold is now
`σ_{m−1}² ≥ R²/(2 log(1 + κ/m)) ≈ R²m/(2κ) ≈ 4(n+1)L²R²/κ²` — it grows with the phase
count, exactly cancelling part of the cooling. On the tightest admissible schedule the
cold-start exponent is

  `R²/(2σ₀²) = log(1 + κ/m)·(1 + α)^{m−1} ≈ κ²·e^{2L}/(8(n+1)L²)`,

since `m·α = 2L` at `m = 8(n+1)L²/κ`. `cold_start_exponent_ge_of_coolRate` proves the
weaker but unconditional `≥ log(1 + κ/m)·e^L/(1 + α)`. Either way, it beats Part 1's
ceiling of `11/(5n)` only once

  `e^{2L} ≳ 88(n+1)L²/(5nκ²) ≈ 17.6·L²/κ²`,

which is essentially **dimension-free**. At `κ = log(21/20)/2 ≈ 0.0244` the crossover is
`L ≈ 7.2` for `n = 100` and `L ≈ 7.3` for `n = 1000`; in Cousins–Vempala's own regime
`e^L ≈ nR²` that is `R ≳ 3.7` at `n = 100`. Below the crossover the general schedule
inherits Part 1's degeneracy in full. **No running-time claim is made or implied**; the
per-phase sampling cost is untouched and this repository's conductance constants are
exponentially small in `n`. -/

/-- Along any geometric schedule with a nonnegative rate the variance is nondecreasing. -/
theorem sigmaSq_mono_of_rate {σsq : ℕ → ℝ} {α : ℝ} (hσ : ∀ j, 0 < σsq j) (hα : 0 ≤ α)
    (hrate : ∀ j, σsq (j + 1) = σsq j * (1 + α)) {j k : ℕ} (hjk : j ≤ k) :
    σsq j ≤ σsq k := by
  rw [sigmaSq_eq_pow hrate j, sigmaSq_eq_pow hrate k]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by linarith) hjk) (hσ 0).le

/-- **Flatness propagates forward along any geometric schedule**, at any constant `c ≥ 0`.
The general-rate successor of `Arlib.GaussianCooling.flat_of_fixedRate_of_le`; it is what
lets `hflat` be checked at the single index `j = m − 1`. -/
theorem flat_of_rate_of_le {σsq : ℕ → ℝ} {α c R : ℝ} (hσ : ∀ j, 0 < σsq j) (hα : 0 ≤ α)
    (hc : 0 ≤ c) (hrate : ∀ j, σsq (j + 1) = σsq j * (1 + α)) {j k : ℕ} (hjk : j ≤ k)
    (hflat : R ^ 2 ≤ 2 * σsq j * c) :
    R ^ 2 ≤ 2 * σsq k * c := by
  have := sigmaSq_mono_of_rate hσ hα hrate hjk
  nlinarith

/-- **`hvar_exact` at *every* phase of the annealing schedule**, on `interior K`.

The general-`α` counterpart of `hvar_exact_of_fixedRate_all`, with three differences, all
of them improvements or forced:

* the constant is `1 + κ/m` — the algorithm's own per-phase allowance — rather than
  `1 + 2/n`, so `hvarSum` no longer forces `2m ≤ nκ` and the schedule is free to anneal;
* **no `3 ≤ n`**: `Arlib.GaussianCooling.coolLaw_sq_moment_le_rate` needs no dimension
  bound, since it consumes `G_mul_G_le_indicator` directly rather than the fixed-rate
  specialisation;
* the flatness condition is at the *matching* constant, `R² ≤ 2σⱼ² log(1 + κ/m)`. Terminal
  phases go through `Arlib.GaussianCooling.coolLaw_sq_moment_le_terminal`, which needs only
  the radius.

`Arlib.GaussianCooling.terminal_sq_moment_unbounded` still applies: no constant depending
on `n` alone works at a terminal phase, so the radius/flatness pair cannot be dropped. -/
theorem hvar_exact_of_coolRate_all {L κ : ℝ} (hL : 1 ≤ L) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    {K : Set (Space n)} (hK : Convex ℝ K)
    (hball : Metric.ball (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : ℝ} (hKR : interior K ⊆ Metric.closedBall (0 : Space n) R)
    (hrate : ∀ j, σsq (j + 1) = σsq j * (1 + coolRate n L κ))
    (hflat : ∀ j, coolPhases n L κ ≤ j + 1 →
      R ^ 2 ≤ 2 * σsq j * Real.log (1 + κ / (coolPhases n L κ : ℝ)))
    (i : ℕ) :
    ∫ x, phaseScore (coolPhases n L κ) σsq (interior K) i x ^ 2
        ∂(coolLaw (coolPhases n L κ) σsq (interior K) i)
      ≤ (1 + κ / (coolPhases n L κ : ℝ))
        * (∫ x, phaseScore (coolPhases n L κ) σsq (interior K) i x
            ∂(coolLaw (coolPhases n L κ) σsq (interior K) i)) ^ 2 := by
  have hm0 : (0 : ℝ) < (coolPhases n L κ : ℝ) := by
    have := one_le_coolPhases (n := n) hL hκ0; linarith
  have hC : (0 : ℝ) < 1 + κ / (coolPhases n L κ : ℝ) := by positivity
  rcases lt_or_ge (i + 1) (coolPhases n L κ) with h | h
  · exact coolLaw_sq_moment_le_budget hL hκ0 hκ1 hσ hK.interior
      isOpen_interior.measurableSet (ball_subset_interior hball)
      (volume_interior_ne_top hfin) h (hrate i)
  · refine (coolLaw_sq_moment_le_terminal hσ isOpen_interior.measurableSet
      (ball_subset_interior hball) (volume_interior_ne_top hfin) hKR h).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [← Real.exp_log hC]
    refine Real.exp_le_exp.2 ?_
    rw [div_le_iff₀ (by linarith [hσ i] : (0 : ℝ) < 2 * σsq i)]
    linarith [hflat i h]

/-- **The schedule of `cousinsVempalaOfSamplerCooling` really anneals.** Its total cooling
factor is at least `e^L`:

  `e^L · σ₀² ≤ σ_m²`,   `m = coolPhases n L κ`.

This is the exact negation of the fixed-rate situation: `geomSchedule_total_cooling_lt`
caps a budget-meeting fixed-rate schedule at `(1 + 1/n)^m < 11/10`, and `L` here is
unbounded. -/
theorem cool_schedule_anneals {L κ : ℝ} (hL : 1 ≤ L) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    {σsq : ℕ → ℝ} (hσ0 : 0 < σsq 0)
    (hrate : ∀ j, σsq (j + 1) = σsq j * (1 + coolRate n L κ)) :
    Real.exp L * σsq 0 ≤ σsq (coolPhases n L κ) := by
  rw [sigmaSq_eq_pow hrate (coolPhases n L κ)]
  nlinarith [coolSchedule_total_cooling (n := n) hL hκ0 hκ1]

/-- **The cold-start exponent under real cooling — the quantitative counterpart of
`chain_zero_mem_relErr_of_flat`.**

Take the schedule that meets the flatness condition *exactly* at the last index (the
cheapest admissible one; any larger schedule is flatter still). Then

  `R²/(2σ₀²) = log(1 + κ/m)·(1+α)^{m−1} ≥ log(1 + κ/m)·e^L/(1+α)`.

Contrast Part 1, where the same quantity is at most `11/(5n)` no matter what. Here it grows
with the cooling factor, so the cold start is genuinely cold — **but only once that factor
is large enough to beat the `log(1 + κ/m) ≈ κ/m ≈ κ²/(8(n+1)L²)` that the enlarged phase
count costs.** Taking `m·α = 2L` (its value at `m = 8(n+1)L²/κ`) the true exponent is
`≈ κ²e^{2L}/(8(n+1)L²)`, so the crossover against Part 1's `11/(5n)` is

  `e^{2L} ≳ 88(n+1)L²/(5nκ²) ≈ 17.6·L²/κ²`   — essentially dimension-free,

i.e. `L ≈ 7.2` at `κ = log(21/20)/2`, `n = 100`, and `L ≈ 7.3` at `n = 1000`. Below the
crossover the general-`α` schedule is as degenerate as the fixed-rate one. No running-time
claim follows either way. -/
theorem cold_start_exponent_ge_of_coolRate {L κ R : ℝ} (hL : 1 ≤ L) (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    (hrate : ∀ j, σsq (j + 1) = σsq j * (1 + coolRate n L κ))
    (htight : R ^ 2 = 2 * σsq (coolPhases n L κ - 1)
      * Real.log (1 + κ / (coolPhases n L κ : ℝ))) :
    Real.log (1 + κ / (coolPhases n L κ : ℝ)) * Real.exp L / (1 + coolRate n L κ)
      ≤ R ^ 2 / (2 * σsq 0) := by
  set m := coolPhases n L κ with hmdef
  set α := coolRate n L κ with hαdef
  have hm1 : 1 ≤ m := by have := eight_le_coolPhases (n := n) hL hκ0 hκ1; omega
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    linarith
  have hα0 : 0 ≤ α := coolRate_nonneg n L κ
  have hp : (0 : ℝ) < 1 + α := by linarith
  have hlog : 0 ≤ Real.log (1 + κ / (m : ℝ)) :=
    Real.log_nonneg (by have : (0 : ℝ) ≤ κ / (m : ℝ) := by positivity
                        linarith)
  have hpow : (1 + α) ^ (m - 1) * (1 + α) = (1 + α) ^ m := by
    rw [← pow_succ]; congr 1; omega
  have hcool : Real.exp L ≤ (1 + α) ^ m := coolSchedule_total_cooling hL hκ0 hκ1
  have hs0 := hσ 0
  have hsig : σsq (m - 1) = σsq 0 * (1 + α) ^ (m - 1) := sigmaSq_eq_pow hrate (m - 1)
  have hrw : R ^ 2 / (2 * σsq 0) = Real.log (1 + κ / (m : ℝ)) * (1 + α) ^ (m - 1) := by
    rw [htight, hsig]; field_simp
  rw [hrw, div_le_iff₀ hp]
  calc Real.log (1 + κ / (m : ℝ)) * Real.exp L
      ≤ Real.log (1 + κ / (m : ℝ)) * (1 + α) ^ m :=
        mul_le_mul_of_nonneg_left hcool hlog
    _ = Real.log (1 + κ / (m : ℝ)) * (1 + α) ^ (m - 1) * (1 + α) := by rw [← hpow]; ring

/-- **THE ANSWER TO PART 2's CRUX: `hflat` and the two slack conditions ARE jointly
satisfiable under real cooling, with a strictly positive TV error.**

For any cooling requirement `L ≥ 1`, any schedule budget `0 < κ ≤ 1` strictly inside the
algorithm's total budget `V` (`κ < V`), and any body containing the unit ball and of finite
volume, there is a schedule `σsq` at the rate `coolRate n L κ` for which **all** of

* `hsigma` — positivity;
* `hrate` — the cooling rate `coolRate n L κ`;
* `hflat` at *every* index, at the matching constant `log(1 + κ/m)`;
* **the schedule still cools by `e^L`** (`cool_schedule_anneals`);
* a strictly positive variance slack `(V − κ)/m`;
* both slack conditions of `cousinsVempalaOfSamplerCooling`, at a strictly positive TV error

hold simultaneously.

**Why there is no tension, contrary to what the shape of the hypotheses suggests.** `hflat`
is a lower bound on the variances, and the construction places **no upper bound on any
`σᵢ²`** — the two slack thresholds carry `e^{−R²/(2σᵢ²)}` and `e^{−R²/σᵢ²}` and therefore
*grow* as the variances grow. The whole schedule may be scaled up freely, so the flatness
condition costs nothing in consistency. What it costs is *content*: see
`cold_start_exponent_ge_of_coolRate`.

**The one honest gap, inherited unchanged from `exists_pos_tvErr`:** the TV error is
produced per phase index, while `cousinsVempalaOfSamplerCooling` wants a single
`tvErr K ε p` valid for all `i`. That quantifier swap is a pre-existing gap of
`exists_pos_tvErr` and is untouched here. -/
theorem cool_flat_slacks_satisfiable {L κ V : ℝ} (hL : 1 ≤ L) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hκV : κ < V) {K : Set (Space n)}
    (hball : Metric.ball (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤) :
    ∃ σsq : ℕ → ℝ,
      (∀ j, 0 < σsq j) ∧
      (∀ j, σsq (j + 1) = σsq j * (1 + coolRate n L κ)) ∧
      (∀ j, cvRadius K ^ 2
        ≤ 2 * σsq j * Real.log (1 + κ / (coolPhases n L κ : ℝ))) ∧
      Real.exp L * σsq 0 ≤ σsq (coolPhases n L κ) ∧
      0 < (V - κ) / (coolPhases n L κ : ℝ) ∧
      ∀ i : ℕ, ∃ e : ℝ, 0 < e ∧
        Real.exp (cvRadius K ^ 2 / (2 * σsq i)) * e
            ≤ 1 / (6 * (coolPhases n L κ : ℝ))
              * (chain (coolPhases n L κ) σsq (interior K) (i + 1)
                  / chain (coolPhases n L κ) σsq (interior K) i) ∧
        e * (Real.exp (cvRadius K ^ 2 / (2 * σsq i)) ^ 2
              * (1 + 2 * (1 + V / (coolPhases n L κ : ℝ))))
            ≤ (V - κ) / (coolPhases n L κ : ℝ)
              * (chain (coolPhases n L κ) σsq (interior K) (i + 1)
                  / chain (coolPhases n L κ) σsq (interior K) i) ^ 2 := by
  have hm1 : (1 : ℝ) ≤ (coolPhases n L κ : ℝ) := one_le_coolPhases hL hκ0
  have hm0 : (0 : ℝ) < (coolPhases n L κ : ℝ) := by linarith
  have hα0 : 0 ≤ coolRate n L κ := coolRate_nonneg n L κ
  have hq1 : (1 : ℝ) ≤ 1 + coolRate n L κ := by linarith
  have hlog : (0 : ℝ) < Real.log (1 + κ / (coolPhases n L κ : ℝ)) := by
    refine Real.log_pos ?_
    have : (0 : ℝ) < κ / (coolPhases n L κ : ℝ) := by positivity
    linarith
  set c : ℝ := cvRadius K ^ 2 / (2 * Real.log (1 + κ / (coolPhases n L κ : ℝ))) + 1 with hc
  have hc0 : (0 : ℝ) < c := by
    have : (0 : ℝ) ≤ cvRadius K ^ 2 / (2 * Real.log (1 + κ / (coolPhases n L κ : ℝ))) := by
      positivity
    rw [hc]; linarith
  have hσpos : ∀ j, (0 : ℝ) < c * (1 + coolRate n L κ) ^ j := fun j =>
    mul_pos hc0 (pow_pos (by linarith) j)
  have hslack0 : (0 : ℝ) < (V - κ) / (coolPhases n L κ : ℝ) := by
    apply div_pos (by linarith) hm0
  have halg : ∀ l : ℝ, l ≠ 0 →
      2 * (cvRadius K ^ 2 / (2 * l) + 1) * l = cvRadius K ^ 2 + 2 * l := by
    intro l hl; field_simp
  have hflat0 : cvRadius K ^ 2
      ≤ 2 * c * Real.log (1 + κ / (coolPhases n L κ : ℝ)) := by
    rw [hc, halg _ hlog.ne']; linarith
  refine ⟨fun j => c * (1 + coolRate n L κ) ^ j, hσpos,
    fun j => by simp only [pow_succ]; ring, fun j => ?_, ?_, hslack0, fun i => ?_⟩
  · have hp : (1 : ℝ) ≤ (1 + coolRate n L κ) ^ j := one_le_pow₀ hq1
    nlinarith
  · have h := coolSchedule_total_cooling (n := n) hL hκ0 hκ1
    show Real.exp L * (c * (1 + coolRate n L κ) ^ 0)
      ≤ c * (1 + coolRate n L κ) ^ coolPhases n L κ
    rw [pow_zero, mul_one]
    nlinarith
  · obtain ⟨e, he0, hmean, hvar⟩ :=
      exists_pos_tvErr (m := coolPhases n L κ)
        (σsq := fun j => c * (1 + coolRate n L κ) ^ j) hσpos
        (ball_subset_interior hball) (volume_interior_ne_top hfin)
        (R := cvRadius K) (η := 1 / (6 * (coolPhases n L κ : ℝ)))
        (s := (V - κ) / (coolPhases n L κ : ℝ))
        (C := 1 + κ / (coolPhases n L κ : ℝ))
        (by positivity) hslack0 (by positivity) i
    have hCs : (1 : ℝ) + κ / (coolPhases n L κ : ℝ) + (V - κ) / (coolPhases n L κ : ℝ)
        = 1 + V / (coolPhases n L κ : ℝ) := by field_simp; ring
    rw [hCs] at hvar
    exact ⟨e, he0, hmean, hvar⟩

/-- **The remaining budgets of `cousinsVempalaOfSamplerCooling`, at explicit numbers.**
At `ε = 1`, `innerAcc = 1/2`, `meanBias = 1/3`, `varBudget = log(21/20)`,
`schedBudget = log(21/20)/2` and `phaseBias = 1/(6m)`, the three arithmetic side conditions
`hbudget`, `hcompose` and `hphaseBudget` hold — the first two with equality — and the
schedule guards `0 < κ ≤ 1` and `κ < varBudget` hold, so `cool_flat_slacks_satisfiable`
applies. Unlike the fixed-rate `flat_slacks_satisfiable`, **there is no lower bound on `n`**:
the `n ≥ 82` there came from `varSlack = varBudget/2 − 2/n > 0`, i.e. from the fixed-rate
constant `1 + 2/n`, which no longer appears. -/
theorem cool_budgets_at_numbers (n : ℕ) {L : ℝ} (hL : 1 ≤ L) :
    (0 : ℝ) < Real.log (21 / 20) / 2 ∧
    Real.log (21 / 20) / 2 ≤ 1 ∧
    Real.log (21 / 20) / 2 < Real.log (21 / 20) ∧
    Real.exp (Real.log (21 / 20)) - 1 = (1 / 2 : ℝ) ^ 2 / 5 ∧
    (1 / 2 : ℝ) + 1 / 3 + 1 / 2 * (1 / 3) ≤ 1 ∧
    2 * (coolPhases n L (Real.log (21 / 20) / 2) : ℝ)
        * (1 / (6 * (coolPhases n L (Real.log (21 / 20) / 2) : ℝ))) ≤ 1 / 3 := by
  have hlow : (1 : ℝ) / 25 < Real.log (21 / 20) := by
    have h1 : Real.exp ((1 : ℝ) / 25) < 21 / 20 :=
      lt_of_le_of_lt (exp_le_inv_one_sub (by norm_num)) (by norm_num)
    rw [← Real.exp_log (show (0 : ℝ) < 21 / 20 by norm_num)] at h1
    exact Real.exp_lt_exp.mp h1
  have hhigh : Real.log (21 / 20) ≤ 1 / 20 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 21 / 20 by norm_num)
    linarith
  have hκ0 : (0 : ℝ) < Real.log (21 / 20) / 2 := by linarith
  have hm1 : (1 : ℝ) ≤ (coolPhases n L (Real.log (21 / 20) / 2) : ℝ) :=
    one_le_coolPhases hL hκ0
  refine ⟨hκ0, by linarith, by linarith, ?_, by norm_num, ?_⟩
  · rw [Real.exp_log (show (0 : ℝ) < 21 / 20 by norm_num)]; norm_num
  · have hm0 : (0 : ℝ) < (coolPhases n L (Real.log (21 / 20) / 2) : ℝ) := by linarith
    field_simp
    norm_num

end Sampler

end CV

/-! ## Building a `Ttc.VolumeAlgorithm`

Two constructions. The first is complete mathematics with implementation-level data:
given runs that are correct at the *fixed* confidence `4/5`, it produces the interface at
*every* confidence `1 − p`. The second feeds the §5.2 telescope into the first, and its
hypotheses are the development's residual debt on the volume oracle. -/

/-- **The median-boost construction.** A family of independent runs, each correct to
relative error `ε` with probability `4/5`, together with a measurable median of them, is
a `Ttc.VolumeAlgorithm n`.

Every field is discharged: `est` is the median, `est_meas` is `hmed_meas`, and `correct`
is `Ttc.CV.median_relErr_ge`, i.e. `Arlib.GaussianCooling.median_boost` at the
`O(log (1/p))` repetition rate. The amplification `4/5 → 1 − p` is the content; `hgood`
is *not* the conclusion, since the conclusion quantifies over every confidence `p` and
`hgood` holds at one fixed confidence.

`med` is data rather than a construction because any tie-breaking rule works:
`Arlib.GaussianCooling.median_mem_of_majority` is stated for *every* median. -/
noncomputable def VolumeAlgorithm.ofRuns (n : ℕ) (Ω : Type) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (reps : ℝ → ℝ → ℕ)
    (run : Set (Space n) → ℝ → ℝ → ℕ → Ω → ℝ)
    (med : Set (Space n) → ℝ → ℝ → Ω → ℝ)
    (hreps_pos : ∀ ε p, 0 < p → p < 1 → 0 < reps ε p)
    (hreps : ∀ ε p, 0 < p → p < 1 →
      Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2) ≤ (reps ε p : ℝ))
    (hrun_meas : ∀ K ε p j, Measurable (run K ε p j))
    (hmed_meas : ∀ K ε p, Measurable (med K ε p))
    (hmed : ∀ K ε p ω,
      IsMedian (fun j : Fin (reps ε p) => run K ε p (j : ℕ) ω) (med K ε p ω))
    (hindep : ∀ K ε p, iIndepFun (fun j : Fin (reps ε p) => run K ε p (j : ℕ)) μ)
    (hgood : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j : Fin (reps ε p),
      4 / 5 ≤ μ.real {ω | run K ε p (j : ℕ) ω ∈ relErr ε (volume K).toReal}) :
    VolumeAlgorithm n where
  Ω := Ω
  mΩ := mΩ
  μ := μ
  isProb := inferInstance
  est := med
  est_meas := fun K ε p => hmed_meas K ε p
  correct := fun K ε p hε hp hp1 hconv hball hfin =>
    CV.median_relErr_ge (hreps_pos ε p hp hp1) (fun j => hrun_meas K ε p (j : ℕ))
      (hindep K ε p) (hmed K ε p) (hgood K ε p hε hp hp1 hconv hball hfin) hp
      (hreps ε p hp hp1)

/-- **Cousins–Vempala Theorem 1.1 from §5.2, with the debt in the type.**

The estimate on body `K` at accuracy `ε` and confidence `p` is the median of
`reps ε p` independent runs, each run being `chain K ε p 0 · ∏ᵢ W K ε p j i` — the
cold-start value times the telescoping product of the per-phase ratio estimators. The
construction is complete: it produces a `Ttc.VolumeAlgorithm n`. What it takes on trust is
listed below, and this is exactly what the development still owes.

**Mathematical debt (four hypotheses).**

* `hphase_mean` — each phase's score is unbiased for `G(σᵢ₊₁²)/G(σᵢ²)`. This is the
  *sampler*: it presumes a draw from the logconcave density `∝ 1_K(x)e^{−‖x‖²/(2σᵢ²)}`.
  Blocked on isoperimetry for logconcave densities → conductance → mixing of the ball
  walk, none of which is proved in this development.
* `hphase_var` — each phase's score has relative second moment `1 + κ/m`. §5.1 proves the
  corresponding statement about the *ideal* estimator unconditionally
  (`Arlib.GaussianCooling.fixed_var_bound_ratio_indicator`: `E(Y²)/E(Y)² ≤ 1 + 2/n` for
  the indicator of a convex body, with `ZLogconcaveHypothesis` discharged); transporting
  it to the sampled score again needs the sampler.
* `hphase_indep` — the `m` phases use independent randomness.
* `hchain_end` — the last Gaussian integrates *exactly* to `Vol(K)`. This is an
  idealization, and it is the one hypothesis here that has since been removed: under the
  radius hypothesis `K ⊆ R·Bₙ`, `Ttc.CV.G_indicator_mem_relErr` proves the true statement
  `G(s) ∈ (1 ± (1 − e^{−R²/(2s)}))·Vol(K)`, and
  `Ttc.VolumeAlgorithm.cousinsVempalaOfBiasedEnd` is this same construction taking that
  instead. Prefer that one; this exact form is kept because it is what the downstream
  files already reference.

**Scheduling and admissibility (the rest).** `hreps_pos`, `hreps` fix the repetition
count; `hbudget0`, `hbudget` fix the variance budget; `hW_meas`, `hmed_meas`, `hmed`,
`hindep_runs`, `hprodLp`, `hchain_pos` are measurability, median-selection, independence
and integrability guards.

**Non-vacuity** (`CLAUDE.md` §11): `Ttc.VolumeAlgorithm.cousinsVempalaWitness` instantiates
every argument below and proves every hypothesis, so this bundle is satisfiable. -/
noncomputable def VolumeAlgorithm.cousinsVempala (n : ℕ) (Ω : Type)
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (phases : Set (Space n) → ℝ → ℝ → ℕ)
    (reps : ℝ → ℝ → ℕ)
    (varBudget : ℝ → ℝ)
    (chain : Set (Space n) → ℝ → ℝ → ℕ → ℝ)
    (W : Set (Space n) → ℝ → ℝ → ℕ → ℕ → Ω → ℝ)
    (med : Set (Space n) → ℝ → ℝ → Ω → ℝ)
    -- the schedule
    (hreps_pos : ∀ ε p, 0 < p → p < 1 → 0 < reps ε p)
    (hreps : ∀ ε p, 0 < p → p < 1 →
      Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2) ≤ (reps ε p : ℝ))
    (hbudget0 : ∀ ε, 0 < ε → 0 ≤ varBudget ε)
    (hbudget : ∀ ε, 0 < ε → Real.exp (varBudget ε) - 1 ≤ ε ^ 2 / 5)
    -- admissibility
    (hW_meas : ∀ K ε p j i, Measurable (W K ε p j i))
    (hmed_meas : ∀ K ε p, Measurable (med K ε p))
    (hmed : ∀ K ε p ω, IsMedian (fun j : Fin (reps ε p) =>
      chain K ε p 0 * ∏ i : Fin (phases K ε p), W K ε p (j : ℕ) (i : ℕ) ω) (med K ε p ω))
    (hindep_runs : ∀ K ε p, iIndepFun (fun (j : Fin (reps ε p)) (ω : Ω) =>
      chain K ε p 0 * ∏ i : Fin (phases K ε p), W K ε p (j : ℕ) (i : ℕ) ω) μ)
    (hprodLp : ∀ K ε p j,
      MemLp (fun ω => ∏ i : Fin (phases K ε p), W K ε p j (i : ℕ) ω) 2 μ)
    -- the cooling chain and the per-phase ratio estimators
    (hchain_pos : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ i, 0 < chain K ε p i)
    (hchain_end : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      chain K ε p (phases K ε p) = (volume K).toReal)
    (hphase_indep : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j,
      iIndepFun (fun i : Fin (phases K ε p) => W K ε p j (i : ℕ)) μ)
    (hphase_mean : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j (i : Fin (phases K ε p)),
      ∫ ω, W K ε p j (i : ℕ) ω ∂μ = chain K ε p ((i : ℕ) + 1) / chain K ε p (i : ℕ))
    (hphase_var : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j (i : Fin (phases K ε p)),
      ∫ ω, (W K ε p j (i : ℕ) ω) ^ 2 ∂μ
        ≤ (1 + varBudget ε / (phases K ε p : ℝ)) * (∫ ω, W K ε p j (i : ℕ) ω ∂μ) ^ 2) :
    VolumeAlgorithm n :=
  VolumeAlgorithm.ofRuns n Ω μ reps
    (fun K ε p j ω => chain K ε p 0 * ∏ i : Fin (phases K ε p), W K ε p j (i : ℕ) ω)
    med hreps_pos hreps
    (fun K ε p j =>
      measurable_const.mul (Finset.measurable_prod _ fun i _ => hW_meas K ε p j (i : ℕ)))
    hmed_meas hmed hindep_runs
    (fun K ε p hε hp hp1 hconv hball hfin j => by
      have h := CV.run_relErr_four_fifths (μ := μ)
        (W := fun i : Fin (phases K ε p) => W K ε p (j : ℕ) (i : ℕ))
        (A := chain K ε p) (κ := varBudget ε) (ε := ε) (hbudget0 ε hε) hε
        (hphase_indep K ε p hε hp hp1 hconv hball hfin (j : ℕ))
        (fun i => (hW_meas K ε p (j : ℕ) (i : ℕ)).aestronglyMeasurable)
        (hprodLp K ε p (j : ℕ))
        (hchain_pos K ε p hε hp hp1 hconv hball hfin)
        (hphase_mean K ε p hε hp hp1 hconv hball hfin (j : ℕ))
        (hphase_var K ε p hε hp hp1 hconv hball hfin (j : ℕ))
        (hbudget ε hε)
      rwa [hchain_end K ε p hε hp hp1 hconv hball hfin] at h)

/-- **The same construction with the endpoint idealization removed.**

**Not needed for `Arlib`'s cooling schedule — see the caveat at the end.**

`Ttc.VolumeAlgorithm.cousinsVempala` asks for `chain K ε p (phases K ε p) = Vol(K)` on the
nose. For a schedule whose terminal phase is still a genuine Gaussian, the last entry is
*not* `Vol(K)`: by `Ttc.CV.G_indicator_mem_relErr` it is `Vol(K)` up to a relative bias
`η(s) = 1 − e^{−R²/(2s)}` on a body inside `R·Bₙ`, and that bias is strictly positive for
every finite `s`. So for such a schedule the exact hypothesis is (presumably — the strict
inequality `G(s) < Vol(K)` is not formalized here) not the one the algorithm can supply,
and this construction takes the honest one instead:

* `hchain_end` becomes `chain K ε p (phases K ε p) ∈ relErr (endBias ε) Vol(K)`,
  which is `G_indicator_mem_relErr` with `endBias ε = 1 − e^{−R²/(2σ_m²)}`;
* the runs are computed at an *inner* accuracy `innerAcc ε`, and `hcompose` is the
  scheduling condition `innerAcc ε + endBias ε + innerAcc ε · endBias ε ≤ ε` that makes the
  composed error meet the requested `ε` (`Ttc.CV.relErr_trans`). It is satisfiable for
  every `ε > 0` — e.g. `endBias ε = ε/4`, `innerAcc ε = ε/2` — and `endBias ε` can be
  driven below any target by flattening the last Gaussian (`s → ∞`);
* `hbudget` is correspondingly stated at `innerAcc ε`.

The remaining debt is unchanged and is still the sampler: `hphase_mean`.

**Caveat — this variant is unnecessary for the schedule actually used.**
`Arlib.GaussianCooling.coolWeight` sets the terminal weight to the *literal constant* `1`
(`Chain.lean:144`), not to a Gaussian, and `Chain.lean:141-143` records that as a
deliberate design choice made for precisely this reason. Consequently
`Arlib.GaussianCooling.chain_end` (`Chain.lean:257`) gives
`chain m σsq K m = Vol(K)` **exactly and with no side conditions whatsoever** — no
convexity, no `volume K ≠ ⊤`, no radius bound `K ⊆ R·Bₙ`. So for that chain the exact
`hchain_end` of `cousinsVempala` is simply available, and
`Ttc.VolumeAlgorithm.cousinsVempalaOfSchedule` (`Ttc/Volume/CVInstantiate.lean`) supplies
it. This construction is retained for schedules that do end on a genuine Gaussian; it is
not on the path to the volume oracle. -/
noncomputable def VolumeAlgorithm.cousinsVempalaOfBiasedEnd (n : ℕ) (Ω : Type)
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (phases : Set (Space n) → ℝ → ℝ → ℕ)
    (reps : ℝ → ℝ → ℕ)
    (varBudget : ℝ → ℝ)
    (innerAcc : ℝ → ℝ)
    (endBias : ℝ → ℝ)
    (chain : Set (Space n) → ℝ → ℝ → ℕ → ℝ)
    (W : Set (Space n) → ℝ → ℝ → ℕ → ℕ → Ω → ℝ)
    (med : Set (Space n) → ℝ → ℝ → Ω → ℝ)
    -- the schedule
    (hreps_pos : ∀ ε p, 0 < p → p < 1 → 0 < reps ε p)
    (hreps : ∀ ε p, 0 < p → p < 1 →
      Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2) ≤ (reps ε p : ℝ))
    (hbudget0 : ∀ ε, 0 < ε → 0 ≤ varBudget ε)
    (hinner_pos : ∀ ε, 0 < ε → 0 < innerAcc ε)
    (hbias_nonneg : ∀ ε, 0 < ε → 0 ≤ endBias ε)
    (hcompose : ∀ ε, 0 < ε → innerAcc ε + endBias ε + innerAcc ε * endBias ε ≤ ε)
    (hbudget : ∀ ε, 0 < ε → Real.exp (varBudget ε) - 1 ≤ (innerAcc ε) ^ 2 / 5)
    -- admissibility
    (hW_meas : ∀ K ε p j i, Measurable (W K ε p j i))
    (hmed_meas : ∀ K ε p, Measurable (med K ε p))
    (hmed : ∀ K ε p ω, IsMedian (fun j : Fin (reps ε p) =>
      chain K ε p 0 * ∏ i : Fin (phases K ε p), W K ε p (j : ℕ) (i : ℕ) ω) (med K ε p ω))
    (hindep_runs : ∀ K ε p, iIndepFun (fun (j : Fin (reps ε p)) (ω : Ω) =>
      chain K ε p 0 * ∏ i : Fin (phases K ε p), W K ε p (j : ℕ) (i : ℕ) ω) μ)
    (hprodLp : ∀ K ε p j,
      MemLp (fun ω => ∏ i : Fin (phases K ε p), W K ε p j (i : ℕ) ω) 2 μ)
    -- the cooling chain and the per-phase ratio estimators
    (hchain_pos : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ i, 0 < chain K ε p i)
    (hchain_end : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      chain K ε p (phases K ε p) ∈ relErr (endBias ε) (volume K).toReal)
    (hphase_indep : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j,
      iIndepFun (fun i : Fin (phases K ε p) => W K ε p j (i : ℕ)) μ)
    (hphase_mean : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j (i : Fin (phases K ε p)),
      ∫ ω, W K ε p j (i : ℕ) ω ∂μ = chain K ε p ((i : ℕ) + 1) / chain K ε p (i : ℕ))
    (hphase_var : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j (i : Fin (phases K ε p)),
      ∫ ω, (W K ε p j (i : ℕ) ω) ^ 2 ∂μ
        ≤ (1 + varBudget ε / (phases K ε p : ℝ)) * (∫ ω, W K ε p j (i : ℕ) ω ∂μ) ^ 2) :
    VolumeAlgorithm n :=
  VolumeAlgorithm.ofRuns n Ω μ reps
    (fun K ε p j ω => chain K ε p 0 * ∏ i : Fin (phases K ε p), W K ε p j (i : ℕ) ω)
    med hreps_pos hreps
    (fun K ε p j =>
      measurable_const.mul (Finset.measurable_prod _ fun i _ => hW_meas K ε p j (i : ℕ)))
    hmed_meas hmed hindep_runs
    (fun K ε p hε hp hp1 hconv hball hfin j =>
      CV.run_relErr_four_fifths_biasedEnd (μ := μ)
        (W := fun i : Fin (phases K ε p) => W K ε p (j : ℕ) (i : ℕ))
        (A := chain K ε p) (κ := varBudget ε) (ε := innerAcc ε) (ε₀ := ε)
        (η := endBias ε) (b := (volume K).toReal)
        (hbudget0 ε hε) (hinner_pos ε hε) (hbias_nonneg ε hε) ENNReal.toReal_nonneg
        (hphase_indep K ε p hε hp hp1 hconv hball hfin (j : ℕ))
        (fun i => (hW_meas K ε p (j : ℕ) (i : ℕ)).aestronglyMeasurable)
        (hprodLp K ε p (j : ℕ))
        (hchain_pos K ε p hε hp hp1 hconv hball hfin)
        (hphase_mean K ε p hε hp hp1 hconv hball hfin (j : ℕ))
        (hphase_var K ε p hε hp hp1 hconv hball hfin (j : ℕ))
        (hbudget ε hε)
        (hchain_end K ε p hε hp hp1 hconv hball hfin)
        (hcompose ε hε))

/-- **The construction with `hphase_mean` weakened to a relative bound.**

Identical to `Ttc.VolumeAlgorithm.cousinsVempala` except that the per-phase score is only
required to have mean *within a relative `phaseBias K ε p`* of the chain ratio, rather than
equal to it. That is the honest shape: an equality is unattainable for a sampled score, and
`Ttc.CV.run_relErr_four_fifths_approxMean` is the run bound that tolerates the bias.

The price is bookkeeping, all of it explicit:

* `hphaseBudget` — the per-phase budget `2·m·phaseBias ≤ meanBias ε`, i.e. the per-phase
  bias must be `Θ(τ/m)`, not `Θ(τ)`. This is `Arlib.GaussianCooling.phaseBias_le`, and the
  `m` is not cosmetic: the per-phase errors multiply.
* `hcompose` — the accuracy split `innerAcc ε + meanBias ε + innerAcc ε · meanBias ε ≤ ε`
  (`Ttc.CV.relErr_trans`), satisfiable for every `ε > 0` by e.g. `innerAcc ε = ε/2`,
  `meanBias ε = ε/4`, which asks each phase for `phaseBias ≤ ε/(8m)`.
* `hbudget` is stated at the *inner* accuracy `innerAcc ε`.

`hphase_var` is still an argument here; `Ttc.VolumeAlgorithm.cousinsVempalaOfSampler`
discharges both it and `hphase_mean`. -/
noncomputable def VolumeAlgorithm.cousinsVempalaOfApproxMean (n : ℕ) (Ω : Type)
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (phases : Set (Space n) → ℝ → ℝ → ℕ)
    (reps : ℝ → ℝ → ℕ)
    (varBudget : ℝ → ℝ)
    (innerAcc : ℝ → ℝ)
    (meanBias : ℝ → ℝ)
    (phaseBias : Set (Space n) → ℝ → ℝ → ℝ)
    (chain : Set (Space n) → ℝ → ℝ → ℕ → ℝ)
    (W : Set (Space n) → ℝ → ℝ → ℕ → ℕ → Ω → ℝ)
    (med : Set (Space n) → ℝ → ℝ → Ω → ℝ)
    -- the schedule
    (hreps_pos : ∀ ε p, 0 < p → p < 1 → 0 < reps ε p)
    (hreps : ∀ ε p, 0 < p → p < 1 →
      Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2) ≤ (reps ε p : ℝ))
    (hbudget0 : ∀ ε, 0 < ε → 0 ≤ varBudget ε)
    (hinner_pos : ∀ ε, 0 < ε → 0 < innerAcc ε)
    (hbias_nonneg : ∀ K ε p, 0 < ε → 0 ≤ phaseBias K ε p)
    (hmean_nonneg : ∀ ε, 0 < ε → 0 ≤ meanBias ε)
    (hmean_lt_one : ∀ ε, 0 < ε → meanBias ε < 1)
    (hphases_pos : ∀ K ε p, 0 < ε → 0 < phases K ε p)
    (hphaseBudget : ∀ K ε p, 0 < ε →
      2 * (phases K ε p : ℝ) * phaseBias K ε p ≤ meanBias ε)
    (hcompose : ∀ ε, 0 < ε → innerAcc ε + meanBias ε + innerAcc ε * meanBias ε ≤ ε)
    (hbudget : ∀ ε, 0 < ε → Real.exp (varBudget ε) - 1 ≤ (innerAcc ε) ^ 2 / 5)
    -- admissibility
    (hW_meas : ∀ K ε p j i, Measurable (W K ε p j i))
    (hmed_meas : ∀ K ε p, Measurable (med K ε p))
    (hmed : ∀ K ε p ω, IsMedian (fun j : Fin (reps ε p) =>
      chain K ε p 0 * ∏ i : Fin (phases K ε p), W K ε p (j : ℕ) (i : ℕ) ω) (med K ε p ω))
    (hindep_runs : ∀ K ε p, iIndepFun (fun (j : Fin (reps ε p)) (ω : Ω) =>
      chain K ε p 0 * ∏ i : Fin (phases K ε p), W K ε p (j : ℕ) (i : ℕ) ω) μ)
    (hprodLp : ∀ K ε p j,
      MemLp (fun ω => ∏ i : Fin (phases K ε p), W K ε p j (i : ℕ) ω) 2 μ)
    -- the cooling chain and the per-phase ratio estimators
    (hchain_pos : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ i, 0 < chain K ε p i)
    (hchain_end : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      chain K ε p (phases K ε p) = (volume K).toReal)
    (hphase_indep : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j,
      iIndepFun (fun i : Fin (phases K ε p) => W K ε p j (i : ℕ)) μ)
    -- ★ the only mathematical change: an interval, not an equality
    (hphase_mean : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j (i : Fin (phases K ε p)),
      ∫ ω, W K ε p j (i : ℕ) ω ∂μ ∈
        relErr (phaseBias K ε p) (chain K ε p ((i : ℕ) + 1) / chain K ε p (i : ℕ)))
    (hphase_var : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j (i : Fin (phases K ε p)),
      ∫ ω, (W K ε p j (i : ℕ) ω) ^ 2 ∂μ
        ≤ (1 + varBudget ε / (phases K ε p : ℝ)) * (∫ ω, W K ε p j (i : ℕ) ω ∂μ) ^ 2) :
    VolumeAlgorithm n :=
  VolumeAlgorithm.ofRuns n Ω μ reps
    (fun K ε p j ω => chain K ε p 0 * ∏ i : Fin (phases K ε p), W K ε p j (i : ℕ) ω)
    med hreps_pos hreps
    (fun K ε p j =>
      measurable_const.mul (Finset.measurable_prod _ fun i _ => hW_meas K ε p j (i : ℕ)))
    hmed_meas hmed hindep_runs
    (fun K ε p hε hp hp1 hconv hball hfin j => by
      have h := CV.run_relErr_four_fifths_approxMean (μ := μ)
        (W := fun i : Fin (phases K ε p) => W K ε p (j : ℕ) (i : ℕ))
        (A := chain K ε p) (κ := varBudget ε) (ε := innerAcc ε) (ε₀ := ε)
        (η := phaseBias K ε p) (τ := meanBias ε)
        (hphases_pos K ε p hε) (hbudget0 ε hε) (hinner_pos ε hε) (hbias_nonneg K ε p hε)
        (hmean_nonneg ε hε) (hmean_lt_one ε hε) (hphaseBudget K ε p hε)
        (hphase_indep K ε p hε hp hp1 hconv hball hfin (j : ℕ))
        (fun i => (hW_meas K ε p (j : ℕ) (i : ℕ)).aestronglyMeasurable)
        (hprodLp K ε p (j : ℕ))
        (hchain_pos K ε p hε hp hp1 hconv hball hfin)
        (hphase_mean K ε p hε hp hp1 hconv hball hfin (j : ℕ))
        (hphase_var K ε p hε hp hp1 hconv hball hfin (j : ℕ))
        (hbudget ε hε) (hcompose ε hε)
      rwa [hchain_end K ε p hε hp hp1 hconv hball hfin] at h)

/-- **§5.2 driven by a sampler: `hphase_mean` and `hphase_var` are no longer arguments.**

This is `Ttc.VolumeAlgorithm.cousinsVempalaOfApproxMean` with the cooling chain, the phase
score, the per-phase mean bound and the per-phase second-moment bound all **supplied**,
from three inputs that the previous constructions did not have:

1. **an explicit radius** `radius K`, with `0 < radius K` and (under `cousinsVempala`'s own
   hypotheses on `K`) `K ⊆ radius K · Bₙ`. It is unavoidable: the phase score
   `Arlib.GaussianCooling.coolRatio` is unbounded on an unbounded body, so the
   total-variation transport has no bound `B` to rescale by. `Ttc.CV.cvRadius` /
   `Ttc.CV.subset_closedBall_cvRadius` supply one from `cousinsVempala`'s hypotheses alone,
   so this input costs nothing in generality;
2. **a sampler** `X K ε p j i : Ω → ℝⁿ` with the guarantee `hTV` that the law of the phase
   sample is within total variation `tvErr K ε p` of the *exact* phase law
   `Arlib.GaussianCooling.coolLaw`. Nothing here proves any chain achieves such a bound —
   `hTV` is an input, and producing it is the ball-walk mixing problem;
3. **the exact-law second moment** `hvar_exact`, `E_π(W²) ≤ varConst ε · E_π(W)²`. For an
   interior phase of the fixed-rate schedule this is a *theorem*,
   `Arlib.GaussianCooling.coolLaw_sq_moment_le` with `varConst = 1 + 2/n` — see the
   obstruction note below.

**The body is `interior K`, not `K`.** A convex set need not be Borel measurable (an open
ball together with an arbitrary subset of its bounding sphere is convex), so a hypothesis
`∀ K, Convex ℝ K → … → MeasurableSet K` would be *false* and any construction carrying it
would be vacuous. `interior K` is open, convex, contains the unit ball whenever `K` does,
and has the same volume (`Ttc.CV.volume_interior_eq`, from `Convex.addHaar_frontier`), so
the whole pipeline runs on it and still reports about `volume K`.

**What is derived here** (was an argument of `cousinsVempala`): `hchain_pos`
(`Arlib.GaussianCooling.chain_pos`), `hchain_end` (`chain_end` plus `volume_interior_eq`),
`hW_meas` (`measurable_phaseScore`), `hphase_mean` (`Ttc.CV.sampledPhase_mean_mem_relErr`)
and `hphase_var` (`Arlib.GaussianCooling.sq_moment_le_of_tvLe_map`).

**What is still an argument.** The scheduling data and its budgets; the independence and
`L²` guards (`hphase_indep`, `hindep_runs`, `hprodLp`, `hmed`, `hmed_meas`); the two slack
conditions `hslack_mean`, `hslack_var` relating `tvErr` to the radius; and `hvar_exact`.

**Satisfiability of (1) and (2) together.** Both slack conditions are upper bounds on the
single number `(tvErr K ε p).toReal`, with strictly positive right-hand sides whenever the
chain ratio, `phaseBias` and `varSlack` are positive — see `Ttc.CV.tv_slacks_satisfiable`
and `Ttc.CV.tv_slack_threshold_pos`. So they are simultaneously satisfiable, at a
*strictly positive* TV error; the threshold degrades like `e^{−R²/σᵢ²}`.

**The obstruction, and what this does NOT claim.** `hvar_exact` at the fixed cooling rate
`σᵢ₊₁² = σᵢ²(1 + 1/n)` holds with `varConst = 1 + 2/n`
(`Arlib.GaussianCooling.coolLaw_sq_moment_le`), but only at *interior* phases, and
`hvarSum` then forces `2m ≤ n·varBudget ε`, which by
`Arlib.GaussianCooling.geomSchedule_total_cooling_lt` makes the schedule's **total** cooling
factor `(1 + 1/n)^m < 11/10` — it cannot anneal. A schedule that does anneal needs the
general-`α` variance bound, which is not constructed anywhere in this development. So this
construction is a *reduction* of the volume oracle to a sampler and a schedule, not a
volume oracle; and nothing here bounds any running time. The conductance constants
available in this repository are exponentially small in `n`
(`Arlib/Convexity/GaussianCooling/Unblock.lean`), so no polynomial-time claim is implied
by anything above. -/
noncomputable def VolumeAlgorithm.cousinsVempalaOfSampler (n : ℕ) (Ω : Type)
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    -- the schedule data
    (phases : Set (Space n) → ℝ → ℝ → ℕ)
    (reps : ℝ → ℝ → ℕ)
    (varBudget : ℝ → ℝ)
    (innerAcc : ℝ → ℝ)
    (meanBias : ℝ → ℝ)
    (varConst : ℝ → ℝ)
    (phaseBias : Set (Space n) → ℝ → ℝ → ℝ)
    (varSlack : Set (Space n) → ℝ → ℝ → ℝ)
    (σsq : Set (Space n) → ℝ → ℝ → ℕ → ℝ)
    -- ★ (1) the explicit radius
    (radius : Set (Space n) → ℝ)
    -- ★ (2) the sampler and its total-variation error
    (tvErr : Set (Space n) → ℝ → ℝ → ℝ≥0∞)
    (X : Set (Space n) → ℝ → ℝ → ℕ → ℕ → Ω → Space n)
    (med : Set (Space n) → ℝ → ℝ → Ω → ℝ)
    -- the schedule's budgets
    (hreps_pos : ∀ ε p, 0 < p → p < 1 → 0 < reps ε p)
    (hreps : ∀ ε p, 0 < p → p < 1 →
      Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2) ≤ (reps ε p : ℝ))
    (hbudget0 : ∀ ε, 0 < ε → 0 ≤ varBudget ε)
    (hinner_pos : ∀ ε, 0 < ε → 0 < innerAcc ε)
    (hbias_nonneg : ∀ K ε p, 0 < ε → 0 ≤ phaseBias K ε p)
    (hmean_nonneg : ∀ ε, 0 < ε → 0 ≤ meanBias ε)
    (hmean_lt_one : ∀ ε, 0 < ε → meanBias ε < 1)
    (hphases_pos : ∀ K ε p, 0 < ε → 0 < phases K ε p)
    (hphaseBudget : ∀ K ε p, 0 < ε →
      2 * (phases K ε p : ℝ) * phaseBias K ε p ≤ meanBias ε)
    (hcompose : ∀ ε, 0 < ε → innerAcc ε + meanBias ε + innerAcc ε * meanBias ε ≤ ε)
    (hbudget : ∀ ε, 0 < ε → Real.exp (varBudget ε) - 1 ≤ (innerAcc ε) ^ 2 / 5)
    (hsigma : ∀ K ε p j, 0 < σsq K ε p j)
    -- ★ (1) the radius hypotheses
    (hradius_pos : ∀ K, 0 < radius K)
    (hradius : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      K ⊆ Metric.closedBall (0 : Space n) (radius K))
    -- ★ (2) the sampler hypotheses
    (hX_meas : ∀ K ε p j i, Measurable (X K ε p j i))
    (htvErr_ne_top : ∀ K ε p, tvErr K ε p ≠ ⊤)
    (hTV : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j i,
      Arlib.TVLe (μ.map (X K ε p j i))
        (coolLaw (phases K ε p) (σsq K ε p) (interior K) i) (tvErr K ε p))
    -- the slack the radius and the TV error must leave: the mean side
    (hslack_mean : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ i,
      Real.exp (radius K ^ 2 / (2 * σsq K ε p i)) * (tvErr K ε p).toReal
        ≤ phaseBias K ε p * (chain (phases K ε p) (σsq K ε p) (interior K) (i + 1)
            / chain (phases K ε p) (σsq K ε p) (interior K) i))
    -- the exact-law second moment, and the room left above it
    (hvarConst_nonneg : ∀ ε, 0 < ε → 0 ≤ varConst ε)
    (hvarSlack_nonneg : ∀ K ε p, 0 < ε → 0 ≤ varSlack K ε p)
    (hvarSum : ∀ K ε p, 0 < ε →
      varConst ε + varSlack K ε p = 1 + varBudget ε / (phases K ε p : ℝ))
    (hvar_exact : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ i,
      ∫ x, phaseScore (phases K ε p) (σsq K ε p) (interior K) i x ^ 2
          ∂(coolLaw (phases K ε p) (σsq K ε p) (interior K) i)
        ≤ varConst ε * (∫ x, phaseScore (phases K ε p) (σsq K ε p) (interior K) i x
            ∂(coolLaw (phases K ε p) (σsq K ε p) (interior K) i)) ^ 2)
    -- the slack the radius and the TV error must leave: the variance side
    (hslack_var : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ i,
      (tvErr K ε p).toReal * (Real.exp (radius K ^ 2 / (2 * σsq K ε p i)) ^ 2
          * (1 + 2 * (1 + varBudget ε / (phases K ε p : ℝ))))
        ≤ varSlack K ε p * (chain (phases K ε p) (σsq K ε p) (interior K) (i + 1)
            / chain (phases K ε p) (σsq K ε p) (interior K) i) ^ 2)
    -- admissibility
    (hmed_meas : ∀ K ε p, Measurable (med K ε p))
    (hmed : ∀ K ε p ω, IsMedian (fun j : Fin (reps ε p) =>
      chain (phases K ε p) (σsq K ε p) (interior K) 0 *
        ∏ i : Fin (phases K ε p),
          phaseScore (phases K ε p) (σsq K ε p) (interior K) (i : ℕ)
            (X K ε p (j : ℕ) (i : ℕ) ω)) (med K ε p ω))
    (hindep_runs : ∀ K ε p, iIndepFun (fun (j : Fin (reps ε p)) (ω : Ω) =>
      chain (phases K ε p) (σsq K ε p) (interior K) 0 *
        ∏ i : Fin (phases K ε p),
          phaseScore (phases K ε p) (σsq K ε p) (interior K) (i : ℕ)
            (X K ε p (j : ℕ) (i : ℕ) ω)) μ)
    (hprodLp : ∀ K ε p j, MemLp (fun ω => ∏ i : Fin (phases K ε p),
      phaseScore (phases K ε p) (σsq K ε p) (interior K) (i : ℕ)
        (X K ε p j (i : ℕ) ω)) 2 μ)
    (hphase_indep : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j,
      iIndepFun (fun i : Fin (phases K ε p) => fun ω =>
        phaseScore (phases K ε p) (σsq K ε p) (interior K) (i : ℕ)
          (X K ε p j (i : ℕ) ω)) μ) :
    VolumeAlgorithm n :=
  VolumeAlgorithm.cousinsVempalaOfApproxMean n Ω μ phases reps varBudget innerAcc meanBias
    phaseBias
    (fun K ε p => chain (phases K ε p) (σsq K ε p) (interior K))
    (fun K ε p j i ω =>
      phaseScore (phases K ε p) (σsq K ε p) (interior K) i (X K ε p j i ω))
    med
    hreps_pos hreps hbudget0 hinner_pos hbias_nonneg hmean_nonneg hmean_lt_one hphases_pos
    hphaseBudget hcompose hbudget
    -- `hW_meas`: the phase score is measurable on the *open* body `interior K`
    (fun K ε p j i =>
      (measurable_phaseScore isOpen_interior.measurableSet i).comp (hX_meas K ε p j i))
    hmed_meas hmed hindep_runs hprodLp
    -- `hchain_pos`
    (fun K ε p _ _ _ _ hball hfin i =>
      chain_pos (hsigma K ε p) (CV.ball_subset_interior hball)
        (CV.volume_interior_ne_top hfin) i)
    -- `hchain_end`
    (fun K ε p _ _ _ hconv _ _ => by
      rw [chain_end, CV.volume_interior_eq hconv])
    hphase_indep
    -- ★ `hphase_mean`, DERIVED from the sampler's TV guarantee
    (fun K ε p hε hp hp1 hconv hball hfin j i =>
      CV.sampledPhase_mean_mem_relErr (hsigma K ε p) isOpen_interior.measurableSet
        (CV.ball_subset_interior hball) (CV.volume_interior_ne_top hfin)
        (interior_subset.trans (hradius K ε p hε hp hp1 hconv hball hfin))
        (hX_meas K ε p j (i : ℕ))
        (hTV K ε p hε hp hp1 hconv hball hfin j (i : ℕ)) (htvErr_ne_top K ε p)
        (hslack_mean K ε p hε hp hp1 hconv hball hfin (i : ℕ)))
    -- ★ `hphase_var`, DERIVED from the sampler's TV guarantee and `hvar_exact`
    (fun K ε p hε hp hp1 hconv hball hfin j i => by
      have hKm : MeasurableSet (interior K) := isOpen_interior.measurableSet
      have hball' := CV.ball_subset_interior hball
      have hfin' := CV.volume_interior_ne_top hfin
      have hchain := chain_pos (m := phases K ε p) (hsigma K ε p) hball' hfin' (i : ℕ)
      haveI := coolLaw_isProbabilityMeasure (m := phases K ε p) (hsigma K ε p) hball' hfin'
        (i : ℕ)
      have hmeanEq := integral_phaseScore_coolLaw (m := phases K ε p)
        (σsq := σsq K ε p) hKm hchain
      have hsl := hslack_var K ε p hε hp hp1 hconv hball hfin (i : ℕ)
      rw [← hvarSum K ε p hε, ← hmeanEq] at hsl
      have hmain := sq_moment_le_of_tvLe_map (C := varConst ε) (s := varSlack K ε p)
        (hX_meas K ε p j (i : ℕ)) (hTV K ε p hε hp hp1 hconv hball hfin j (i : ℕ))
        (htvErr_ne_top K ε p)
        (Real.exp_pos (radius K ^ 2 / (2 * σsq K ε p (i : ℕ))))
        (measurable_phaseScore hKm (i : ℕ))
        (phaseScore_nonneg (phases K ε p) (σsq K ε p) (interior K) (i : ℕ))
        (phaseScore_le (hsigma K ε p)
          (interior_subset.trans (hradius K ε p hε hp hp1 hconv hball hfin)) (i : ℕ))
        (hvarConst_nonneg ε hε) (hvarSlack_nonneg K ε p hε)
        (hvar_exact K ε p hε hp hp1 hconv hball hfin (i : ℕ)) hsl
      rwa [hvarSum K ε p hε] at hmain)

/-- **§5.2 driven by a sampler, with `hvar_exact` discharged at *every* phase.**

`Ttc.VolumeAlgorithm.cousinsVempalaOfSampler` derives `hphase_mean` and `hphase_var` from a
sampler, but still takes the *exact-law* second moment `hvar_exact` as an argument, because
`Arlib.GaussianCooling.coolLaw_sq_moment_le` covers only the interior phases `i + 1 < m`.
This construction removes that argument: `hvar_exact` is supplied by
`Ttc.CV.hvar_exact_of_fixedRate_all` (i.e. `Arlib.GaussianCooling.coolLaw_sq_moment_le_all`)
for **all** `i`, at the fixed cooling rate and with `varConst = 1 + 2/n`.

**What it costs — three new arguments, and no new radius.**

* `hn : 3 ≤ n` and `hrate : σⱼ₊₁² = σⱼ²(1 + 1/n)` — the hypotheses the interior bound
  already had, now demanded of the schedule globally rather than phase by phase;
* `hflat` — the flatness inequality `R² ≤ 2σⱼ² log(1 + 2/n)` at the terminal indices
  `m ≤ j + 1`. It is checked at `j = m − 1` only (`Ttc.CV.flat_of_fixedRate_terminal`) and
  holds as soon as `σⱼ² ≥ n·R²/2` (`Ttc.CV.flat_of_sigmaSq_ge`).
* **the radius is the one already there.** `cousinsVempalaOfSampler` carries
  `radius : Set (Space n) → ℝ` with `hradius : K ⊆ radius K · Bₙ` for the two slack
  conditions, and `interior K ⊆ K` gives the terminal bound exactly the enclosure it needs
  (`interior_subset.trans (hradius …)`). No second radius parameter is introduced.

**The flatness hypothesis cannot be dropped.** `Arlib.GaussianCooling.terminal_sq_moment_unbounded`
proves that at a terminal phase no constant depending on `n` alone can work: on `K = B₁`,
which satisfies *every* hypothesis the interior theorem places on the body, the ratio
`E(W²)/E(W)²` exceeds any prescribed `C` at a small enough variance. So this construction
is the strongest `∀ i` form available, not a weakening of one that could be stated without
`R`.

**Everything else is unchanged**, including what is *not* claimed. `hTV` — the sampler — is
still an input and is still the open problem; there is still no non-vacuity witness for this
bundle, for the reason recorded on `cousinsVempalaOfSampler` (a degenerate instantiation
provably fails `hslack_mean`); and the variance budget still forces `2m ≤ n·varBudget ε`,
hence a total cooling factor below `11/10`
(`Arlib.GaussianCooling.geomSchedule_total_cooling_lt`), so the schedule cannot anneal and
**no running-time claim of any kind follows**. The conductance constants in this repository
are exponentially small in `n`.

**Arithmetic consistency of the new hypothesis with the old ones** is machine-checked by
`Ttc.CV.flat_slacks_satisfiable`: at `ε = 1`, `m = 2` phases, `innerAcc = 1/2`,
`meanBias = 1/3`, `phaseBias = 1/12`, `varBudget = log(21/20)` and any `n ≥ 100`, the
schedule `σⱼ² = (n·R²/2 + 1)(1 + 1/n)ʲ` satisfies `hflat` at every index while
`hcompose`, `hphaseBudget`, `hbudget` and `hvarSum` hold with `varSlack > 0` and both slack
conditions are met at a strictly positive TV error. `hflat` pushes the variance *up*, which
makes `e^{R²/(2σᵢ²)}` smaller and both slack thresholds *larger*: the new condition and the
old ones pull in the same direction.

**⚠ And the schedule those hypotheses admit does no cooling, so this construction estimates
nothing.** `Ttc.CV.chain_zero_mem_relErr_of_flat` proves that under exactly the hypotheses
listed above — `hflat`, `hrate`, and the `2m ≤ n·varBudget ε` that `hvarSum` + `hbudget`
force — the *cold endpoint alone* already satisfies
`chain m σsq K 0 ∈ (1 ± 11/(5n))·Vol(K)`. The telescope this construction drives has nothing
left to telescope. `Ttc.VolumeAlgorithm.cousinsVempalaOfSamplerCooling` is the version on a
schedule that provably anneals. -/
noncomputable def VolumeAlgorithm.cousinsVempalaOfSamplerFixedRate (n : ℕ) (Ω : Type)
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    -- the schedule data
    (phases : Set (Space n) → ℝ → ℝ → ℕ)
    (reps : ℝ → ℝ → ℕ)
    (varBudget : ℝ → ℝ)
    (innerAcc : ℝ → ℝ)
    (meanBias : ℝ → ℝ)
    (phaseBias : Set (Space n) → ℝ → ℝ → ℝ)
    (varSlack : Set (Space n) → ℝ → ℝ → ℝ)
    (σsq : Set (Space n) → ℝ → ℝ → ℕ → ℝ)
    (radius : Set (Space n) → ℝ)
    (tvErr : Set (Space n) → ℝ → ℝ → ℝ≥0∞)
    (X : Set (Space n) → ℝ → ℝ → ℕ → ℕ → Ω → Space n)
    (med : Set (Space n) → ℝ → ℝ → Ω → ℝ)
    -- the schedule's budgets
    (hreps_pos : ∀ ε p, 0 < p → p < 1 → 0 < reps ε p)
    (hreps : ∀ ε p, 0 < p → p < 1 →
      Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2) ≤ (reps ε p : ℝ))
    (hbudget0 : ∀ ε, 0 < ε → 0 ≤ varBudget ε)
    (hinner_pos : ∀ ε, 0 < ε → 0 < innerAcc ε)
    (hbias_nonneg : ∀ K ε p, 0 < ε → 0 ≤ phaseBias K ε p)
    (hmean_nonneg : ∀ ε, 0 < ε → 0 ≤ meanBias ε)
    (hmean_lt_one : ∀ ε, 0 < ε → meanBias ε < 1)
    (hphases_pos : ∀ K ε p, 0 < ε → 0 < phases K ε p)
    (hphaseBudget : ∀ K ε p, 0 < ε →
      2 * (phases K ε p : ℝ) * phaseBias K ε p ≤ meanBias ε)
    (hcompose : ∀ ε, 0 < ε → innerAcc ε + meanBias ε + innerAcc ε * meanBias ε ≤ ε)
    (hbudget : ∀ ε, 0 < ε → Real.exp (varBudget ε) - 1 ≤ (innerAcc ε) ^ 2 / 5)
    (hsigma : ∀ K ε p j, 0 < σsq K ε p j)
    -- ★ the fixed cooling rate and the dimension bound the variance bound needs
    (hn : 3 ≤ n)
    (hrate : ∀ K ε p j, σsq K ε p (j + 1) = σsq K ε p j * (1 + 1 / (n : ℝ)))
    -- ★ the flatness condition at the terminal indices — see `Ttc.CV.flat_of_sigmaSq_ge`
    (hflat : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → ∀ j, phases K ε p ≤ j + 1 →
      radius K ^ 2 ≤ 2 * σsq K ε p j * Real.log (1 + 2 / (n : ℝ)))
    -- the radius hypotheses
    (hradius_pos : ∀ K, 0 < radius K)
    (hradius : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      K ⊆ Metric.closedBall (0 : Space n) (radius K))
    -- the sampler hypotheses
    (hX_meas : ∀ K ε p j i, Measurable (X K ε p j i))
    (htvErr_ne_top : ∀ K ε p, tvErr K ε p ≠ ⊤)
    (hTV : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j i,
      Arlib.TVLe (μ.map (X K ε p j i))
        (coolLaw (phases K ε p) (σsq K ε p) (interior K) i) (tvErr K ε p))
    (hslack_mean : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ i,
      Real.exp (radius K ^ 2 / (2 * σsq K ε p i)) * (tvErr K ε p).toReal
        ≤ phaseBias K ε p * (chain (phases K ε p) (σsq K ε p) (interior K) (i + 1)
            / chain (phases K ε p) (σsq K ε p) (interior K) i))
    -- the room left above the exact-law second moment `1 + 2/n`
    (hvarSlack_nonneg : ∀ K ε p, 0 < ε → 0 ≤ varSlack K ε p)
    (hvarSum : ∀ K ε p, 0 < ε →
      (1 + 2 / (n : ℝ)) + varSlack K ε p = 1 + varBudget ε / (phases K ε p : ℝ))
    (hslack_var : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ i,
      (tvErr K ε p).toReal * (Real.exp (radius K ^ 2 / (2 * σsq K ε p i)) ^ 2
          * (1 + 2 * (1 + varBudget ε / (phases K ε p : ℝ))))
        ≤ varSlack K ε p * (chain (phases K ε p) (σsq K ε p) (interior K) (i + 1)
            / chain (phases K ε p) (σsq K ε p) (interior K) i) ^ 2)
    -- admissibility
    (hmed_meas : ∀ K ε p, Measurable (med K ε p))
    (hmed : ∀ K ε p ω, IsMedian (fun j : Fin (reps ε p) =>
      chain (phases K ε p) (σsq K ε p) (interior K) 0 *
        ∏ i : Fin (phases K ε p),
          phaseScore (phases K ε p) (σsq K ε p) (interior K) (i : ℕ)
            (X K ε p (j : ℕ) (i : ℕ) ω)) (med K ε p ω))
    (hindep_runs : ∀ K ε p, iIndepFun (fun (j : Fin (reps ε p)) (ω : Ω) =>
      chain (phases K ε p) (σsq K ε p) (interior K) 0 *
        ∏ i : Fin (phases K ε p),
          phaseScore (phases K ε p) (σsq K ε p) (interior K) (i : ℕ)
            (X K ε p (j : ℕ) (i : ℕ) ω)) μ)
    (hprodLp : ∀ K ε p j, MemLp (fun ω => ∏ i : Fin (phases K ε p),
      phaseScore (phases K ε p) (σsq K ε p) (interior K) (i : ℕ)
        (X K ε p j (i : ℕ) ω)) 2 μ)
    (hphase_indep : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j,
      iIndepFun (fun i : Fin (phases K ε p) => fun ω =>
        phaseScore (phases K ε p) (σsq K ε p) (interior K) (i : ℕ)
          (X K ε p j (i : ℕ) ω)) μ) :
    VolumeAlgorithm n :=
  VolumeAlgorithm.cousinsVempalaOfSampler n Ω μ phases reps varBudget innerAcc meanBias
    (fun _ => 1 + 2 / (n : ℝ)) phaseBias varSlack σsq radius tvErr X med
    hreps_pos hreps hbudget0 hinner_pos hbias_nonneg hmean_nonneg hmean_lt_one hphases_pos
    hphaseBudget hcompose hbudget hsigma hradius_pos hradius hX_meas htvErr_ne_top hTV
    hslack_mean
    -- `hvarConst_nonneg`
    (fun _ _ => by positivity)
    hvarSlack_nonneg hvarSum
    -- ★ `hvar_exact`, DERIVED at every phase — interior *and* terminal
    (fun K ε p hε hp hp1 hconv hball hfin i =>
      CV.hvar_exact_of_fixedRate_all (hsigma K ε p) hconv hball hfin
        (interior_subset.trans (hradius K ε p hε hp hp1 hconv hball hfin)) hn
        (hrate K ε p) (hflat K ε p hε) i)
    hslack_var hmed_meas hmed hindep_runs hprodLp hphase_indep

/-- **§5.2 driven by a sampler, on a schedule that actually anneals.**

The general-`α` counterpart of `Ttc.VolumeAlgorithm.cousinsVempalaOfSamplerFixedRate`. The
phase count and the cooling rate are no longer free data: they are

  `m = coolPhases n L κ = ⌈8(n+1)L²/κ⌉`,   `α = coolRate n L κ = √(κ/(2m(n+1)))`

(`Arlib/Convexity/GaussianCooling/PhaseSchedule.lean`), where `L` is the *logarithm of the
required total cooling factor* (for Cousins–Vempala `e^L ≈ nR²`) and `κ = schedBudget ε` is
the slice of the algorithm's relative-variance budget spent on the schedule.

**What changes relative to the fixed rate.**

* `varConst ε = 1 + κ/m` instead of `1 + 2/n`, supplied by
  `Arlib.GaussianCooling.coolRate_meets_budget`. So `hvarSum` no longer forces
  `2m ≤ n·varBudget ε`, and `Arlib.GaussianCooling.geomSchedule_total_cooling_lt` — which
  capped the fixed-rate schedule's total cooling below `11/10` — does not apply.
  `Ttc.CV.cool_schedule_anneals` proves the positive statement instead: the schedule cools
  by a factor at least `e^L`.
* `varSlack = (varBudget ε − κ)/m`, so a **strictly positive** slack (hence a strictly
  positive admissible TV error) is available exactly when `κ < varBudget ε`. Spending only
  half the budget on the schedule, `κ = varBudget ε / 2`, leaves
  `varSlack = varBudget ε/(2m) > 0`.
* `hflat` is at the *matching* constant, `R² ≤ 2σⱼ² log(1 + κ/m)`, and terminal phases go
  through `Arlib.GaussianCooling.coolLaw_sq_moment_le_terminal`, which assumes only the
  radius. See `Ttc.CV.hvar_exact_of_coolRate_all`.
* **`3 ≤ n` is gone.** The general-rate second-moment bound needs no dimension bound.

**`hflat` and the two slack conditions are jointly satisfiable** —
`Ttc.CV.cool_flat_slacks_satisfiable` checks it at explicit numbers, with a strictly
positive TV error. There is no tension: `hflat` is a *lower* bound on the variances, both
slack thresholds carry `e^{−R²/(2σᵢ²)}` and `e^{−R²/σᵢ²}` and so grow with the variance,
and nothing in `cousinsVempalaOfSampler` bounds any `σᵢ²` from above.

**What it costs, stated honestly.** The flatness threshold scales with the phase count:
`σ_{m−1}² ≥ R²/(2 log(1 + κ/m)) ≈ 4(n+1)L²R²/κ²`, which cancels part of the `e^{2L}` the
schedule gains. So `Ttc.CV.chain_zero_mem_relErr_of_flat`'s degeneracy — the cold start
already being the answer — is escaped only once `e^{2L} ≳ 17.6·L²/κ²` (a dimension-free
condition; `L ≈ 7.2` at `κ = log(21/20)/2`, `n = 100`). Below that the general schedule is
as empty of content as the fixed one. `Ttc.CV.cold_start_exponent_ge_of_coolRate` is the
quantitative form.

**Unchanged: `hTV` is still the whole mathematical debt.** Nothing here produces a sampler,
and **no running-time claim of any kind follows**. The per-phase cost is untouched and this
repository's conductance constants are exponentially small in `n`
(`Arlib/Convexity/GaussianCooling/Unblock.lean`). A polynomial phase count is not a
polynomial algorithm. -/
noncomputable def VolumeAlgorithm.cousinsVempalaOfSamplerCooling (n : ℕ) (Ω : Type)
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    -- ★ the cooling requirement `e^L` and the budget slice the schedule may spend
    (L : ℝ) (schedBudget : ℝ → ℝ)
    -- the remaining schedule data — the phase count and the rate are now determined
    (reps : ℝ → ℝ → ℕ)
    (varBudget : ℝ → ℝ)
    (innerAcc : ℝ → ℝ)
    (meanBias : ℝ → ℝ)
    (phaseBias : Set (Space n) → ℝ → ℝ → ℝ)
    (σsq : Set (Space n) → ℝ → ℝ → ℕ → ℝ)
    (radius : Set (Space n) → ℝ)
    (tvErr : Set (Space n) → ℝ → ℝ → ℝ≥0∞)
    (X : Set (Space n) → ℝ → ℝ → ℕ → ℕ → Ω → Space n)
    (med : Set (Space n) → ℝ → ℝ → Ω → ℝ)
    -- ★ the schedule's guards: `1 ≤ L`, `0 < κ ≤ 1`, and `κ` inside the algorithm's budget
    (hL : 1 ≤ L)
    (hsched_pos : ∀ ε, 0 < ε → 0 < schedBudget ε)
    (hsched_le_one : ∀ ε, 0 < ε → schedBudget ε ≤ 1)
    (hsched_le : ∀ ε, 0 < ε → schedBudget ε ≤ varBudget ε)
    -- the schedule's budgets
    (hreps_pos : ∀ ε p, 0 < p → p < 1 → 0 < reps ε p)
    (hreps : ∀ ε p, 0 < p → p < 1 →
      Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2) ≤ (reps ε p : ℝ))
    (hbudget0 : ∀ ε, 0 < ε → 0 ≤ varBudget ε)
    (hinner_pos : ∀ ε, 0 < ε → 0 < innerAcc ε)
    (hbias_nonneg : ∀ K ε p, 0 < ε → 0 ≤ phaseBias K ε p)
    (hmean_nonneg : ∀ ε, 0 < ε → 0 ≤ meanBias ε)
    (hmean_lt_one : ∀ ε, 0 < ε → meanBias ε < 1)
    (hphaseBudget : ∀ K ε p, 0 < ε →
      2 * (coolPhases n L (schedBudget ε) : ℝ) * phaseBias K ε p ≤ meanBias ε)
    (hcompose : ∀ ε, 0 < ε → innerAcc ε + meanBias ε + innerAcc ε * meanBias ε ≤ ε)
    (hbudget : ∀ ε, 0 < ε → Real.exp (varBudget ε) - 1 ≤ (innerAcc ε) ^ 2 / 5)
    (hsigma : ∀ K ε p j, 0 < σsq K ε p j)
    -- ★ the cooling rate the schedule must follow
    (hrate : ∀ K ε p j,
      σsq K ε p (j + 1) = σsq K ε p j * (1 + coolRate n L (schedBudget ε)))
    -- ★ flatness at the terminal indices, at the *matching* constant `1 + κ/m`
    (hflat : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε →
      ∀ j, coolPhases n L (schedBudget ε) ≤ j + 1 →
      radius K ^ 2 ≤ 2 * σsq K ε p j
        * Real.log (1 + schedBudget ε / (coolPhases n L (schedBudget ε) : ℝ)))
    -- the radius hypotheses
    (hradius_pos : ∀ K, 0 < radius K)
    (hradius : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      K ⊆ Metric.closedBall (0 : Space n) (radius K))
    -- the sampler hypotheses
    (hX_meas : ∀ K ε p j i, Measurable (X K ε p j i))
    (htvErr_ne_top : ∀ K ε p, tvErr K ε p ≠ ⊤)
    (hTV : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j i,
      Arlib.TVLe (μ.map (X K ε p j i))
        (coolLaw (coolPhases n L (schedBudget ε)) (σsq K ε p) (interior K) i) (tvErr K ε p))
    (hslack_mean : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ i,
      Real.exp (radius K ^ 2 / (2 * σsq K ε p i)) * (tvErr K ε p).toReal
        ≤ phaseBias K ε p
          * (chain (coolPhases n L (schedBudget ε)) (σsq K ε p) (interior K) (i + 1)
              / chain (coolPhases n L (schedBudget ε)) (σsq K ε p) (interior K) i))
    (hslack_var : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ i,
      (tvErr K ε p).toReal * (Real.exp (radius K ^ 2 / (2 * σsq K ε p i)) ^ 2
          * (1 + 2 * (1 + varBudget ε / (coolPhases n L (schedBudget ε) : ℝ))))
        ≤ (varBudget ε - schedBudget ε) / (coolPhases n L (schedBudget ε) : ℝ)
          * (chain (coolPhases n L (schedBudget ε)) (σsq K ε p) (interior K) (i + 1)
              / chain (coolPhases n L (schedBudget ε)) (σsq K ε p) (interior K) i) ^ 2)
    -- admissibility
    (hmed_meas : ∀ K ε p, Measurable (med K ε p))
    (hmed : ∀ K ε p ω, IsMedian (fun j : Fin (reps ε p) =>
      chain (coolPhases n L (schedBudget ε)) (σsq K ε p) (interior K) 0 *
        ∏ i : Fin (coolPhases n L (schedBudget ε)),
          phaseScore (coolPhases n L (schedBudget ε)) (σsq K ε p) (interior K) (i : ℕ)
            (X K ε p (j : ℕ) (i : ℕ) ω)) (med K ε p ω))
    (hindep_runs : ∀ K ε p, iIndepFun (fun (j : Fin (reps ε p)) (ω : Ω) =>
      chain (coolPhases n L (schedBudget ε)) (σsq K ε p) (interior K) 0 *
        ∏ i : Fin (coolPhases n L (schedBudget ε)),
          phaseScore (coolPhases n L (schedBudget ε)) (σsq K ε p) (interior K) (i : ℕ)
            (X K ε p (j : ℕ) (i : ℕ) ω)) μ)
    (hprodLp : ∀ K ε p j, MemLp (fun ω => ∏ i : Fin (coolPhases n L (schedBudget ε)),
      phaseScore (coolPhases n L (schedBudget ε)) (σsq K ε p) (interior K) (i : ℕ)
        (X K ε p j (i : ℕ) ω)) 2 μ)
    (hphase_indep : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j,
      iIndepFun (fun i : Fin (coolPhases n L (schedBudget ε)) => fun ω =>
        phaseScore (coolPhases n L (schedBudget ε)) (σsq K ε p) (interior K) (i : ℕ)
          (X K ε p j (i : ℕ) ω)) μ) :
    VolumeAlgorithm n :=
  VolumeAlgorithm.cousinsVempalaOfSampler n Ω μ
    (fun _ ε _ => coolPhases n L (schedBudget ε)) reps varBudget innerAcc meanBias
    (fun ε => 1 + schedBudget ε / (coolPhases n L (schedBudget ε) : ℝ)) phaseBias
    (fun _ ε _ => (varBudget ε - schedBudget ε) / (coolPhases n L (schedBudget ε) : ℝ))
    σsq radius tvErr X med
    hreps_pos hreps hbudget0 hinner_pos hbias_nonneg hmean_nonneg hmean_lt_one
    -- `hphases_pos`: the schedule always has at least `8` phases
    (fun _ ε _ hε => coolPhases_pos hL (hsched_pos ε hε))
    hphaseBudget hcompose hbudget hsigma hradius_pos hradius hX_meas htvErr_ne_top hTV
    hslack_mean
    -- `hvarConst_nonneg`
    (fun ε hε => by
      have h1 : (0 : ℝ) ≤ schedBudget ε / (coolPhases n L (schedBudget ε) : ℝ) :=
        div_nonneg (hsched_pos ε hε).le (Nat.cast_nonneg _)
      linarith)
    -- `hvarSlack_nonneg`
    (fun _ ε _ hε =>
      div_nonneg (by linarith [hsched_le ε hε]) (Nat.cast_nonneg _))
    -- `hvarSum`: `(1 + κ/m) + (V − κ)/m = 1 + V/m`, exactly
    (fun _ ε _ hε => by
      have hm0 : (0 : ℝ) < (coolPhases n L (schedBudget ε) : ℝ) := by
        have := one_le_coolPhases (n := n) hL (hsched_pos ε hε); linarith
      field_simp
      ring)
    -- ★ `hvar_exact`, DERIVED at every phase — interior *and* terminal
    (fun K ε p hε hp hp1 hconv hball hfin i =>
      CV.hvar_exact_of_coolRate_all hL (hsched_pos ε hε) (hsched_le_one ε hε)
        (hsigma K ε p) hconv hball hfin
        (interior_subset.trans (hradius K ε p hε hp hp1 hconv hball hfin))
        (hrate K ε p) (hflat K ε p hε) i)
    hslack_var hmed_meas hmed hindep_runs hprodLp hphase_indep

/-! ## Non-vacuity of the construction's hypothesis bundle (`CLAUDE.md` §11)

`Ttc.VolumeAlgorithm.cousinsVempala` takes fourteen hypotheses. A construction whose
hypotheses are jointly *unsatisfiable* is a construction about nothing, so §11 asks for a
witness: an explicit instantiation of every argument, with every hypothesis proved. That is
what this section supplies (`Ttc.VolumeAlgorithm.cousinsVempalaWitness`), together with the
one ingredient that made it awkward — independence of an arbitrary family of random
variables on a one-point probability space.

**What the witness does and does not certify.** It certifies that the bundle is consistent:
no two hypotheses contradict each other, so `cousinsVempala` is not vacuous. It does *not*
certify that the Gaussian-cooling schedule of the paper satisfies them — the witness uses a
degenerate schedule (one phase, deterministic scores, a chain that is a multiple of `Vol(K)`
rather than a chain of Gaussian integrals), and the estimator it produces is the exact
oracle `Ttc.VolumeAlgorithm.exact` in disguise. The real content, `hphase_mean` for the
*sampled* score, is still blocked on isoperimetry. -/

namespace CV

/-- **A nonempty set on a one-point space is everything.** On a subsingleton a set with a
point in it is `univ`, so a probability measure gives it mass `1` — no measurability
needed. -/
theorem measure_eq_one_of_mem {Ω : Type*} [MeasurableSpace Ω] [Subsingleton Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {x : Ω} {A : Set Ω} (h : x ∈ A) : μ A = 1 := by
  have hA : A = (Set.univ : Set Ω) := by
    ext y; simp only [Set.mem_univ, iff_true]; rwa [Subsingleton.elim y x]
  rw [hA, measure_univ]

/-- **A set on a one-point space missing that point is empty**, hence null. -/
theorem measure_eq_zero_of_notMem {Ω : Type*} [MeasurableSpace Ω] [Subsingleton Ω]
    (μ : Measure Ω) {x : Ω} {A : Set Ω} (h : x ∉ A) : μ A = 0 := by
  have hA : A = (∅ : Set Ω) := by
    ext y
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hy; exact h (by rwa [Subsingleton.elim x y])
  rw [hA, measure_empty]

/-- **Independence is free on a one-point probability space.** Every family of random
variables on a subsingleton is `iIndepFun`: each conditioning event is null or everything,
so the product formula reads `1 = 1·…·1` or `0 = …·0·…`.

Mathlib has `indepFun_const_left`/`_right` for a *pair* with one constant, but no `iIndepFun`
version for a whole family, and the family here is indexed by `Fin m` with `m` arbitrary.
This is the missing ingredient the non-vacuity witness below needs (twice: for the phases
of a run and for the runs of the median). -/
theorem iIndepFun_of_subsingleton {ι : Type*} {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {Ω : Type*} [MeasurableSpace Ω] [Subsingleton Ω] [Nonempty Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : ∀ i, Ω → β i) :
    iIndepFun f μ := by
  classical
  obtain ⟨x⟩ : Nonempty Ω := inferInstance
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _hS
  by_cases h : ∀ i ∈ S, x ∈ f i ⁻¹' sets i
  · rw [measure_eq_one_of_mem μ (Set.mem_iInter₂.mpr h)]
    exact (Finset.prod_eq_one fun i hi => measure_eq_one_of_mem μ (h i hi)).symm
  · push_neg at h
    obtain ⟨i, hiS, hi⟩ := h
    rw [measure_eq_zero_of_notMem μ fun hc => hi (Set.mem_iInter₂.mp hc i hiS)]
    exact (Finset.prod_eq_zero hiS (measure_eq_zero_of_notMem μ hi)).symm

/-- **A body containing the unit ball has positive, finite volume.** Both guards of
`Ttc.VolumeAlgorithm`'s `correct` are used: `Metric.ball 0 1 ⊆ K` for positivity and
`volume K ≠ ⊤` for finiteness. This is forced on any instantiation of `cousinsVempala`,
since `hchain_pos` and `hchain_end` together demand `0 < Vol(K)`. -/
theorem toReal_volume_pos {n : ℕ} {K : Set (Space n)}
    (hball : Metric.ball (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤) :
    0 < (volume K).toReal :=
  ENNReal.toReal_pos
    (lt_of_lt_of_le (Metric.measure_ball_pos volume 0 one_pos) (measure_mono hball)).ne' hfin

/-! ### The witness data

One phase; the cooling chain `2·Vol(K), Vol(K), Vol(K), …`; the deterministic score `1/2`,
which is exactly the ratio `chain 1 / chain 0` the telescope wants and has relative second
moment exactly `1`; the median of the (constant) runs. The chain is deliberately *not*
constant, so that `hphase_mean` is instantiated at a ratio different from `1` and the
telescoping product does real work. -/

/-- The witness's phase count: one phase. -/
def witPhases {n : ℕ} : Set (Space n) → ℝ → ℝ → ℕ := fun _ _ _ => 1

/-- The witness's repetition count: `⌈(50/9)·log(1/p)⌉ + 1`, the smallest schedule meeting
the median boost's `O(log 1/p)` requirement. -/
noncomputable def witReps : ℝ → ℝ → ℕ :=
  fun _ p => ⌈Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2)⌉₊ + 1

/-- The witness's variance budget: `κ = 0`. The deterministic score has relative second
moment exactly `1 = 1 + 0/m`, and `e⁰ − 1 = 0 ≤ ε²/5`. -/
def witVarBudget : ℝ → ℝ := fun _ => 0

/-- The witness's cooling chain: `2·Vol(K)` at the cold end, `Vol(K)` afterwards. -/
noncomputable def witChain {n : ℕ} : Set (Space n) → ℝ → ℝ → ℕ → ℝ :=
  fun K _ _ i => (if i = 0 then 2 else 1) * (volume K).toReal

/-- The witness's per-phase score: the deterministic `1/2 = chain 1 / chain 0`. -/
noncomputable def witW {n : ℕ} : Set (Space n) → ℝ → ℝ → ℕ → ℕ → Unit → ℝ :=
  fun _ _ _ _ _ _ => 1 / 2

/-- The witness's median: every run equals `2·Vol(K)·(1/2) = Vol(K)`. -/
noncomputable def witMed {n : ℕ} : Set (Space n) → ℝ → ℝ → Unit → ℝ :=
  fun K _ _ _ => (volume K).toReal

/-- Every run of the witness returns `Vol(K)` exactly. -/
theorem witRun_eq {n : ℕ} (K : Set (Space n)) (ε p : ℝ) (j : ℕ) (ω : Unit) :
    witChain K ε p 0 * ∏ i : Fin (witPhases K ε p), witW K ε p j (i : ℕ) ω
      = (volume K).toReal := by
  have hp : (∏ i : Fin (witPhases K ε p), witW K ε p j (i : ℕ) ω) = (1 / 2 : ℝ) := by
    simp [witW, witPhases]
  have hc : witChain K ε p 0 = 2 * (volume K).toReal := by simp [witChain]
  rw [hp, hc]; ring

/-! ### The fourteen hypotheses, discharged

Each lemma below is exactly one argument of `Ttc.VolumeAlgorithm.cousinsVempala`, in the
order the construction takes them. -/

/-- `hreps_pos`. -/
theorem witReps_pos (ε p : ℝ) : 0 < witReps ε p := by unfold witReps; omega

/-- `hreps`: the median boost's `O(log 1/p)` repetition count. -/
theorem witReps_ge (ε p : ℝ) :
    Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2) ≤ (witReps ε p : ℝ) := by
  have h := Nat.le_ceil (Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2))
  simp only [witReps, Nat.cast_add, Nat.cast_one]
  linarith

/-- `hbudget0`. -/
theorem witVarBudget_nonneg (ε : ℝ) : 0 ≤ witVarBudget ε := le_of_eq rfl

/-- `hbudget`: `e⁰ − 1 = 0 ≤ ε²/5`. -/
theorem witVarBudget_le (ε : ℝ) (hε : 0 < ε) :
    Real.exp (witVarBudget ε) - 1 ≤ ε ^ 2 / 5 := by
  simp only [witVarBudget, Real.exp_zero, sub_self]
  positivity

/-- `hW_meas`. -/
theorem witW_meas {n : ℕ} (K : Set (Space n)) (ε p : ℝ) (j i : ℕ) :
    Measurable (witW K ε p j i) := measurable_const

/-- `hmed_meas`. -/
theorem witMed_meas {n : ℕ} (K : Set (Space n)) (ε p : ℝ) : Measurable (witMed K ε p) :=
  measurable_const

/-- `hmed`: every run equals `Vol(K)`, so `Vol(K)` is a median of them. -/
theorem witMed_isMedian {n : ℕ} (K : Set (Space n)) (ε p : ℝ) (ω : Unit) :
    IsMedian (fun j : Fin (witReps ε p) =>
      witChain K ε p 0 * ∏ i : Fin (witPhases K ε p), witW K ε p (j : ℕ) (i : ℕ) ω)
      (witMed K ε p ω) := by
  have hv : ∀ j : Fin (witReps ε p),
      witChain K ε p 0 * ∏ i : Fin (witPhases K ε p), witW K ε p (j : ℕ) (i : ℕ) ω
        = witMed K ε p ω := fun j => witRun_eq K ε p (j : ℕ) ω
  constructor
  · rw [Finset.filter_true_of_mem fun j _ => (hv j).le]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  · rw [Finset.filter_true_of_mem fun j _ => (hv j).ge]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega

/-- `hindep_runs`: independence of the runs, free on a one-point space. -/
theorem witIndep_runs {n : ℕ} (K : Set (Space n)) (ε p : ℝ) :
    iIndepFun (fun (j : Fin (witReps ε p)) (ω : Unit) =>
      witChain K ε p 0 * ∏ i : Fin (witPhases K ε p), witW K ε p (j : ℕ) (i : ℕ) ω)
      (Measure.dirac ()) :=
  iIndepFun_of_subsingleton _ _

/-- `hprodLp`: the product is a constant, hence in every `Lᵖ` of a finite measure. -/
theorem witProdLp {n : ℕ} (K : Set (Space n)) (ε p : ℝ) (j : ℕ) :
    MemLp (fun ω : Unit => ∏ i : Fin (witPhases K ε p), witW K ε p j (i : ℕ) ω) 2
      (Measure.dirac ()) := by
  have hconst : (fun ω : Unit => ∏ i : Fin (witPhases K ε p), witW K ε p j (i : ℕ) ω)
      = fun _ : Unit => (1 / 2 : ℝ) := by
    funext ω; simp [witW, witPhases]
  rw [hconst]
  exact memLp_const _

/-- `hchain_pos`: the chain is a positive multiple of `Vol(K) > 0`. -/
theorem witChain_pos {n : ℕ} {K : Set (Space n)} (ε p : ℝ)
    (hball : Metric.ball (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤) (i : ℕ) :
    0 < witChain K ε p i := by
  have hv := toReal_volume_pos hball hfin
  unfold witChain
  split <;> linarith

/-- `hchain_end`: the chain's endpoint is `Vol(K)` exactly. -/
theorem witChain_end {n : ℕ} (K : Set (Space n)) (ε p : ℝ) :
    witChain K ε p (witPhases K ε p) = (volume K).toReal := by
  simp [witChain, witPhases]

/-- `hphase_indep`: independence of the phases, free on a one-point space. -/
theorem witPhase_indep {n : ℕ} (K : Set (Space n)) (ε p : ℝ) (j : ℕ) :
    iIndepFun (fun i : Fin (witPhases K ε p) => witW K ε p j (i : ℕ)) (Measure.dirac ()) :=
  iIndepFun_of_subsingleton _ _

/-- `hphase_mean`: the score `1/2` is unbiased for `chain 1 / chain 0 = Vol(K)/(2Vol(K))`.
This is the hypothesis the sampler would have to supply; here the "sampler" is
deterministic and the chain is chosen to match it. -/
theorem witPhase_mean {n : ℕ} {K : Set (Space n)} (ε p : ℝ)
    (hball : Metric.ball (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤) (j : ℕ)
    (i : Fin (witPhases K ε p)) :
    ∫ ω, witW K ε p j (i : ℕ) ω ∂(Measure.dirac ())
      = witChain K ε p ((i : ℕ) + 1) / witChain K ε p (i : ℕ) := by
  have hv := toReal_volume_pos hball hfin
  have hlt : (i : ℕ) < 1 := by simpa [witPhases] using i.isLt
  have hi : (i : ℕ) = 0 := by omega
  have hL : ∫ ω, witW K ε p j (i : ℕ) ω ∂(Measure.dirac ()) = (1 / 2 : ℝ) := by
    simp [witW]
  have h1 : witChain K ε p (0 + 1) = (volume K).toReal := by simp [witChain]
  have h0 : witChain K ε p 0 = 2 * (volume K).toReal := by simp [witChain]
  rw [hL, hi, h1, h0, eq_div_iff (show (0:ℝ) < 2 * (volume K).toReal by linarith).ne']
  ring

/-- `hphase_var`: the deterministic score has relative second moment exactly `1`. -/
theorem witPhase_var {n : ℕ} (K : Set (Space n)) (ε p : ℝ) (j : ℕ)
    (i : Fin (witPhases K ε p)) :
    ∫ ω, (witW K ε p j (i : ℕ) ω) ^ 2 ∂(Measure.dirac ())
      ≤ (1 + witVarBudget ε / (witPhases K ε p : ℝ))
        * (∫ ω, witW K ε p j (i : ℕ) ω ∂(Measure.dirac ())) ^ 2 := by
  simp [witW, witVarBudget, witPhases]

/-! ### The three extra hypotheses of the biased-endpoint construction

`Ttc.VolumeAlgorithm.cousinsVempalaOfBiasedEnd` splits the requested accuracy `ε` between
an inner accuracy and an endpoint bias. The split `innerAcc ε = ε/2`,
`endBias ε = ε/(2+ε)` meets `hcompose` with equality — and with a *strictly positive* bias,
so the witness exercises the biased branch rather than collapsing it to the exact one. -/

/-- The witness's inner accuracy: half the requested `ε`. -/
noncomputable def witInnerAcc : ℝ → ℝ := fun ε => ε / 2

/-- The witness's endpoint bias: `ε/(2+ε)`, the largest bias the inner accuracy `ε/2`
leaves room for. Strictly positive whenever `ε` is. -/
noncomputable def witEndBias : ℝ → ℝ := fun ε => ε / (2 + ε)

/-- `hinner_pos`. -/
theorem witInnerAcc_pos (ε : ℝ) (hε : 0 < ε) : 0 < witInnerAcc ε := by
  simp only [witInnerAcc]; linarith

/-- `hbias_nonneg`; in fact `0 < witEndBias ε`. -/
theorem witEndBias_pos (ε : ℝ) (hε : 0 < ε) : 0 < witEndBias ε := by
  simp only [witEndBias]
  exact div_pos hε (by linarith)

/-- `hcompose`: `ε/2 + ε/(2+ε) + (ε/2)·(ε/(2+ε)) = ε`, exactly. -/
theorem witCompose (ε : ℝ) (hε : 0 < ε) :
    witInnerAcc ε + witEndBias ε + witInnerAcc ε * witEndBias ε ≤ ε := by
  have h2 : (2 : ℝ) + ε ≠ 0 := by positivity
  simp only [witInnerAcc, witEndBias]
  have key : ε / 2 + ε / (2 + ε) + ε / 2 * (ε / (2 + ε)) = ε := by
    field_simp; ring
  exact key.le

/-- `hbudget`, at the inner accuracy. -/
theorem witVarBudget_le_inner (ε : ℝ) (hε : 0 < ε) :
    Real.exp (witVarBudget ε) - 1 ≤ (witInnerAcc ε) ^ 2 / 5 := by
  simp only [witVarBudget, Real.exp_zero, sub_self, witInnerAcc]
  positivity

/-! ### The extra hypotheses of the approximate-mean construction

`Ttc.VolumeAlgorithm.cousinsVempalaOfApproxMean` splits the requested accuracy `ε` between
the inner (Chebyshev) accuracy and the *mean bias* of the telescoped product, and then
splits that mean bias across the phases. The witness reuses the endpoint split
`innerAcc ε = ε/2`, `meanBias ε = ε/(2+ε)` — `Ttc.CV.witEndBias` does double duty as the
mean bias, `Ttc.CV.witCompose` is the same equality — and takes the per-phase bias to be
`meanBias/(2m) = ε/(2(2+ε))`, which meets `hphaseBudget` with equality. Both are
**strictly positive**, so the witness exercises the approximate branch rather than
collapsing it to the exact one. -/

/-- The witness's per-phase mean bias: `meanBias/(2m) = ε/(2(2+ε))` at `m = 1`. Strictly
positive whenever `ε` is. -/
noncomputable def witPhaseBias {n : ℕ} : Set (Space n) → ℝ → ℝ → ℝ :=
  fun _ ε _ => ε / (2 * (2 + ε))

/-- `hphases_pos`. -/
theorem witPhases_pos {n : ℕ} (K : Set (Space n)) (ε p : ℝ) : 0 < witPhases K ε p := by
  simp [witPhases]

/-- `hbias_nonneg`; in fact `0 < witPhaseBias K ε p`. -/
theorem witPhaseBias_pos {n : ℕ} (K : Set (Space n)) (ε p : ℝ) (hε : 0 < ε) :
    0 < witPhaseBias K ε p := by
  simp only [witPhaseBias]
  exact div_pos hε (by linarith)

/-- `hmean_lt_one`: `ε/(2+ε) < 1`. -/
theorem witEndBias_lt_one (ε : ℝ) (hε : 0 < ε) : witEndBias ε < 1 := by
  simp only [witEndBias]
  rw [div_lt_one (by linarith)]
  linarith

/-- `hphaseBudget`: `2·m·(ε/(2(2+ε))) = ε/(2+ε)` at `m = 1`, so the per-phase budget is met
with equality. -/
theorem witPhaseBudget {n : ℕ} (K : Set (Space n)) (ε p : ℝ) (hε : 0 < ε) :
    2 * (witPhases K ε p : ℝ) * witPhaseBias K ε p ≤ witEndBias ε := by
  have h2 : (2 : ℝ) + ε ≠ 0 := by positivity
  have key : 2 * (witPhases K ε p : ℝ) * witPhaseBias K ε p = witEndBias ε := by
    simp only [witPhases, witPhaseBias, witEndBias, Nat.cast_one]
    field_simp
  exact key.le

/-- `hphase_mean`, in relative-error form: the exact score `1/2` is in particular within a
relative `witPhaseBias K ε p` of the chain ratio. -/
theorem witPhase_mean_mem {n : ℕ} {K : Set (Space n)} (ε p : ℝ) (hε : 0 < ε)
    (hball : Metric.ball (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤) (j : ℕ)
    (i : Fin (witPhases K ε p)) :
    ∫ ω, witW K ε p j (i : ℕ) ω ∂(Measure.dirac ())
      ∈ relErr (witPhaseBias K ε p)
          (witChain K ε p ((i : ℕ) + 1) / witChain K ε p (i : ℕ)) := by
  have hb : 0 < witChain K ε p ((i : ℕ) + 1) / witChain K ε p (i : ℕ) :=
    div_pos (witChain_pos ε p hball hfin _) (witChain_pos ε p hball hfin _)
  have hη : 0 ≤ witPhaseBias K ε p := (witPhaseBias_pos K ε p hε).le
  rw [witPhase_mean ε p hball hfin j i]
  simp only [relErr, Set.mem_Icc]
  constructor <;> nlinarith

/-- `hchain_end`, in relative-error form: an exact endpoint is in particular a biased one. -/
theorem witChain_end_mem {n : ℕ} (K : Set (Space n)) (ε p : ℝ) (hε : 0 < ε) :
    witChain K ε p (witPhases K ε p) ∈ relErr (witEndBias ε) (volume K).toReal := by
  rw [witChain_end]
  have hb : (0:ℝ) ≤ (volume K).toReal := ENNReal.toReal_nonneg
  have hη : 0 ≤ witEndBias ε := (witEndBias_pos ε hε).le
  simp only [relErr, Set.mem_Icc]
  constructor <;> nlinarith

end CV

/-- **The non-vacuity witness for `Ttc.VolumeAlgorithm.cousinsVempala`** (`CLAUDE.md` §11).

Every argument of the construction is instantiated and every hypothesis is proved, so the
hypothesis bundle is **satisfiable**: `cousinsVempala` is a theorem about something. The
instantiation is `Ω = Unit`, `μ = dirac ()`, one phase, the chain `2Vol(K), Vol(K), …`, the
deterministic score `1/2`, variance budget `κ = 0`, and `⌈(50/9)log(1/p)⌉+1` repetitions.

The witness is *degenerate on purpose*: it is the smallest instantiation that touches every
hypothesis non-vacuously (the chain is non-constant, so `hphase_mean` is instantiated at a
ratio `≠ 1` and the telescope is not trivial), and it makes no claim that the paper's
Gaussian schedule satisfies the bundle. The resulting algorithm returns `Vol(K)` exactly
(`cousinsVempalaWitness_est`), i.e. it is `Ttc.VolumeAlgorithm.exact` factored through
§5.2's median-of-products. -/
noncomputable def VolumeAlgorithm.cousinsVempalaWitness (n : ℕ) : VolumeAlgorithm n :=
  VolumeAlgorithm.cousinsVempala n Unit (Measure.dirac ())
    CV.witPhases CV.witReps CV.witVarBudget CV.witChain CV.witW CV.witMed
    (fun ε p _ _ => CV.witReps_pos ε p)
    (fun ε p _ _ => CV.witReps_ge ε p)
    (fun ε _ => CV.witVarBudget_nonneg ε)
    (fun ε hε => CV.witVarBudget_le ε hε)
    CV.witW_meas
    CV.witMed_meas
    CV.witMed_isMedian
    CV.witIndep_runs
    CV.witProdLp
    (fun K ε p _ _ _ _ hball hfin => CV.witChain_pos ε p hball hfin)
    (fun K ε p _ _ _ _ _ _ => CV.witChain_end K ε p)
    (fun K ε p _ _ _ _ _ _ => CV.witPhase_indep K ε p)
    (fun K ε p _ _ _ _ hball hfin => CV.witPhase_mean ε p hball hfin)
    (fun K ε p _ _ _ _ _ _ => CV.witPhase_var K ε p)

/-- The witness's estimate is `Vol(K)` on the nose, at every accuracy, confidence and coin
toss. (So it certifies satisfiability of the bundle, not the existence of the paper's
algorithm.) -/
theorem VolumeAlgorithm.cousinsVempalaWitness_est (n : ℕ) (K : Set (Space n)) (ε p : ℝ)
    (ω : (cousinsVempalaWitness n).Ω) :
    (cousinsVempalaWitness n).est K ε p ω = (volume K).toReal := rfl

/-- **The non-vacuity witness for `Ttc.VolumeAlgorithm.cousinsVempalaOfBiasedEnd`.** The
same data, with the accuracy split `innerAcc ε = ε/2`, `endBias ε = ε/(2+ε) > 0`. The
endpoint bias is genuinely positive here, so the biased branch of the construction is
exercised rather than collapsed back to the exact one. -/
noncomputable def VolumeAlgorithm.cousinsVempalaBiasedWitness (n : ℕ) : VolumeAlgorithm n :=
  VolumeAlgorithm.cousinsVempalaOfBiasedEnd n Unit (Measure.dirac ())
    CV.witPhases CV.witReps CV.witVarBudget CV.witInnerAcc CV.witEndBias
    CV.witChain CV.witW CV.witMed
    (fun ε p _ _ => CV.witReps_pos ε p)
    (fun ε p _ _ => CV.witReps_ge ε p)
    (fun ε _ => CV.witVarBudget_nonneg ε)
    CV.witInnerAcc_pos
    (fun ε hε => (CV.witEndBias_pos ε hε).le)
    CV.witCompose
    CV.witVarBudget_le_inner
    CV.witW_meas
    CV.witMed_meas
    CV.witMed_isMedian
    CV.witIndep_runs
    CV.witProdLp
    (fun K ε p _ _ _ _ hball hfin => CV.witChain_pos ε p hball hfin)
    (fun K ε p hε _ _ _ _ _ => CV.witChain_end_mem K ε p hε)
    (fun K ε p _ _ _ _ _ _ => CV.witPhase_indep K ε p)
    (fun K ε p _ _ _ _ hball hfin => CV.witPhase_mean ε p hball hfin)
    (fun K ε p _ _ _ _ _ _ => CV.witPhase_var K ε p)

/-- **The non-vacuity witness for `Ttc.VolumeAlgorithm.cousinsVempalaOfApproxMean`**
(`CLAUDE.md` §11). Every argument is instantiated and every hypothesis proved, with a
**strictly positive** per-phase mean bias `ε/(2(2+ε))` and mean bias `ε/(2+ε)`, so the
approximate-mean branch is genuinely exercised.

As with `cousinsVempalaWitness`, this certifies that the bundle is *consistent*, not that
the paper's Gaussian schedule satisfies it: the schedule is degenerate (one phase, a
deterministic score, a chain that is a multiple of `Vol(K)`) and the resulting algorithm is
`Ttc.VolumeAlgorithm.exact` in disguise. -/
noncomputable def VolumeAlgorithm.cousinsVempalaApproxMeanWitness (n : ℕ) :
    VolumeAlgorithm n :=
  VolumeAlgorithm.cousinsVempalaOfApproxMean n Unit (Measure.dirac ())
    CV.witPhases CV.witReps CV.witVarBudget CV.witInnerAcc CV.witEndBias CV.witPhaseBias
    CV.witChain CV.witW CV.witMed
    (fun ε p _ _ => CV.witReps_pos ε p)
    (fun ε p _ _ => CV.witReps_ge ε p)
    (fun ε _ => CV.witVarBudget_nonneg ε)
    CV.witInnerAcc_pos
    (fun K ε p hε => (CV.witPhaseBias_pos K ε p hε).le)
    (fun ε hε => (CV.witEndBias_pos ε hε).le)
    CV.witEndBias_lt_one
    (fun K ε p _ => CV.witPhases_pos K ε p)
    CV.witPhaseBudget
    CV.witCompose
    CV.witVarBudget_le_inner
    CV.witW_meas
    CV.witMed_meas
    CV.witMed_isMedian
    CV.witIndep_runs
    CV.witProdLp
    (fun K ε p _ _ _ _ hball hfin => CV.witChain_pos ε p hball hfin)
    (fun K ε p _ _ _ _ _ _ => CV.witChain_end K ε p)
    (fun K ε p _ _ _ _ _ _ => CV.witPhase_indep K ε p)
    (fun K ε p hε _ _ _ hball hfin => CV.witPhase_mean_mem ε p hε hball hfin)
    (fun K ε p _ _ _ _ _ _ => CV.witPhase_var K ε p)

/-- The approximate-mean witness's estimate is `Vol(K)` on the nose. -/
theorem VolumeAlgorithm.cousinsVempalaApproxMeanWitness_est (n : ℕ) (K : Set (Space n))
    (ε p : ℝ) (ω : (cousinsVempalaApproxMeanWitness n).Ω) :
    (cousinsVempalaApproxMeanWitness n).est K ε p ω = (volume K).toReal := rfl

/-! ## Axiom audit for §5.2 -/

#print axioms CV.mem_relErr_iff
#print axioms CV.relErr_trans
#print axioms CV.measure_notMem_relErr_le
#print axioms CV.prod_range_ratio
#print axioms CV.prod_fin_ratio
#print axioms CV.prod_relErr_ge
#print axioms CV.run_relErr_ge
#print axioms CV.run_relErr_four_fifths
#print axioms CV.median_relErr_ge
#print axioms CV.G_indicator_eq
#print axioms CV.G_indicator_le
#print axioms CV.G_indicator_ge
#print axioms CV.gaussianCooling_accuracy
#print axioms CV.relErr_mono
#print axioms CV.G_indicator_mem_relErr
#print axioms CV.run_relErr_four_fifths_biasedEnd
#print axioms CV.gaussianCooling_accuracy_biasedEnd
#print axioms CV.run_relErr_four_fifths_approxMean
#print axioms CV.volume_interior_eq
#print axioms CV.volume_interior_ne_top
#print axioms CV.ball_subset_interior
#print axioms CV.cvRadius_pos
#print axioms CV.subset_closedBall_cvRadius
#print axioms CV.integral_map_mem_relErr_of_tvLe
#print axioms CV.sampledPhase_mean_mem_relErr
#print axioms CV.tv_slacks_satisfiable
#print axioms CV.tv_slack_threshold_pos
#print axioms CV.exists_pos_tvErr
#print axioms CV.hvar_exact_of_fixedRate
#print axioms CV.exp_le_inv_one_sub
#print axioms CV.one_div_le_log_one_add_two_div
#print axioms CV.flat_of_sigmaSq_ge
#print axioms CV.flat_of_fixedRate_terminal
#print axioms CV.hvar_exact_of_fixedRate_all
#print axioms CV.flat_slacks_satisfiable
#print axioms CV.log_one_add_two_div_le
#print axioms CV.sigmaSq_ge_of_flat
#print axioms CV.sigmaSq_eq_pow
#print axioms CV.sigmaSq_zero_gt_of_flat_of_meet
#print axioms CV.coolWeight_zero_ge_of_flat
#print axioms CV.chain_zero_mem_relErr_of_flat
#print axioms CV.cold_start_mem_relErr_of_flat
#print axioms CV.varBudget_param_le
#print axioms CV.meet_of_fixedRate_fields
#print axioms CV.cold_start_mem_relErr_of_fixedRate_fields
#print axioms CV.sigmaSq_mono_of_rate
#print axioms CV.flat_of_rate_of_le
#print axioms CV.hvar_exact_of_coolRate_all
#print axioms CV.cool_schedule_anneals
#print axioms CV.cold_start_exponent_ge_of_coolRate
#print axioms CV.cool_flat_slacks_satisfiable
#print axioms CV.cool_budgets_at_numbers
#print axioms VolumeAlgorithm.cousinsVempalaOfSamplerCooling
#print axioms VolumeAlgorithm.cousinsVempalaOfSamplerFixedRate
#print axioms CV.iIndepFun_of_subsingleton
#print axioms CV.toReal_volume_pos
#print axioms VolumeAlgorithm.ofRuns
#print axioms VolumeAlgorithm.cousinsVempala
#print axioms VolumeAlgorithm.cousinsVempalaOfBiasedEnd
#print axioms VolumeAlgorithm.cousinsVempalaOfApproxMean
#print axioms VolumeAlgorithm.cousinsVempalaOfSampler
#print axioms VolumeAlgorithm.cousinsVempalaWitness
#print axioms VolumeAlgorithm.cousinsVempalaWitness_est
#print axioms VolumeAlgorithm.cousinsVempalaBiasedWitness
#print axioms CV.witPhases_pos
#print axioms CV.witPhaseBias_pos
#print axioms CV.witEndBias_lt_one
#print axioms CV.witPhaseBudget
#print axioms CV.witPhase_mean_mem
#print axioms VolumeAlgorithm.cousinsVempalaApproxMeanWitness
#print axioms VolumeAlgorithm.cousinsVempalaApproxMeanWitness_est

end Ttc
