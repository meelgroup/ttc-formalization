/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.Convexity.SpeedyGaussianMixing
import Arlib.Convexity.GaussianCooling.ColdStart
import Arlib.Convexity.GaussianCooling.WarmChain
import Arlib.MarkovChains.Continuous.WastedSteps
import Arlib.MarkovChains.Continuous.KLS97Shell

/-!
# The sampler's step count, at the regime `δ = 1/(2n)`

## Scope — read this first

`Ttc.VolumeAlgorithm` has **no complexity field**.  No running time can therefore be *stated*
inside that interface, and nothing in this file changes that.  What is proved here is an
**arithmetic/accounting result about step counts that are already proved elsewhere**:

* how many *speedy* steps the mixing theorem
  `Arlib.mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit` demands per annealing
  phase once the step size is fixed at `δ = 1/(2n)`;
* what that becomes when multiplied by an annealing phase count;
* what `Arlib.MarkovChains.sum_lintegral_inv_ell_iterate_speedyWalk_le` then says about the
  summed *ball-walk* cost of that many speedy steps.

**This is not a claim that any volume algorithm runs in polynomial time.**  There is no cost
model, no machine model, no arithmetic-operation count, and no statement about `Ttc`'s
algorithm anywhere below.  A step count is not a running time, and the products formed here
are products of *proved bounds on counters*, nothing more.  Nothing under `Ttc/` is edited,
imported or referred to.

## The regime, and the arithmetic

`Arlib/MarkovChains/Continuous/KLS97Shell.lean` isolates the step-size regime `δ ≤ 1 − c =
1/(2n)`, at which the two Kannan–Lovász–Simonovits inputs to `lem:map-speedy-to-ball` become
provable outright (`ell_eq_one_on_shrunken`, `half_le_speedy_shrunken`).  Substituting
`δ = 1/(2n)` into the mixing deadline

    `4·640²·σ²·n·(log M + 2·log(1/ε)) / (δ·log 2)² + 1`

replaces `1/δ²` by `4n²`, so `4·640² = 1638400` becomes `4·4·640² = 6553600` and the
dimension exponent rises from `n` to `n³`:

    `6553600·σ²·n³·(log M + 2·log(1/ε)) / (log 2)² + 1`.

This is the `O(σ²n³·log(M/ε))` shape that `KLS97Shell.lean`'s module docstring already
predicts, in place of the `O(σ²n²·log(M/ε))` available at Cousins–Vempala's larger step.
No constant and no regime is changed silently: `6553600` is `4·640²·4` and nothing else.

### The side condition the substitution forces (a binder, and a finding)

The mixing theorem carries `hδσ : δ ≤ σ/(8√n)`.  At `δ = 1/(2n)` this is *exactly*

    `hσn : 4 ≤ σ·√n`,   i.e.   `σ² ≥ 16/n`,

which is **not** implied by the other hypotheses, so it appears as a binder on every theorem
below.  It is worth stating plainly what it costs: `ColdStart.lean`'s schedule starts at
`σ²₀ = 1/n` exactly (`geomSchedule (1/n) α`), where `σ₀·√n = 1 < 4`.  **The earliest
cold-start phases therefore fall outside the `δ = 1/(2n)` regime**: at `σ² = 1/n` the mixing
theorem needs `δ ≤ 1/(8n)`, a different constant, and the per-phase count below does not
apply to them.  Nothing here repairs that; it is recorded as a genuine gap between the two
ingredients, in the spirit of `CLAUDE.md` §5.

## What each section delivers

1. **Per phase** — `mixesWithin_lazy_speedyMetropolisGaussian_kls`: the mixing theorem at
   `δ = 1/(2n)` with the constant `6553600` explicit.
2. **All phases at one budget** — `mixesWithin_all_phases_kls`: a family of phases sharing the
   body `K`, each with its own variance `σⱼ²` and its own start `μⱼ`, all mixing within the
   single budget `t = ⌈D(σmax)⌉₊` computed at a dominating `σmax`.
3. **Total speedy steps** — `total_speedy_steps_le`: `m·t ≤ (32(n+1)L²/κ + 1)·(D + 1)`, where
   `32(n+1)L²/κ + 1` is `GeneralRate.lean`'s bound `generalPhaseCount_le` on the phase count
   `ColdStart.lean` uses.
4. **Polynomial shape** — `total_speedy_steps_poly` and `total_speedy_steps_poly_varBudget`.
5. **Total ball-walk cost** — `sum_ballWalk_cost_phases_le`.
6. **Non-vacuity** — `sampler_step_count_witness`.

## Which closed form was chosen for the polynomial shape

An **explicit product of factors**, not a single closed form in `n, R, 1/ε` alone:

    `m·t ≤ 5·10⁸ · (n+1) · n³ · σmax² · L² · (1 + log M + 2·log(1/ε)) / κ`

and, at `κ = varBudget (ε/2)`,

    `m·t ≤ 2·10¹⁰ · (n+1) · n³ · σmax² · L² · (1 + log M + 2·log(1/ε)) / ε²`.

So the **exponents achieved** are `n⁴` (as `(n+1)·n³`), `σmax²`, `ε⁻²`, `L²` and one power of
`log M`.  The reason a closed form in `R` is *not* offered is structural, and is itself a
finding: `cold_start_annealing_witness` is an existential over `(α, m, σsq)` that exposes only
a *lower* bound on the phase count (`32 ≤ m`) and only a *lower* bound on the total cooling
(`nR² ≤ σsq m / σsq 0`).  Neither `m` nor `max_j σⱼ` is pinned from above by that statement, so
neither can be eliminated here.  Both therefore enter as hypotheses: `hm`, which
`generalPhaseCount_le` discharges for `ColdStart.lean`'s *stated* choice
`m = generalPhaseCount n κ L'`, and `hsigmax`.  Since `hflat` forces
`σ²_{m−1} ≥ R²/(2Λ)` with `Λ` small, a binder `σmax² ≤ R²` would be **false** for the intended
schedule — which is why `σmax²` is carried as a factor rather than converted into `R²`.
`L` is likewise a parameter; `ColdStart.lean` runs at `L' = 3·log(nR²) + 4·log(256(n+1)/κ²)`.

## Hypotheses carried unproved

* **`hlam : lam ≤ avgLocalConductance K δ`** — Cousins–Vempala's `lem:lambda-bound`
  (`vol3_journal.tex:855`).  Nothing in this repository proves it and nothing here attempts
  to; §5's theorem carries it as a binder exactly as `WastedSteps.lean` does.  (At
  `δ ≤ 1/(2n)`, `KLS97Shell.ell_eq_one_on_shrunken` gives `ℓ ≡ 1` on the shrunken body, which
  *suggests* a route to a lower bound on `λ` in this regime; **that route is not taken and no
  such bound is proved here**.)
* **`hwarm : IsWarm (ofReal M) μⱼ (ellGaussianProb K δ σⱼ²)`** — the per-phase warm start.
  `WarmChain.lean` proves the `n`-free constants `√e` (`isWarm_coolLaw_succ_sqrt_exp`) and
  `e` (`isWarm_coolLaw_succ_exp`), but those are warmness of `coolLaw i` **for `coolLaw (i+1)`**
  — the Gaussian-weighted *uniform* phase laws.  The speedy chain's stationary law
  `ellGaussianProb` carries an extra factor `ℓ`, and the reweighting bridge between the two is
  **not proved in this repository**.  `M` therefore stays a hypothesis, with `hM : 1 ≤ M`;
  substituting `M = √e` (so `log M = 1/2`) is legitimate arithmetic only once that bridge
  exists.
* **`hm`** — the identification of `ColdStart.lean`'s existentially-bound phase count with
  `generalPhaseCount n κ L'`.  True by construction (the docstring of
  `cold_start_annealing_witness` states the witness), but the theorem's `∃` hides it.
* **`hsigmax`** — that `σmax` dominates every phase's `σⱼ`; see above.
* **`hσn : 4 ≤ σ·√n`** — the regime side condition, with the cold-phase failure recorded above.

## The chain mismatch in §5, stated honestly

`WastedSteps.lean` converts speedy steps to ball-walk steps for the **uniform** speedy walk
(`speedyWalk K δ`, stationary law `ellProb K δ`).  The step count of §§1–4 is for the
**Gaussian** speedy chain (`speedyMetropolisGaussian K δ σ²`, stationary law
`ellGaussianProb K δ σ²`).  No Gaussian analogue of `WastedSteps.lean` exists in this
repository.  §5 is therefore stated verbatim over the uniform chain, with the total step count
`m·t` supplied as a plain natural number; reading it as "the ball-walk cost of the Gaussian
sampler" is **not** licensed by anything proved here.

`WastedSteps.lean`'s own caveat is preserved and must be quoted with §5: the left-hand side is
`∑_{i<T} E_{Qᵢ}[mean holding time]`, a sum of **per-step conditional expectations** — the
quantity Cousins–Vempala bound by linearity of expectation — and **not** the path-level number
of ball-walk steps a single trajectory takes.  The path-level time change is
`TrajTransfer.lean`'s unproved item.

## Audit surface (`CLAUDE.md` §11)

* **Capstones**: `mixesWithin_lazy_speedyMetropolisGaussian_kls` (§1),
  `total_speedy_steps_poly_varBudget` (§4), `sum_ballWalk_cost_phases_le` (§5).  Read the
  types only.
* **Hypotheses carried unproved**: the five listed above, each an inline binder.
* **Non-vacuity**: `sampler_step_count_witness`, which discharges every binder of §§1–5
  simultaneously at `n = 21`, `K = B(0,1)`, `σ = 100`, `R = 1`, `M = 1`, `ε = 1/2`,
  `m = 10⁸`, and exhibits the numeric total `m·t ≤ 2·10²³`.
* **Semantic `def`s**: none.  This file introduces no `def`, no `structure`, no `class`, no
  `axiom` and no named `Prop`; every step count is written out in the statement that uses it,
  so no name stands in for a proof.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

variable {n : ℕ}

/-! ## 1. One phase, at `δ = 1/(2n)`

The mixing theorem `Arlib.mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit` with the
step size fixed at the `KLS97Shell.lean` regime.  Only two things happen: the deadline is
rewritten (`4·640²/(1/(2n))² = 6553600·n²` extra), and `hδσ` is re-expressed as `4 ≤ σ·√n`. -/

/-- **The per-phase speedy step count at `δ = 1/(2n)`.**

The lazy speedy Metropolis–Gaussian chain at step size `δ = 1/(2n)` mixes to within `ε` of its
own stationary law `ellGaussianProb K δ σ²` from an `M`-warm start after

    `t ≥ 6553600·σ²·n³·(log M + 2·log(1/ε)) / (log 2)² + 1`

steps, where `6553600 = 4·4·640²`.

Every binder is `Arlib.mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit`'s, with one
replacement: that theorem's `hδ : 0 < δ` is discharged from `hn`, and its `hδσ : δ ≤ σ/(8√n)`
becomes the binder `hσn : 4 ≤ σ·√n`, which is *equivalent* to it at `δ = 1/(2n)` — see the
module docstring for what that costs at the cold end of the annealing schedule.

This is a step-count statement about a Markov chain.  It is not a running-time statement; see
the module docstring's scope paragraph. -/
theorem mixesWithin_lazy_speedyMetropolisGaussian_kls (hn : 21 ≤ n) {σ R : ℝ}
    (hσ : 0 < σ) (hσn : 4 ≤ σ * Real.sqrt n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hK0 : volume K ≠ 0) (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRσ : R ≤ 2 * σ * Real.sqrt n)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M eps : ℝ}
    (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 (ellGaussianProb K (1 / (2 * (n : ℝ))) (σ ^ 2)))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 6553600 * σ ^ 2 * (n : ℝ) ^ 3 * (Real.log M + 2 * Real.log (1 / eps))
      / Real.log 2 ^ 2 + 1 ≤ (t : ℝ)) :
    MixesWithin (lazy (speedyMetropolisGaussian K (1 / (2 * (n : ℝ))) (σ ^ 2)))
      (ellGaussianProb K (1 / (2 * (n : ℝ))) (σ ^ 2)) mu0 t (ENNReal.ofReal eps) := by
  have hnR : (21 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn0
  have hδ : (0 : ℝ) < 1 / (2 * (n : ℝ)) := by positivity
  have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hsn : (0 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hspos : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hδσ : 1 / (2 * (n : ℝ)) ≤ σ / (8 * Real.sqrt (n : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.2 hσn) hsn]
  refine mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit hn hσ hδ hδσ hK hKc hK0
    hR hKR hRσ hM hwarm heps0 heps1 ?_
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have heq : 4 * 640 ^ 2 * σ ^ 2 * (n : ℝ) * (Real.log M + 2 * Real.log (1 / eps))
        / (1 / (2 * (n : ℝ)) * Real.log 2) ^ 2
      = 6553600 * σ ^ 2 * (n : ℝ) ^ 3 * (Real.log M + 2 * Real.log (1 / eps))
        / Real.log 2 ^ 2 := by
    field_simp
    ring
  rw [heq]
  exact ht

/-! ## 2. Every phase, at one budget

The annealing schedule keeps the body `K` fixed and raises the variance.  Phase `j` runs the
chain at variance `σⱼ²` from a start `μⱼ`, and the deadline of §1 is increasing in `σ`, so a
single budget computed at a dominating `σmax` serves every phase at once. -/

/-- **All `m` phases mix within the same budget.**

For a family of variances `σ : ℕ → ℝ` and starts `μ : ℕ → Measure _` sharing the body `K`,
every phase `j < m` mixes to within `ε` after

    `t = ⌈6553600·σmax²·n³·(log M + 2·log(1/ε))/(log 2)² + 1⌉₊`

speedy steps, where `σmax` dominates every `σⱼ`.  The per-phase hypotheses are §1's, imposed
for `j < m` only; `hσmax` is the domination.

`M` is one warmness constant serving every phase — the shape `WarmChain.lean` supplies for the
*cooling laws*.  See the module docstring: the bridge from `coolLaw` warmness to warmness for
`ellGaussianProb` is not proved in this repository, so `hwarm` is a binder here. -/
theorem mixesWithin_all_phases_kls (hn : 21 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hK0 : volume K ≠ 0) {R : ℝ} (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    {m : ℕ} {sig : ℕ → ℝ} {mu : ℕ → Measure (EuclideanSpace ℝ (Fin n))}
    (hmu : ∀ j, IsProbabilityMeasure (mu j))
    (hsig0 : ∀ j < m, 0 < sig j) (hsign : ∀ j < m, 4 ≤ sig j * Real.sqrt n)
    (hRsig : ∀ j < m, R ≤ 2 * sig j * Real.sqrt n)
    {M eps sigmax : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hwarm : ∀ j < m, IsWarm (ENNReal.ofReal M) (mu j)
      (ellGaussianProb K (1 / (2 * (n : ℝ))) (sig j ^ 2)))
    (hsigmax : ∀ j < m, sig j ≤ sigmax) :
    ∀ j < m, MixesWithin (lazy (speedyMetropolisGaussian K (1 / (2 * (n : ℝ))) (sig j ^ 2)))
      (ellGaussianProb K (1 / (2 * (n : ℝ))) (sig j ^ 2)) (mu j)
      ⌈6553600 * sigmax ^ 2 * (n : ℝ) ^ 3 * (Real.log M + 2 * Real.log (1 / eps))
        / Real.log 2 ^ 2 + 1⌉₊ (ENNReal.ofReal eps) := by
  have hX : 0 ≤ Real.log M + 2 * Real.log (1 / eps) := by
    have h1 : 0 ≤ Real.log M := Real.log_nonneg hM
    have h2 : 0 ≤ Real.log (1 / eps) :=
      Real.log_nonneg (by rw [le_div_iff₀ heps0]; linarith)
    linarith
  have hlog2 : (0 : ℝ) < Real.log 2 ^ 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  intro j hj
  haveI := hmu j
  refine mixesWithin_lazy_speedyMetropolisGaussian_kls hn (hsig0 j hj) (hsign j hj) hK hKc hK0
    hR hKR (hRsig j hj) hM (hwarm j hj) heps0 heps1 ?_
  have hsq : sig j ^ 2 ≤ sigmax ^ 2 := by
    nlinarith [hsig0 j hj, hsigmax j hj]
  have hn3 : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
  have hmono : 6553600 * sig j ^ 2 * (n : ℝ) ^ 3 * (Real.log M + 2 * Real.log (1 / eps))
        / Real.log 2 ^ 2
      ≤ 6553600 * sigmax ^ 2 * (n : ℝ) ^ 3 * (Real.log M + 2 * Real.log (1 / eps))
        / Real.log 2 ^ 2 := by
    rw [div_le_div_iff₀ hlog2 hlog2]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.2 hsq) hn3) hX) hlog2.le]
  have hceil := Nat.le_ceil (6553600 * sigmax ^ 2 * (n : ℝ) ^ 3
    * (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 + 1)
  linarith

/-! ## 3. The total number of speedy steps

The phase count.  `ColdStart.lean` runs `GeneralRate.lean`'s explicit construction at the
raised log-target `L' = 3·log(nR²) + 4·log(256(n+1)/κ²)`, i.e. at
`m = generalPhaseCount n κ L' = ⌈32(n+1)L'²/κ⌉₊`, for which `generalPhaseCount_le` gives

    `m ≤ 32(n+1)L'²/κ + 1`.

`cold_start_annealing_witness` states only `∃ m, 32 ≤ m ∧ …`, so that upper bound is *not*
recoverable from its type; it enters below as the binder `hm`, and
`total_speedy_steps_le_generalPhaseCount` discharges `hm` for the stated choice. -/

/-- **Total speedy steps: phase count times per-phase budget.**

Pure accounting: `m·t ≤ (32(n+1)L²/κ + 1)·(D + 1)` where `D` is §2's per-phase deadline and
`t = ⌈D⌉₊` is §2's budget.  The `+1` on the right is `⌈D⌉₊ < D + 1`.

`m` is a number of phases and `t` a number of speedy steps; the product is a number of speedy
steps and nothing else — no cost model is involved. -/
theorem total_speedy_steps_le (hn : 21 ≤ n) {m : ℕ} {sigmax M eps κ L : ℝ}
    (hκ0 : 0 < κ) (hL : 1 ≤ L) (_hsigmax : 0 ≤ sigmax) (hM : 1 ≤ M)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hm : (m : ℝ) ≤ 32 * ((n : ℝ) + 1) * L ^ 2 / κ + 1) :
    ((m * ⌈6553600 * sigmax ^ 2 * (n : ℝ) ^ 3 * (Real.log M + 2 * Real.log (1 / eps))
          / Real.log 2 ^ 2 + 1⌉₊ : ℕ) : ℝ)
      ≤ (32 * ((n : ℝ) + 1) * L ^ 2 / κ + 1)
        * (6553600 * sigmax ^ 2 * (n : ℝ) ^ 3 * (Real.log M + 2 * Real.log (1 / eps))
            / Real.log 2 ^ 2 + 2) := by
  have hX : 0 ≤ Real.log M + 2 * Real.log (1 / eps) := by
    have h1 : 0 ≤ Real.log M := Real.log_nonneg hM
    have h2 : 0 ≤ Real.log (1 / eps) :=
      Real.log_nonneg (by rw [le_div_iff₀ heps0]; linarith)
    linarith
  have hlog2 : (0 : ℝ) < Real.log 2 ^ 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  have hD0 : (0 : ℝ) ≤ 6553600 * sigmax ^ 2 * (n : ℝ) ^ 3
      * (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 + 1 := by positivity
  have hceil : ((⌈6553600 * sigmax ^ 2 * (n : ℝ) ^ 3
        * (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 + 1⌉₊ : ℕ) : ℝ)
      ≤ 6553600 * sigmax ^ 2 * (n : ℝ) ^ 3 * (Real.log M + 2 * Real.log (1 / eps))
          / Real.log 2 ^ 2 + 2 := by
    have := Nat.ceil_lt_add_one hD0
    linarith
  have hAnn : (0 : ℝ) ≤ 32 * ((n : ℝ) + 1) * L ^ 2 / κ + 1 := by positivity
  have hcast : ((m * ⌈6553600 * sigmax ^ 2 * (n : ℝ) ^ 3
        * (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 + 1⌉₊ : ℕ) : ℝ)
      = (m : ℝ) * ((⌈6553600 * sigmax ^ 2 * (n : ℝ) ^ 3
        * (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 + 1⌉₊ : ℕ) : ℝ) := by
    push_cast; ring
  rw [hcast]
  exact mul_le_mul hm hceil (Nat.cast_nonneg _) hAnn

/-- **The same bound with `hm` discharged at `ColdStart.lean`'s stated phase count.**

`m = generalPhaseCount n κ L = ⌈32(n+1)L²/κ⌉₊` is the witness `cold_start_annealing_witness`
constructs (at `κ = varBudget (ε/2)` and `L` the raised log-target `L'`); `generalPhaseCount_le`
is the bound.  What is *not* proved is that the `m` bound by that theorem's `∃` is this one —
its type does not say so. -/
theorem total_speedy_steps_le_generalPhaseCount (hn : 21 ≤ n) {sigmax M eps κ L : ℝ}
    (hκ0 : 0 < κ) (hL : 1 ≤ L) (hsigmax : 0 ≤ sigmax) (hM : 1 ≤ M)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    ((GaussianCooling.generalPhaseCount n κ L
        * ⌈6553600 * sigmax ^ 2 * (n : ℝ) ^ 3 * (Real.log M + 2 * Real.log (1 / eps))
          / Real.log 2 ^ 2 + 1⌉₊ : ℕ) : ℝ)
      ≤ (32 * ((n : ℝ) + 1) * L ^ 2 / κ + 1)
        * (6553600 * sigmax ^ 2 * (n : ℝ) ^ 3 * (Real.log M + 2 * Real.log (1 / eps))
            / Real.log 2 ^ 2 + 2) :=
  total_speedy_steps_le hn hκ0 hL hsigmax hM heps0 heps1
    (GaussianCooling.generalPhaseCount_le hκ0)

end Arlib.MarkovChains
