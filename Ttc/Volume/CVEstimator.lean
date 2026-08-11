/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CousinsVempala

/-!
# `Volume/CVEstimator`: §5.2's estimator, with the sample count made explicit

Cousins–Vempala, *Gaussian Cooling and `O*(n³)` Algorithms for Volume and Gaussian Volume*
(arXiv:1409.6011), §5.2 — the telescoping estimator, Chebyshev, and the median boost.

`Ttc/Volume/CousinsVempala.lean` already carries most of §5.2: the telescoping identity
(`Ttc.CV.prod_range_ratio`, `Ttc.CV.prod_fin_ratio`), Chebyshev in relative-error form
(`Ttc.CV.measure_notMem_relErr_le`), the product estimator's accuracy
(`Ttc.CV.prod_relErr_ge`, `Ttc.CV.run_relErr_four_fifths`,
`Ttc.CV.run_relErr_four_fifths_approxMean`) and the median boost
(`Ttc.CV.median_relErr_ge`). **None of that is reproved here.** What was missing, and what
this file supplies, is the step that connects §5.1's variance bound to §5.2's variance
*budget*:

> §5.1 bounds the relative second moment of a **single** phase score by a constant `c`
> (`Arlib.GaussianCooling.fixed_var_bound_ratio_indicator`: `c = 1 + 2/n`). §5.2's
> Chebyshev step consumes `1 + κ/m`, which for a large phase count is far smaller. The
> gap is closed by averaging `k` samples — and `k` is a **cost**, which an accuracy-only
> statement is otherwise silent about.

## What is proved

* `avgOf` — the empirical mean of `k` scores. A `def` with no semantic content: it *is*
  `(∑ⱼ Yⱼ)/k`, and asserts nothing.
* `integral_avgOf` — the empirical mean is unbiased.
* `variance_avgOf_le` — `Var(Ȳ) ≤ v/k` for pairwise independent scores of variance `≤ v`.
* `avgOf_sq_moment_le` — hence relative second moment `1 + (c − 1)/k`.
* `sample_count_meets_budget`, `avgOf_sq_moment_le_budget` — **the sample count**:
  `k ≥ (c − 1)·m/κ` samples per phase put the per-phase relative second moment at
  `1 + κ/m`, which is exactly `Ttc.CV.run_relErr_four_fifths`'s `hvar`.
* `avgOf_relErr_ge`, `avgOf_relErr_three_quarters` — **per-ratio Chebyshev**: one phase's
  empirical mean is within a relative `δ` with probability `≥ 1 − (c − 1)/(k·δ²)`, hence
  `≥ 3/4` once `k ≥ 4(c − 1)/δ²`.
* `prod_bounds_of_perFactor`, `prod_relErr_of_perFactor` — **error composition**: for
  `0 ≤ ε ≤ 1`, `m` factors each within a relative `ε/m` of positive targets satisfy
  `(1 − ε)·∏aᵢ ≤ ∏xᵢ ≤ e^ε·∏aᵢ`, i.e. `∏xᵢ ∈ relErr (e^ε − 1) (∏aᵢ)`. The `e^ε − 1` is
  the honest slack and is **not** rounded down to `ε`.
* `cool_telescope` — the telescoping identity specialized to the schedule that actually
  anneals (`coolPhases`/`coolRate`), packaged with `Ttc.CV.cool_schedule_anneals` so that
  the endpoint is recorded as genuinely cooled. The fixed-rate schedule satisfies the
  identity and provably fails the annealing
  (`Arlib.GaussianCooling.geomSchedule_total_cooling_lt`), which is why the specialization
  is worth stating.
* `run_four_fifths_of_samples` — **the assembly for one run**: `m` phases, `k` samples
  each, per-phase score `avgOf k (Y i)`, output `A 0 · ∏ᵢ avgOf k (Y i)`, correct to a
  relative `ε₀ ≥ ε + τ + ε·τ` with probability `≥ 4/5`.
* `median_accuracy_of_samples` — **the same amplified**: the median of `r` independent runs
  is correct with probability `≥ 1 − p` once `r ≥ log(1/p)/(2(4/5 − 1/2)²) = (50/9)·log(1/p)`.
* `volume_accuracy_of_samples` — the same with the conclusion written in
  `Ttc.VolumeAlgorithm`'s shape, `(1 − ε₀)·Vol(K) ≤ z ≤ (1 + ε₀)·Vol(K)` with probability
  `≥ 1 − p`, given the endpoint identification `A m = Vol(K)` as a binder.

## The sample count, stated in the same breath as the accuracy

`median_accuracy_of_samples` and `volume_accuracy_of_samples` demand

  `k ≥ (c − 1)·m/κ` samples per phase,  `m` phases,  `r ≥ (50/9)·log(1/p)` runs,

hence **`r·m·k ≥ (50/9)·log(1/p)·(c − 1)·m²/κ` samples in total**. At §5.1's
`c = 1 + 2/n` this is `(100/9)·log(1/p)·m²/(n·κ)`, and at the annealing schedule
`m = coolPhases n L κ = ⌈8(n+1)L²/κ⌉` it is `Θ(n·L⁴·log(1/p)/κ³)` samples.

**Nothing here bounds the cost of producing one sample**, and therefore nothing here is a
running-time statement. In particular *this file must not be quoted as establishing
`O*(n³)`*: that claim needs the mixing/isoperimetry half of the critical path
(`thm:iso` → `thm:speedyconductance` → sampling), which `CV-ROADMAP.md` §0′ records as
open, and the only sampler constants available in this repository are exponential in `n`.

## Why the per-ratio route is not the assembly

The brief's items 2 and 3 describe a route — bound each ratio to `ε/m` at confidence `3/4`,
then multiply — and both steps are proved here (`avgOf_relErr_three_quarters`,
`prod_relErr_of_perFactor`). They do **not** chain: `m` events of probability `3/4` give no
useful intersection bound, and a union bound would need per-phase confidence `1 − 1/(4m)`,
i.e. `k ≳ m³/ε²` samples per phase. The paper's route, and the one the assembly takes,
bounds the *product's* relative second moment once
(`Arlib.GaussianCooling.prod_sq_div_le_exp`) and applies Chebyshev once, costing
`k ≳ m/κ`. The two lemmas are kept because they are the honest statement of what the
per-ratio route gives, and because the comparison is the reason the cheaper route is used.

## What is assumed

Every residual assumption is an explicit named binder of
`run_four_fifths_of_samples` / `median_accuracy_of_samples` / `volume_accuracy_of_samples`.
None is an `axiom`, and none is hidden in a `def`.

* `hsampler : ∀ i, ν i ∈ relErr η (A (i+1) / A i)` — **this is the sampler, and it is where
  the open half of the critical path plugs in.** Its shape is exactly the conclusion of
  `Ttc.CV.sampledPhase_mean_mem_relErr`, which derives it from an `Arlib.TVLe` bound
  between the law of the sample and `Arlib.GaussianCooling.coolLaw`. **Caveat, stated
  rather than glossed:** `Ttc.HitAndRunTheorem11Input.at_steps` supplies `Arlib.TVLe` to
  `Arlib.uniformOn volume K`, the *uniform* target — not to the cooled Gaussian the phases
  need. Bridging uniform to Gaussian is §4's speedy-walk/Metropolis machinery and is not
  attempted here.
* `hsample_mean : ∀ i j, ∫ Y i j = ν i` — the `k` samples of a phase share a mean. True of
  `k` runs of the same chain to the same step count; false if the runs are truncated at
  different lengths.
* `hsample_sq : ∀ i j, ∫ (Y i j)² ≤ c·(ν i)²` — §5.1's single-sample variance bound, at the
  *realised* (sampled) law rather than the exact one. `Ttc.CV.hvar_exact_of_coolRate_all`
  proves the exact-law version at the annealing schedule; transporting it across TV is
  `Ttc.VolumeAlgorithm.cousinsVempalaOfSampler`'s `hslack_var`, not redone here.
* `hindep_in`, `hindep_ph`, `hindep_runs` — pairwise independence within a phase,
  independence across phases, independence across runs. All three follow from joint
  independence of the whole `r × m × k` array, but Mathlib has no `iIndepFun` grouping
  lemma for functions of disjoint blocks (it has `iIndepFun.indepFun_finset`, a *pairwise*
  statement between two disjoint finsets), so they are taken as separate binders.
* `hprod`, `hL2`, `hrun_meas` — `L²` and measurability guards.
* `hApos`, `hend : A m = Vol(K)` — the chain is positive, and its endpoint *is* the volume.
  `hend` is an idealization: `Ttc.CV.G_indicator_mem_relErr` shows the last Gaussian is only
  within a relative `1 − e^{−R²/(2σ_m²)}` of `Vol(K)`. Absorbing that is
  `Ttc.CV.relErr_trans`'s job in `Ttc.VolumeAlgorithm.cousinsVempalaOfBiasedEnd`; keeping it
  a binder here keeps the two idealizations separable.

## Non-vacuity

**`run_bundle_inhabited` is the statement an auditor should read.** Its *type* is an
existential over `run_four_fifths_of_samples`' entire mathematical hypothesis list, so it
certifies satisfiability without the reader having to inspect a proof term — and it does so
for a **two-parameter family**, every sample count `k ≥ 1` and every target `b > 0`, with
`A 1 = b` pinned so the family is not secretly a point.

`run_bundle_nonvacuous`, `run_bundle_nonvacuous_one`/`_two` (the required **pair**, at
`k = 1, b = 1` and `k = 2, b = 3`; `witChain_one_ne_three` shows the data really differ) and
`median_bundle_nonvacuous` (the median-level bundle of `median_accuracy_of_samples`, at
`r = 4` runs and the informative confidence `p = 1/2`) additionally *apply* the assembly
theorems at that data. **For these four, the certification is the proof term, not the
displayed inequality** — each displayed conclusion is a weak statement that could be proved
on its own; what carries the content is that the proof is a
`refine run_four_fifths_of_samples …` / `refine median_accuracy_of_samples …` application
with every hypothesis discharged.

The witness is degenerate in the way `CLAUDE.md` §11 warns about and this is flagged, not
hidden: its scores are deterministic, so `hsampler` holds at `η = 0`, which is precisely
what no real sampler achieves. It certifies that the bundle is satisfiable, not that the
paper's Gaussian phases satisfy it.
-/

namespace Ttc

open MeasureTheory Set ProbabilityTheory Arlib.GaussianCooling

namespace CVEst

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The empirical mean of `k` scores.** Purely a piece of arithmetic: `avgOf k Y ω` is
`(Y 0 ω + … + Y (k−1) ω)/k`. The name asserts nothing beyond that. -/
noncomputable def avgOf {Ω : Type*} (k : ℕ) (Y : Fin k → Ω → ℝ) (ω : Ω) : ℝ :=
  (∑ j, Y j ω) / (k : ℝ)

omit [MeasurableSpace Ω] in
/-- `avgOf` as a scalar multiple of a `Finset` sum of functions — the shape Mathlib's
variance lemmas are stated in. -/
theorem avgOf_eq_const_mul {k : ℕ} (Y : Fin k → Ω → ℝ) :
    avgOf k Y = fun ω => (k : ℝ)⁻¹ * (∑ j, Y j) ω := by
  funext ω
  simp [avgOf, Finset.sum_apply, div_eq_inv_mul]

/-- **The empirical mean is unbiased.** If every score has mean `ν`, so does their
average. -/
theorem integral_avgOf {k : ℕ} (hk : 0 < k) {Y : Fin k → Ω → ℝ}
    (hint : ∀ j, Integrable (Y j) μ) {ν : ℝ} (hmean : ∀ j, ∫ ω, Y j ω ∂μ = ν) :
    ∫ ω, avgOf k Y ω ∂μ = ν := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hsum : ∫ ω, (∑ j, Y j ω) ∂μ = (k : ℝ) * ν := by
    rw [integral_finsetSum _ (fun j _ => hint j)]
    simp [hmean, Finset.card_univ]
  calc ∫ ω, avgOf k Y ω ∂μ = ∫ ω, (∑ j, Y j ω) / (k : ℝ) ∂μ := rfl
    _ = (∫ ω, (∑ j, Y j ω) ∂μ) / (k : ℝ) := by rw [integral_div]
    _ = ν := by rw [hsum]; field_simp

/-- The average of `k` `L²` scores is `L²`. -/
theorem memLp_avgOf {k : ℕ} {Y : Fin k → Ω → ℝ} (hL2 : ∀ j, MemLp (Y j) 2 μ) :
    MemLp (avgOf k Y) 2 μ := by
  rw [avgOf_eq_const_mul]
  exact (memLp_finsetSum' _ (fun j _ => hL2 j)).const_mul _

/-- **Variance reduction by averaging.** `k` pairwise-independent scores, each of variance
at most `v`, have empirical mean of variance at most `v/k`.

This is the only place the sample count enters the estimator's accuracy, and it is what
`Ttc.CV.run_relErr_four_fifths`'s `hvar` hypothesis silently presupposes: §5.1 bounds the
*single-sample* relative second moment by a constant `c` that does **not** shrink with the
phase count, so the per-phase budget `1 + κ/m` is bought by averaging, at the price
quantified in `avgOf_sq_moment_le_budget` below. -/
theorem variance_avgOf_le {k : ℕ} (hk : 0 < k) {Y : Fin k → Ω → ℝ}
    (hL2 : ∀ j, MemLp (Y j) 2 μ)
    (hindep : Pairwise fun i j => IndepFun (Y i) (Y j) μ)
    {v : ℝ} (hvar : ∀ j, variance (Y j) μ ≤ v) :
    variance (avgOf k Y) μ ≤ v / (k : ℝ) := by
  have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hv0 : 0 ≤ v := le_trans (variance_nonneg (Y ⟨0, hk⟩) μ) (hvar ⟨0, hk⟩)
  have hsum : variance (∑ j, Y j) μ = ∑ j, variance (Y j) μ :=
    IndepFun.variance_sum (fun j _ => hL2 j) (fun i _ j _ hij => hindep hij)
  have hle : ∑ j, variance (Y j) μ ≤ (k : ℝ) * v := by
    refine le_trans (Finset.sum_le_sum (fun j _ => hvar j)) ?_
    simp [Finset.card_univ, mul_comm]
  rw [avgOf_eq_const_mul]
  have := variance_const_mul (k : ℝ)⁻¹ (∑ j, Y j) μ
  rw [this, hsum]
  rw [div_eq_inv_mul, inv_pow]
  have hkk : ((k : ℝ) ^ 2)⁻¹ * ((k : ℝ) * v) = (k : ℝ)⁻¹ * v := by
    field_simp
  calc ((k : ℝ) ^ 2)⁻¹ * ∑ j, variance (Y j) μ
      ≤ ((k : ℝ) ^ 2)⁻¹ * ((k : ℝ) * v) := by
        exact mul_le_mul_of_nonneg_left hle (by positivity)
    _ = (k : ℝ)⁻¹ * v := hkk

/-- **The relative second moment of the empirical mean.** If each of `k` pairwise
independent scores has mean `ν` and relative second moment at most `c`, then their
empirical mean has mean `ν` and relative second moment at most `1 + (c − 1)/k`.

This is the missing link between §5.1 and §5.2: §5.1 delivers a *fixed* `c` (e.g.
`Arlib.GaussianCooling.fixed_var_bound_ratio_indicator`'s `1 + 2/n`), while §5.2's
`Ttc.CV.run_relErr_four_fifths` consumes `1 + κ/m`. Averaging converts one into the other,
and `k` is the conversion rate. -/
theorem avgOf_sq_moment_le [IsProbabilityMeasure μ] {k : ℕ} (hk : 0 < k) {Y : Fin k → Ω → ℝ}
    (hL2 : ∀ j, MemLp (Y j) 2 μ)
    (hindep : Pairwise fun i j => IndepFun (Y i) (Y j) μ)
    {c ν : ℝ} (hmean : ∀ j, ∫ ω, Y j ω ∂μ = ν)
    (hc : ∀ j, ∫ ω, (Y j ω) ^ 2 ∂μ ≤ c * ν ^ 2) :
    ∫ ω, (avgOf k Y ω) ^ 2 ∂μ ≤ (1 + (c - 1) / (k : ℝ)) * ν ^ 2 := by
  have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hvarj : ∀ j, variance (Y j) μ ≤ (c - 1) * ν ^ 2 := by
    intro j
    have h := variance_eq_sub (μ := μ) (hL2 j)
    have hsq : μ[(Y j) ^ 2] = ∫ ω, (Y j ω) ^ 2 ∂μ := by simp
    rw [hsq, hmean j] at h
    have := hc j
    rw [h]; linarith
  have hvA := variance_avgOf_le (μ := μ) hk hL2 hindep hvarj
  have hmA : MemLp (avgOf k Y) 2 μ := memLp_avgOf hL2
  have hIA : ∫ ω, avgOf k Y ω ∂μ = ν :=
    integral_avgOf hk (fun j => (hL2 j).integrable one_le_two) hmean
  have h := variance_eq_sub (μ := μ) hmA
  have hsqA : μ[(avgOf k Y) ^ 2] = ∫ ω, (avgOf k Y ω) ^ 2 ∂μ := by simp
  rw [hsqA, hIA] at h
  have hsplit : (1 + (c - 1) / (k : ℝ)) * ν ^ 2 = ν ^ 2 + (c - 1) * ν ^ 2 / (k : ℝ) := by
    field_simp
  rw [hsplit]
  linarith [h, hvA]

/-! ## The sample count

`avgOf_sq_moment_le` prices the per-phase budget in samples. Everything below is that
price, made explicit. -/

/-- **The sample count that buys the per-phase budget.** With a single-sample relative
second moment `c` and `m` phases, `k ≥ (c − 1)·m/κ` samples per phase reduce the relative
second moment to `1 + κ/m`. -/
theorem sample_count_meets_budget {c κ : ℝ} {k m : ℕ} (hκ : 0 < κ)
    (hm : 0 < m) (hk : 0 < k) (hkge : (c - 1) * (m : ℝ) / κ ≤ (k : ℝ)) :
    1 + (c - 1) / (k : ℝ) ≤ 1 + κ / (m : ℝ) := by
  have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnum : (c - 1) * (m : ℝ) ≤ κ * (k : ℝ) := by
    have := (div_le_iff₀ hκ).1 hkge
    linarith
  have : (c - 1) / (k : ℝ) ≤ κ / (m : ℝ) := by
    rw [div_le_div_iff₀ hk' hm']
    nlinarith
  linarith

/-- **The per-phase estimator, at the budget.** `k ≥ (c − 1)·m/κ` samples put the empirical
mean's relative second moment inside `Ttc.CV.run_relErr_four_fifths`'s `hvar`. -/
theorem avgOf_sq_moment_le_budget [IsProbabilityMeasure μ] {k m : ℕ} (hk : 0 < k)
    (hm : 0 < m) {Y : Fin k → Ω → ℝ}
    (hL2 : ∀ j, MemLp (Y j) 2 μ)
    (hindep : Pairwise fun i j => IndepFun (Y i) (Y j) μ)
    {c ν κ : ℝ} (hκ : 0 < κ)
    (hmean : ∀ j, ∫ ω, Y j ω ∂μ = ν)
    (hcm : ∀ j, ∫ ω, (Y j ω) ^ 2 ∂μ ≤ c * ν ^ 2)
    (hkge : (c - 1) * (m : ℝ) / κ ≤ (k : ℝ)) :
    ∫ ω, (avgOf k Y ω) ^ 2 ∂μ ≤ (1 + κ / (m : ℝ)) * ν ^ 2 := by
  refine le_trans (avgOf_sq_moment_le hk hL2 hindep hmean hcm) ?_
  exact mul_le_mul_of_nonneg_right
    (sample_count_meets_budget hκ hm hk hkge) (sq_nonneg ν)

/-! ## Per-ratio Chebyshev

The tail bound for **one** phase's empirical mean. Recorded because the brief asks for it;
the *assembly* below does not route through it, and cannot — see the module docstring's
"Why the per-ratio route is not the assembly". -/

/-- Subadditivity turns a bound on a failure event into a lower bound on the success
event's real-valued measure. The complementary sets cover `univ`, so no measurability of
either is needed. -/
theorem measureReal_ge_of_compl_le [IsProbabilityMeasure μ] {P : Ω → Prop} {b : ℝ}
    (hb : 0 ≤ b) (h : μ {ω | ¬ P ω} ≤ ENNReal.ofReal b) : 1 - b ≤ μ.real {ω | P ω} := by
  have hbad : μ.real {ω | ¬ P ω} ≤ b := by
    rw [measureReal_def]
    refine le_trans (ENNReal.toReal_mono (by finiteness) h) ?_
    rw [ENNReal.toReal_ofReal hb]
  have hcov : (1 : ℝ) ≤ μ.real {ω | P ω} + μ.real {ω | ¬ P ω} := by
    have hsub : (Set.univ : Set Ω) ⊆ {ω | P ω} ∪ {ω | ¬ P ω} := by
      intro ω _; by_cases hP : P ω
      · exact Or.inl hP
      · exact Or.inr hP
    have h1 : μ Set.univ ≤ μ {ω | P ω} + μ {ω | ¬ P ω} :=
      le_trans (measure_mono hsub) (measure_union_le _ _)
    have h2 : (μ Set.univ).toReal ≤ (μ {ω | P ω} + μ {ω | ¬ P ω}).toReal :=
      ENNReal.toReal_mono (by finiteness) h1
    rw [measure_univ, ENNReal.toReal_one,
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h2
    exact h2
  linarith

/-- **A relative second moment is at least `1`.** Cauchy–Schwarz, in the form the
hypotheses below are stated in: `E(X²) ≥ E(X)²`, so `E(X²) ≤ c·ν²` with `ν = E(X) ≠ 0`
forces `1 ≤ c`. Used so that no lemma here has to *assume* `1 ≤ c`. -/
theorem one_le_of_sq_moment_le [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ)
    {c ν : ℝ} (hν : ν ≠ 0) (hmean : ∫ ω, X ω ∂μ = ν)
    (hc : ∫ ω, (X ω) ^ 2 ∂μ ≤ c * ν ^ 2) : 1 ≤ c := by
  have h := variance_eq_sub (μ := μ) hX
  have hsq : μ[X ^ 2] = ∫ ω, (X ω) ^ 2 ∂μ := by simp
  rw [hsq, hmean] at h
  have hv : 0 ≤ variance X μ := variance_nonneg _ _
  have hν2 : (0 : ℝ) < ν ^ 2 := by positivity
  nlinarith

/-- **Per-ratio Chebyshev.** The empirical mean of `k` pairwise-independent scores of
common mean `ν > 0` and relative second moment `≤ c` lands within a relative `δ` of `ν`
with probability at least `1 − (c − 1)/(k·δ²)`.

This is `Ttc.CV.measure_notMem_relErr_le` fed the variance reduction of
`avgOf_sq_moment_le`; the sample count is visible in the denominator. -/
theorem avgOf_relErr_ge [IsProbabilityMeasure μ] {k : ℕ} (hk : 0 < k) {Y : Fin k → Ω → ℝ}
    (hL2 : ∀ j, MemLp (Y j) 2 μ)
    (hindep : Pairwise fun i j => IndepFun (Y i) (Y j) μ)
    {c ν δ : ℝ} (hδ : 0 < δ) (hν : 0 < ν)
    (hmean : ∀ j, ∫ ω, Y j ω ∂μ = ν)
    (hcm : ∀ j, ∫ ω, (Y j ω) ^ 2 ∂μ ≤ c * ν ^ 2) :
    1 - (c - 1) / ((k : ℝ) * δ ^ 2) ≤ μ.real {ω | avgOf k Y ω ∈ relErr δ ν} := by
  have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hc1 : 1 ≤ c := one_le_of_sq_moment_le (hL2 ⟨0, hk⟩) hν.ne' (hmean _) (hcm _)
  have hmA : MemLp (avgOf k Y) 2 μ := memLp_avgOf hL2
  have hIA : ∫ ω, avgOf k Y ω ∂μ = ν :=
    integral_avgOf hk (fun j => (hL2 j).integrable one_le_two) hmean
  have hsq := avgOf_sq_moment_le (μ := μ) hk hL2 hindep hmean hcm
  rw [← hIA] at hsq ⊢
  have hbad := CV.measure_notMem_relErr_le (μ := μ) (X := avgOf k Y) hmA hδ
    (by rw [hIA]; exact hν) hsq
  have hbnd : (1 + (c - 1) / (k : ℝ) - 1) / δ ^ 2 = (c - 1) / ((k : ℝ) * δ ^ 2) := by
    field_simp; ring
  rw [hbnd] at hbad
  have hnn : (0 : ℝ) ≤ (c - 1) / ((k : ℝ) * δ ^ 2) := by positivity
  exact measureReal_ge_of_compl_le (P := fun ω => avgOf k Y ω ∈ relErr δ (∫ ω, avgOf k Y ω ∂μ))
    hnn hbad

/-- **The paper's per-ratio confidence.** `k ≥ 4(c − 1)/δ²` samples put one phase's
empirical mean within a relative `δ` with probability at least `3/4`.

At the brief's `δ = ε/m` this reads `k ≥ 4(c − 1)m²/ε²` — quadratic in the phase count.
That is *not* the sample count the assembly below pays, and the module docstring explains
why the per-ratio route is the more expensive one. -/
theorem avgOf_relErr_three_quarters [IsProbabilityMeasure μ] {k : ℕ} (hk : 0 < k)
    {Y : Fin k → Ω → ℝ} (hL2 : ∀ j, MemLp (Y j) 2 μ)
    (hindep : Pairwise fun i j => IndepFun (Y i) (Y j) μ)
    {c ν δ : ℝ} (hδ : 0 < δ) (hν : 0 < ν)
    (hmean : ∀ j, ∫ ω, Y j ω ∂μ = ν)
    (hcm : ∀ j, ∫ ω, (Y j ω) ^ 2 ∂μ ≤ c * ν ^ 2)
    (hkge : 4 * (c - 1) / δ ^ 2 ≤ (k : ℝ)) :
    3 / 4 ≤ μ.real {ω | avgOf k Y ω ∈ relErr δ ν} := by
  have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hc1 : 1 ≤ c := one_le_of_sq_moment_le (hL2 ⟨0, hk⟩) hν.ne' (hmean _) (hcm _)
  have hmain := avgOf_relErr_ge hk hL2 hindep hδ hν hmean hcm
  have hstep : (c - 1) / ((k : ℝ) * δ ^ 2) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have h4 : 4 * (c - 1) ≤ (k : ℝ) * δ ^ 2 := by
      have := (div_le_iff₀ (by positivity : (0:ℝ) < δ ^ 2)).1 hkge
      linarith
    linarith
  linarith

/-! ## Error composition across phases

`m` ratios each good to `ε/m` multiply to a product good to `ε` on the low side and to
`e^ε − 1` on the high side. The asymmetry is real and is not rounded away: `(1 + ε/m)^m`
exceeds `1 + ε`, and the excess is exactly what `e^ε` absorbs. -/

/-- **The two-sided composition, stated exactly.** Under `0 ≤ ε ≤ 1` and positive targets,
`m` factors each within a relative `ε/m` give

  `(1 − ε)·∏ aᵢ ≤ ∏ xᵢ ≤ e^ε·∏ aᵢ`.

The low side is Bernoulli, the high side is `1 + t ≤ e^t`. Neither is tight, and neither is
weakened: this is what the arithmetic gives. -/
theorem prod_bounds_of_perFactor {m : ℕ} (hm : 0 < m) {x a : Fin m → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (ha : ∀ i, 0 < a i)
    (hx : ∀ i, x i ∈ relErr (ε / (m : ℝ)) (a i)) :
    (1 - ε) * ∏ i, a i ≤ ∏ i, x i ∧ ∏ i, x i ≤ Real.exp ε * ∏ i, a i := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hr0 : 0 ≤ ε / (m : ℝ) := by positivity
  have hr1 : ε / (m : ℝ) ≤ 1 := by
    rw [div_le_one hm']; linarith
  have hlow : ∀ i, (1 - ε / (m : ℝ)) * a i ≤ x i := fun i => (hx i).1
  have hhigh : ∀ i, x i ≤ (1 + ε / (m : ℝ)) * a i := fun i => (hx i).2
  have hxnn : ∀ i, 0 ≤ x i := fun i =>
    le_trans (mul_nonneg (by linarith) (ha i).le) (hlow i)
  have hsplitL : ∏ i, (1 - ε / (m : ℝ)) * a i
      = (1 - ε / (m : ℝ)) ^ m * ∏ i, a i := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsplitU : ∏ i, (1 + ε / (m : ℝ)) * a i
      = (1 + ε / (m : ℝ)) ^ m * ∏ i, a i := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have haprod : 0 ≤ ∏ i, a i := Finset.prod_nonneg fun i _ => (ha i).le
  constructor
  · have hstep : ∏ i, (1 - ε / (m : ℝ)) * a i ≤ ∏ i, x i :=
      Finset.prod_le_prod (fun i _ => mul_nonneg (by linarith) (ha i).le)
        (fun i _ => hlow i)
    rw [hsplitL] at hstep
    have hbern : 1 - ε ≤ (1 - ε / (m : ℝ)) ^ m := by
      have h := one_add_mul_le_pow (a := -(ε / (m : ℝ))) (by linarith) m
      have hmm : (m : ℝ) * (ε / (m : ℝ)) = ε := by field_simp
      have : 1 + (m : ℝ) * -(ε / (m : ℝ)) = 1 - ε := by rw [mul_neg, hmm]; ring
      rw [this] at h
      simpa [sub_eq_add_neg] using h
    exact le_trans (mul_le_mul_of_nonneg_right hbern haprod) hstep
  · have hstep : ∏ i, x i ≤ ∏ i, (1 + ε / (m : ℝ)) * a i :=
      Finset.prod_le_prod (fun i _ => hxnn i) (fun i _ => hhigh i)
    rw [hsplitU] at hstep
    have hexp : (1 + ε / (m : ℝ)) ^ m ≤ Real.exp ε := by
      have hbase : 1 + ε / (m : ℝ) ≤ Real.exp (ε / (m : ℝ)) := by
        have := Real.add_one_le_exp (ε / (m : ℝ)); linarith
      have hpow : (1 + ε / (m : ℝ)) ^ m ≤ (Real.exp (ε / (m : ℝ))) ^ m :=
        pow_le_pow_left₀ (by linarith) hbase m
      have hcollapse : (Real.exp (ε / (m : ℝ))) ^ m = Real.exp ε := by
        rw [← Real.exp_nat_mul]
        congr 1
        field_simp
      rwa [hcollapse] at hpow
    exact le_trans hstep (mul_le_mul_of_nonneg_right hexp haprod)

/-- **Error composition across phases, in `relErr` form.** `m` ratios each within a
relative `ε/m` multiply to within a relative `e^ε − 1`.

`e^ε − 1 ≥ ε`, so this is strictly weaker than "`ε` compose to `ε`" — which is false. The
loss is the honest price of the product form and is what the assembly below pays. -/
theorem prod_relErr_of_perFactor {m : ℕ} (hm : 0 < m) {x a : Fin m → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (ha : ∀ i, 0 < a i)
    (hx : ∀ i, x i ∈ relErr (ε / (m : ℝ)) (a i)) :
    ∏ i, x i ∈ relErr (Real.exp ε - 1) (∏ i, a i) := by
  obtain ⟨hlo, hhi⟩ := prod_bounds_of_perFactor hm hε hε1 ha hx
  have haprod : 0 ≤ ∏ i, a i := Finset.prod_nonneg fun i _ => (ha i).le
  have hexp : 1 + ε ≤ Real.exp ε := by have := Real.add_one_le_exp ε; linarith
  refine ⟨?_, ?_⟩
  · refine le_trans (mul_le_mul_of_nonneg_right ?_ haprod) hlo
    linarith
  · simpa using le_trans hhi (le_of_eq (by ring))

/-! ## The telescope, at the schedule that actually anneals

The telescoping identity itself is `Ttc.CV.prod_range_ratio` / `Ttc.CV.prod_fin_ratio` and
holds for any nowhere-zero chain; it is *not* reproved here. What is recorded is its
specialization to the general-`α` schedule `coolPhases`/`coolRate`, packaged with the
statement that that schedule's endpoint really is cooled by `e^L` — so the telescope's
right-hand end is the hot Gaussian and not, as under the fixed rate, a variance that has
barely moved (`Arlib.GaussianCooling.geomSchedule_total_cooling_lt`). -/

/-- **The telescope on the annealing schedule.** On `m = coolPhases n L κ` phases of the
geometric schedule at rate `coolRate n L κ`:

* the `m` consecutive ratios of any nowhere-zero chain `A` collapse to `A m / A 0`, so the
  run `A 0 · ∏ᵢ Wᵢ` targets `A m` exactly; and
* the schedule's terminal variance is at least `e^L·σ₀²`, i.e. the endpoint is genuinely
  the cooled one.

The first conjunct is `Ttc.CV.prod_fin_ratio`; the second is
`Ttc.CV.cool_schedule_anneals`. The point of stating them together is that the fixed-rate
schedule satisfies the first and provably fails the second. -/
theorem cool_telescope {n : ℕ} {L κ : ℝ} (hL : 1 ≤ L) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    {σsq : ℕ → ℝ} (hσ0 : 0 < σsq 0)
    (hrate : ∀ j, σsq (j + 1) = σsq j * (1 + coolRate n L κ))
    {A : ℕ → ℝ} (hA : ∀ i, A i ≠ 0) :
    A 0 * ∏ i : Fin (coolPhases n L κ), A ((i : ℕ) + 1) / A (i : ℕ)
        = A (coolPhases n L κ)
      ∧ Real.exp L * σsq 0 ≤ σsq (coolPhases n L κ) := by
  refine ⟨?_, CV.cool_schedule_anneals hL hκ0 hκ1 hσ0 hrate⟩
  rw [CV.prod_fin_ratio hA, mul_comm, div_mul_cancel₀ _ (hA 0)]

/-! ## The assembly

One run of the estimator, with every phase's score an explicit `k`-sample empirical mean.
The sampler enters through exactly one binder, `hsampler`, whose shape is
`ν i ∈ relErr η (A (i+1) / A i)` — the conclusion of
`Ttc.CV.sampledPhase_mean_mem_relErr`, i.e. what an `Arlib.TVLe` guarantee delivers. -/

/-- **One run, from samples.** `m` phases, `k` samples per phase, drawn so that

* the `k` samples of a phase are pairwise independent and share a common mean `ν i`
  (`hindep_in`, `hsample_mean`);
* that common mean is within a relative `η` of the chain ratio (`hsampler` — **this is the
  sampler**, and it is exactly the shape `Ttc.CV.sampledPhase_mean_mem_relErr` produces
  from an `Arlib.TVLe` bound);
* each sample's relative second moment is at most `c` (`hsample_sq` — this is §5.1);
* the phases are independent (`hindep_ph`).

Then, with `k ≥ (c − 1)·m/κ` samples per phase, `2mη ≤ τ < 1` and `e^κ − 1 ≤ ε²/5`, the
run `A 0 · ∏ᵢ avgOf k (Y i)` is within a relative `ε₀ ≥ ε + τ + ε·τ` of `A m` with
probability at least `4/5`.

**The sample count is `m·k ≥ (c − 1)·m²/κ` per run**, and nothing here bounds the cost of
producing one sample. -/
theorem run_four_fifths_of_samples [IsProbabilityMeasure μ] {m k : ℕ} (hm : 0 < m)
    (hk : 0 < k) {Y : Fin m → Fin k → Ω → ℝ} {A : ℕ → ℝ} {ν : Fin m → ℝ}
    {c κ ε ε₀ η τ : ℝ}
    (hκ0 : 0 < κ) (hε : 0 < ε) (hη : 0 ≤ η) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hmeanBudget : 2 * (m : ℝ) * η ≤ τ)
    (hApos : ∀ i, 0 < A i)
    (hL2 : ∀ i j, MemLp (Y i j) 2 μ)
    (hindep_in : ∀ i, Pairwise fun j j' => IndepFun (Y i j) (Y i j') μ)
    (hindep_ph : iIndepFun (fun i => avgOf k (Y i)) μ)
    (hprod : MemLp (fun ω => ∏ i, avgOf k (Y i) ω) 2 μ)
    (hsample_mean : ∀ i j, ∫ ω, Y i j ω ∂μ = ν i)
    (hsampler : ∀ i : Fin m, ν i ∈ relErr η (A ((i : ℕ) + 1) / A (i : ℕ)))
    (hsample_sq : ∀ i j, ∫ ω, (Y i j ω) ^ 2 ∂μ ≤ c * (ν i) ^ 2)
    (hkge : (c - 1) * (m : ℝ) / κ ≤ (k : ℝ))
    (hbudget : Real.exp κ - 1 ≤ ε ^ 2 / 5)
    (hcompose : ε + τ + ε * τ ≤ ε₀) :
    4 / 5 ≤ μ.real {ω | A 0 * ∏ i, avgOf k (Y i) ω ∈ relErr ε₀ (A m)} := by
  have hmeanW : ∀ i, ∫ ω, avgOf k (Y i) ω ∂μ = ν i := fun i =>
    integral_avgOf hk (fun j => (hL2 i j).integrable one_le_two) (hsample_mean i)
  refine CV.run_relErr_four_fifths_approxMean hm hκ0.le hε hη hτ0 hτ1 hmeanBudget
    hindep_ph (fun i => (memLp_avgOf (hL2 i)).aestronglyMeasurable) hprod hApos
    (fun i => by rw [hmeanW i]; exact hsampler i) (fun i => ?_) hbudget hcompose
  rw [hmeanW i]
  exact avgOf_sq_moment_le_budget hk hm (hL2 i) (hindep_in i) hκ0
    (hsample_mean i) (hsample_sq i) hkge

/-- **The estimator, amplified.** `r` independent runs of `run_four_fifths_of_samples`, each
`m` phases of `k` samples, with the median taken across runs: correct to relative error
`ε₀` with probability at least `1 − p`, once `r ≥ (50/9)·log(1/p)`.

**Total sample count: `r·m·k`, with `k ≥ (c − 1)·m/κ` and `r ≥ (50/9)·log(1/p)`** — i.e.
`≳ (50/9)·log(1/p)·(c − 1)·m²/κ` samples. No claim is made about the cost of one sample;
see the module docstring. -/
theorem median_accuracy_of_samples [IsProbabilityMeasure μ] {m k r : ℕ} (hm : 0 < m)
    (hk : 0 < k) (hr : 0 < r) {Y : Fin r → Fin m → Fin k → Ω → ℝ} {z : Ω → ℝ}
    {A : ℕ → ℝ} {ν : Fin m → ℝ} {c κ ε ε₀ η τ p : ℝ}
    (hκ0 : 0 < κ) (hε : 0 < ε) (hη : 0 ≤ η) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hmeanBudget : 2 * (m : ℝ) * η ≤ τ)
    (hApos : ∀ i, 0 < A i)
    (hL2 : ∀ t i j, MemLp (Y t i j) 2 μ)
    (hindep_in : ∀ t i, Pairwise fun j j' => IndepFun (Y t i j) (Y t i j') μ)
    (hindep_ph : ∀ t, iIndepFun (fun i => avgOf k (Y t i)) μ)
    (hprod : ∀ t, MemLp (fun ω => ∏ i, avgOf k (Y t i) ω) 2 μ)
    (hsample_mean : ∀ t i j, ∫ ω, Y t i j ω ∂μ = ν i)
    (hsampler : ∀ i : Fin m, ν i ∈ relErr η (A ((i : ℕ) + 1) / A (i : ℕ)))
    (hsample_sq : ∀ t i j, ∫ ω, (Y t i j ω) ^ 2 ∂μ ≤ c * (ν i) ^ 2)
    (hkge : (c - 1) * (m : ℝ) / κ ≤ (k : ℝ))
    (hbudget : Real.exp κ - 1 ≤ ε ^ 2 / 5)
    (hcompose : ε + τ + ε * τ ≤ ε₀)
    (hrun_meas : ∀ t, Measurable fun ω => A 0 * ∏ i, avgOf k (Y t i) ω)
    (hindep_runs : iIndepFun (fun t ω => A 0 * ∏ i, avgOf k (Y t i) ω) μ)
    (hmed : ∀ ω, IsMedian (fun t => A 0 * ∏ i, avgOf k (Y t i) ω) (z ω))
    (hp : 0 < p)
    (hrp : Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2) ≤ (r : ℝ)) :
    1 - p ≤ μ.real {ω | z ω ∈ relErr ε₀ (A m)} :=
  CV.median_relErr_ge hr hrun_meas hindep_runs hmed
    (fun t => run_four_fifths_of_samples hm hk hκ0 hε hη hτ0 hτ1 hmeanBudget hApos
      (hL2 t) (hindep_in t) (hindep_ph t) (hprod t) (hsample_mean t) hsampler
      (hsample_sq t) hkge hbudget hcompose) hp hrp

/-- **The `Ttc.VolumeAlgorithm`-shaped conclusion.** Identical hypotheses to
`median_accuracy_of_samples`, plus the endpoint identification `hend : A m = Vol(K)`, with
the conclusion written out as the two-sided bound the oracle interface consumes:

  `P( (1 − ε₀)·Vol(K) ≤ z ≤ (1 + ε₀)·Vol(K) ) ≥ 1 − p`.

`hend` is *not* discharged here: `Ttc.CV.G_indicator_mem_relErr` shows the last Gaussian is
only within a relative `1 − e^{−R²/(2σ_m²)}` of `Vol(K)`, and absorbing that bias is
`Ttc.CV.relErr_trans`'s job in `Ttc.VolumeAlgorithm.cousinsVempalaOfBiasedEnd`. Stating it
as a binder keeps the two idealizations separable. -/
theorem volume_accuracy_of_samples {n : ℕ} [IsProbabilityMeasure μ] {m k r : ℕ}
    (hm : 0 < m) (hk : 0 < k) (hr : 0 < r) {Y : Fin r → Fin m → Fin k → Ω → ℝ}
    {z : Ω → ℝ} {A : ℕ → ℝ} {ν : Fin m → ℝ} {K : Set (Space n)} {c κ ε ε₀ η τ p : ℝ}
    (hκ0 : 0 < κ) (hε : 0 < ε) (hη : 0 ≤ η) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hmeanBudget : 2 * (m : ℝ) * η ≤ τ)
    (hApos : ∀ i, 0 < A i)
    (hL2 : ∀ t i j, MemLp (Y t i j) 2 μ)
    (hindep_in : ∀ t i, Pairwise fun j j' => IndepFun (Y t i j) (Y t i j') μ)
    (hindep_ph : ∀ t, iIndepFun (fun i => avgOf k (Y t i)) μ)
    (hprod : ∀ t, MemLp (fun ω => ∏ i, avgOf k (Y t i) ω) 2 μ)
    (hsample_mean : ∀ t i j, ∫ ω, Y t i j ω ∂μ = ν i)
    (hsampler : ∀ i : Fin m, ν i ∈ relErr η (A ((i : ℕ) + 1) / A (i : ℕ)))
    (hsample_sq : ∀ t i j, ∫ ω, (Y t i j ω) ^ 2 ∂μ ≤ c * (ν i) ^ 2)
    (hkge : (c - 1) * (m : ℝ) / κ ≤ (k : ℝ))
    (hbudget : Real.exp κ - 1 ≤ ε ^ 2 / 5)
    (hcompose : ε + τ + ε * τ ≤ ε₀)
    (hrun_meas : ∀ t, Measurable fun ω => A 0 * ∏ i, avgOf k (Y t i) ω)
    (hindep_runs : iIndepFun (fun t ω => A 0 * ∏ i, avgOf k (Y t i) ω) μ)
    (hmed : ∀ ω, IsMedian (fun t => A 0 * ∏ i, avgOf k (Y t i) ω) (z ω))
    (hp : 0 < p)
    (hrp : Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2) ≤ (r : ℝ))
    (hend : A m = (volume K).toReal) :
    1 - p ≤ μ.real {ω | (1 - ε₀) * (volume K).toReal ≤ z ω
        ∧ z ω ≤ (1 + ε₀) * (volume K).toReal} := by
  have h := median_accuracy_of_samples hm hk hr hκ0 hε hη hτ0 hτ1 hmeanBudget hApos
    hL2 hindep_in hindep_ph hprod hsample_mean hsampler hsample_sq hkge hbudget
    hcompose hrun_meas hindep_runs hmed hp hrp
  rw [hend] at h
  convert h using 3 with ω
  simp [relErr, Set.mem_Icc]

/-! ### Non-vacuity of the assembly's hypothesis bundle (`CLAUDE.md` §11, `AUDIT.md` 4)

`run_four_fifths_of_samples` has eighteen hypotheses; a theorem with eighteen hypotheses
proves nothing if they cannot all hold at once. They can, on a **two-parameter family** —
every sample count `k ≥ 1` and every target `b > 0` — so the bundle is not forced at a
single point. What the witness does **not** certify is that the paper's Gaussian phases
satisfy it: the scores here are deterministic, so `hsampler` holds at `η = 0`, which is
exactly the hypothesis a real sampler cannot meet. That is the same honest limit
`Ttc.VolumeAlgorithm.cousinsVempalaWitness` records. -/

/-- The witness chain: `A 0 = 2b`, `A i = b` for `i ≥ 1`. One phase, ratio `1/2`. -/
noncomputable def witChain (b : ℝ) : ℕ → ℝ := fun i => if i = 0 then 2 * b else b

/-- The witness scores: `k` deterministic copies of `1/2`, on a one-point space. -/
noncomputable def witScore (k : ℕ) : Fin 1 → Fin k → Unit → ℝ := fun _ _ _ => 1 / 2

/-- A constant family has its constant value as a median. -/
theorem isMedian_of_const {r : ℕ} {v : Fin r → ℝ} {z : ℝ} (h : ∀ t, v t = z) :
    IsMedian v z := by
  classical
  have hle : (Finset.univ : Finset (Fin r)) ⊆ Finset.univ.filter fun t => v t ≤ z :=
    fun t _ => Finset.mem_filter.2 ⟨Finset.mem_univ t, le_of_eq (h t)⟩
  have hge : (Finset.univ : Finset (Fin r)) ⊆ Finset.univ.filter fun t => z ≤ v t :=
    fun t _ => Finset.mem_filter.2 ⟨Finset.mem_univ t, ge_of_eq (h t)⟩
  have h1 := Finset.card_le_card hle
  have h2 := Finset.card_le_card hge
  simp only [Finset.card_univ, Fintype.card_fin] at h1 h2
  exact ⟨by omega, by omega⟩

theorem witChain_pos {b : ℝ} (hb : 0 < b) (i : ℕ) : 0 < witChain b i := by
  unfold witChain; split <;> linarith

theorem avgOf_witScore (k : ℕ) (hk : 0 < k) (i : Fin 1) (ω : Unit) :
    avgOf k (witScore k i) ω = 1 / 2 := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  simp [avgOf, witScore, Finset.sum_const, Finset.card_univ]
  field_simp

/-- **The hypothesis bundle of `run_four_fifths_of_samples` is inhabited, at every sample
count `k ≥ 1` and every target `b > 0`.** Every one of its eighteen hypotheses is
discharged; the conclusion it yields is the one displayed. -/
theorem run_bundle_nonvacuous {k : ℕ} (hk : 0 < k) {b : ℝ} (hb : 0 < b) :
    4 / 5 ≤ (Measure.dirac ()).real
      {ω | witChain b 0 * ∏ i, avgOf k (witScore k i) ω ∈ relErr 1 (witChain b 1)} := by
  have hlog : (0 : ℝ) < Real.log (6 / 5) := Real.log_pos (by norm_num)
  refine run_four_fifths_of_samples (μ := Measure.dirac ()) (m := 1) (k := k)
    (Y := witScore k) (A := witChain b) (ν := fun _ => 1 / 2) (c := 1)
    (κ := Real.log (6 / 5)) (ε := 1) (ε₀ := 1) (η := 0) (τ := 0)
    one_pos hk hlog one_pos le_rfl le_rfl one_pos (by norm_num)
    (fun i => witChain_pos hb i)
    (fun i j => memLp_const _)
    (fun i => fun j j' hjj' =>
      (CV.iIndepFun_of_subsingleton (Measure.dirac ()) (witScore k i)).indepFun hjj')
    (CV.iIndepFun_of_subsingleton (Measure.dirac ()) (fun i => avgOf k (witScore k i)))
    (by
      have hfun : (fun ω : Unit => ∏ i, avgOf k (witScore k i) ω) = fun _ => (1 / 2 : ℝ) := by
        funext ω; simp [avgOf_witScore k hk]
      rw [hfun]; exact memLp_const _)
    (fun i j => by simp [witScore])
    (fun i => ?_) (fun i j => by simp [witScore]) (by simp)
    (by rw [Real.exp_log (by norm_num)]; norm_num) (by norm_num)
  · have : witChain b ((i : ℕ) + 1) / witChain b (i : ℕ) = 1 / 2 := by
      have hi : (i : ℕ) = 0 := by omega
      rw [hi]; unfold witChain; norm_num; field_simp
    rw [this]
    simp [relErr]

/-- **The hypothesis bundle, as an existential — the auditable form.**

`run_bundle_nonvacuous` discharges every hypothesis, but its *type* is a conclusion, and a
conclusion can be true for reasons unrelated to the bundle. This statement puts the
hypotheses themselves in the type: it asserts, for every `k ≥ 1` and every `b > 0`, that
data exist satisfying **all** of `run_four_fifths_of_samples`' mathematical hypotheses
simultaneously, with the target `A 1 = b` pinned so the family is genuinely two-parameter.

An auditor reads this type and needs nothing else. -/
theorem run_bundle_inhabited {k : ℕ} (hk : 0 < k) {b : ℝ} (hb : 0 < b) :
    ∃ (Y : Fin 1 → Fin k → Unit → ℝ) (ν : Fin 1 → ℝ) (A : ℕ → ℝ) (c κ ε ε₀ η τ : ℝ),
      0 < κ ∧ 0 < ε ∧ 0 ≤ η ∧ 0 ≤ τ ∧ τ < 1 ∧
      2 * ((1 : ℕ) : ℝ) * η ≤ τ ∧
      (∀ i, 0 < A i) ∧
      (∀ i j, MemLp (Y i j) 2 (Measure.dirac ())) ∧
      (∀ i, Pairwise fun j j' => IndepFun (Y i j) (Y i j') (Measure.dirac ())) ∧
      iIndepFun (fun i => avgOf k (Y i)) (Measure.dirac ()) ∧
      MemLp (fun ω => ∏ i, avgOf k (Y i) ω) 2 (Measure.dirac ()) ∧
      (∀ i j, ∫ ω, Y i j ω ∂(Measure.dirac ()) = ν i) ∧
      (∀ i : Fin 1, ν i ∈ relErr η (A ((i : ℕ) + 1) / A (i : ℕ))) ∧
      (∀ i j, ∫ ω, (Y i j ω) ^ 2 ∂(Measure.dirac ()) ≤ c * (ν i) ^ 2) ∧
      (c - 1) * ((1 : ℕ) : ℝ) / κ ≤ (k : ℝ) ∧
      Real.exp κ - 1 ≤ ε ^ 2 / 5 ∧
      ε + τ + ε * τ ≤ ε₀ ∧
      A 1 = b := by
  have hlog : (0 : ℝ) < Real.log (6 / 5) := Real.log_pos (by norm_num)
  refine ⟨witScore k, fun _ => 1 / 2, witChain b, 1, Real.log (6 / 5), 1, 1, 0, 0,
    hlog, one_pos, le_rfl, le_rfl, one_pos, by norm_num,
    fun i => witChain_pos hb i, fun i j => memLp_const _,
    fun i j j' hjj' =>
      (CV.iIndepFun_of_subsingleton (Measure.dirac ()) (witScore k i)).indepFun hjj',
    CV.iIndepFun_of_subsingleton (Measure.dirac ()) (fun i => avgOf k (witScore k i)),
    ?_, fun i j => by simp [witScore], fun i => ?_, fun i j => by simp [witScore],
    by simp, by rw [Real.exp_log (by norm_num)]; norm_num, by norm_num, ?_⟩
  · have hfun : (fun ω : Unit => ∏ i, avgOf k (witScore k i) ω) = fun _ => (1 / 2 : ℝ) := by
      funext ω; simp [avgOf_witScore k hk]
    rw [hfun]; exact memLp_const _
  · have hi : (i : ℕ) = 0 := by omega
    have hratio : witChain b ((i : ℕ) + 1) / witChain b (i : ℕ) = 1 / 2 := by
      rw [hi]; unfold witChain; norm_num; field_simp
    rw [hratio]; simp [relErr]
  · unfold witChain; norm_num

/-- **Witness 1 of the pair**: one sample per phase, target `1`. -/
theorem run_bundle_nonvacuous_one :
    4 / 5 ≤ (Measure.dirac ()).real
      {ω | witChain 1 0 * ∏ i, avgOf 1 (witScore 1 i) ω ∈ relErr 1 (witChain 1 1)} :=
  run_bundle_nonvacuous one_pos one_pos

/-- **Witness 2 of the pair**: two samples per phase, target `3`. Two inhabitants differing
in *both* free parameters, so the bundle is not forced at a point. -/
theorem run_bundle_nonvacuous_two :
    4 / 5 ≤ (Measure.dirac ()).real
      {ω | witChain 3 0 * ∏ i, avgOf 2 (witScore 2 i) ω ∈ relErr 1 (witChain 3 1)} :=
  run_bundle_nonvacuous (by norm_num) (by norm_num)

/-- The two witnesses really are different data: their targets differ. -/
theorem witChain_one_ne_three : witChain 1 1 ≠ witChain 3 1 := by
  unfold witChain; norm_num

/-- **The median-level bundle is inhabited too**, at every `k ≥ 1` and every `b > 0`, with
`r = 4` runs and a *strictly informative* confidence `p = 1/2` (so the conclusion reads
`1/2 ≤ …`, not the vacuous `0 ≤ …`). `4 ≥ (50/9)·log 2 ≈ 3.85` is the repetition count
`Ttc.CV.median_relErr_ge` demands.

Same honest caveat as `run_bundle_nonvacuous`: the runs are deterministic. -/
theorem median_bundle_nonvacuous {k : ℕ} (hk : 0 < k) {b : ℝ} (hb : 0 < b) :
    1 - 1 / 2 ≤ (Measure.dirac ()).real
      {ω | (fun _ : Unit => b) ω ∈ relErr 1 (witChain b 1)} := by
  have hlog : (0 : ℝ) < Real.log (6 / 5) := Real.log_pos (by norm_num)
  have hrun : ∀ t : Fin 4,
      (fun ω : Unit => witChain b 0 * ∏ i, avgOf k (witScore k i) ω) = fun _ => b := by
    intro t
    funext ω
    simp [avgOf_witScore k hk, witChain]
    ring
  refine median_accuracy_of_samples (μ := Measure.dirac ()) (m := 1) (k := k) (r := 4)
    (Y := fun _ => witScore k) (z := fun _ => b) (A := witChain b) (ν := fun _ => 1 / 2)
    (c := 1) (κ := Real.log (6 / 5)) (ε := 1) (ε₀ := 1) (η := 0) (τ := 0) (p := 1 / 2)
    one_pos hk (by norm_num) hlog one_pos le_rfl le_rfl one_pos (by norm_num)
    (fun i => witChain_pos hb i)
    (fun t i j => memLp_const _)
    (fun t i => fun j j' hjj' =>
      (CV.iIndepFun_of_subsingleton (Measure.dirac ()) (witScore k i)).indepFun hjj')
    (fun t => CV.iIndepFun_of_subsingleton (Measure.dirac ())
      (fun i => avgOf k (witScore k i)))
    (fun t => by
      have hfun : (fun ω : Unit => ∏ i, avgOf k (witScore k i) ω) = fun _ => (1 / 2 : ℝ) := by
        funext ω; simp [avgOf_witScore k hk]
      rw [hfun]; exact memLp_const _)
    (fun t i j => by simp [witScore])
    (fun i => ?_) (fun t i j => by simp [witScore]) (by simp)
    (by rw [Real.exp_log (by norm_num)]; norm_num) (by norm_num)
    (fun t => by rw [hrun t]; exact measurable_const)
    (CV.iIndepFun_of_subsingleton (Measure.dirac ())
      (fun t : Fin 4 => fun ω : Unit => witChain b 0 * ∏ i, avgOf k (witScore k i) ω))
    (fun ω => ?_) (by norm_num) ?_
  · have hi : (i : ℕ) = 0 := by omega
    have : witChain b ((i : ℕ) + 1) / witChain b (i : ℕ) = 1 / 2 := by
      rw [hi]; unfold witChain; norm_num; field_simp
    rw [this]; simp [relErr]
  · exact isMedian_of_const (fun t => congrFun (hrun t) ω)
  · rw [one_div_one_div]
    have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    norm_num
    nlinarith

/-! ### Axiom audit

`#print axioms` is the authoritative check (`CLAUDE.md` §4). Every headline result of this
file must depend on `[propext, Classical.choice, Quot.sound]` and nothing else. -/

#print axioms integral_avgOf
#print axioms variance_avgOf_le
#print axioms avgOf_sq_moment_le
#print axioms sample_count_meets_budget
#print axioms avgOf_sq_moment_le_budget
#print axioms avgOf_relErr_ge
#print axioms avgOf_relErr_three_quarters
#print axioms prod_bounds_of_perFactor
#print axioms prod_relErr_of_perFactor
#print axioms cool_telescope
#print axioms run_four_fifths_of_samples
#print axioms median_accuracy_of_samples
#print axioms volume_accuracy_of_samples
#print axioms run_bundle_inhabited
#print axioms run_bundle_nonvacuous
#print axioms run_bundle_nonvacuous_one
#print axioms run_bundle_nonvacuous_two
#print axioms median_bundle_nonvacuous

end CVEst

end Ttc
