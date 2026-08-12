/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVEstimator
import Mathlib.Analysis.Asymptotics.Defs

/-!
# `Exec/VolumePriceCV`: a *polynomial* per-call price for the Cousins–Vempala volume oracle

> ## ⚠ THIS FILE MUST NOT BE QUOTED AS ESTABLISHING `O*(n³)` ⚠
>
> Cousins–Vempala, *Gaussian Cooling and `O*(n³)` Algorithms for Volume and Gaussian Volume*
> (arXiv:1409.6011), Theorem 1.1 is an `O*(n³)` **membership-query** bound. **Nothing in this
> repository proves it.** What is priced below is the sample count of the estimator this
> repository actually proves correct — `Ttc.CVEst.median_accuracy_of_samples` /
> `Ttc.CVEst.volume_accuracy_of_samples` — whose own module docstring
> (`Ttc/Volume/CVEstimator.lean:68`) records its total as `Θ(n·L⁴·log(1/p)/κ³)` samples,
> **worse than the paper's**. Three further caveats, none of which this file removes:
>
> * **The unit is SAMPLES, not operations.** Nothing in this repository bounds the cost of
>   producing one sample from a cooled Gaussian. The only mixing input available,
>   `Ttc.HitAndRunTheorem11Input.at_steps`, targets the *uniform* law, not the cooled
>   Gaussian the phases need (`Ttc/Volume/CVEstimator.lean` §"What is assumed"), and it is
>   itself an assumed, nowhere-inhabited structure. `Ttc.CVCost.cvVolumeOpsPrice` below makes
>   the missing factor an explicit parameter `q` rather than hiding it.
> * **The estimator is conditional.** `Ttc.VolumeAlgorithm.cousinsVempalaOfRuns` leaves
>   `hphase_mean` and `hphase_var` open (`Ttc/Volume/CVInstantiate.lean:66-67, 120, 125`), and
>   `Ttc.CVEst.volume_accuracy_of_samples` carries `hsampler`, `hsample_sq` and `hend` as
>   binders. The count priced here is the count *those* theorems demand; it is not a
>   certificate that they are dischargeable.
> * **The `ε`-dependence proved here is `ε⁻⁶`, not the paper's `ε⁻²`** — see
>   `Ttc.CVCost.cvVolumeSamplePrice_le_of_eps`.

## The repository's CV cost contract cannot be priced against — checked, not assumed

`Ttc/Volume/CVTheorem11.lean` records Theorem 1.1's complexity contract, but every piece of
it is declaration-only:

* `Ttc.cvComplexityShape` (`Ttc/Volume/CVTheorem11.lean:47`) is a bare `noncomputable def`
  transcribing the paper's displayed expression. **No lemma anywhere relates it to a sample
  count, a query count, or any executable.**
* `Ttc.CVTheorem11Implementation` (`Ttc/Volume/CVTheorem11.lean:64`) is the structure that
  would carry `queryCost_le`. **It has no inhabitant in this repository**, and its own
  docstring says so.
* `Ttc.CVWellRoundedRuntimeOrder` (`Ttc/Volume/CVTheorem11.lean:95`) and
  `Ttc.cvWellRoundedRuntimeOrder_of_bound` (`:102`) are generic `IsBigO` plumbing over a
  `cost : ℕ → ℝ` supplied by the caller.

A grep over the whole development finds **zero** uses of any of those three names outside
`Ttc/Volume/CVTheorem11.lean` itself (this file mentions them in prose only). So there is
nothing to instantiate: this file prices the estimator directly.

## What is priced, and against what

`Ttc.CVEst.volume_accuracy_of_samples` consumes three counts:

| count | hypothesis it must meet | this file's choice |
| --- | --- | --- |
| runs `r` | `log(1/p)/(2·(4/5 − 1/2)²) ≤ r`, i.e. `r ≥ (50/9)·log(1/p)` | `Ttc.CVCost.cvRuns` |
| phases `m` | `0 < m`; the annealing schedule's own count | `Arlib.GaussianCooling.coolPhases n L κ = ⌈8(n+1)L²/κ⌉` |
| samples/phase `k` | `(c − 1)·m/κ ≤ k` (`Ttc.CVEst.avgOf_sq_moment_le_budget`) | `Ttc.CVCost.cvSamplesPerPhase` |

`Ttc.CVCost.cvVolumeSamplePrice` is their product `r·m·k`, and
`Ttc.CVCost.median_accuracy_at_price` / `Ttc.CVCost.volume_accuracy_at_price` are the
theorems that make it a *price* rather than loose arithmetic: they are
`Ttc.CVEst.median_accuracy_of_samples` / `Ttc.CVEst.volume_accuracy_of_samples` applied at
exactly these three numbers, with the three count hypotheses discharged from the
definitions and every other binder passed through unchanged.
`Ttc.CVCost.price_bundle_nonvacuous` shows that bundle is inhabited **at these counts**,
so the wrapper is not vacuous.

### One thing the wrappers do NOT prove, and must not be read as proving

`Ttc.CVEst.median_accuracy_of_samples` demands only `0 < m` of the phase count. **Taking
`m = Arlib.GaussianCooling.coolPhases n L κ` is a modelling choice, not a consequence of
the accuracy theorem**: a caller who set `m = 1` would satisfy that theorem and pay a far
smaller price, at the cost of an endpoint that is not cooled. What justifies the choice is
the *separate* schedule result `Ttc.CVEst.cool_telescope` /
`Arlib.GaussianCooling.coolSchedule_total_cooling` — the schedule reaches `σ_m² ≥ e^L·σ_0²`
only after `coolPhases n L κ` steps — and that result is **not chained into**
`Ttc.CVCost.median_accuracy_at_price`; its hypotheses (the geometric rate `hrate`, the
identification of the chain with the Gaussian phases) are not discharged anywhere here. So
the number below is the price of *this schedule*, and the link "this schedule is the one
the estimator must run" is prose in `Ttc/Volume/CVEstimator.lean`, not a theorem chained
here.

`c` is the single-sample relative second moment. Its intended discharger is
`Arlib.GaussianCooling.fixed_var_bound_ratio_indicator`
(`Arlib/Convexity/GaussianCooling/ZLogconcave.lean:467`), which gives `c = 1 + 2/n`; that is
why the explicit bound's hypothesis is `hc : c ≤ 1 + 2/n` rather than a numeral.

`L` is the logarithm of the total cooling factor (`σ_m²/σ_0² ≥ e^L`; for Cousins–Vempala
`L ≈ log n + 2 log R`). It is **not** collapsed to `log n` anywhere below: nothing in this
repository forces its growth, so it stays a visible parameter — including in the `IsBigO`
statement.

## The derived exponent is `1` — in SAMPLES

`Ttc.CVCost.cvVolumeSamplePrice_le`:

```
cvVolumeSamplePrice n L κ c p  ≤  2¹³ · n · L⁴ · log(1/p) / κ³
```

under `1 ≤ n`, `1 ≤ L`, `0 < κ ≤ 1`, `1 ≤ c ≤ 1 + 2/n`, `0 < p ≤ 1/2`. So the exponent of
`n` is **1**, and every other factor is on the right-hand side rather than inside an `O(·)`.

Read that number correctly. `Ttc.ttcVolPrice` (`Ttc/Exec/PriceList.lean:258`) is a count of
**coins**, exponential in `n`; this is a count of **samples**, linear in `n`. The two are
directly comparable only after a per-sample charge is supplied, which is what
`Ttc.CVCost.cvVolumeOpsPrice` parametrises and what this repository does not have. A
sanity check in the paper's direction: `O*(n)` samples at the paper's `O*(n²)` steps per
sample is the paper's `O*(n³)` — but the second factor is precisely the open half.

Comparison against `Ttc.cvComplexityShape` in the accuracy parameter is *unfavourable*: at
the estimator's own budget relation `e^κ − 1 ≤ ε²/5` one has `κ ≈ ε²/5`, so `κ⁻³` is
`ε⁻⁶`, whereas `Ttc.cvComplexityShape` prints `ε⁻²·polylog(1/ε)`.
`Ttc.CVCost.cvVolumeSamplePrice_le_of_eps` states the `ε⁻⁶` form with the conversion
`ε²/10 ≤ κ` as a visible hypothesis.
-/

namespace Ttc.CVCost

open MeasureTheory Arlib.GaussianCooling

/-! ## Section 1 — the three counts

Each is a plain arithmetic `def`. None of their names asserts a semantic identity; the
lemmas immediately following each one are what tie them to
`Ttc.CVEst.volume_accuracy_of_samples`' hypotheses. -/

/-- **The number of independent runs whose median is taken.**

`⌈(50/9)·log(1/p)⌉ + 1`, written in the exact shape `Ttc.CV.median_relErr_ge` /
`Ttc.CVEst.median_accuracy_of_samples` demand — `2·(4/5 − 1/2)² = 9/50`, so the divisor is
the Hoeffding exponent of a `4/5`-vs-`1/2` median boost, not a constant chosen here.

The trailing `+ 1` is house style (`Ttc.ttcVolPrice`, `Ttc.SamplerCost.stepsPrice`): it
makes the count positive at every `p`, including `p ≥ 1` where the logarithm is `≤ 0`. -/
noncomputable def cvRuns (p : ℝ) : ℕ := ⌈Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2)⌉₊ + 1

/-- **The number of samples averaged per phase.**

`⌈(c − 1)·m/κ⌉ + 1` at `m = Arlib.GaussianCooling.coolPhases n L κ`. This is
`Ttc.CVEst.avgOf_sq_moment_le_budget`'s `hkge` made into a number: `k ≥ (c − 1)·m/κ` is
exactly what converts §5.1's fixed single-sample relative second moment `c` into §5.2's
per-phase budget `1 + κ/m`. -/
noncomputable def cvSamplesPerPhase (n : ℕ) (L κ c : ℝ) : ℕ :=
  ⌈(c - 1) * (coolPhases n L κ : ℝ) / κ⌉₊ + 1

/-- **THE PER-CALL VOLUME PRICE, IN SAMPLES.** `r · m · k`: the total number of samples one
call of the Cousins–Vempala estimator draws, at the counts this repository's own accuracy
theorem demands.

A plain arithmetic `def`. Its name says `SamplePrice`, and samples — not arithmetic
operations, not membership queries — is what it counts;
`Ttc.CVCost.volume_accuracy_at_price` is the lemma that makes it a *price*. -/
noncomputable def cvVolumeSamplePrice (n : ℕ) (L κ c p : ℝ) : ℕ :=
  cvRuns p * (coolPhases n L κ * cvSamplesPerPhase n L κ c)

/-- **The same price in operations, with the per-sample charge `q` left as a parameter.**

`q` is the arithmetic (or membership-query) charge of producing **one** sample from the
cooled Gaussian of a phase. **This repository does not bound `q`**: the only mixing input
it has, `Ttc.HitAndRunTheorem11Input`, is an assumed structure and targets the *uniform*
law rather than the cooled Gaussian. Keeping `q` a parameter is the honest statement that
the volume oracle's operation count is polynomial *exactly when* `q` is. -/
noncomputable def cvVolumeOpsPrice (n : ℕ) (L κ c p : ℝ) (q : ℕ) : ℕ :=
  q * cvVolumeSamplePrice n L κ c p

/-! ### The counts meet the hypotheses they were chosen for -/

/-- `Ttc.CVEst.median_accuracy_of_samples`' `hrp`, discharged. Unconditional: `Nat.le_ceil`
holds at every real, and the `+ 1` only helps. -/
theorem le_cvRuns (p : ℝ) :
    Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2) ≤ (cvRuns p : ℝ) := by
  unfold cvRuns
  push_cast
  linarith [Nat.le_ceil (Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2))]

/-- The run count is positive at every `p`. -/
theorem cvRuns_pos (p : ℝ) : 0 < cvRuns p := Nat.succ_pos _

/-- `Ttc.CVEst.avgOf_sq_moment_le_budget`' `hkge`, discharged. Unconditional, for the same
reason as `Ttc.CVCost.le_cvRuns`. -/
theorem le_cvSamplesPerPhase (n : ℕ) (L κ c : ℝ) :
    (c - 1) * (coolPhases n L κ : ℝ) / κ ≤ (cvSamplesPerPhase n L κ c : ℝ) := by
  unfold cvSamplesPerPhase
  push_cast
  linarith [Nat.le_ceil ((c - 1) * (coolPhases n L κ : ℝ) / κ)]

/-- The per-phase sample count is positive at every parameter. -/
theorem cvSamplesPerPhase_pos (n : ℕ) (L κ c : ℝ) : 0 < cvSamplesPerPhase n L κ c :=
  Nat.succ_pos _

/-- **The price is a positive natural** whenever the schedule has at least one phase, i.e.
whenever `1 ≤ L` and `0 < κ` (`Arlib.GaussianCooling.coolPhases_pos`). -/
theorem cvVolumeSamplePrice_pos {n : ℕ} {L κ : ℝ} (c p : ℝ) (hL : 1 ≤ L) (hκ0 : 0 < κ) :
    0 < cvVolumeSamplePrice n L κ c p :=
  Nat.mul_pos (cvRuns_pos p)
    (Nat.mul_pos (coolPhases_pos hL hκ0) (cvSamplesPerPhase_pos n L κ c))

/-- The price, unfolded: it **is** `r · m · k`, and nothing else. Stated so that an auditor
can read the product without unfolding three definitions. -/
theorem cvVolumeSamplePrice_eq (n : ℕ) (L κ c p : ℝ) :
    cvVolumeSamplePrice n L κ c p
      = cvRuns p * (coolPhases n L κ * cvSamplesPerPhase n L κ c) := rfl

/-! ## Section 2 — what makes the number a *price*

`Ttc.SamplerCost.samplePrice` is a price because `Ttc.SamplerCost.drawWork_le_samplePrice`
exists. The analogue here is the theorem below: `Ttc.CVEst.volume_accuracy_of_samples`
*applied at exactly these three counts*, with `hm`, `hk`, `hr`, `hkge` and `hrp` discharged
from Section 1 and every remaining binder passed through verbatim.

Nothing is weakened: the hypotheses that carry the open half of the argument — `hsampler`
(the sampler), `hsample_sq` (§5.1's variance bound at the realised law), `hend` (the
endpoint identification) — are still binders here, exactly as they are there. -/

/-- **The median-level conclusion, at this file's counts.**

`Ttc.CVEst.median_accuracy_of_samples` applied at `r = Ttc.CVCost.cvRuns p`,
`m = Arlib.GaussianCooling.coolPhases n L κ`, `k = Ttc.CVCost.cvSamplesPerPhase n L κ c`.
`Ttc.CVCost.volume_accuracy_at_price` is the same statement with the endpoint
identification `hend : A m = Vol(K)` added; that one extra binder is the idealization
`Ttc/Volume/CVEstimator.lean` flags, and it is the only difference between the two. -/
theorem median_accuracy_at_price {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {L κ c p : ℝ} (hL : 1 ≤ L) (hκ0 : 0 < κ)
    {Y : Fin (cvRuns p) → Fin (coolPhases n L κ) →
      Fin (cvSamplesPerPhase n L κ c) → Ω → ℝ}
    {z : Ω → ℝ} {A : ℕ → ℝ} {ν : Fin (coolPhases n L κ) → ℝ} {ε ε₀ η τ : ℝ}
    (hε : 0 < ε) (hη : 0 ≤ η) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hmeanBudget : 2 * ((coolPhases n L κ : ℕ) : ℝ) * η ≤ τ)
    (hApos : ∀ i, 0 < A i)
    (hL2 : ∀ t i j, MemLp (Y t i j) 2 μ)
    (hindep_in : ∀ t i, Pairwise fun j j' => ProbabilityTheory.IndepFun (Y t i j) (Y t i j') μ)
    (hindep_ph : ∀ t, ProbabilityTheory.iIndepFun
      (fun i => CVEst.avgOf (cvSamplesPerPhase n L κ c) (Y t i)) μ)
    (hprod : ∀ t, MemLp
      (fun ω => ∏ i, CVEst.avgOf (cvSamplesPerPhase n L κ c) (Y t i) ω) 2 μ)
    (hsample_mean : ∀ t i j, ∫ ω, Y t i j ω ∂μ = ν i)
    (hsampler : ∀ i : Fin (coolPhases n L κ),
      ν i ∈ relErr η (A ((i : ℕ) + 1) / A (i : ℕ)))
    (hsample_sq : ∀ t i j, ∫ ω, (Y t i j ω) ^ 2 ∂μ ≤ c * (ν i) ^ 2)
    (hbudget : Real.exp κ - 1 ≤ ε ^ 2 / 5)
    (hcompose : ε + τ + ε * τ ≤ ε₀)
    (hrun_meas : ∀ t, Measurable
      fun ω => A 0 * ∏ i, CVEst.avgOf (cvSamplesPerPhase n L κ c) (Y t i) ω)
    (hindep_runs : ProbabilityTheory.iIndepFun
      (fun t ω => A 0 * ∏ i, CVEst.avgOf (cvSamplesPerPhase n L κ c) (Y t i) ω) μ)
    (hmed : ∀ ω, IsMedian
      (fun t => A 0 * ∏ i, CVEst.avgOf (cvSamplesPerPhase n L κ c) (Y t i) ω) (z ω))
    (hp : 0 < p) :
    1 - p ≤ μ.real {ω | z ω ∈ relErr ε₀ (A (coolPhases n L κ))} :=
  CVEst.median_accuracy_of_samples (coolPhases_pos hL hκ0)
    (cvSamplesPerPhase_pos n L κ c) (cvRuns_pos p) hκ0 hε hη hτ0 hτ1 hmeanBudget hApos
    hL2 hindep_in hindep_ph hprod hsample_mean hsampler hsample_sq
    (le_cvSamplesPerPhase n L κ c) hbudget hcompose hrun_meas hindep_runs hmed hp
    (le_cvRuns p)

/-- **The estimator's accuracy conclusion, at this file's counts.**

`r = Ttc.CVCost.cvRuns p` runs of `m = Arlib.GaussianCooling.coolPhases n L κ` phases of
`k = Ttc.CVCost.cvSamplesPerPhase n L κ c` samples each — in total
`Ttc.CVCost.cvVolumeSamplePrice n L κ c p` samples — return a median `z` with

  `P( (1 − ε₀)·Vol(K) ≤ z ≤ (1 + ε₀)·Vol(K) ) ≥ 1 − p`.

This is the statement that turns `Ttc.CVCost.cvVolumeSamplePrice` from arithmetic into a
price: the three counts are *sufficient*, not merely defined. -/
theorem volume_accuracy_at_price {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {L κ c p : ℝ} (hL : 1 ≤ L) (hκ0 : 0 < κ)
    {Y : Fin (cvRuns p) → Fin (coolPhases n L κ) →
      Fin (cvSamplesPerPhase n L κ c) → Ω → ℝ}
    {z : Ω → ℝ} {A : ℕ → ℝ} {ν : Fin (coolPhases n L κ) → ℝ} {K : Set (Space n)}
    {ε ε₀ η τ : ℝ}
    (hε : 0 < ε) (hη : 0 ≤ η) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hmeanBudget : 2 * ((coolPhases n L κ : ℕ) : ℝ) * η ≤ τ)
    (hApos : ∀ i, 0 < A i)
    (hL2 : ∀ t i j, MemLp (Y t i j) 2 μ)
    (hindep_in : ∀ t i, Pairwise fun j j' => ProbabilityTheory.IndepFun (Y t i j) (Y t i j') μ)
    (hindep_ph : ∀ t, ProbabilityTheory.iIndepFun
      (fun i => CVEst.avgOf (cvSamplesPerPhase n L κ c) (Y t i)) μ)
    (hprod : ∀ t, MemLp
      (fun ω => ∏ i, CVEst.avgOf (cvSamplesPerPhase n L κ c) (Y t i) ω) 2 μ)
    (hsample_mean : ∀ t i j, ∫ ω, Y t i j ω ∂μ = ν i)
    (hsampler : ∀ i : Fin (coolPhases n L κ),
      ν i ∈ relErr η (A ((i : ℕ) + 1) / A (i : ℕ)))
    (hsample_sq : ∀ t i j, ∫ ω, (Y t i j ω) ^ 2 ∂μ ≤ c * (ν i) ^ 2)
    (hbudget : Real.exp κ - 1 ≤ ε ^ 2 / 5)
    (hcompose : ε + τ + ε * τ ≤ ε₀)
    (hrun_meas : ∀ t, Measurable
      fun ω => A 0 * ∏ i, CVEst.avgOf (cvSamplesPerPhase n L κ c) (Y t i) ω)
    (hindep_runs : ProbabilityTheory.iIndepFun
      (fun t ω => A 0 * ∏ i, CVEst.avgOf (cvSamplesPerPhase n L κ c) (Y t i) ω) μ)
    (hmed : ∀ ω, IsMedian
      (fun t => A 0 * ∏ i, CVEst.avgOf (cvSamplesPerPhase n L κ c) (Y t i) ω) (z ω))
    (hp : 0 < p)
    (hend : A (coolPhases n L κ) = (volume K).toReal) :
    1 - p ≤ μ.real {ω | (1 - ε₀) * (volume K).toReal ≤ z ω
        ∧ z ω ≤ (1 + ε₀) * (volume K).toReal} :=
  CVEst.volume_accuracy_of_samples (coolPhases_pos hL hκ0)
    (cvSamplesPerPhase_pos n L κ c) (cvRuns_pos p) hκ0 hε hη hτ0 hτ1 hmeanBudget hApos
    hL2 hindep_in hindep_ph hprod hsample_mean hsampler hsample_sq
    (le_cvSamplesPerPhase n L κ c) hbudget hcompose hrun_meas hindep_runs hmed hp
    (le_cvRuns p) hend

/-! ## Section 3 — the explicit bound, one factor at a time

Every regime hypothesis is named and visible. `L` and `κ` are **not** suppressed; the
statement below carries them on the right-hand side. -/

section Explicit

/-- **The phase count is `≤ 18·n·L²/κ`.**

`Arlib.GaussianCooling.coolPhases n L κ = ⌈8(n+1)L²/κ⌉`; the ceiling costs `+1` and
`n + 1 ≤ 2n`, both absorbed into `18` by `1 ≤ n·L²/κ`. -/
theorem coolPhases_le {n : ℕ} {L κ : ℝ} (hn : 1 ≤ n) (hL : 1 ≤ L) (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) : (coolPhases n L κ : ℝ) ≤ 18 * (n : ℝ) * L ^ 2 / κ := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hLsq : (1 : ℝ) ≤ L ^ 2 := by nlinarith
  have harg0 : (0 : ℝ) ≤ 8 * ((n : ℝ) + 1) * L ^ 2 / κ := by positivity
  have hceil : (coolPhases n L κ : ℝ) ≤ 8 * ((n : ℝ) + 1) * L ^ 2 / κ + 1 :=
    (Nat.ceil_lt_add_one harg0).le
  rw [le_div_iff₀ hκ0]
  have hstep : (coolPhases n L κ : ℝ) * κ ≤ (8 * ((n : ℝ) + 1) * L ^ 2 / κ + 1) * κ :=
    mul_le_mul_of_nonneg_right hceil hκ0.le
  have hcancel : (8 * ((n : ℝ) + 1) * L ^ 2 / κ + 1) * κ = 8 * ((n : ℝ) + 1) * L ^ 2 + κ := by
    field_simp
  have hnL : L ^ 2 ≤ (n : ℝ) * L ^ 2 := by nlinarith
  linarith

/-- **The per-phase sample count is `≤ 38·L²/κ²`** — note that `n` has *cancelled*: the
`(c − 1) = 2/n` of `Arlib.GaussianCooling.fixed_var_bound_ratio_indicator` exactly kills the
`n` of the phase count.

Hypotheses: `1 ≤ c` (automatic — `Ttc.CVEst.one_le_of_sq_moment_le`) and `c ≤ 1 + 2/n`
(§5.1's constant). -/
theorem cvSamplesPerPhase_le {n : ℕ} {L κ c : ℝ} (hn : 1 ≤ n) (hL : 1 ≤ L) (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (hc1 : 1 ≤ c) (hc : c ≤ 1 + 2 / (n : ℝ)) :
    (cvSamplesPerPhase n L κ c : ℝ) ≤ 38 * L ^ 2 / κ ^ 2 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hLsq : (1 : ℝ) ≤ L ^ 2 := by nlinarith
  have hm := coolPhases_le hn hL hκ0 hκ1
  have hm0 : (0 : ℝ) ≤ (coolPhases n L κ : ℝ) := Nat.cast_nonneg _
  have harg0 : (0 : ℝ) ≤ (c - 1) * (coolPhases n L κ : ℝ) / κ :=
    div_nonneg (mul_nonneg (by linarith) hm0) hκ0.le
  have hceil : (cvSamplesPerPhase n L κ c : ℝ)
      ≤ (c - 1) * (coolPhases n L κ : ℝ) / κ + 2 := by
    unfold cvSamplesPerPhase
    push_cast
    linarith [(Nat.ceil_lt_add_one harg0).le]
  have hcm : (c - 1) * (coolPhases n L κ : ℝ) ≤ 36 * L ^ 2 / κ := by
    calc (c - 1) * (coolPhases n L κ : ℝ)
        ≤ (2 / (n : ℝ)) * (18 * (n : ℝ) * L ^ 2 / κ) :=
          mul_le_mul (by linarith) hm hm0 (by positivity)
      _ = 36 * L ^ 2 / κ := by field_simp; ring
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < κ ^ 2)]
  have h1 : (cvSamplesPerPhase n L κ c : ℝ) * κ ^ 2
      ≤ ((c - 1) * (coolPhases n L κ : ℝ) / κ + 2) * κ ^ 2 :=
    mul_le_mul_of_nonneg_right hceil (by positivity)
  have h2 : ((c - 1) * (coolPhases n L κ : ℝ) / κ + 2) * κ ^ 2
      = (c - 1) * (coolPhases n L κ : ℝ) * κ + 2 * κ ^ 2 := by field_simp
  have h3 : (c - 1) * (coolPhases n L κ : ℝ) * κ ≤ 36 * L ^ 2 := by
    have h4 := mul_le_mul_of_nonneg_right hcm hκ0.le
    have h5 : 36 * L ^ 2 / κ * κ = 36 * L ^ 2 := by field_simp
    linarith
  nlinarith

/-- **The run count is `≤ 9·log(1/p)`**, for `0 < p ≤ 1/2`.

The divisor `2·(4/5 − 1/2)² = 9/50` is the median-boost exponent, so the count is
`(50/9)·log(1/p) + 2`; `p ≤ 1/2` gives `log(1/p) ≥ log 2 > 0.693`, which absorbs the `+2`
into the constant `9`. For `p > 1/2` the additive term cannot be absorbed at all —
`log(1/p) → 0` as `p → 1`, so a confidence weaker than `1/2` is not a regime this bound
covers, and the hypothesis says so. -/
theorem cvRuns_le {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 2) :
    (cvRuns p : ℝ) ≤ 9 * Real.log (1 / p) := by
  have h2le : (2 : ℝ) ≤ 1 / p := by rw [le_div_iff₀ hp0]; linarith
  have hlog2 : Real.log 2 ≤ Real.log (1 / p) := Real.log_le_log (by norm_num) h2le
  have hlog : (0.6931 : ℝ) ≤ Real.log (1 / p) := by
    have := Real.log_two_gt_d9
    linarith
  have harg0 : (0 : ℝ) ≤ Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2) := by
    apply div_nonneg (by linarith) (by norm_num)
  have hceil : (cvRuns p : ℝ) ≤ Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2) + 2 := by
    unfold cvRuns
    push_cast
    linarith [(Nat.ceil_lt_add_one harg0).le]
  have heq : Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2) = 50 / 9 * Real.log (1 / p) := by
    norm_num
    ring
  rw [heq] at hceil
  linarith

/-- **THE HEADLINE OF THIS FILE — the derived exponent of `n` is `1`, and the unit is
SAMPLES.**

```
cvVolumeSamplePrice n L κ c p  ≤  2¹³ · n · L⁴ · log(1/p) / κ³
```

*Every* factor is on the right-hand side, and every regime assumption is a named
hypothesis:

* `hn : 1 ≤ n`;
* `hL : 1 ≤ L` — `L` is the log of the total cooling factor (`≈ log n + 2 log R` for
  Cousins–Vempala) and is **not** suppressed; `L⁴` is where the schedule's cost lives;
* `hκ0 : 0 < κ`, `hκ1 : κ ≤ 1` — the total relative-variance budget, **not** suppressed;
  `κ⁻³` is the dominant accuracy cost and is the reason
  `Ttc.CVCost.cvVolumeSamplePrice_le_of_eps` reads `ε⁻⁶`;
* `hc1 : 1 ≤ c`, `hc : c ≤ 1 + 2/n` — §5.1's single-sample relative second moment, whose
  intended discharger is `Arlib.GaussianCooling.fixed_var_bound_ratio_indicator`;
* `hp0 : 0 < p`, `hp1 : p ≤ 1/2` — a confidence at least `1/2`.

The proved constant is `9 · 18 · 38 = 6156`; it is rounded up to `2¹³ = 8192` so that the
statement has the same shape as `Ttc.SamplerCost.samplePrice_le_quartic`.

**The exponent `1` counts samples, not operations.** `Ttc.ttcVolPrice`
(`Ttc/Exec/PriceList.lean:258`) counts coins and is exponential in `n`; converting this
number into a comparable operation count needs the per-sample charge
`Ttc.CVCost.cvVolumeOpsPrice`'s `q`, which this repository does not bound. -/
theorem cvVolumeSamplePrice_le {n : ℕ} {L κ c p : ℝ} (hn : 1 ≤ n) (hL : 1 ≤ L)
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hc1 : 1 ≤ c) (hc : c ≤ 1 + 2 / (n : ℝ))
    (hp0 : 0 < p) (hp1 : p ≤ 1 / 2) :
    (cvVolumeSamplePrice n L κ c p : ℝ)
      ≤ 2 ^ 13 * (n : ℝ) * L ^ 4 * Real.log (1 / p) / κ ^ 3 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h2le : (2 : ℝ) ≤ 1 / p := by rw [le_div_iff₀ hp0]; linarith
  have hlog2 : Real.log 2 ≤ Real.log (1 / p) := Real.log_le_log (by norm_num) h2le
  have hlog : (0 : ℝ) ≤ Real.log (1 / p) := by
    have := Real.log_two_gt_d9
    linarith
  have hr := cvRuns_le hp0 hp1
  have hm := coolPhases_le hn hL hκ0 hκ1
  have hk := cvSamplesPerPhase_le hn hL hκ0 hκ1 hc1 hc
  have hm0 : (0 : ℝ) ≤ (coolPhases n L κ : ℝ) := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ (cvSamplesPerPhase n L κ c : ℝ) := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ (cvRuns p : ℝ) := Nat.cast_nonneg _
  have hmk : (coolPhases n L κ : ℝ) * (cvSamplesPerPhase n L κ c : ℝ)
      ≤ (18 * (n : ℝ) * L ^ 2 / κ) * (38 * L ^ 2 / κ ^ 2) :=
    mul_le_mul hm hk hk0 (by positivity)
  have hall : (cvRuns p : ℝ)
        * ((coolPhases n L κ : ℝ) * (cvSamplesPerPhase n L κ c : ℝ))
      ≤ (9 * Real.log (1 / p)) * ((18 * (n : ℝ) * L ^ 2 / κ) * (38 * L ^ 2 / κ ^ 2)) :=
    mul_le_mul hr hmk (mul_nonneg hm0 hk0) (by linarith)
  have hX : (0 : ℝ) ≤ (n : ℝ) * L ^ 4 * Real.log (1 / p) / κ ^ 3 :=
    div_nonneg (mul_nonneg (mul_nonneg (by linarith) (by positivity)) hlog) (by positivity)
  have hcast : (cvVolumeSamplePrice n L κ c p : ℝ)
      = (cvRuns p : ℝ) * ((coolPhases n L κ : ℝ) * (cvSamplesPerPhase n L κ c : ℝ)) := by
    unfold cvVolumeSamplePrice
    push_cast
    ring
  rw [hcast]
  refine hall.trans ?_
  calc (9 * Real.log (1 / p)) * ((18 * (n : ℝ) * L ^ 2 / κ) * (38 * L ^ 2 / κ ^ 2))
      = 6156 * ((n : ℝ) * L ^ 4 * Real.log (1 / p) / κ ^ 3) := by
        field_simp
        ring
    _ ≤ 2 ^ 13 * ((n : ℝ) * L ^ 4 * Real.log (1 / p) / κ ^ 3) := by nlinarith
    _ = 2 ^ 13 * (n : ℝ) * L ^ 4 * Real.log (1 / p) / κ ^ 3 := by ring

/-- **The same bound in the accuracy parameter: `ε⁻⁶`, not the paper's `ε⁻²`.**

```
cvVolumeSamplePrice n L κ c p  ≤  2²³ · n · L⁴ · log(1/p) / ε⁶
```

The conversion is the visible hypothesis `hκε : ε²/10 ≤ κ`, i.e. *the variance budget is
taken as large as the estimator's own budget relation `e^κ − 1 ≤ ε²/5` allows*
(`Ttc.CVEst.volume_accuracy_of_samples`' `hbudget`; `Ttc.CVCost.exists_budget_kappa` shows
the two are simultaneously satisfiable). Choosing a smaller `κ` only raises the price, so
this is the favourable reading of the repository's own route.

**This is the honest comparison against the paper, and it is unfavourable.**
`Ttc.cvComplexityShape` (`Ttc/Volume/CVTheorem11.lean:47`) prints `ε⁻²·log²(1/ε)·…`; the
route this repository actually proves pays `ε⁻⁶`, because the per-phase budget enters
three times over (once in the phase count `m ∼ nL²/κ` and twice in the per-phase sample
count `k ∼ L²/κ²`). Nothing here closes that gap; it records it. -/
theorem cvVolumeSamplePrice_le_of_eps {n : ℕ} {L κ c p ε : ℝ} (hn : 1 ≤ n) (hL : 1 ≤ L)
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hc1 : 1 ≤ c) (hc : c ≤ 1 + 2 / (n : ℝ))
    (hp0 : 0 < p) (hp1 : p ≤ 1 / 2) (hε0 : 0 < ε) (hκε : ε ^ 2 / 10 ≤ κ) :
    (cvVolumeSamplePrice n L κ c p : ℝ)
      ≤ 2 ^ 23 * (n : ℝ) * L ^ 4 * Real.log (1 / p) / ε ^ 6 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h2le : (2 : ℝ) ≤ 1 / p := by rw [le_div_iff₀ hp0]; linarith
  have hlog : (0 : ℝ) ≤ Real.log (1 / p) := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 2) h2le
    have := Real.log_two_gt_d9
    linarith
  have hmain := cvVolumeSamplePrice_le hn hL hκ0 hκ1 hc1 hc hp0 hp1
  have hN : (0 : ℝ) ≤ (n : ℝ) * L ^ 4 * Real.log (1 / p) :=
    mul_nonneg (mul_nonneg (by linarith) (by positivity)) hlog
  have hcube : ε ^ 6 / 1000 ≤ κ ^ 3 := by
    have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ ε ^ 2 / 10) hκε 3
    calc ε ^ 6 / 1000 = (ε ^ 2 / 10) ^ 3 := by ring
      _ ≤ κ ^ 3 := h
  refine hmain.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg hN (by linarith : (0:ℝ) ≤ κ ^ 3 - ε ^ 6 / 1000),
    mul_nonneg hN (by positivity : (0:ℝ) ≤ ε ^ 6)]

/-- **`x/2 ≤ log(1 + x)` on `0 ≤ x ≤ 1`** — the elementary step behind
`Ttc.CVCost.exists_budget_kappa`.

`e^{−x/2} ≥ 1 − x/2` gives `e^{x/2} ≤ 1/(1 − x/2)`, and `(1 + x)(1 − x/2) = 1 + x/2 − x²/2
≥ 1` exactly when `x ≤ 1`. -/
theorem half_le_log_one_add {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ Real.log (1 + x) := by
  have hd : (0 : ℝ) < 1 - x / 2 := by linarith
  have hpos : (0 : ℝ) < Real.exp (x / 2) := Real.exp_pos _
  have h1 : 1 - x / 2 ≤ (Real.exp (x / 2))⁻¹ := by
    have h := Real.add_one_le_exp (-(x / 2))
    rw [Real.exp_neg] at h
    linarith
  have h3 : (1 - x / 2) * Real.exp (x / 2) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right h1 hpos.le
    rwa [inv_mul_cancel₀ hpos.ne'] at h
  have h5 : (1 - x / 2) * Real.exp (x / 2) ≤ (1 - x / 2) * (1 + x) := by nlinarith
  have h4 : Real.exp (x / 2) ≤ 1 + x := le_of_mul_le_mul_left h5 hd
  have h6 := Real.log_le_log hpos h4
  rwa [Real.log_exp] at h6

/-- **The `ε`-regime of `Ttc.CVCost.cvVolumeSamplePrice_le_of_eps` is compatible with the
estimator's own variance budget.**

At `κ = log(1 + ε²/5)` — the largest budget `Ttc.CVEst.volume_accuracy_of_samples`' binder
`hbudget : e^κ − 1 ≤ ε²/5` permits — all four constraints hold at once, so the `ε⁻⁶` bound
is a statement about a reachable regime and not a vacuous one. -/
theorem exists_budget_kappa {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧ Real.exp κ - 1 ≤ ε ^ 2 / 5 ∧ ε ^ 2 / 10 ≤ κ := by
  have hx0 : (0 : ℝ) < ε ^ 2 / 5 := by positivity
  have hx1 : ε ^ 2 / 5 ≤ 1 := by nlinarith
  refine ⟨Real.log (1 + ε ^ 2 / 5), Real.log_pos (by linarith), ?_, ?_, ?_⟩
  · have h := Real.log_le_sub_one_of_pos (x := 1 + ε ^ 2 / 5) (by linarith)
    linarith
  · rw [Real.exp_log (by linarith)]
    linarith
  · have h := half_le_log_one_add (x := ε ^ 2 / 5) hx0.le hx1
    linarith

/-- **The operation count, with the per-sample charge `q` explicit.**

`Ttc.CVCost.cvVolumeSamplePrice_le` multiplied by `q`. The statement is *the* honest form
of "the CV volume oracle is polynomial": it is polynomial in `n` **iff** `q` is, and this
repository bounds `q` nowhere (module docstring). -/
theorem cvVolumeOpsPrice_le {n : ℕ} {L κ c p : ℝ} {q : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ L)
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hc1 : 1 ≤ c) (hc : c ≤ 1 + 2 / (n : ℝ))
    (hp0 : 0 < p) (hp1 : p ≤ 1 / 2) :
    (cvVolumeOpsPrice n L κ c p q : ℝ)
      ≤ (q : ℝ) * (2 ^ 13 * (n : ℝ) * L ^ 4 * Real.log (1 / p) / κ ^ 3) := by
  have hmain := cvVolumeSamplePrice_le hn hL hκ0 hκ1 hc1 hc hp0 hp1
  have hq : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
  unfold cvVolumeOpsPrice
  push_cast
  exact mul_le_mul_of_nonneg_left hmain hq

end Explicit

/-! ## Section 4 — the asymptotic form, with the regime hypotheses visible

`L` is **not** collapsed to `log n`: nothing in this repository forces its growth, so it
stays a parameter with `1 ≤ L n` as a named hypothesis and `(L n)⁴` on the right of the
`O(·)`. Likewise `κ` and `p` are fixed constants of the statement, and the implied constant
`2¹³·log(1/p)/κ³` is visible in the proof. -/

section Asymptotic

/-- **The `IsBigO` form — `O(n · L⁴)` samples per volume-oracle call.**

Nothing is hidden in the `O(·)` that is not a hypothesis here: the accuracy budget `κ`, the
confidence `p`, and §5.1's constant `c n ≤ 1 + 2/n` are all named, and the cooling
logarithm `L n` appears explicitly in the comparison function. -/
theorem isBigO_cvVolumeSamplePrice_linear {κ p : ℝ} {L c : ℕ → ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1 / 2)
    (hL : ∀ n, 1 ≤ L n) (hc1 : ∀ n, 1 ≤ c n) (hc : ∀ n : ℕ, c n ≤ 1 + 2 / (n : ℝ)) :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => (cvVolumeSamplePrice n (L n) κ (c n) p : ℝ))
      (fun n : ℕ => (n : ℝ) * (L n) ^ 4) := by
  refine Asymptotics.IsBigO.of_bound (2 ^ 13 * Real.log (1 / p) / κ ^ 3) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) * (L n) ^ 4)]
  calc (cvVolumeSamplePrice n (L n) κ (c n) p : ℝ)
      ≤ 2 ^ 13 * (n : ℝ) * (L n) ^ 4 * Real.log (1 / p) / κ ^ 3 :=
        cvVolumeSamplePrice_le hn (hL n) hκ0 hκ1 (hc1 n) (hc n) hp0 hp1
    _ = 2 ^ 13 * Real.log (1 / p) / κ ^ 3 * ((n : ℝ) * (L n) ^ 4) := by ring

end Asymptotic

/-! ## Section 5 — non-vacuity (`CLAUDE.md` §11)

A `∀`-statement over unsatisfiable hypotheses proves nothing. -/

section Witness

/-- **The regime hypotheses of Section 3 are simultaneously satisfiable, at a price that is
a positive natural.**

`n = 1`, `L = κ = 1`, `c = 3` (tight against `1 + 2/n`), `p = 1/2` (tight against the
confidence hypothesis), `ε = 1`. Every hypothesis of `Ttc.CVCost.cvVolumeSamplePrice_le`
and of `Ttc.CVCost.cvVolumeSamplePrice_le_of_eps` appears in the type, so an auditor reads
satisfiability off the statement without inspecting the proof. -/
theorem exists_nondegenerate_price :
    ∃ (n : ℕ) (L κ c p ε : ℝ),
      1 ≤ n ∧ 1 ≤ L ∧ 0 < κ ∧ κ ≤ 1 ∧ 1 ≤ c ∧ c ≤ 1 + 2 / (n : ℝ) ∧
      0 < p ∧ p ≤ 1 / 2 ∧ 0 < ε ∧ ε ^ 2 / 10 ≤ κ ∧
      0 < cvVolumeSamplePrice n L κ c p := by
  refine ⟨1, 1, 1, 3, 1 / 2, 1, le_rfl, le_rfl, one_pos, le_rfl, by norm_num, by norm_num,
    by norm_num, le_rfl, one_pos, by norm_num, ?_⟩
  exact cvVolumeSamplePrice_pos 3 (1 / 2) le_rfl one_pos

/-- The empirical mean of `k ≥ 1` copies of a constant is that constant. -/
theorem avgOf_const {Ω : Type*} {k : ℕ} (hk : 0 < k) (v : ℝ) (ω : Ω) :
    CVEst.avgOf k (fun (_ : Fin k) (_ : Ω) => v) ω = v := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  simp only [CVEst.avgOf, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

/-! ### The accuracy bundle at the priced counts

`Ttc.CVCost.exists_nondegenerate_price` certifies Section 3's *arithmetic* hypotheses. This
subsection certifies the other half: that `Ttc.CVCost.median_accuracy_at_price` — the
theorem that makes the number a price — has an inhabited hypothesis bundle **at the counts
this file defines**, not at some convenient smaller ones.

Honest caveat, the same one `Ttc/Volume/CVEstimator.lean` records for its own witness: the
scores are deterministic, so `hsampler` holds at `η = 0`, which is exactly what no real
sampler achieves. This certifies that the bundle is satisfiable, not that the paper's
Gaussian phases satisfy it. As there, **the certification is the proof term, not the
displayed inequality**: the conclusion below is weak on its own, and what carries the
content is that it is discharged by a `median_accuracy_at_price` application. -/

/-- The witness variance budget: `κ = log(6/5)`, the largest budget the estimator's
`hbudget : e^κ − 1 ≤ ε²/5` permits at `ε = 1`. -/
noncomputable def witKappa : ℝ := Real.log (6 / 5)

theorem witKappa_pos : 0 < witKappa := Real.log_pos (by norm_num)

/-- The witness phase count — `Arlib.GaussianCooling.coolPhases` at `n = 1`, `L = 1`. -/
noncomputable abbrev witM : ℕ := coolPhases 1 1 witKappa

/-- The witness per-phase sample count — `Ttc.CVCost.cvSamplesPerPhase` at `c = 1`. -/
noncomputable abbrev witK : ℕ := cvSamplesPerPhase 1 1 witKappa 1

/-- The witness run count — `Ttc.CVCost.cvRuns` at `p = 1/2`. -/
noncomputable abbrev witR : ℕ := cvRuns (1 / 2)

/-- The witness chain `A i = 2⁻ⁱ`: every ratio is exactly `1/2`. -/
noncomputable def witA : ℕ → ℝ := fun i => (1 / 2) ^ i

/-- The witness scores: deterministic `1/2`, on a one-point space. -/
noncomputable def witY : Fin witR → Fin witM → Fin witK → Unit → ℝ := fun _ _ _ _ => 1 / 2

theorem avgOf_witY (t : Fin witR) (i : Fin witM) (ω : Unit) :
    CVEst.avgOf witK (witY t i) ω = 1 / 2 :=
  avgOf_const (cvSamplesPerPhase_pos 1 1 witKappa 1) _ _

theorem prod_avgOf_witY (t : Fin witR) (ω : Unit) :
    ∏ i, CVEst.avgOf witK (witY t i) ω = ((1 : ℝ) / 2) ^ witM := by
  simp [avgOf_witY t _ ω]

theorem witRun (t : Fin witR) (ω : Unit) :
    witA 0 * ∏ i, CVEst.avgOf witK (witY t i) ω = ((1 : ℝ) / 2) ^ witM := by
  rw [prod_avgOf_witY t ω]
  unfold witA
  norm_num

/-- **The hypothesis bundle of `Ttc.CVCost.median_accuracy_at_price` is inhabited at this
file's own counts** — `witR` runs of `witM` phases of `witK` samples, i.e.
`Ttc.CVCost.cvVolumeSamplePrice 1 1 witKappa 1 (1/2)` samples in total.

Every one of its hypotheses is discharged. See the caveat above: the certification is the
proof term. -/
theorem price_bundle_nonvacuous :
    1 - 1 / 2 ≤ (Measure.dirac ()).real
      {_ω : Unit | ((1 : ℝ) / 2) ^ witM ∈ relErr 1 (witA witM)} := by
  refine median_accuracy_at_price (μ := Measure.dirac ()) (n := 1) (L := 1) (κ := witKappa)
    (c := 1) (p := 1 / 2) (Y := witY) (z := fun _ => ((1 : ℝ) / 2) ^ witM) (A := witA)
    (ν := fun _ => 1 / 2) (ε := 1) (ε₀ := 1) (η := 0) (τ := 0)
    le_rfl witKappa_pos one_pos le_rfl le_rfl one_pos (by simp)
    (fun i => by unfold witA; positivity)
    (fun t i j => memLp_const _)
    (fun t i => fun j j' hjj' =>
      (CV.iIndepFun_of_subsingleton (Measure.dirac ()) (witY t i)).indepFun hjj')
    (fun t => CV.iIndepFun_of_subsingleton (Measure.dirac ())
      (fun i => CVEst.avgOf witK (witY t i)))
    (fun t => ?_) (fun t i j => by simp [witY]) (fun i => ?_)
    (fun t i j => by simp [witY])
    (by unfold witKappa; rw [Real.exp_log (by norm_num)]; norm_num) (by norm_num)
    (fun t => ?_)
    (CV.iIndepFun_of_subsingleton (Measure.dirac ())
      (fun t : Fin witR => fun ω : Unit =>
        witA 0 * ∏ i, CVEst.avgOf witK (witY t i) ω))
    (fun ω => CVEst.isMedian_of_const (fun t => witRun t ω)) (by norm_num)
  · have hfun : (fun ω : Unit => ∏ i, CVEst.avgOf witK (witY t i) ω)
        = fun _ => ((1 : ℝ) / 2) ^ witM := funext (prod_avgOf_witY t)
    rw [hfun]
    exact memLp_const _
  · have hratio : witA ((i : ℕ) + 1) / witA (i : ℕ) = 1 / 2 := by
      unfold witA
      rw [pow_succ]
      field_simp
    rw [hratio]
    simp [relErr]
  · have hfun : (fun ω : Unit => witA 0 * ∏ i, CVEst.avgOf witK (witY t i) ω)
        = fun _ => ((1 : ℝ) / 2) ^ witM := funext (witRun t)
    rw [hfun]
    exact measurable_const

end Witness

end Ttc.CVCost

/-! ## Axiom profile

Target for every line: `[propext, Classical.choice, Quot.sound]`.

What `#print axioms` **cannot** see, and what the module docstring therefore says instead:
the unit of `Ttc.CVCost.cvVolumeSamplePrice` is *samples*, not operations; the per-sample
charge `q` of `Ttc.CVCost.cvVolumeOpsPrice` is bounded nowhere in this repository; and
`Ttc.CVEst.volume_accuracy_of_samples`, which this file's counts serve, still carries
`hsampler`, `hsample_sq` and `hend` as binders. -/

-- Section 1: the counts
#print axioms Ttc.CVCost.cvRuns
#print axioms Ttc.CVCost.cvSamplesPerPhase
#print axioms Ttc.CVCost.cvVolumeSamplePrice
#print axioms Ttc.CVCost.cvVolumeOpsPrice
#print axioms Ttc.CVCost.le_cvRuns
#print axioms Ttc.CVCost.cvRuns_pos
#print axioms Ttc.CVCost.le_cvSamplesPerPhase
#print axioms Ttc.CVCost.cvSamplesPerPhase_pos
#print axioms Ttc.CVCost.cvVolumeSamplePrice_pos
#print axioms Ttc.CVCost.cvVolumeSamplePrice_eq

-- Section 2: what makes it a price
#print axioms Ttc.CVCost.median_accuracy_at_price
#print axioms Ttc.CVCost.volume_accuracy_at_price

-- Section 3: the explicit bound
#print axioms Ttc.CVCost.coolPhases_le
#print axioms Ttc.CVCost.cvSamplesPerPhase_le
#print axioms Ttc.CVCost.cvRuns_le
#print axioms Ttc.CVCost.cvVolumeSamplePrice_le
#print axioms Ttc.CVCost.cvVolumeSamplePrice_le_of_eps
#print axioms Ttc.CVCost.half_le_log_one_add
#print axioms Ttc.CVCost.exists_budget_kappa
#print axioms Ttc.CVCost.cvVolumeOpsPrice_le

-- Section 4: the asymptotics
#print axioms Ttc.CVCost.isBigO_cvVolumeSamplePrice_linear

-- Section 5: non-vacuity
#print axioms Ttc.CVCost.exists_nondegenerate_price
#print axioms Ttc.CVCost.avgOf_const
#print axioms Ttc.CVCost.witKappa
#print axioms Ttc.CVCost.witKappa_pos
#print axioms Ttc.CVCost.witA
#print axioms Ttc.CVCost.witY
#print axioms Ttc.CVCost.avgOf_witY
#print axioms Ttc.CVCost.prod_avgOf_witY
#print axioms Ttc.CVCost.witRun
#print axioms Ttc.CVCost.price_bundle_nonvacuous
