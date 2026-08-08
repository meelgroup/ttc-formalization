/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.Bridge
import Arlib.Convexity.GaussianCooling.Estimator
import Arlib.Convexity.GaussianCooling.ZLogconcave

/-!
# `Volume/CousinsVempala`: §5.2 assembled, and what the volume oracle still owes

`Ttc.VolumeAlgorithm` (`Model/ProblemSetting`) is Cousins–Vempala Theorem 1.1 as an
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

**One approximation is still idealized to an equality: `hphase_mean`.** It asks for an
*exactly* unbiased phase estimator, whereas the real algorithm's sampler is only nearly
uniform; relaxing it needs the total-variation bookkeeping of `Arlib.Probability.TV`, and
is not done. The *other* idealization, the exact endpoint `hchain_end`, has been removed:
see `Ttc.CV.G_indicator_mem_relErr` and
`Ttc.VolumeAlgorithm.cousinsVempalaOfBiasedEnd`.

**No `Prop` introduced here assumes its conclusion.** The two `def`s are constructions of
`Ttc.VolumeAlgorithm`, and every hypothesis they take is a statement about the *inputs*
(scores, chains, schedules), never about the estimate being correct at the accuracy the
conclusion asserts — except `ofRuns`' `hgood`, which asserts correctness at the fixed
confidence `4/5` and is amplified to `1 − p`; that amplification is the theorem, and it
is `median_boost`.
-/

namespace Ttc

open MeasureTheory Set ProbabilityTheory Arlib.GaussianCooling

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

`Ttc.VolumeAlgorithm.cousinsVempala` asks for `chain K ε p (phases K ε p) = Vol(K)` on the
nose. The actual last Gaussian of the cooling schedule is *not* `Vol(K)`: by
`Ttc.CV.G_indicator_mem_relErr` it is `Vol(K)` up to a relative bias
`η(s) = 1 − e^{−R²/(2s)}` on a body inside `R·Bₙ`, and that bias is strictly positive for
every finite `s`. So the exact hypothesis is (presumably — the strict inequality
`G(s) < Vol(K)` is not formalized here) not the one the algorithm can supply, and this
construction takes the honest one instead:

* `hchain_end` becomes `chain K ε p (phases K ε p) ∈ relErr (endBias ε) Vol(K)`,
  which is `G_indicator_mem_relErr` with `endBias ε = 1 − e^{−R²/(2σ_m²)}`;
* the runs are computed at an *inner* accuracy `innerAcc ε`, and `hcompose` is the
  scheduling condition `innerAcc ε + endBias ε + innerAcc ε · endBias ε ≤ ε` that makes the
  composed error meet the requested `ε` (`Ttc.CV.relErr_trans`). It is satisfiable for
  every `ε > 0` — e.g. `endBias ε = ε/4`, `innerAcc ε = ε/2` — and `endBias ε` can be
  driven below any target by flattening the last Gaussian (`s → ∞`);
* `hbudget` is correspondingly stated at `innerAcc ε`.

The remaining debt is unchanged and is still the sampler: `hphase_mean`. -/
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
#print axioms CV.iIndepFun_of_subsingleton
#print axioms CV.toReal_volume_pos
#print axioms VolumeAlgorithm.ofRuns
#print axioms VolumeAlgorithm.cousinsVempala
#print axioms VolumeAlgorithm.cousinsVempalaOfBiasedEnd
#print axioms VolumeAlgorithm.cousinsVempalaWitness
#print axioms VolumeAlgorithm.cousinsVempalaWitness_est
#print axioms VolumeAlgorithm.cousinsVempalaBiasedWitness

end Ttc
