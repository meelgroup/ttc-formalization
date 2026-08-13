/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVEstimator
import Arlib.Convexity.GaussianCooling.CouplingRoute

/-!
# `Volume/CouplingAccuracy`: the volume estimator's accuracy on the *realised* chain

`Arlib/Convexity/GaussianCooling/CouplingRoute.lean` assembles Cousins–Vempala's coupling
route (`1409.6011/vol3_journal.tex:1021, 1426-1430`) but leaves the exact-law success
probability as an abstract binder `q`, because `Arlib/**` may not import `Ttc.*`
(`lakefile.toml`).  `Ttc/Volume/CVEstimator.lean` proves exactly that `q`, over an
**arbitrary** probability space.  This file is the composition, which can only be taken on
this side of the import edge.

Every declaration below is a `theorem`; there is no `def`, `structure`, `class`, `axiom`,
`sorry`, `admit` or `native_decide` in this file, and nothing is assumed that is not a
binder of a named statement.

## The two inputs

1. **The exact-law success probability** — `Ttc.CVEst.volume_accuracy_of_samples`
   (`Ttc/Volume/CVEstimator.lean:582`).  Over any probability space `μ`, `r` runs of `m`
   phases of `k` samples with a median `z` satisfy
   `1 − p ≤ μ.real {ω | (1 − ε₀)·Vol(K) ≤ z ω ≤ (1 + ε₀)·Vol(K)}`, given the estimator
   bundle (`hsampler`, `hsample_sq`, the independence facts) and the endpoint
   identification `hend : A m = Vol(K)`.
   (`CouplingRoute.lean`'s docstring calls this `Ttc.CV.volume_accuracy_of_samples`; the
   declaration actually lives in namespace `Ttc.CVEst`.)
2. **The coupling transfer** — `Arlib.GaussianCooling.le_measureReal_runMeasure_of_failure_budget`
   and its chain-level instantiation
   `Arlib.GaussianCooling.le_measureReal_runMeasure_metropolisGaussian_budget`
   (`CouplingRoute.lean:208, 324`).  A per-sample total-variation budget `b` with
   `(r·m)·b ≤ ρ` costs at most `ρ` of success probability, additively, with **no** sup norm
   of the estimator and no `e^{R²/(2σᵢ²)}`.

The join point is exact: (1) concludes on the set
`{ω | (1 − ε₀)·Vol(K) ≤ z ω ∧ z ω ≤ (1 + ε₀)·Vol(K)}`, which is syntactically the set (2)
consumes at `vol := (volume K).toReal`, `acc := ε₀`, `V := z`, `q := 1 − p`.  No use is made
of `Arlib.GaussianCooling.setOf_abs_sub_le_eq_relErr`, because no reshaping is needed.

## What is proved here

* `volume_accuracy_couplingRoute` — **the abstract composition.**  The estimator bundle over
  the *exact*-law run measure `runMeasure ν'`, plus a per-sample TV bound `b` with
  `(r·m)·b ≤ ρ`, gives `1 − p − ρ` on the *realised* run measure `runMeasure ν`.  `E` is an
  arbitrary measurable space; nothing here knows about Markov chains or convex bodies.
* `volume_accuracy_metropolisGaussian` — **the chain-level statement.**  The same with `ν`
  instantiated at the law of the lazy Metropolis–Gaussian chain after `t` steps and `ν'` at
  the exact phase law `coolLaw`, so the per-sample TV bound is *derived* from the mixing
  theorem and the step count is explicit:

      t ≥ 4·(5120²·n²·(log M + 2·log(r·m/ρ))/log²2) + 1.

  Conclusion: the realised run is within `(1 ± ε₀)·Vol(K)` with probability `≥ 1 − p − ρ`.

## Scope, stated honestly (`CLAUDE.md` §6, `CouplingRoute.lean` §4)

This is a statement about an **estimator's success probability under a stated step count**.
It is *not* a running-time claim about TTC, *not* an `O(m·n⁴)` or `O*(n³)` claim, and *not*
a proof that any particular cooling schedule is admissible.  Nothing here bounds the cost of
one Metropolis step, the cost of one oracle call, or the arithmetic inside either.  The step
count `ht` is the mixing theorem's hypothesis, carried through verbatim; nothing here proves
that a chain meeting it exists on a body of interest.

## Binders carried unproved

Every hypothesis of both inputs is carried, none weakened.  The ones that carry the open
half of the argument, and are **assumed, not proved, anywhere in this repository**:

* from the estimator (`CVEstimator.lean`): `hsampler` (the per-phase mean is within a
  relative `η` of the true ratio — this is the sampler), `hsample_sq` (§5.1's relative
  second-moment bound at the realised law), `hend` (`A m = Vol(K)`, the endpoint
  identification that `Ttc.CV.G_indicator_mem_relErr` shows is only approximate);
* from the chain (`CouplingRoute.lean` §3): `hiso` (an isoperimetric inequality for the
  Gaussian-tilted indicator of `K`), `hell`, `hfloor` (the one-step overlap floor) and
  `hwarm` (an `M`-warm start).

`hiso` is now provable for convex `K`: `Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo`
(`Arlib/Convexity/OneDimSharp.lean`) discharges it from `√3·R ≤ 2σ√n`.  The chain theorems
in `CouplingRoute.lean` predate that and still take `hiso` as a binder, so this file carries
it too; swapping to an `hiso`-free upstream is a one-line change here (replace the `hiso`
binder by `hRσ` and pass it through).

## Non-vacuity (`CLAUDE.md` §11)

**This file adds no witness of its own, and the composition has none.**  Each *input* is
separately certified non-vacuous, on a different space:

* the **transfer layer** by `Arlib.GaussianCooling.exists_couplingRoute_witness`
  (`CouplingRoute.lean:427`) — a strictly positive per-sample budget, with the realised and
  exact laws provably different measures, on `RunSpace Bool 1 1`;
* the **estimator bundle** by `Ttc.CVEst.run_bundle_inhabited`, `run_bundle_nonvacuous`
  and `median_bundle_nonvacuous` (`CVEstimator.lean` §"Non-vacuity") — on the one-point
  space `Unit`, with deterministic scores, so `hsampler` holds at `η = 0`, which is exactly
  what no real sampler achieves.

Neither is a witness for the *composed* bundle, whose estimator half must live on
`Arlib.Probability.RunSpace E r m` and whose transfer half must hold at the same `ν'`.  No
such joint witness is constructed here.  Two specific obstructions, flagged rather than
papered over:

* *The `k`-per-phase reading.*  `Arlib.Probability.RunSpace E r m = Fin r → Fin m → E`
  carries **one** `E`-coordinate per (run, phase).  So for `k ≥ 2` the binders `hindep_in`
  and `hsample_mean` constrain `k` functions of a *single* coordinate, which forces
  degeneracy unless `E` itself packs `k` draws (e.g. `E = F^k`).  The bundle is cleanly
  satisfiable at `k = 1` (`Pairwise` over `Fin 1` is vacuous), so the theorems are not
  vacuous; but the "`k` independent samples per phase" reading of
  `volume_accuracy_metropolisGaussian`, where `E = EuclSpace n` is forced, needs `k = 1`.
  Flagged, not fixed: fixing it means reindexing `ν'` over `Fin (m·k)`, which the chain
  theorem's hard-coded `ν' j i = coolLaw m σsq K i` does not admit.
* *The chain layer.*  `CouplingRoute.lean` §5 records why no witness is offered for `hiso`,
  `hell`, `hfloor`, `hwarm`: the existing mixing witness
  `Arlib.MarkovChains.exists_mixesWithin_lazy_metropolisGaussian_witness` lives on
  `B(0,1/2) ⊆ ℝ²`, whose body does **not** contain the unit ball, so it cannot simultaneously
  witness `chain_pos`/`coolLaw_isProbabilityMeasure`, which the chain theorem needs
  (`hball : ball 0 1 ⊆ K`).  No single body is yet known to satisfy both.  Flagged, not
  faked.
-/

namespace Ttc

open MeasureTheory Set ProbabilityTheory Arlib Arlib.GaussianCooling
open scoped ENNReal

namespace CVCoupling

/-! ## 1.  The abstract composition

`E` is an arbitrary measurable space.  `ν' j i` is the *exact* law of the sample at phase
`i` of run `j`; `ν j i` is whatever law the implementation actually realises, assumed within
total variation `b` of it.  The estimator bundle is stated over the exact-law run measure —
that is where `CVEstimator.lean` proves `1 − p`, and the coupling then transfers it. -/

/-- **The volume estimator on a coupled sampler.**

Suppose the Cousins–Vempala estimator bundle holds over the **exact**-law run measure
`Arlib.Probability.runMeasure ν'` — `r` runs of `m` phases of `k` samples, median `z`,
telescoping chain `A` with `A m = Vol(K)`, per-phase means `w` within a relative `η` of the
true ratios, relative second moment `≤ c`, `k ≥ (c−1)·m/κ`, `r ≥ (50/9)·log(1/p)`.  Then it
gives `1 − p` there (`Ttc.CVEst.volume_accuracy_of_samples`).

Suppose further that each of the `r·m` coordinates is actually drawn from a law `ν j i`
within total variation `b` of `ν' j i`, with total budget `(r·m)·b ≤ ρ`.

Then the **realised** run is within `(1 ± ε₀)·Vol(K)` with probability at least `1 − p − ρ`.

The loss is additive in the sample count and carries no bound on the estimator: that is the
whole content of the coupling route (`CouplingRoute.lean` §0). -/
theorem volume_accuracy_couplingRoute
    {E : Type*} [MeasurableSpace E] {r m k : ℕ}
    {ν ν' : Fin r → Fin m → Measure E}
    [hν : ∀ j i, IsProbabilityMeasure (ν j i)]
    [hν' : ∀ j i, IsProbabilityMeasure (ν' j i)]
    {b : ℝ≥0∞} (hb : b ≠ ⊤) (htv : ∀ j i, Arlib.TVLe (ν j i) (ν' j i) b)
    {ρ : ℝ} (hρ : ((r * m : ℕ) : ℝ) * b.toReal ≤ ρ)
    (hm : 0 < m) (hk : 0 < k) (hr : 0 < r)
    {n : ℕ} {K : Set (Space n)}
    {Y : Fin r → Fin m → Fin k → Arlib.Probability.RunSpace E r m → ℝ}
    {z : Arlib.Probability.RunSpace E r m → ℝ}
    {A : ℕ → ℝ} {w : Fin m → ℝ} {c κ ε ε₀ η τ p : ℝ}
    (hz : Measurable z)
    (hκ0 : 0 < κ) (hε : 0 < ε) (hη : 0 ≤ η) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hmeanBudget : 2 * (m : ℝ) * η ≤ τ)
    (hApos : ∀ i, 0 < A i)
    (hL2 : ∀ t i j, MemLp (Y t i j) 2 (Arlib.Probability.runMeasure ν'))
    (hindep_in : ∀ t i, Pairwise fun j j' =>
      IndepFun (Y t i j) (Y t i j') (Arlib.Probability.runMeasure ν'))
    (hindep_ph : ∀ t, iIndepFun (fun i => CVEst.avgOf k (Y t i))
      (Arlib.Probability.runMeasure ν'))
    (hprod : ∀ t, MemLp (fun ω => ∏ i, CVEst.avgOf k (Y t i) ω) 2
      (Arlib.Probability.runMeasure ν'))
    (hsample_mean : ∀ t i j, ∫ ω, Y t i j ω ∂(Arlib.Probability.runMeasure ν') = w i)
    (hsampler : ∀ i : Fin m, w i ∈ relErr η (A ((i : ℕ) + 1) / A (i : ℕ)))
    (hsample_sq : ∀ t i j,
      ∫ ω, (Y t i j ω) ^ 2 ∂(Arlib.Probability.runMeasure ν') ≤ c * (w i) ^ 2)
    (hkge : (c - 1) * (m : ℝ) / κ ≤ (k : ℝ))
    (hbudget : Real.exp κ - 1 ≤ ε ^ 2 / 5)
    (hcompose : ε + τ + ε * τ ≤ ε₀)
    (hrun_meas : ∀ t, Measurable fun ω => A 0 * ∏ i, CVEst.avgOf k (Y t i) ω)
    (hindep_runs : iIndepFun (fun t ω => A 0 * ∏ i, CVEst.avgOf k (Y t i) ω)
      (Arlib.Probability.runMeasure ν'))
    (hmed : ∀ ω, IsMedian (fun t => A 0 * ∏ i, CVEst.avgOf k (Y t i) ω) (z ω))
    (hp : 0 < p)
    (hrp : Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2) ≤ (r : ℝ))
    (hend : A m = (volume K).toReal) :
    1 - p - ρ ≤ (Arlib.Probability.runMeasure ν).real
      {ω | (1 - ε₀) * (volume K).toReal ≤ z ω ∧ z ω ≤ (1 + ε₀) * (volume K).toReal} := by
  haveI : IsProbabilityMeasure (Arlib.Probability.runMeasure ν') := inferInstance
  have hgood := CVEst.volume_accuracy_of_samples (μ := Arlib.Probability.runMeasure ν')
    hm hk hr hκ0 hε hη hτ0 hτ1 hmeanBudget hApos hL2 hindep_in hindep_ph hprod
    hsample_mean hsampler hsample_sq hkge hbudget hcompose hrun_meas hindep_runs hmed
    hp hrp hend
  exact Arlib.GaussianCooling.le_measureReal_runMeasure_of_failure_budget
    (hν := hν) (hν' := hν') hb htv hρ hz hgood

/-! ## 2.  The chain-level statement

`ν j i` is now the law of the **realised** sampler: the lazy Metropolis–Gaussian chain with
kernel `lazy (metropolisGaussian K (δ i) (σ i ^ 2))`, started at an `M`-warm `mu0 j i` and
run for `t` steps.  `ν' j i` is the exact phase law `coolLaw m σsq K i`.  The per-sample TV
budget is no longer a binder — it is `ρ/(r·m)`, and the mixing theorem turns that into the
step count

    t ≥ 4·(5120²·n²·(log M + 2·log(r·m/ρ))/log²2) + 1,

whose `log(r·m/ρ)` is logarithmic in the sample count and in `1/ρ`, with no dependence on
`R`, on `σᵢ` or on the estimator.  That is the point of the coupling route
(`CouplingRoute.lean` §0, §4).

Everything the chain theorem assumes is carried verbatim; in particular `hiso`, `hell`,
`hfloor` and `hwarm` are **unproved binders** here, as they are there. -/

/-- **The Gaussian-cooling volume estimator, on the realised Markov chain.**

Each of the `r·m` samples is drawn by running the lazy Metropolis–Gaussian chain for phase
`i` — kernel `lazy (metropolisGaussian K (δ i) (σ i ^ 2))` — from an `M`-warm start
`mu0 j i` for `t` steps, with

    t ≥ 4·(5120²·n²·(log M + 2·log(r·m/ρ))/log²2) + 1.

Suppose the Cousins–Vempala estimator bundle (`Ttc.CVEst.volume_accuracy_of_samples`) holds
over the **exact** phase law's run measure, so that the idealized run would be within
`(1 ± ε₀)·Vol(K)` with probability `≥ 1 − p`.

Then the **realised** run's median `z` satisfies

    P( (1 − ε₀)·Vol(K) ≤ z ≤ (1 + ε₀)·Vol(K) ) ≥ 1 − p − ρ.

This is `Ttc.CVEst.volume_accuracy_of_samples` composed with
`Arlib.GaussianCooling.le_measureReal_runMeasure_metropolisGaussian_budget`; the failure
probability is `p` (from the median boost, `r ≥ (50/9)·log(1/p)`) plus `ρ` (the total
coupling budget, union-bounded over all `r·m` samples).

**Not a running-time statement**: nothing here bounds the cost of one Metropolis step.  See
the module docstring for the full list of unproved binders (`hiso`, `hell`, `hfloor`,
`hwarm`, `hsampler`, `hsample_sq`, `hend`) and for the non-vacuity position. -/
theorem volume_accuracy_metropolisGaussian {n : ℕ} (hn : 2 ≤ n) {r m k : ℕ}
    (hr : 0 < r) (hm : 0 < m) (hk : 0 < k)
    {σ δ θ : Fin m → ℝ} {R M ρ : ℝ}
    (hσpos : ∀ i, 0 < σ i) (hδop : ∀ i, δ i = σ i / (8 * Real.sqrt n)) (hR : 0 ≤ R)
    {K : Set (EuclSpace n)} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hKtop : volume K ≠ ⊤) (hK0 : volume K ≠ 0)
    (hell : ∀ i, ∀ x ∈ K, ENNReal.ofReal (θ i) ≤ MarkovChains.ell K (δ i) x)
    (hfloor : ∀ i, 1 ≤ 20 * Real.exp (-(2 * R * δ i + δ i ^ 2) / (2 * σ i ^ 2)) * (1 / 4) * θ i)
    (hiso : ∀ i, ∀ S₁ S₂ S₃ : Set (EuclSpace n),
      IsPartition3 Set.univ S₁ S₂ S₃ →
      MeasurableSet S₁ → MeasurableSet S₂ → MeasurableSet S₃ →
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        δ i * Real.log 2 / Real.sqrt n / Real.log 2 ≤ ‖u - v‖ ∨
          4 * (δ i * Real.log 2 / Real.sqrt n / σ i) * Real.sqrt n
            ≤ densDist (Set.indicator K (MarkovChains.gaussianWeightReal (σ i ^ 2))) u v) →
      δ i * Real.log 2 / Real.sqrt n / σ i
          * ((∫ x in S₁, Set.indicator K (MarkovChains.gaussianWeightReal (σ i ^ 2)) x)
            * ∫ x in S₂, Set.indicator K (MarkovChains.gaussianWeightReal (σ i ^ 2)) x)
        ≤ (∫ x, Set.indicator K (MarkovChains.gaussianWeightReal (σ i ^ 2)) x)
          * ∫ x in S₃, Set.indicator K (MarkovChains.gaussianWeightReal (σ i ^ 2)) x)
    {mu0 : Fin r → Fin m → Measure (EuclSpace n)}
    [∀ j i, IsProbabilityMeasure (mu0 j i)] (hM : 1 ≤ M)
    (hwarm : ∀ j i, IsWarm (ENNReal.ofReal M) (mu0 j i)
      (Arlib.uniformOn ((volume : Measure (EuclSpace n)).withDensity
        (MarkovChains.gaussianWeight (σ i ^ 2))) K))
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ (r * m : ℕ))
    {t : ℕ} (ht : 4 * (5120 ^ 2 * (n : ℝ) ^ 2
        * (Real.log M + 2 * Real.log ((r * m : ℕ) / ρ)) / Real.log 2 ^ 2) + 1 ≤ (t : ℝ))
    {σsq : ℕ → ℝ} (hσsch : ∀ j, 0 < σsq j) (hball : Metric.ball (0 : EuclSpace n) 1 ⊆ K)
    (hs : ∀ i : Fin m, σ i ^ 2 = σsq (i : ℕ))
    {Y : Fin r → Fin m → Fin k → Arlib.Probability.RunSpace (EuclSpace n) r m → ℝ}
    {z : Arlib.Probability.RunSpace (EuclSpace n) r m → ℝ}
    {A : ℕ → ℝ} {w : Fin m → ℝ} {c κ ε ε₀ η τ p : ℝ}
    (hz : Measurable z)
    (hκ0 : 0 < κ) (hε : 0 < ε) (hη : 0 ≤ η) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hmeanBudget : 2 * (m : ℝ) * η ≤ τ)
    (hApos : ∀ i, 0 < A i)
    (hL2 : ∀ t' i j, MemLp (Y t' i j) 2 (Arlib.Probability.runMeasure
      fun (_ : Fin r) (i : Fin m) => coolLaw m σsq K (i : ℕ)))
    (hindep_in : ∀ t' i, Pairwise fun j j' => IndepFun (Y t' i j) (Y t' i j')
      (Arlib.Probability.runMeasure fun (_ : Fin r) (i : Fin m) => coolLaw m σsq K (i : ℕ)))
    (hindep_ph : ∀ t', iIndepFun (fun i => CVEst.avgOf k (Y t' i))
      (Arlib.Probability.runMeasure fun (_ : Fin r) (i : Fin m) => coolLaw m σsq K (i : ℕ)))
    (hprod : ∀ t', MemLp (fun ω => ∏ i, CVEst.avgOf k (Y t' i) ω) 2
      (Arlib.Probability.runMeasure fun (_ : Fin r) (i : Fin m) => coolLaw m σsq K (i : ℕ)))
    (hsample_mean : ∀ t' i j, ∫ ω, Y t' i j ω ∂(Arlib.Probability.runMeasure
      fun (_ : Fin r) (i : Fin m) => coolLaw m σsq K (i : ℕ)) = w i)
    (hsampler : ∀ i : Fin m, w i ∈ relErr η (A ((i : ℕ) + 1) / A (i : ℕ)))
    (hsample_sq : ∀ t' i j, ∫ ω, (Y t' i j ω) ^ 2 ∂(Arlib.Probability.runMeasure
      fun (_ : Fin r) (i : Fin m) => coolLaw m σsq K (i : ℕ)) ≤ c * (w i) ^ 2)
    (hkge : (c - 1) * (m : ℝ) / κ ≤ (k : ℝ))
    (hbudget : Real.exp κ - 1 ≤ ε ^ 2 / 5)
    (hcompose : ε + τ + ε * τ ≤ ε₀)
    (hrun_meas : ∀ t', Measurable fun ω => A 0 * ∏ i, CVEst.avgOf k (Y t' i) ω)
    (hindep_runs : iIndepFun (fun t' ω => A 0 * ∏ i, CVEst.avgOf k (Y t' i) ω)
      (Arlib.Probability.runMeasure fun (_ : Fin r) (i : Fin m) => coolLaw m σsq K (i : ℕ)))
    (hmed : ∀ ω, IsMedian (fun t' => A 0 * ∏ i, CVEst.avgOf k (Y t' i) ω) (z ω))
    (hp : 0 < p)
    (hrp : Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2) ≤ (r : ℝ))
    (hend : A m = (volume K).toReal) :
    1 - p - ρ ≤ (Arlib.Probability.runMeasure
        fun (j : Fin r) (i : Fin m) => MarkovChains.iterate
          (MarkovChains.lazy (MarkovChains.metropolisGaussian K (δ i) (σ i ^ 2)))
          (mu0 j i) t).real
      {ω | (1 - ε₀) * (volume K).toReal ≤ z ω ∧ z ω ≤ (1 + ε₀) * (volume K).toReal} := by
  haveI hcool : ∀ (_ : Fin r) (i : Fin m), IsProbabilityMeasure (coolLaw m σsq K (i : ℕ)) :=
    fun _ i => coolLaw_isProbabilityMeasure hσsch hball hKtop _
  haveI : IsProbabilityMeasure (Arlib.Probability.runMeasure
      fun (_ : Fin r) (i : Fin m) => coolLaw m σsq K (i : ℕ)) :=
    @Arlib.Probability.isProbabilityMeasure_runMeasure r m (EuclSpace n) _
      (fun (_ : Fin r) (i : Fin m) => coolLaw m σsq K (i : ℕ)) hcool
  have hgood := CVEst.volume_accuracy_of_samples
    (μ := Arlib.Probability.runMeasure fun (_ : Fin r) (i : Fin m) => coolLaw m σsq K (i : ℕ))
    hm hk hr hκ0 hε hη hτ0 hτ1 hmeanBudget hApos hL2 hindep_in hindep_ph hprod
    hsample_mean hsampler hsample_sq hkge hbudget hcompose hrun_meas hindep_runs hmed
    hp hrp hend
  exact Arlib.GaussianCooling.le_measureReal_runMeasure_metropolisGaussian_budget
    hn hr hm hσpos hδop hR hK hKc hKR hKtop hK0 hell hfloor hiso hM hwarm hρ0 hρ1 ht
    hσsch hball hs hz hgood

end CVCoupling

end Ttc

/-! ## Axiom audit (`CLAUDE.md` §4) -/

#print axioms Ttc.CVCoupling.volume_accuracy_couplingRoute
#print axioms Ttc.CVCoupling.volume_accuracy_metropolisGaussian
