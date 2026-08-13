/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CousinsVempala
import Arlib.Convexity.GaussianCooling.Chain
import Arlib.Convexity.GaussianCooling.Schedule
import Arlib.Probability.RunPlumbing

/-!
# `Volume/CVInstantiate`: plugging the proved schedule and cooling chain into §5.2

`Ttc.VolumeAlgorithm.cousinsVempala` (`Ttc/Volume/CousinsVempala.lean`) is the §5.2
assembly with **fourteen** named hypotheses and six pieces of data. Six of those fourteen
are not open problems at all — they are already unconditional theorems in `Arlib`, about
concrete `Arlib` data (`Arlib.GaussianCooling.reps`, `Arlib.GaussianCooling.varBudget`,
`Arlib.GaussianCooling.chain`). This file is the wiring: it supplies that data and
discharges those six, leaving **eight** hypotheses on the table.

Nothing here is assumed. Every one of the six is closed by a `theorem` proved outright in
`Arlib`; no new `Prop`, `def`, `structure` or `class` is introduced that asserts anything.
The only *new* inputs are the two pieces of schedule data the algorithm's caller must pick
anyway (`phases`, `σsq`) plus the side condition `0 < σsq K ε p j` that `Arlib`'s
`chain_pos` needs — a positivity guard on a variance schedule, not a mathematical debt.

A second step, `Ttc.VolumeAlgorithm.cousinsVempalaOfRuns`, then takes the coin space to be
`Arlib.Probability.NatRunSpace E` (independent runs of independent phases) and discharges
six more from `Arlib/Probability/RunPlumbing.lean`, leaving **exactly two**:
`hphase_mean` and `hphase_var`. Those two are the whole residual gap, and both are about
the sampler, not about bookkeeping.

A third step, `Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMean`, is the same wiring with
`hphase_mean` **relaxed from an equation to an interval** — the shape a total-variation
bound on a sampler can actually deliver, and the shape
`Ttc.CV.run_relErr_four_fifths_approxMean` consumes. It is the constructor the capstone
`Ttc.ttc_runtime_mn4` runs on. Its conclusion, its coin space, its score and its estimate
are `cousinsVempalaOfRuns`'s; only the mean hypothesis (and, forced by the accuracy split,
the variance budget) differs.
-/

namespace Ttc

open MeasureTheory ProbabilityTheory
open Arlib.GaussianCooling (IsMedian)

/-- **§5.2 with the schedule and the cooling chain supplied and proved.**

A partial application of `Ttc.VolumeAlgorithm.cousinsVempala` in which

* the repetition count is `Arlib.GaussianCooling.reps ε p = ⌈(50/9)·log(1/p)⌉₊ + 1`,
* the relative-variance budget is `Arlib.GaussianCooling.varBudget ε = log(1 + ε²/5)`,
* the cooling chain is `Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K`, i.e.
  `i ↦ ∫_K e^{−‖x‖²/(2 σsq i)}` for `i < phases K ε p` and `∫_K 1 = Vol(K)` from the
  terminal index onwards,

and the six hypotheses that concern *only* those three are discharged from `Arlib`.

## What is discharged, and what remains

| hypothesis of `cousinsVempala` | status | by |
| --- | --- | --- |
| `hreps_pos`   | **discharged** | `Arlib.GaussianCooling.reps_pos` |
| `hreps`       | **discharged** | `Arlib.GaussianCooling.reps_spec` |
| `hbudget0`    | **discharged** | `Arlib.GaussianCooling.varBudget_nonneg` |
| `hbudget`     | **discharged** | `Arlib.GaussianCooling.varBudget_spec` |
| `hchain_pos`  | **discharged** | `Arlib.GaussianCooling.chain_pos` (needs `hσ`) |
| `hchain_end`  | **discharged** | `Arlib.GaussianCooling.chain_end` (no side conditions) |
| `hW_meas`      | remains | measurability of each phase score |
| `hmed_meas`    | remains | measurability of the median selector |
| `hmed`         | remains | the selector really selects a median |
| `hindep_runs`  | remains | the `reps` runs use independent randomness |
| `hprodLp`      | remains | each run's telescoping product is in `L²` |
| `hphase_indep` | remains | the `phases` phases use independent randomness |
| `hphase_mean`  | remains | **stated too strongly — see below** |
| `hphase_var`   | remains | relative second moment `≤ 1 + κ/m` for the *sampled* score |

Six discharged, **eight remaining**. Six of the eight (`hW_meas`, `hmed_meas`, `hmed`,
`hindep_runs`, `hprodLp`, `hphase_indep`) are admissibility and independence
bookkeeping about whatever concrete `W` and `med` a caller supplies; `hphase_var` is a
transport problem (§5.1 proves the corresponding bound for the *ideal* estimator
unconditionally, `Arlib.GaussianCooling.fixed_var_bound_ratio_indicator`).

**`hphase_mean` is the deep one, and it is stated too strongly here.** It demands
`∫ W K ε p j i dμ = chain (i+1) / chain i` — *exact* unbiasedness of the phase-`i` score
for the phase ratio. `Arlib.GaussianCooling.chain_ratio_eq` identifies the right-hand side
as a deterministic integral against the phase-`i` density `coolWeight i / chain i`, so
what is missing is a random variable whose law *is* that density.

The reason no mixing bound delivers the equation is **not** that a Markov chain is always
at positive total-variation distance from its stationary law. That claim is *false*, and
this repository refutes it: `Arlib.MarkovChains.mixesWithin_const`
(`Arlib/MarkovChains/Continuous/Warmness.lean:382`) proves
`MixesWithin (Kernel.const Ω π) π μ₀ 1 0` — total variation exactly `0`, in one step. The
correct argument is about what a *bound* buys: a guarantee `TV ≤ tvErr` with `tvErr > 0`
pins the score's mean only to within `tvErr` (times the score's sup-norm), and
`Arlib.GaussianCooling.exists_tvLe_coolLaw_integral_phaseScore_ne` makes that
machine-checked — at every `tvErr > 0` there is a law within `tvErr` of `coolLaw` whose
phase-score integral is *not* the chain ratio. So an equation is not a hypothesis any
mixing theorem can discharge, at any rate.

Nor is the remedy "a perfect sampler *or* restating §5.2" — Cousins–Vempala do neither:
they keep the exact-law equation and pay for the sampler with a coupling. The remedy used
here is the third one, and it is already in the repository:
`Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMean` (below) carries the **interval**
`∫ W ∈ (1 ± ε/(2(2+ε)m))·(chain(i+1)/chain i)` instead, which is exactly what a TV bound
buys, and `Ttc.VolumeAlgorithm.cousinsVempalaOfSampler` *derives* that interval from a TV
guarantee (`Ttc.CV.sampledPhase_mean_mem_relErr`) rather than assuming it. The capstone
`Ttc.ttc_runtime_mn4` runs on the interval form. The equation-carrying
`cousinsVempalaOfRuns` is kept only because `Ttc.cvVolAlg` and
`Ttc.ttcPoly_volume_estimate_cv` are stated at it. What remains genuinely open is the
*sampler*: producing `hTV` at the accuracy the slack conditions need.

## Side conditions introduced

`hσ : ∀ K ε p j, 0 < σsq K ε p j` — the variance schedule is positive. Required by
`Arlib.GaussianCooling.chain_pos`; it is a condition on data the caller chooses (e.g.
`Arlib.GaussianCooling.geomSchedule`), not an assumption about the algorithm.

Note that `hchain_end` needs *no* side condition at all — not `0 < ε`, not convexity, not
`volume K ≠ ⊤`, and in particular no radius hypothesis `K ⊆ R·Bₙ`. `Arlib`'s `coolWeight`
is literally the constant `1` from the terminal index on, so the terminal chain entry is
`∫_K 1 = Vol(K)` by `setIntegral_const`. -/
noncomputable def VolumeAlgorithm.cousinsVempalaOfSchedule (n : ℕ) (Ω : Type)
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    -- the schedule data the caller picks
    (phases : Set (Space n) → ℝ → ℝ → ℕ)
    (σsq : Set (Space n) → ℝ → ℝ → ℕ → ℝ)
    (W : Set (Space n) → ℝ → ℝ → ℕ → ℕ → Ω → ℝ)
    (med : Set (Space n) → ℝ → ℝ → Ω → ℝ)
    -- side condition on the schedule data (NOT one of the fourteen)
    (hσ : ∀ K ε p j, 0 < σsq K ε p j)
    -- the eight remaining hypotheses
    (hW_meas : ∀ K ε p j i, Measurable (W K ε p j i))
    (hmed_meas : ∀ K ε p, Measurable (med K ε p))
    (hmed : ∀ K ε p ω,
      IsMedian (fun j : Fin (Arlib.GaussianCooling.reps ε p) =>
        Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K 0 *
          ∏ i : Fin (phases K ε p), W K ε p (j : ℕ) (i : ℕ) ω) (med K ε p ω))
    (hindep_runs : ∀ K ε p,
      iIndepFun (fun (j : Fin (Arlib.GaussianCooling.reps ε p)) (ω : Ω) =>
        Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K 0 *
          ∏ i : Fin (phases K ε p), W K ε p (j : ℕ) (i : ℕ) ω) μ)
    (hprodLp : ∀ K ε p j,
      MemLp (fun ω => ∏ i : Fin (phases K ε p), W K ε p j (i : ℕ) ω) 2 μ)
    (hphase_indep : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j,
      iIndepFun (fun i : Fin (phases K ε p) => W K ε p j (i : ℕ)) μ)
    (hphase_mean : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j (i : Fin (phases K ε p)),
      ∫ ω, W K ε p j (i : ℕ) ω ∂μ =
        Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K ((i : ℕ) + 1) /
          Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K (i : ℕ))
    (hphase_var : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j (i : Fin (phases K ε p)),
      ∫ ω, (W K ε p j (i : ℕ) ω) ^ 2 ∂μ
        ≤ (1 + Arlib.GaussianCooling.varBudget ε / (phases K ε p : ℝ)) *
            (∫ ω, W K ε p j (i : ℕ) ω ∂μ) ^ 2) :
    VolumeAlgorithm n :=
  VolumeAlgorithm.cousinsVempala n Ω μ phases
    Arlib.GaussianCooling.reps
    Arlib.GaussianCooling.varBudget
    (fun K ε p i => Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K i)
    W med
    -- hreps_pos, hreps, hbudget0, hbudget : from `Arlib/…/Schedule.lean`
    Arlib.GaussianCooling.reps_pos
    Arlib.GaussianCooling.reps_spec
    Arlib.GaussianCooling.varBudget_nonneg
    Arlib.GaussianCooling.varBudget_spec
    -- admissibility: passed through unchanged
    hW_meas hmed_meas hmed hindep_runs hprodLp
    -- hchain_pos, hchain_end : from `Arlib/…/Chain.lean`
    (fun K ε p _hε _hp _hp1 _hconv hball hfin i =>
      Arlib.GaussianCooling.chain_pos (hσ K ε p) hball hfin i)
    (fun K ε p _hε _hp _hp1 _hconv _hball _hfin =>
      Arlib.GaussianCooling.chain_end (phases K ε p) (σsq K ε p) K)
    -- the sampler debt: passed through unchanged
    hphase_indep hphase_mean hphase_var

/-- The six discharged hypotheses, restated as standalone facts about the concrete
schedule data used above, so that a reader can check each one in isolation without
unfolding the partial application. Purely a re-export; each field is the `Arlib` theorem
verbatim. -/
theorem VolumeAlgorithm.cousinsVempalaOfSchedule_discharged
    (n : ℕ) (phases : Set (Space n) → ℝ → ℝ → ℕ)
    (σsq : Set (Space n) → ℝ → ℝ → ℕ → ℝ) (hσ : ∀ K ε p j, 0 < σsq K ε p j) :
    (∀ ε p : ℝ, 0 < p → p < 1 → 0 < Arlib.GaussianCooling.reps ε p) ∧
    (∀ ε p : ℝ, 0 < p → p < 1 →
      Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2) ≤
        (Arlib.GaussianCooling.reps ε p : ℝ)) ∧
    (∀ ε : ℝ, 0 < ε → 0 ≤ Arlib.GaussianCooling.varBudget ε) ∧
    (∀ ε : ℝ, 0 < ε →
      Real.exp (Arlib.GaussianCooling.varBudget ε) - 1 ≤ ε ^ 2 / 5) ∧
    (∀ (K : Set (Space n)) (ε p : ℝ), Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ i, 0 < Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K i) ∧
    (∀ (K : Set (Space n)) (ε p : ℝ),
      Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K (phases K ε p) =
        (volume K).toReal) :=
  ⟨Arlib.GaussianCooling.reps_pos, Arlib.GaussianCooling.reps_spec,
    Arlib.GaussianCooling.varBudget_nonneg, Arlib.GaussianCooling.varBudget_spec,
    fun K ε p hball hfin i => Arlib.GaussianCooling.chain_pos (hσ K ε p) hball hfin i,
    fun K ε p => Arlib.GaussianCooling.chain_end (phases K ε p) (σsq K ε p) K⟩

/-! ## Taking the coin space to be independent runs of independent phases

`cousinsVempalaOfSchedule` still asks the caller for a coin space `Ω`, a score family `W`
and a median selector `med`, and for six bookkeeping facts about them. Those six are not
about the sampler at all — they say "the runs really are independent, the phases really
are independent, the scores really are measurable, the selector really selects a median,
the run product really is in `L²`". `Arlib/Probability/RunPlumbing.lean` proves all six
outright for the canonical such space. This section wires it in.

**Which of the two `RunPlumbing` spaces.** `RunSpace E r m = Fin r → Fin m → E` fixes the
run count `r` and the phase count `m` *in the type*, but the counts the algorithm needs
are `Arlib.GaussianCooling.reps ε p` and `phases K ε p`, which depend on the input
`(K, ε, p)` — while `VolumeAlgorithm.cousinsVempala` fixes a single `Ω` and `μ` up front,
before any input is seen. That is a genuine dependency clash, and it rules out the finite
space. We therefore use the **universal** space `NatRunSpace E = ℕ → ℕ → E` with
`natRunMeasure ν = infinitePi fun j => infinitePi fun i => ν j i`, whose indices are
naturals and where `r` and `m` are arguments of the *theorems* rather than of the space.
No side condition `r = reps ε p` is needed.

**Index order (checked, not guessed).** In `cousinsVempala` the first index of
`W K ε p j i` is the **run** (`hindep_runs` quantifies `j : Fin (reps ε p)`) and the
second is the **phase** (`hphase_indep` quantifies `i : Fin (phases K ε p)`). In
`RunPlumbing`, `natScore g j i ω = g j i (ω j i)` and `iIndepFun_natRuns` /
`iIndepFun_natScore_phases` likewise range `j` over runs (`Fin r`) and `i` over phases
(`Fin m`). The two conventions **agree**; no transposition is applied anywhere below. -/

/-- **The coordinate `ω j i` of the universal run space has law `ν j i`.**

A one-line consequence of `Arlib.Probability.measurePreserving_natCoord`: the integral of
any measurable `f` against the phase-`(j, i)` coordinate of the big product measure is the
integral of `f` against the single measure `ν j i`. This is what lets the two remaining
hypotheses of `cousinsVempalaOfRuns` be stated about the *sampler's own law* `ν j i`
rather than about the product space. -/
theorem integral_natRunCoord {E : Type} [MeasurableSpace E] (ν : ℕ → ℕ → Measure E)
    [∀ j i, IsProbabilityMeasure (ν j i)] (j i : ℕ) {f : E → ℝ} (hf : Measurable f) :
    ∫ ω, f (ω j i) ∂(Arlib.Probability.natRunMeasure ν) = ∫ x, f x ∂(ν j i) := by
  have hmp := Arlib.Probability.measurePreserving_natCoord ν j i
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable]
  rw [hmp.map_eq]
  exact hf.aestronglyMeasurable

/-- **§5.2 with the schedule, the cooling chain *and all the run/phase bookkeeping*
supplied and proved — exactly two hypotheses left.**

The coin space is `Arlib.Probability.NatRunSpace E = ℕ → ℕ → E`: one coordinate of an
arbitrary measurable space `E` (a sampler trajectory, say) per (run, phase) pair, all
coordinates independent with laws `ν j i`. The score of run `j`, phase `i` is
`Arlib.Probability.natScore (g K ε p) j i ω = g K ε p j i (ω j i)`, i.e. an arbitrary
measurable function of that pair's *own* randomness, and the median selector is
`Arlib.Probability.medianSel`.

## What is discharged here, and by what

| hypothesis of `cousinsVempalaOfSchedule` | by |
| --- | --- |
| `hW_meas`      | `Arlib.Probability.measurable_natScore` |
| `hmed_meas`    | `Arlib.Probability.measurable_medianSel_natRuns` |
| `hmed`         | `Arlib.Probability.isMedian_medianSel_natRuns` |
| `hindep_runs`  | `Arlib.Probability.iIndepFun_natRuns` |
| `hprodLp`      | `Arlib.Probability.memLp_two_natRunProd` |
| `hphase_indep` | `Arlib.Probability.iIndepFun_natScore_phases` |

Together with the six that `cousinsVempalaOfSchedule` already discharged from `Arlib`'s
schedule and chain files, **twelve of `cousinsVempala`'s fourteen hypotheses are now
theorems**. The two that remain are exactly the two that are about the *sampler* rather
than about bookkeeping:

* `hphase_mean` — the phase-`i` score is **exactly** unbiased for the phase-`i` chain
  ratio. This is stronger than the mathematics needs and stronger than any sampler
  guarantee can supply; `Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMean` below is the
  same construction on the interval form, and is what the capstone runs on. This
  constructor is retained because `Ttc.cvVolAlg` and `Ttc.ttcPoly_volume_estimate_cv` are
  stated at it;
* `hphase_var` — its relative second moment is at most `1 + varBudget ε / phases`.

Both are now stated against `ν j i`, the law of one phase's randomness, not against the
product measure (`Ttc.integral_natRunCoord` performs the transfer, and is a proved
equality, not an assumption). `Arlib.Probability.memLp_two_natRunProd` deliberately does
**not** give `hphase_var`: it gives membership in `L²`, not the `(1 + κ/m)` ratio bound.

## Data and side conditions the caller supplies

* `ν j i` — the law of the randomness of run `j`, phase `i`. It is a *fixed* family: the
  estimator interface fixes one `Ω` and one `μ` before the input `(K, ε, p)` is seen, so
  the input-dependence lives entirely in the score functions `g K ε p j i`, which read the
  raw randomness of that phase. `E` needs nothing beyond `MeasurableSpace E`.
* `g` — the score family; `hg` its measurability and `hgb` a uniform bound `|g| ≤ B`.
  Both are conditions on data the caller picks, and `hgb` is what `memLp_two_natRunProd`
  consumes; neither asserts anything about means or variances.
* `hσ` — positivity of the variance schedule, inherited from `cousinsVempalaOfSchedule`.

## Index convention

`j` is the **run** index and `i` the **phase** index on *both* sides; see the section
docstring above for where this was checked. Nothing is transposed. -/
noncomputable def VolumeAlgorithm.cousinsVempalaOfRuns (n : ℕ) (E : Type)
    [MeasurableSpace E] (ν : ℕ → ℕ → Measure E) [∀ j i, IsProbabilityMeasure (ν j i)]
    -- the schedule data the caller picks
    (phases : Set (Space n) → ℝ → ℝ → ℕ)
    (σsq : Set (Space n) → ℝ → ℝ → ℕ → ℝ)
    -- the score family: run `j`, phase `i` of input `(K, ε, p)` scores its own coordinate
    (g : Set (Space n) → ℝ → ℝ → ℕ → ℕ → E → ℝ) (B : ℝ)
    -- side conditions on that data (NOT among the fourteen)
    (hσ : ∀ K ε p j, 0 < σsq K ε p j)
    (hg : ∀ K ε p j i, Measurable (g K ε p j i))
    (hgb : ∀ K ε p j i x, |g K ε p j i x| ≤ B)
    -- the two remaining hypotheses, both about the sampler
    (hphase_mean : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j (i : Fin (phases K ε p)),
      ∫ x, g K ε p j (i : ℕ) x ∂(ν j (i : ℕ)) =
        Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K ((i : ℕ) + 1) /
          Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K (i : ℕ))
    (hphase_var : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j (i : Fin (phases K ε p)),
      ∫ x, (g K ε p j (i : ℕ) x) ^ 2 ∂(ν j (i : ℕ))
        ≤ (1 + Arlib.GaussianCooling.varBudget ε / (phases K ε p : ℝ)) *
            (∫ x, g K ε p j (i : ℕ) x ∂(ν j (i : ℕ))) ^ 2) :
    VolumeAlgorithm n :=
  VolumeAlgorithm.cousinsVempalaOfSchedule n (Arlib.Probability.NatRunSpace E)
    (Arlib.Probability.natRunMeasure ν) phases σsq
    -- `W`: the phase score reads the coordinate of its own (run, phase) pair
    (fun K ε p => Arlib.Probability.natScore (g K ε p))
    -- `med`: the explicit measurable median selector of the `reps ε p` run products
    (fun K ε p ω => Arlib.Probability.medianSel
      fun j : Fin (Arlib.GaussianCooling.reps ε p) =>
        Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K 0 *
          ∏ i : Fin (phases K ε p),
            Arlib.Probability.natScore (g K ε p) (j : ℕ) (i : ℕ) ω)
    hσ
    -- hW_meas
    (fun K ε p => Arlib.Probability.measurable_natScore (hg K ε p))
    -- hmed_meas
    (fun K ε p => Arlib.Probability.measurable_medianSel_natRuns (hg K ε p) _ _ _)
    -- hmed
    (fun K ε p ω => Arlib.Probability.isMedian_medianSel_natRuns (g K ε p) _ _ _ ω)
    -- hindep_runs
    (fun K ε p => Arlib.Probability.iIndepFun_natRuns ν (hg K ε p) _ _ _)
    -- hprodLp
    (fun K ε p j => Arlib.Probability.memLp_two_natRunProd ν (hg K ε p) (hgb K ε p) j _)
    -- hphase_indep
    (fun K ε p _ _ _ _ _ _ j =>
      Arlib.Probability.iIndepFun_natScore_phases ν (hg K ε p) j _)
    -- hphase_mean : transferred to the coordinate law by `integral_natRunCoord`
    (fun K ε p hε hp hp1 hconv hball hfin j i =>
      (integral_natRunCoord ν j (i : ℕ) (hg K ε p j (i : ℕ))).trans
        (hphase_mean K ε p hε hp hp1 hconv hball hfin j i))
    -- hphase_var : same transfer, on both the second moment and the mean
    (fun K ε p hε hp hp1 hconv hball hfin j i => by
      -- both `have`s hold by `integral_natRunCoord` after unfolding `natScore`
      have hsq : ∫ ω, (Arlib.Probability.natScore (g K ε p) j (i : ℕ) ω) ^ 2
            ∂(Arlib.Probability.natRunMeasure ν)
          = ∫ x, (g K ε p j (i : ℕ) x) ^ 2 ∂(ν j (i : ℕ)) :=
        integral_natRunCoord ν j (i : ℕ) ((hg K ε p j (i : ℕ)).pow_const 2)
      have hmean : ∫ ω, Arlib.Probability.natScore (g K ε p) j (i : ℕ) ω
            ∂(Arlib.Probability.natRunMeasure ν)
          = ∫ x, g K ε p j (i : ℕ) x ∂(ν j (i : ℕ)) :=
        integral_natRunCoord ν j (i : ℕ) (hg K ε p j (i : ℕ))
      rw [hsq, hmean]
      exact hphase_var K ε p hε hp hp1 hconv hball hfin j i)

/-- **Non-vacuity of the `cousinsVempalaOfRuns` bundle** (`CLAUDE.md` §11): every argument
of `Ttc.VolumeAlgorithm.cousinsVempalaOfRuns` can be supplied simultaneously, so the
definition is about something and its hypotheses do not contradict each other.

This witness is **degenerate on purpose**, and it is not evidence that the sampler debt is
dischargeable. It takes zero phases, so `Fin (phases K ε p)` is empty and both remaining
hypotheses hold by `Fin.elim0`; the cooling chain then collapses to its `0`-th entry,
which `Arlib.GaussianCooling.chain_end` already proves is `Vol(K)`. It witnesses
*satisfiability of the hypothesis bundle*, nothing more. The genuinely random witnesses
for the run/phase plumbing itself live in `Arlib/Probability/RunPlumbing.lean`
(`natWit_not_ae_const`, `trajWit_not_ae_const`), which prove that on the same universal
space no score is almost-everywhere constant. -/
noncomputable def VolumeAlgorithm.cousinsVempalaOfRunsWitness (n : ℕ) : VolumeAlgorithm n :=
  VolumeAlgorithm.cousinsVempalaOfRuns n Unit (fun _ _ => Measure.dirac ())
    (fun _ _ _ => 0) (fun _ _ _ _ => 1) (fun _ _ _ _ _ _ => 1) 1
    (fun _ _ _ _ => one_pos) (fun _ _ _ _ _ => measurable_const)
    (fun _ _ _ _ _ _ => le_of_eq (abs_one))
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)

/-! ## The same, with the phase mean an interval rather than an equation

`cousinsVempalaOfRuns` above asks each phase score to be **exactly** unbiased for the
chain ratio.  No sampler can supply that (see the docstring of
`cousinsVempalaOfRunsApproxMean` below), and the run bound does not need it:
`Ttc.CV.run_relErr_four_fifths_approxMean` tolerates a per-phase relative bias `η`
provided `2·m·η ≤ τ` and the accuracy is split as `innerAcc + τ + innerAcc·τ ≤ ε`.
`cousinsVempalaOfRunsApproxMean` is the same wiring on that weaker hypothesis, with the
split **hard-wired** so that no new binder appears for it. -/

/-- **§5.2 on the universal run space, with `hphase_mean` an interval rather than an
equation — the constructor the capstone `Ttc.ttc_runtime_mn4` runs on.**

Same coin space, same score, same median selector, same conclusion as
`Ttc.VolumeAlgorithm.cousinsVempalaOfRuns`: the estimate on `K` at accuracy `ε` and
confidence `p` is the median of `Arlib.GaussianCooling.reps ε p` independent runs of
`Arlib.GaussianCooling.chain … 0 · ∏ᵢ g K ε p j i (ω j i)`, correct within relative `ε`
with probability `≥ 1 − p`.  **The `VolumeAlgorithm` guarantee is character-for-character
the one `cousinsVempalaOfRuns` produces** — `VolumeAlgorithm.correct` is a `Prop` field, so
the two constructions differ only in *how* that field is proved, not in what it says, and
the data fields (`Ω`, `μ`, `est`) are the same expressions —
`Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMean_est` below checks the `est` half of
that claim by `rfl` rather than leaving it to the reader's eye.

## The one hypothesis that changes

| | `cousinsVempalaOfRuns` | here |
| --- | --- | --- |
| `hphase_mean` | `∫ g dν = chain(i+1)/chain(i)` | `∫ g dν ∈ (1 ± ε/(2(2+ε)m))·(chain(i+1)/chain(i))` |

`m = phases K ε p`, so the per-phase tolerance is `Θ(ε/m)`, not `Θ(ε)` — the `m` is not
cosmetic, the per-phase biases multiply and `Arlib.GaussianCooling.phaseBias_le` is what
pays for the compounding.

**Why the equation had to go.**  It is not that a Markov chain is always at positive
total-variation distance from its stationary law — that claim is *false*, and this
repository refutes it: `Arlib.MarkovChains.mixesWithin_const` exhibits
`MixesWithin (Kernel.const Ω π) π μ₀ 1 0`, total variation exactly `0` in one step.  The
correct statement is about what a *bound* buys: a guarantee `TV(law of the sample, coolLaw
i) ≤ tvErr` with `tvErr > 0` constrains the score's mean only to within `tvErr` (times the
score's sup-norm), and no strengthening of a mixing bound short of `tvErr = 0` pins the
mean on the nose.  `Arlib.GaussianCooling.exists_tvLe_coolLaw_integral_phaseScore_ne` makes
this machine-checked: it exhibits a law at total variation `≤ tvErr` of `coolLaw` whose
phase-score integral is **not** the chain ratio, at every `tvErr > 0`.  The interval below
is exactly what a TV bound does buy, and
`Ttc.VolumeAlgorithm.cousinsVempalaOfSampler` derives it from `hTV` rather than assuming
it (`Ttc.CV.sampledPhase_mean_mem_relErr`).

## The accuracy split, hard-wired

`Ttc.VolumeAlgorithm.cousinsVempalaOfApproxMean` splits the requested `ε` into an inner
(Chebyshev) accuracy and a mean bias.  Rather than expose the split as data, this
constructor fixes it at the repository's own choice, which meets the composition
`innerAcc + meanBias + innerAcc·meanBias ≤ ε` with **equality**:

* `innerAcc ε = ε/2`,
* `meanBias ε = ε/(2+ε)` (so `ε/2 + ε/(2+ε) + (ε/2)(ε/(2+ε)) = ε`),
* `phaseBias K ε p = ε/(2(2+ε)·m) = meanBias ε/(2m)`, meeting `2·m·phaseBias ≤ meanBias`
  with equality when `m > 0` and trivially when `m = 0`.

Consequently **`hphase_var` is stated at `Arlib.GaussianCooling.varBudget (ε/2)`, not at
`varBudget ε`**.  That is forced, not chosen: `Real.exp (varBudget ε) - 1 = ε²/5`
(`Arlib.GaussianCooling.exp_varBudget`), and `cousinsVempalaOfApproxMean` needs
`exp (varBudget') - 1 ≤ innerAcc(ε)²/5`; once any of the budget is spent on bias,
`innerAcc ε < ε` and the variance budget shrinks with it.  There is no split with a
strictly positive bias tolerance that keeps the full `varBudget ε`.

## Everything else is `cousinsVempalaOfRuns` verbatim

`hσ`, `hg`, `hgb` are the same side conditions on caller-chosen data; the six plumbing
hypotheses are discharged from the same `Arlib/Probability/RunPlumbing.lean` theorems and
the four schedule/chain hypotheses from the same `Arlib/…/Schedule.lean` and
`Arlib/…/Chain.lean` theorems.  No `hphases_pos` is required: `cousinsVempalaOfApproxMean`
handles the zero-phase case directly, which is what keeps the degenerate non-vacuity
witness below available. -/
noncomputable def VolumeAlgorithm.cousinsVempalaOfRunsApproxMean (n : ℕ) (E : Type)
    [MeasurableSpace E] (ν : ℕ → ℕ → Measure E) [∀ j i, IsProbabilityMeasure (ν j i)]
    -- the schedule data the caller picks
    (phases : Set (Space n) → ℝ → ℝ → ℕ)
    (σsq : Set (Space n) → ℝ → ℝ → ℕ → ℝ)
    -- the score family: run `j`, phase `i` of input `(K, ε, p)` scores its own coordinate
    (g : Set (Space n) → ℝ → ℝ → ℕ → ℕ → E → ℝ) (B : ℝ)
    -- side conditions on that data (NOT among the fourteen)
    (hσ : ∀ K ε p j, 0 < σsq K ε p j)
    (hg : ∀ K ε p j i, Measurable (g K ε p j i))
    (hgb : ∀ K ε p j i x, |g K ε p j i x| ≤ B)
    -- the two remaining hypotheses, both about the sampler
    (hphase_mean : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j (i : Fin (phases K ε p)),
      ∫ x, g K ε p j (i : ℕ) x ∂(ν j (i : ℕ)) ∈
        relErr (ε / (2 * (2 + ε) * (phases K ε p : ℝ)))
          (Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K ((i : ℕ) + 1) /
            Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K (i : ℕ)))
    (hphase_var : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j (i : Fin (phases K ε p)),
      ∫ x, (g K ε p j (i : ℕ) x) ^ 2 ∂(ν j (i : ℕ))
        ≤ (1 + Arlib.GaussianCooling.varBudget (ε / 2) / (phases K ε p : ℝ)) *
            (∫ x, g K ε p j (i : ℕ) x ∂(ν j (i : ℕ))) ^ 2) :
    VolumeAlgorithm n :=
  VolumeAlgorithm.cousinsVempalaOfApproxMean n (Arlib.Probability.NatRunSpace E)
    (Arlib.Probability.natRunMeasure ν) phases
    Arlib.GaussianCooling.reps
    (fun ε => Arlib.GaussianCooling.varBudget (ε / 2))
    (fun ε => ε / 2)
    (fun ε => ε / (2 + ε))
    (fun K ε p => ε / (2 * (2 + ε) * (phases K ε p : ℝ)))
    (fun K ε p i => Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K i)
    -- `W`: the phase score reads the coordinate of its own (run, phase) pair
    (fun K ε p => Arlib.Probability.natScore (g K ε p))
    -- `med`: the explicit measurable median selector of the `reps ε p` run products
    (fun K ε p ω => Arlib.Probability.medianSel
      fun j : Fin (Arlib.GaussianCooling.reps ε p) =>
        Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K 0 *
          ∏ i : Fin (phases K ε p),
            Arlib.Probability.natScore (g K ε p) (j : ℕ) (i : ℕ) ω)
    -- hreps_pos, hreps : from `Arlib/…/Schedule.lean`
    Arlib.GaussianCooling.reps_pos
    Arlib.GaussianCooling.reps_spec
    -- hbudget0 : the budget is taken at the *inner* accuracy `ε/2`
    (fun ε hε => Arlib.GaussianCooling.varBudget_nonneg (ε / 2) (by linarith))
    -- hinner_pos
    (fun ε hε => by linarith)
    -- hbias_nonneg
    (fun K ε p hε => by
      have h2 : (0 : ℝ) ≤ 2 + ε := by linarith
      have hm : (0 : ℝ) ≤ (phases K ε p : ℝ) := Nat.cast_nonneg _
      exact div_nonneg hε.le (by nlinarith))
    -- hmean_nonneg
    (fun ε hε => div_nonneg hε.le (by linarith))
    -- hmean_lt_one
    (fun ε hε => by rw [div_lt_one (by linarith)]; linarith)
    -- hphaseBudget : `2·m·phaseBias = meanBias` when `m > 0`, and `0 ≤ meanBias` when `m = 0`
    (fun K ε p hε => by
      have h2 : (0 : ℝ) < 2 + ε := by linarith
      rcases Nat.eq_zero_or_pos (phases K ε p) with h0 | hp
      · rw [h0]
        simp only [Nat.cast_zero, mul_zero, zero_mul]
        exact div_nonneg hε.le h2.le
      · have hm : ((phases K ε p : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
        have key : 2 * ((phases K ε p : ℝ)) * (ε / (2 * (2 + ε) * (phases K ε p : ℝ)))
            = ε / (2 + ε) := by
          field_simp
        exact key.le)
    -- hcompose : the split meets the composition with equality
    (fun ε hε => by
      have h2 : (2 : ℝ) + ε ≠ 0 := by positivity
      have key : ε / 2 + ε / (2 + ε) + ε / 2 * (ε / (2 + ε)) = ε := by
        field_simp
        ring
      exact key.le)
    -- hbudget : `varBudget_spec` at the inner accuracy
    (fun ε hε => Arlib.GaussianCooling.varBudget_spec (ε / 2) (by linarith))
    -- hW_meas
    (fun K ε p => Arlib.Probability.measurable_natScore (hg K ε p))
    -- hmed_meas
    (fun K ε p => Arlib.Probability.measurable_medianSel_natRuns (hg K ε p) _ _ _)
    -- hmed
    (fun K ε p ω => Arlib.Probability.isMedian_medianSel_natRuns (g K ε p) _ _ _ ω)
    -- hindep_runs
    (fun K ε p => Arlib.Probability.iIndepFun_natRuns ν (hg K ε p) _ _ _)
    -- hprodLp
    (fun K ε p j => Arlib.Probability.memLp_two_natRunProd ν (hg K ε p) (hgb K ε p) j _)
    -- hchain_pos, hchain_end : from `Arlib/…/Chain.lean`
    (fun K ε p _hε _hp _hp1 _hconv hball hfin i =>
      Arlib.GaussianCooling.chain_pos (hσ K ε p) hball hfin i)
    (fun K ε p _hε _hp _hp1 _hconv _hball _hfin =>
      Arlib.GaussianCooling.chain_end (phases K ε p) (σsq K ε p) K)
    -- hphase_indep
    (fun K ε p _ _ _ _ _ _ j =>
      Arlib.Probability.iIndepFun_natScore_phases ν (hg K ε p) j _)
    -- hphase_mean : transferred to the coordinate law by `integral_natRunCoord`
    (fun K ε p hε hp hp1 hconv hball hfin j i => by
      have hmean : ∫ ω, Arlib.Probability.natScore (g K ε p) j (i : ℕ) ω
            ∂(Arlib.Probability.natRunMeasure ν)
          = ∫ x, g K ε p j (i : ℕ) x ∂(ν j (i : ℕ)) :=
        integral_natRunCoord ν j (i : ℕ) (hg K ε p j (i : ℕ))
      rw [hmean]
      exact hphase_mean K ε p hε hp hp1 hconv hball hfin j i)
    -- hphase_var : same transfer, on both the second moment and the mean
    (fun K ε p hε hp hp1 hconv hball hfin j i => by
      have hsq : ∫ ω, (Arlib.Probability.natScore (g K ε p) j (i : ℕ) ω) ^ 2
            ∂(Arlib.Probability.natRunMeasure ν)
          = ∫ x, (g K ε p j (i : ℕ) x) ^ 2 ∂(ν j (i : ℕ)) :=
        integral_natRunCoord ν j (i : ℕ) ((hg K ε p j (i : ℕ)).pow_const 2)
      have hmean : ∫ ω, Arlib.Probability.natScore (g K ε p) j (i : ℕ) ω
            ∂(Arlib.Probability.natRunMeasure ν)
          = ∫ x, g K ε p j (i : ℕ) x ∂(ν j (i : ℕ)) :=
        integral_natRunCoord ν j (i : ℕ) (hg K ε p j (i : ℕ))
      rw [hsq, hmean]
      exact hphase_var K ε p hε hp hp1 hconv hball hfin j i)

/-- **The two constructors build the *same estimator*** — the prose claim above, checked.

`Ttc.VolumeAlgorithm.cousinsVempalaOfRuns` (equation form of `hphase_mean`) and
`Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMean` (interval form) produce
`VolumeAlgorithm`s with the same coin space, the same coin law and — this lemma — the same
`est`, by `rfl`. So swapping one for the other in a statement about a *run* of the
algorithm (e.g. `Ttc.ttc_runtime_mn4`) changes no distribution and weakens no conclusion;
it changes only which hypothesis the `VolumeAlgorithm.correct` field was proved from.

The equation-form hypotheses are taken as arguments here only because `cousinsVempalaOfRuns`
cannot be applied without them; nothing in the proof uses them (`VolumeAlgorithm.est` does
not depend on the `Prop` fields). -/
theorem VolumeAlgorithm.cousinsVempalaOfRunsApproxMean_est (n : ℕ) (E : Type)
    [MeasurableSpace E] (ν : ℕ → ℕ → Measure E) [∀ j i, IsProbabilityMeasure (ν j i)]
    (phases : Set (Space n) → ℝ → ℝ → ℕ) (σsq : Set (Space n) → ℝ → ℝ → ℕ → ℝ)
    (g : Set (Space n) → ℝ → ℝ → ℕ → ℕ → E → ℝ) (B : ℝ)
    (hσ : ∀ K ε p j, 0 < σsq K ε p j) (hg : ∀ K ε p j i, Measurable (g K ε p j i))
    (hgb : ∀ K ε p j i x, |g K ε p j i x| ≤ B)
    (hmean_eq : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j (i : Fin (phases K ε p)),
      ∫ x, g K ε p j (i : ℕ) x ∂(ν j (i : ℕ)) =
        Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K ((i : ℕ) + 1) /
          Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K (i : ℕ))
    (hvar_eq : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j (i : Fin (phases K ε p)),
      ∫ x, (g K ε p j (i : ℕ) x) ^ 2 ∂(ν j (i : ℕ))
        ≤ (1 + Arlib.GaussianCooling.varBudget ε / (phases K ε p : ℝ)) *
            (∫ x, g K ε p j (i : ℕ) x ∂(ν j (i : ℕ))) ^ 2)
    (hmean_mem : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j (i : Fin (phases K ε p)),
      ∫ x, g K ε p j (i : ℕ) x ∂(ν j (i : ℕ)) ∈
        relErr (ε / (2 * (2 + ε) * (phases K ε p : ℝ)))
          (Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K ((i : ℕ) + 1) /
            Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K (i : ℕ)))
    (hvar_half : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j (i : Fin (phases K ε p)),
      ∫ x, (g K ε p j (i : ℕ) x) ^ 2 ∂(ν j (i : ℕ))
        ≤ (1 + Arlib.GaussianCooling.varBudget (ε / 2) / (phases K ε p : ℝ)) *
            (∫ x, g K ε p j (i : ℕ) x ∂(ν j (i : ℕ))) ^ 2) :
    (VolumeAlgorithm.cousinsVempalaOfRuns n E ν phases σsq g B hσ hg hgb
        hmean_eq hvar_eq).est
      = (VolumeAlgorithm.cousinsVempalaOfRunsApproxMean n E ν phases σsq g B hσ hg hgb
          hmean_mem hvar_half).est :=
  rfl

/-- **Non-vacuity of the `cousinsVempalaOfRunsApproxMean` bundle** (`CLAUDE.md` §11).

The capstone `Ttc.ttc_runtime_mn4` quantifies over *this* bundle, so it needs its own
witness; `Ttc.Box.exists_cvVolAlg_witness` witnesses the equation-carrying bundle of
`cousinsVempalaOfRuns` and does not cover this one.

Exactly as degenerate, and for exactly the same reason, as
`Ttc.VolumeAlgorithm.cousinsVempalaOfRunsWitness`: zero phases, so `Fin (phases K ε p)` is
empty and both remaining hypotheses hold by `Fin.elim0`.  It witnesses *satisfiability of
the hypothesis bundle* and nothing else — in particular it is not evidence that the
sampler debt is dischargeable.  (It survives only because
`Ttc.VolumeAlgorithm.cousinsVempalaOfApproxMean` no longer demands `0 < phases K ε p`; a
witness with `m ≥ 1` is not available here, because `hgb` asks for a **uniform** bound on
the score while the chain ratio `chain(i+1)/chain(i)` is unbounded over the bodies `K` the
hypotheses range over.) -/
noncomputable def VolumeAlgorithm.cousinsVempalaOfRunsApproxMeanWitness (n : ℕ) :
    VolumeAlgorithm n :=
  VolumeAlgorithm.cousinsVempalaOfRunsApproxMean n Unit (fun _ _ => Measure.dirac ())
    (fun _ _ _ => 0) (fun _ _ _ _ => 1) (fun _ _ _ _ _ _ => 1) 1
    (fun _ _ _ _ => one_pos) (fun _ _ _ _ _ => measurable_const)
    (fun _ _ _ _ _ _ => le_of_eq (abs_one))
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)

end Ttc

/-! ## Axiom audit (`CLAUDE.md` §4) -/

#print axioms Ttc.VolumeAlgorithm.cousinsVempalaOfSchedule
#print axioms Ttc.VolumeAlgorithm.cousinsVempalaOfSchedule_discharged
#print axioms Ttc.integral_natRunCoord
#print axioms Ttc.VolumeAlgorithm.cousinsVempalaOfRuns
#print axioms Ttc.VolumeAlgorithm.cousinsVempalaOfRunsWitness
#print axioms Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMean
#print axioms Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMean_est
#print axioms Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMeanWitness
