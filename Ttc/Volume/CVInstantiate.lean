/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CousinsVempala
import Arlib.Convexity.GaussianCooling.Chain
import Arlib.Convexity.GaussianCooling.Schedule

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
| `hphase_mean`  | remains | **the deep one — see below** |
| `hphase_var`   | remains | relative second moment `≤ 1 + κ/m` for the *sampled* score |

Six discharged, **eight remaining**. Six of the eight (`hW_meas`, `hmed_meas`, `hmed`,
`hindep_runs`, `hprodLp`, `hphase_indep`) are admissibility and independence
bookkeeping about whatever concrete `W` and `med` a caller supplies; `hphase_var` is a
transport problem (§5.1 proves the corresponding bound for the *ideal* estimator
unconditionally, `Arlib.GaussianCooling.fixed_var_bound_ratio_indicator`).

**`hphase_mean` is the deep one.** It demands
`∫ W K ε p j i dμ = chain (i+1) / chain i` — *exact* unbiasedness of the phase-`i` score
for the phase ratio. `Arlib.GaussianCooling.chain_ratio_eq` identifies the right-hand side
as a deterministic integral against the phase-`i` density `coolWeight i / chain i`, so
what is missing is a random variable whose law *is* that density. No mixing bound can
deliver this: a Markov chain run for finitely many steps is at total-variation distance
`> 0` from its stationary law, which makes the score's mean the ratio only up to an error,
never on the nose. Closing it requires either a perfect sampler or restating §5.2 with an
approximately-unbiased score. This is where the development actually stops.

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

end Ttc

/-! ## Axiom audit (`CLAUDE.md` §4) -/

#print axioms Ttc.VolumeAlgorithm.cousinsVempalaOfSchedule
#print axioms Ttc.VolumeAlgorithm.cousinsVempalaOfSchedule_discharged
