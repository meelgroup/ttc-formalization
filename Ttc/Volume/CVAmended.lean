/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVInstantiate
import Arlib.Convexity.GaussianCooling.TerminalMoment

/-!
# `Volume/CVAmended`: `cousinsVempalaOfRunsApproxMean` with the four missing inputs as binders

`Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMean` (`Ttc/Volume/CVInstantiate.lean:458`)
is the constructor the capstone `Ttc.ttc_runtime_mn4` runs on, and its two surviving
hypotheses `hphase_mean` and `hphase_var` quantify over **every** `K` with `Convex ℝ K`,
`Metric.ball 0 1 ⊆ K` and `volume K ≠ ⊤` — and over nothing else.  Four things the
sampler-side proof needs are *provably* not available at that generality.  This file adds
them as explicit binders and, having added them, **discharges `hphase_mean` and
`hphase_var` outright** from `Arlib`, so that the amended constructor assumes a per-phase
*total-variation* bound instead of assuming the two conclusions.

Purely additive: nothing under `Ttc/` or `Arlib/` is edited, and
`Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMean` is applied, not modified.

## Which base constructor, and why

`Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMean`.  Three reasons, in order of force:

1. `Arlib/Convexity/GaussianCooling/PhaseFromTV.lean` §4 was written to prove *that*
   constructor's two binders **character for character** — its own docstring quotes them
   verbatim (`PhaseFromTV.lean:19-29`) and says drift becomes a type error at exactly the
   application performed below.  `Arlib` may not import `Ttc`, so this file is where that
   claim is cashed.
2. It is the constructor the capstone runs on (`CVInstantiate.lean:394`); the
   equation-carrying `cousinsVempalaOfRuns` is retained only for `Ttc.cvVolAlg` and
   `Ttc.ttcPoly_volume_estimate_cv`, and its exact-unbiasedness `hphase_mean` is refuted as
   a sampler guarantee by `Arlib.GaussianCooling.exists_tvLe_coolLaw_integral_phaseScore_ne`
   — no TV route can discharge it.
3. Its `hphase_var` is stated at `Arlib.GaussianCooling.varBudget (ε/2)`, which is the
   constant `Arlib.GaussianCooling.hphase_var_of_tvLe_of_flat` concludes at.

## The four inputs, and what each costs

| # | needed for | how it is supplied here |
| --- | --- | --- |
| 1 | `MeasurableSet K` | **not a binder** — the score is `interior K`; see below |
| 2 | a radius `K ⊆ R·Bₙ` | new data `Rad` + new binder `hKrad` |
| 3 | the terminal constant | new binder `hflat` |
| 4 | a uniform score bound | `hgb`, carried unproved, at the new score |

### (1) `MeasurableSet K` is **not** added as a binder, and must not be

Quantified per `K` the way the other binders are, `hKmeas` would read

    ∀ K ε p, 0 < ε → … → volume K ≠ ⊤ → MeasurableSet K

and that proposition is **false**: `MeasurableSet` on `EuclideanSpace ℝ (Fin n)` is Borel,
and `Metric.ball 0 2 ∪ S` with `S` an arbitrary subset of `Metric.sphere 0 2` is convex,
contains the unit ball and has finite volume while being non-Borel
(`Arlib/Convexity/GaussianCooling/PhaseFromTV.lean:44-59`; the same refutation is recorded
at `Ttc/Volume/CousinsVempala.lean:2160-2165`).  A constructor carrying it as a *binder*
would therefore never be applicable — the mandated non-vacuity witness could not be built,
and `phases = 0` would not save it, since `hKmeas` does not sit under the `Fin (phases …)`
quantifier that the degenerate witness empties.  Parking it under
`∀ (_j : ℕ) (_i : Fin (phases K ε p))` would make it vacuously suppliable but then unused.

Item (1) is instead supplied by the **modelling decision** `Arlib` already made
(`CLAUDE.md` §6): the phase score is `Arlib.GaussianCooling.phaseScore … (interior K) i`.
`interior K` is open, hence Borel; it is convex, contains the unit ball and has finite
volume whenever `K` does; and `Convex.addHaar_frontier` makes the frontier null, so
`chain … (interior K) i = chain … K i` and `coolLaw … (interior K) i = coolLaw … K i`
(`Arlib.GaussianCooling.chain_interior`, `coolLaw_interior`).  The chain ratios in the
binders below are therefore written at `K` itself and are unchanged.  What *is* a real
choice, and is stated rather than hidden: the algorithm is modelled as scoring
`x ∈ interior K`, and the sampled law `ν` may charge the frontier, so
`phaseScore … (interior K) i` and `phaseScore … K i` are not interchangeable under `ν`.

### (2) The radius: new data `Rad`, new binder `hKrad`

`Ttc.VolumeAlgorithm.cousinsVempala` and every constructor derived from it expose **no**
radius.  The bound `B = e^{R²/(2σᵢ²)}` on the score
(`Arlib.GaussianCooling.phaseScore_le`) is the only thing that makes the total-variation
transport quantitative, and `coolRatio` is unbounded on an unbounded body
(`Arlib/Convexity/GaussianCooling/PhaseVar.lean`'s scope note;
`PhaseFromTV.lean:98-99`).  So `Rad` and `hKrad` are unavoidable.  They cost nothing in
generality — `Ttc.CV.cvRadius` / `Ttc.CV.subset_closedBall_cvRadius` construct such a
radius from `cousinsVempala`'s own hypotheses — but they cannot be *derived inside* the
existing binder, which is why they are new.

### (3) The terminal constant: new binder `hflat`

`Arlib.GaussianCooling.hterm_not_dischargeable`
(`Arlib/Convexity/GaussianCooling/TerminalMoment.lean:364`) proves that at the terminal
phase the single uniform constant `1 + 2/n` is **FALSE**: for every `n ≥ 1` there is a
variance `s > 0` at which, on `K = B₁` with `phases = 1` and the fixed-rate schedule
`σⱼ² = s(1 + 1/n)ʲ`, the exact-law second moment exceeds `(1 + 2/n)·(mean)²` — and indeed
exceeds `C·(mean)²` for every `C`.  The true terminal ratio is `e^{R²/(2σᵢ²)}`.  The repair
is the flatness binder of `Arlib.GaussianCooling.hphase_var_of_tvLe_of_flat`,

    hflat :  Rad K ε p ² ≤ 2 · σsq K ε p i · log(1 + 2/n)   at   (i : ℕ) + 1 = phases K ε p,

i.e. exactly `e^{R²/(2σᵢ²)} ≤ 1 + 2/n`.  The paper never claims `1 + 2/n` at the terminal
phase (`1409.6011/vol3_journal.tex`, `lem:starting-gauss` gives `e²` and `lem:accuracy`
pays for it separately); collapsing the two-constant accounting into one constant is what
`hflat` buys.

### (4) `hgb`: carried unproved, and the obstruction is inherited, not repaired

`Ttc/Volume/CVInstantiate.lean:629-633` records that `hgb` asks for a bound on the score
**uniform in `K`** while the chain ratio `chain(i+1)/chain(i)` is unbounded over the bodies
the binders range over.  `hgb` feeds `Arlib.Probability.memLp_two_natRunProd` through the
base constructor's `hprodLp` obligation, which is **unguarded** (no `0 < ε`, no convexity,
no `volume K ≠ ⊤` — see `Ttc/Volume/CousinsVempala.lean:2079`), so a `K`-guarded or
`Rad`-derived bound cannot replace it.  It is therefore kept as an explicit binder with the
existing quantifier structure, only restated at the new score (`g` is no longer free data).
Nothing here repairs that obstruction.

## Binder diff against `Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMean`

**Removed** (now derived, not assumed):

* `g` — no longer free data; it is
  `fun K ε p j i x => phaseScore (phases K ε p) (σsq K ε p) (interior K) i (X K ε p j i x)`.
* `hg` — discharged by `Arlib.GaussianCooling.measurable_phaseScore` at
  `isOpen_interior.measurableSet`, composed with `hX`.
* `hphase_mean` — discharged by `Arlib.GaussianCooling.hphase_mean_of_tvLe`.
* `hphase_var` — discharged by `Arlib.GaussianCooling.hphase_var_of_tvLe_of_flat`.

**Kept unchanged**: `n`, `E`, `ν` (+ its instance), `phases`, `σsq`, `B`, `hσ`.

**New data**: `Rad` (item 2), `X` (the sampler, replacing free `g`), `tvErr`.

**New hypotheses**, all quantified exactly as the existing `hphase_mean` / `hphase_var`
binders are — `∀ K ε p, 0 < ε → 0 < p → p < 1 → Convex ℝ K → ball 0 1 ⊆ K → volume K ≠ ⊤ →
∀ j (i : Fin (phases K ε p))` — and copied character for character from the two `Arlib`
theorems they feed:

| binder | why unavoidable |
| --- | --- |
| `hn : 3 ≤ n` | the regime of `Arlib.GaussianCooling.coolLaw_sq_moment_le` |
| `hX` | measurability of the sampler (replaces `hg`) |
| `hgb` | item (4); `CVInstantiate.lean:629-633` |
| `hKrad` | item (2); `PhaseVar.lean`'s scope note |
| `htop` | `tvErr ≠ ⊤`, so `.toReal` means something |
| `hTV` | **the sampler's guarantee.** Conductance/mixing; not proved anywhere here |
| `hslack_mean` | the TV error is small enough for the `Θ(ε/m)` mean tolerance |
| `hrate` | the fixed cooling rate `σᵢ₊₁² = σᵢ²(1 + 1/n)` |
| `hbudget` | `2m ≤ n·varBudget (ε/2)` |
| `hflat` | item (3); `hterm_not_dischargeable` |
| `hslack_var` | the TV error is small enough for the variance budget |

## What this does NOT claim

Nothing here produces a total-variation bound, a conductance bound, a phase count or a
running time; `hTV` is an input.  `hbudget` inherits, unchanged, the obstruction
`Arlib.GaussianCooling.geomSchedule_total_cooling_lt` (`PhaseVar.lean:620`) records: a
fixed-rate schedule meeting `2m ≤ n·varBudget (ε/2)` cools by a total factor `< 1.1`, i.e.
it does not anneal.  This is a *reduction* of the volume oracle to a sampler and a
schedule, not a volume oracle.
-/

namespace Ttc

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ## 1.  A bound the degenerate witness needs

At zero phases every cooling weight is the constant `1` (`coolWeight_of_ge`), so the phase
ratio is `1` and the phase score is an indicator.  This is the only place the *value* of
the score is computed; the constructor itself never touches it. -/

/-- **At `phases = 0` the phase score is an indicator, hence bounded by `1`.**  Used only
by the non-vacuity witness, where `Arlib.GaussianCooling.phaseScore_le` is unavailable
because the witness's `hgb` binder is unguarded in `K`. -/
theorem abs_phaseScore_zero_le_one {n : ℕ} (σsq : ℕ → ℝ) (S : Set (Space n)) (i : ℕ)
    (x : Space n) : |Arlib.GaussianCooling.phaseScore 0 σsq S i x| ≤ 1 := by
  have hratio : Arlib.GaussianCooling.coolRatio 0 σsq i x = 1 := by
    unfold Arlib.GaussianCooling.coolRatio Arlib.GaussianCooling.coolWeight
    simp
  rw [abs_of_nonneg (Arlib.GaussianCooling.phaseScore_nonneg 0 σsq S i x),
    Arlib.GaussianCooling.phaseScore]
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx, hratio]
  · rw [Set.indicator_of_notMem hx]; norm_num

/-! ## 2.  The amended constructor -/

/-- **`Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMean`, amended: the four inputs that
are not suppliable at its generality are explicit binders, and its two sampler hypotheses
are then *proved* rather than assumed.**

Same coin space (`Arlib.Probability.NatRunSpace E`), same coin law
(`Arlib.Probability.natRunMeasure ν`), same median selector, same schedule data, same
accuracy split and hence the same `VolumeAlgorithm` guarantee as the base constructor: the
estimate on `K` at accuracy `ε` and confidence `p` is the median of
`Arlib.GaussianCooling.reps ε p` independent runs of
`chain … 0 · ∏ᵢ phaseScore … (interior K) i (X K ε p j i (ω j i))`, correct within relative
`ε` with probability `≥ 1 − p`.

Read the module docstring for the binder diff and for why each new binder is unavoidable.
In one line each:

* **`hn`, `hrate`** — the fixed-rate regime of `Arlib.GaussianCooling.coolLaw_sq_moment_le`;
* **`Rad`, `hKrad`** — item (2): the interface exposes no radius and
  `e^{R²/(2σᵢ²)}` is the only bound on the score;
* **`X`, `tvErr`, `htop`, `hTV`** — the sampler and its guarantee, the one genuinely open
  input;
* **`hslack_mean`, `hslack_var`** — the TV error is small enough;
* **`hbudget`** — `2m ≤ n·varBudget (ε/2)`, inheriting `geomSchedule_total_cooling_lt`'s
  non-cooling obstruction unchanged;
* **`hflat`** — item (3): `Arlib.GaussianCooling.hterm_not_dischargeable` shows the uniform
  constant `1 + 2/n` is FALSE at the terminal phase, and this is the repair;
* **`hgb`** — item (4): carried unproved, uniform in `K`, restated at the new score.

**Item (1), `MeasurableSet K`, is deliberately *not* a binder** — quantified per `K` it is
the refuted proposition, and the score is `interior K` instead. -/
noncomputable def VolumeAlgorithm.cousinsVempalaOfRunsApproxMeanAmended
    (n : ℕ) (E : Type) [MeasurableSpace E] (ν : ℕ → ℕ → Measure E)
    [∀ j i, IsProbabilityMeasure (ν j i)]
    -- ★ NEW: the dimension regime of the interior-phase variance bound
    (hn : 3 ≤ n)
    -- the schedule data the caller picks (unchanged)
    (phases : Set (Space n) → ℝ → ℝ → ℕ)
    (σsq : Set (Space n) → ℝ → ℝ → ℕ → ℝ)
    -- ★ NEW data: the enclosing radius (item 2)
    (Rad : Set (Space n) → ℝ → ℝ → ℝ)
    -- ★ NEW data: the sampler and its total-variation error, replacing the free score `g`
    (X : Set (Space n) → ℝ → ℝ → ℕ → ℕ → E → Space n)
    (tvErr : Set (Space n) → ℝ → ℝ → ℕ → ℕ → ℝ≥0∞)
    (B : ℝ)
    -- side conditions on that data (NOT among the fourteen); `hg` is now derived
    (hσ : ∀ K ε p j, 0 < σsq K ε p j)
    (hX : ∀ K ε p j i, Measurable (X K ε p j i))
    -- ★ (4) `hgb`, at the new score.  Uniform in `K`; `CVInstantiate.lean:629-633`
    (hgb : ∀ K ε p j i x,
      |Arlib.GaussianCooling.phaseScore (phases K ε p) (σsq K ε p) (interior K) i
        (X K ε p j i x)| ≤ B)
    -- ★ (2) the radius hypothesis
    (hKrad : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (_i : Fin (phases K ε p)),
      K ⊆ Metric.closedBall (0 : Space n) (Rad K ε p))
    -- ★ the sampler's guarantee and its finiteness
    (htop : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ (j : ℕ) (i : Fin (phases K ε p)),
      tvErr K ε p j (i : ℕ) ≠ ⊤)
    (hTV : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ (j : ℕ) (i : Fin (phases K ε p)),
      Arlib.TVLe ((ν j (i : ℕ)).map (X K ε p j (i : ℕ)))
        (Arlib.GaussianCooling.coolLaw (phases K ε p) (σsq K ε p) K (i : ℕ))
        (tvErr K ε p j (i : ℕ)))
    -- ★ the mean-side slack
    (hslack_mean : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ (j : ℕ) (i : Fin (phases K ε p)),
      Real.exp (Rad K ε p ^ 2 / (2 * σsq K ε p (i : ℕ))) * (tvErr K ε p j (i : ℕ)).toReal
        ≤ ε / (2 * (2 + ε) * (phases K ε p : ℝ))
            * (Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K ((i : ℕ) + 1)
                / Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K (i : ℕ)))
    -- ★ the fixed cooling rate and the variance budget
    (hrate : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (i : Fin (phases K ε p)),
      σsq K ε p ((i : ℕ) + 1) = σsq K ε p (i : ℕ) * (1 + 1 / (n : ℝ)))
    (hbudget : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (_i : Fin (phases K ε p)),
      2 * (phases K ε p : ℝ) ≤ (n : ℝ) * Arlib.GaussianCooling.varBudget (ε / 2))
    -- ★ (3) the terminal flatness condition
    (hflat : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (i : Fin (phases K ε p)),
      (i : ℕ) + 1 = phases K ε p →
      Rad K ε p ^ 2 ≤ 2 * σsq K ε p (i : ℕ) * Real.log (1 + 2 / (n : ℝ)))
    -- ★ the variance-side slack
    (hslack_var : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ (j : ℕ) (i : Fin (phases K ε p)),
      (tvErr K ε p j (i : ℕ)).toReal
          * (Real.exp (Rad K ε p ^ 2 / (2 * σsq K ε p (i : ℕ))) ^ 2
              * (1 + 2 * (1 + Arlib.GaussianCooling.varBudget (ε / 2)
                  / (phases K ε p : ℝ))))
        ≤ (Arlib.GaussianCooling.varBudget (ε / 2) / (phases K ε p : ℝ) - 2 / (n : ℝ))
            * (Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K ((i : ℕ) + 1)
                / Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K (i : ℕ)) ^ 2) :
    VolumeAlgorithm n :=
  VolumeAlgorithm.cousinsVempalaOfRunsApproxMean n E ν phases σsq
    -- the score: `g` is no longer free data, it is the interior phase score of the sample
    (fun K ε p j i x =>
      Arlib.GaussianCooling.phaseScore (phases K ε p) (σsq K ε p) (interior K) i
        (X K ε p j i x))
    B hσ
    -- `hg` : discharged — `interior K` is open, hence Borel
    (fun K ε p j i =>
      (Arlib.GaussianCooling.measurable_phaseScore isOpen_interior.measurableSet i).comp
        (hX K ε p j i))
    hgb
    -- `hphase_mean` : discharged from `hTV` by `Arlib`, character for character
    (fun K ε p hε hp hp1 hconv hball hfin j i =>
      Arlib.GaussianCooling.hphase_mean_of_tvLe E phases σsq ν X Rad tvErr hσ hX hKrad htop
        hTV hslack_mean K ε p hε hp hp1 hconv hball hfin j i)
    -- `hphase_var` : discharged from `hTV` and `hflat` by `Arlib`, character for character
    (fun K ε p hε hp hp1 hconv hball hfin j i =>
      Arlib.GaussianCooling.hphase_var_of_tvLe_of_flat E hn phases σsq ν X Rad tvErr hσ hX
        hKrad htop hTV hrate hbudget hflat hslack_var K ε p hε hp hp1 hconv hball hfin j i)

/-! ## 3.  Non-vacuity (`CLAUDE.md` §11) -/

/-- **Non-vacuity of the amended binder bundle**: every argument of
`Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMeanAmended` can be supplied
simultaneously, so its hypotheses do not contradict one another.

**This witness is degenerate, and honestly so.**  It takes `phases = 0`, so
`Fin (phases K ε p)` is empty and every sampler-side binder (`hKrad`, `htop`, `hTV`,
`hslack_mean`, `hrate`, `hbudget`, `hflat`, `hslack_var`) holds by `Fin.elim0`.  Only `hσ`,
`hX` and `hgb` carry content, and `hgb` holds because at zero phases the score is an
indicator (`Ttc.abs_phaseScore_zero_le_one`).  It witnesses *satisfiability of the
hypothesis bundle*, nothing more; it is **not** evidence that the sampler debt is
dischargeable.

It is exactly as degenerate as `Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMeanWitness`
(`Ttc/Volume/CVInstantiate.lean:634`), and for the structural reason recorded at
`Arlib/Convexity/GaussianCooling/PhaseFromTV.lean` §5: `ν` is a *fixed* family of laws
chosen before the input `K` is seen, while `hTV` asks each `ν j i` to be within a small
total variation of `coolLaw … K i` for **every** admissible `K`.  With `phases > 0` that is
the `Ttc` interface's own obstruction, which no amendment on this side repairs.

**One honest difference from the existing witness**: this one is conditional on `3 ≤ n`,
because `hn` is a binder of the amended constructor.  The existing witness is unconditional
in `n`. -/
noncomputable def VolumeAlgorithm.cousinsVempalaOfRunsApproxMeanAmendedWitness
    (n : ℕ) (hn : 3 ≤ n) : VolumeAlgorithm n :=
  VolumeAlgorithm.cousinsVempalaOfRunsApproxMeanAmended n Unit
    (fun _ _ => Measure.dirac ()) hn
    -- phases, σsq, Rad, X, tvErr, B
    (fun _ _ _ => 0) (fun _ _ _ _ => 1) (fun _ _ _ => 1) (fun _ _ _ _ _ _ => 0)
    (fun _ _ _ _ _ => 0) 1
    -- hσ, hX
    (fun _ _ _ _ => one_pos) (fun _ _ _ _ _ => measurable_const)
    -- hgb : at zero phases the score is an indicator
    (fun _ _ _ _ _ _ => abs_phaseScore_zero_le_one _ _ _ _)
    -- hKrad, htop, hTV, hslack_mean, hrate, hbudget, hflat, hslack_var : all `Fin 0`-vacuous
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)

end Ttc

/-! ## Axiom audit (`CLAUDE.md` §4)

Every declaration above must depend on exactly `[propext, Classical.choice, Quot.sound]`. -/

#print axioms Ttc.abs_phaseScore_zero_le_one
#print axioms Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMeanAmended
#print axioms Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMeanAmendedWitness
