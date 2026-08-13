/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVAmended
import Arlib.Convexity.GaussianCooling.WarmSpeedy
import Arlib.Convexity.GaussianCooling.InteriorBridge

/-!
# `Volume/CVSampler`: the speedy-walk sampler, wired into the volume algorithm's `hTV`

`Ttc/Volume/CVAmended.lean:246` carries a hypothesis `hTV`, described at
`Ttc/Volume/CousinsVempala.lean:2530` as "the whole mathematical debt":

```
hTV : ∀ K ε p, 0 < ε → 0 < p → p < 1 → Convex ℝ K → ball 0 1 ⊆ K → volume K ≠ ⊤ →
  ∀ (j : ℕ) (i : Fin (phases K ε p)),
  Arlib.TVLe ((ν j i).map (X K ε p j i))
    (Arlib.GaussianCooling.coolLaw (phases K ε p) (σsq K ε p) K i) (tvErr K ε p j i)
```

**This file discharges it** (`hTV_cvLaw`, §6) and feeds the result to the amended
constructor (`Ttc.VolumeAlgorithm.cousinsVempalaOfSpeedySampler`, §7), leaving the
interface's *other* binders — `hgb`, `hKrad`, `hslack_mean`, `hbudget`, `hflat`,
`hslack_var` — untouched, and leaving **one** sampler input open, named below.

## What the sampler is

`phaseLaw K δ s mu0 t` (§1) is the honest Cousins–Vempala composite: `t` steps of the lazy
speedy Metropolis–Gaussian walk from `mu0`, then condition on the shrunken body `c·K` at
`c = 1 − 1/(2n)`, rescale by `c⁻¹`, reweight by `speedyAcceptReal c s`, renormalise.  It is
written character for character as the conclusion of
`Arlib.GaussianCooling.tvLe_speedyRejection_coolLaw_of_mixing`, so the transports below are
`rfl` on the sampler side.  `cvPhaseLaw` runs it on `interior K` from `phaseStart`.

## Two things that had to be got right

**Measurability.**  The interface deliberately carries no `MeasurableSet K` binder, and
cannot: `∀ K, Convex ℝ K → … → MeasurableSet K` is *false*
(`Ttc/Volume/CousinsVempala.lean:819`).  The sampler therefore runs on `interior K`, which
`Arlib.GaussianCooling.interior_admissible` shows is Borel, convex, contains the unit ball
and has the same finite nonzero volume; and the target is transported back to `K` by
`Arlib.GaussianCooling.coolLaw_interior`, an **equality** of measures, not an estimate.

**The coin space.**  `Ttc/Volume/CVAmended.lean:318-323` and
`Arlib/Convexity/GaussianCooling/PhaseFromTV.lean` §5 record, in prose, what they take to be
a structural obstruction: `ν` is a *fixed* family of laws chosen before the input `K` is
seen, while `hTV` asks `(ν j i).map (X K ε p j i)` to be close to `coolLaw … K i` for
**every** admissible `K`.  **That is not an obstruction, and §5 dissolves it.**  Take the
coin space to be `CoinSpace n = (Set (Space n) × ℝ × ℝ) → Space n`, the coin law to be the
product measure `MeasureTheory.Measure.infinitePi` of the per-input sampler laws — which
exists for an *arbitrary* index type, with no countability and no standard-Borel hypothesis
— and the sampler `X K ε p j i` to be the projection onto the `(K, ε, p)` coordinate.  Then
`Measure.infinitePi_map_eval` gives `(ν j i).map (X K ε p j i) = ` the phase law at that
input, exactly.  Operationally this says only that the algorithm draws fresh randomness for
the input it is handed.  No prose claim in the repository is contradicted by a *theorem*;
what is contradicted is the prose.

`Measure.infinitePi` needs every factor to be a probability measure, including at inputs
that are not admissible bodies at all, so the factors are wrapped in `probOrDirac` — a `def`
whose promised identity is proved by `probOrDirac_eq`, never left to the name.

## The residual: the phase-`0` warm start

`Arlib/Convexity/GaussianCooling/WarmSpeedy.lean` discharges the warm start of phase `i+1`
from phase `i` (`isWarm_condOn_coolLaw_ellGaussianProb`, constant `2e`, `n`-free).  Phase `0`
has no predecessor, and **nothing in this repository warms it**.  It is carried, explicitly,
as `hwarm` in `prob_and_tvLe_cvPhaseLaw`, `hTV_cvLaw` and
`cousinsVempalaOfSpeedySampler`.  This is the single open sampler input.

Two further honest caveats, inherited from `WarmSpeedy.lean` and not repaired here:

1. the start of phase `i+1` is phase `i`'s **exact** law conditioned on `c·K`, not the
   previous phase's sampler output — composing the per-phase errors across phases is a
   separate additive bookkeeping step, not done here.  It is consistent with the interface,
   which models the phases as independent draws (`Arlib.Probability.NatRunSpace`);
2. the conditioning on `c·K` is a genuine modification of the algorithm's start; it costs at
   most `2` expected redraws (`half_le_coolLaw_smul_set`) and is not optional
   (`Arlib/MarkovChains/Continuous/EllFloor.lean`).

## The regime, and what it costs — read this before believing the wiring is free

The mixing bound behind everything is
`Arlib.mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit`, whose binders are
carried unchanged and are all supplied here as explicit hypotheses:

| binder | shape |
| --- | --- |
| `hn` | `21 ≤ n` |
| `hδn` | `δ ≤ 1/(2n)` — the rejection routine's shrink slack |
| `hδσ` | `δ ≤ σⱼ/(8√n)` — the conductance bound; **neither implies the other** |
| `hRadσ` | `R ≤ 2σⱼ√n` at **every** phase `j` |
| `hacc32` | `acc ≤ 1/32`, so `tvErr = 64·acc`; non-trivial only for `acc < 1/64` |
| `hsteps` | the explicit `Θ(σ²n(log M + 2log(1/acc))/(δ log 2)²)` deadline |

**`hRadσ` at the coldest phase is the sharp restriction, and it is worth stating plainly.**
`σⱼ²` is increasing, so `R ≤ 2σⱼ√n` binds at `j = 0`: it demands `σ²₀ ≥ R²/(4n)`.  A
Gaussian-cooling *volume* algorithm, however, must start **cold**, `σ²₀ ≲ 1/n`, or else
`chain 0 = ∫_K e^{−‖x‖²/(2σ²₀)}` is not the known Gaussian integral but `vol K` itself and
the telescope is circular — this is exactly the point of
`Arlib/Convexity/GaussianCooling/ColdStart.lean`.  The two together force
`R ≤ 2σ₀√n ≤ 2√(1/n)·√n = 2`, i.e. `K ⊆ 2·Bₙ`.  So this sampler's regime and a non-circular
cold start are compatible **only on bodies with sandwiching ratio at most `2`**.  (Arithmetic
observation about the two stated binders; it is not itself a machine-checked theorem here,
and it is a limitation of *this* conductance bound's `R ≤ 2σ√n` hypothesis, not of
Cousins–Vempala.)

The accuracy side is *not* an obstruction: `hslack_mean` needs
`e^{R²/(2σᵢ²)}·tvErr` small, and at `σᵢ² ≥ R²/(4n)` the prefactor is at most `e^{2n}`, so
`acc = e^{−Θ(n)}` suffices — and `acc` enters the step count only through `log(1/acc)`, i.e.
at polynomial cost.  (Again an arithmetic observation, not proved here.)

## Why the *other* consumer, `cousinsVempalaOfSampler`, is not fed — the exact quantifier

`Ttc.VolumeAlgorithm.cousinsVempalaOfSampler` (`Ttc/Volume/CousinsVempala.lean:2194`) carries
its own `hTV` at `:2235`, and it is **not** the same proposition:

```
hTV : … → ∀ j i,   -- `i : ℕ`, UNBOUNDED — not `i : Fin (phases K ε p)`
  Arlib.TVLe (μ.map (X K ε p j i))
    (coolLaw (phases K ε p) (σsq K ε p) (interior K) i) (tvErr K ε p)
```

At `i ≥ phases K ε p` the cooling weight is the constant `1`
(`Arlib.GaussianCooling.coolWeight_of_ge`) and `coolLaw … i` is the **uniform** law on
`interior K`, not a Gaussian one; the identification the whole route runs through,
`Arlib.GaussianCooling.coolLaw_eq_condOn_gaussianRestrict`, carries `i < m` and is *false*
without it (`Arlib/Convexity/GaussianCooling/PhaseSamplerTV.lean` §1 says so explicitly).
And `tvErr K ε p` there has no `i` index, so those terminal indices cannot be given a
trivial (`≥ 1`) error while the interior ones get a small one.  Discharging that `hTV` would
need a sampler for the **uniform** law on the body — a different theorem, not in this
repository.  The amended constructor quantifies `i : Fin (phases K ε p)`, which is exactly
the `i < m` guard the identification needs, and that is the one fed here.

## What is proved here

| name | content |
| --- | --- |
| `phaseLaw`, `phaseStart`, `cvPhaseLaw` | the composite, as a law |
| `tvLe_cvPhaseLaw_succ` | `hTV`'s body at a cooled phase, warm start **discharged** |
| `tvLe_cvPhaseLaw_zero` | `hTV`'s body at phase `0`, warm start assumed |
| `isProbabilityMeasure_phaseLaw` | the composite is a probability measure — `TVLe` alone does not force this |
| `isProbabilityMeasure_cvPhaseLaw_succ` / `_zero` | the same, under the mixing binders |
| `prob_and_tvLe_cvPhaseLaw` | both, at every phase of one input |
| `probOrDirac`, `probOrDirac_eq` | the total-ising wrapper and its promised identity |
| `coinMeasure`, `coinX`, `map_coinX`, `tvLe_map_coinX` | the coin space and its marginal |
| `hTV_cvLaw` | **`hTV` itself, discharged** |
| `Ttc.VolumeAlgorithm.cousinsVempalaOfSpeedySampler` | the amended constructor, `hTV`-free |
| `prob_and_tvLe_cvPhaseLaw_witness` | non-vacuity, **non-degenerate**: `i = 1`, `σ²₀ ≠ σ²₁`, error `1/2`, law a probability measure |
| `Ttc.VolumeAlgorithm.cousinsVempalaOfSpeedySamplerWitness` | non-vacuity of the constructor, degenerate (`phases = 0`) |

## What has no witness here, and is flagged

* `hTV_cvLaw` states its hypotheses **unguarded in `K`** — a radius function valid for every
  admissible body, and a phase-`0` warm start for every admissible body.  No witness for that
  bundle is given.  (`cousinsVempalaOfSpeedySampler` guards the same hypotheses by
  `Fin (phases K ε p)`, exactly as the amended constructor guards its own, and *is*
  witnessed.)
* The constructor's witness is degenerate at `phases = 0`.  A `phases > 0` witness would have
  to meet `hbudget` (`2m ≤ n·varBudget (ε/2)`), which
  `Arlib.GaussianCooling.geomSchedule_total_cooling_lt` shows forces total cooling `< 1.1`.
  That obstruction is the interface's, is inherited unchanged, and is **not** touched here.

Every declaration below is a `theorem` or a `def`; there is no `axiom`, no `sorry` and no
`native_decide`.
-/

namespace Ttc.CVSampler

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

variable {n : ℕ}

/-! ## 1.  The composite the per-phase theorem is about -/

/-- **One phase of the Cousins–Vempala sampler, as a law.**

`t` steps of the lazy speedy Metropolis–Gaussian walk on `K` at step `δ` and variance `s`,
started from `mu0`; then the rejection routine at shrink factor `c = 1 − 1/(2n)`:
condition on `c·K`, rescale by `c⁻¹`, reweight by `speedyAcceptReal c s`, renormalise.

The expression is copied character for character from the conclusion of
`Arlib.GaussianCooling.tvLe_speedyRejection_coolLaw_of_mixing`, so
`phaseLaw_eq_of_mixing` below is `rfl`. -/
noncomputable def phaseLaw (K : Set (Space n)) (δ s : ℝ) (mu0 : Measure (Space n)) (t : ℕ) :
    Measure (Space n) :=
  Arlib.condOn
    ((Measure.map (fun x : Space n => (1 - 1 / (2 * (n : ℝ)))⁻¹ • x)
        (Arlib.condOn
          (Arlib.MarkovChains.iterate
            (Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyMetropolisGaussian K δ s))
            mu0 t)
          ((1 - 1 / (2 * (n : ℝ))) • K))).withDensity
      fun v => ENNReal.ofReal
        (Arlib.MarkovChains.speedyAcceptReal (1 - 1 / (2 * (n : ℝ))) s v))
    Set.univ

/-- **The start of phase `i`.**  Phase `0` starts from the caller's `mu0`; phase `i+1` starts
from phase `i`'s exact law conditioned on the shrunken body, which is what
`Arlib.GaussianCooling.isWarm_condOn_coolLaw_ellGaussianProb` warms. -/
noncomputable def phaseStart (m : ℕ) (σsq : ℕ → ℝ) (K : Set (Space n))
    (mu0 : Measure (Space n)) : ℕ → Measure (Space n)
  | 0 => mu0
  | i + 1 =>
    Arlib.condOn (Arlib.GaussianCooling.coolLaw m σsq (interior K) i)
      ((1 - 1 / (2 * (n : ℝ))) • interior K)

/-- **The law of the phase-`i` sample**, run on `interior K` (which is Borel, while `K` need
not be) and started from `phaseStart`. -/
noncomputable def cvPhaseLaw (m : ℕ) (σsq : ℕ → ℝ) (K : Set (Space n)) (δ : ℝ)
    (mu0 : Measure (Space n)) (i t : ℕ) : Measure (Space n) :=
  phaseLaw (interior K) δ (σsq i) (phaseStart m σsq K mu0 i) t

/-! ## 2.  The per-phase total-variation guarantee -/

/-- **`hTV`'s body at a phase `i + 1`, on `K`, with the warm start discharged.**

`Arlib.GaussianCooling.tvLe_speedyRejection_coolLaw_of_mixing_warmStart` run on `interior K`
— which `Arlib.GaussianCooling.interior_admissible` shows is measurable, convex and contains
the unit ball — and transported to `K` by `Arlib.GaussianCooling.coolLaw_interior`, which is
an *equality* of measures.

No `MeasurableSet K` binder: there is none, and there cannot be one
(`Ttc/Volume/CousinsVempala.lean:819`). -/
theorem tvLe_cvPhaseLaw_succ (hn : 21 ≤ n) {m : ℕ} {σsq : ℕ → ℝ}
    (hσ : ∀ j, 0 < σsq j) {σ δ R : ℝ} (hσpos : 0 < σ) (hδ : 0 < δ)
    (hδσ : δ ≤ σ / (8 * Real.sqrt n)) (hδn : δ ≤ 1 / (2 * (n : ℝ)))
    {K : Set (Space n)} (hKc : Convex ℝ K) (hball : ball (0 : Space n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRσ : R ≤ 2 * σ * Real.sqrt n) {i : ℕ} (hi : i + 1 < m) (hσsq : σsq (i + 1) = σ ^ 2)
    {cc : ℝ} (hcc1 : 1 ≤ cc) (hcc : cc ≤ 1 + 2 / (n : ℝ)) (hsched : σsq (i + 1) = cc * σsq i)
    {mu0 : Measure (Space n)} {eps : ℝ} (heps0 : 0 < eps) (heps32 : eps ≤ 1 / 32)
    {t : ℕ} (ht : 4 * 640 ^ 2 * σ ^ 2 * (n : ℝ)
        * (Real.log (2 * Real.exp 1) + 2 * Real.log (1 / eps)) / (δ * Real.log 2) ^ 2 + 1
      ≤ (t : ℝ)) :
    Arlib.TVLe (cvPhaseLaw m σsq K δ mu0 (i + 1) t)
      (Arlib.GaussianCooling.coolLaw m σsq K (i + 1)) (64 * ENNReal.ofReal eps) := by
  obtain ⟨hKm', hKc', hball', _, hfin'⟩ :=
    Arlib.GaussianCooling.interior_admissible hKc hball hfin
  have h := Arlib.GaussianCooling.tvLe_speedyRejection_coolLaw_of_mixing_warmStart hn hσ hσpos
    hδ hδσ hδn hKm' hKc' hball' hfin' hR (fun x hx => hKR x (interior_subset hx)) hRσ hi hσsq
    hcc1 hcc hsched heps0 heps32 ht
  rwa [Arlib.GaussianCooling.coolLaw_interior m σsq hKc (i + 1)] at h

/-- **`hTV`'s body at phase `0`, on `K`, with the warm start *assumed*.**

`Arlib.GaussianCooling.tvLe_speedyRejection_coolLaw_of_mixing` run on `interior K` and
transported by `coolLaw_interior`.  Unlike `tvLe_cvPhaseLaw_succ` this carries `hwarm`: the
warm start of phase `i+1` comes from phase `i`, and phase `0` has no predecessor.  This is
the one hypothesis of the per-phase chain that is not discharged anywhere in this
repository. -/
theorem tvLe_cvPhaseLaw_zero (hn : 21 ≤ n) {m : ℕ} {σsq : ℕ → ℝ}
    (hσ : ∀ j, 0 < σsq j) {σ δ R : ℝ} (hσpos : 0 < σ) (hδ : 0 < δ)
    (hδσ : δ ≤ σ / (8 * Real.sqrt n)) (hδn : δ ≤ 1 / (2 * (n : ℝ)))
    {K : Set (Space n)} (hKc : Convex ℝ K) (hball : ball (0 : Space n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRσ : R ≤ 2 * σ * Real.sqrt n) (hm : 0 < m) (hσsq : σsq 0 = σ ^ 2)
    {mu0 : Measure (Space n)} [IsProbabilityMeasure mu0] {M eps : ℝ} (hM : 1 ≤ M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu0
      (Arlib.MarkovChains.ellGaussianProb (interior K) δ (σ ^ 2)))
    (heps0 : 0 < eps) (heps32 : eps ≤ 1 / 32)
    {t : ℕ} (ht : 4 * 640 ^ 2 * σ ^ 2 * (n : ℝ) * (Real.log M + 2 * Real.log (1 / eps))
      / (δ * Real.log 2) ^ 2 + 1 ≤ (t : ℝ)) :
    Arlib.TVLe (cvPhaseLaw m σsq K δ mu0 0 t)
      (Arlib.GaussianCooling.coolLaw m σsq K 0) (64 * ENNReal.ofReal eps) := by
  obtain ⟨hKm', hKc', hball', _, hfin'⟩ :=
    Arlib.GaussianCooling.interior_admissible hKc hball hfin
  have h := Arlib.GaussianCooling.tvLe_speedyRejection_coolLaw_of_mixing hn hσ hσpos hδ hδσ
    hδn hKm' hKc' hball' hfin' hR (fun x hx => hKR x (interior_subset hx)) hRσ hm hσsq hM
    hwarm heps0 heps32 ht
  rwa [Arlib.GaussianCooling.coolLaw_interior m σsq hKc 0] at h

/-! ## 3.  The composite really is a sampler: it is a probability measure -/

/-- **`phaseLaw` is a probability measure.**

Nothing in `Arlib.TVLe` forces this — `TVLe 0 ν ε` holds for the zero measure — so it is
proved rather than assumed.  Three normalisations have to be shown non-degenerate:

* `Arlib.condOn P (c·K)`: the chain's law puts at least `1/4` of its mass on the shrunken
  body (`Arlib.MarkovChains.quarter_le_shrunken_mass`), which is where the mixing hypothesis
  is used and why `eps ≤ 1/4` is a binder;
* the rescaling `x ↦ c⁻¹ • x`, a pushforward, which is harmless;
* the acceptance reweighting, whose total mass lies in `(0, 1]`: at most `1` because
  `speedyAcceptReal ≤ 1` for `c² ≤ 1`, and nonzero because `speedyAcceptReal > 0`
  *pointwise* (`Arlib.MarkovChains.speedyAcceptReal_pos`) — there is no uniform positive
  floor, so the argument goes through `lintegral_eq_zero_iff`, not through a constant. -/
theorem isProbabilityMeasure_phaseLaw (hn : 1 ≤ n) {K : Set (Space n)}
    (hKm : MeasurableSet K) (hKc : Convex ℝ K) (hball : ball (0 : Space n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) {δ s : ℝ} (hδ : 0 < δ) (hδn : δ ≤ 1 / (2 * (n : ℝ))) (hs : 0 < s)
    (mu0 : Measure (Space n)) [IsProbabilityMeasure mu0] (t : ℕ) {eps : ℝ≥0∞}
    (hmix : Arlib.TVLe
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyMetropolisGaussian K δ s)) mu0 t)
      (Arlib.MarkovChains.ellGaussianProb K δ s) eps)
    (heps : eps ≤ ENNReal.ofReal (1 / 4)) :
    IsProbabilityMeasure (phaseLaw K δ s mu0 t) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hhalf : 1 / (2 * (n : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hc0 : (0 : ℝ) < 1 - 1 / (2 * (n : ℝ)) := by linarith
  have hc2 : (1 - 1 / (2 * (n : ℝ))) ^ 2 ≤ 1 := Arlib.MarkovChains.sq_shrink_le_one hn
  -- the chain's law charges the shrunken body
  have hquarter : ENNReal.ofReal (1 / 4)
      ≤ (Arlib.MarkovChains.iterate
          (Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyMetropolisGaussian K δ s)) mu0 t)
        ((1 - 1 / (2 * (n : ℝ))) • K) := by
    refine Arlib.MarkovChains.quarter_le_shrunken_mass hn hKm hKc hball hfin hδ hδn hs ?_ heps
    rwa [← Arlib.GaussianCooling.ellGaussianProb_eq_condOn]
  have hpos4 : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / 4) := by simp
  have hne0 := (lt_of_lt_of_le hpos4 hquarter).ne'
  haveI hcond : IsProbabilityMeasure
      (Arlib.condOn
        (Arlib.MarkovChains.iterate
          (Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyMetropolisGaussian K δ s)) mu0 t)
        ((1 - 1 / (2 * (n : ℝ))) • K)) :=
    Arlib.isProbabilityMeasure_condOn _ hne0 (measure_ne_top _ _)
  -- the rescaling
  have hsmul : Measurable fun x : Space n => (1 - 1 / (2 * (n : ℝ)))⁻¹ • x :=
    measurable_const_smul _
  haveI hmap : IsProbabilityMeasure
      (Measure.map (fun x : Space n => (1 - 1 / (2 * (n : ℝ)))⁻¹ • x)
        (Arlib.condOn
          (Arlib.MarkovChains.iterate
            (Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyMetropolisGaussian K δ s)) mu0 t)
          ((1 - 1 / (2 * (n : ℝ))) • K))) :=
    Measure.isProbabilityMeasure_map hsmul.aemeasurable
  -- the acceptance reweighting
  set Q := Measure.map (fun x : Space n => (1 - 1 / (2 * (n : ℝ)))⁻¹ • x)
    (Arlib.condOn
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyMetropolisGaussian K δ s)) mu0 t)
      ((1 - 1 / (2 * (n : ℝ))) • K)) with hQdef
  set f : Space n → ℝ≥0∞ := fun v => ENNReal.ofReal
    (Arlib.MarkovChains.speedyAcceptReal (1 - 1 / (2 * (n : ℝ))) s v) with hfdef
  have hfmeas : Measurable f :=
    ENNReal.measurable_ofReal.comp (Arlib.MarkovChains.measurable_speedyAcceptReal _ _)
  have hmass : (Q.withDensity f) Set.univ = ∫⁻ v, f v ∂Q := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hle : (Q.withDensity f) Set.univ ≤ 1 := by
    rw [hmass]
    calc ∫⁻ v, f v ∂Q ≤ ∫⁻ _, 1 ∂Q :=
          lintegral_mono fun v => ENNReal.ofReal_le_one.2
            (Arlib.MarkovChains.speedyAcceptReal_le_one hs hc2 v)
      _ = 1 := by simp
  have hfne : ∀ v, f v ≠ 0 := fun v =>
    (ENNReal.ofReal_pos.2 (Arlib.MarkovChains.speedyAcceptReal_pos _ _ v)).ne'
  have hne : (Q.withDensity f) Set.univ ≠ 0 := by
    rw [hmass]
    intro h
    have h0 : f =ᵐ[Q] 0 := (lintegral_eq_zero_iff hfmeas).1 h
    have hfalse : ∀ᵐ v ∂Q, False := by
      refine h0.mono fun v hv => ?_
      simp only [Pi.zero_apply] at hv
      exact hfne v hv
    rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at hfalse
    have h1 : Q Set.univ = 1 := measure_univ
    rw [hfalse] at h1
    simp at h1
  exact Arlib.isProbabilityMeasure_condOn _ hne (ne_top_of_le_ne_top ENNReal.one_ne_top hle)

/-- **The phase-`i+1` sampler is a probability measure**, under exactly the binders of
`tvLe_cvPhaseLaw_succ`.  The mixing bound is re-derived here (rather than extracted from
`tvLe_cvPhaseLaw_succ`, which does not expose it) because
`isProbabilityMeasure_phaseLaw` needs the *chain's* law, not the post-processed one. -/
theorem isProbabilityMeasure_cvPhaseLaw_succ (hn : 21 ≤ n) {m : ℕ} {σsq : ℕ → ℝ}
    (hσ : ∀ j, 0 < σsq j) {σ δ R : ℝ} (hσpos : 0 < σ) (hδ : 0 < δ)
    (hδσ : δ ≤ σ / (8 * Real.sqrt n)) (hδn : δ ≤ 1 / (2 * (n : ℝ)))
    {K : Set (Space n)} (hKc : Convex ℝ K) (hball : ball (0 : Space n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRσ : R ≤ 2 * σ * Real.sqrt n) {i : ℕ} (hi : i + 1 < m) (hσsq : σsq (i + 1) = σ ^ 2)
    {cc : ℝ} (hcc1 : 1 ≤ cc) (hcc : cc ≤ 1 + 2 / (n : ℝ)) (hsched : σsq (i + 1) = cc * σsq i)
    {mu0 : Measure (Space n)} {eps : ℝ} (heps0 : 0 < eps) (heps32 : eps ≤ 1 / 32)
    {t : ℕ} (ht : 4 * 640 ^ 2 * σ ^ 2 * (n : ℝ)
        * (Real.log (2 * Real.exp 1) + 2 * Real.log (1 / eps)) / (δ * Real.log 2) ^ 2 + 1
      ≤ (t : ℝ)) :
    IsProbabilityMeasure (cvPhaseLaw m σsq K δ mu0 (i + 1) t) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hKm', hKc', hball', hK0', hfin'⟩ :=
    Arlib.GaussianCooling.interior_admissible hKc hball hfin
  haveI hprob : IsProbabilityMeasure
      (Arlib.GaussianCooling.coolLaw m σsq (interior K) i) :=
    Arlib.GaussianCooling.coolLaw_isProbabilityMeasure hσ hball' hfin' i
  have hmass : ENNReal.ofReal (1 / 2)
      ≤ Arlib.GaussianCooling.coolLaw m σsq (interior K) i
        ((1 - 1 / (2 * (n : ℝ))) • interior K) :=
    Arlib.GaussianCooling.half_le_coolLaw_smul_set hn1 hσ hKm' hKc' hball' hfin'
      (Nat.lt_of_succ_lt hi)
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / 2) := by simp
  haveI hmu0 : IsProbabilityMeasure
      (Arlib.condOn (Arlib.GaussianCooling.coolLaw m σsq (interior K) i)
        ((1 - 1 / (2 * (n : ℝ))) • interior K)) :=
    Arlib.isProbabilityMeasure_condOn _ (lt_of_lt_of_le hpos hmass).ne' (measure_ne_top _ _)
  have hwarm := Arlib.GaussianCooling.isWarm_condOn_coolLaw_ellGaussianProb hn1 hσ hKm' hKc'
    hball' hfin' hi hcc1 hcc hsched hδ hδn
  rw [hσsq] at hwarm
  have hM : (1 : ℝ) ≤ 2 * Real.exp 1 := by
    nlinarith [Real.one_le_exp (zero_le_one : (0 : ℝ) ≤ 1)]
  have hmix := Arlib.mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit hn hσpos hδ hδσ
    hKm' hKc' hK0' hR (fun x hx => hKR x (interior_subset hx)) hRσ hM hwarm heps0
    (by linarith : eps ≤ 1) ht
  rw [Arlib.MarkovChains.mixesWithin_iff, ← hσsq] at hmix
  exact isProbabilityMeasure_phaseLaw hn1 hKm' hKc' hball' hfin' hδ hδn (hσ (i + 1))
    (Arlib.condOn (Arlib.GaussianCooling.coolLaw m σsq (interior K) i)
      ((1 - 1 / (2 * (n : ℝ))) • interior K)) t hmix
    (ENNReal.ofReal_le_ofReal (by linarith))

/-- **The phase-`0` sampler is a probability measure**, under exactly the binders of
`tvLe_cvPhaseLaw_zero` (the warm start included). -/
theorem isProbabilityMeasure_cvPhaseLaw_zero (hn : 21 ≤ n) {m : ℕ} {σsq : ℕ → ℝ}
    (hσ : ∀ j, 0 < σsq j) {σ δ R : ℝ} (hσpos : 0 < σ) (hδ : 0 < δ)
    (hδσ : δ ≤ σ / (8 * Real.sqrt n)) (hδn : δ ≤ 1 / (2 * (n : ℝ)))
    {K : Set (Space n)} (hKc : Convex ℝ K) (hball : ball (0 : Space n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRσ : R ≤ 2 * σ * Real.sqrt n) (hσsq : σsq 0 = σ ^ 2)
    {mu0 : Measure (Space n)} [IsProbabilityMeasure mu0] {M eps : ℝ} (hM : 1 ≤ M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu0
      (Arlib.MarkovChains.ellGaussianProb (interior K) δ (σ ^ 2)))
    (heps0 : 0 < eps) (heps32 : eps ≤ 1 / 32)
    {t : ℕ} (ht : 4 * 640 ^ 2 * σ ^ 2 * (n : ℝ) * (Real.log M + 2 * Real.log (1 / eps))
      / (δ * Real.log 2) ^ 2 + 1 ≤ (t : ℝ)) :
    IsProbabilityMeasure (cvPhaseLaw m σsq K δ mu0 0 t) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hKm', hKc', hball', hK0', hfin'⟩ :=
    Arlib.GaussianCooling.interior_admissible hKc hball hfin
  have hmix := Arlib.mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit hn hσpos hδ hδσ
    hKm' hKc' hK0' hR (fun x hx => hKR x (interior_subset hx)) hRσ hM hwarm heps0
    (by linarith : eps ≤ 1) ht
  rw [Arlib.MarkovChains.mixesWithin_iff, ← hσsq] at hmix
  exact isProbabilityMeasure_phaseLaw hn1 hKm' hKc' hball' hfin' hδ hδn (hσ 0)
    mu0 t hmix (ENNReal.ofReal_le_ofReal (by linarith))

/-! ## 4.  Every phase at once -/

/-- **The sampler's guarantee at every phase of one input**, packaging
`tvLe_cvPhaseLaw_zero`/`_succ` and `isProbabilityMeasure_cvPhaseLaw_zero`/`_succ`.

The variance at phase `i` is `σ² = σsq i`, so the two regime binders are written with
`Real.sqrt (σsq i)`; the step count is stated once, at the *phase-`0`* warmness constant `M`,
and `2e ≤ M` makes it cover the interior phases too, whose constant is `2e`.

`hwarm` is the only hypothesis here that is not discharged anywhere in this repository. -/
theorem prob_and_tvLe_cvPhaseLaw (hn : 21 ≤ n) {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    {δ R M eps : ℝ} (hδ : 0 < δ) (hδn : δ ≤ 1 / (2 * (n : ℝ)))
    (hδσ : ∀ j, δ ≤ Real.sqrt (σsq j) / (8 * Real.sqrt n))
    {K : Set (Space n)} (hKc : Convex ℝ K) (hball : ball (0 : Space n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRσ : ∀ j, R ≤ 2 * Real.sqrt (σsq j) * Real.sqrt n)
    {cc : ℝ} (hcc1 : 1 ≤ cc) (hcc2 : cc ≤ 1 + 2 / (n : ℝ))
    (hrate : ∀ j, σsq (j + 1) = cc * σsq j)
    {mu0 : Measure (Space n)} [IsProbabilityMeasure mu0] (hM : 2 * Real.exp 1 ≤ M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu0
      (Arlib.MarkovChains.ellGaussianProb (interior K) δ (σsq 0)))
    (heps0 : 0 < eps) (heps32 : eps ≤ 1 / 32) {t : ℕ → ℕ}
    (ht : ∀ i, 4 * 640 ^ 2 * σsq i * (n : ℝ) * (Real.log M + 2 * Real.log (1 / eps))
      / (δ * Real.log 2) ^ 2 + 1 ≤ (t i : ℝ))
    {i : ℕ} (hi : i < m) :
    IsProbabilityMeasure (cvPhaseLaw m σsq K δ mu0 i (t i)) ∧
      Arlib.TVLe (cvPhaseLaw m σsq K δ mu0 i (t i))
        (Arlib.GaussianCooling.coolLaw m σsq K i) (64 * ENNReal.ofReal eps) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have he1 : (1 : ℝ) ≤ 2 * Real.exp 1 := by
    nlinarith [Real.one_le_exp (zero_le_one : (0 : ℝ) ≤ 1)]
  have hM1 : (1 : ℝ) ≤ M := le_trans he1 hM
  set σ := Real.sqrt (σsq i) with hσdef
  have hsq : σ ^ 2 = σsq i := Real.sq_sqrt (hσ i).le
  have hσpos : 0 < σ := Real.sqrt_pos.2 (hσ i)
  have htnum : 4 * 640 ^ 2 * σ ^ 2 * (n : ℝ) * (Real.log M + 2 * Real.log (1 / eps))
      / (δ * Real.log 2) ^ 2 + 1 ≤ (t i : ℝ) := by rw [hsq]; exact ht i
  cases i with
  | zero =>
    have hwarm' : Arlib.IsWarm (ENNReal.ofReal M) mu0
        (Arlib.MarkovChains.ellGaussianProb (interior K) δ (σ ^ 2)) := by rw [hsq]; exact hwarm
    exact ⟨isProbabilityMeasure_cvPhaseLaw_zero hn hσ hσpos hδ (hδσ 0) hδn hKc hball hfin hR
        hKR (hRσ 0) hsq.symm hM1 hwarm' heps0 heps32 htnum,
      tvLe_cvPhaseLaw_zero hn hσ hσpos hδ (hδσ 0) hδn hKc hball hfin hR hKR (hRσ 0) hi
        hsq.symm hM1 hwarm' heps0 heps32 htnum⟩
  | succ k =>
    -- the interior phases mix from the constant `2e`, and `2e ≤ M` makes one deadline serve
    have hlogM : Real.log (2 * Real.exp 1) ≤ Real.log M :=
      Real.log_le_log (by positivity) hM
    have htsucc : 4 * 640 ^ 2 * σ ^ 2 * (n : ℝ)
        * (Real.log (2 * Real.exp 1) + 2 * Real.log (1 / eps)) / (δ * Real.log 2) ^ 2 + 1
        ≤ (t (k + 1) : ℝ) := by
      refine le_trans ?_ htnum
      have hA : (0 : ℝ) ≤ 4 * 640 ^ 2 * σ ^ 2 * (n : ℝ) := by positivity
      have hd : (0 : ℝ) < (δ * Real.log 2) ^ 2 := by positivity
      gcongr
    exact ⟨isProbabilityMeasure_cvPhaseLaw_succ hn hσ hσpos hδ (hδσ (k + 1)) hδn hKc hball
        hfin hR hKR (hRσ (k + 1)) hi hsq.symm hcc1 hcc2 (hrate k) heps0 heps32 htsucc,
      tvLe_cvPhaseLaw_succ hn hσ hσpos hδ (hδσ (k + 1)) hδn hKc hball hfin hR hKR
        (hRσ (k + 1)) hi hsq.symm hcc1 hcc2 (hrate k) heps0 heps32 htsucc⟩

/-! ## 5.  The coin space: one coordinate per input -/

/-- The volume algorithm's input: a body, an accuracy and a failure probability. -/
abbrev Param (n : ℕ) := Set (Space n) × ℝ × ℝ

/-- **The coin space.**  One `Space n`-valued coordinate for every possible input.

This is what dissolves the obstruction recorded at
`Arlib/Convexity/GaussianCooling/PhaseFromTV.lean` §5 and at
`Ttc/Volume/CVAmended.lean:318-323` — that the coin law `ν j i` is fixed *before* the body
`K` is seen, while `hTV` asks it to be close to `coolLaw … K i` for **every** `K`.  The coin
law is a *product* over all inputs (`MeasureTheory.Measure.infinitePi`, which needs no
countability and no standard-Borel hypothesis on the index), and the sampler `X K ε p j i`
reads off the `(K, ε, p)` coordinate.  Operationally: the algorithm draws fresh randomness
for the input it is given, which is what a sampler does. -/
abbrev CoinSpace (n : ℕ) := Param n → Space n

open scoped Classical in
/-- `μ` when `μ` is a probability measure, and the Dirac mass at the origin otherwise.

Needed because `Measure.infinitePi` requires *every* factor to be a probability measure,
including the factors at inputs `(K, ε, p)` that are not admissible bodies at all.  The
name promises a semantic identity, and `probOrDirac_eq` proves it (`CLAUDE.md` §11). -/
noncomputable def probOrDirac (μ : Measure (Space n)) : Measure (Space n) :=
  if IsProbabilityMeasure μ then μ else Measure.dirac 0

instance instIsProbabilityMeasureProbOrDirac (μ : Measure (Space n)) :
    IsProbabilityMeasure (probOrDirac μ) := by
  unfold probOrDirac
  split_ifs with h
  · exact h
  · exact Measure.dirac.isProbabilityMeasure

/-- **The promised identity**: on a probability measure `probOrDirac` is the identity. -/
theorem probOrDirac_eq {μ : Measure (Space n)} (h : IsProbabilityMeasure μ) :
    probOrDirac μ = μ := by
  unfold probOrDirac
  split_ifs
  rfl

/-- **The coin law at phase `i`**: independent coordinates, one per input. -/
noncomputable def coinMeasure (law : Param n → ℕ → Measure (Space n)) (i : ℕ) :
    Measure (CoinSpace n) :=
  Measure.infinitePi fun a => probOrDirac (law a i)

instance instIsProbabilityMeasureCoinMeasure (law : Param n → ℕ → Measure (Space n)) (i : ℕ) :
    IsProbabilityMeasure (coinMeasure law i) := by
  unfold coinMeasure; infer_instance

/-- **The sampler**: read off the coordinate belonging to the input. -/
def coinX (a : Param n) : CoinSpace n → Space n := fun ω => ω a

theorem measurable_coinX (a : Param n) : Measurable (coinX (n := n) a) :=
  measurable_pi_apply a

/-- **The law of the sample is the law at that coordinate.**  This is the marginal of an
arbitrary-index product measure, `MeasureTheory.Measure.infinitePi_map_eval`. -/
theorem map_coinX (law : Param n → ℕ → Measure (Space n)) (i : ℕ) (a : Param n) :
    (coinMeasure law i).map (coinX a) = probOrDirac (law a i) :=
  Measure.infinitePi_map_eval _ a

/-- **Transport of a total-variation bound through the coin space.** -/
theorem tvLe_map_coinX {law : Param n → ℕ → Measure (Space n)} {i : ℕ} {a : Param n}
    {ν : Measure (Space n)} {e : ℝ≥0∞} (hprob : IsProbabilityMeasure (law a i))
    (h : Arlib.TVLe (law a i) ν e) :
    Arlib.TVLe ((coinMeasure law i).map (coinX a)) ν e := by
  rw [map_coinX, probOrDirac_eq hprob]; exact h

/-- **The sampler's law family**, as a function of the input. -/
noncomputable def cvLaw (phases : Set (Space n) → ℝ → ℝ → ℕ)
    (σsq : Set (Space n) → ℝ → ℝ → ℕ → ℝ) (stepSize : Set (Space n) → ℝ → ℝ → ℝ)
    (start : Set (Space n) → ℝ → ℝ → Measure (Space n))
    (steps : Set (Space n) → ℝ → ℝ → ℕ → ℕ) (a : Param n) (i : ℕ) : Measure (Space n) :=
  cvPhaseLaw (phases a.1 a.2.1 a.2.2) (σsq a.1 a.2.1 a.2.2) a.1 (stepSize a.1 a.2.1 a.2.2)
    (start a.1 a.2.1 a.2.2) i (steps a.1 a.2.1 a.2.2 i)

/-! ## 6.  `hTV` itself -/

/-- **The `hTV` binder of `Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMeanAmended`
(`Ttc/Volume/CVAmended.lean:246`), discharged**, at

    E      := CoinSpace n
    ν j i  := coinMeasure (cvLaw phases σsq stepSize start steps) i
    X …    := coinX (K, ε, p)
    tvErr  := 64 · ENNReal.ofReal (acc K ε p)

Note what is **not** a binder: `MeasurableSet K`.  The sampler runs on `interior K` and
`Arlib.GaussianCooling.coolLaw_interior` transports the target back to `K` as an equality of
measures.

What *is* carried, and where it comes from:

| binder | supplier |
| --- | --- |
| `hn : 21 ≤ n` | the speedy conductance bound's regime |
| `hδn`, `hδσ` | the two independent step-size regimes, neither implying the other |
| `hRad0`, `hKrad`, `hRadσ` | the enclosing radius, and `R ≤ 2σᵢ√n` at **every** phase |
| `hcc1`, `hcc2`, `hrate` | the cooling schedule, `1 ≤ cc ≤ 1 + 2/n` |
| `hacc0`, `hacc32` | `0 < acc ≤ 1/32`, the rejection routine's accuracy window |
| `hsteps` | the mixing deadline, at the phase-`0` warmness constant |
| `hwarm` | **the phase-`0` warm start — the one genuinely open input** |

`hwarm` is unavoidable *here*: `Arlib.GaussianCooling.isWarm_condOn_coolLaw_ellGaussianProb`
warms phase `i+1` from phase `i`, and phase `0` has no predecessor.  Nothing in this
repository warms it. -/
theorem hTV_cvLaw (hn : 21 ≤ n)
    (phases : Set (Space n) → ℝ → ℝ → ℕ) (σsq : Set (Space n) → ℝ → ℝ → ℕ → ℝ)
    (stepSize : Set (Space n) → ℝ → ℝ → ℝ) (start : Set (Space n) → ℝ → ℝ → Measure (Space n))
    (steps : Set (Space n) → ℝ → ℝ → ℕ → ℕ) (Rad : Set (Space n) → ℝ → ℝ → ℝ)
    (acc warmM cc : Set (Space n) → ℝ → ℝ → ℝ)
    (hσ : ∀ K ε p j, 0 < σsq K ε p j)
    (hstart : ∀ K ε p, IsProbabilityMeasure (start K ε p))
    (hδ0 : ∀ K ε p, 0 < stepSize K ε p)
    (hδn : ∀ K ε p, stepSize K ε p ≤ 1 / (2 * (n : ℝ)))
    (hδσ : ∀ K ε p j, stepSize K ε p ≤ Real.sqrt (σsq K ε p j) / (8 * Real.sqrt n))
    (hRad0 : ∀ K ε p, 0 ≤ Rad K ε p)
    (hRadσ : ∀ K ε p j, Rad K ε p ≤ 2 * Real.sqrt (σsq K ε p j) * Real.sqrt n)
    (hcc1 : ∀ K ε p, 1 ≤ cc K ε p) (hcc2 : ∀ K ε p, cc K ε p ≤ 1 + 2 / (n : ℝ))
    (hrate : ∀ K ε p j, σsq K ε p (j + 1) = cc K ε p * σsq K ε p j)
    (hM : ∀ K ε p, 2 * Real.exp 1 ≤ warmM K ε p)
    (hacc0 : ∀ K ε p, 0 < acc K ε p) (hacc32 : ∀ K ε p, acc K ε p ≤ 1 / 32)
    (hsteps : ∀ K ε p i, 4 * 640 ^ 2 * σsq K ε p i * (n : ℝ)
      * (Real.log (warmM K ε p) + 2 * Real.log (1 / acc K ε p))
      / (stepSize K ε p * Real.log 2) ^ 2 + 1 ≤ (steps K ε p i : ℝ))
    (hKrad : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ x ∈ K, ‖x‖ ≤ Rad K ε p)
    (hwarm : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      Arlib.IsWarm (ENNReal.ofReal (warmM K ε p)) (start K ε p)
        (Arlib.MarkovChains.ellGaussianProb (interior K) (stepSize K ε p) (σsq K ε p 0))) :
    ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ (_j : ℕ) (i : Fin (phases K ε p)),
      Arlib.TVLe
        ((coinMeasure (cvLaw phases σsq stepSize start steps) (i : ℕ)).map (coinX (K, ε, p)))
        (Arlib.GaussianCooling.coolLaw (phases K ε p) (σsq K ε p) K (i : ℕ))
        (64 * ENNReal.ofReal (acc K ε p)) := by
  intro K ε p hε hp hp1 hconv hball hfin _j i
  haveI := hstart K ε p
  obtain ⟨hprob, htv⟩ := prob_and_tvLe_cvPhaseLaw hn (hσ K ε p) (hδ0 K ε p) (hδn K ε p)
    (hδσ K ε p) hconv hball hfin (hRad0 K ε p) (hKrad K ε p hε hp hp1 hconv hball hfin)
    (hRadσ K ε p) (hcc1 K ε p) (hcc2 K ε p) (hrate K ε p) (hM K ε p)
    (hwarm K ε p hε hp hp1 hconv hball hfin) (hacc0 K ε p) (hacc32 K ε p) (hsteps K ε p)
    i.isLt
  exact tvLe_map_coinX (law := cvLaw phases σsq stepSize start steps) hprob htv

/-! ## 7.  The volume algorithm with `hTV` removed -/

/-- **`Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMeanAmended` with its `hTV` argument
discharged**, by the speedy-walk sampler of §1 on the coin space of §5.

`E`, `ν`, `X` and `tvErr` are no longer the caller's data: they are

    E      = CoinSpace n,   ν j i = coinMeasure (cvLaw …) i,
    X …    = coinX (K, ε, p),   tvErr K ε p j i = 64 · ENNReal.ofReal (acc K ε p).

`hTV` and `htop` are proved.  What remains are the interface's *other* open binders — `hgb`,
`hKrad`, `hslack_mean`, `hbudget`, `hflat`, `hslack_var` — plus the sampler's regime, all
guarded by `∀ (_j : ℕ) (_i : Fin (phases K ε p))` exactly as the amended constructor guards
its own, so that the degenerate `phases = 0` witness below still exists.

The cooling rate is hard-wired to `1 + 1/n`, the amended constructor's `hrate`, which lies
inside `Arlib.GaussianCooling.isWarm_condOn_coolLaw_ellGaussianProb`'s window `cc ≤ 1 + 2/n`.

**The one open sampler input is `hwarm`**: warmness of the phase-`0` start against the speedy
stationary law.  Everything else the mixing chain needs is either proved
(`Arlib/Convexity/GaussianCooling/WarmSpeedy.lean` for phases `≥ 1`) or is a numeric side
condition on the schedule. -/
noncomputable def _root_.Ttc.VolumeAlgorithm.cousinsVempalaOfSpeedySampler (n : ℕ)
    (hn : 21 ≤ n)
    (phases : Set (Space n) → ℝ → ℝ → ℕ)
    (σsq : Set (Space n) → ℝ → ℝ → ℕ → ℝ)
    (Rad : Set (Space n) → ℝ → ℝ → ℝ)
    (stepSize : Set (Space n) → ℝ → ℝ → ℝ)
    (start : Set (Space n) → ℝ → ℝ → Measure (Space n))
    (steps : Set (Space n) → ℝ → ℝ → ℕ → ℕ)
    (acc warmM : Set (Space n) → ℝ → ℝ → ℝ) (B : ℝ)
    (hσ : ∀ K ε p j, 0 < σsq K ε p j)
    (hstart : ∀ K ε p, IsProbabilityMeasure (start K ε p))
    -- the interface's own surviving binders
    (hgb : ∀ K ε p (j i : ℕ) x,
      |Arlib.GaussianCooling.phaseScore (phases K ε p) (σsq K ε p) (interior K) i
        (coinX (K, ε, p) x)| ≤ B)
    (hKrad : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (_i : Fin (phases K ε p)),
      K ⊆ Metric.closedBall (0 : Space n) (Rad K ε p))
    (hslack_mean : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ (j : ℕ) (i : Fin (phases K ε p)),
      Real.exp (Rad K ε p ^ 2 / (2 * σsq K ε p (i : ℕ)))
          * (64 * ENNReal.ofReal (acc K ε p)).toReal
        ≤ ε / (2 * (2 + ε) * (phases K ε p : ℝ))
            * (Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K ((i : ℕ) + 1)
                / Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K (i : ℕ)))
    (hbudget : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (_i : Fin (phases K ε p)),
      2 * (phases K ε p : ℝ) ≤ (n : ℝ) * Arlib.GaussianCooling.varBudget (ε / 2))
    (hflat : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (i : Fin (phases K ε p)), (i : ℕ) + 1 = phases K ε p →
      Rad K ε p ^ 2 ≤ 2 * σsq K ε p (i : ℕ) * Real.log (1 + 2 / (n : ℝ)))
    (hslack_var : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ (j : ℕ) (i : Fin (phases K ε p)),
      (64 * ENNReal.ofReal (acc K ε p)).toReal
          * (Real.exp (Rad K ε p ^ 2 / (2 * σsq K ε p (i : ℕ))) ^ 2
              * (1 + 2 * (1 + Arlib.GaussianCooling.varBudget (ε / 2)
                  / (phases K ε p : ℝ))))
        ≤ (Arlib.GaussianCooling.varBudget (ε / 2) / (phases K ε p : ℝ) - 2 / (n : ℝ))
            * (Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K ((i : ℕ) + 1)
                / Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K (i : ℕ)) ^ 2)
    -- the sampler's regime, guarded exactly as the interface guards its own binders
    (hδ0 : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (_i : Fin (phases K ε p)), 0 < stepSize K ε p)
    (hδn : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (_i : Fin (phases K ε p)), stepSize K ε p ≤ 1 / (2 * (n : ℝ)))
    (hδσ : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (_i : Fin (phases K ε p)) (j : ℕ),
      stepSize K ε p ≤ Real.sqrt (σsq K ε p j) / (8 * Real.sqrt n))
    (hRad0 : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (_i : Fin (phases K ε p)), 0 ≤ Rad K ε p)
    (hRadσ : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (_i : Fin (phases K ε p)) (j : ℕ),
      Rad K ε p ≤ 2 * Real.sqrt (σsq K ε p j) * Real.sqrt n)
    (hrateAll : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (_i : Fin (phases K ε p)) (j : ℕ),
      σsq K ε p (j + 1) = σsq K ε p j * (1 + 1 / (n : ℝ)))
    (hM : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (_i : Fin (phases K ε p)), 2 * Real.exp 1 ≤ warmM K ε p)
    (hwarm : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (_i : Fin (phases K ε p)),
      Arlib.IsWarm (ENNReal.ofReal (warmM K ε p)) (start K ε p)
        (Arlib.MarkovChains.ellGaussianProb (interior K) (stepSize K ε p) (σsq K ε p 0)))
    (hacc0 : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (_i : Fin (phases K ε p)), 0 < acc K ε p)
    (hacc32 : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (_i : Fin (phases K ε p)), acc K ε p ≤ 1 / 32)
    (hsteps : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (_i : Fin (phases K ε p)) (j : ℕ),
      4 * 640 ^ 2 * σsq K ε p j * (n : ℝ)
          * (Real.log (warmM K ε p) + 2 * Real.log (1 / acc K ε p))
          / (stepSize K ε p * Real.log 2) ^ 2 + 1 ≤ (steps K ε p j : ℝ)) :
    Ttc.VolumeAlgorithm n :=
  Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMeanAmended n (CoinSpace n)
    (fun _j i => coinMeasure (cvLaw phases σsq stepSize start steps) i)
    (by omega) phases σsq Rad
    (fun K ε p _j _i => coinX (K, ε, p))
    (fun K ε p _j _i => 64 * ENNReal.ofReal (acc K ε p)) B hσ
    (fun _ _ _ _ _ => measurable_coinX _) hgb hKrad
    -- `htop` : `64 · ofReal _` is finite
    (fun _ _ _ _ _ _ _ _ _ _ _ =>
      ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)
    -- ★ `hTV` : DISCHARGED
    (fun K ε p hε hp hp1 hconv hball hfin j i => by
      haveI := hstart K ε p
      have hn0 : (0 : ℝ) < (n : ℝ) := by positivity
      have hnpos : (0 : ℝ) < 1 / (n : ℝ) := by positivity
      obtain ⟨hprob, htv⟩ := prob_and_tvLe_cvPhaseLaw hn (hσ K ε p)
        (hδ0 K ε p hε hp hp1 hconv hball hfin j i)
        (hδn K ε p hε hp hp1 hconv hball hfin j i)
        (hδσ K ε p hε hp hp1 hconv hball hfin j i) hconv hball hfin
        (hRad0 K ε p hε hp hp1 hconv hball hfin j i)
        (fun x hx => mem_closedBall_zero_iff.1
          (hKrad K ε p hε hp hp1 hconv hball hfin j i hx))
        (hRadσ K ε p hε hp hp1 hconv hball hfin j i)
        (by linarith : (1 : ℝ) ≤ 1 + 1 / (n : ℝ))
        (by
          have : 1 / (n : ℝ) ≤ 2 / (n : ℝ) := by
            rw [div_le_div_iff_of_pos_right hn0]; norm_num
          linarith)
        (fun k => by
          rw [hrateAll K ε p hε hp hp1 hconv hball hfin j i k]; ring)
        (hM K ε p hε hp hp1 hconv hball hfin j i)
        (hwarm K ε p hε hp hp1 hconv hball hfin j i)
        (hacc0 K ε p hε hp hp1 hconv hball hfin j i)
        (hacc32 K ε p hε hp hp1 hconv hball hfin j i)
        (hsteps K ε p hε hp hp1 hconv hball hfin j i) i.isLt
      exact tvLe_map_coinX (law := cvLaw phases σsq stepSize start steps) hprob htv)
    hslack_mean
    -- `hrate` : the amended constructor's, at the hard-wired rate
    (fun K ε p hε hp hp1 hconv hball hfin j i =>
      hrateAll K ε p hε hp hp1 hconv hball hfin j i (i : ℕ))
    hbudget hflat hslack_var

/-! ## 8.  Non-vacuity (`CLAUDE.md` §11) -/

/-- **Every binder of `prob_and_tvLe_cvPhaseLaw` discharged simultaneously, at a genuine
cooling phase**, on

    n = 21,  K = B̄(0,1) ⊆ ℝ²¹,  σ²ⱼ = 100²·(22/21)ʲ,  δ = 1/42,  R = 1,
    m = 2,  i = 1,  M = 2e,  eps = 1/128,  t k = ⌈deadline k⌉₊,
    mu0 = ellGaussianProb (interior K) δ σ²₀.

Non-degenerate in three ways that matter:

* `i = 1 > 0`, so the phase is a **cooled** one, warmed from phase `0` by
  `Arlib.GaussianCooling.isWarm_condOn_coolLaw_ellGaussianProb`, not the assumed-warm start;
* `σ²₀ ≠ σ²₁` (carried as a conjunct), so the schedule really cools, at the hard-wired rate
  `1 + 1/n = 22/21`;
* `64·ofReal(1/128) = ofReal(1/2) < 1`, so the total-variation conclusion is a genuine bound
  and not the vacuous `≥ 1`; and the sampler's law is a **probability measure**, so the
  conclusion is not the trivially-`TVLe` zero measure.

The warm start `hwarm` is discharged here only because `mu0` *is* the speedy stationary law,
`IsWarm M μ μ` for `M ≥ 1`.  That is a witness of satisfiability, not an algorithm: the
sampler cannot start from the law it is trying to reach.  See the module docstring. -/
theorem prob_and_tvLe_cvPhaseLaw_witness :
    ∃ (nn m : ℕ) (K : Set (Space nn)) (σsq : ℕ → ℝ) (δ R M eps : ℝ)
      (mu0 : Measure (Space nn)) (t : ℕ → ℕ) (i : ℕ),
      21 ≤ nn ∧ (∀ j, 0 < σsq j) ∧ 0 < δ ∧ δ ≤ 1 / (2 * (nn : ℝ)) ∧
        (∀ j, δ ≤ Real.sqrt (σsq j) / (8 * Real.sqrt nn)) ∧
        Convex ℝ K ∧ ball (0 : Space nn) 1 ⊆ K ∧ volume K ≠ ⊤ ∧
        0 ≤ R ∧ (∀ x ∈ K, ‖x‖ ≤ R) ∧
        (∀ j, R ≤ 2 * Real.sqrt (σsq j) * Real.sqrt nn) ∧
        (∀ j, σsq (j + 1) = (1 + 1 / (nn : ℝ)) * σsq j) ∧
        IsProbabilityMeasure mu0 ∧ 2 * Real.exp 1 ≤ M ∧
        Arlib.IsWarm (ENNReal.ofReal M) mu0
          (Arlib.MarkovChains.ellGaussianProb (interior K) δ (σsq 0)) ∧
        0 < eps ∧ eps ≤ 1 / 32 ∧
        (∀ k, 4 * 640 ^ 2 * σsq k * (nn : ℝ) * (Real.log M + 2 * Real.log (1 / eps))
          / (δ * Real.log 2) ^ 2 + 1 ≤ (t k : ℝ)) ∧
        0 < i ∧ i < m ∧ σsq 0 ≠ σsq 1 ∧
        (64 : ℝ≥0∞) * ENNReal.ofReal eps = ENNReal.ofReal (1 / 2) ∧
        IsProbabilityMeasure (cvPhaseLaw m σsq K δ mu0 i (t i)) ∧
        Arlib.TVLe (cvPhaseLaw m σsq K δ mu0 i (t i))
          (Arlib.GaussianCooling.coolLaw m σsq K i) (64 * ENNReal.ofReal eps) := by
  classical
  have hcast : Real.sqrt ((21 : ℕ) : ℝ) = Real.sqrt (21 : ℝ) := by norm_num
  have hnn0 : (0 : ℝ) ≤ Real.sqrt (21 : ℝ) := Real.sqrt_nonneg _
  have hsq21 : Real.sqrt (21 : ℝ) ^ 2 = 21 := Real.sq_sqrt (by norm_num)
  have h5 : Real.sqrt (21 : ℝ) ≤ 5 := by nlinarith
  have h4 : (4 : ℝ) ≤ Real.sqrt (21 : ℝ) := by nlinarith
  -- the schedule
  have hpos : ∀ j : ℕ, (0 : ℝ) < 100 ^ 2 * (22 / 21 : ℝ) ^ j := by
    intro j; positivity
  have hge : ∀ j : ℕ, (100 : ℝ) ≤ Real.sqrt (100 ^ 2 * (22 / 21 : ℝ) ^ j) := by
    intro j
    have h1 : (1 : ℝ) ≤ (22 / 21 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have h2 : (100 : ℝ) ^ 2 ≤ 100 ^ 2 * (22 / 21 : ℝ) ^ j := by nlinarith
    calc (100 : ℝ) = Real.sqrt (100 ^ 2) := by rw [Real.sqrt_sq (by norm_num)]
      _ ≤ _ := Real.sqrt_le_sqrt h2
  -- the body
  have hKm' : MeasurableSet (interior (Metric.closedBall (0 : Space 21) 1)) :=
    isOpen_interior.measurableSet
  have hKc : Convex ℝ (Metric.closedBall (0 : Space 21) 1) := convex_closedBall _ _
  have hball : ball (0 : Space 21) 1 ⊆ Metric.closedBall (0 : Space 21) 1 :=
    Metric.ball_subset_closedBall
  have hfin : volume (Metric.closedBall (0 : Space 21) 1) ≠ ⊤ := measure_closedBall_lt_top.ne
  obtain ⟨-, hKc', hball', hK0', hfin'⟩ :=
    Arlib.GaussianCooling.interior_admissible hKc hball hfin
  have hKb' : Bornology.IsBounded (interior (Metric.closedBall (0 : Space 21) 1)) :=
    Metric.isBounded_closedBall.subset interior_subset
  haveI hmu0 : IsProbabilityMeasure
      (Arlib.MarkovChains.ellGaussianProb (interior (Metric.closedBall (0 : Space 21) 1))
        ((1 : ℝ) / 42) (100 ^ 2 * (22 / 21 : ℝ) ^ 0)) :=
    Arlib.MarkovChains.isProbabilityMeasure_ellGaussianProb
      (Arlib.MarkovChains.ellGaussianMeasure_univ_ne_zero hKm' hKc' hKb' hK0' (by norm_num) _)
      (ne_top_of_le_ne_top hfin'
        (Arlib.MarkovChains.ellGaussianMeasure_univ_le (hpos 0) _ ((1 : ℝ) / 42)))
  have h1e : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * Real.exp 1) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal
      (by nlinarith [Real.one_le_exp (zero_le_one : (0 : ℝ) ≤ 1)])
  have hwarm : Arlib.IsWarm (ENNReal.ofReal (2 * Real.exp 1))
      (Arlib.MarkovChains.ellGaussianProb (interior (Metric.closedBall (0 : Space 21) 1))
        ((1 : ℝ) / 42) (100 ^ 2 * (22 / 21 : ℝ) ^ 0))
      (Arlib.MarkovChains.ellGaussianProb (interior (Metric.closedBall (0 : Space 21) 1))
        ((1 : ℝ) / 42) (100 ^ 2 * (22 / 21 : ℝ) ^ 0)) := by
    intro S _
    conv_lhs => rw [← one_mul (Arlib.MarkovChains.ellGaussianProb _ _ _ S)]
    exact mul_le_mul_right' h1e _
  have hδσ : ∀ j : ℕ, (1 : ℝ) / 42
      ≤ Real.sqrt (100 ^ 2 * (22 / 21 : ℝ) ^ j) / (8 * Real.sqrt ((21 : ℕ) : ℝ)) := by
    intro j
    rw [hcast, le_div_iff₀ (by positivity)]
    nlinarith [hge j]
  have hRσ : ∀ j : ℕ, (1 : ℝ)
      ≤ 2 * Real.sqrt (100 ^ 2 * (22 / 21 : ℝ) ^ j) * Real.sqrt ((21 : ℕ) : ℝ) := by
    intro j
    rw [hcast]
    nlinarith [hge j]
  have hrate : ∀ j : ℕ, (100 : ℝ) ^ 2 * (22 / 21 : ℝ) ^ (j + 1)
      = (1 + 1 / ((21 : ℕ) : ℝ)) * (100 ^ 2 * (22 / 21 : ℝ) ^ j) := by
    intro j
    rw [pow_succ]
    push_cast
    ring
  have hdead : ∀ k : ℕ, 4 * 640 ^ 2 * (100 ^ 2 * (22 / 21 : ℝ) ^ k) * ((21 : ℕ) : ℝ)
        * (Real.log (2 * Real.exp 1) + 2 * Real.log (1 / ((1 : ℝ) / 128)))
        / (((1 : ℝ) / 42) * Real.log 2) ^ 2 + 1
      ≤ ((⌈4 * 640 ^ 2 * (100 ^ 2 * (22 / 21 : ℝ) ^ k) * ((21 : ℕ) : ℝ)
        * (Real.log (2 * Real.exp 1) + 2 * Real.log (1 / ((1 : ℝ) / 128)))
        / (((1 : ℝ) / 42) * Real.log 2) ^ 2 + 1⌉₊ : ℕ) : ℝ) := fun k => Nat.le_ceil _
  obtain ⟨hprob, htv⟩ := prob_and_tvLe_cvPhaseLaw (n := 21) (m := 2)
    (σsq := fun j => 100 ^ 2 * (22 / 21 : ℝ) ^ j) le_rfl hpos (by norm_num) (by norm_num)
    hδσ hKc hball hfin (by norm_num) (fun x hx => by
      rw [Metric.mem_closedBall, dist_zero_right] at hx; exact hx)
    hRσ (by norm_num : (1 : ℝ) ≤ 1 + 1 / ((21 : ℕ) : ℝ))
    (by push_cast; norm_num) hrate
    (le_refl (2 * Real.exp 1)) hwarm (by norm_num) (by norm_num) hdead
    (by norm_num : 1 < 2)
  refine ⟨21, 2, Metric.closedBall 0 1, fun j => 100 ^ 2 * (22 / 21 : ℝ) ^ j, 1 / 42, 1,
    2 * Real.exp 1, 1 / 128,
    Arlib.MarkovChains.ellGaussianProb (interior (Metric.closedBall (0 : Space 21) 1))
      ((1 : ℝ) / 42) (100 ^ 2 * (22 / 21 : ℝ) ^ 0),
    (fun k => ⌈4 * 640 ^ 2 * (100 ^ 2 * (22 / 21 : ℝ) ^ k) * ((21 : ℕ) : ℝ)
        * (Real.log (2 * Real.exp 1) + 2 * Real.log (1 / ((1 : ℝ) / 128)))
        / (((1 : ℝ) / 42) * Real.log 2) ^ 2 + 1⌉₊), 1,
    le_rfl, hpos, by norm_num, by norm_num, hδσ, hKc, hball, hfin, by norm_num,
    (fun x hx => by rw [Metric.mem_closedBall, dist_zero_right] at hx; exact hx), hRσ,
    hrate, hmu0, le_rfl, hwarm, by norm_num, by norm_num, hdead,
    by norm_num, by norm_num, by norm_num, ?_, hprob, htv⟩
  rw [show (64 : ℝ≥0∞) = ENNReal.ofReal 64 by simp,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64)]
  norm_num

/-- **Non-vacuity of `Ttc.VolumeAlgorithm.cousinsVempalaOfSpeedySampler`'s binder bundle.**

Degenerate, and honestly so: `phases = 0`, so `Fin (phases K ε p)` is empty and every
guarded binder — the interface's `hKrad`, `hslack_mean`, `hbudget`, `hflat`, `hslack_var`
and the sampler's whole regime — holds by `Fin.elim0`.  Only `hσ`, `hstart` and `hgb` carry
content, and `hgb` holds because at zero phases the score is an indicator
(`Ttc.abs_phaseScore_zero_le_one`).

It certifies that the constructor's hypotheses do not contradict one another, and nothing
more.  The *sampler* side is witnessed non-degenerately, at a genuine cooling phase, by
`prob_and_tvLe_cvPhaseLaw_witness`; what no witness here supplies is a schedule meeting
`hbudget` and `hslack_mean`/`hslack_var` at `phases > 0`, which is the interface's own
obstruction (`Arlib.GaussianCooling.geomSchedule_total_cooling_lt`), untouched by this
file. -/
noncomputable def _root_.Ttc.VolumeAlgorithm.cousinsVempalaOfSpeedySamplerWitness (n : ℕ)
    (hn : 21 ≤ n) : Ttc.VolumeAlgorithm n :=
  Ttc.VolumeAlgorithm.cousinsVempalaOfSpeedySampler n hn
    (fun _ _ _ => 0) (fun _ _ _ _ => 1) (fun _ _ _ => 1)
    (fun _ _ _ => 1 / (2 * (n : ℝ))) (fun _ _ _ => Measure.dirac 0) (fun _ _ _ _ => 0)
    (fun _ _ _ => 1 / 32) (fun _ _ _ => 2 * Real.exp 1) 1
    (fun _ _ _ _ => one_pos) (fun _ _ _ => Measure.dirac.isProbabilityMeasure)
    (fun _ _ _ _ _ _ => abs_phaseScore_zero_le_one _ _ _ _)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0) (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0) (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0) (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0) (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0) (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0) (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0) (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0) (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)

section AxiomCheck

#print axioms Ttc.CVSampler.tvLe_cvPhaseLaw_succ
#print axioms Ttc.CVSampler.tvLe_cvPhaseLaw_zero
#print axioms Ttc.CVSampler.isProbabilityMeasure_phaseLaw
#print axioms Ttc.CVSampler.isProbabilityMeasure_cvPhaseLaw_succ
#print axioms Ttc.CVSampler.isProbabilityMeasure_cvPhaseLaw_zero
#print axioms Ttc.CVSampler.prob_and_tvLe_cvPhaseLaw
#print axioms Ttc.CVSampler.probOrDirac_eq
#print axioms Ttc.CVSampler.map_coinX
#print axioms Ttc.CVSampler.tvLe_map_coinX
#print axioms Ttc.CVSampler.measurable_coinX
#print axioms Ttc.CVSampler.hTV_cvLaw
#print axioms Ttc.VolumeAlgorithm.cousinsVempalaOfSpeedySampler
#print axioms Ttc.CVSampler.prob_and_tvLe_cvPhaseLaw_witness
#print axioms Ttc.VolumeAlgorithm.cousinsVempalaOfSpeedySamplerWitness

end AxiomCheck

end Ttc.CVSampler
