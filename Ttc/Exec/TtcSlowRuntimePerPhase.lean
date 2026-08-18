import Ttc.Exec.TtcSlowRuntimeSharp
import Ttc.Exec.CVPerPhaseFrontier

/-!
# The **per-phase** cost envelope for the slow canonical volume route — and the exact
obstruction that keeps it from becoming a third unconditional runtime capstone

The intended deliverable of this file was `ttc_volume_runtime_perPhase`, the analogue of
`Ttc.TtcSlowRuntimeSharp.ttc_volume_runtime_sharp` combining

* **P1**, the sharp transport exponent (`Ttc.CVPerPhaseFrontier.perPhaseExpSharp`), and
* **P2**, the `n`-aware per-phase stream count
  (`Ttc.CVPerPhaseSamples.perPhaseRuntimeSamples`, a factor `n / 3` below
  `Ttc.CVCorrectedRuntime.correctedRuntimeSamples`),

with the **stated** envelope taken at the smaller stream count.  That capstone is **not**
in this file, and it is not in this file for a mathematical reason, not a bookkeeping one.
The reason is recorded in full below, because it is the load-bearing finding.

## What *is* proved here

The whole *envelope* half of the mirror, which is where the `n` of P2 has to show up if the
stated bound is to improve at all:

* `perPhaseStreamsP` — the pinned stream count at the per-phase provisioning;
* `n_le_slowPhasesP_add_one` — the phase-count side condition of the saving, discharged
  outright, so that the two comparisons below assume nothing beyond `4 ≤ n` and
  `0 < eps ≤ 1`;
* `nmul_perPhaseStreamsP_le_three_slowStreamsP`,
  `perPhaseStreamsP_lt_slowStreamsP` — the factor-`n` saving, quantified;
* `slowPerPhaseOverhead` — `Ttc.CVSlowActualCostEnvelope.slowActualOverhead` with
  `Ttc.CVSlowEffectiveOverhead.slowStreamsP` replaced by `perPhaseStreamsP`;
* `slowPerPhaseOverhead_le_slowActualOverhead` and
  `nmul_slowPerPhaseRetained_le_three_slowActualRetained` — the payoff, isolated: at the
  *same* per-phase retry and deadline envelopes `(Lenv, Tenv)` the per-phase overhead is
  below the sharp one, and the retained scalar it clips is smaller by the full factor
  `n / 3`;
* `slowPerPhase_hscalar` — the frontier's cost-side binder at that overhead;
* `slowPerPhaseOV`, `slowPerPhaseEffective`, `one_le_slowPerPhaseOV`,
  `slowPerPhaseEffective_le_slowPerPhaseOV` — the `OV` / `heff` pair in the exact shape
  `Ttc.TtcShapedRuntime.implementationOfEffectiveCertificatesGen` consumes, and
* `slowPerPhaseOV_le_slowSharpOV` — the relationship the capstone would have stated.

Everything here is unconditional and axiom-clean.  None of it needs the frontier.

## READ THIS BEFORE CITING `slowPerPhaseOV` — it is NOT a runtime bound

`slowPerPhaseOV` and `slowPerPhaseOverhead` are **declarations of an envelope, not
theorems about any run.**  No law in this repository is proved to have expected cost under
them, because the certificate that would establish that is exactly what is blocked below.
They are the envelope the *repaired* capstone would state.

Two specific traps, both of which pass `#print axioms` and a green build:

* the `Lenv` / `Tenv` slots of `slowPerPhaseOV` are still the **sharp** route's
  (`Ttc.TtcSlowRuntimeSharp.slowSharpLenv`, `slowSharpTenv`), because no per-phase retry or
  deadline chain exists against a correct schedule.  `slowPerPhaseOverhead` and
  `slowPerPhase_hscalar` are fully parametric in `(Lenv, Tenv)` and survive the repair, but
  the *instantiation* in `slowPerPhaseOV` does not;
* `slowPerPhaseOV_le_slowSharpOV` is a comparison of two **declared** envelopes.  It says
  the per-phase envelope is smaller.  It does **not** say anything runs within it.

The honest one-line summary: **the operative complexity of this development is still the
sharp route's, `Õ(m·n⁷·ρ⁸/ε⁴)`.**  Nothing in this file improves it.  Citing
`slowPerPhaseOV_le_slowSharpOV` as evidence of a factor `n` in the *runtime* would be a
misreading of exactly the kind `AUDIT.md` §11 exists to catch.

## What blocks the capstone, precisely

`Ttc.CVPerPhaseFrontier.exists_slowOneRunCertificate_canonical_perPhase`
(`Ttc/Exec/CVPerPhaseFrontier.lean:1139`) carries the binder

```
hphaseMoment : ∀ j, ∫ (clipped j)² ≤ perPhaseFactor n m k j * (∫ clipped j)²
```

(`Ttc/Exec/CVPerPhaseFrontier.lean:1208`).  It is exactly the binder the `n`-fold stream
saving is paid for by, and it is the only route to `factor := perPhaseFactor`.  Every
proved way to reach it goes through
`Ttc.CVPerPhaseMomentBundle.operational_slowCanonical_clippedMoment_bundle_perPhase`, whose
own scalar input is the operational per-phase second moment at
`Ttc.CVPerPhaseMomentBundle.sharpTransportedFactor n m (i+1)`, i.e. through
`Ttc.CVSharpFactorSeven.operational_path_phaseScore_memLp_and_sq_moment_le_factor_of_targetTV_bound`
(`Ttc/Exec/CVSharpFactorSeven.lean:335`) whose `hslack` binder (`:357`) reads

```
(mixError i + targetError).toReal * (S i ^ 2 * (1 + 2 * T)) ≤ (T - C) * ratio ^ 2
```

At `C := 1 + 2/n` and `T := 2 C - 1 = 1 + 4/n` — the per-phase pair — this is

```
(mixError + targetError) * S² * (3 + 8/n) ≤ (2/n) * ratio²           (interior index)
(mixError + targetError) * S² * 7         ≤ 1     * ratio²           (terminal index)
```

while the **only** thing the declared schedule supplies is
`Ttc.CVGaussianScoreAwareParameters.scoreAwareMixError_mul_boundSq_le_slack`
(`Ttc/Exec/CVGaussianScoreAwareParameters.lean:123`),

```
mixError * boundSq ≤ slack,
```

which at `slack := Ttc.CVPerPhaseFrontier.perPhaseSlack n m K = (2/n)·ratio²`
(`Ttc/Exec/CVPerPhaseFrontier.lean:160`) and
`boundSq := perPhaseBoundSqGen n E = E²·(3 + 8/n)` (`:185`) is

```
mixError * E² * (3 + 8/n) ≤ (2/n) * ratio².
```

At the **terminal** index this is comfortable (`7 · (2/n)/(3 + 8/n) = 14/(3n+8) ≤ 1` iff
`n ≥ 2`, free under `21 ≤ n`) — that is the arithmetic note the frontier left, and it
re-derives.  At every **interior** index it is *exactly saturated*: the required and the
available right-hand sides are literally the same number `(2/n)·ratio²`, and the required
left-hand side is strictly larger than the available one, because

1. it carries the radial tail `targetError` in addition to `mixError`, and
2. at the P1-sharp exponent `S² ≤ 3 E²` is the only available link
   (`Ttc.CVPerPhaseFrontier.perPhaseSharp_supData`, last conjunct), costing a further
   factor `3`.

Item 1 alone is fatal, at *both* exponent instantiations: `perPhaseStandard_supData` takes
`S = E`, and the inequality still fails by exactly the tail term.

The structural cause is visible by comparison.  The loose route declares
`Ttc.CVSlowCanonicalUniformParameters.slowUniformSlack = phaseMomentSlackSeven … / 2` and
the sharp route `Ttc.CVSharpUniformParameters.slowSharpSlack = phaseMomentSlackSeven … / 6`.
Those divisors are not decoration: they are precisely the headroom that pays for the radial
half `slowTargetError` (`Ttc.CVRAwareGlobalRadius.slowTargetError_rAware_scaled_le` feeding
`Ttc.CVSlowCanonicalMomentBinders.slowCanonical_htailBudget`).  `perPhaseSlack` declares the
mixing slack at the **full** transport allowance `(C - 1)·ratio²` with no divisor, so the
schedule it defines has no room for the tail.  `Ttc.CVPerPhaseMomentBundle`'s own Step 9
docstring says as much: "Only that slack inequality is left open, and it is a statement
about the *mixing schedule* … Declaring it is the existing-file change this file
deliberately does not make."

`Ttc.CVPerPhaseFrontier.perPhaseSlack` is used nowhere outside
`Ttc/Exec/CVPerPhaseFrontier.lean`, and both §5 and §6 of that file pin it (§5 through the
binder `hslackDef : slack = perPhaseSlack n m K`), so the repair cannot be made from a new
file: it is an edit to `CVPerPhaseFrontier`.

**And the repair is not a one-token change.**  Dividing the declared slack by a constant
`c` buys `mixError · S² · (3 + 8/n) ≤ (2/(cn))·ratio²`, leaving `(1 - 1/c)·(2/n)·ratio²`
for the tail — an allowance of order `1/n`.  But the tail budget available is
`slowTargetError · exp(R²/2σ) ≤ slowUniformMeanTailFloor` together with
`slowCanonical_htailBudget`, which caps the tail's contribution at order `ratio²/30` — a
**constant** fraction, not an `O(1/n)` one.  So a constant divisor fixes the interior index
only for `n` below a fixed threshold, while the theorem quantifies over all `n ≥ 21`.  The
per-phase route additionally needs an `n`-aware mean-tail floor, i.e. a larger global
truncation radius `q` (logarithmic cost) so that `slowUniformMeanTailFloor` itself shrinks
like `1/n`.  Both changes live in existing files.

## A second, independent gap on the cost side

Even with the slack repaired, §6's `hsteps` binder
(`Ttc/Exec/CVPerPhaseFrontier.lean:1231`) is stated at
`Ttc.CVSlowRadiusQCanonicalOperational.slowCanonicalSteps` — the *compounding-warmness*
deadline — and at the mixing radius `slowUniformQ`.  §3's cap
`Ttc.CVPerPhaseFrontier.slowScoreAwareSteps_perPhase_active_le` (`:631`) is stated at
`Ttc.CVSlowSourceReferenceCertificate.slowScoreAwareSteps` — the *fixed-warm* deadline —
and at `Ttc.CVSlowGlobalRadiusTailBudget.slowGlobalRadiusQ`.  Neither the deadline function
nor the radius matches, so §3 does not discharge §6's `hsteps`.  What is needed is the
per-phase analogue of the whole of `Ttc/Exec/CVSharpSlowSteps.lean` (a
`slowCanonicalSteps_perPhase_le` built from `Ttc.CVSlowActualDeadline`'s bound-independent
bridge, `Ttc.CVSlowWarmBudgetBound` / `Ttc.CVRefreshWarmRoute`, and §1's
`perPhaseShareFloorGen_le_scoreAwareShare`).  That layer *is* mechanical and would close
today — but it is pinned to `perPhaseSlack`, which the repair above must change, so
building it now would build fifteen declarations against a schedule known to be wrong.  It
is deliberately not built here.

## Consequence for the `OV`

Because no per-phase `hsteps` / `hretries` pair is available against a *correct* schedule,
`slowPerPhaseOV` below keeps `Ttc.TtcSlowRuntimeSharp`'s own per-phase retry and deadline
envelopes `slowSharpLenv`, `slowSharpTenv` in its two envelope slots, and differs from
`Ttc.TtcSlowRuntimeSharp.slowSharpOV` in **exactly one place**: the stream count of the
retained-scalar envelope.  That is the honest statement of what P2 buys once its schedule
is repaired, and `slowPerPhaseOV_le_slowSharpOV` /
`nmul_slowPerPhaseRetained_le_three_slowActualRetained` are its quantified form.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Ttc.TtcSlowRuntimePerPhase

open MeasureTheory ProbabilityTheory Metric Set
open Ttc.CVSourcePolynomialCutoffCapstone (sourceLogFactor sourceOneRunQueryEnvelope
  sourceOneRunQueryBudget sourceLogFactor_pos)
open Ttc.TtcCircumRadius (circumR circumR_nonneg)
open Ttc.CVCorrectedRuntime (correctedRuntimeSamples correctedRuntimeSamples_pos)
open Ttc.CVPerPhaseSamples (perPhaseRuntimeSamples perPhaseRuntimeSamples_pos
  perPhaseRuntimeSamples_saving)
open Ttc.CVPerPhaseMomentBundle (perPhaseRuntimeSamples_lt_correctedRuntimeSamples)
open Ttc.CVSlowEffectiveOverhead (slowPhasesP slowStreamsP le_sourceOneRunQueryEnvelope_of_le)
open Ttc.CVSlowActualCostEnvelope (slowActualRetainedRealEnvelope
  slowActualRetainedRealEnvelope_nonneg slowActualRetainedRealEnvelope_mono
  slowActualRetainedScalar_le_realEnvelope slowActualOverhead
  one_le_slowActualOverhead slowActualOverhead_nonneg)
open Ttc.TtcCallCircumAdmissible (cvAdmCircum)
open Ttc.TtcSlowRuntimeFinal (one_le_sourceLogFactor)
open Ttc.TtcSlowRuntimeSharp (slowSharpLenv slowSharpTenv slowSharpOV)
open scoped ENNReal Classical BigOperators

/-! ## Step 1 — the pinned stream count at the per-phase provisioning

`Ttc.CVSlowEffectiveOverhead.slowStreamsP n R2 eps = correctedRuntimeSamples (slowPhasesP n R2) eps`
(`Ttc/Exec/CVSlowEffectiveOverhead.lean:592`) is the stream count that sits inside the
*envelope*, feeding `slowRetriesP`, `slowDeadlineP` and hence every overhead constant of the
route.  This is that definition with `correctedRuntimeSamples` replaced by the `n`-aware
`perPhaseRuntimeSamples`; it is the only substitution the whole cost layer needs. -/

/-- **The per-phase pinned stream count.**  `Ttc.CVSlowEffectiveOverhead.slowStreamsP` at
the `n`-aware provisioning `Ttc.CVPerPhaseSamples.perPhaseRuntimeSamples`. -/
noncomputable def perPhaseStreamsP (n : Nat) (R2 eps : Real) : Nat :=
  perPhaseRuntimeSamples n (slowPhasesP n R2) eps

theorem perPhaseStreamsP_pos (n : Nat) (R2 eps : Real) : 0 < perPhaseStreamsP n R2 eps :=
  perPhaseRuntimeSamples_pos _ _ _

theorem perPhaseStreamsP_eq (n : Nat) (R2 eps : Real) :
    perPhaseStreamsP n R2 eps = perPhaseRuntimeSamples n (slowPhasesP n R2) eps := rfl

theorem slowStreamsP_eq (n : Nat) (R2 eps : Real) :
    slowStreamsP n R2 eps = correctedRuntimeSamples (slowPhasesP n R2) eps := rfl

/-- **The phase-count side condition of the saving, discharged.**  `perPhaseRuntimeSamples`
beats `correctedRuntimeSamples` only when `n ≤ m + 1`; at the pinned phase count that holds
outright, and by a wide margin.  Indeed
`slowPhasesP n R2 = coldPhases n (s0 / max 1 R2) + 1` with `s0 = 1/(16 n)`, so the cooling
schedule needs `⌈log (16 n · max 1 R2) / log (1 + 1/n)⌉₊ ≥ n · log 16 > 2 n` phases. -/
theorem n_le_slowPhasesP_add_one {n : Nat} (hn : 1 ≤ n) (R2 : Real) :
    (n : Real) ≤ (slowPhasesP n R2 : Real) + 1 := by
  have hnR : (1 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hn0 : (0 : Real) < (n : Real) := by linarith
  have hR1 : (1 : Real) ≤ max 1 R2 := le_max_left _ _
  set x : Real :=
    Ttc.CVSlowSourceReferenceCertificate.slowSourceInitialVariance n / max 1 R2 with hxdef
  have hs0 : Ttc.CVSlowSourceReferenceCertificate.slowSourceInitialVariance n =
      1 / (16 * (n : Real)) := rfl
  have hx0 : 0 < x := by
    rw [hxdef, hs0]
    positivity
  have hinvx : 1 / x = 16 * (n : Real) * max 1 R2 := by
    rw [hxdef, hs0]
    field_simp
  have hexp : Real.exp 1 ≤ 1 / x := by
    rw [hinvx]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    nlinarith
  have hlog1 : (1 : Real) ≤ Real.log (1 / x) :=
    (Real.le_log_iff_exp_le (by positivity)).2 hexp
  have hbase0 : 0 < Real.log (1 + 1 / (n : Real)) :=
    Real.log_pos (by
      have : (0 : Real) < 1 / (n : Real) := by positivity
      linarith)
  have hbase : Real.log (1 + 1 / (n : Real)) ≤ 1 / (n : Real) := by
    have := Real.log_le_sub_one_of_pos
      (show (0 : Real) < 1 + 1 / (n : Real) by positivity)
    linarith
  have hratio : (n : Real) ≤
      max 0 (Real.log (1 / x)) / Real.log (1 + 1 / (n : Real)) := by
    rw [max_eq_right (by linarith : (0 : Real) ≤ Real.log (1 / x)), le_div_iff₀ hbase0]
    have hstep : (n : Real) * Real.log (1 + 1 / (n : Real)) ≤
        (n : Real) * (1 / (n : Real)) :=
      mul_le_mul_of_nonneg_left hbase (by linarith)
    have hone : (n : Real) * (1 / (n : Real)) = 1 := by field_simp
    linarith [hone ▸ hstep]
  have hceil : max 0 (Real.log (1 / x)) / Real.log (1 + 1 / (n : Real)) ≤
      (Ttc.CVHybridSchedule.coldPhases n x : Real) := by
    unfold Ttc.CVHybridSchedule.coldPhases
    exact Nat.le_ceil _
  have hphases : (Ttc.CVHybridSchedule.coldPhases n x : Real) ≤
      (slowPhasesP n R2 : Real) := by
    have : Ttc.CVHybridSchedule.coldPhases n x ≤ slowPhasesP n R2 := by
      show Ttc.CVHybridSchedule.coldPhases n x ≤
        Ttc.CVHybridSchedule.coldPhases n x + 1
      omega
    exact_mod_cast this
  linarith

/-- **The factor-`n` saving in the pinned stream count, quantified.**  This is
`Ttc.CVPerPhaseSamples.perPhaseRuntimeSamples_saving` at the pinned phase count: the
per-phase provisioning is smaller than the uniform one by a factor `n / 3`. -/
theorem nmul_perPhaseStreamsP_le_three_slowStreamsP
    {n : Nat} {R2 eps : Real} (hn : 0 < n)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (n : Real) * (perPhaseStreamsP n R2 eps : Real) ≤
      3 * (slowStreamsP n R2 eps : Real) :=
  perPhaseRuntimeSamples_saving hn (n_le_slowPhasesP_add_one hn R2) heps heps1

/-- The per-phase pinned stream count is strictly below the uniform one. -/
theorem perPhaseStreamsP_lt_slowStreamsP
    {n : Nat} {R2 eps : Real} (hn : 4 ≤ n)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    perPhaseStreamsP n R2 eps < slowStreamsP n R2 eps :=
  perPhaseRuntimeSamples_lt_correctedRuntimeSamples hn
    (n_le_slowPhasesP_add_one (by omega) R2) heps heps1

theorem perPhaseStreamsP_le_slowStreamsP
    {n : Nat} {R2 eps : Real} (hn : 4 ≤ n)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    perPhaseStreamsP n R2 eps ≤ slowStreamsP n R2 eps :=
  (perPhaseStreamsP_lt_slowStreamsP hn heps heps1).le

/-! ## Step 2 — the overhead envelope at the smaller stream count

`Ttc.CVSlowActualCostEnvelope.slowActualOverhead n R2 epsP p Lenv Tenv` is
`max 1 (slowActualRetainedRealEnvelope (slowPhasesP n R2 + 1) (slowStreamsP n R2 epsP) Lenv Tenv)`.
The definition below is that expression with `slowStreamsP` replaced by `perPhaseStreamsP`,
and nothing else changed.  **This is the one place where the smaller stream count enters
the stated envelope.**  Because the underlying retained envelope
`Ttc.CVSlowActualCostEnvelope.slowActualRetainedRealEnvelope` is `k · m · 10 · Lenv · Tenv ·
2e` — linear in `k` — the saving is transmitted to the overhead with no loss. -/

set_option linter.unusedVariables false in
/-- **The overhead envelope of the slow schedule at the `n`-aware stream count.**  A
drop-in replacement for `Ttc.CVSlowActualCostEnvelope.slowActualOverhead n R2 epsP p Lenv
Tenv`, differing from it in exactly one argument: `perPhaseStreamsP` in place of
`Ttc.CVSlowEffectiveOverhead.slowStreamsP`. -/
noncomputable def slowPerPhaseOverhead
    (n : Nat) (R2 epsP p : Real) (Lenv Tenv : Real) : Real :=
  max 1 (slowActualRetainedRealEnvelope (slowPhasesP n R2 + 1) (perPhaseStreamsP n R2 epsP)
    Lenv Tenv)

theorem one_le_slowPerPhaseOverhead (n : Nat) (R2 epsP p Lenv Tenv : Real) :
    1 ≤ slowPerPhaseOverhead n R2 epsP p Lenv Tenv := le_max_left _ _

theorem slowPerPhaseOverhead_nonneg (n : Nat) (R2 epsP p Lenv Tenv : Real) :
    0 ≤ slowPerPhaseOverhead n R2 epsP p Lenv Tenv :=
  zero_le_one.trans (one_le_slowPerPhaseOverhead n R2 epsP p Lenv Tenv)

/-- **The payoff of P2 on the retained scalar, quantified.**  At the same per-phase retry
and deadline envelopes the retained-scalar envelope of the per-phase route is smaller than
the uniform one by the full factor `n / 3`. -/
theorem nmul_slowPerPhaseRetained_le_three_slowActualRetained
    {n : Nat} {R2 epsP Lenv Tenv : Real} (hn : 0 < n)
    (heps : 0 < epsP) (heps1 : epsP ≤ 1)
    (hLenv : 0 ≤ Lenv) (hTenv : 0 ≤ Tenv) :
    (n : Real) * slowActualRetainedRealEnvelope (slowPhasesP n R2 + 1)
        (perPhaseStreamsP n R2 epsP) Lenv Tenv ≤
      3 * slowActualRetainedRealEnvelope (slowPhasesP n R2 + 1)
        (slowStreamsP n R2 epsP) Lenv Tenv := by
  have hsave := nmul_perPhaseStreamsP_le_three_slowStreamsP
    (n := n) (R2 := R2) (eps := epsP) hn heps heps1
  have hm0 : (0 : Real) ≤ ((slowPhasesP n R2 + 1 : Nat) : Real) := by positivity
  have he0 : (0 : Real) ≤ 2 * Real.exp 1 := by positivity
  have hrest : (0 : Real) ≤ ((slowPhasesP n R2 + 1 : Nat) : Real) * 10 * Lenv * Tenv *
      (2 * Real.exp 1) := by positivity
  unfold slowActualRetainedRealEnvelope
  calc
    (n : Real) * ((perPhaseStreamsP n R2 epsP : Real) *
          ((slowPhasesP n R2 + 1 : Nat) : Real) * 10 * Lenv * Tenv * (2 * Real.exp 1))
        = ((n : Real) * (perPhaseStreamsP n R2 epsP : Real)) *
          (((slowPhasesP n R2 + 1 : Nat) : Real) * 10 * Lenv * Tenv *
            (2 * Real.exp 1)) := by ring
    _ ≤ (3 * (slowStreamsP n R2 epsP : Real)) *
          (((slowPhasesP n R2 + 1 : Nat) : Real) * 10 * Lenv * Tenv *
            (2 * Real.exp 1)) := mul_le_mul_of_nonneg_right hsave hrest
    _ = 3 * ((slowStreamsP n R2 epsP : Real) *
          ((slowPhasesP n R2 + 1 : Nat) : Real) * 10 * Lenv * Tenv *
            (2 * Real.exp 1)) := by ring

/-- **The payoff of P2 on the overhead.**  At the same per-phase envelopes the per-phase
overhead never exceeds the uniform one. -/
theorem slowPerPhaseOverhead_le_slowActualOverhead
    {n : Nat} {R2 epsP p Lenv Tenv : Real} (hn : 4 ≤ n)
    (heps : 0 < epsP) (heps1 : epsP ≤ 1)
    (hLenv : 0 ≤ Lenv) (hTenv : 0 ≤ Tenv) :
    slowPerPhaseOverhead n R2 epsP p Lenv Tenv ≤
      slowActualOverhead n R2 epsP p Lenv Tenv := by
  unfold slowPerPhaseOverhead slowActualOverhead
  refine max_le_max (le_refl 1) ?_
  exact slowActualRetainedRealEnvelope_mono (le_refl _)
    (perPhaseStreamsP_le_slowStreamsP hn heps heps1)
    hLenv hTenv (le_refl _) (le_refl _)

/-! ## Step 3 — the cost-side binder at the per-phase overhead

The mirror of `Ttc.CVSlowActualCostEnvelope.slowActual_hscalar`, with the stream-count
bound taken at `perPhaseStreamsP`.  Nothing else changes: the cost layer is pure
bookkeeping over `(Lenv, Tenv)` and is entirely parametric in the stream count. -/

/-- **The frontier's `hscalar` binder at the per-phase overhead.**  This is
`Ttc.CVSlowActualCostEnvelope.slowActual_hscalar` with
`hk : k ≤ perPhaseStreamsP n R2 epsP` in place of `hk : k ≤ slowStreamsP n R2 epsP`, and
`runtimeConstant := slowPerPhaseOverhead n R2 epsP p Lenv Tenv`. -/
theorem slowPerPhase_hscalar
    (n : Nat) (hn : 1 ≤ n) {m k L T : Nat} {R requested R2 epsP p Lenv Tenv : Real}
    (hreq : 0 < requested) (hreq1 : requested < 1)
    (hm : m ≤ slowPhasesP n R2) (hk : k ≤ perPhaseStreamsP n R2 epsP)
    (hL : (L : Real) ≤ Lenv) (hT : (T : Real) ≤ Tenv)
    (hLenv : 0 ≤ Lenv) (hTenv : 0 ≤ Tenv) :
    (k : ENNReal) * (m : ENNReal) * ENNReal.ofReal
        (10 * (L : Real) * (T : Real) * (2 * Real.exp 1)) ≤
      sourceOneRunQueryBudget (slowPerPhaseOverhead n R2 epsP p Lenv Tenv) n R requested := by
  have hk0 : (0 : Real) ≤ (k : Real) := by positivity
  have hm0 : (0 : Real) ≤ (m : Real) := by positivity
  have hreal := slowActualRetainedScalar_le_realEnvelope
    (m := m) (k := k) (L := L) (T := T) (Lenv := Lenv) (Tenv := Tenv)
    hL hT hLenv hTenv
  have hmono := slowActualRetainedRealEnvelope_mono
    (m := m) (m' := slowPhasesP n R2 + 1) (k := k) (k' := perPhaseStreamsP n R2 epsP)
    (Lenv := Lenv) (Lenv' := Lenv) (Tenv := Tenv) (Tenv' := Tenv)
    (hm.trans (Nat.le_succ _)) hk hLenv hTenv (le_refl _) (le_refl _)
  have hover : (k : Real) * (m : Real) *
      (10 * (L : Real) * (T : Real) * (2 * Real.exp 1)) ≤
      slowPerPhaseOverhead n R2 epsP p Lenv Tenv := by
    refine hreal.trans (hmono.trans ?_)
    exact le_max_right _ _
  have hcore : slowPerPhaseOverhead n R2 epsP p Lenv Tenv ≤
      sourceOneRunQueryEnvelope (slowPerPhaseOverhead n R2 epsP p Lenv Tenv) n R requested :=
    le_sourceOneRunQueryEnvelope_of_le hn hreq hreq1
      (slowPerPhaseOverhead_nonneg n R2 epsP p Lenv Tenv)
  unfold sourceOneRunQueryBudget
  rw [← ENNReal.ofReal_natCast k, ← ENNReal.ofReal_natCast m,
    ← ENNReal.ofReal_mul hk0, ← ENNReal.ofReal_mul (mul_nonneg hk0 hm0)]
  exact ENNReal.ofReal_le_ofReal (hover.trans hcore)

/-! ## Step 4 — the `OV` and the `heff` pair

`Ttc.TtcSlowRuntimeSharp.slowSharpOV n R2 eps p` is

```
64 * (max 1 eps) ^ 2 * sourceLogFactor n ^ 2 *
  slowActualOverhead n R2 (min eps 1 / 2) p
    (slowSharpLenv n R2 (min eps 1 / 2)) (slowSharpTenv n R2 (min eps 1 / 2)).
```

`slowPerPhaseOV` below is that expression with `slowActualOverhead` replaced by
`slowPerPhaseOverhead` — i.e. with the **smaller stream count in the envelope** — and with
every other slot, including the two per-phase envelopes, untouched.  See the module
docstring for why the two envelope slots are still the sharp route's: no per-phase
`hsteps` / `hretries` pair exists against a schedule with a correct mixing slack, so
substituting the per-phase caps here would advertise an envelope nothing proves. -/

/-- **The overhead envelope of the combined P1 + P2 route**, at the sharp per-phase retry
and deadline envelopes.  Identical to `Ttc.TtcSlowRuntimeSharp.slowSharpOV` except for the
stream count of the retained-scalar envelope. -/
noncomputable def slowPerPhaseOV (n : Nat) (R2 eps p : Real) : Real :=
  64 * (max 1 eps) ^ 2 * sourceLogFactor n ^ 2 *
    slowPerPhaseOverhead n R2 (min eps 1 / 2) p
      (slowSharpLenv n R2 (min eps 1 / 2)) (slowSharpTenv n R2 (min eps 1 / 2))

/-- The per-input effective runtime constant, at the interior circumradius — the radius
`Ttc.TtcCallCircumAdmissible.cvAdmCircum` declares. -/
noncomputable def slowPerPhaseEffective (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) : Real :=
  slowPerPhaseOV n ((circumR (interior a.1)) ^ 2) a.2.1 a.2.2

theorem one_le_slowPerPhaseOV (n : Nat) (R2 eps p : Real) : 1 ≤ slowPerPhaseOV n R2 eps p := by
  unfold slowPerPhaseOV
  have h1 : (1 : Real) ≤ (max 1 eps) ^ 2 := by
    have := le_max_left (1 : Real) eps
    nlinarith
  have h2 : (1 : Real) ≤ sourceLogFactor n ^ 2 := by
    have := one_le_sourceLogFactor (n : Real)
    nlinarith
  have h3 : (1 : Real) ≤ slowPerPhaseOverhead n R2 (min eps 1 / 2) p
      (slowSharpLenv n R2 (min eps 1 / 2)) (slowSharpTenv n R2 (min eps 1 / 2)) :=
    one_le_slowPerPhaseOverhead _ _ _ _ _ _
  have h64 : (1 : Real) ≤ 64 * (max 1 eps) ^ 2 := by nlinarith
  have h641 : (1 : Real) ≤ 64 * (max 1 eps) ^ 2 * sourceLogFactor n ^ 2 := by nlinarith
  nlinarith

theorem slowPerPhaseOV_nonneg (n : Nat) (R2 eps p : Real) : 0 ≤ slowPerPhaseOV n R2 eps p :=
  zero_le_one.trans (one_le_slowPerPhaseOV n R2 eps p)

theorem slowPerPhaseEffective_nonneg (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    0 ≤ slowPerPhaseEffective n a := slowPerPhaseOV_nonneg _ _ _ _

/-- **The `heff` binder of the generic consumer, at `Adm := cvAdmCircum`**, in the exact
shape `Ttc.TtcShapedRuntime.implementationOfEffectiveCertificatesGen` asks for. -/
theorem slowPerPhaseEffective_le_slowPerPhaseOV
    (n : Nat) (K : Set (Ttc.Space n)) (eps p R2 : Real)
    (hK : cvAdmCircum n K R2) :
    slowPerPhaseEffective n (K, eps, p) ≤ slowPerPhaseOV n R2 eps p := by
  show slowPerPhaseOV n ((circumR (interior K)) ^ 2) eps p ≤ slowPerPhaseOV n R2 eps p
  rw [hK.2]

/-! ## Step 5 — the relationship the capstone would have stated -/

/-- **`slowPerPhaseOV ≤ slowSharpOV`.**  The two differ in exactly one argument — the
stream count of the retained-scalar envelope — and
`nmul_slowPerPhaseRetained_le_three_slowActualRetained` says that argument is smaller by
the factor `n / 3`.  The hypothesis `hnm` is the phase-count side condition of
`Ttc.CVPerPhaseSamples.perPhaseRuntimeSamples_saving`. -/
theorem slowPerPhaseOV_le_slowSharpOV
    {n : Nat} {R2 eps p : Real} (hn : 4 ≤ n) (heps : 0 < eps) :
    slowPerPhaseOV n R2 eps p ≤ slowSharpOV n R2 eps p := by
  have hb0 : (0 : Real) < min eps 1 / 2 := by
    have : (0 : Real) < min eps 1 := lt_min heps (by norm_num)
    linarith
  have hb1 : min eps 1 / 2 ≤ 1 := by
    have : min eps 1 ≤ 1 := min_le_right _ _
    linarith
  have hLenv0 : (0 : Real) ≤ slowSharpLenv n R2 (min eps 1 / 2) := by
    unfold slowSharpLenv
    positivity
  have hTenv0 : (0 : Real) ≤ slowSharpTenv n R2 (min eps 1 / 2) := by
    unfold slowSharpTenv
    have := Ttc.CVSharpSlowSteps.slowSharpStepsEnvelope_nonneg
      (n := n) (m := slowPhasesP n R2) (k := slowStreamsP n R2 (min eps 1 / 2))
      (q := Ttc.TtcSlowRuntimeUnconditional.slowUncQ n R2 (min eps 1 / 2))
      (epsP := min eps 1 / 2) (R := Real.sqrt R2) (by omega) hb0
    linarith
  have hover := slowPerPhaseOverhead_le_slowActualOverhead
    (n := n) (R2 := R2) (epsP := min eps 1 / 2) (p := p)
    (Lenv := slowSharpLenv n R2 (min eps 1 / 2))
    (Tenv := slowSharpTenv n R2 (min eps 1 / 2))
    hn hb0 hb1 hLenv0 hTenv0
  have hpre : (0 : Real) ≤ 64 * (max 1 eps) ^ 2 * sourceLogFactor n ^ 2 := by
    have h1 : (0 : Real) ≤ (max 1 eps) ^ 2 := sq_nonneg _
    have h2 : (0 : Real) ≤ sourceLogFactor n ^ 2 := sq_nonneg _
    positivity
  unfold slowPerPhaseOV slowSharpOV
  exact mul_le_mul_of_nonneg_left hover hpre

section AxiomCheck

#print axioms perPhaseStreamsP
#print axioms perPhaseStreamsP_pos
#print axioms n_le_slowPhasesP_add_one
#print axioms nmul_perPhaseStreamsP_le_three_slowStreamsP
#print axioms perPhaseStreamsP_eq
#print axioms slowStreamsP_eq
#print axioms perPhaseStreamsP_lt_slowStreamsP
#print axioms perPhaseStreamsP_le_slowStreamsP
#print axioms slowPerPhaseOverhead
#print axioms one_le_slowPerPhaseOverhead
#print axioms slowPerPhaseOverhead_nonneg
#print axioms slowPerPhaseOV_nonneg
#print axioms slowPerPhaseEffective
#print axioms slowPerPhaseEffective_nonneg
#print axioms nmul_slowPerPhaseRetained_le_three_slowActualRetained
#print axioms slowPerPhaseOverhead_le_slowActualOverhead
#print axioms slowPerPhase_hscalar
#print axioms slowPerPhaseOV
#print axioms one_le_slowPerPhaseOV
#print axioms slowPerPhaseEffective_le_slowPerPhaseOV
#print axioms slowPerPhaseOV_le_slowSharpOV

end AxiomCheck

end Ttc.TtcSlowRuntimePerPhase
