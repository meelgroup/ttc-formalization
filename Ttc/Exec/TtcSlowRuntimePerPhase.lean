import Ttc.Exec.TtcSlowRuntimeSharp
import Ttc.Exec.CVPerPhaseFrontier

/-!
# The **per-phase** unconditional TTC runtime capstone for the slow canonical volume route

`Ttc/Exec/TtcSlowRuntimeSharp.lean` carries the same assembly at the **sharp** pair

* `slack := Ttc.CVSharpUniformParameters.slowSharpSlack n m K` (`… / 6`),
* `boundSq := Ttc.CVSharpScoreTransport.slowSharpBoundSq n R`,
* `k := Ttc.CVCorrectedRuntime.correctedRuntimeSamples (slowPhases n a) (slowEpsInt n a)`,
* `q := Ttc.CVSlowCanonicalUniformParameters.slowUniformQ …`.

This file redoes the assembly at the **combined P1 + P2** pair

* `slack := Ttc.CVPerPhaseFrontier.perPhaseSlack n m K` — the `relativePhase` slack at
  `C = 1 + 2/n`, divided by `6`,
* `boundSq := Ttc.CVPerPhaseFrontier.perPhaseBoundSqGen n (perPhaseExpSharp n R)` — the
  P1-sharp transport exponent `exp (R²/(2 σ_i (n+1)))`,
* `k := Ttc.CVPerPhaseSamples.perPhaseRuntimeSamples n (slowPhases n a) (slowEpsInt n a)` —
  the `n`-aware stream count, a factor `n / 3` below `correctedRuntimeSamples`
  (`nmul_perPhaseStreamsP_le_three_slowStreamsP` below),
* `q := Ttc.CVPerPhaseFrontier.perPhaseQ …` — the `n`-aware truncation radius the repaired
  mean-tail floor forces (a `+ 4 log n / n` in `q²`, i.e. logarithmic).

## Main result

`ttc_volume_runtime_perPhase` — the third unconditional runtime capstone.  There is no
oracle binder, no certificate binder, no implementation binder and **no cost-side binder**;
the volume subroutine is `slowPerPhaseImplementation.algorithm n`, which appears in the
statement with no arguments.

## Which envelope the capstone states

The capstone's cost envelope is `slowPerPhaseOV`, which differs from
`Ttc.TtcSlowRuntimeSharp.slowSharpOV` in **three** places, all of them per-phase:

* the stream count of the retained-scalar envelope is `perPhaseStreamsP`, not
  `Ttc.CVSlowEffectiveOverhead.slowStreamsP` (this is `slowPerPhaseOverhead`);
* the retry envelope slot is `perPhaseLenv`, i.e.
  `Ttc.CVPerPhaseFrontier.perPhaseRetriesCapAt` at the per-phase share floor and the
  per-phase stream count, not `Ttc.TtcSlowRuntimeSharp.slowSharpLenv`;
* the deadline envelope slot is `perPhaseTenv`, i.e.
  `Ttc.CVPerPhaseFrontier.perPhaseStepsEnvelope` at the `n`-aware radius `perPhaseQ`, not
  `Ttc.TtcSlowRuntimeSharp.slowSharpTenv`.

All three are the quantities the per-phase analysis itself produces, so the frontier's
`hsteps`, `hretries` and `hscalar` binders are discharged outright and nothing is assumed.

## READ THIS BEFORE CITING `slowPerPhaseOV` OR `slowPerPhaseOverhead`

The earlier version of this file carried a warning that `slowPerPhaseOV` was a *declared
envelope, not a runtime bound*, because no per-phase retry or deadline chain existed
against a schedule with a correct mixing slack.  That is no longer the situation, and the
warning is replaced by the precise statement of what is and is not certified:

* **`slowPerPhaseOV n R2 eps p` — certified.**  `ttc_volume_runtime_perPhase` bounds the
  expected query cost of the real run at exactly this constant (per cube, at that cube's
  own interior circumradius squared).  It is `slowPerPhaseOVGen` at the two *per-phase*
  envelope slots, and at no other pair.
* **`slowPerPhaseOverhead n R2 epsP p Lenv Tenv` and `slowPerPhaseOVGen` — declared, at a
  general `(Lenv, Tenv)`.**  They are parametric in the retry and deadline envelopes, and
  nothing is claimed to run within them at an arbitrary pair.  Only the instantiation
  `Lenv := perPhaseLenv`, `Tenv := perPhaseTenv` — that is, `slowPerPhaseOV` — is a
  statement about a run.
* **`slowPerPhaseOVGen_sharpEnv_le_slowSharpOV` — a comparison of two declared envelopes.**
  It says that the per-phase *overhead* (the smaller stream count) beats the sharp one at
  the sharp route's own `(Lenv, Tenv)`.  It is **not** `slowPerPhaseOV ≤ slowSharpOV`: the
  capstone's `slowPerPhaseOV` sits at the per-phase envelopes, and no comparison of
  `perPhaseLenv` with `slowSharpLenv` or of `perPhaseTenv` with `slowSharpTenv` is proved
  here — the two chains run at different share floors and different truncation radii, and
  relating them is a separate question this file does not answer.  So the honest summary of
  the quantified payoff remains `nmul_slowPerPhaseRetained_le_three_slowActualRetained`: a
  factor `n / 3` in the retained scalar **at a common `(Lenv, Tenv)`**.

## What had to be mirrored, and what did not

`Ttc.CVSlowTotalFamilies.slowLaw` writes the loose slack / transport pair *inside* the
`slowCanonicalCostedActiveSchedule` term and pins the index type at
`Ttc.CVSlowTotalFamilies.slowStreams`, so both the law and the four total families had to
be mirrored here: `perPhaseStreams`, `perPhaseOmega`, `perPhaseCost`, `perPhaseValue`,
`perPhaseLaw`, `perPhaseLaw_of_valid` and their clipped versions, together with the two
Markov instances `perPhaseIsMarkovKernel_costedSchedule` / `_activeSchedule`.  This is one
layer more than `Ttc.TtcSlowRuntimeSharp` needed, because that file reuses
`Ttc.CVSlowTotalFamilies`' index type — which is only possible at the uniform stream count.

`Ttc.TtcSlowRuntimeFinal.clipInput` and the accuracy-clip arithmetic are reused verbatim.

## The one arithmetic fact the smaller stream count forced

`Ttc.CVSlowAccuracyStrict.slowAccuracyRequested_half_lt_one` and
`Ttc.CVSlowCanonicalAccuracyBudget.slowAccuracyRequested_le_of_half` are stated at
`k := correctedRuntimeSamples m eps` and are therefore unusable at the per-phase count.
§4 below re-proves both **generically in `k`** — `scoreAwareMeanGamma_le_div_hundred` holds
for *every* stream count, because `Ttc.CVCorrected.correctedNu m eps` divides by
`correctedAlpha m eps ^ 4 ≥ (100000 (m+1) / eps²) ^ 4`, which already dominates the whole
aggregate mean budget before a single sample is drawn.  The existing `k`-pinned proofs
throw that factor away (`1 ≤ a ^ 4`) and spend the sample count instead; keeping it makes
the bound `k`-free, and the per-phase route pays nothing in accuracy for its `n`-fold
smaller `k`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Ttc.TtcSlowRuntimePerPhase

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.GaussianCooling
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
open Ttc.TtcCallCircumAdmissible (cvAdmCircum cvAdmCircum_imp_cvAdmissible
  circumInterior_sq_le_of_cvAdmCircum cvAdmCircum_callBody)
open Ttc.TtcSlowRuntimeFinal (clipInput clipInput_valid clipInput_eps_pos
  one_le_sourceLogFactor sourceOneRunQueryBudget_clip_eps)
open Ttc.TtcSlowRuntimeSharp (slowSharpLenv slowSharpTenv slowSharpOV)
open Ttc.CVEffectiveTotalise (CVValidInput)
open Ttc.CVSlowTotalFamilies
open Ttc.CVSlowOneRunValid
open Ttc.CVSlowCanonicalRetainedReference
open Ttc.CVHeterogeneousRetainedPathLaw
open Ttc.CVHeterogeneousHistoryReference
open Ttc.CVSourceReferenceTVCapstone
open Ttc.CVGaussianHybridWeightedCertificate (gaussianScorePrefixReadout
  measurable_gaussianScorePrefixReadout)
open Ttc.CVSlowFullBodySourceSchedule (slowSourceSigmaSq)
open Ttc.CVSlowSourceReferenceCertificate (slowInitialPair slowReferenceWarm
  slowSourceInitialVariance)
open Ttc.CVSlowRadiusQCanonicalOperational (slowCanonicalSteps)
open Ttc.CVGaussianScoreAwareParameters (scoreAwareRetries scoreAwareEta scoreAwareZeta)
open Ttc.CVSlowCanonicalAccuracyBudget (slowAccuracyRequested
  phase_div_two_correctedAlpha_le scoreAwareAccuracyBeta_nonneg)
open Ttc.CVSlowAccuracyStrict (slowAccuracyRequested_half_pos
  half_le_slowAccuracyRequested)
open Ttc.CVCorrected (correctedAlpha correctedAlpha_pos correctedNu correctedNu_nonneg
  one_le_correctedAlpha)
open Ttc.CVGaussianBlockRetryParameters (blockShare blockShare_pos)
open Ttc.CVGaussianScoreAwareMeanBudget (scoreAwareMeanEta scoreAwareMeanGamma
  scoreAwareAccuracyBeta scoreAwareMeanGamma_nonneg)
open Ttc.CVPerPhaseFrontier
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

/-! ## Step 4 — the realised accuracy at an arbitrary stream count

`Ttc.CVSlowAccuracyStrict.slowAccuracyRequested_half_lt_one` and
`Ttc.CVSlowCanonicalAccuracyBudget.slowAccuracyRequested_le_of_half` are the two facts the
final weakening needs, and both are stated at `k := correctedRuntimeSamples m eps`.  At the
`n`-aware stream count they are unavailable, and they cannot be obtained by monotonicity:
the aggregate mean budget grows as `k` shrinks.

They are nevertheless true at **every** `k`, and the reason is that the existing proofs are
lossy at exactly one step.  `Ttc.CVCorrected.correctedNu m eps =
eps² / (100000 · correctedAlpha m eps ^ 4 · (m+1))` with
`correctedAlpha m eps = 100000 (m+1) / eps² ≥ 100000 (m+1)`; the canonical proof bounds
`correctedAlpha ^ 4` below by `1` and recovers the missing factor from
`k ≥ 100000 (m+1) / eps²`.  Keeping `correctedAlpha ^ 4 ≥ correctedAlpha ≥ 100000 (m+1)`
instead gives the *same* final bound `blockShare ≤ eps² / (8·10¹⁰ (m+1)²)` with no
constraint on `k` at all. -/

/-- **The aggregate mean bias is negligible at every stream count.**  `k`-generic form of
`Ttc.CVGaussianScoreAwareMeanBudget.scoreAwareMeanGamma_corrected_le_div_hundred`. -/
theorem scoreAwareMeanGamma_le_div_hundred (m k : Nat) {eps : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    scoreAwareMeanGamma m k eps ≤ eps / 100 := by
  have hx0 : (0 : Real) ≤ (m : Real) := Nat.cast_nonneg m
  have hk0 : (0 : Real) ≤ (k : Real) := Nat.cast_nonneg k
  have hm1 : (0 : Real) < (m : Real) + 1 := by linarith
  have hk1 : (1 : Real) ≤ (k : Real) + 1 := by linarith
  have he2 : eps ^ 2 ≤ 1 := by nlinarith
  have ha1 : (1 : Real) ≤ correctedAlpha m eps := one_le_correctedAlpha heps heps1
  have halow : 100000 * ((m : Real) + 1) ≤ correctedAlpha m eps := by
    unfold correctedAlpha
    rw [le_div_iff₀ (by positivity : (0 : Real) < eps ^ 2)]
    nlinarith
  have hA3 : (1 : Real) ≤ correctedAlpha m eps ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.2 ha1)
      (show (0 : Real) ≤ correctedAlpha m eps ^ 2 + correctedAlpha m eps + 1 by positivity)]
  have ha4 : correctedAlpha m eps ≤ correctedAlpha m eps ^ 4 := by
    nlinarith [mul_nonneg (le_trans zero_le_one ha1) (sub_nonneg.2 hA3)]
  have haden : 100000 * ((m : Real) + 1) ≤ correctedAlpha m eps ^ 4 := halow.trans ha4
  have hb0 : (0 : Real) ≤ blockShare m k eps := (blockShare_pos heps).le
  have hbase : (80000000000 : Real) * ((m : Real) + 1) ^ 2 ≤
      100000 * correctedAlpha m eps ^ 4 * ((m : Real) + 1) * 8 := by
    nlinarith [haden, hm1]
  have hC0 : (0 : Real) ≤ 100000 * correctedAlpha m eps ^ 4 * ((m : Real) + 1) * 8 := by
    positivity
  have hstep : (80000000000 : Real) * ((m : Real) + 1) ^ 2 ≤
      (100000 * correctedAlpha m eps ^ 4 * ((m : Real) + 1)) * (8 * ((k : Real) + 1)) := by
    calc (80000000000 : Real) * ((m : Real) + 1) ^ 2
        ≤ 100000 * correctedAlpha m eps ^ 4 * ((m : Real) + 1) * 8 := hbase
      _ = (100000 * correctedAlpha m eps ^ 4 * ((m : Real) + 1) * 8) * 1 := by ring
      _ ≤ (100000 * correctedAlpha m eps ^ 4 * ((m : Real) + 1) * 8) * ((k : Real) + 1) :=
          mul_le_mul_of_nonneg_left hk1 hC0
      _ = (100000 * correctedAlpha m eps ^ 4 * ((m : Real) + 1)) *
            (8 * ((k : Real) + 1)) := by ring
  have hb : blockShare m k eps ≤ eps ^ 2 / (80000000000 * ((m : Real) + 1) ^ 2) := by
    unfold blockShare correctedNu
    rw [div_div]
    exact div_le_div_of_nonneg_left (sq_nonneg eps) (by positivity) hstep
  have hetaSq : (scoreAwareMeanEta m k eps) ^ 2 = (7 / 5 : Real) * blockShare m k eps := by
    unfold scoreAwareMeanEta
    rw [Real.sq_sqrt]
    exact mul_nonneg (by norm_num) hb0
  have hgamma0 := scoreAwareMeanGamma_nonneg m k eps
  have hsmall : 4 * (m : Real) ^ 2 * ((7 / 5 : Real) * blockShare m k eps) ≤
      eps ^ 2 / 10000 := by
    calc
      4 * (m : Real) ^ 2 * ((7 / 5 : Real) * blockShare m k eps) ≤
          4 * ((m : Real) + 1) ^ 2 *
            ((7 / 5 : Real) * (eps ^ 2 / (80000000000 * ((m : Real) + 1) ^ 2))) := by
        gcongr
        nlinarith
      _ = (28 / 400000000000 : Real) * eps ^ 2 := by
        field_simp [show ((m : Real) + 1) ≠ 0 by positivity]
        <;> ring
      _ ≤ eps ^ 2 / 10000 := by
        have := sq_nonneg eps
        nlinarith
  have hgammaSq : (scoreAwareMeanGamma m k eps) ^ 2 ≤ (eps / 100) ^ 2 := by
    calc
      (scoreAwareMeanGamma m k eps) ^ 2 =
          4 * (m : Real) ^ 2 * ((7 / 5 : Real) * blockShare m k eps) := by
        rw [scoreAwareMeanGamma, mul_pow, mul_pow, hetaSq]
        ring
      _ ≤ eps ^ 2 / 10000 := hsmall
      _ = (eps / 100) ^ 2 := by ring
  nlinarith [sq_nonneg (scoreAwareMeanGamma m k eps + eps / 100)]

/-- **The score-aware allowance costs at most a quarter of the accuracy, at every stream
count.**  `k`-generic form of
`Ttc.CVSlowCanonicalAccuracyBudget.scoreAwareAccuracyBeta_canonical_le`. -/
theorem scoreAwareAccuracyBeta_le_quarter (m k : Nat) {eps : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    scoreAwareAccuracyBeta m k eps ≤ eps / 4 := by
  have htheta : (m : Real) / (2 * correctedAlpha m eps) ≤ eps ^ 2 / 200000 :=
    phase_div_two_correctedAlpha_le m heps
  have halpha : 0 < correctedAlpha m eps := correctedAlpha_pos heps
  have htheta0 : 0 ≤ (m : Real) / (2 * correctedAlpha m eps) :=
    div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hgamma : scoreAwareMeanGamma m k eps ≤ eps / 8 := by
    have := scoreAwareMeanGamma_le_div_hundred m k heps heps1
    linarith
  have hgamma0 : 0 ≤ scoreAwareMeanGamma m k eps := scoreAwareMeanGamma_nonneg m k eps
  have hprod : ((m : Real) / (2 * correctedAlpha m eps)) * scoreAwareMeanGamma m k eps ≤
      (eps ^ 2 / 200000) * (eps / 8) :=
    mul_le_mul htheta hgamma hgamma0 (by positivity)
  have hsq : eps ^ 2 ≤ eps := by nlinarith
  have hcube : eps ^ 2 * eps ≤ eps := by nlinarith
  unfold scoreAwareAccuracyBeta
  calc
    (m : Real) / (2 * correctedAlpha m eps) + scoreAwareMeanGamma m k eps +
        ((m : Real) / (2 * correctedAlpha m eps)) * scoreAwareMeanGamma m k eps ≤
        eps ^ 2 / 200000 + eps / 8 + (eps ^ 2 / 200000) * (eps / 8) := by
      gcongr
    _ ≤ eps / 4 := by nlinarith

/-- **The realised accuracy is strictly below one, at every stream count.**  `k`-generic
form of `Ttc.CVSlowAccuracyStrict.slowAccuracyRequested_half_lt_one`. -/
theorem slowAccuracyRequested_half_lt_one_any (m k : Nat) {epsIn : Real}
    (heps : 0 < epsIn) (heps1 : epsIn ≤ 1) :
    slowAccuracyRequested m k (epsIn / 2) < 1 := by
  have hhalf : (0 : Real) < epsIn / 2 := by linarith
  have hb := scoreAwareAccuracyBeta_le_quarter m k (eps := epsIn / 2) hhalf (by linarith)
  have hb0 := scoreAwareAccuracyBeta_nonneg m k hhalf
  unfold slowAccuracyRequested
  nlinarith

/-- **The realised accuracy meets the external request, at every stream count.**
`k`-generic form of
`Ttc.CVSlowCanonicalAccuracyBudget.slowAccuracyRequested_le_of_half`. -/
theorem slowAccuracyRequested_half_le_any (m k : Nat) {epsIn : Real}
    (heps : 0 < epsIn) (heps1 : epsIn ≤ 1) :
    slowAccuracyRequested m k (epsIn / 2) ≤ epsIn := by
  have hhalf : (0 : Real) < epsIn / 2 := by linarith
  have hb := scoreAwareAccuracyBeta_le_quarter m k (eps := epsIn / 2) hhalf (by linarith)
  have hb0 := scoreAwareAccuracyBeta_nonneg m k hhalf
  unfold slowAccuracyRequested
  nlinarith

/-! ## Step 5 — the four total families at the per-phase stream count

`Ttc.CVSlowTotalFamilies.slowOmega` is `Fin (slowStreams n a) → …`, so it is pinned at the
uniform stream count and cannot be reused.  These are its four families verbatim with
`slowStreams` replaced by `perPhaseStreams`. -/

/-- The per-phase stream count at a concrete input. -/
noncomputable def perPhaseStreams (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) : Nat :=
  perPhaseRuntimeSamples n (slowPhases n a) (slowEpsInt n a)

theorem perPhaseStreams_pos (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    0 < perPhaseStreams n a := perPhaseRuntimeSamples_pos _ _ _

theorem perPhaseStreams_eq (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    perPhaseStreams n a = perPhaseStreamsP n (slowR2 n a) (slowEpsInt n a) := rfl

/-- **The index type of one per-phase run**: `perPhaseStreams n a` independent
heterogeneous retained histories. -/
abbrev perPhaseOmega (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) : Type :=
  Fin (perPhaseStreams n a) → HeterogeneousHistoryState (Ttc.Space n) (Ttc.Space n)

/-- The recorded query cost of one per-phase run. -/
noncomputable def perPhaseCost (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    perPhaseOmega n a → ENNReal :=
  fun omega ↦ ∑ j, (omega j).1.1

/-- The volume estimate one per-phase run reports. -/
noncomputable def perPhaseValue (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    perPhaseOmega n a → Real :=
  fun omega ↦ gaussianScorePrefixReadout (slowPhases n a) (slowPhases n a)
    (perPhaseStreams n a) (slowSourceSigmaSq n (slowSourceInitialVariance n))
    (interior a.1)
    (chain (slowPhases n a) (slowSourceSigmaSq n (slowSourceInitialVariance n))
      (interior a.1) 0)
    (independentStoredScorePrefixCurrent (slowPhases n a) omega)

theorem measurable_perPhaseCost (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    Measurable (perPhaseCost n a) := by
  unfold perPhaseCost
  apply Finset.measurable_sum
  intro j _hj
  exact measurable_fst.comp (measurable_fst.comp (measurable_pi_apply j))

theorem measurable_perPhaseValue (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    Measurable (perPhaseValue n a) :=
  (measurable_gaussianScorePrefixReadout _).comp
    (measurable_independentStoredScorePrefixCurrent _)

/-! ## Step 6 — the law family at the per-phase pair -/

/-- The canonical **seed** schedule at the per-phase pair is Markov. -/
theorem perPhaseIsMarkovKernel_activeSchedule {n : Nat}
    (hn : 21 ≤ n) {eps R R2 : Real} {K : Set (Ttc.Space n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : Ttc.Space n) 1 ⊆ K) (i : Nat) :
    IsMarkovKernel (slowCanonicalActiveSchedule (by omega : 1 ≤ n)
      (slowCanonicalPhases n R2 + 1)
      (perPhaseRuntimeSamples n (slowCanonicalPhases n R2) eps)
      (q := perPhaseQ n (slowCanonicalPhases n R2)
        (perPhaseRuntimeSamples n (slowCanonicalPhases n R2) eps) eps R)
      (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (perPhase_canonical_hq0 hn R2 eps R) (canonical_hs0 hn) K hK 0 slowReferenceWarm
      (perPhaseSlack n (slowCanonicalPhases n R2) K)
      (perPhaseBoundSqGen n (perPhaseExpSharp n R)) i) := by
  letI : ∀ j, IsProbabilityMeasure (slowStationaryTail n
      (perPhaseQ n (slowCanonicalPhases n R2)
        (perPhaseRuntimeSamples n (slowCanonicalPhases n R2) eps) eps R)
      (slowSourceInitialVariance n) K j) := fun j ↦
    perPhase_canonical_isProbabilityMeasure_slowStationaryTail hn hK hKc hball j
  infer_instance

/-- The canonical **costed** active schedule at the per-phase pair is Markov, at the
parameter choices of `Ttc.CVSlowTotalFamilies` and the per-phase stream count. -/
theorem perPhaseIsMarkovKernel_costedSchedule {n : Nat}
    {a : Ttc.CVAdaptive.VolumeInput n} (h : CVValidInput a) (hn : 21 ≤ n) (i : Nat) :
    IsMarkovKernel (slowCanonicalCostedActiveSchedule (n := n) (by omega : 1 ≤ n)
      (slowPhases n a + 1) (perPhaseStreams n a)
      (q := perPhaseQ n (slowPhases n a) (perPhaseStreams n a) (slowEpsInt n a)
        (slowRadius n a))
      (eps := slowEpsInt n a / 2) (s0 := slowSourceInitialVariance n)
      (perPhase_canonical_hq0 hn (slowR2 n a) (slowEpsInt n a) (slowRadius n a))
      (canonical_hs0 hn) (interior a.1) (measurableSet_slowBody n a) 0 slowReferenceWarm
      (perPhaseSlack n (slowPhases n a) (interior a.1))
      (perPhaseBoundSqGen n (perPhaseExpSharp n (slowRadius n a))) i) := by
  letI : ∀ j, IsProbabilityMeasure (slowStationaryTail n
      (perPhaseQ n (slowPhases n a) (perPhaseStreams n a) (slowEpsInt n a)
        (slowRadius n a))
      (slowSourceInitialVariance n) (interior a.1) j) := fun j ↦
    perPhase_canonical_isProbabilityMeasure_slowStationaryTail hn
      (measurableSet_slowBody n a) (convex_slowBody h) (ball_subset_slowBody h) j
  infer_instance

/-- **The law of one run at the per-phase pair, totalised.** -/
noncomputable def perPhaseLaw (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    Measure (perPhaseOmega n a) :=
  if h : CVValidInput a ∧ 21 ≤ n then
    @independentHeterogeneousRetainedPathLaw _ _ _ _ (perPhaseStreams n a)
      (slowCanonicalCostedActiveSchedule (n := n) (by omega : 1 ≤ n)
        (slowPhases n a + 1) (perPhaseStreams n a)
        (q := perPhaseQ n (slowPhases n a) (perPhaseStreams n a) (slowEpsInt n a)
          (slowRadius n a))
        (eps := slowEpsInt n a / 2) (s0 := slowSourceInitialVariance n)
        (perPhase_canonical_hq0 h.2 (slowR2 n a) (slowEpsInt n a) (slowRadius n a))
        (canonical_hs0 h.2) (interior a.1) (measurableSet_slowBody n a) 0 slowReferenceWarm
        (perPhaseSlack n (slowPhases n a) (interior a.1))
        (perPhaseBoundSqGen n (perPhaseExpSharp n (slowRadius n a))))
      (fun i ↦ perPhaseIsMarkovKernel_costedSchedule h.1 h.2 i)
      (slowInitialPair n) (slowPhases n a)
  else Measure.dirac (Classical.arbitrary _)

/-- **The unfolding of `perPhaseLaw` on the guarded branch.** -/
theorem perPhaseLaw_of_valid {n : Nat} {a : Ttc.CVAdaptive.VolumeInput n}
    (h : CVValidInput a) (hn : 21 ≤ n) :
    perPhaseLaw n a =
      @independentHeterogeneousRetainedPathLaw _ _ _ _ (perPhaseStreams n a)
        (slowCanonicalCostedActiveSchedule (n := n) (by omega : 1 ≤ n)
          (slowPhases n a + 1) (perPhaseStreams n a)
          (q := perPhaseQ n (slowPhases n a) (perPhaseStreams n a) (slowEpsInt n a)
            (slowRadius n a))
          (eps := slowEpsInt n a / 2) (s0 := slowSourceInitialVariance n)
          (perPhase_canonical_hq0 hn (slowR2 n a) (slowEpsInt n a) (slowRadius n a))
          (canonical_hs0 hn) (interior a.1) (measurableSet_slowBody n a) 0
          slowReferenceWarm
          (perPhaseSlack n (slowPhases n a) (interior a.1))
          (perPhaseBoundSqGen n (perPhaseExpSharp n (slowRadius n a))))
        (fun i ↦ perPhaseIsMarkovKernel_costedSchedule h hn i)
        (slowInitialPair n) (slowPhases n a) :=
  dif_pos ⟨h, hn⟩

/-- The four total families at the clipped input. -/
abbrev perPhaseFinalOmega (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) : Type :=
  perPhaseOmega n (clipInput a)

noncomputable def perPhaseFinalLaw (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    Measure (perPhaseFinalOmega n a) := perPhaseLaw n (clipInput a)

noncomputable def perPhaseFinalCost (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    perPhaseFinalOmega n a → ENNReal := perPhaseCost n (clipInput a)

noncomputable def perPhaseFinalValue (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    perPhaseFinalOmega n a → Real := perPhaseValue n (clipInput a)

theorem measurable_perPhaseFinalCost (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    Measurable (perPhaseFinalCost n a) := measurable_perPhaseCost n (clipInput a)

theorem measurable_perPhaseFinalValue (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    Measurable (perPhaseFinalValue n a) := measurable_perPhaseValue n (clipInput a)

/-! ## Step 7 — the two per-phase envelopes

These are the slots the earlier version of this file had to borrow from
`Ttc.TtcSlowRuntimeSharp`.  They are now the per-phase route's own: the retry cap of
`Ttc.CVPerPhaseFrontier.scoreAwareRetries_perPhase_le` and the deadline envelope of
`Ttc.CVPerPhaseFrontier.slowCanonicalSteps_perPhase_le`, both at the `n`-aware stream count
and, for the deadline, at the `n`-aware truncation radius `perPhaseQ`.  The exponent bound
`B := exp (8 R²)` is `Ttc.CVPerPhaseFrontier.perPhaseExpSharp_le` — dimension-free, exactly
as on the sharp route. -/

/-- The mixing parameter the per-phase schedule runs at, as a function of the declared
squared radius alone. -/
noncomputable def perPhaseQEnv (n : Nat) (R2 epsP : Real) : Real :=
  perPhaseQ n (slowPhasesP n R2) (perPhaseStreamsP n R2 epsP) epsP (Real.sqrt R2)

/-- **The per-phase per-run retry envelope.**  The cap of
`Ttc.CVPerPhaseFrontier.scoreAwareRetries_perPhase_le` at the schedule's `(m+1, epsP/2)`. -/
noncomputable def perPhaseLenv (n : Nat) (R2 epsP : Real) : Real :=
  (perPhaseRetriesCapAt n (slowPhasesP n R2) (perPhaseStreamsP n R2 epsP) epsP
    (Real.exp (8 * Real.sqrt R2 ^ 2)) : Real)

/-- **The per-phase per-phase deadline envelope.**  This is
`Ttc.CVPerPhaseFrontier.perPhaseStepsEnvelope` — the deadline of the compounding
actual-warm schedule at the per-phase share floor and the `n`-aware radius — plus `2`,
which pays for the ceiling and the `+ 1` of
`Ttc.CVPerPhaseFrontier.slowCanonicalSteps_perPhase_le`. -/
noncomputable def perPhaseTenv (n : Nat) (R2 epsP : Real) : Real :=
  perPhaseStepsEnvelope n (slowPhasesP n R2) (perPhaseStreamsP n R2 epsP)
    (perPhaseQEnv n R2 epsP) epsP (Real.exp (8 * Real.sqrt R2 ^ 2)) + 2

/-! ## Step 8 — the `OV` and the `heff` pair -/

/-- The overhead envelope of the combined P1 + P2 route, **parametric** in the retry and
deadline envelopes.  Nothing is claimed to run within it at a general `(Lenv, Tenv)`. -/
noncomputable def slowPerPhaseOVGen (n : Nat) (R2 eps p Lenv Tenv : Real) : Real :=
  64 * (max 1 eps) ^ 2 * sourceLogFactor n ^ 2 *
    slowPerPhaseOverhead n R2 (min eps 1 / 2) p Lenv Tenv

/-- **The cost envelope `ttc_volume_runtime_perPhase` states.**  `slowPerPhaseOVGen` at the
two **per-phase** envelope slots of Step 7 — the retry cap and the deadline envelope the
per-phase analysis itself produces — and at the per-phase stream count inside
`slowPerPhaseOverhead`.  It differs from `Ttc.TtcSlowRuntimeSharp.slowSharpOV` in all three
of those places. -/
noncomputable def slowPerPhaseOV (n : Nat) (R2 eps p : Real) : Real :=
  slowPerPhaseOVGen n R2 eps p (perPhaseLenv n R2 (min eps 1 / 2))
    (perPhaseTenv n R2 (min eps 1 / 2))

/-- The per-input effective runtime constant, at the interior circumradius — the radius
`Ttc.TtcCallCircumAdmissible.cvAdmCircum` declares. -/
noncomputable def slowPerPhaseEffective (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    Real :=
  slowPerPhaseOV n ((circumR (interior a.1)) ^ 2) a.2.1 a.2.2

theorem one_le_slowPerPhaseOVGen (n : Nat) (R2 eps p Lenv Tenv : Real) :
    1 ≤ slowPerPhaseOVGen n R2 eps p Lenv Tenv := by
  unfold slowPerPhaseOVGen
  have h1 : (1 : Real) ≤ (max 1 eps) ^ 2 := by
    have := le_max_left (1 : Real) eps
    nlinarith
  have h2 : (1 : Real) ≤ sourceLogFactor n ^ 2 := by
    have := one_le_sourceLogFactor (n : Real)
    nlinarith
  have h3 : (1 : Real) ≤ slowPerPhaseOverhead n R2 (min eps 1 / 2) p Lenv Tenv :=
    one_le_slowPerPhaseOverhead _ _ _ _ _ _
  have h64 : (1 : Real) ≤ 64 * (max 1 eps) ^ 2 := by nlinarith
  have h641 : (1 : Real) ≤ 64 * (max 1 eps) ^ 2 * sourceLogFactor n ^ 2 := by nlinarith
  nlinarith

theorem one_le_slowPerPhaseOV (n : Nat) (R2 eps p : Real) : 1 ≤ slowPerPhaseOV n R2 eps p :=
  one_le_slowPerPhaseOVGen _ _ _ _ _ _

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

/-! ## Step 9 — the pre-repair comparison, preserved

The earlier version of this file stated `slowPerPhaseOV ≤ slowSharpOV` because its
`slowPerPhaseOV` sat at the **sharp** route's `(Lenv, Tenv)`; the only difference between
the two was the stream count of the retained-scalar envelope.  Now that `slowPerPhaseOV`
sits at the per-phase envelopes, that comparison is a statement about
`slowPerPhaseOVGen` at the sharp slots, and it is preserved verbatim under that name.  It
is **not** a comparison of the capstone's envelope with the sharp capstone's: see the
module docstring. -/

/-- **`slowPerPhaseOVGen` at the sharp envelopes is below `slowSharpOV`.**  The two differ
in exactly one argument — the stream count of the retained-scalar envelope — and
`nmul_slowPerPhaseRetained_le_three_slowActualRetained` says that argument is smaller by
the factor `n / 3`. -/
theorem slowPerPhaseOVGen_sharpEnv_le_slowSharpOV
    {n : Nat} {R2 eps p : Real} (hn : 4 ≤ n) (heps : 0 < eps) :
    slowPerPhaseOVGen n R2 eps p (slowSharpLenv n R2 (min eps 1 / 2))
        (slowSharpTenv n R2 (min eps 1 / 2)) ≤ slowSharpOV n R2 eps p := by
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
  unfold slowPerPhaseOVGen slowSharpOV
  exact mul_le_mul_of_nonneg_left hover hpre

/-! ## Step 10 — the same parameters at a concrete input -/

/-- `perPhaseLenv` at the input's own declared data. -/
noncomputable def perPhaseLenvAt (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) : Real :=
  perPhaseLenv n (slowR2 n a) (slowEpsInt n a)

/-- `perPhaseTenv` at the input's own declared data. -/
noncomputable def perPhaseTenvAt (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) : Real :=
  perPhaseTenv n (slowR2 n a) (slowEpsInt n a)

theorem sqrt_slowR2' (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    Real.sqrt (slowR2 n a) = slowRadius n a :=
  Real.sqrt_sq (circumR_nonneg _)

theorem perPhaseLenvAt_eq (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    perPhaseLenvAt n a =
      (perPhaseRetriesCapAt n (slowPhases n a) (perPhaseStreams n a) (slowEpsInt n a)
        (Real.exp (8 * slowRadius n a ^ 2)) : Real) := by
  unfold perPhaseLenvAt perPhaseLenv
  rw [sqrt_slowR2']
  rfl

theorem perPhaseTenvAt_eq (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    perPhaseTenvAt n a =
      perPhaseStepsEnvelope n (slowPhases n a) (perPhaseStreams n a)
        (perPhaseQ n (slowPhases n a) (perPhaseStreams n a) (slowEpsInt n a)
          (slowRadius n a))
        (slowEpsInt n a) (Real.exp (8 * slowRadius n a ^ 2)) + 2 := by
  unfold perPhaseTenvAt perPhaseTenv perPhaseQEnv
  rw [sqrt_slowR2']
  rfl

/-- The realised accuracy of the per-phase run. -/
noncomputable def perPhaseRealisedAccuracy (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) :
    Real :=
  slowAccuracyRequested (slowPhases n a) (perPhaseStreams n a) (slowEpsInt n a)

/-! ## Step 11 — the producer, with every binder discharged at the per-phase pair

`Ttc.CVPerPhaseFrontier.exists_slowOneRunCertificate_canonical_perPhase` with

* `(E, S)` from `Ttc.CVPerPhaseFrontier.perPhaseSharp_supData` at the P1-sharp exponent;
* the five estimator-moment binders from
  `Ttc.CVPerPhaseFrontier.perPhase_canonical_momentBinders_sharp`, whose `hnm` is
  `n_le_slowPhasesP_add_one` above;
* `hsteps` from `Ttc.CVPerPhaseFrontier.perPhase_canonical_hsteps`;
* `hretries` from `Ttc.CVPerPhaseFrontier.scoreAwareRetries_perPhase_le`;
* `hscalar` from `slowPerPhase_hscalar` above.

Nothing is assumed. -/

/-- **The one-run certificate on a valid input of accuracy at most one, at the per-phase
pair.** -/
theorem exists_slowPerPhaseCertificate_of_valid
    {n : Nat} (hn : 21 ≤ n) {a : Ttc.CVAdaptive.VolumeInput n}
    (h : CVValidInput a) (heps1 : a.2.1 ≤ 1) :
    ∃ r : Measure (perPhaseOmega n a),
      SourceReferenceTVOneRunCertificate (perPhaseLaw n a) r (perPhaseCost n a)
        (perPhaseValue n a)
        (slowPerPhaseOverhead n (slowR2 n a) (slowEpsInt n a) a.2.2
          (perPhaseLenvAt n a) (perPhaseTenvAt n a))
        n (circumR (interior a.1)) (perPhaseRealisedAccuracy n a)
        ((1 - perPhaseRealisedAccuracy n a) * (volume (interior a.1)).toReal)
        ((1 + perPhaseRealisedAccuracy n a) * (volume (interior a.1)).toReal) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hK, hKc, hball, hfin, hvolEq, hKR, hRR⟩ :=
    Ttc.CVValidInteriorBridge.validInput_interior_facts h h.isBounded
  have heps : (0 : Real) < slowEpsInt n a := by
    have := h.1; unfold slowEpsInt; linarith
  have heps1' : slowEpsInt n a ≤ 1 := by unfold slowEpsInt; linarith
  have hB0 : (0 : Real) < Real.exp (8 * circumR (interior a.1) ^ 2) := Real.exp_pos _
  haveI : IsProbabilityMeasure (slowInitialPair n) :=
    canonical_isProbabilityMeasure_slowInitialPair hn
  haveI hprob : ∀ j, IsProbabilityMeasure (slowStationaryTail n
      (perPhaseQ n (slowPhases n a) (perPhaseStreams n a) (slowEpsInt n a)
        (circumR (interior a.1)))
      (slowSourceInitialVariance n) (interior a.1) j) := fun j ↦
    perPhase_canonical_isProbabilityMeasure_slowStationaryTail hn hK hKc hball j
  haveI hmk := fun i ↦ perPhaseIsMarkovKernel_costedSchedule (a := a) h hn i
  haveI hQmk : ∀ i, IsMarkovKernel (slowCanonicalActiveSchedule (n := n) hn1
      (slowCanonicalPhases n (slowR2 n a) + 1)
      (perPhaseRuntimeSamples n (slowCanonicalPhases n (slowR2 n a)) (slowEpsInt n a))
      (q := perPhaseQ n (slowCanonicalPhases n (slowR2 n a))
        (perPhaseRuntimeSamples n (slowCanonicalPhases n (slowR2 n a)) (slowEpsInt n a))
        (slowEpsInt n a) (circumR (interior a.1)))
      (eps := slowEpsInt n a / 2) (s0 := slowSourceInitialVariance n)
      (perPhase_canonical_hq0 hn (slowR2 n a) (slowEpsInt n a) (circumR (interior a.1)))
      (canonical_hs0 hn) (interior a.1) hK 0 slowReferenceWarm
      (perPhaseSlack n (slowCanonicalPhases n (slowR2 n a)) (interior a.1))
      (perPhaseBoundSqGen n (perPhaseExpSharp n (circumR (interior a.1)))) i) := fun i ↦
    perPhaseIsMarkovKernel_activeSchedule hn (R2 := slowR2 n a)
      (eps := slowEpsInt n a) (R := circumR (interior a.1)) hK hKc hball i
  -- the `(E, S)` data of the combined P1 + P2 family
  obtain ⟨hE0, hS0, hSbound, hSloose, hSE⟩ :=
    perPhaseSharp_supData (n := n) hn1 (slowPhases n a) hKR
      (perPhase_canonical_hR2 hn (le_refl (slowR2 n a)))
  -- the five estimator-moment binders
  have hmoments := perPhase_canonical_momentBinders_sharp hn
    (eps := slowEpsInt n a) (R := circumR (interior a.1)) (R2 := slowR2 n a)
    heps heps1' (n_le_slowPhasesP_add_one hn1 (slowR2 n a)) (le_refl _)
    hK hKc hball hfin hKR rfl
  -- the per-phase deadline
  have hsteps := perPhase_canonical_hsteps hn
    (eps := slowEpsInt n a) (R := circumR (interior a.1)) (R2 := slowR2 n a)
    heps heps1' hK hball hfin
  -- the per-phase retry cap
  have hretries : ∀ i,
      scoreAwareRetries (slowPhases n a + 1) (perPhaseStreams n a) (slowEpsInt n a / 2)
        (perPhaseSlack n (slowPhases n a) (interior a.1))
        (perPhaseBoundSqGen n (perPhaseExpSharp n (circumR (interior a.1)))) i ≤
      perPhaseRetriesCapAt n (slowPhases n a) (perPhaseStreams n a) (slowEpsInt n a)
        (Real.exp (8 * circumR (interior a.1) ^ 2)) := fun i ↦
    scoreAwareRetries_perPhase_le hn1 (by linarith : (0 : Real) < slowEpsInt n a / 2)
      (fun j ↦ perPhaseExpSharp_pos j) (fun j ↦ perPhaseExpSharp_le hn1 j)
      hK hball hfin i
  -- the two real envelopes, and the casts the cost layer consumes
  have hEnv0 : 0 ≤ perPhaseStepsEnvelope n (slowPhases n a) (perPhaseStreams n a)
      (perPhaseQ n (slowPhases n a) (perPhaseStreams n a) (slowEpsInt n a)
        (circumR (interior a.1)))
      (slowEpsInt n a) (Real.exp (8 * circumR (interior a.1) ^ 2)) :=
    perPhaseStepsEnvelope_nonneg hn1 heps heps1' hB0
  have hLcast : (perPhaseRetriesCapAt n (slowPhases n a) (perPhaseStreams n a)
      (slowEpsInt n a) (Real.exp (8 * circumR (interior a.1) ^ 2)) : Real) ≤ perPhaseLenvAt n a :=
    le_of_eq (perPhaseLenvAt_eq n a).symm
  have hLenv0 : (0 : Real) ≤ perPhaseLenvAt n a := by
    rw [perPhaseLenvAt_eq]; positivity
  have hTcast : ((⌈perPhaseStepsEnvelope n (slowPhases n a) (perPhaseStreams n a)
        (perPhaseQ n (slowPhases n a) (perPhaseStreams n a) (slowEpsInt n a)
          (circumR (interior a.1)))
        (slowEpsInt n a) (Real.exp (8 * circumR (interior a.1) ^ 2))⌉₊ + 1 : Nat) : Real) ≤
      perPhaseTenvAt n a := by
    rw [perPhaseTenvAt_eq]
    exact cast_perPhaseStepsCap_le n _ _ _ _ _ hEnv0
  have hTenv0 : (0 : Real) ≤ perPhaseTenvAt n a := by
    rw [perPhaseTenvAt_eq]
    have h2 : (0 : Real) ≤ perPhaseStepsEnvelope n (slowPhases n a) (perPhaseStreams n a)
        (perPhaseQ n (slowPhases n a) (perPhaseStreams n a) (slowEpsInt n a)
          (slowRadius n a))
        (slowEpsInt n a) (Real.exp (8 * slowRadius n a ^ 2)) := hEnv0
    linarith
  -- the cost side
  have hscalar := slowPerPhase_hscalar n hn1
    (m := slowPhases n a) (k := perPhaseStreams n a)
    (L := perPhaseRetriesCapAt n (slowPhases n a) (perPhaseStreams n a) (slowEpsInt n a)
      (Real.exp (8 * circumR (interior a.1) ^ 2)))
    (T := ⌈perPhaseStepsEnvelope n (slowPhases n a) (perPhaseStreams n a)
      (perPhaseQ n (slowPhases n a) (perPhaseStreams n a) (slowEpsInt n a)
        (circumR (interior a.1)))
      (slowEpsInt n a) (Real.exp (8 * circumR (interior a.1) ^ 2))⌉₊ + 1)
    (R := circumR (interior a.1)) (requested := perPhaseRealisedAccuracy n a) (R2 := slowR2 n a)
    (epsP := slowEpsInt n a) (p := a.2.2)
    (Lenv := perPhaseLenvAt n a) (Tenv := perPhaseTenvAt n a)
    (slowAccuracyRequested_half_pos (slowPhases n a) (perPhaseStreams n a) h.1)
    (slowAccuracyRequested_half_lt_one_any (slowPhases n a) (perPhaseStreams n a)
      h.1 heps1)
    (le_refl _) (le_refl _) hLcast hTcast hLenv0 hTenv0
  obtain ⟨r, hr⟩ := exists_slowOneRunCertificate_canonical_perPhase hn
    (eps := slowEpsInt n a) (R := circumR (interior a.1)) (R2 := slowR2 n a)
    heps heps1' hK hKc hball hfin hE0 hS0 hSbound hSloose hSE rfl
    hmoments.1 hmoments.2.1 hmoments.2.2.1 hmoments.2.2.2.1 hmoments.2.2.2.2
    (runtimeConstant := slowPerPhaseOverhead n (slowR2 n a) (slowEpsInt n a) a.2.2
      (perPhaseLenvAt n a) (perPhaseTenvAt n a))
    (⌈perPhaseStepsEnvelope n (slowPhases n a) (perPhaseStreams n a)
      (perPhaseQ n (slowPhases n a) (perPhaseStreams n a) (slowEpsInt n a)
        (circumR (interior a.1)))
      (slowEpsInt n a) (Real.exp (8 * circumR (interior a.1) ^ 2))⌉₊ + 1)
    (perPhaseRetriesCapAt n (slowPhases n a) (perPhaseStreams n a) (slowEpsInt n a)
      (Real.exp (8 * circumR (interior a.1) ^ 2)))
    (fun i hi ↦ hsteps i hi) (fun i _ ↦ hretries i) hscalar
  refine ⟨r, ?_⟩
  rw [perPhaseLaw_of_valid h hn]
  exact hr

/-! ## Step 12 — the weakening -/

/-- **The per-phase certificate at the consumer's parameters.** -/
theorem exists_slowPerPhaseFinalCertificate
    {n : Nat} (hn : 21 ≤ n) {a : Ttc.CVAdaptive.VolumeInput n} (h : CVValidInput a) :
    ∃ r : Measure (perPhaseFinalOmega n a),
      SourceReferenceTVOneRunCertificate (perPhaseFinalLaw n a) r (perPhaseFinalCost n a)
        (perPhaseFinalValue n a) (slowPerPhaseEffective n a) n (circumR (interior a.1))
        a.2.1 ((1 - a.2.1) * (volume a.1).toReal)
        ((1 + a.2.1) * (volume a.1).toReal) := by
  have hn1 : 1 ≤ n := by omega
  have hb0 : (0 : Real) < min a.2.1 1 := clipInput_eps_pos h
  have hb1 : min a.2.1 1 ≤ 1 := min_le_right _ _
  have hR0 : (0 : Real) ≤ circumR (interior a.1) := circumR_nonneg _
  obtain ⟨r, hr⟩ := exists_slowPerPhaseCertificate_of_valid hn (clipInput_valid h) hb1
  refine ⟨r, hr.weaken_of_subset ?_ ?_⟩
  · -- the budget
    have hrc0 : (0 : Real) ≤ slowPerPhaseOverhead n (slowR2 n (clipInput a))
        (slowEpsInt n (clipInput a)) a.2.2
        (perPhaseLenvAt n (clipInput a)) (perPhaseTenvAt n (clipInput a)) :=
      slowPerPhaseOverhead_nonneg _ _ _ _ _ _
    have hreq0 : 0 < perPhaseRealisedAccuracy n (clipInput a) :=
      slowAccuracyRequested_half_pos (slowPhases n (clipInput a))
        (perPhaseStreams n (clipInput a)) hb0
    have hhalf : min a.2.1 1 / 2 ≤ perPhaseRealisedAccuracy n (clipInput a) :=
      half_le_slowAccuracyRequested (slowPhases n (clipInput a))
        (perPhaseStreams n (clipInput a)) hb0
    have habs := Ttc.CVBudgetEpsAbsorb.sourceOneRunQueryBudget_absorb
      (rc := slowPerPhaseOverhead n (slowR2 n (clipInput a))
        (slowEpsInt n (clipInput a)) a.2.2
        (perPhaseLenvAt n (clipInput a)) (perPhaseTenvAt n (clipInput a)))
      (R := circumR (interior a.1)) (R' := circumR (interior a.1))
      (e := perPhaseRealisedAccuracy n (clipInput a)) (eps := min a.2.1 1) (n := n)
      hrc0 hn1 hb0 hb1 hreq0 hhalf hR0 (le_refl _)
    have hclip := sourceOneRunQueryBudget_clip_eps (n := n)
      (rc := 64 * slowPerPhaseOverhead n (slowR2 n (clipInput a))
        (slowEpsInt n (clipInput a)) a.2.2
        (perPhaseLenvAt n (clipInput a)) (perPhaseTenvAt n (clipInput a)))
      (R := circumR (interior a.1)) (eps := a.2.1) (by positivity) h.1
    have hrw : slowPerPhaseEffective n a =
        64 * (max 1 a.2.1) ^ 2 * sourceLogFactor n ^ 2 *
          slowPerPhaseOverhead n (slowR2 n (clipInput a)) (slowEpsInt n (clipInput a))
            a.2.2 (perPhaseLenvAt n (clipInput a))
            (perPhaseTenvAt n (clipInput a)) := rfl
    have hconst : 64 * slowPerPhaseOverhead n (slowR2 n (clipInput a))
          (slowEpsInt n (clipInput a)) a.2.2
          (perPhaseLenvAt n (clipInput a)) (perPhaseTenvAt n (clipInput a)) *
          (max 1 a.2.1) ^ 2 * sourceLogFactor n ^ 2 ≤ slowPerPhaseEffective n a :=
      le_of_eq (by rw [hrw]; ring)
    have hcore : (0 : Real) ≤
        max (circumR (interior a.1) ^ 2 * (n : Real) ^ 2) ((n : Real) ^ 3) / a.2.1 ^ 2 *
          sourceLogFactor n ^ 2 * sourceLogFactor (1 / a.2.1) ^ 2 *
          sourceLogFactor ((n : Real) / a.2.1) ^ 2 := by
      have h0 : (0 : Real) ≤
          max (circumR (interior a.1) ^ 2 * (n : Real) ^ 2) ((n : Real) ^ 3) :=
        le_max_of_le_right (by positivity)
      have h1 : (0 : Real) ≤ sourceLogFactor (1 / a.2.1) := (sourceLogFactor_pos _).le
      have h2 : (0 : Real) ≤ sourceLogFactor ((n : Real) / a.2.1) :=
        (sourceLogFactor_pos _).le
      have h3 : (0 : Real) ≤ sourceLogFactor n := (sourceLogFactor_pos _).le
      have h4 : (0 : Real) ≤
          max (circumR (interior a.1) ^ 2 * (n : Real) ^ 2) ((n : Real) ^ 3) /
            a.2.1 ^ 2 := by positivity
      positivity
    exact habs.trans (hclip.trans
      (Ttc.CVSourceReferenceWeaken.sourceOneRunQueryBudget_mono_constant hconst hcore))
  · -- the accepted output window
    have hle : perPhaseRealisedAccuracy n (clipInput a) ≤ a.2.1 :=
      (slowAccuracyRequested_half_le_any (slowPhases n (clipInput a))
        (perPhaseStreams n (clipInput a)) hb0 hb1).trans (min_le_left _ _)
    exact Ttc.CVSourceReferenceWeaken.Icc_relErr_subset hle ENNReal.toReal_nonneg
      (Ttc.CVValidInteriorBridge.toReal_volume_interior_eq_of_convex h.2.2.2.1)

/-! ## Step 13 — the `H` binder and the implementation -/

/-- **The `H` binder of `Ttc.TtcShapedRuntime.ttc_runtime_of_effectiveCertificatesGen`**,
at `radialR := fun n K ↦ circumR (interior K)`, **with no residual hypothesis.** -/
theorem slowPerPhaseCertificate_H :
    ∀ n, 21 ≤ n → ∀ a : Ttc.CVAdaptive.VolumeInput n, CVValidInput a →
      ∃ r : Measure (perPhaseFinalOmega n a),
        SourceReferenceTVOneRunCertificate (perPhaseFinalLaw n a) r
          (perPhaseFinalCost n a) (perPhaseFinalValue n a) (slowPerPhaseEffective n a) n
          (circumR (interior a.1)) a.2.1 ((1 - a.2.1) * (volume a.1).toReal)
          ((1 + a.2.1) * (volume a.1).toReal) :=
  fun _ hn _ h ↦ exists_slowPerPhaseFinalCertificate hn h

/-- **The TTC volume implementation built from the slow canonical route at the combined
P1 + P2 slack / transport / stream-count / radius choice**, with no residual hypothesis. -/
noncomputable def slowPerPhaseImplementation :
    Ttc.CVShaped.CVShapedExpectedImplementation cvAdmCircum
      (Ttc.TtcShapedRuntime.shapeOf slowPerPhaseOV) :=
  Ttc.TtcShapedRuntime.implementationOfEffectiveCertificatesGen cvAdmCircum
    cvAdmCircum_imp_cvAdmissible (fun _ K ↦ circumR (interior K))
    circumInterior_sq_le_of_cvAdmCircum slowPerPhaseOV one_le_slowPerPhaseOV
    slowPerPhaseEffective slowPerPhaseEffective_nonneg slowPerPhaseEffective_le_slowPerPhaseOV
    perPhaseFinalOmega perPhaseFinalLaw perPhaseFinalCost perPhaseFinalValue
    measurable_perPhaseFinalCost measurable_perPhaseFinalValue slowPerPhaseCertificate_H

section Capstone

open Ttc.CVShaped
open Ttc.TtcShapedRuntime
open Ttc.TTCCVExpectedImplementation
open Ttc.ConcreteHybridCanonicalOwnerPoly
open Ttc.CostedCanonicalOwnerTTCPlugin
open Ttc.TTCSourceSharpOperationalFinal
open Ttc.TTCSourceSharpOperationalTheorem

variable {A : Type*}

/-- **TTC's accuracy and query cost, from the slow canonical volume construction at the
combined P1 + P2 pair — unconditionally.**

There is no oracle binder, no certificate binder, no implementation binder and **no
cost-side binder**: the volume subroutine is `slowPerPhaseImplementation.algorithm n`,
built here out of the slow canonical Gaussian-cooling construction run at
`Ttc.CVPerPhaseFrontier.perPhaseSlack`,
`Ttc.CVPerPhaseFrontier.perPhaseBoundSqGen n (perPhaseExpSharp n R)`, the `n`-aware stream
count `Ttc.CVPerPhaseSamples.perPhaseRuntimeSamples` and the `n`-aware truncation radius
`Ttc.CVPerPhaseFrontier.perPhaseQ`; the two conjuncts are about the one law
`canonicalFullOperationalLaw V P` that executes it.

**The cost envelope.**  The volume term is the per-cube sum of
`cvComplexityShapeClipped * slowPerPhaseOV`, each cube taken at **its own interior
circumradius squared**, where

  `slowPerPhaseOV n R2 eps p = 64 * (max 1 eps) ^ 2 * sourceLogFactor n ^ 2 *
      slowPerPhaseOverhead n R2 (min eps 1 / 2) p
        (perPhaseLenv n R2 (min eps 1 / 2)) (perPhaseTenv n R2 (min eps 1 / 2))`

and `slowPerPhaseOverhead` is `Ttc.CVSlowActualCostEnvelope.slowActualOverhead` at the
**per-phase stream count** `perPhaseStreamsP`.  All three per-phase substitutions — stream
count, retry cap, deadline envelope — are inside the envelope this theorem states; see the
module docstring for the precise scope of what is and is not certified.

It is **not** the paper's `O(m · n^5 · rho^2 · r_max)` exponents, and no constant here is
pretending to be one: what is proved is a bound at this explicit shape. -/
theorem ttc_volume_runtime_perPhase
    {n : Nat} (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 21 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi) :
    let deltaRun := 4 * delta / 5
    let hn1 : 1 ≤ n := le_trans (by norm_num) hn
    let I := slowPerPhaseImplementation
    let V := I.algorithm n
    letI : NeZero n := ⟨Nat.ne_of_gt hn1⟩
    let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
      h_eps_pos h_eps_le hn1 hphi hvol
    (1 - delta ≤ (canonicalFullOperationalLaw V P).real
      {r | r.1 ∈ relErr eps (volSol (atomSet atoms) phi)}) ∧
    ((∫⁻ r, r.2 ∂canonicalFullOperationalLaw V P) ≤
      shapedVolumeQueryEnvelopeAt I atoms phi eps deltaRun
        (fun j ↦ (circumR (interior (callBody atoms phi eps deltaRun j))) ^ 2) +
        canonicalCappedSampleQueryEnvelope atoms phi eps deltaRun) :=
  ttc_runtime_of_effectiveCertificatesGen cvAdmCircum cvAdmCircum_imp_cvAdmissible
    (fun _ K ↦ circumR (interior K)) circumInterior_sq_le_of_cvAdmCircum
    slowPerPhaseOV one_le_slowPerPhaseOV slowPerPhaseEffective slowPerPhaseEffective_nonneg
    slowPerPhaseEffective_le_slowPerPhaseOV perPhaseFinalOmega perPhaseFinalLaw
    perPhaseFinalCost perPhaseFinalValue
    measurable_perPhaseFinalCost measurable_perPhaseFinalValue
    slowPerPhaseCertificate_H
    atoms phi eps delta
    (fun j ↦ (circumR (interior (callBody atoms phi eps (4 * delta / 5) j))) ^ 2)
    h_eps_pos h_eps_le h_delta_pos h_delta_le hn hphi hvol
    (fun j ↦ cvAdmCircum_callBody atoms phi eps (4 * delta / 5)
      h_eps_pos h_eps_le (le_trans (by norm_num) hn) hphi hvol j)

end Capstone

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
#print axioms nmul_slowPerPhaseRetained_le_three_slowActualRetained
#print axioms slowPerPhaseOverhead_le_slowActualOverhead
#print axioms slowPerPhase_hscalar
#print axioms scoreAwareMeanGamma_le_div_hundred
#print axioms scoreAwareAccuracyBeta_le_quarter
#print axioms slowAccuracyRequested_half_lt_one_any
#print axioms slowAccuracyRequested_half_le_any
#print axioms perPhaseStreams
#print axioms measurable_perPhaseCost
#print axioms measurable_perPhaseValue
#print axioms perPhaseIsMarkovKernel_activeSchedule
#print axioms perPhaseIsMarkovKernel_costedSchedule
#print axioms perPhaseLaw
#print axioms perPhaseLaw_of_valid
#print axioms perPhaseQEnv
#print axioms perPhaseLenv
#print axioms perPhaseTenv
#print axioms slowPerPhaseOVGen
#print axioms slowPerPhaseOV
#print axioms one_le_slowPerPhaseOV
#print axioms slowPerPhaseOV_nonneg
#print axioms slowPerPhaseEffective
#print axioms slowPerPhaseEffective_nonneg
#print axioms slowPerPhaseEffective_le_slowPerPhaseOV
#print axioms slowPerPhaseOVGen_sharpEnv_le_slowSharpOV
#print axioms perPhaseLenvAt_eq
#print axioms perPhaseTenvAt_eq
#print axioms perPhaseRealisedAccuracy
#print axioms exists_slowPerPhaseCertificate_of_valid
#print axioms exists_slowPerPhaseFinalCertificate
#print axioms slowPerPhaseCertificate_H
#print axioms slowPerPhaseImplementation
#print axioms ttc_volume_runtime_perPhase

end AxiomCheck

end Ttc.TtcSlowRuntimePerPhase
