/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.CVPerPhaseSamples
import Ttc.Exec.CVSlowCanonicalMomentBinders

/-!
# The moment bundles at the `n`-aware per-phase factor (P2, integration step)

`Ttc.CVPerPhaseSamples` (P2) established the two *ends* of the estimator's variance
chain at the `n`-aware stream count `perPhaseRuntimeSamples n m eps`:

* the sharp **scalar** relative second moment under the exact cooling law
  (`slowSource_phaseScore_sq_moment_sharp`: `1 + 2/n` interior, `2` terminal), and
* the **clipping** normalisation at the smaller sample count
  (`perPhaseRuntime_interior_clipping`, `perPhaseRuntime_terminal_clipping`).

This file supplies the *middle* — independent-stream averaging — and re-assembles the
clipped/stream moment bundles and the frontier's seven moment binders at
`factor := perPhaseFactor n m (perPhaseRuntimeSamples n m eps)` instead of the uniform
`fun _ ↦ 1 + 8 / (correctedRuntimeSamples m eps : Real)`.

## The index convention, pinned

`Ttc.CVRelativeMeanClippingAssembly.positiveScalarPhaseFamilyChainLength` is
`| i + 1 => scalarPhaseScore chainLength sigmaSq K i`, so the recursion's phase `j` is
the schedule's phase `j - 1`.  `slowSource_phaseScore_sq_moment_sharp` branches on
`i + 1 < m` at schedule phase `i`; at `j = i + 1` that is exactly `j < m`, which is the
branch of `Ttc.CVPerPhaseSamples.perPhaseFactor`.  The coordinates `j = 0` and `j > m`
are the constant one, for which any factor `≥ 1` is admissible
(`one_le_perPhaseFactor`).  The `example` in Step 0 and `sharpExactFactor_succ_eq` /
`slowSource_phaseScore_sq_moment_sharpExact` in Step 8 pin this as machine checks rather
than as comments.

## The transport gap (stated honestly, `CLAUDE.md` §11)

The bundles below take the **operational** scalar moment as a hypothesis, exactly as
`Ttc.CVSlowCanonicalPhaseMomentPackage.operational_slowCanonical_clippedMoment_bundle_upto`
does — but at the sharp family `sharpTransportedFactor` rather than the constant `7`.
That change is forced and it is *not* a weakening; it is where the honest accounting
lives:

* P2's sharp moment is under `coolLaw`.  The bundles' `hscalar` slot is under the
  operational path measure `inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0`.
* The only bridge between them is
  `Ttc.CVGaussianSourceWeightedMoment.operational_path_phaseScore_memLp_and_sq_moment_le_factor_of_targetTV`
  (`Ttc/Exec/CVGaussianSourceWeightedMoment.lean:121`), which inflates the exact-law
  factor `C` to an operational target `T` and consumes a *strictly positive* slack
  `(T - C) · ratio²` against `mixError + targetError`.  Since the mixing error is never
  zero in this development, `T > C` is unavoidable: an operational hypothesis at the
  exact factor `1 + 2/n` itself is not dischargeable by any schedule here, and stating
  the bundle at it would be a vacuous strengthening.
* The natural dischargeable target is `T = 2·C - 1`, the shape produced by
  `Ttc.CVGaussianSourceWeightedMoment.operational_path_phaseScore_scoreAware_relative_of_targetTV`
  under `slack := relativePhaseSlack`, `boundSq := relativePhaseBoundSq`.  At the sharp
  `C` that is `sharpTransportedFactor n m = if · < m then 1 + 4/n else 3`, which is what
  the bundles below assume.
* The *slow canonical frontier's own* schedule pins `slack` to
  `Ttc.CVGaussianFactorSevenAssembly.phaseMomentSlackSeven`
  (`Ttc/Exec/CVGaussianFactorSevenAssembly.lean:174`), whose transport target is the
  hard-coded constant `7`
  (`hslackDef`/`hboundDef` binders of
  `Ttc.CVSlowCanonicalRobustCertificate.exists_sourceReferenceTVOneRunCertificate_slowCanonical_of_weightedData`,
  `Ttc/Exec/CVSlowCanonicalRobustCertificate.lean:191`).  **Under that schedule the
  factor `n` is lost a second time, at transport, whatever the exact-law factor is.**
  This refines P2's audit, which located the single loss at the `2/n ≤ 1` relaxation in
  `Ttc/Exec/CVSlowGaussianPhaseMoment.lean:53-57`: that is the whole story for the
  *exact-law* chain, but the *operational* chain re-loses it at the transport target.
  Repairing it means re-declaring `slack`/`boundSq` in the frontier's schedule — an
  existing-file change, outside this file's write scope, and a runtime-only cost (more
  mixing steps per phase, no extra streams).
* That the transported hypothesis really *is* what the transport delivers is not left as
  prose: `operational_phaseScore_sharpTransported_of_slack` (Step 9) derives it from P2's
  sharp exact-law factor and the single slack inequality `(C - 1)·ratio²`, which is
  `(2/n)·ratio²` on interior phases.

Nothing here is asserted without proof, and no existing file is modified.

## Semantic `def`s (`CLAUDE.md` §11)

`sharpExactFactor`, `sharpTransportedFactor` and `averagedPerPhaseFactor` are closed-form
abbreviations asserting no property; `sharpTransportedFactor_eq` records the identity
their names suggest, and everything else claimed of them is proved below.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Ttc.CVPerPhaseMomentBundle

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVCorrected Ttc.CVCorrectedRuntime
open Ttc.CVIndependentStreamDependence Ttc.CVScoreSeedPhaseKernel
open Ttc.CVGaussianScoreAwareParameters Ttc.CVGaussianFactorSevenAssembly
open Ttc.CVGaussianScoreAwareMeanBudget Ttc.CVScoreAwareHalfMeanBudget
open Ttc.CVGaussianBlockRetryParameters Ttc.CVContinuingRetryParameters
open Ttc.CVSlowFullBodySourceSchedule Ttc.CVSlowSourceReferenceCertificate
open Ttc.CVSlowSourceTargetTVAccuracy
open Ttc.CVRAwareGlobalRadius Ttc.CVSlowCanonicalShareBounds
open Ttc.CVMinimalScoreAwareWarmLogArithmetic
open Ttc.CVSlowRadiusQReferencePhaseTV Ttc.CVSlowRadiusQCanonicalOperational
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVSlowCanonicalUniformParameters
open Ttc.CVSlowCanonicalPhaseMomentPackage
open Ttc.CVSlowCanonicalMomentInstantiation
open Ttc.CVSlowCanonicalMomentBinders
open Ttc.CVSlowCanonicalRobustCertificate
open Ttc.CVRelativeMeanClippingAssembly Ttc.CVIndependentStreamMoments
open Ttc.CVSourceWeightedClipping Ttc.CVGaussianSourceWeightedMoment
open Ttc.CVPerPhaseSamples
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-! ## Step 0 — the index convention, pinned

`slowSource_phaseScore_sq_moment_sharp` branches on `i + 1 < m` at *schedule* phase `i`;
`perPhaseFactor` branches on `j < m` at *recursion* phase `j`.  The two agree under
`j = i + 1`, which is the index shift built into
`positiveScalarPhaseFamilyChainLength`. -/

example (n m k i : Nat) :
    (if i + 1 < m then 1 + 8 / ((n : Real) * k) else 1 + 8 / (k : Real)) =
      perPhaseFactor n m k (i + 1) := by
  unfold perPhaseFactor
  rfl

/-! ## Step 1 — arithmetic at the `n`-aware stream count -/

/-- The `n`-aware stream count is at least two.  (In fact it exceeds `100000`; two is all
the clipping step needs, via `c ≤ 2` in
`Ttc.CVSourceWeightedClipping.clipped_sq_moment_le_factor`.) -/
theorem two_le_perPhaseRuntimeSamples {n m : Nat} {eps : Real}
    (hn : 0 < n) (heps : 0 < eps) : 2 ≤ perPhaseRuntimeSamples n m eps := by
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hden : (0 : Real) < (n : Real) * eps ^ 2 := by positivity
  have hnum : (0 : Real) < 100000 * ((m : Real) + (n : Real)) := by
    have : (0 : Real) ≤ (m : Real) := Nat.cast_nonneg m
    nlinarith
  have hq : (0 : Real) < 100000 * ((m : Real) + (n : Real)) / ((n : Real) * eps ^ 2) :=
    div_pos hnum hden
  have hceil : 1 ≤ ⌈100000 * ((m : Real) + (n : Real)) / ((n : Real) * eps ^ 2)⌉₊ :=
    Nat.one_le_ceil_iff.mpr hq
  unfold perPhaseRuntimeSamples
  omega

/-- **A sharper truncation-level comparison than P2's `≤ 5·correctedAlpha`.**  The
`4/x`-shaped clipping absorption below needs `n·k + 8 ≤ 4·correctedAlpha`, which `5·α`
does not give; `3·α` does. -/
theorem nmul_perPhaseRuntimeSamples_le_three_correctedAlpha {n m : Nat} {eps : Real}
    (hn : 0 < n) (hnm : (n : Real) ≤ (m : Real) + 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (n : Real) * (perPhaseRuntimeSamples n m eps : Real) ≤ 3 * correctedAlpha m eps := by
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hmR : (0 : Real) ≤ (m : Real) := Nat.cast_nonneg m
  have he2 : (0 : Real) < eps ^ 2 := by positivity
  have he2le : eps ^ 2 ≤ 1 := by nlinarith
  have hden : (0 : Real) < (n : Real) * eps ^ 2 := by positivity
  have hPlt := perPhaseRuntimeSamples_cast_lt (n := n) (m := m) (eps := eps)
  have hPmul : (perPhaseRuntimeSamples n m eps : Real) * ((n : Real) * eps ^ 2)
      < 100000 * ((m : Real) + (n : Real)) + 2 * ((n : Real) * eps ^ 2) := by
    have hstep := mul_lt_mul_of_pos_right hPlt hden
    have hexp : (100000 * ((m : Real) + (n : Real)) / ((n : Real) * eps ^ 2) + 2)
        * ((n : Real) * eps ^ 2)
        = 100000 * ((m : Real) + (n : Real)) + 2 * ((n : Real) * eps ^ 2) := by
      field_simp
    linarith [hexp ▸ hstep]
  have halpha : correctedAlpha m eps * eps ^ 2 = 100000 * ((m : Real) + 1) := by
    rw [correctedAlpha]
    field_simp
  have hgoal : (n : Real) * (perPhaseRuntimeSamples n m eps : Real) * eps ^ 2
      ≤ 3 * correctedAlpha m eps * eps ^ 2 := by nlinarith
  nlinarith

/-- `n·k + 8 ≤ 4·correctedAlpha` at the `n`-aware stream count. -/
theorem nmul_perPhaseRuntimeSamples_add_eight_le_four_correctedAlpha
    {n m : Nat} {eps : Real}
    (hn : 0 < n) (hnm : (n : Real) ≤ (m : Real) + 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (n : Real) * (perPhaseRuntimeSamples n m eps : Real) + 8 ≤
      4 * correctedAlpha m eps := by
  have h3 := nmul_perPhaseRuntimeSamples_le_three_correctedAlpha hn hnm heps heps1
  have ha := Ttc.CVCorrectedClippingArithmetic.correctedAlpha_ge_hundred_thousand
    (m := m) heps heps1
  linarith

/-- Generic clipping absorption at the transported interior factor: a raw-averaged factor
`1 + 4/x` survives division by `(1 - 1/(2α))²` inside `1 + 8/x`, provided `x + 8 ≤ 4α`.
This is the `4/x` analogue of
`Ttc.CVPerPhaseSamples.two_over_clipping_sq_le_eight_of_nearby`. -/
theorem four_over_clipping_sq_le_eight_of_nearby {x alpha : Real}
    (halpha : 10 ≤ alpha) (hx : 0 < x) (hxa : x + 8 ≤ 4 * alpha) :
    (1 + 4 / x) / (1 - 1 / (2 * alpha)) ^ 2 ≤ 1 + 8 / x := by
  have ha0 : 0 < alpha := by linarith
  have hd0 : 0 < 1 - 1 / (2 * alpha) := by
    rw [sub_pos, div_lt_one (by positivity)]
    linarith
  have hxa0 : 0 < x * alpha := by positivity
  have hkey : 1 + 4 / x ≤ (1 + 8 / x) * (1 - 1 / alpha) := by
    rw [← sub_nonneg]
    have hid : (1 + 8 / x) * (1 - 1 / alpha) - (1 + 4 / x)
        = (4 * alpha - x - 8) / (x * alpha) := by
      field_simp
      ring
    rw [hid]
    exact div_nonneg (by linarith) hxa0.le
  have hsq : 1 - 1 / alpha ≤ (1 - 1 / (2 * alpha)) ^ 2 := by
    have hid : (1 - 1 / (2 * alpha)) ^ 2 - (1 - 1 / alpha)
        = (1 / (2 * alpha)) ^ 2 := by
      field_simp
      ring
    nlinarith [sq_nonneg (1 / (2 * alpha))]
  have h8 : (0 : Real) ≤ 1 + 8 / x := by positivity
  rw [div_le_iff₀ (sq_pos_of_pos hd0)]
  calc
    1 + 4 / x ≤ (1 + 8 / x) * (1 - 1 / alpha) := hkey
    _ ≤ (1 + 8 / x) * (1 - 1 / (2 * alpha)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq h8

/-- **The transported interior clipped factor at the new sample count is the interior
`perPhaseFactor`.**  P2's `perPhaseRuntime_interior_clipping` does this at the *exact*
interior factor `1 + 2/(n·k)`; this is the same statement at the *transported* factor
`1 + 4/(n·k)`, which is the one the operational chain actually produces. -/
theorem perPhaseRuntime_interior_clipping_four {n m : Nat} {eps : Real}
    (hn : 0 < n) (hnm : (n : Real) ≤ (m : Real) + 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (1 + 4 / ((n : Real) * (perPhaseRuntimeSamples n m eps : Real))) /
        (1 - 1 / (2 * correctedAlpha m eps)) ^ 2 ≤
      1 + 8 / ((n : Real) * (perPhaseRuntimeSamples n m eps : Real)) := by
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hPpos : (0 : Real) < (perPhaseRuntimeSamples n m eps : Real) := by
    exact_mod_cast perPhaseRuntimeSamples_pos n m eps
  refine four_over_clipping_sq_le_eight_of_nearby ?_ (by positivity) ?_
  · exact (show (10 : Real) ≤ 100000 by norm_num).trans
      (Ttc.CVCorrectedClippingArithmetic.correctedAlpha_ge_hundred_thousand
        (m := m) heps heps1)
  · exact nmul_perPhaseRuntimeSamples_add_eight_le_four_correctedAlpha hn hnm heps heps1

/-! ## Step 2 — the quantified payoff -/

/-- **The `n`-fold saving in the stream count, strictly.**  For `4 ≤ n ≤ m + 1` the
`n`-aware count is *strictly* below the uniform one; quantitatively
`n · perPhaseRuntimeSamples ≤ 3 · correctedRuntimeSamples`
(`Ttc.CVPerPhaseSamples.perPhaseRuntimeSamples_saving`), i.e. the saving is a factor
`n/3`.  At `n = 3` only `≤` is available, which is why the hypothesis is `4 ≤ n`; the
slow canonical frontier assumes `21 ≤ n`, so this costs nothing. -/
theorem perPhaseRuntimeSamples_lt_correctedRuntimeSamples {n m : Nat} {eps : Real}
    (hn : 4 ≤ n) (hnm : (n : Real) ≤ (m : Real) + 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    perPhaseRuntimeSamples n m eps < correctedRuntimeSamples m eps := by
  have hnR : (4 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hsav := perPhaseRuntimeSamples_saving (n := n) (m := m) (eps := eps)
    (by omega) hnm heps heps1
  have hP1 : (1 : Real) ≤ (perPhaseRuntimeSamples n m eps : Real) := by
    exact_mod_cast perPhaseRuntimeSamples_pos n m eps
  have hC0 : (0 : Real) ≤ (correctedRuntimeSamples m eps : Real) := Nat.cast_nonneg _
  have hlt : (perPhaseRuntimeSamples n m eps : Real)
      < (correctedRuntimeSamples m eps : Real) := by nlinarith
  exact_mod_cast hlt

/-! ## Step 3 — the sharp factor families

`sharpExactFactor` is the exact-law family of
`Ttc.CVPerPhaseSamples.slowSource_phaseScore_sq_moment_sharp`, re-indexed from schedule
phase `i` to recursion phase `j = i + 1` (see Step 0).  `sharpTransportedFactor` is its
operational image `2·C - 1` under
`Ttc.CVGaussianSourceWeightedMoment.operational_path_phaseScore_scoreAware_relative_of_targetTV`,
and `averagedPerPhaseFactor` is what `k` independent streams make of it. -/

/-- The sharp *exact-law* per-phase relative second-moment family: `1 + 2/n` on the
interior phases, `2` at the single terminal phase. -/
noncomputable def sharpExactFactor (n m : Nat) (j : Nat) : Real :=
  if j < m then 1 + 2 / (n : Real) else 2

/-- The sharp *operational* per-phase family, i.e. the exact-law family after TV
transport at the dischargeable target `2·C - 1`. -/
noncomputable def sharpTransportedFactor (n m : Nat) (j : Nat) : Real :=
  if j < m then 1 + 4 / (n : Real) else 3

/-- The transported family really is `2·C - 1` at the exact family — the identity its
name promises (`CLAUDE.md` §11). -/
theorem sharpTransportedFactor_eq (n m j : Nat) :
    sharpTransportedFactor n m j = 2 * sharpExactFactor n m j - 1 := by
  unfold sharpTransportedFactor sharpExactFactor
  split <;> ring

/-- The transported family dominates the exact one, so an exact-law-sharp hypothesis is
in particular a transported-sharp one. -/
theorem sharpExactFactor_le_sharpTransportedFactor {n : Nat} (hn : 0 < n) (m j : Nat) :
    sharpExactFactor n m j ≤ sharpTransportedFactor n m j := by
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  unfold sharpExactFactor sharpTransportedFactor
  split
  · have h : (2 : Real) / (n : Real) ≤ 4 / (n : Real) := by
      rw [div_le_div_iff₀ hnR hnR]
      nlinarith
    linarith
  · norm_num

/-- What `k` independent streams make of `sharpTransportedFactor`. -/
noncomputable def averagedPerPhaseFactor (n m k : Nat) (j : Nat) : Real :=
  if j < m then 1 + 4 / ((n : Real) * (k : Real)) else 1 + 2 / (k : Real)

/-- The averaging identity: a raw per-path factor `c` becomes `1 + (c-1)/k`
(`Ttc.CVIndependentStreamMoments.integral_streamAverage_sq_le`), and at
`c = sharpTransportedFactor` that is exactly `averagedPerPhaseFactor`. -/
theorem averagedPerPhaseFactor_eq (n m k j : Nat) :
    averagedPerPhaseFactor n m k j =
      1 + (sharpTransportedFactor n m j - 1) / (k : Real) := by
  unfold averagedPerPhaseFactor sharpTransportedFactor
  split
  · rw [show (1 : Real) + 4 / (n : Real) - 1 = 4 / (n : Real) by ring, div_div]
  · norm_num

theorem averagedPerPhaseFactor_nonneg {n m k : Nat} (j : Nat) :
    0 ≤ averagedPerPhaseFactor n m k j := by
  unfold averagedPerPhaseFactor
  split <;> positivity

/-- `averagedPerPhaseFactor ≤ 2`, the `hc2` premise of
`Ttc.CVSourceWeightedClipping.clipped_sq_moment_le_factor`.  Interior needs `4 ≤ n·k`,
terminal needs `2 ≤ k`. -/
theorem averagedPerPhaseFactor_le_two {n m k : Nat} (j : Nat)
    (hnk : (4 : Real) ≤ (n : Real) * (k : Real)) (hk2 : 2 ≤ k) :
    averagedPerPhaseFactor n m k j ≤ 2 := by
  have hkR : (2 : Real) ≤ (k : Real) := by exact_mod_cast hk2
  unfold averagedPerPhaseFactor
  split
  · have hnk0 : (0 : Real) < (n : Real) * (k : Real) := by linarith
    have : (4 : Real) / ((n : Real) * (k : Real)) ≤ 1 := (div_le_one hnk0).2 hnk
    linarith
  · have : (2 : Real) / (k : Real) ≤ 1 := (div_le_one (by linarith)).2 hkR
    linarith

/-- **Deliverable 1 — the stream-averaged sharp moment.**  A scalar score with the sharp
operational per-phase factor has, after averaging `k` independent streams, the factor
`averagedPerPhaseFactor`: `1 + 4/(n·k)` on interior phases and `1 + 2/k` at the terminal
one. -/
theorem perPhase_streamAverage_sq_le {Path : Type*} [MeasurableSpace Path]
    {n m k j : Nat} (hk : 0 < k)
    (mu : Measure Path) [IsProbabilityMeasure mu]
    {g : Path → Real} (hg : Measurable g) (hL2 : MemLp g 2 mu)
    (hsq : ∫ x, (g x) ^ 2 ∂mu ≤
      sharpTransportedFactor n m j * (∫ x, g x ∂mu) ^ 2) :
    ∫ omega, (streamAverage (k := k) g omega) ^ 2 ∂(independentStreamLaw mu) ≤
      averagedPerPhaseFactor n m k j *
        (∫ omega, streamAverage (k := k) g omega
          ∂(independentStreamLaw mu)) ^ 2 := by
  have hmean := integral_streamAverage hk mu hg (hL2.integrable one_le_two)
  rw [hmean, averagedPerPhaseFactor_eq]
  exact integral_streamAverage_sq_le hk mu hg hL2 rfl hsq

/-- **The clipping step lands on `perPhaseFactor`.**  Both branches: the interior one via
`perPhaseRuntime_interior_clipping_four`, the terminal one via P2's
`Ttc.CVPerPhaseSamples.perPhaseRuntime_terminal_clipping`. -/
theorem clippedFactor_averagedPerPhaseFactor_le {n m : Nat} {eps : Real}
    (hn : 0 < n) (hnm : (n : Real) ≤ (m : Real) + 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (j : Nat) :
    clippedFactor (correctedAlpha m eps)
        (averagedPerPhaseFactor n m (perPhaseRuntimeSamples n m eps) j) ≤
      perPhaseFactor n m (perPhaseRuntimeSamples n m eps) j := by
  unfold clippedFactor averagedPerPhaseFactor perPhaseFactor
  split
  · exact perPhaseRuntime_interior_clipping_four hn hnm heps heps1
  · exact perPhaseRuntime_terminal_clipping hn hnm heps heps1

/-! ## Step 4 — the clipped moment bundle at `perPhaseFactor` -/

theorem streamAverage_positiveScalar_nonneg
    {m k : Nat} {sigmaSq : Nat → Real} {K : Set (State n)} (j : Nat)
    (omega : Fin k → Nat → State n × State n) :
    0 ≤ streamAverage (k := k)
      (positiveScalarPhaseFamilyChainLength (Seed := State n) m sigmaSq K j) omega := by
  unfold streamAverage Ttc.CVEst.avgOf streamScore
  apply div_nonneg
  · exact Finset.sum_nonneg fun l _ ↦
      positiveScalarPhaseFamilyChainLength_nonneg j (omega l)
  · positivity

theorem one_lt_correctedAlpha_of {m : Nat} {eps : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) : 1 < correctedAlpha m eps := by
  have h := Ttc.CVCorrectedClippingArithmetic.correctedAlpha_ge_hundred_thousand
    (m := m) heps heps1
  linarith

/-- **Deliverable 2 — the analogue of
`Ttc.CVSlowCanonicalPhaseMomentPackage.operational_slowCanonical_clippedMoment_bundle_upto`
at the per-phase factor.**

Every binder has the shape of the original, with two forced changes and nothing else:

* `k := perPhaseRuntimeSamples n m eps` instead of `correctedRuntimeSamples m eps`;
* `hscalar` is at the sharp operational family `sharpTransportedFactor n m j` instead of
  the constant `7`, and the conclusion is correspondingly at
  `perPhaseFactor n m (perPhaseRuntimeSamples n m eps) j` instead of
  `1 + 8 / (correctedRuntimeSamples m eps : Real)`.

The extra hypotheses `4 ≤ n` and `(n : ℝ) ≤ m + 1` are the regime in which the `n`-fold
saving is claimed at all (`Ttc.CVPerPhaseSamples`, "Regime caveat"); they are what P2's
clipping lemmas consume. -/
theorem operational_slowCanonical_clippedMoment_bundle_perPhase
    {m : Nat} {eps : Real} (hn : 4 ≤ n) (hnm : (n : Real) ≤ (m : Real) + 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    {sigmaSq : Nat → Real} {K : Set (State n)} (hK : MeasurableSet K)
    {Q : Nat → Kernel (State n) (State n × State n)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × State n)} [IsProbabilityMeasure mu0]
    {V : Nat →
      (Fin (perPhaseRuntimeSamples n m eps) → Nat → State n × State n) → Real}
    (hscalar : ∀ j, j ≤ m →
      MemLp (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m sigmaSq K j) 2
        (inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ∧
      ∫ omega,
          (positiveScalarPhaseFamilyChainLength (Seed := State n)
            m sigmaSq K j omega) ^ 2
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ≤
        sharpTransportedFactor n m j * (∫ omega,
          positiveScalarPhaseFamilyChainLength (Seed := State n)
            m sigmaSq K j omega
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0)) ^ 2)
    (hmeanPos : ∀ j, j ≤ m → 0 < ∫ omega,
      streamAverage (k := perPhaseRuntimeSamples n m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m sigmaSq K j) omega
      ∂(independentPathLaw (perPhaseRuntimeSamples n m eps)
        (stateScheduleFromSeed Q) mu0))
    (hVdef : ∀ j omega, j ≤ m → V j omega =
      min (streamAverage (k := perPhaseRuntimeSamples n m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m sigmaSq K j) omega)
        (correctedAlpha m eps * ∫ z,
          streamAverage (k := perPhaseRuntimeSamples n m eps)
            (positiveScalarPhaseFamilyChainLength (Seed := State n)
              m sigmaSq K j) z
          ∂(independentPathLaw (perPhaseRuntimeSamples n m eps)
            (stateScheduleFromSeed Q) mu0))) :
    ∀ j, j ≤ m →
      Integrable (fun omega ↦ (V j omega) ^ 2)
        (independentPathLaw (perPhaseRuntimeSamples n m eps)
          (stateScheduleFromSeed Q) mu0) ∧
      ∫ omega, (V j omega) ^ 2
          ∂(independentPathLaw (perPhaseRuntimeSamples n m eps)
            (stateScheduleFromSeed Q) mu0) ≤
        perPhaseFactor n m (perPhaseRuntimeSamples n m eps) j *
          (∫ omega, V j omega
            ∂(independentPathLaw (perPhaseRuntimeSamples n m eps)
              (stateScheduleFromSeed Q) mu0)) ^ 2 := by
  intro j hj
  have hn0 : 0 < n := by omega
  have hnR : (4 : Real) ≤ (n : Real) := by exact_mod_cast hn
  let P : Nat := perPhaseRuntimeSamples n m eps
  have hP0 : 0 < P := perPhaseRuntimeSamples_pos n m eps
  have hP2 : 2 ≤ P := two_le_perPhaseRuntimeSamples hn0 heps
  have hPR : (2 : Real) ≤ (P : Real) := by exact_mod_cast hP2
  have hnk : (4 : Real) ≤ (n : Real) * (P : Real) := by nlinarith
  let scalarLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
  let g := positiveScalarPhaseFamilyChainLength (Seed := State n) m sigmaSq K j
  have hgm : Measurable g := measurable_positiveScalarPhaseFamilyChainLength hK j
  have hgL2 : MemLp g 2 scalarLaw := (hscalar j hj).1
  have hW0 : ∀ omega : Fin P → Nat → State n × State n,
      0 ≤ streamAverage (k := P) g omega := fun omega ↦
    streamAverage_positiveScalar_nonneg j omega
  have hWm : Measurable (streamAverage (k := P) g) := measurable_streamAverage hgm
  have hWint : Integrable (streamAverage (k := P) g)
      (independentStreamLaw scalarLaw) :=
    (memLp_streamAverage (k := P) scalarLaw hgL2).integrable one_le_two
  have hW2int : Integrable
      (fun omega ↦ (streamAverage (k := P) g omega) ^ 2)
      (independentStreamLaw scalarLaw) :=
    integrable_streamAverage_sq (k := P) scalarLaw hgL2
  have hraw := perPhase_streamAverage_sq_le (n := n) (m := m) (k := P) (j := j)
    hP0 scalarLaw hgm hgL2 (hscalar j hj).2
  have h := clipped_sq_moment_le_factor
    (mu := independentStreamLaw (k := P) scalarLaw)
    (alpha := correctedAlpha m eps) (c := averagedPerPhaseFactor n m P j)
    (one_lt_correctedAlpha_of heps heps1)
    (averagedPerPhaseFactor_nonneg j)
    (averagedPerPhaseFactor_le_two j hnk hP2)
    hW0 hWm hWint hW2int
    (by simpa only [P, scalarLaw, g, independentPathLaw] using hmeanPos j hj)
    hraw
    (fun omega ↦ by
      simpa only [P, scalarLaw, g, independentPathLaw] using hVdef j omega hj)
  have hclip := clippedFactor_averagedPerPhaseFactor_le (n := n) (m := m) (eps := eps)
    hn0 hnm heps heps1 j
  refine ⟨by simpa only [P, scalarLaw, g, independentPathLaw] using h.1, ?_⟩
  have h2 : ∫ omega, (V j omega) ^ 2
      ∂(independentStreamLaw (k := P) scalarLaw) ≤
      perPhaseFactor n m P j *
        (∫ omega, V j omega ∂(independentStreamLaw (k := P) scalarLaw)) ^ 2 :=
    h.2.trans (mul_le_mul_of_nonneg_right hclip (sq_nonneg _))
  simpa only [P, scalarLaw, g, independentPathLaw] using h2

/-! ## Step 5 — the five-fold totalized bundle -/

theorem streamAverage_slowRelevant_nonneg
    {m k : Nat} {sigmaSq : Nat → Real} {K : Set (State n)} (j : Nat)
    (omega : Fin k → Nat → State n × State n) :
    0 ≤ streamAverage (k := k)
      (slowRelevantPositiveScalarFamily m sigmaSq K j) omega := by
  unfold streamAverage Ttc.CVEst.avgOf streamScore
  apply div_nonneg
  · exact Finset.sum_nonneg fun l _ ↦
      slowRelevantPositiveScalarFamily_nonneg j (omega l)
  · positivity

/-- **Deliverable 3 — the analogue of
`Ttc.CVSlowCanonicalPhaseMomentPackage.slowRelevant_stream_and_clipped_moments_all`
at the per-phase factor.**  Five conjuncts, all-natural in `j` (the totalized family is
literally one past `m`), at `k := perPhaseRuntimeSamples n m eps`.  Only the last
conjunct's factor changes: `perPhaseFactor n m (perPhaseRuntimeSamples n m eps) j`
instead of `1 + 8 / (correctedRuntimeSamples m eps : Real)`. -/
theorem slowRelevant_stream_and_clipped_moments_perPhase
    {m : Nat} {eps : Real} (hn : 4 ≤ n) (hnm : (n : Real) ≤ (m : Real) + 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    {sigmaSq : Nat → Real} {K : Set (State n)} (hK : MeasurableSet K)
    {Q : Nat → Kernel (State n) (State n × State n)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × State n)} [IsProbabilityMeasure mu0]
    {V : Nat →
      (Fin (perPhaseRuntimeSamples n m eps) → Nat → State n × State n) → Real}
    (hscalar : ∀ j,
      MemLp (slowRelevantPositiveScalarFamily m sigmaSq K j) 2
        (inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ∧
      ∫ omega, (slowRelevantPositiveScalarFamily m sigmaSq K j omega) ^ 2
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ≤
        sharpTransportedFactor n m j *
          (∫ omega, slowRelevantPositiveScalarFamily m sigmaSq K j omega
            ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0)) ^ 2)
    (hmeanPos : ∀ j, 0 < ∫ omega,
      streamAverage (k := perPhaseRuntimeSamples n m eps)
        (slowRelevantPositiveScalarFamily m sigmaSq K j) omega
      ∂(independentPathLaw (perPhaseRuntimeSamples n m eps)
        (stateScheduleFromSeed Q) mu0))
    (hVdef : ∀ j omega, V j omega =
      min (streamAverage (k := perPhaseRuntimeSamples n m eps)
        (slowRelevantPositiveScalarFamily m sigmaSq K j) omega)
        (correctedAlpha m eps * ∫ z,
          streamAverage (k := perPhaseRuntimeSamples n m eps)
            (slowRelevantPositiveScalarFamily m sigmaSq K j) z
          ∂(independentPathLaw (perPhaseRuntimeSamples n m eps)
            (stateScheduleFromSeed Q) mu0))) :
    (∀ j,
      Integrable (streamAverage (k := perPhaseRuntimeSamples n m eps)
        (slowRelevantPositiveScalarFamily m sigmaSq K j))
        (independentPathLaw (perPhaseRuntimeSamples n m eps)
          (stateScheduleFromSeed Q) mu0)) ∧
    (∀ j, Integrable (fun omega ↦
      (streamAverage (k := perPhaseRuntimeSamples n m eps)
        (slowRelevantPositiveScalarFamily m sigmaSq K j) omega) ^ 2)
        (independentPathLaw (perPhaseRuntimeSamples n m eps)
          (stateScheduleFromSeed Q) mu0)) ∧
    (∀ j, ∫ omega, (streamAverage (k := perPhaseRuntimeSamples n m eps)
        (slowRelevantPositiveScalarFamily m sigmaSq K j) omega) ^ 2
          ∂(independentPathLaw (perPhaseRuntimeSamples n m eps)
            (stateScheduleFromSeed Q) mu0) ≤
      2 * (∫ omega, streamAverage (k := perPhaseRuntimeSamples n m eps)
        (slowRelevantPositiveScalarFamily m sigmaSq K j) omega
          ∂(independentPathLaw (perPhaseRuntimeSamples n m eps)
            (stateScheduleFromSeed Q) mu0)) ^ 2) ∧
    (∀ j, Integrable (fun omega ↦ (V j omega) ^ 2)
      (independentPathLaw (perPhaseRuntimeSamples n m eps)
        (stateScheduleFromSeed Q) mu0)) ∧
    (∀ j, ∫ omega, (V j omega) ^ 2
        ∂(independentPathLaw (perPhaseRuntimeSamples n m eps)
          (stateScheduleFromSeed Q) mu0) ≤
      perPhaseFactor n m (perPhaseRuntimeSamples n m eps) j *
        (∫ omega, V j omega
          ∂(independentPathLaw (perPhaseRuntimeSamples n m eps)
            (stateScheduleFromSeed Q) mu0)) ^ 2) := by
  have hn0 : 0 < n := by omega
  have hnR : (4 : Real) ≤ (n : Real) := by exact_mod_cast hn
  let scalarLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
  let P : Nat := perPhaseRuntimeSamples n m eps
  have hP0 : 0 < P := perPhaseRuntimeSamples_pos n m eps
  have hP2 : 2 ≤ P := two_le_perPhaseRuntimeSamples hn0 heps
  have hPR : (2 : Real) ≤ (P : Real) := by exact_mod_cast hP2
  have hnk : (4 : Real) ≤ (n : Real) * (P : Real) := by nlinarith
  have hstream : ∀ j,
      Integrable (streamAverage (k := P)
        (slowRelevantPositiveScalarFamily m sigmaSq K j))
          (independentStreamLaw scalarLaw) ∧
      Integrable (fun omega ↦ (streamAverage (k := P)
        (slowRelevantPositiveScalarFamily m sigmaSq K j) omega) ^ 2)
          (independentStreamLaw scalarLaw) ∧
      ∫ omega, (streamAverage (k := P)
          (slowRelevantPositiveScalarFamily m sigmaSq K j) omega) ^ 2
          ∂(independentStreamLaw scalarLaw) ≤
        2 * (∫ omega, streamAverage (k := P)
          (slowRelevantPositiveScalarFamily m sigmaSq K j) omega
          ∂(independentStreamLaw scalarLaw)) ^ 2 := by
    intro j
    refine ⟨(memLp_streamAverage (k := P) scalarLaw (hscalar j).1).integrable
        one_le_two,
      integrable_streamAverage_sq (k := P) scalarLaw (hscalar j).1, ?_⟩
    refine (perPhase_streamAverage_sq_le (n := n) (m := m) (k := P) (j := j) hP0
      scalarLaw (measurable_slowRelevantPositiveScalarFamily hK j)
      (hscalar j).1 (hscalar j).2).trans ?_
    exact mul_le_mul_of_nonneg_right
      (averagedPerPhaseFactor_le_two j hnk hP2) (sq_nonneg _)
  have hclip : ∀ j,
      Integrable (fun omega ↦ (V j omega) ^ 2)
        (independentStreamLaw (k := P) scalarLaw) ∧
      ∫ omega, (V j omega) ^ 2 ∂(independentStreamLaw (k := P) scalarLaw) ≤
        perPhaseFactor n m P j *
          (∫ omega, V j omega
            ∂(independentStreamLaw (k := P) scalarLaw)) ^ 2 := by
    intro j
    have h := clipped_sq_moment_le_factor
      (mu := independentStreamLaw (k := P) scalarLaw)
      (alpha := correctedAlpha m eps) (c := averagedPerPhaseFactor n m P j)
      (one_lt_correctedAlpha_of heps heps1)
      (averagedPerPhaseFactor_nonneg j)
      (averagedPerPhaseFactor_le_two j hnk hP2)
      (fun omega ↦ streamAverage_slowRelevant_nonneg j omega)
      (measurable_streamAverage (measurable_slowRelevantPositiveScalarFamily hK j))
      ((memLp_streamAverage (k := P) scalarLaw (hscalar j).1).integrable one_le_two)
      (integrable_streamAverage_sq (k := P) scalarLaw (hscalar j).1)
      (by simpa only [P, scalarLaw, independentPathLaw] using hmeanPos j)
      (perPhase_streamAverage_sq_le (n := n) (m := m) (k := P) (j := j) hP0
        scalarLaw (measurable_slowRelevantPositiveScalarFamily hK j)
        (hscalar j).1 (hscalar j).2)
      (fun omega ↦ by
        simpa only [P, scalarLaw, independentPathLaw] using hVdef j omega)
    exact ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_right
      (clippedFactor_averagedPerPhaseFactor_le (n := n) (m := m) (eps := eps)
        hn0 hnm heps heps1 j) (sq_nonneg _))⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    simpa only [P, scalarLaw, independentPathLaw] using (hstream j).1
  · intro j
    simpa only [P, scalarLaw, independentPathLaw] using (hstream j).2.1
  · intro j
    simpa only [P, scalarLaw, independentPathLaw] using (hstream j).2.2
  · intro j
    simpa only [P, scalarLaw, independentPathLaw] using (hclip j).1
  · intro j
    simpa only [P, scalarLaw, independentPathLaw] using (hclip j).2

/-! ## Step 6 — `hWEpos` at an arbitrary stream count

`Ttc.CVSlowCanonicalMomentBinders.slowCanonical_hWEpos` is stated only at
`k := correctedRuntimeSamples m eps`, but every ingredient of its proof
(`scoreAwareMixError_succ_halfSlack_mean_le_half`, `mix_add_slowTargetError_rAware_scaled_le`,
`slowUniformMeanTailFloor_le_meanBudget`, `slowCanonical_htargetTV`,
`scoreAwareMeanEta_lt_one`) is generic in the stream count.  This is that proof at an
arbitrary `k`; specializing to `k := perPhaseRuntimeSamples n m eps` is what the
per-phase binders need. -/
theorem slowCanonical_hWEpos_atCount
    (hn : 21 ≤ n) (m k : Nat) (hk : 0 < k) {eps R : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {Q : Nat → Kernel (State n) (State n × State n)} [∀ i, IsMarkovKernel (Q i)]
    [IsProbabilityMeasure (slowInitialPair n)]
    {V : Nat → (Fin k → Nat → State n × State n) → Real}
    (hop : IndependentStreamOperational k
      (stateScheduleFromSeed Q) Q Prod.snd (slowInitialPair n) V m eps)
    (htau : ∀ i, i < m → hop.tau i =
      slowLocalPairReference (m + 1) n (slowUniformQ n m k eps R)
        (slowSourceInitialVariance n) K i)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) k (eps / 2)
        (fun t ↦ phaseMomentSlackSeven m
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (fun _ ↦ 2) t / 2)
        (phaseScoreTransportBoundSqSeven R
          (slowSourceSigmaSq n (slowSourceInitialVariance n)))) j) :
    ∀ j, j ≤ m → 0 < ∫ omega, streamAverage (k := k)
      (positiveScalarPhaseFamilyChainLength (Seed := State n) m
        (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
      ∂(independentPathLaw k (stateScheduleFromSeed Q) (slowInitialPair n)) := by
  have hn1 : 1 ≤ n := by omega
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn1
  have hmeanMix : ∀ i : Fin m,
      (hop.mixError (i : Nat)).toReal * Real.exp (R ^ 2 /
          (2 * slowSourceSigmaSq n (slowSourceInitialVariance n) (i : Nat))) ≤
        (scoreAwareMeanEta m k eps *
          (chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
              ((i : Nat) + 1) /
            chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
              (i : Nat))) / 2 := by
    intro i
    rw [hmixError (i : Nat), activeReferenceMixError,
      if_pos (by omega : (i : Nat) + 1 < m + 1)]
    simpa only [mul_comm] using scoreAwareMixError_succ_halfSlack_mean_le_half
      (m := m) (k := k) (chainLength := m) (eps := eps) (R := R)
      (sigmaSq := slowSourceSigmaSq n (slowSourceInitialVariance n))
      (K := K) (C := fun _ ↦ 2) (i := (i : Nat))
      heps heps1 (slowSourceSigmaSq_pos hn1 hs0) hball hfin
      (fun _ ↦ by norm_num) (fun _ ↦ by norm_num)
  have hmeanError : ∀ i : Fin m,
      (hop.mixError (i : Nat) + slowTargetError n
            (rAwareGlobalRadiusQ n R (slowSourceInitialVariance n)
              (slowUniformMeanTailFloor n m k eps R))
            m (i : Nat)).toReal *
          Real.exp (R ^ 2 /
            (2 * slowSourceSigmaSq n (slowSourceInitialVariance n) (i : Nat))) ≤
        scoreAwareMeanEta m k eps *
          (chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
              ((i : Nat) + 1) /
            chain m (slowSourceSigmaSq n (slowSourceInitialVariance n))
              K (i : Nat)) := by
    intro i
    exact mix_add_slowTargetError_rAware_scaled_le hn1 hs0
      (slowUniformMeanTailFloor_pos heps) i.isLt (hop.mixError_ne_top i)
      (hmeanMix i)
      (slowUniformMeanTailFloor_le_meanBudget hn1 heps hK hball hfin (i : Nat))
  exact operational_positiveStreamMean_upto_of_targetTV hk hop
    (slowSourceSigmaSq_pos hn1 hs0) hK hKc hball hfin hKR
    (scoreAwareMeanEta_nonneg m k eps)
    (scoreAwareMeanEta_lt_one m k heps heps1)
    (slowCanonical_htargetTV hop hn1 hK hKc hball hfin htau)
    (slowTargetError_ne_top n _ m) hmeanError

/-! ## Step 7 — the seven frontier binders at the per-phase factor -/

/-- **Deliverable 4 — the analogue of
`Ttc.CVSlowCanonicalMomentBinders.slowCanonical_momentBinders`.**

All seven conjuncts have the frontier's shape.  Exactly two things change relative to
the uniform version, and nothing else:

* `k := perPhaseRuntimeSamples n m eps` in place of `correctedRuntimeSamples m eps`
  (an `n`-fold saving, `perPhaseRuntimeSamples_lt_correctedRuntimeSamples`), and
* `factor := perPhaseFactor n m (perPhaseRuntimeSamples n m eps)` in place of
  `fun _ ↦ 1 + 8 / (correctedRuntimeSamples m eps : Real)` in conjuncts 5, 6, 7.

The mixing schedule (`hmixError`), the reference targets (`htau`) and the mean-tail
floor are the frontier's own, unchanged; the mean-positivity conjunct is discharged from
them by `slowCanonical_hWEpos_atCount`.

The one binder that is *not* the frontier's own is `hscalar`: the uniform version derives
it from `hexact` through the factor-seven transport, which destroys any `n`-dependence
(see the module docstring).  Here it is assumed at the sharp operational family
`sharpTransportedFactor n m j`, which is what the transport
`operational_path_phaseScore_scoreAware_relative_of_targetTV` produces from the sharp
exact-law factor of `Ttc.CVPerPhaseSamples.slowSource_phaseScore_sq_moment_sharp` once the
schedule declares `relativePhaseSlack` in place of `phaseMomentSlackSeven`. -/
theorem slowCanonical_momentBinders_perPhase
    (hn : 21 ≤ n) (m : Nat) (hnm : (n : Real) ≤ (m : Real) + 1)
    {eps R : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {Q : Nat → Kernel (State n) (State n × State n)} [∀ i, IsMarkovKernel (Q i)]
    [IsProbabilityMeasure (slowInitialPair n)]
    (hop : IndependentStreamOperational (perPhaseRuntimeSamples n m eps)
      (stateScheduleFromSeed Q) Q Prod.snd (slowInitialPair n)
      (slowClippedPositiveEmpiricalFamily m (perPhaseRuntimeSamples n m eps) eps Q
        (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n)) K) m eps)
    (htau : ∀ i, i < m → hop.tau i =
      slowLocalPairReference (m + 1) n
        (slowUniformQ n m (perPhaseRuntimeSamples n m eps) eps R)
        (slowSourceInitialVariance n) K i)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) (perPhaseRuntimeSamples n m eps) (eps / 2)
        (fun t ↦ phaseMomentSlackSeven m
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (fun _ ↦ 2) t / 2)
        (phaseScoreTransportBoundSqSeven R
          (slowSourceSigmaSq n (slowSourceInitialVariance n)))) j)
    (hscalar : ∀ j, j ≤ m →
      MemLp (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) 2
        (inhomogeneousPathMeasure (stateScheduleFromSeed Q) (slowInitialPair n)) ∧
      ∫ omega, (positiveScalarPhaseFamilyChainLength (Seed := State n)
            m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega) ^ 2
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
        sharpTransportedFactor n m j *
          (∫ omega, positiveScalarPhaseFamilyChainLength (Seed := State n)
              m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega
            ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q)
              (slowInitialPair n))) ^ 2) :
    (∀ j, j ≤ m → Integrable
      (fun omega ↦ streamAverage (k := perPhaseRuntimeSamples n m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega)
      (independentPathLaw (perPhaseRuntimeSamples n m eps)
        (stateScheduleFromSeed Q) (slowInitialPair n))) ∧
    (∀ j, j ≤ m → Integrable
      (fun omega ↦ (streamAverage (k := perPhaseRuntimeSamples n m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2)
      (independentPathLaw (perPhaseRuntimeSamples n m eps)
        (stateScheduleFromSeed Q) (slowInitialPair n))) ∧
    (∀ j, j ≤ m → 0 < ∫ omega,
      streamAverage (k := perPhaseRuntimeSamples n m eps)
      (positiveScalarPhaseFamilyChainLength (Seed := State n)
        m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
      ∂(independentPathLaw (perPhaseRuntimeSamples n m eps)
        (stateScheduleFromSeed Q) (slowInitialPair n))) ∧
    (∀ j, j ≤ m → ∫ omega,
      (streamAverage (k := perPhaseRuntimeSamples n m eps)
      (positiveScalarPhaseFamilyChainLength (Seed := State n)
        m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2
        ∂(independentPathLaw (perPhaseRuntimeSamples n m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
      2 * (∫ omega, streamAverage (k := perPhaseRuntimeSamples n m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
        ∂(independentPathLaw (perPhaseRuntimeSamples n m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2) ∧
    (∀ _j : Nat, 0 ≤ perPhaseFactor n m (perPhaseRuntimeSamples n m eps) _j) ∧
    (∀ j, j ≤ m → ∫ omega,
        (slowClippedPositiveEmpiricalFamily m (perPhaseRuntimeSamples n m eps) eps Q
          (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n))
          K j omega) ^ 2
        ∂(independentPathLaw (perPhaseRuntimeSamples n m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
      perPhaseFactor n m (perPhaseRuntimeSamples n m eps) j *
        (∫ omega, slowClippedPositiveEmpiricalFamily m
            (perPhaseRuntimeSamples n m eps) eps Q (slowInitialPair n)
            (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega
          ∂(independentPathLaw (perPhaseRuntimeSamples n m eps)
            (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2) ∧
    (∀ i, i ≤ m →
      prefixMomentRatio (perPhaseFactor n m (perPhaseRuntimeSamples n m eps)) i ≤
        1 + eps ^ 2 / 6250) := by
  have hn0 : 0 < n := by omega
  have hn4 : 4 ≤ n := by omega
  have hP0 : 0 < perPhaseRuntimeSamples n m eps := perPhaseRuntimeSamples_pos n m eps
  have hP2 : 2 ≤ perPhaseRuntimeSamples n m eps :=
    two_le_perPhaseRuntimeSamples hn0 heps
  have hPR : (2 : Real) ≤ (perPhaseRuntimeSamples n m eps : Real) := by
    exact_mod_cast hP2
  have hnR : (4 : Real) ≤ (n : Real) := by exact_mod_cast hn4
  have hnk : (4 : Real) ≤ (n : Real) * (perPhaseRuntimeSamples n m eps : Real) := by
    nlinarith
  have hmeanPos := slowCanonical_hWEpos_atCount hn m (perPhaseRuntimeSamples n m eps)
    hP0 heps heps1 hK hKc hball hfin hKR hop htau hmixError
  have hclip := operational_slowCanonical_clippedMoment_bundle_perPhase
    (n := n) (m := m) (eps := eps) hn4 hnm heps heps1 hK
    (Q := Q) (mu0 := slowInitialPair n)
    (V := slowClippedPositiveEmpiricalFamily m (perPhaseRuntimeSamples n m eps) eps Q
      (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n)) K)
    hscalar hmeanPos (fun _ _ _ ↦ rfl)
  have hstream : ∀ j, j ≤ m →
      Integrable (streamAverage (k := perPhaseRuntimeSamples n m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j))
        (independentPathLaw (perPhaseRuntimeSamples n m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)) ∧
      Integrable (fun omega ↦
        (streamAverage (k := perPhaseRuntimeSamples n m eps)
          (positiveScalarPhaseFamilyChainLength (Seed := State n)
            m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2)
        (independentPathLaw (perPhaseRuntimeSamples n m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)) ∧
      ∫ omega, (streamAverage (k := perPhaseRuntimeSamples n m eps)
          (positiveScalarPhaseFamilyChainLength (Seed := State n)
            m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2
          ∂(independentPathLaw (perPhaseRuntimeSamples n m eps)
            (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
        2 * (∫ omega, streamAverage (k := perPhaseRuntimeSamples n m eps)
          (positiveScalarPhaseFamilyChainLength (Seed := State n)
            m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
          ∂(independentPathLaw (perPhaseRuntimeSamples n m eps)
            (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2 := by
    intro j hj
    refine ⟨(memLp_streamAverage (k := perPhaseRuntimeSamples n m eps)
        (inhomogeneousPathMeasure (stateScheduleFromSeed Q) (slowInitialPair n))
        (hscalar j hj).1).integrable one_le_two,
      integrable_streamAverage_sq (k := perPhaseRuntimeSamples n m eps)
        (inhomogeneousPathMeasure (stateScheduleFromSeed Q) (slowInitialPair n))
        (hscalar j hj).1, ?_⟩
    refine (perPhase_streamAverage_sq_le (n := n) (m := m)
      (k := perPhaseRuntimeSamples n m eps) (j := j) hP0
      (inhomogeneousPathMeasure (stateScheduleFromSeed Q) (slowInitialPair n))
      (measurable_positiveScalarPhaseFamilyChainLength hK j)
      (hscalar j hj).1 (hscalar j hj).2).trans ?_
    exact mul_le_mul_of_nonneg_right
      (averagedPerPhaseFactor_le_two j hnk hP2) (sq_nonneg _)
  refine ⟨fun j hj ↦ (hstream j hj).1, fun j hj ↦ (hstream j hj).2.1, hmeanPos,
    fun j hj ↦ (hstream j hj).2.2, fun j ↦ perPhaseFactor_nonneg j,
    fun j hj ↦ (hclip j hj).2, fun i hi ↦ ?_⟩
  exact perPhase_prefixMomentRatio_le hn0 hP0 heps heps1
    (perPhaseRuntimeSamples_budget hn0 heps) hi

/-! ## Step 8 — the index convention against P2's sharp exact-law moment

`Ttc.CVPerPhaseSamples.slowSource_phaseScore_sq_moment_sharp` is stated at *schedule*
phase `i` with the branch `i + 1 < m`.  The recursion reads it at *recursion* phase
`j = i + 1` (`positiveScalarPhaseFamilyChainLength` is
`| i + 1 => scalarPhaseScore chainLength sigmaSq K i`), where the branch is `j < m` —
the branch of `sharpExactFactor` and of `Ttc.CVPerPhaseSamples.perPhaseFactor`.  The two
statements below pin that as a machine check rather than a comment. -/

theorem sharpExactFactor_succ_eq (n m i : Nat) :
    (if i + 1 < m then 1 + 2 / (n : Real) else 2) = sharpExactFactor n m (i + 1) := rfl

/-- P2's sharp exact-law per-phase moment, restated at the recursion's index and at
`sharpExactFactor`.  This is `Ttc.CVPerPhaseSamples.slowSource_phaseScore_sq_moment_sharp`
verbatim, with the `if` folded into the named family. -/
theorem slowSource_phaseScore_sq_moment_sharpExact
    {n : Nat} (hn : 3 ≤ n) {N s0 R : Real} (hN : 0 < N) (hs0 : 0 < s0)
    (hsN : s0 ≤ N) (hR2 : R ^ 2 ≤ N)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R) (i : Nat) :
    let m := slowSourcePhases n N s0 + 1
    let sigmaSq := slowSourceSigmaSq n s0
    ∫ x, phaseScore m sigmaSq (interior K) i x ^ 2 ∂(coolLaw m sigmaSq K i) ≤
      sharpExactFactor n m (i + 1) *
        (∫ x, phaseScore m sigmaSq (interior K) i x
          ∂(coolLaw m sigmaSq K i)) ^ 2 :=
  slowSource_phaseScore_sq_moment_sharp hn hN hs0 hsN hR2 hK hKc hball hfin hKR i

/-- The brief-literal shape: an `hscalar` hypothesis at the *exact* sharp family
`sharpExactFactor` is in particular one at the transported family, so every bundle above
applies to it unchanged.  (The converse fails, and it is the transported shape that is
dischargeable — see the module docstring.) -/
theorem sq_moment_sharpTransported_of_sharpExact
    {Path : Type*} [MeasurableSpace Path] {n m j : Nat} (hn : 0 < n)
    {mu : Measure Path} {g : Path → Real}
    (h : ∫ x, (g x) ^ 2 ∂mu ≤ sharpExactFactor n m j * (∫ x, g x ∂mu) ^ 2) :
    ∫ x, (g x) ^ 2 ∂mu ≤ sharpTransportedFactor n m j * (∫ x, g x ∂mu) ^ 2 :=
  h.trans (mul_le_mul_of_nonneg_right
    (sharpExactFactor_le_sharpTransportedFactor hn m j) (sq_nonneg _))

/-! ## Step 9 — the transported hypothesis is dischargeable, machine-checked

The bundles above assume the operational scalar moment at `sharpTransportedFactor`.  The
theorem below shows this is not an idle assumption (`CLAUDE.md` §11, non-vacuity): it is
exactly what `Ttc.CVGaussianSourceWeightedMoment`'s TV transport delivers from P2's sharp
*exact-law* factor, against the slack `(C - 1)·ratio²` — which is `(2/n)·ratio²` on
interior phases and `ratio²` at the terminal one.  Only that slack inequality is left
open, and it is a statement about the *mixing schedule*, i.e. about how many local steps
each phase runs — a runtime cost, not a stream count.  Declaring it is the existing-file
change this file deliberately does not make. -/

theorem sharpExactFactor_nonneg {n : Nat} (hn : 0 < n) (m j : Nat) :
    0 ≤ sharpExactFactor n m j := by
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  unfold sharpExactFactor
  split
  · positivity
  · norm_num

/-- **The sharp operational per-phase moment, from the sharp exact-law one.**  This is
`Ttc.CVGaussianSourceWeightedMoment.operational_path_phaseScore_memLp_and_sq_moment_le_factor_of_targetTV`
at `C := sharpExactFactor n m (i+1)`, `T := sharpTransportedFactor n m (i+1) = 2·C - 1`.
Its conclusion is precisely the `hscalar` slot of
`operational_slowCanonical_clippedMoment_bundle_perPhase` at the schedule's phase `i`. -/
theorem operational_phaseScore_sharpTransported_of_slack
    {k mPhases m i : Nat} (hn : 0 < n)
    {Q : Nat → Kernel (State n) (State n × State n)} [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × State n)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → State n × State n) → Real} {eta : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V mPhases eta)
    {sigmaSq : Nat → Real} {K : Set (State n)} {R : Real}
    (hsigma : ∀ j, 0 < sigmaSq j) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {targetError : ENNReal}
    (htargetTV : TVLe (Measure.map Prod.fst (hop.tau i))
      (coolLaw m sigmaSq K i) targetError)
    (htargetError : targetError ≠ ⊤)
    (hexact : ∫ x, phaseScore m sigmaSq (interior K) i x ^ 2
        ∂(coolLaw m sigmaSq K i) ≤
      sharpExactFactor n m (i + 1) *
        (∫ x, phaseScore m sigmaSq (interior K) i x
          ∂(coolLaw m sigmaSq K i)) ^ 2)
    (hslack : (hop.mixError i + targetError).toReal *
        (Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2 *
          (1 + 2 * sharpTransportedFactor n m (i + 1))) ≤
      (sharpExactFactor n m (i + 1) - 1) *
        (chain m sigmaSq K (i + 1) / chain m sigmaSq K i) ^ 2) :
    let pathLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
    let g := fun omega : Nat → State n × State n ↦
      phaseScore m sigmaSq (interior K) i (omega (i + 1)).1
    MemLp g 2 pathLaw ∧
      (∫ omega, (g omega) ^ 2 ∂pathLaw) ≤
        sharpTransportedFactor n m (i + 1) * (∫ omega, g omega ∂pathLaw) ^ 2 := by
  have hCT : sharpExactFactor n m (i + 1) ≤ sharpTransportedFactor n m (i + 1) :=
    sharpExactFactor_le_sharpTransportedFactor hn m (i + 1)
  have hslack' : (hop.mixError i + targetError).toReal *
      (Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2 *
        (1 + 2 * sharpTransportedFactor n m (i + 1))) ≤
      (sharpTransportedFactor n m (i + 1) - sharpExactFactor n m (i + 1)) *
        (chain m sigmaSq K (i + 1) / chain m sigmaSq K i) ^ 2 := by
    have heq : sharpTransportedFactor n m (i + 1) - sharpExactFactor n m (i + 1)
        = sharpExactFactor n m (i + 1) - 1 := by
      rw [sharpTransportedFactor_eq]; ring
    rw [heq]
    exact hslack
  exact operational_path_phaseScore_memLp_and_sq_moment_le_factor_of_targetTV
    (C := sharpExactFactor n m (i + 1))
    (T := sharpTransportedFactor n m (i + 1))
    hop hsigma hKc hball hfin hKR htargetTV htargetError
    (sharpExactFactor_nonneg hn m (i + 1)) hCT hexact hslack'

/-! ## Axiom audit (`CLAUDE.md` §4) -/

#print axioms two_le_perPhaseRuntimeSamples
#print axioms nmul_perPhaseRuntimeSamples_le_three_correctedAlpha
#print axioms nmul_perPhaseRuntimeSamples_add_eight_le_four_correctedAlpha
#print axioms four_over_clipping_sq_le_eight_of_nearby
#print axioms perPhaseRuntime_interior_clipping_four
#print axioms perPhaseRuntimeSamples_lt_correctedRuntimeSamples
#print axioms sharpTransportedFactor_eq
#print axioms sharpExactFactor_le_sharpTransportedFactor
#print axioms averagedPerPhaseFactor_eq
#print axioms averagedPerPhaseFactor_nonneg
#print axioms averagedPerPhaseFactor_le_two
#print axioms perPhase_streamAverage_sq_le
#print axioms clippedFactor_averagedPerPhaseFactor_le
#print axioms streamAverage_positiveScalar_nonneg
#print axioms one_lt_correctedAlpha_of
#print axioms operational_slowCanonical_clippedMoment_bundle_perPhase
#print axioms streamAverage_slowRelevant_nonneg
#print axioms slowRelevant_stream_and_clipped_moments_perPhase
#print axioms slowCanonical_hWEpos_atCount
#print axioms slowCanonical_momentBinders_perPhase
#print axioms sharpExactFactor_succ_eq
#print axioms slowSource_phaseScore_sq_moment_sharpExact
#print axioms sq_moment_sharpTransported_of_sharpExact
#print axioms sharpExactFactor_nonneg
#print axioms operational_phaseScore_sharpTransported_of_slack

end Ttc.CVPerPhaseMomentBundle
