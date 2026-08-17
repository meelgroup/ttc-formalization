import Ttc.Exec.CVSlowCanonicalHopAssembly
import Ttc.Exec.CVSlowCanonicalMomentBinders
import Ttc.Exec.CVSlowCanonicalUniformParameters
import Ttc.Exec.CVSlowCanonicalAccuracyBudget

/-!
# The slow canonical one-run certificate at the canonical parameter choices

`Ttc.CVSlowCanonicalRobustCertificate.exists_sourceReferenceTVOneRunCertificate_slowCanonical_of_weightedData`
is the frontier composition theorem for the honest slow sampler.  It carries a long list
of binders, most of which are *schedule selections* rather than genuine mathematical
obligations.  This file instantiates every one of those selections at the canonical
choices and discharges every binder that today's development can close, leaving a short,
explicitly named residual list.

## The canonical choices

* `N := max 1 R2`, where `R2` is a declared squared-radius budget for the body;
* `m := slowCanonicalPhases n R2 = slowOperationalPhases n (max 1 R2) + 1`;
* `k := correctedRuntimeSamples m eps`;
* `C := fun _ ↦ 2`, `q`, `slack`, `boundSq`, `meanTailFloor` from
  `Ttc.CVSlowCanonicalUniformParameters`;
* `beta := scoreAwareAccuracyBeta m k eps`, `requested := slowAccuracyRequested m k eps`;
* `scoreScale := 0`;
* `initialNormalizer := chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K 0`
  and `volumeTarget := (volume K).toReal`, the latter pinned to the chain endpoint by
  `Arlib.GaussianCooling.chain_end`, so the certificate's accuracy interval is literally
  `[(1 - requested) * Vol(K), (1 + requested) * Vol(K)]`.

## What remains a binder, and why

1. `hWint`, `hW2int`, `hWEpos`, `hrawSecond`, `hphaseMoment` — the five estimator-moment
   facts in the frontier's **unguarded** `∀ j` shapes.
   `Ttc.CVSlowCanonicalMomentBinders.slowCanonical_momentBinders` proves all five, but
   only on the estimator prefix `j ≤ m`: beyond `m` the untotalized positive scalar family
   degenerates to the indicator of `interior K`, and no ingredient of the development
   bounds the probability of that event from below.  Closing the tail is the job of
   `Ttc/Exec/CVSlowCanonicalTailPhases.lean`.
2. `runtimeConstant`, `T`, `L`, `hsteps`, `hretries`, `hscalar` — the cost side, copied
   verbatim from the frontier (note the internal accuracy `eps / 2` in every
   `scoreAware*` argument).  These belong to
   `Ttc/Exec/CVSlowEffectiveOverhead.lean`.
3. `R` and `hKR : K ⊆ closedBall 0 R` — the declared radius of the body.
4. `Q`, its Markov instance and `hQ` — purely definitional binders in the frontier's own
   style; a caller supplies `hQ := rfl`.

Everything else — the eleven schedule side conditions, the three accuracy binders, the
`hop` / `htau` / `hmixError` triple, `hfactor0`, `hprefix`, the analytic `hexact`, the
chain endpoints and the probability-measure instances — is discharged here.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Ttc.CVSlowOneRunValid

open MeasureTheory ProbabilityTheory Metric Set Finset
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVCorrected Ttc.CVCorrectedRuntime
open Ttc.CVIndependentStreamDependence Ttc.CVIndependentStreamMoments
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVGaussianScoreAwareParameters Ttc.CVGaussianScoreAwareMeanBudget
open Ttc.CVGaussianFactorSevenAssembly
open Ttc.CVGaussianHybridWeightedCertificate
open Ttc.CVHeterogeneousRetainedPathLaw Ttc.CVHeterogeneousHistoryReference
open Ttc.CVRelativeMeanClippingAssembly Ttc.CVSlowRadiusQCanonicalOperational
open Ttc.CVSourceReferenceTVCapstone
open Ttc.CVRAwareGlobalRadius
open Ttc.CVSlowFullBodySourceSchedule Ttc.CVSlowSourceReferenceCertificate
open Ttc.CVSlowRadiusQReferencePhaseTV Ttc.CVSlowCanonicalRetainedReference
open Ttc.CVSlowCanonicalRobustCertificate
open Ttc.CVSlowCanonicalUniformParameters
open Ttc.CVSlowCanonicalHopAssembly
open Ttc.CVSlowCanonicalMomentBinders
open Ttc.CVSlowCanonicalAccuracyBudget
open scoped ENNReal Classical BigOperators

variable {n : Nat}

/-- The state space of one cooling stream. -/
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- One recorded pair (state, raw seed) of one cooling stream. -/
abbrev ScoreSeed (n : Nat) := State n × State n

/-! ## Step 1 — the canonical phase count -/

/-- The canonical number of cooling phases at declared squared radius `R2`: the slow
operational phase count at terminal variance `max 1 R2`, plus one.

The `+ 1` is deliberate.  It makes the frontier's `0 < m` free, and it aligns `m` with
`Ttc.CVSlowCanonicalMomentBinders.slowCanonical_hexact_at_slowPhases`, which is stated at
`slowSourcePhases n N (slowSourceInitialVariance n) + 1`. -/
noncomputable def slowCanonicalPhases (n : Nat) (R2 : Real) : Nat :=
  slowOperationalPhases n (max 1 R2) + 1

theorem slowCanonicalPhases_eq (n : Nat) (R2 : Real) :
    slowCanonicalPhases n R2 =
      slowSourcePhases n (max 1 R2) (slowSourceInitialVariance n) + 1 := rfl

theorem slowCanonicalPhases_pos (n : Nat) (R2 : Real) :
    0 < slowCanonicalPhases n R2 := Nat.succ_pos _

/-- The canonical terminal variance is positive. -/
theorem one_le_canonicalN (R2 : Real) : (1 : Real) ≤ max 1 R2 := le_max_left _ _

theorem canonicalN_pos (R2 : Real) : (0 : Real) < max 1 R2 :=
  lt_of_lt_of_le one_pos (one_le_canonicalN R2)

/-- The canonical initial variance sits below the canonical terminal variance. -/
theorem slowSourceInitialVariance_le_canonicalN (hn : 21 ≤ n) (R2 : Real) :
    slowSourceInitialVariance n ≤ max 1 R2 := by
  have hn0 : (21 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have h1 : slowSourceInitialVariance n ≤ 1 := by
    unfold slowSourceInitialVariance
    rw [div_le_one (by linarith)]
    linarith
  exact h1.trans (one_le_canonicalN R2)

/-! ## Step 2 — the canonical radius -/

/-- The canonical truncation radius is at least four. -/
theorem canonical_hq4 (hn : 21 ≤ n) (R2 eps R : Real) :
    4 ≤ slowUniformQ n (slowCanonicalPhases n R2)
      (correctedRuntimeSamples (slowCanonicalPhases n R2) eps) eps R :=
  four_le_slowUniformQ (by omega) _ _ eps R

theorem canonical_hq0 (hn : 21 ≤ n) (R2 eps R : Real) :
    (0 : Real) < slowUniformQ n (slowCanonicalPhases n R2)
      (correctedRuntimeSamples (slowCanonicalPhases n R2) eps) eps R :=
  lt_of_lt_of_le (by norm_num) (canonical_hq4 hn R2 eps R)

theorem canonical_hs0 (hn : 21 ≤ n) : 0 < slowSourceInitialVariance n :=
  slowSourceInitialVariance_pos (by omega)

/-! ## Step 3 — the probability-measure instances -/

theorem canonical_isProbabilityMeasure_slowInitialPair (hn : 21 ≤ n) :
    IsProbabilityMeasure (slowInitialPair n) := by
  unfold slowInitialPair
  letI : IsProbabilityMeasure (slowInitialSeed n) :=
    isProbabilityMeasure_slowInitialSeed (by omega)
  exact Measure.isProbabilityMeasure_map
    ((by fun_prop : Measurable (fun y : State n ↦ ((0 : State n), y))).aemeasurable)

theorem canonical_isProbabilityMeasure_slowStationaryTail
    (hn : 21 ≤ n) {R2 eps R : Real} {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K) (j : Nat) :
    IsProbabilityMeasure (slowStationaryTail n
      (slowUniformQ n (slowCanonicalPhases n R2)
        (correctedRuntimeSamples (slowCanonicalPhases n R2) eps) eps R)
      (slowSourceInitialVariance n) K j) :=
  isProbabilityMeasure_slowStationaryTail (by omega) (canonical_hq0 hn R2 eps R)
    (canonical_hs0 hn) hK hKc hball
    (fun r ↦ one_le_slow_radius (by omega) (canonical_hq4 hn R2 eps R) (by rfl) r) j

/-- The canonical seed schedule really is a Markov schedule, so the `Q` /
`[∀ i, IsMarkovKernel (Q i)]` / `hQ` binders of `exists_slowOneRunCertificate_canonical`
are instantiable, with `hQ := rfl`. -/
theorem canonical_isMarkovKernel_activeSchedule
    (hn : 21 ≤ n) {eps R R2 : Real} {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K) (i : Nat) :
    IsMarkovKernel (slowCanonicalActiveSchedule (by omega : 1 ≤ n)
      (slowCanonicalPhases n R2 + 1)
      (correctedRuntimeSamples (slowCanonicalPhases n R2) eps)
      (q := slowUniformQ n (slowCanonicalPhases n R2)
        (correctedRuntimeSamples (slowCanonicalPhases n R2) eps) eps R)
      (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (canonical_hq0 hn R2 eps R) (canonical_hs0 hn) K hK 0 slowReferenceWarm
      (slowUniformSlack n (slowCanonicalPhases n R2) K) (slowUniformBoundSq n R) i) := by
  letI : ∀ j, IsProbabilityMeasure (slowStationaryTail n
      (slowUniformQ n (slowCanonicalPhases n R2)
        (correctedRuntimeSamples (slowCanonicalPhases n R2) eps) eps R)
      (slowSourceInitialVariance n) K j) := fun j ↦
    canonical_isProbabilityMeasure_slowStationaryTail hn hK hKc hball j
  infer_instance

/-! ## Step 4 — the chain endpoints -/

theorem canonical_chain_zero_nonneg (hn : 21 ≤ n) (R2 : Real)
    {K : Set (State n)} (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤) :
    0 ≤ chain (slowCanonicalPhases n R2)
      (slowSourceSigmaSq n (slowSourceInitialVariance n)) K 0 :=
  (chain_pos (slowSourceSigmaSq_pos (by omega) (canonical_hs0 hn)) hball hfin 0).le

/-- The chain endpoint is the volume, on the nose. -/
theorem slowCanonical_volumeTarget_eq (n : Nat) (R2 : Real) (K : Set (State n)) :
    chain (slowCanonicalPhases n R2)
      (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
      (slowCanonicalPhases n R2) = (volume K).toReal :=
  chain_end _ _ K

/-! ## Step 5 — the analytic exact-moment binder -/

/-- The single analytic binder of
`Ttc.CVSlowCanonicalMomentBinders.slowCanonical_momentBinders`, discharged at the
canonical phase count.  The only new input is `hR2 : R ^ 2 ≤ R2`, i.e. that `R2` really
is a declared squared-radius budget for the body. -/
theorem canonical_hexact (hn : 21 ≤ n) {R R2 : Real} (hR2 : R ^ 2 ≤ R2)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R) :
    ∀ j,
      ∫ x, phaseScore (slowCanonicalPhases n R2)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) (interior K) j x ^ 2
        ∂(coolLaw (slowCanonicalPhases n R2)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) ≤
      2 * (∫ x, phaseScore (slowCanonicalPhases n R2)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) (interior K) j x
        ∂(coolLaw (slowCanonicalPhases n R2)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j)) ^ 2 :=
  slowCanonical_hexact_at_slowPhases hn (canonicalN_pos R2)
    (slowSourceInitialVariance_le_canonicalN hn R2)
    (hR2.trans (le_max_right 1 R2)) hK hKc hball hfin hKR

/-! ## Step 6 — the canonical one-run certificate -/

/-- **The slow canonical one-run certificate at the canonical parameter choices.**

Every schedule selection of
`Ttc.CVSlowCanonicalRobustCertificate.exists_sourceReferenceTVOneRunCertificate_slowCanonical_of_weightedData`
is instantiated:
`m := slowCanonicalPhases n R2`, `k := correctedRuntimeSamples m eps`,
`C := 2`, `q := slowUniformQ …`, `slack := slowUniformSlack …`,
`boundSq := slowUniformBoundSq …`, `meanTailFloor := slowUniformMeanTailFloor …`,
`beta := scoreAwareAccuracyBeta m k eps`, `requested := slowAccuracyRequested m k eps`,
`scoreScale := 0`, `initialNormalizer := chain m σsq K 0`,
`volumeTarget := (volume K).toReal`.

The residual hypotheses are exactly: the five unguarded estimator-moment facts (tail
phases), the six cost-side binders, the declared radius `R` with `hKR`, and the
definitional schedule binder `Q`/`hQ`. -/
theorem exists_slowOneRunCertificate_canonical
    (hn : 21 ≤ n) {eps R R2 : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hR2 : R ^ 2 ≤ R2)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    (hQ : Q = slowCanonicalActiveSchedule (by omega : 1 ≤ n)
      (slowCanonicalPhases n R2 + 1)
      (correctedRuntimeSamples (slowCanonicalPhases n R2) eps)
      (q := slowUniformQ n (slowCanonicalPhases n R2)
        (correctedRuntimeSamples (slowCanonicalPhases n R2) eps) eps R)
      (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (canonical_hq0 hn R2 eps R) (canonical_hs0 hn) K hK 0 slowReferenceWarm
      (slowUniformSlack n (slowCanonicalPhases n R2) K) (slowUniformBoundSq n R))
    (hWint : ∀ j, Integrable
      (fun omega ↦ streamAverage
        (k := correctedRuntimeSamples (slowCanonicalPhases n R2) eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          (slowCanonicalPhases n R2)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega)
      (independentPathLaw (correctedRuntimeSamples (slowCanonicalPhases n R2) eps)
        (stateScheduleFromSeed Q) (slowInitialPair n)))
    (hW2int : ∀ j, Integrable
      (fun omega ↦ (streamAverage
        (k := correctedRuntimeSamples (slowCanonicalPhases n R2) eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          (slowCanonicalPhases n R2)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2)
      (independentPathLaw (correctedRuntimeSamples (slowCanonicalPhases n R2) eps)
        (stateScheduleFromSeed Q) (slowInitialPair n)))
    (hWEpos : ∀ j, 0 < ∫ omega, streamAverage
        (k := correctedRuntimeSamples (slowCanonicalPhases n R2) eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          (slowCanonicalPhases n R2)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
      ∂(independentPathLaw (correctedRuntimeSamples (slowCanonicalPhases n R2) eps)
        (stateScheduleFromSeed Q) (slowInitialPair n)))
    (hrawSecond : ∀ j, ∫ omega, (streamAverage
        (k := correctedRuntimeSamples (slowCanonicalPhases n R2) eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          (slowCanonicalPhases n R2)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2
        ∂(independentPathLaw (correctedRuntimeSamples (slowCanonicalPhases n R2) eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
      2 * (∫ omega, streamAverage
        (k := correctedRuntimeSamples (slowCanonicalPhases n R2) eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          (slowCanonicalPhases n R2)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
        ∂(independentPathLaw (correctedRuntimeSamples (slowCanonicalPhases n R2) eps)
          (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2)
    (hphaseMoment : ∀ j, ∫ omega,
          (slowClippedPositiveEmpiricalFamily (slowCanonicalPhases n R2)
            (correctedRuntimeSamples (slowCanonicalPhases n R2) eps) eps Q
            (slowInitialPair n)
            (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega) ^ 2
        ∂(independentPathLaw (correctedRuntimeSamples (slowCanonicalPhases n R2) eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
      (1 + 8 / (correctedRuntimeSamples (slowCanonicalPhases n R2) eps : Real)) *
        (∫ omega, slowClippedPositiveEmpiricalFamily (slowCanonicalPhases n R2)
            (correctedRuntimeSamples (slowCanonicalPhases n R2) eps) eps Q
            (slowInitialPair n)
            (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega
          ∂(independentPathLaw (correctedRuntimeSamples (slowCanonicalPhases n R2) eps)
            (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2)
    {runtimeConstant : Real} (T L : Nat)
    (hsteps : ∀ i, i < slowCanonicalPhases n R2 →
      slowCanonicalSteps slowReferenceWarm n
        (slowUniformQ n (slowCanonicalPhases n R2)
          (correctedRuntimeSamples (slowCanonicalPhases n R2) eps) eps R)
        (slowSourceInitialVariance n) K
        (scoreAwareRetries (slowCanonicalPhases n R2 + 1)
          (correctedRuntimeSamples (slowCanonicalPhases n R2) eps) (eps / 2)
          (slowUniformSlack n (slowCanonicalPhases n R2) K) (slowUniformBoundSq n R))
        (scoreAwareEta (slowCanonicalPhases n R2 + 1)
          (correctedRuntimeSamples (slowCanonicalPhases n R2) eps) (eps / 2)
          (slowUniformSlack n (slowCanonicalPhases n R2) K) (slowUniformBoundSq n R))
        (scoreAwareZeta (slowCanonicalPhases n R2 + 1)
          (correctedRuntimeSamples (slowCanonicalPhases n R2) eps) (eps / 2)
          (slowUniformSlack n (slowCanonicalPhases n R2) K) (slowUniformBoundSq n R))
        i 0 ≤ T)
    (hretries : ∀ i, i < slowCanonicalPhases n R2 →
      scoreAwareRetries (slowCanonicalPhases n R2 + 1)
        (correctedRuntimeSamples (slowCanonicalPhases n R2) eps) (eps / 2)
        (slowUniformSlack n (slowCanonicalPhases n R2) K) (slowUniformBoundSq n R) i ≤ L)
    (hscalar : ((correctedRuntimeSamples (slowCanonicalPhases n R2) eps : Nat) : ENNReal) *
        ((slowCanonicalPhases n R2 : Nat) : ENNReal) * ENNReal.ofReal
          (10 * (L : Real) * (T : Real) * (2 * Real.exp 1)) ≤
      Ttc.CVSourcePolynomialCutoffCapstone.sourceOneRunQueryBudget
        runtimeConstant n R
        (slowAccuracyRequested (slowCanonicalPhases n R2)
          (correctedRuntimeSamples (slowCanonicalPhases n R2) eps) eps)) :
    ∃ reference : Measure
        (Fin (correctedRuntimeSamples (slowCanonicalPhases n R2) eps) →
          HeterogeneousHistoryState (State n) (State n)),
      SourceReferenceTVOneRunCertificate
        (@independentHeterogeneousRetainedPathLaw _ _ _ _
          (correctedRuntimeSamples (slowCanonicalPhases n R2) eps)
          (slowCanonicalCostedActiveSchedule (by omega : 1 ≤ n)
            (slowCanonicalPhases n R2 + 1)
            (correctedRuntimeSamples (slowCanonicalPhases n R2) eps)
            (q := slowUniformQ n (slowCanonicalPhases n R2)
              (correctedRuntimeSamples (slowCanonicalPhases n R2) eps) eps R)
            (eps := eps / 2) (s0 := slowSourceInitialVariance n)
            (canonical_hq0 hn R2 eps R) (canonical_hs0 hn) K hK 0 slowReferenceWarm
            (slowUniformSlack n (slowCanonicalPhases n R2) K) (slowUniformBoundSq n R))
          (by
            letI : ∀ j, IsProbabilityMeasure (slowStationaryTail n
                (slowUniformQ n (slowCanonicalPhases n R2)
                  (correctedRuntimeSamples (slowCanonicalPhases n R2) eps) eps R)
                (slowSourceInitialVariance n) K j) := fun j ↦
              canonical_isProbabilityMeasure_slowStationaryTail hn hK hKc hball j
            intro i; infer_instance)
          (slowInitialPair n) (slowCanonicalPhases n R2))
        reference (fun omega ↦ ∑ j, (omega j).1.1)
        (fun omega ↦ gaussianScorePrefixReadout (slowCanonicalPhases n R2)
          (slowCanonicalPhases n R2)
          (correctedRuntimeSamples (slowCanonicalPhases n R2) eps)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
          (chain (slowCanonicalPhases n R2)
            (slowSourceSigmaSq n (slowSourceInitialVariance n)) K 0)
          (independentStoredScorePrefixCurrent (slowCanonicalPhases n R2) omega))
        runtimeConstant n R
        (slowAccuracyRequested (slowCanonicalPhases n R2)
          (correctedRuntimeSamples (slowCanonicalPhases n R2) eps) eps)
        ((1 - slowAccuracyRequested (slowCanonicalPhases n R2)
          (correctedRuntimeSamples (slowCanonicalPhases n R2) eps) eps) *
            (volume K).toReal)
        ((1 + slowAccuracyRequested (slowCanonicalPhases n R2)
          (correctedRuntimeSamples (slowCanonicalPhases n R2) eps) eps) *
            (volume K).toReal) := by
  have hn1 : 1 ≤ n := by omega
  haveI : IsProbabilityMeasure (slowInitialPair n) :=
    canonical_isProbabilityMeasure_slowInitialPair hn
  haveI : ∀ j, IsProbabilityMeasure (slowStationaryTail n
      (slowUniformQ n (slowCanonicalPhases n R2)
        (correctedRuntimeSamples (slowCanonicalPhases n R2) eps) eps R)
      (slowSourceInitialVariance n) K j) := fun j ↦
    canonical_isProbabilityMeasure_slowStationaryTail hn hK hKc hball j
  obtain ⟨hbC1, hbC7, hbslack, hbbound, hbfloor, hbq4, hbqRAware, hbrad,
    hbslackDef, hbboundDef, hbmeanTail⟩ :=
    slowUniformParameters_valid (n := n) hn1 (slowCanonicalPhases n R2)
      (correctedRuntimeSamples (slowCanonicalPhases n R2) eps) (R := R) heps hK hball hfin
  obtain ⟨hop, htau, hmixError⟩ := exists_slowCanonicalHop_literal hn
    (slowCanonicalPhases n R2)
    (correctedRuntimeSamples (slowCanonicalPhases n R2) eps)
    (correctedRuntimeSamples_pos _ _) hbq4 heps heps1 hK hKc hball hfin (0 : Real)
    hbslack hbbound hQ
  obtain ⟨-, -, -, -, hfactor0, -, hprefix⟩ :=
    slowCanonical_momentBinders hn (slowCanonicalPhases n R2) heps heps1 hK hKc hball
      hfin hKR hop htau hmixError (canonical_hexact hn hR2 hK hKc hball hfin hKR)
  exact exists_sourceReferenceTVOneRunCertificate_slowCanonical_of_weightedData
    hn (slowCanonicalPhases n R2)
    (correctedRuntimeSamples (slowCanonicalPhases n R2) eps)
    (slowCanonicalPhases_pos n R2) (correctedRuntimeSamples_pos _ _)
    hbq4 heps heps1 (scoreAwareAccuracyBeta_nonneg _ _ heps)
    (slowAccuracyBudget_le _ _ eps)
    hK hKc hball hfin hKR hbfloor hbqRAware hbrad
    (slowUniformSlack n (slowCanonicalPhases n R2) K) (slowUniformBoundSq n R)
    hbslack hbbound (0 : Real) hQ _ rfl hop htau hmixError
    hbslackDef hbboundDef hbC7 hbmeanTail hbC1
    hWint hW2int hWEpos hrawSecond hfactor0 hphaseMoment hprefix
    (chain (slowCanonicalPhases n R2)
      (slowSourceSigmaSq n (slowSourceInitialVariance n)) K 0)
    (volume K).toReal
    (canonical_chain_zero_nonneg hn R2 hball hfin) ENNReal.toReal_nonneg
    rfl (slowCanonical_volumeTarget_eq n R2 K).symm (le_refl _)
    T L hsteps hretries hscalar

#print axioms exists_slowOneRunCertificate_canonical
#print axioms canonical_hexact
#print axioms slowCanonicalPhases_eq
#print axioms slowSourceInitialVariance_le_canonicalN
#print axioms canonical_hq4
#print axioms canonical_isProbabilityMeasure_slowInitialPair
#print axioms canonical_isProbabilityMeasure_slowStationaryTail
#print axioms canonical_isMarkovKernel_activeSchedule
#print axioms canonical_chain_zero_nonneg
#print axioms slowCanonical_volumeTarget_eq

end Ttc.CVSlowOneRunValid
