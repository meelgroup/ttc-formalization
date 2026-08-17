import Ttc.Exec.CVSlowCanonicalMomentInstantiation

/-!
# The estimator-moment binders of the slow canonical frontier theorem

`Ttc.CVSlowCanonicalRobustCertificate.exists_sourceReferenceTVOneRunCertificate_slowCanonical_of_weightedData`
takes seven estimator-moment hypotheses — `hWint`, `hW2int`, `hWEpos`, `hrawSecond`,
`hfactor0`, `hphaseMoment`, `hprefix` — as binders.  This file discharges them from
the analytic phase-moment package, at

* `k := correctedRuntimeSamples m eps`,
* `factor := fun _ ↦ 1 + 8 / (correctedRuntimeSamples m eps : Real)`,
* `C := fun _ ↦ 2` (see below),
* `q := slowUniformQ n m (correctedRuntimeSamples m eps) eps R`.

Two honest scope notes, both recorded in the statements themselves.

**Range.**  Five of the seven conjuncts are delivered in the guarded form
`∀ j, j ≤ m → …`, whereas the frontier binds them for **all** `j`.  This is forced:
for `j = i + 1 > m` the raw coordinate
`positiveScalarPhaseFamilyChainLength m sigmaSq K j omega` is
`Set.indicator (interior K) (coolRatio m sigmaSq i) ((omega j).1)`, which by
`Arlib.GaussianCooling.coolRatio_of_ge` is the *indicator of `interior K`* — not the
constant one.  `hWEpos` and `hrawSecond` at such `j` therefore require a quantitative
lower bound on the probability that the path sits in `interior K` at time `j`, a fact
no ingredient of the development supplies.  The totalized family
`slowRelevantPositiveScalarFamily` exists precisely to sidestep this, but the
frontier's own `V` (`slowClippedPositiveEmpiricalFamily`) is built from the untotalized
family, so the totalization is not available at the frontier's binder shapes.

**The comparison constant `C`.**  `Ttc.CVSlowCanonicalUniformParameters.slowUniformC`
is the constant `4`, which lies in the frontier's window `(1, 7)` but is *not*
compatible with the R-aware tail floor: the floor's defining branch
`1 / (6 * exp (R² / (2 s0)))` only yields
`b * (exp (R²/(2σᵢ)) * 15) ≤ 5/2`, while `phaseMomentSlackSeven … C i / 2` at `C = 4`
is `(3/2) * ratio²`, which equals `3/2 < 5/2` at `ratio = 1`.  At `C = 2` the same
computation gives the required `(5/2) * ratio²`.  So this file fixes `C := fun _ ↦ 2`;
the frontier is happy with it (`1 < 2 < 7`), and the only alternative repair would be
to change the floor's constant `6` to `10`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Ttc.CVSlowCanonicalMomentBinders

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVCorrected Ttc.CVCorrectedRuntime
open Ttc.CVIndependentStreamDependence Ttc.CVScoreSeedPhaseKernel
open Ttc.CVGaussianScoreAwareParameters Ttc.CVGaussianFactorSevenAssembly
open Ttc.CVGaussianScoreAwareMeanBudget Ttc.CVScoreAwareHalfMeanBudget
open Ttc.CVGaussianBlockRetryParameters Ttc.CVContinuingRetryParameters
open Ttc.CVSlowFullBodySourceSchedule Ttc.CVSlowSourceReferenceCertificate
open Ttc.CVSlowSourceTargetTVAccuracy Ttc.CVRAwareGlobalRadius
open Ttc.CVSlowCanonicalShareBounds Ttc.CVMinimalScoreAwareWarmLogArithmetic
open Ttc.CVSlowCanonicalUniformParameters
open Ttc.CVSlowCanonicalPhaseMomentPackage
open Ttc.CVSlowCanonicalMomentInstantiation
open Ttc.CVSlowRadiusQReferencePhaseTV Ttc.CVSlowRadiusQCanonicalOperational
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVRelativeMeanClippingAssembly Ttc.CVIndependentStreamMoments
open Ttc.CVSlowCanonicalRobustCertificate
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-! ## Step 0 — arithmetic side facts -/

/-- The score-aware relative mean error is strictly below one: `blockShare ≤ 1/8`,
hence `eta ≤ sqrt (7/40) < 1`.  This is the `heta1` premise of
`operational_positiveStreamMean_upto_of_targetTV`. -/
theorem scoreAwareMeanEta_lt_one (m k : Nat) {eps : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) : scoreAwareMeanEta m k eps < 1 := by
  have hnu1 : correctedNu m eps ≤ 1 := correctedNu_le_one heps heps1
  have hnu0 : 0 < correctedNu m eps := correctedNu_pos heps
  have hk0 : (0 : Real) ≤ (k : Real) := Nat.cast_nonneg k
  have hshare : blockShare m k eps ≤ 1 / 8 := by
    unfold blockShare
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hshare0 : 0 < blockShare m k eps := blockShare_pos heps
  have hlt : (7 / 5 : Real) * blockShare m k eps < 1 := by linarith
  unfold scoreAwareMeanEta
  calc Real.sqrt ((7 / 5 : Real) * blockShare m k eps) < Real.sqrt 1 :=
        Real.sqrt_lt_sqrt (by positivity) hlt
    _ = 1 := Real.sqrt_one

/-! ## Step 1 — `hfactor0` and `hprefix` -/

/-- The frontier's `hfactor0` and `hprefix`, at
`factor := fun _ ↦ 1 + 8 / (correctedRuntimeSamples m eps : Real)`. -/
theorem slowCanonical_factorBundle (m : Nat) {eps : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (∀ _j : Nat, 0 ≤ (1 + 8 / (correctedRuntimeSamples m eps : Real))) ∧
    (∀ i, i ≤ m →
      prefixMomentRatio
        (fun _ ↦ 1 + 8 / (correctedRuntimeSamples m eps : Real)) i ≤
          1 + eps ^ 2 / 6250) :=
  corrected_factorEight_prefix_bundle heps heps1

/-! ## Step 2 — the squared-observable tail budget at the uniform floor -/

/-- The `htailBudget` premise of
`operational_slowCanonical_positiveScalar_factorSeven_upto`, at the uniform mean-tail
floor and at `C := fun _ ↦ 2`.  This is where `C ≤ 2` is forced: the floor only pays
`5/2`, and `phaseMomentSlackSeven … C i / 2 = ((7 - C i) / 2) * ratio ^ 2` with
`ratio ≥ 1`. -/
theorem slowCanonical_htailBudget (hn : 1 ≤ n) (m k : Nat) {eps R : Real}
    {K : Set (State n)} (hK : MeasurableSet K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤) :
    ∀ i : Fin m,
      slowUniformMeanTailFloor n m k eps R *
        (Real.exp (R ^ 2 /
          (2 * slowSourceSigmaSq n (slowSourceInitialVariance n) (i : Nat))) * 15) ≤
      phaseMomentSlackSeven m
        (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
        (fun _ ↦ 2) (i : Nat) / 2 := by
  intro i
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  let ratio := chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
      ((i : Nat) + 1) /
    chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (i : Nat)
  have hratio : (1 : Real) ≤ ratio := by
    dsimp only [ratio]
    exact one_le_chain_ratio_of_sigmaSq_le_succ hK hfin hball
      (slowSourceSigmaSq_pos hn hs0) (slowSourceSigmaSq_mono_succ hn hs0 (i : Nat))
  have hfit := slowCanonicalJointTailFloor_moment_le (m := m) (k := k) (eps := eps)
    (R := R) (s0 := slowSourceInitialVariance n)
    (sigma := slowSourceSigmaSq n (slowSourceInitialVariance n) (i : Nat))
    (ratio := ratio) hs0 (initial_le_slowSourceSigmaSq hn hs0 (i : Nat)) hratio
  simpa only [slowUniformMeanTailFloor, phaseMomentSlackSeven, ratio] using hfit

/-! ## Step 3 — the scalar factor-seven package on the estimator prefix -/

/-- The finite-prefix scalar factor-seven package for the slow canonical stream, at the
uniform radius selection and `C := fun _ ↦ 2`.  The single analytic premise left open is
`hexact`, the exact-law factor-two comparison of the phase score under `coolLaw`; it is
supplied by `Ttc.CVSlowGaussianPhaseMoment.slowSource_phaseScore_interior_sq_moment_le_two`
whenever `m` is the canonical slow phase count `slowSourcePhases n N s0 + 1`. -/
theorem slowCanonical_scalarFactorSeven
    (hn : 21 ≤ n) (m : Nat) {eps R : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    [IsProbabilityMeasure (slowInitialPair n)]
    (hop : IndependentStreamOperational (correctedRuntimeSamples m eps)
      (stateScheduleFromSeed Q) Q Prod.snd (slowInitialPair n)
      (slowClippedPositiveEmpiricalFamily m (correctedRuntimeSamples m eps) eps Q
        (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n)) K) m eps)
    (htau : ∀ i, i < m → hop.tau i =
      slowLocalPairReference (m + 1) n
        (slowUniformQ n m (correctedRuntimeSamples m eps) eps R)
        (slowSourceInitialVariance n) K i)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) (correctedRuntimeSamples m eps) (eps / 2)
        (fun t ↦ phaseMomentSlackSeven m
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (fun _ ↦ 2) t / 2)
        (phaseScoreTransportBoundSqSeven R
          (slowSourceSigmaSq n (slowSourceInitialVariance n)))) j)
    (hexact : ∀ j,
      ∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x ^ 2
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) ≤
      2 * (∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j)) ^ 2) :
    ∀ j, j ≤ m →
      MemLp (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) 2
        (inhomogeneousPathMeasure (stateScheduleFromSeed Q) (slowInitialPair n)) ∧
      ∫ omega, (positiveScalarPhaseFamilyChainLength (Seed := State n)
            m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega) ^ 2
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
        7 * (∫ omega, positiveScalarPhaseFamilyChainLength (Seed := State n)
            m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q)
            (slowInitialPair n))) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn1
  exact operational_slowCanonical_positiveScalar_factorSeven_upto
    (b := slowUniformMeanTailFloor n m (correctedRuntimeSamples m eps) eps R)
    (C := fun _ ↦ 2)
    hop hn1 heps heps1 hs0 (slowUniformMeanTailFloor_pos heps)
    (slowSourceSigmaSq_pos hn1 hs0) hKc hball hfin hKR
    (fun _ ↦ by norm_num) (fun _ ↦ by norm_num) hmixError
    (slowCanonical_htargetTV hop hn1 hK hKc hball hfin htau) rfl
    hexact
    (slowCanonical_htailBudget hn1 m (correctedRuntimeSamples m eps) hK hball hfin)

/-! ## Step 4 — `hWEpos` -/

/-- The frontier's `hWEpos`, on the estimator prefix.  Raw stream means are strictly
positive because the first-moment transport budget is met with `eta < 1`. -/
theorem slowCanonical_hWEpos
    (hn : 21 ≤ n) (m : Nat) {eps R : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    [IsProbabilityMeasure (slowInitialPair n)]
    (hop : IndependentStreamOperational (correctedRuntimeSamples m eps)
      (stateScheduleFromSeed Q) Q Prod.snd (slowInitialPair n)
      (slowClippedPositiveEmpiricalFamily m (correctedRuntimeSamples m eps) eps Q
        (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n)) K) m eps)
    (htau : ∀ i, i < m → hop.tau i =
      slowLocalPairReference (m + 1) n
        (slowUniformQ n m (correctedRuntimeSamples m eps) eps R)
        (slowSourceInitialVariance n) K i)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) (correctedRuntimeSamples m eps) (eps / 2)
        (fun t ↦ phaseMomentSlackSeven m
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (fun _ ↦ 2) t / 2)
        (phaseScoreTransportBoundSqSeven R
          (slowSourceSigmaSq n (slowSourceInitialVariance n)))) j) :
    ∀ j, j ≤ m → 0 < ∫ omega, streamAverage (k := correctedRuntimeSamples m eps)
      (positiveScalarPhaseFamilyChainLength (Seed := State n) m
        (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
      ∂(independentPathLaw (correctedRuntimeSamples m eps)
        (stateScheduleFromSeed Q) (slowInitialPair n)) := by
  have hn1 : 1 ≤ n := by omega
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn1
  have hmeanMix : ∀ i : Fin m,
      (hop.mixError (i : Nat)).toReal * Real.exp (R ^ 2 /
          (2 * slowSourceSigmaSq n (slowSourceInitialVariance n) (i : Nat))) ≤
        (scoreAwareMeanEta m (correctedRuntimeSamples m eps) eps *
          (chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
              ((i : Nat) + 1) /
            chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
              (i : Nat))) / 2 := by
    intro i
    rw [hmixError (i : Nat), activeReferenceMixError,
      if_pos (by omega : (i : Nat) + 1 < m + 1)]
    simpa only [mul_comm] using scoreAwareMixError_succ_halfSlack_mean_le_half
      (m := m) (k := correctedRuntimeSamples m eps) (chainLength := m)
      (eps := eps) (R := R)
      (sigmaSq := slowSourceSigmaSq n (slowSourceInitialVariance n))
      (K := K) (C := fun _ ↦ 2) (i := (i : Nat))
      heps heps1 (slowSourceSigmaSq_pos hn1 hs0) hball hfin
      (fun _ ↦ by norm_num) (fun _ ↦ by norm_num)
  have hmeanError : ∀ i : Fin m,
      (hop.mixError (i : Nat) + slowTargetError n
            (rAwareGlobalRadiusQ n R (slowSourceInitialVariance n)
              (slowUniformMeanTailFloor n m (correctedRuntimeSamples m eps) eps R))
            m (i : Nat)).toReal *
          Real.exp (R ^ 2 /
            (2 * slowSourceSigmaSq n (slowSourceInitialVariance n) (i : Nat))) ≤
        scoreAwareMeanEta m (correctedRuntimeSamples m eps) eps *
          (chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
              ((i : Nat) + 1) /
            chain m (slowSourceSigmaSq n (slowSourceInitialVariance n))
              K (i : Nat)) := by
    intro i
    exact mix_add_slowTargetError_rAware_scaled_le hn1 hs0
      (slowUniformMeanTailFloor_pos heps) i.isLt (hop.mixError_ne_top i)
      (hmeanMix i)
      (slowUniformMeanTailFloor_le_meanBudget hn1 heps hK hball hfin (i : Nat))
  exact operational_positiveStreamMean_upto_of_targetTV
    (correctedRuntimeSamples_pos m eps) hop
    (slowSourceSigmaSq_pos hn1 hs0) hK hKc hball hfin hKR
    (scoreAwareMeanEta_nonneg m (correctedRuntimeSamples m eps) eps)
    (scoreAwareMeanEta_lt_one m (correctedRuntimeSamples m eps) heps heps1)
    (slowCanonical_htargetTV hop hn1 hK hKc hball hfin htau)
    (slowTargetError_ne_top n _ m) hmeanError

/-! ## Step 5 — the bundle -/

/-- **The seven estimator-moment binders of the slow canonical frontier theorem**, at
`k := correctedRuntimeSamples m eps`,
`factor := fun _ ↦ 1 + 8 / (correctedRuntimeSamples m eps : Real)`,
`C := fun _ ↦ 2` and `q := slowUniformQ n m (correctedRuntimeSamples m eps) eps R`.

Conjuncts 1–4 and 6 are the frontier's `hWint`, `hW2int`, `hWEpos`, `hrawSecond`,
`hphaseMoment` **restricted to the estimator prefix `j ≤ m`** (see the module
docstring: the untotalized family is the indicator of `interior K` beyond `m`, so the
unguarded `∀ j` forms are not consequences of the analytic package).  Conjuncts 5 and 7
are the frontier's `hfactor0` and `hprefix` verbatim. -/
theorem slowCanonical_momentBinders
    (hn : 21 ≤ n) (m : Nat) {eps R : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    [IsProbabilityMeasure (slowInitialPair n)]
    (hop : IndependentStreamOperational (correctedRuntimeSamples m eps)
      (stateScheduleFromSeed Q) Q Prod.snd (slowInitialPair n)
      (slowClippedPositiveEmpiricalFamily m (correctedRuntimeSamples m eps) eps Q
        (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n)) K) m eps)
    (htau : ∀ i, i < m → hop.tau i =
      slowLocalPairReference (m + 1) n
        (slowUniformQ n m (correctedRuntimeSamples m eps) eps R)
        (slowSourceInitialVariance n) K i)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) (correctedRuntimeSamples m eps) (eps / 2)
        (fun t ↦ phaseMomentSlackSeven m
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (fun _ ↦ 2) t / 2)
        (phaseScoreTransportBoundSqSeven R
          (slowSourceSigmaSq n (slowSourceInitialVariance n)))) j)
    (hexact : ∀ j,
      ∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x ^ 2
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) ≤
      2 * (∫ x, phaseScore m (slowSourceSigmaSq n (slowSourceInitialVariance n))
          (interior K) j x
        ∂(coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j)) ^ 2) :
    (∀ j, j ≤ m → Integrable
      (fun omega ↦ streamAverage (k := correctedRuntimeSamples m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega)
      (independentPathLaw (correctedRuntimeSamples m eps)
        (stateScheduleFromSeed Q) (slowInitialPair n))) ∧
    (∀ j, j ≤ m → Integrable
      (fun omega ↦ (streamAverage (k := correctedRuntimeSamples m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2)
      (independentPathLaw (correctedRuntimeSamples m eps)
        (stateScheduleFromSeed Q) (slowInitialPair n))) ∧
    (∀ j, j ≤ m → 0 < ∫ omega, streamAverage (k := correctedRuntimeSamples m eps)
      (positiveScalarPhaseFamilyChainLength (Seed := State n)
        m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
      ∂(independentPathLaw (correctedRuntimeSamples m eps)
        (stateScheduleFromSeed Q) (slowInitialPair n))) ∧
    (∀ j, j ≤ m → ∫ omega, (streamAverage (k := correctedRuntimeSamples m eps)
      (positiveScalarPhaseFamilyChainLength (Seed := State n)
        m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2
        ∂(independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
      2 * (∫ omega, streamAverage (k := correctedRuntimeSamples m eps)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
        ∂(independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2) ∧
    (∀ _j : Nat, 0 ≤ (fun _ ↦ 1 + 8 / (correctedRuntimeSamples m eps : Real)) _j) ∧
    (∀ j, j ≤ m → ∫ omega,
        (slowClippedPositiveEmpiricalFamily m (correctedRuntimeSamples m eps) eps Q
          (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n))
          K j omega) ^ 2
        ∂(independentPathLaw (correctedRuntimeSamples m eps)
          (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
      (fun _ ↦ 1 + 8 / (correctedRuntimeSamples m eps : Real)) j *
        (∫ omega, slowClippedPositiveEmpiricalFamily m
            (correctedRuntimeSamples m eps) eps Q (slowInitialPair n)
            (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega
          ∂(independentPathLaw (correctedRuntimeSamples m eps)
            (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2) ∧
    (∀ i, i ≤ m →
      prefixMomentRatio
        (fun _ ↦ 1 + 8 / (correctedRuntimeSamples m eps : Real)) i ≤
          1 + eps ^ 2 / 6250) := by
  have hscalar := slowCanonical_scalarFactorSeven hn m heps heps1 hK hKc hball hfin
    hKR hop htau hmixError hexact
  have hmeanPos := slowCanonical_hWEpos hn m heps heps1 hK hKc hball hfin hKR
    hop htau hmixError
  have hstream := operational_slowCanonical_streamMoment_bundle_upto
    (m := m) (eps := eps) heps heps1 hK
    (Q := Q) (mu0 := slowInitialPair n) hscalar
  have hclip := operational_slowCanonical_clippedMoment_bundle_upto
    (m := m) (eps := eps) heps heps1 hK (Q := Q) (mu0 := slowInitialPair n)
    (V := slowClippedPositiveEmpiricalFamily m (correctedRuntimeSamples m eps) eps Q
      (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n)) K)
    hscalar hmeanPos (fun _ _ _ ↦ rfl)
  refine ⟨fun j hj ↦ (hstream j hj).1, fun j hj ↦ (hstream j hj).2.1, hmeanPos,
    fun j hj ↦ (hstream j hj).2.2, (slowCanonical_factorBundle m heps heps1).1,
    fun j hj ↦ (hclip j hj).2, (slowCanonical_factorBundle m heps heps1).2⟩

/-! ## Step 6 — discharging `hexact` at the canonical slow phase count -/

/-- The one analytic binder of `slowCanonical_momentBinders`, discharged whenever the
phase count is the canonical `slowSourcePhases n N s0 + 1` and the body fits inside the
declared terminal variance budget `R ^ 2 ≤ N`. -/
theorem slowCanonical_hexact_at_slowPhases
    (hn : 21 ≤ n) {N R : Real} (hN : 0 < N)
    (hsN : slowSourceInitialVariance n ≤ N) (hR2 : R ^ 2 ≤ N)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R) :
    ∀ j,
      ∫ x, phaseScore (slowSourcePhases n N (slowSourceInitialVariance n) + 1)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) (interior K) j x ^ 2
        ∂(coolLaw (slowSourcePhases n N (slowSourceInitialVariance n) + 1)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) ≤
      2 * (∫ x, phaseScore (slowSourcePhases n N (slowSourceInitialVariance n) + 1)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) (interior K) j x
        ∂(coolLaw (slowSourcePhases n N (slowSourceInitialVariance n) + 1)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j)) ^ 2 := by
  intro j
  exact Ttc.CVSlowGaussianPhaseMoment.slowSource_phaseScore_interior_sq_moment_le_two
    (by omega : 3 ≤ n) hN (slowSourceInitialVariance_pos (by omega : 1 ≤ n)) hsN hR2
    hK hKc hball hfin hKR j

#print axioms scoreAwareMeanEta_lt_one
#print axioms slowCanonical_factorBundle
#print axioms slowCanonical_htailBudget
#print axioms slowCanonical_scalarFactorSeven
#print axioms slowCanonical_hWEpos
#print axioms slowCanonical_momentBinders
#print axioms slowCanonical_hexact_at_slowPhases

end Ttc.CVSlowCanonicalMomentBinders
