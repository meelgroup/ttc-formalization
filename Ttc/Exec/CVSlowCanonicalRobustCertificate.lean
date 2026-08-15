import Ttc.Exec.CVSlowCanonicalSourceReferenceCertificate
import Ttc.Exec.CVSlowSourceTargetTVAccuracy
import Ttc.Exec.CVSlowGlobalRadiusTailBudget
import Ttc.Exec.CVConcreteAugmentedRetryCutoffBudget
import Ttc.Exec.CVGaussianHybridWeightedCertificate
import Ttc.Exec.CVRAwareGlobalRadius
import Ttc.Exec.CVScoreAwareHalfMeanBudget

/-! Target-TV robust accuracy composed with the canonical slow retained certificate. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Ttc.CVSlowCanonicalRobustCertificate

open MeasureTheory ProbabilityTheory Metric Set Finset
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler Ttc.CVIndependentStreamDependence
open Ttc.CVScoreSeedPhaseKernel Ttc.CVSlowFullBodySourceSchedule
open Ttc.CVSlowRadiusQCanonicalOperational Ttc.CVSlowRadiusQRecursiveOperational
open Ttc.CVSlowSourceReferenceCertificate Ttc.CVSlowCanonicalRetainedReference
open Ttc.CVSlowCanonicalSourceReferenceCertificate
open Ttc.CVSlowSourceTargetTVAccuracy Ttc.CVSourceWeightedMeanRepair
open Ttc.CVHeterogeneousHistoryReference Ttc.CVHeterogeneousRetainedPathLaw
open Ttc.CVSourceReferenceTVCapstone Ttc.CVSlowRadiusQReferencePhaseTV
open Ttc.CVCorrected Ttc.CVGaussianScoreAwareMeanBudget
open Ttc.CVGaussianScoreAwareParameters Ttc.CVIndependentStreamMoments
open Ttc.CVGaussianFactorSevenAssembly
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVWeightedIndependentStreamAccuracy Ttc.CVRelativeMeanClippingAssembly
open Ttc.CVSlowGlobalRadiusTailBudget
open Ttc.CVConcreteAugmentedRetryCutoffBudget
open Ttc.CVGaussianHybridWeightedCertificate
open Ttc.CVCorrectedClippingArithmetic
open Ttc.CVRAwareGlobalRadius
open Ttc.CVScoreAwareHalfMeanBudget
open scoped ENNReal Classical BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- Literal clipped Gaussian statistic at an arbitrary stream count. -/
noncomputable def slowClippedPositiveEmpiricalFamily
    (m k : Nat) (eps : Real)
    (Q : Nat → Kernel (State n) (ScoreSeed n)) [∀ i, IsMarkovKernel (Q i)]
    (mu0 : Measure (ScoreSeed n)) (sigmaSq : Nat → Real) (K : Set (State n)) :
    Nat → (Fin k → Nat → ScoreSeed n) → Real :=
  fun j omega ↦
    let Wbar := streamAverage (k := k)
      (positiveScalarPhaseFamilyChainLength (Seed := State n) m sigmaSq K j)
    min (Wbar omega) (correctedAlpha m eps *
      ∫ z, Wbar z ∂independentPathLaw k (stateScheduleFromSeed Q) mu0)

/-- Explicit uniform envelope for the recursive-deadline retained cost.  This is the
named scalar runtime seam: the large actual warmness occurs only inside `steps`; the
retained expected-cost multiplier remains the constant `2e`. -/
theorem aggregate_slowCanonicalRetainedCost_le_uniform
    {n m k : Nat} {q eps : Real} {K : Set (State n)}
    {slack boundSq : Nat → Real} {T L : Nat}
    (hsteps : ∀ i, i < m → slowCanonicalSteps slowReferenceWarm n q
      (slowSourceInitialVariance n) K
      (scoreAwareRetries (m + 1) k eps slack boundSq)
      (scoreAwareEta (m + 1) k eps slack boundSq)
      (scoreAwareZeta (m + 1) k eps slack boundSq) i 0 ≤ T)
    (hretries : ∀ i, i < m →
      scoreAwareRetries (m + 1) k eps slack boundSq i ≤ L) :
    (k : ENNReal) * (∑ i ∈ range m,
      slowCanonicalRetainedCost n m k q eps K slack boundSq i) ≤
      (k : ENNReal) * (m : ENNReal) * ENNReal.ofReal
        (10 * (L : Real) * (T : Real) * (2 * Real.exp 1)) := by
  have hphase : ∀ i, i < m →
      slowCanonicalRetainedCost n m k q eps K slack boundSq i ≤
        ENNReal.ofReal (10 * (L : Real) * (T : Real) * (2 * Real.exp 1)) := by
    intro i hi
    unfold slowCanonicalRetainedCost slowCanonicalPhaseCostBound
    rw [if_pos hi]
    apply ENNReal.ofReal_le_ofReal
    have hmean := retryReferenceMeanEnvelope_le_uniform
      (M := 2 * Real.exp 1)
      (steps := slowCanonicalSteps slowReferenceWarm n q (slowSourceInitialVariance n) K
        (scoreAwareRetries (m + 1) k eps slack boundSq)
        (scoreAwareEta (m + 1) k eps slack boundSq)
        (scoreAwareZeta (m + 1) k eps slack boundSq) i)
      (L := scoreAwareRetries (m + 1) k eps slack boundSq i) (T := T)
      (by positivity) (fun _ _ ↦ by
        simpa only [slowCanonicalSteps] using hsteps i hi)
    calc
      retryReferenceMeanEnvelope (2 * Real.exp 1)
          (slowCanonicalSteps slowReferenceWarm n q (slowSourceInitialVariance n) K
            (scoreAwareRetries (m + 1) k eps slack boundSq)
            (scoreAwareEta (m + 1) k eps slack boundSq)
            (scoreAwareZeta (m + 1) k eps slack boundSq) i)
          (scoreAwareRetries (m + 1) k eps slack boundSq i) ≤
        10 * (scoreAwareRetries (m + 1) k eps slack boundSq i : Real) *
          (T : Real) * (2 * Real.exp 1) := hmean
      _ ≤ 10 * (L : Real) * (T : Real) * (2 * Real.exp 1) := by
        have hL : (scoreAwareRetries (m + 1) k eps slack boundSq i : Real) ≤ L := by
          exact_mod_cast hretries i hi
        gcongr
  calc
    (k : ENNReal) * (∑ i ∈ range m,
        slowCanonicalRetainedCost n m k q eps K slack boundSq i) ≤
      (k : ENNReal) * (∑ _i ∈ range m,
        ENNReal.ofReal (10 * (L : Real) * (T : Real) * (2 * Real.exp 1))) := by
          gcongr with i hi
          exact hphase i (mem_range.mp hi)
    _ = (k : ENNReal) * (m : ENNReal) * ENNReal.ofReal
        (10 * (L : Real) * (T : Real) * (2 * Real.exp 1)) := by
      simp [nsmul_eq_mul, mul_assoc]

/-- The retained local mixing error is covered by the stronger global-radius full-pair
budget, which also charges the explicit local-to-full target tail. -/
theorem aggregate_slowCanonicalRetainedError_le_globalRadius
    {n m k : Nat} (hn : 1 ≤ n) {eps : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    {slack boundSq : Nat → Real}
    (hslack : ∀ i, 0 < slack i) (hbound : ∀ i, 0 < boundSq i) :
    (k : ENNReal) * (∑ i ∈ range m,
      slowCanonicalRetainedError m k eps slack boundSq i) ≤
      ENNReal.ofReal (1 / 40 : Real) := by
  let q := slowGlobalRadiusQ n (m + 1) k eps
  let fullError := fun i ↦ scoreAwareMixError (m + 1) k eps slack boundSq i +
    slowTargetError n q (m + 1) i
  have hlocal : (∑ i ∈ range m,
      slowCanonicalRetainedError m k eps slack boundSq i) ≤
      ∑ i ∈ range m, fullError i := by
    apply sum_le_sum
    intro i hi
    have him : i < m := mem_range.mp hi
    unfold slowCanonicalRetainedError fullError
    rw [if_pos him]
    exact le_add_right (le_refl _)
  have hsubset : (∑ i ∈ range m, fullError i) ≤
      ∑ i ∈ range (m + 1), fullError i := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (Nat.le_succ m)) (fun _ _ _ ↦ bot_le)
  calc
    (k : ENNReal) * (∑ i ∈ range m,
        slowCanonicalRetainedError m k eps slack boundSq i) ≤
      (k : ENNReal) * (∑ i ∈ range (m + 1), fullError i) := by
        gcongr
        exact hlocal.trans hsubset
    _ ≤ ENNReal.ofReal (1 / 40 : Real) := by
      have heq : (∑ i ∈ range (m + 1), fullError i) =
          ∑ i ∈ range (m + 1),
            (scoreAwareMixError (m + 1) k eps slack boundSq i +
              ENNReal.ofReal
                ((q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n)) := by
        apply sum_congr rfl
        intro i hi
        simp only [fullError, slowTargetError, if_pos (mem_range.mp hi)]
      rw [heq]
      exact slowGlobalRadiusQ_fullPair_sum_le_one_fortieth
        (n := n) (m := m + 1) (k := k) hn heps heps1 hslack hbound

/-- Final composition seam for the honest slow sampler.  In contrast with the older
certificate constructor, there is no opaque `haccuracy`: accuracy is derived from the
local-target TV theorem and the weighted clipping/moment hypotheses. -/
theorem exists_sourceReferenceTVOneRunCertificate_slowCanonical_of_weightedData
    (hn : 21 ≤ n) (m k : Nat) (hm : 0 < m) (hk : 1 ≤ k)
    {q eps beta requested R meanTailFloor : Real} (hq4 : 4 ≤ q)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hbeta : 0 ≤ beta)
    (haccuracyBudget : eps + beta + eps * beta ≤ requested)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    (hmeanTailFloor : 0 < meanTailFloor)
    (hqRAware : q = rAwareGlobalRadiusQ n R (slowSourceInitialVariance n) meanTailFloor)
    (hrad : ∀ i, 1 ≤ q * Real.sqrt
      (slowSourceSigmaSq n (slowSourceInitialVariance n) i) * Real.sqrt n)
    (slack boundSq : Nat → Real) (hslack : ∀ i, 0 < slack i)
    (hbound : ∀ i, 0 < boundSq i) (scoreScale : Real)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    (hQ : Q = slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1) k
      (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (lt_of_lt_of_le (by norm_num) hq4)
      (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
      slowReferenceWarm slack boundSq)
    [IsProbabilityMeasure (slowInitialPair n)]
    (V : Nat → (Fin k → Nat → ScoreSeed n) → Real)
    (hVliteral : V = slowClippedPositiveEmpiricalFamily m k eps Q
      (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n)) K)
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      (slowInitialPair n) V m eps)
    (htau : ∀ i, i < m → hop.tau i =
      slowLocalPairReference (m + 1) n q (slowSourceInitialVariance n) K i)
    {C factor : Nat → Real}
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) k (eps / 2) slack boundSq) j)
    (hslackDef : slack = fun j ↦ phaseMomentSlackSeven m
      (slowSourceSigmaSq n (slowSourceInitialVariance n)) K C j / 2)
    (hboundDef : boundSq = phaseScoreTransportBoundSqSeven R
      (slowSourceSigmaSq n (slowSourceInitialVariance n)))
    (hC7 : ∀ i, C i < 7)
    (hmeanTailBudget : ∀ i : Fin m, meanTailFloor ≤
      (scoreAwareMeanEta m k eps *
        (chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
            ((i : Nat) + 1) /
          chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (i : Nat))) / 2)
    (hC1 : ∀ i, 1 < C i)
    (hWint : ∀ j, Integrable
      (fun omega ↦ streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega)
      (independentPathLaw k (stateScheduleFromSeed Q) (slowInitialPair n)))
    (hW2int : ∀ j, Integrable
      (fun omega ↦ (streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2)
      (independentPathLaw k (stateScheduleFromSeed Q) (slowInitialPair n)))
    (hWEpos : ∀ j, 0 < ∫ omega, streamAverage (k := k)
      (positiveScalarPhaseFamilyChainLength (Seed := State n)
        m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
      ∂(independentPathLaw k (stateScheduleFromSeed Q) (slowInitialPair n)))
    (hrawSecond : ∀ j, ∫ omega, (streamAverage (k := k)
      (positiveScalarPhaseFamilyChainLength (Seed := State n)
        m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega) ^ 2
        ∂(independentPathLaw k (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
      2 * (∫ omega, streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega
        ∂(independentPathLaw k (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2)
    (hfactor0 : ∀ j, 0 ≤ factor j)
    (hphaseMoment : ∀ j, ∫ omega, (V j omega) ^ 2
        ∂(independentPathLaw k (stateScheduleFromSeed Q) (slowInitialPair n)) ≤
      factor j * (∫ omega, V j omega
        ∂(independentPathLaw k (stateScheduleFromSeed Q) (slowInitialPair n))) ^ 2)
    (hprefix : ∀ i, i ≤ m → prefixMomentRatio factor i ≤ 1 + eps ^ 2 / 6250)
    (initialNormalizer volumeTarget : Real)
    (hinit : 0 ≤ initialNormalizer) (hvolume : 0 ≤ volumeTarget)
    (hinitChain : initialNormalizer =
      chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K 0)
    (htargetChain : volumeTarget =
      chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K m)
    (hbetaDef : (m : Real) / (2 * correctedAlpha m eps) +
      scoreAwareMeanGamma m k eps +
      ((m : Real) / (2 * correctedAlpha m eps)) * scoreAwareMeanGamma m k eps ≤ beta)
    {runtimeConstant : Real} (T L : Nat)
    (hsteps : ∀ i, i < m → slowCanonicalSteps slowReferenceWarm n q
      (slowSourceInitialVariance n) K
      (scoreAwareRetries (m + 1) k (eps / 2) slack boundSq)
      (scoreAwareEta (m + 1) k (eps / 2) slack boundSq)
      (scoreAwareZeta (m + 1) k (eps / 2) slack boundSq) i 0 ≤ T)
    (hretries : ∀ i, i < m →
      scoreAwareRetries (m + 1) k (eps / 2) slack boundSq i ≤ L)
    (hscalar : (k : ENNReal) * (m : ENNReal) * ENNReal.ofReal
        (10 * (L : Real) * (T : Real) * (2 * Real.exp 1)) ≤
      Ttc.CVSourcePolynomialCutoffCapstone.sourceOneRunQueryBudget
        runtimeConstant n R requested) :
    ∃ reference : Measure (Fin k → HeterogeneousHistoryState (State n) (State n)),
      SourceReferenceTVOneRunCertificate
        (@independentHeterogeneousRetainedPathLaw _ _ _ _ k
          (slowCanonicalCostedActiveSchedule (by omega : 1 ≤ n) (m + 1) k
            (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
            (lt_of_lt_of_le (by norm_num) hq4)
            (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
            slowReferenceWarm slack boundSq)
          (by
            letI : ∀ j, IsProbabilityMeasure
                (slowStationaryTail n q (slowSourceInitialVariance n) K j) := fun j ↦
              isProbabilityMeasure_slowStationaryTail (by omega : 1 ≤ n)
                (lt_of_lt_of_le (by norm_num) hq4)
                (by unfold slowSourceInitialVariance; positivity) hK hKc hball
                (fun r ↦ one_le_slow_radius (by omega : 1 ≤ n) hq4 (by rfl) r) j
            intro i; infer_instance)
          (slowInitialPair n) m)
        reference (fun omega ↦ ∑ j, (omega j).1.1)
        (fun omega ↦ gaussianScorePrefixReadout m m k
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K initialNormalizer
          (independentStoredScorePrefixCurrent m omega))
        runtimeConstant n R requested
        ((1 - requested) * volumeTarget) ((1 + requested) * volumeTarget) := by
  subst Q
  subst V
  let Qc := slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1) k
      (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (lt_of_lt_of_le (by norm_num) hq4)
      (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
      slowReferenceWarm slack boundSq
  let pathLaw := independentPathLaw k (stateScheduleFromSeed Qc) (slowInitialPair n)
  let Wbar := fun j ↦ streamAverage (k := k)
    (positiveScalarPhaseFamilyChainLength (Seed := State n)
      m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j)
  have halpha : 2 ≤ correctedAlpha m eps := by
    have ha := correctedAlpha_ge_hundred_thousand (m := m) heps heps1
    linarith
  have hW0 : ∀ j omega, 0 ≤ Wbar j omega := by
    intro j omega
    unfold Wbar streamAverage Ttc.CVEst.avgOf streamScore
    apply div_nonneg
    · exact Finset.sum_nonneg fun l _ ↦
        positiveScalarPhaseFamilyChainLength_nonneg j (omega l)
    · positivity
  have hstats : ∀ j,
      Measurable (slowClippedPositiveEmpiricalFamily m k eps Qc (slowInitialPair n)
        (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) ∧
      (∀ omega, 0 ≤ slowClippedPositiveEmpiricalFamily m k eps Qc (slowInitialPair n)
        (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega) ∧
      0 < ∫ omega, slowClippedPositiveEmpiricalFamily m k eps Qc (slowInitialPair n)
        (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega ∂pathLaw ∧
      (∀ omega, slowClippedPositiveEmpiricalFamily m k eps Qc (slowInitialPair n)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega ≤
        2 * correctedAlpha m eps * ∫ z,
          slowClippedPositiveEmpiricalFamily m k eps Qc (slowInitialPair n)
            (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j z ∂pathLaw) ∧
      (∀ omega, (slowClippedPositiveEmpiricalFamily m k eps Qc (slowInitialPair n)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega) ^ 2 ≤
        2 * correctedAlpha m eps ^ 2 * ∫ z,
          (slowClippedPositiveEmpiricalFamily m k eps Qc (slowInitialPair n)
            (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j z) ^ 2 ∂pathLaw) := by
    intro j
    apply clippedStatistic_caps_of_rawSecond halpha
      (hW0 j)
      (measurable_streamAverage
        (measurable_positiveScalarPhaseFamilyChainLength hK j))
      (by simpa only [Wbar, pathLaw] using hWint j)
      (by simpa only [Wbar, pathLaw] using hW2int j)
      (by simpa only [Wbar, pathLaw] using hWEpos j)
      (by simpa only [Wbar, pathLaw] using hrawSecond j)
    intro omega
    simp only [slowClippedPositiveEmpiricalFamily, Wbar, pathLaw]
  have hV2 : ∀ j, Integrable
      (fun omega ↦ (slowClippedPositiveEmpiricalFamily m k eps Qc (slowInitialPair n)
        (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega) ^ 2) pathLaw := by
    intro j
    refine Integrable.mono' (by simpa only [Wbar, pathLaw] using hW2int j)
      ((hstats j).1.pow_const 2).aestronglyMeasurable ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    apply (sq_le_sq₀ ((hstats j).2.1 omega) (hW0 j omega)).2
    exact min_le_left _ _
  have htargetTV := tvLe_map_fst_tau_fullCoolLaw_slowTargetError hop
    (by omega : 1 ≤ n) (lt_of_lt_of_le (by norm_num) hq4)
    (by unfold slowSourceInitialVariance; positivity) hK hKc hball hfin
    (fun i hi ↦ hrad i) (fun i hi ↦
      (htau i hi).trans (slowLocalPairReference_succ_length_eq m n q
        (slowSourceInitialVariance n) K hi))
  have hmeanMix : ∀ i : Fin m,
      (hop.mixError (i : Nat)).toReal * Real.exp (R ^ 2 /
          (2 * slowSourceSigmaSq n (slowSourceInitialVariance n) (i : Nat))) ≤
        (scoreAwareMeanEta m k eps *
          (chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
              ((i : Nat) + 1) /
            chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (i : Nat))) / 2 := by
    intro i
    rw [hmixError (i : Nat), activeReferenceMixError,
      if_pos (by omega : (i : Nat) + 1 < m + 1), hslackDef, hboundDef]
    simpa only [mul_comm] using scoreAwareMixError_succ_halfSlack_mean_le_half
      (m := m) (k := k) (chainLength := m) (eps := eps) (R := R)
      (sigmaSq := slowSourceSigmaSq n (slowSourceInitialVariance n))
      (K := K) (C := C) (i := i)
      heps heps1
      (slowSourceSigmaSq_pos (by omega : 1 ≤ n)
        (by unfold slowSourceInitialVariance; positivity))
      hball hfin (fun j ↦ by linarith [hC1 j]) hC7
  have hmeanError : ∀ i : Fin m,
      (hop.mixError (i : Nat) + slowTargetError n q m (i : Nat)).toReal *
          Real.exp (R ^ 2 /
            (2 * slowSourceSigmaSq n (slowSourceInitialVariance n) (i : Nat))) ≤
        scoreAwareMeanEta m k eps *
          (chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
              ((i : Nat) + 1) /
            chain m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K (i : Nat)) := by
    have hs0 : 0 < slowSourceInitialVariance n := by
      unfold slowSourceInitialVariance
      positivity
    intro i
    have hc := mix_add_slowTargetError_rAware_scaled_le (by omega : 1 ≤ n)
      hs0 hmeanTailFloor i.isLt
      (hop.mixError_ne_top i) (hmeanMix i) (hmeanTailBudget i)
    rw [← hqRAware] at hc
    exact hc
  have haccuracy := relative_weighted_accuracy_four_fifths_sourceSharp_of_targetTV
    (slowClippedPositiveEmpiricalFamily m k eps Qc (slowInitialPair n)
      (slowSourceSigmaSq n (slowSourceInitialVariance n)) K)
    (fun j omega ↦ streamAverage (k := k)
      (positiveScalarPhaseFamilyChainLength (Seed := State n)
        m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) omega)
    hop heps heps1 hm (by omega : 0 < k) hbeta haccuracyBudget
    (slowSourceSigmaSq_pos (by omega : 1 ≤ n)
      (by unfold slowSourceInitialVariance; positivity))
    hK hKc hball hfin hKR htargetTV (slowTargetError_ne_top n q m)
    hmeanError hC1 hWint hW2int hWEpos hrawSecond
    (by intro j omega; rfl)
    (fun j ↦ (hstats j).1) (fun j ↦ (hstats j).2.1)
    (fun j ↦ (hstats j).2.2.1) (fun j ↦ (hstats j).2.2.2.1)
    hV2 (fun j ↦ (hstats j).2.2.2.2)
    hfactor0 hphaseMoment hprefix
    (by
      intro j
      exact measurable_streamAverage
        (measurable_positiveScalarPhaseFamilyChainLength hK j))
    (Eexact := Set.univ) MeasurableSet.univ (by simp)
    (by intro omega _; rfl)
    initialNormalizer volumeTarget hinit hvolume hinitChain htargetChain hbetaDef
  have haccuracy' : 4 / 5 ≤
      (independentPathLaw k (stateScheduleFromSeed
        (slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1) k
          (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
          (lt_of_lt_of_le (by norm_num) hq4)
          (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
          slowReferenceWarm slack boundSq)) (slowInitialPair n)).real
        {omega | gaussianScorePrefixReadout m m k
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K initialNormalizer
          (independentPathScorePrefixCurrent m omega) ∈
          Icc ((1 - requested) * volumeTarget) ((1 + requested) * volumeTarget)} := by
    simpa only [gaussianScorePrefixReadout_independentPathScorePrefixCurrent,
      Ttc.relErr] using haccuracy
  have herror : (k : ENNReal) * (∑ i ∈ range m,
      slowCanonicalRetainedError m k (eps / 2) slack boundSq i) ≤
      ENNReal.ofReal (1 / 40 : Real) :=
    aggregate_slowCanonicalRetainedError_le_globalRadius
      (by omega : 1 ≤ n) (by positivity) (by linarith) hslack hbound
  have hbudget : (k : ENNReal) * (∑ i ∈ range m,
      slowCanonicalRetainedCost n m k q (eps / 2) K slack boundSq i) ≤
      Ttc.CVSourcePolynomialCutoffCapstone.sourceOneRunQueryBudget
        runtimeConstant n R requested :=
    (aggregate_slowCanonicalRetainedCost_le_uniform hsteps hretries).trans hscalar
  exact exists_sourceReferenceTVOneRunCertificate_slowCanonical hn m k hk hq4
    (by positivity) (by linarith)
    hK hKc hball hfin slack boundSq hslack hbound scoreScale
    (gaussianScorePrefixReadout m m k
      (slowSourceSigmaSq n (slowSourceInitialVariance n)) K initialNormalizer)
    (measurable_gaussianScorePrefixReadout initialNormalizer)
    herror hbudget haccuracy'

#print axioms exists_sourceReferenceTVOneRunCertificate_slowCanonical_of_weightedData
#print axioms aggregate_slowCanonicalRetainedCost_le_uniform
#print axioms aggregate_slowCanonicalRetainedError_le_globalRadius

end Ttc.CVSlowCanonicalRobustCertificate
