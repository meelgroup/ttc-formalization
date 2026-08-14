import Ttc.Exec.CVGaussianAdaptiveBlockOperational
import Ttc.Exec.CVGaussianScoreAwareParameters

/-! Score-aware version of the accelerated Gaussian block operation. -/

namespace Ttc.CVGaussianScoreAwareOperational

open MeasureTheory ProbabilityTheory Metric Set Pointwise
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open Ttc.CVCorrected Ttc.CVSequentialPhaseSampler
open Ttc.FiniteContinuingRetryGaussianAugmentedPhase
open Ttc.CVGaussianAugmentedSelectiveTV Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.CVSeedProjectedDependence Ttc.CVScoreSeedPhaseKernel
open Ttc.CVGaussianWarmFallbackOperational Ttc.CVGaussianWarmFallbackAnalytic
open Ttc.CVGaussianWarmFallbackPhaseKernel Ttc.CVGaussianWarmFallbackZeroSafe
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVGaussianAdaptiveAcceptedWarm Ttc.CVGaussianScoreAwareParameters
open Ttc.CVCombinedContinuingAccept Ttc.CVIdealCombinedAccepted
open scoped ENNReal Classical BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- Literal accelerated Gaussian operation with phasewise mixing shares that also pay
for bounded-score moment transport. -/
noncomputable def seedProjectedOperational_gaussianAdaptive_scoreAware
    (hn : 1 ≤ n) (m k : Nat) (hk : 0 < k) (eps : Real)
    {N s₀ : Real} (hN : 0 < N) (hs₀ : 0 < s₀)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hKvol : volume K ≠ ⊤)
    (hbelow : ∀ i, i + 1 < m →
      adaptiveChunkStart N s₀ (adaptivePhaseChunk N s₀ i) ≤ N)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    (slack boundSq : Nat → Real) (hslack : ∀ i, 0 < slack i)
    (hboundSq : ∀ i, 0 < boundSq i)
    (deadline : Nat → ENNReal → Nat)
    (fallback tail : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)] [∀ i, IsProbabilityMeasure (tail i)]
    (fallbackBudget warmBudget : Nat → ENNReal)
    (hwarmOne : ∀ i, 1 ≤ warmBudget i)
    (hfallback : ∀ i, i + 1 < m →
      IsWarm (fallbackBudget i) (Measure.map Prod.snd (fallback i))
        (ellGaussianProb K delta (adaptiveSigmaSq N s₀ (i + 1))))
    (hgrowth : ∀ i, i + 1 < m →
      adaptiveAcceptedBudget n N s₀
          (scoreAwareRetries m k eps slack boundSq) warmBudget i + fallbackBudget i ≤
        warmBudget (i + 1))
    (mu0 : Measure (ScoreSeed n)) [IsProbabilityMeasure mu0]
    (hstart : IsWarm (warmBudget 0) (Measure.map Prod.snd mu0)
      (ellGaussianProb K delta (adaptiveSigmaSq N s₀ 0)))
    (tau : Nat → Measure (ScoreSeed n)) [∀ i, IsProbabilityMeasure (tau i)]
    (htau : ∀ i, tau i = scoreSeedReference (1 - 1 / (2 * (n : Real)))
      (Measure.map (combinedOutput (1 - 1 / (2 * (n : Real))))
        (condOn (SpeedyRejection.proposal
          (ellGaussianProb K delta (adaptiveSigmaSq N s₀ i)))
          (combinedAccept K (1 - 1 / (2 * (n : Real)))
            (adaptiveSigmaSq N s₀ i)))))
    (htailSeed : ∀ i, Measure.map Prod.snd (tail i) =
      ellGaussianProb K delta (adaptiveSigmaSq N s₀ i))
    (hmix : ∀ i (nu : Measure (State n)),
      IsWarm ((2 * warmBudget i) / scoreAwareEta m k eps slack boundSq i) nu
          (ellGaussianProb K delta (adaptiveSigmaSq N s₀ i)) →
      IsProbabilityMeasure nu →
        TVLe (sampleFromKernel
          (iteratedKernel
            (lazy (speedyMetropolisGaussian K delta (adaptiveSigmaSq N s₀ i)))
            (deadline i ((2 * warmBudget i) /
              scoreAwareEta m k eps slack boundSq i))) nu)
          (ellGaussianProb K delta (adaptiveSigmaSq N s₀ i))
          (scoreAwareZeta m k eps slack boundSq i))
    (V : Nat → (Nat → ScoreSeed n) → Real)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (u : (i : Nat) → (Finset.Iic i → ScoreSeed n) → Real)
    (v : Nat → State n → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i,
      accuracyU
          (inhomogeneousPathMeasure
            (stateScheduleFromSeed
              (activeReferenceTailSchedule m
                (warmFallbackSchedule K hK (fun _ ↦ delta) (adaptiveSigmaSq N s₀)
                  (fun _ ↦ 1 - 1 / (2 * (n : Real))) (fun _ ↦ hdelta)
                  (fun _ ↦ by
                    have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
                    have : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
                      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
                    linarith)
                  (fun i _ ↦ deadline i ((2 * warmBudget i) /
                    scoreAwareEta m k eps slack boundSq i))
                  (scoreAwareRetries m k eps slack boundSq) fallback) tail)) mu0)
          V (correctedAlpha m eps) i =
        fun omega ↦ u i (Preorder.frestrictLe i omega))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (omega (i + 1)).1) :
    SeedProjectedOperational
      (stateScheduleFromSeed
        (activeReferenceTailSchedule m
          (warmFallbackSchedule K hK (fun _ ↦ delta) (adaptiveSigmaSq N s₀)
            (fun _ ↦ 1 - 1 / (2 * (n : Real))) (fun _ ↦ hdelta)
            (fun _ ↦ by
              have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
              have : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
                rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
              linarith)
            (fun i _ ↦ deadline i ((2 * warmBudget i) /
              scoreAwareEta m k eps slack boundSq i))
            (scoreAwareRetries m k eps slack boundSq) fallback) tail))
      (activeReferenceTailSchedule m
        (warmFallbackSchedule K hK (fun _ ↦ delta) (adaptiveSigmaSq N s₀)
          (fun _ ↦ 1 - 1 / (2 * (n : Real))) (fun _ ↦ hdelta)
          (fun _ ↦ by
            have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
            have : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
              rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
            linarith)
          (fun i _ ↦ deadline i ((2 * warmBudget i) /
            scoreAwareEta m k eps slack boundSq i))
          (scoreAwareRetries m k eps slack boundSq) fallback) tail)
      Prod.snd Prod.fst mu0 V m eps := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hc0 : 0 < c := by
    have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
    have : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    dsimp [c]; linarith
  let steps : Nat → Nat → Nat := fun i _ ↦
    deadline i ((2 * warmBudget i) / scoreAwareEta m k eps slack boundSq i)
  let retries := scoreAwareRetries m k eps slack boundSq
  let mixError := scoreAwareMixError m k eps slack boundSq
  apply gaussianSeedProjectedOperational_activeReferenceTail m hK
    (fun _ ↦ delta) (adaptiveSigmaSq N s₀) (fun _ ↦ c)
    (fun _ ↦ hdelta) (fun _ ↦ hc0.ne') steps retries fallback tail mu0 V eps
    (fun i ↦ ellGaussianProb K delta (adaptiveSigmaSq N s₀ i)) tau warmBudget
    (adaptiveAcceptedBudget n N s₀ retries warmBudget) fallbackBudget mixError
    hwarmOne hstart
  · intro i hi rho hprob hrho
    simpa only [retries, steps, c] using
      activeAcceptedWarm_gaussian_adaptive hn hN hs₀ hK hKc hball hKvol hbelow
        hdelta hdeltan warmBudget steps retries i hi rho hprob hrho
  · exact hfallback
  · intro i hi; simpa only [retries] using hgrowth i hi
  · exact htailSeed
  · intro i _; exact scoreAwareMixError_ne_top m k eps slack boundSq i
  · intro i hi rho hwrho hrho
    letI : IsProbabilityMeasure rho := hrho
    have hM0 : ellGaussianMeasure K delta (adaptiveSigmaSq N s₀ i) Set.univ ≠ 0 :=
      ellGaussianMeasure_univ_ne_zero_of_ball hK hKc hball hc0
        (by dsimp [c]; exact sub_lt_self 1 (by positivity)) hdelta
        (by simpa [c] using hdeltan) (adaptiveSigmaSq_pos hN hs₀ i)
    have hMtop : ellGaussianMeasure K delta (adaptiveSigmaSq N s₀ i) Set.univ ≠ ⊤ :=
      ellGaussianMeasure_univ_ne_top (adaptiveSigmaSq_pos hN hs₀ i) K delta hKvol
    letI : IsProbabilityMeasure (ellGaussianProb K delta (adaptiveSigmaSq N s₀ i)) :=
      isProbabilityMeasure_ellGaussianProb hM0 hMtop
    letI : IsProbabilityMeasure (Measure.map (seedEmbedding c) rho) :=
      Measure.isProbabilityMeasure_map (measurable_seedEmbedding c).aemeasurable
    change TVLe (sampleFromKernel
      (gaussianWarmFallbackPhaseKernel K hK delta (adaptiveSigmaSq N s₀ i) c
        hdelta hc0.ne' (steps i) (retries i) (fallback i)) rho) (tau i) (mixError i)
    rw [sampleFrom_gaussianWarmFallbackPhaseKernel hK delta (adaptiveSigmaSq N s₀ i)
      c hdelta hc0.ne' (steps i) (retries i) (fallback i) rho, htau i]
    apply tvLe_gaussianWarmFallbackPhase_selective_zeroSafe hK hdelta hc0.ne'
      (deadline i) (Measure.map (seedEmbedding c) rho) (fallback i) (retries i)
      (pi := ellGaussianProb K delta (adaptiveSigmaSq N s₀ i))
      (tau := ellGaussianProb K delta (adaptiveSigmaSq N s₀ i))
      (M := 2 * warmBudget i) (eta := scoreAwareEta m k eps slack boundSq i)
      (zeta := scoreAwareZeta m k eps slack boundSq i)
    · exact ENNReal.ofReal_ne_zero_iff.mpr (scoreAwareShare_pos heps hslack hboundSq i)
    · intro j
      simpa only [steps, c] using
        isWarm_runningCurrent_augmentedMarginalOf_gaussian hK hdelta hc0.ne'
          rho hwrho (steps i) j
    · exact hmix i
    · exact eighth_le_ellGaussianProb_combinedAccept hn hK hKc hball hKvol hdelta
        hdeltan (adaptiveSigmaSq_pos hN hs₀ i)
    · exact scoreAwareZeta_le_sixteenth heps heps1 i
  · exact hu
  · exact hv
  · simpa only [steps, retries, c] using hU
  · exact hV
  · intro i _
    have hb := scoreAwareMixError_budget
      (m := m) (k := k) heps heps1 hslack hboundSq i
    have hk1 : (1 : Real) ≤ k := by exact_mod_cast hk
    calc
      2 * (mixError i).toReal = 1 * (2 * (mixError i).toReal) := by rw [one_mul]
      _ ≤ (k : Real) * (2 * (mixError i).toReal) :=
        mul_le_mul_of_nonneg_right hk1 (by positivity)
      _ ≤ correctedNu m eps := by simpa only [mixError] using hb

#print axioms seedProjectedOperational_gaussianAdaptive_scoreAware

end Ttc.CVGaussianScoreAwareOperational
