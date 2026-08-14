import Ttc.Exec.CVGaussianAdaptiveAcceptedWarm
import Ttc.Exec.CVGaussianBlockRetryParameters
import Ttc.Exec.CVGaussianWarmFallbackCappedOperational

/-! Capped accelerated Gaussian operation with `k`-tensorized retry errors. -/

namespace Ttc.CVGaussianAdaptiveBlockOperational

open MeasureTheory ProbabilityTheory Metric Set Pointwise
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open Ttc.CVCorrected Ttc.CVSequentialPhaseSampler
open Ttc.FiniteContinuingRetry Ttc.FiniteContinuingRetryGaussian
open Ttc.FiniteContinuingRetryGaussianAugmentedPhase
open Ttc.FiniteContinuingRetryRandomFallback
open Ttc.CVGaussianAugmentedSelectiveTV Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.CVSeedProjectedDependence Ttc.CVScoreSeedPhaseKernel
open Ttc.CVGaussianWarmFallbackOperational Ttc.CVGaussianWarmFallbackAnalytic
open Ttc.CVGaussianWarmFallbackPhaseKernel
open Ttc.CVGaussianWarmFallbackZeroSafe
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVGaussianAdaptiveAcceptedWarm Ttc.CVGaussianBlockRetryParameters
open Ttc.CVCombinedContinuingAccept Ttc.CVIdealCombinedAccepted
open Ttc.CVIndependentStreamDependence
open scoped ENNReal Classical BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- Scalar capped operation at the literal accelerated variances.  All accepted warmth,
k-scaled retry-tail arithmetic, and killed-current retry warmth are discharged. -/
noncomputable def seedProjectedOperational_gaussianAdaptive_block
    (hn : 1 ≤ n) (m k : Nat) (hk : 0 < k) (eps : Real)
    {N s₀ : Real} (hN : 0 < N) (hs₀ : 0 < s₀)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hKvol : volume K ≠ ⊤)
    (hbelow : ∀ i, i + 1 < m →
      adaptiveChunkStart N s₀ (adaptivePhaseChunk N s₀ i) ≤ N)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    (deadline : Nat → ENNReal → Nat)
    (fallback tail : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)]
    [∀ i, IsProbabilityMeasure (tail i)]
    (fallbackBudget warmBudget : Nat → ENNReal)
    (hwarmOne : ∀ i, 1 ≤ warmBudget i)
    (hfallback : ∀ i, i + 1 < m →
      IsWarm (fallbackBudget i) (Measure.map Prod.snd (fallback i))
        (ellGaussianProb K delta (adaptiveSigmaSq N s₀ (i + 1))))
    (hgrowth : ∀ i, i + 1 < m →
      adaptiveAcceptedBudget n N s₀ (fun _ ↦ blockRetries m k eps) warmBudget i +
          fallbackBudget i ≤ warmBudget (i + 1))
    (mu0 : Measure (ScoreSeed n)) [IsProbabilityMeasure mu0]
    (hstart : IsWarm (warmBudget 0) (Measure.map Prod.snd mu0)
      (ellGaussianProb K delta (adaptiveSigmaSq N s₀ 0)))
    (tau : Nat → Measure (ScoreSeed n)) [∀ i, IsProbabilityMeasure (tau i)]
    (htau : ∀ i, tau i = scoreSeedReference (1 - 1 / (2 * (n : Real)))
      (Measure.map (combinedOutput (1 - 1 / (2 * (n : Real))))
        (condOn
          (SpeedyRejection.proposal
            (ellGaussianProb K delta (adaptiveSigmaSq N s₀ i)))
          (combinedAccept K (1 - 1 / (2 * (n : Real)))
            (adaptiveSigmaSq N s₀ i)))))
    (htailSeed : ∀ i, Measure.map Prod.snd (tail i) =
      ellGaussianProb K delta (adaptiveSigmaSq N s₀ i))
    (hmix : ∀ i (nu : Measure (State n)),
      IsWarm ((2 * warmBudget i) / blockEta m k eps) nu
          (ellGaussianProb K delta (adaptiveSigmaSq N s₀ i)) →
      IsProbabilityMeasure nu →
        TVLe (sampleFromKernel
          (iteratedKernel
            (lazy (speedyMetropolisGaussian K delta (adaptiveSigmaSq N s₀ i)))
            (deadline i ((2 * warmBudget i) / blockEta m k eps))) nu)
          (ellGaussianProb K delta (adaptiveSigmaSq N s₀ i))
          (blockZeta m k eps))
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
                (warmFallbackSchedule K hK (fun _ ↦ delta)
                  (adaptiveSigmaSq N s₀)
                  (fun _ ↦ 1 - 1 / (2 * (n : Real))) (fun _ ↦ hdelta)
                  (fun _ ↦ by
                    have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
                    have : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
                      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
                      linarith
                    linarith)
                  (fun i _ ↦ deadline i ((2 * warmBudget i) / blockEta m k eps))
                  (fun _ ↦ blockRetries m k eps) fallback) tail)) mu0)
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
                rw [div_le_div_iff₀ (by positivity) (by norm_num)]
                linarith
              linarith)
            (fun i _ ↦ deadline i ((2 * warmBudget i) / blockEta m k eps))
            (fun _ ↦ blockRetries m k eps) fallback) tail))
      (activeReferenceTailSchedule m
        (warmFallbackSchedule K hK (fun _ ↦ delta) (adaptiveSigmaSq N s₀)
          (fun _ ↦ 1 - 1 / (2 * (n : Real))) (fun _ ↦ hdelta)
          (fun _ ↦ by
            have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
            have : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
              rw [div_le_div_iff₀ (by positivity) (by norm_num)]
              linarith
            linarith)
          (fun i _ ↦ deadline i ((2 * warmBudget i) / blockEta m k eps))
          (fun _ ↦ blockRetries m k eps) fallback) tail)
      Prod.snd Prod.fst mu0 V m eps := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hc0 : 0 < c := by
    have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
    have : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    dsimp [c]
    linarith
  let steps : Nat → Nat → Nat := fun i _ ↦
    deadline i ((2 * warmBudget i) / blockEta m k eps)
  let retries : Nat → Nat := fun _ ↦ blockRetries m k eps
  let mixError : Nat → ENNReal := fun _ ↦ blockMixError m k eps
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
  · intro i hi
    simpa only [retries] using hgrowth i hi
  · exact htailSeed
  · intro i hi
    exact blockMixError_ne_top m k eps
  · intro i hi rho hwrho hrho
    letI : IsProbabilityMeasure rho := hrho
    have hM0 : ellGaussianMeasure K delta (adaptiveSigmaSq N s₀ i) Set.univ ≠ 0 :=
      ellGaussianMeasure_univ_ne_zero_of_ball hK hKc hball hc0
        (by dsimp [c]; exact sub_lt_self 1 (by positivity)) hdelta
        (by simpa [c] using hdeltan) (adaptiveSigmaSq_pos hN hs₀ i)
    have hMtop : ellGaussianMeasure K delta (adaptiveSigmaSq N s₀ i) Set.univ ≠ ⊤ :=
      ellGaussianMeasure_univ_ne_top (adaptiveSigmaSq_pos hN hs₀ i) K delta hKvol
    letI : IsProbabilityMeasure
        (ellGaussianProb K delta (adaptiveSigmaSq N s₀ i)) :=
      isProbabilityMeasure_ellGaussianProb hM0 hMtop
    letI : IsProbabilityMeasure (Measure.map (seedEmbedding c) rho) :=
      Measure.isProbabilityMeasure_map (measurable_seedEmbedding c).aemeasurable
    change TVLe
      (sampleFromKernel
        (gaussianWarmFallbackPhaseKernel K hK delta (adaptiveSigmaSq N s₀ i) c
          hdelta hc0.ne' (steps i) (retries i) (fallback i)) rho)
      (tau i) (mixError i)
    rw [sampleFrom_gaussianWarmFallbackPhaseKernel hK delta (adaptiveSigmaSq N s₀ i)
      c hdelta hc0.ne' (steps i) (retries i) (fallback i) rho, htau i]
    apply tvLe_gaussianWarmFallbackPhase_selective_zeroSafe hK hdelta hc0.ne'
      (deadline i) (Measure.map (seedEmbedding c) rho) (fallback i) (retries i)
      (pi := ellGaussianProb K delta (adaptiveSigmaSq N s₀ i))
      (tau := ellGaussianProb K delta (adaptiveSigmaSq N s₀ i))
      (M := 2 * warmBudget i) (eta := blockEta m k eps) (zeta := blockZeta m k eps)
    · exact ENNReal.ofReal_ne_zero_iff.mpr (blockShare_pos heps)
    · intro j
      simpa only [steps, c] using
        isWarm_runningCurrent_augmentedMarginalOf_gaussian hK hdelta hc0.ne'
          rho hwrho (steps i) j
    · exact hmix i
    · exact eighth_le_ellGaussianProb_combinedAccept hn hK hKc hball hKvol hdelta
        hdeltan (adaptiveSigmaSq_pos hN hs₀ i)
    · exact blockZeta_le_sixteenth heps heps1
  · exact hu
  · exact hv
  · simpa only [steps, retries, c] using hU
  · exact hV
  · intro i hi
    exact blockMixError_scalar_budget hk heps heps1

#print axioms seedProjectedOperational_gaussianAdaptive_block

end Ttc.CVGaussianAdaptiveBlockOperational
