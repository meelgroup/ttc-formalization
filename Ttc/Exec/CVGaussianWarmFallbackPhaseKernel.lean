import Ttc.Exec.FiniteContinuingRetryRandomFallback
import Ttc.Exec.CVGaussianAugmentedSelectiveTV
import Ttc.Exec.CVFiniteContinuingPhaseDistributional

/-!
# Gaussian finite-retry phase with an independent warm fallback

This is the phase-level adapter for `FiniteContinuingRetryRandomFallback`.  It runs the
finite augmented Gaussian retry machine from the incoming seed, keeps accepted
`(score,raw-seed)` outputs, and replaces the unresolved branch by one independent
sampleable fallback draw.  Accuracy may charge that branch by its survival probability;
the seed projection remains warm and can therefore drive the next phase honestly.
-/

namespace Ttc.CVGaussianWarmFallbackPhaseKernel

open MeasureTheory ProbabilityTheory Set
open Arlib Arlib.Probability Arlib.MarkovChains
open Ttc.CVSequentialPhaseSampler
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryGaussianAugmentedPhase
open Ttc.FiniteContinuingRetryRandomFallback
open Ttc.FiniteContinuingRetryEmbeddedSelective
open Ttc.CVGaussianAugmentedSelectiveTV
open Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.CVCombinedContinuingRetryPhaseTV
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- Honest linear phase kernel: finite retry followed by independent random fallback
postprocessing of the unresolved state. -/
noncomputable def gaussianWarmFallbackPhaseKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat)
    (fallback : Measure (ScoreSeed n)) [IsProbabilityMeasure fallback] :
    Kernel (State n) (ScoreSeed n) :=
  randomFallbackKernel fallback ∘ₖ
    Kernel.comap
      (augmentedGaussianRetryStateKernel K hK delta s c hdelta hc steps L)
      (seedEmbedding c) (measurable_seedEmbedding c)

instance gaussianWarmFallbackPhaseKernel.isMarkovKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat)
    (fallback : Measure (ScoreSeed n)) [IsProbabilityMeasure fallback] :
    IsMarkovKernel
      (gaussianWarmFallbackPhaseKernel K hK delta s c hdelta hc steps L fallback) := by
  unfold gaussianWarmFallbackPhaseKernel
  infer_instance

/-- Exact arbitrary-incoming-law execution identity. -/
theorem sampleFrom_gaussianWarmFallbackPhaseKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat)
    (fallback : Measure (ScoreSeed n)) [IsProbabilityMeasure fallback]
    (rho : Measure (State n)) [IsProbabilityMeasure rho] :
    sampleFromKernel
        (gaussianWarmFallbackPhaseKernel K hK delta s c hdelta hc steps L fallback) rho =
      sampleFromKernel (randomFallbackKernel fallback)
        (augmentedMarginalOf K hK delta s c hdelta hc steps
          (Measure.map (seedEmbedding c) rho) L) := by
  let rhoPair := Measure.map (seedEmbedding c) rho
  letI : IsProbabilityMeasure rhoPair :=
    Measure.isProbabilityMeasure_map (measurable_seedEmbedding c).aemeasurable
  unfold gaussianWarmFallbackPhaseKernel sampleFromKernel
  rw [← Measure.comp_assoc, Arlib.MarkovChains.bind_comap]
  change (sampleFromKernel
      (augmentedGaussianRetryStateKernel K hK delta s c hdelta hc steps L) rhoPair).bind
        (randomFallbackKernel fallback) = _
  rw [sampleFrom_augmentedRetryStateKernel_eq_marginalOf]

/-- Seed-projected warmness sum.  Accepted mass costs `Macc`; the entire unresolved mass
costs only the warmness `Mfb` of one independent fallback draw, never an atom and never
the incoming phase's cross-target warmness. -/
theorem isWarm_seed_randomFallback
    (mu : Measure (RetryState (State n) (ScoreSeed n))) [IsProbabilityMeasure mu]
    (fallback : Measure (ScoreSeed n)) [IsProbabilityMeasure fallback]
    (piNext : Measure (State n)) {Macc Mfb : ENNReal}
    (hacc : IsWarm Macc
      (Measure.map Prod.snd (acceptedOutputSubmeasure mu)) piNext)
    (hfb : IsWarm Mfb (Measure.map Prod.snd fallback) piNext) :
    IsWarm (Macc + Mfb)
      (Measure.map Prod.snd
        (sampleFromKernel (randomFallbackKernel fallback) mu)) piNext := by
  rw [sampleFrom_randomFallbackKernel mu fallback,
    Measure.map_add (acceptedOutputSubmeasure mu)
      (mu Ttc.FiniteContinuingRetry.runningStates • fallback) measurable_snd,
    Measure.map_smul]
  intro T hT
  rw [Measure.add_apply, Measure.smul_apply]
  calc
    Measure.map Prod.snd (acceptedOutputSubmeasure mu) T +
        mu Ttc.FiniteContinuingRetry.runningStates * Measure.map Prod.snd fallback T ≤
      Macc * piNext T + 1 * (Mfb * piNext T) := by
        gcongr
        · exact hacc T hT
        · exact prob_le_one
        · exact hfb T hT
    _ = (Macc + Mfb) * piNext T := by rw [one_mul, add_mul]

/-- Phase-level form of the preceding seed warmness assembly. -/
theorem isWarm_seed_sampleFrom_gaussianWarmFallbackPhaseKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat)
    (fallback : Measure (ScoreSeed n)) [IsProbabilityMeasure fallback]
    (rho : Measure (State n)) [IsProbabilityMeasure rho]
    (piNext : Measure (State n)) {Macc Mfb : ENNReal}
    (hacc : IsWarm Macc
      (Measure.map Prod.snd
        (acceptedOutputSubmeasure
          (augmentedMarginalOf K hK delta s c hdelta hc steps
            (Measure.map (seedEmbedding c) rho) L))) piNext)
    (hfb : IsWarm Mfb (Measure.map Prod.snd fallback) piNext) :
    IsWarm (Macc + Mfb)
      (Measure.map Prod.snd
        (sampleFromKernel
          (gaussianWarmFallbackPhaseKernel K hK delta s c hdelta hc steps L fallback)
          rho)) piNext := by
  let rhoPair := Measure.map (seedEmbedding c) rho
  letI : IsProbabilityMeasure rhoPair :=
    Measure.isProbabilityMeasure_map (measurable_seedEmbedding c).aemeasurable
  let mu := augmentedMarginalOf K hK delta s c hdelta hc steps rhoPair L
  haveI : IsProbabilityMeasure mu :=
    isProbabilityMeasure_embeddedMarginal
      (phaseCandidate K hK delta s hdelta steps)
      (Ttc.FiniteContinuingRetryGaussian.costedCombinedAccept K c s)
      (Ttc.FiniteContinuingRetryGaussian.measurableSet_costedCombinedAccept hK hc)
      Ttc.FiniteContinuingRetryGaussian.rejectedNext
      Ttc.FiniteContinuingRetryGaussian.measurable_rejectedNext
      (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
      Ttc.FiniteContinuingRetryGaussian.roundQueryCost
      Ttc.FiniteContinuingRetryGaussian.measurable_roundQueryCost
      augmentedEmbedding measurable_augmentedEmbedding rhoPair L
  rw [sampleFrom_gaussianWarmFallbackPhaseKernel hK delta s c hdelta hc steps L
    fallback rho]
  exact isWarm_seed_randomFallback mu fallback piNext hacc hfb

/-- The repository's adaptive cold restart fits the unresolved branch at every phase.
Its warm constant may grow geometrically, but only its logarithm enters the mixing
deadline. -/
theorem isWarm_seed_coldScoreSeedFallback_adaptive
    {m : Nat} {K : Set (State n)} (hKm : MeasurableSet K) (hKc : Convex Real K)
    (hn : 1 ≤ n) (hball : Metric.ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {N s0 radius c delta : Real} (hN : 0 < N) (hs0 : 0 < s0)
    (hc0 : 0 < c) (hc1 : c < 1) (hradius : 0 < radius) (hradiusc : radius < c)
    (hcold : 4 * (n : Real) * s0 ≤ radius ^ 2) (hdelta : 0 < delta)
    (hdeltac : delta ≤ 1 - c)
    (hbelow : ∀ j, j + 1 < m →
      Arlib.GaussianCooling.Chunked.adaptiveChunkStart N s0
        (Arlib.GaussianCooling.Chunked.adaptivePhaseChunk N s0 j) ≤ N)
    {i : Nat} (hi : i < m) (scoreScale : Real) :
    IsWarm (ENNReal.ofReal (Arlib.GaussianCooling.Chunked.adaptiveRestartWarmConst n i))
      (Measure.map Prod.snd
        (coldScoreSeedFallback (n := n) scoreScale s0 radius))
      (ellGaussianProb K delta (Arlib.GaussianCooling.Chunked.adaptiveSigmaSq N s0 i)) := by
  apply isWarm_snd_coldScoreSeedFallback
  exact Arlib.GaussianCooling.Chunked.isWarm_coldBallStart_adaptive_ellGaussianProb
    hKm hKc hn hball hfin hN hs0 hc0 hc1 hradius hradiusc hcold hdelta hdeltac
    hbelow hi

#print axioms sampleFrom_gaussianWarmFallbackPhaseKernel
#print axioms isWarm_seed_randomFallback
#print axioms isWarm_seed_sampleFrom_gaussianWarmFallbackPhaseKernel
#print axioms isWarm_seed_coldScoreSeedFallback_adaptive

end Ttc.CVGaussianWarmFallbackPhaseKernel
