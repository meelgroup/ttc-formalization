import Ttc.Exec.CVColdAcceptedWarm
import Ttc.Exec.CVGaussianWarmFallbackCostedPhaseKernel
import Ttc.Exec.CVColdHotScoreSeedSchedule

/-!
# Literal radius-four/full-body random-fallback schedule

The cold block runs the same finite augmented Gaussian retry machine as the retained
reference certificate, but postprocesses only the unresolved branch with an independent
sampleable fallback.  The hot block is the existing full-body warm-fallback family.
Both blocks record exactly the retry cost; the fallback draw itself is query-free.
-/

set_option autoImplicit false

namespace Ttc.CVGaussianColdHotFallbackSchedule

open MeasureTheory ProbabilityTheory
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVSourceTruncatedFixedCost
open Ttc.CVCorrectedFixedBlockCost
open Ttc.CVGaussianWarmFallbackPhaseKernel
open Ttc.CVGaussianWarmFallbackCostedPhaseKernel
open Ttc.CVColdHotScoreSeedSchedule
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

noncomputable def coldWarmFallbackKernel
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)] :
    Nat → Kernel (State n) (ScoreSeed n) := fun i ↦
  gaussianWarmFallbackPhaseKernel
    (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
    (measurableSet_fixedRadiusFourBody hK _)
    (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
    (fixedSigmaSq n s0 i)
    (1 - 1 / (2 * (n : Real)))
    (fixedRadiusFourDelta_pos hn (by
      unfold fixedSigmaSq
      exact geomSchedule_pos hs0 (by positivity) i))
    (by
      have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
      have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      linarith)
    (steps i) (retries i) (fallback i)

instance coldWarmFallbackKernel.isMarkovKernel
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)] (i : Nat) :
    IsMarkovKernel (coldWarmFallbackKernel hn K hK s0 hs0
      steps retries fallback i) := by
  unfold coldWarmFallbackKernel
  infer_instance

noncomputable def coldWarmFallbackCostedKernel
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)] :
    Nat → Kernel (State n) (ENNReal × ScoreSeed n) := fun i ↦
  gaussianWarmFallbackCostedPhaseKernel
    (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
    (measurableSet_fixedRadiusFourBody hK _)
    (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
    (fixedSigmaSq n s0 i)
    (1 - 1 / (2 * (n : Real)))
    (fixedRadiusFourDelta_pos hn (by
      unfold fixedSigmaSq
      exact geomSchedule_pos hs0 (by positivity) i))
    (by
      have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
      have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      linarith)
    (steps i) (retries i) (fallback i)

instance coldWarmFallbackCostedKernel.isMarkovKernel
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)] (i : Nat) :
    IsMarkovKernel (coldWarmFallbackCostedKernel hn K hK s0 hs0
      steps retries fallback i) := by
  unfold coldWarmFallbackCostedKernel
  infer_instance

theorem map_snd_coldWarmFallbackCostedKernel
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)] (i : Nat) (x : State n) :
    Measure.map Prod.snd
        (coldWarmFallbackCostedKernel hn K hK s0 hs0 steps retries fallback i x) =
      coldWarmFallbackKernel hn K hK s0 hs0 steps retries fallback i x := by
  exact map_snd_gaussianWarmFallbackCostedPhaseKernel
    (measurableSet_fixedRadiusFourBody hK _)
    (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
    (fixedSigmaSq n s0 i) (1 - 1 / (2 * (n : Real)))
    (fixedRadiusFourDelta_pos hn (by
      unfold fixedSigmaSq
      exact geomSchedule_pos hs0 (by positivity) i))
    (by
      have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
      have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      linarith)
    (steps i) (retries i) (fallback i) x

/-- Globally indexed cold/hot operational state kernel. -/
noncomputable def coldHotWarmFallbackSchedule
    (hn : 1 ≤ n) (cold : Nat)
    (K : Set (State n)) (hK : MeasurableSet K) (s0 : Real) (hs0 : 0 < s0)
    (coldSteps : Nat → Nat → Nat) (coldRetries : Nat → Nat)
    (coldFallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (coldFallback i)]
    (hotDelta hotSigmaSq hotShrink : Nat → Real)
    (hhotDelta : ∀ i, 0 < hotDelta i) (hhotShrink : ∀ i, hotShrink i ≠ 0)
    (hotSteps : Nat → Nat → Nat) (hotRetries : Nat → Nat)
    (hotFallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (hotFallback i)] :
    Nat → Kernel (State n) (ScoreSeed n) :=
  coldHotSchedule cold
    (coldWarmFallbackKernel hn K hK s0 hs0 coldSteps coldRetries coldFallback)
    (Ttc.CVGaussianWarmFallbackOperational.warmFallbackSchedule K hK
      hotDelta hotSigmaSq hotShrink hhotDelta hhotShrink hotSteps hotRetries hotFallback)

/-- Costed companion of `coldHotWarmFallbackSchedule`. -/
noncomputable def coldHotWarmFallbackCostedSchedule
    (hn : 1 ≤ n) (cold : Nat)
    (K : Set (State n)) (hK : MeasurableSet K) (s0 : Real) (hs0 : 0 < s0)
    (coldSteps : Nat → Nat → Nat) (coldRetries : Nat → Nat)
    (coldFallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (coldFallback i)]
    (hotDelta hotSigmaSq hotShrink : Nat → Real)
    (hhotDelta : ∀ i, 0 < hotDelta i) (hhotShrink : ∀ i, hotShrink i ≠ 0)
    (hotSteps : Nat → Nat → Nat) (hotRetries : Nat → Nat)
    (hotFallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (hotFallback i)] :
    Nat → Kernel (State n) (ENNReal × ScoreSeed n) :=
  coldHotCostedSchedule cold
    (coldWarmFallbackCostedKernel hn K hK s0 hs0
      coldSteps coldRetries coldFallback)
    (warmFallbackCostedSchedule K hK hotDelta hotSigmaSq hotShrink
      hhotDelta hhotShrink hotSteps hotRetries hotFallback)

theorem map_snd_coldHotWarmFallbackCostedSchedule
    (hn : 1 ≤ n) (cold : Nat)
    (K : Set (State n)) (hK : MeasurableSet K) (s0 : Real) (hs0 : 0 < s0)
    (coldSteps : Nat → Nat → Nat) (coldRetries : Nat → Nat)
    (coldFallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (coldFallback i)]
    (hotDelta hotSigmaSq hotShrink : Nat → Real)
    (hhotDelta : ∀ i, 0 < hotDelta i) (hhotShrink : ∀ i, hotShrink i ≠ 0)
    (hotSteps : Nat → Nat → Nat) (hotRetries : Nat → Nat)
    (hotFallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (hotFallback i)] (i : Nat) (x : State n) :
    Measure.map Prod.snd
        (coldHotWarmFallbackCostedSchedule hn cold K hK s0 hs0
          coldSteps coldRetries coldFallback hotDelta hotSigmaSq hotShrink
          hhotDelta hhotShrink hotSteps hotRetries hotFallback i x) =
      coldHotWarmFallbackSchedule hn cold K hK s0 hs0
        coldSteps coldRetries coldFallback hotDelta hotSigmaSq hotShrink
        hhotDelta hhotShrink hotSteps hotRetries hotFallback i x := by
  apply map_snd_coldHotCostedSchedule
  · exact map_snd_coldWarmFallbackCostedKernel hn K hK s0 hs0
      coldSteps coldRetries coldFallback
  · intro j y
    exact map_snd_gaussianWarmFallbackCostedPhaseKernel hK
      (hotDelta j) (hotSigmaSq j) (hotShrink j) (hhotDelta j) (hhotShrink j)
      (hotSteps j) (hotRetries j) (hotFallback j) y

#print axioms map_snd_coldWarmFallbackCostedKernel
#print axioms map_snd_coldHotWarmFallbackCostedSchedule

end Ttc.CVGaussianColdHotFallbackSchedule
