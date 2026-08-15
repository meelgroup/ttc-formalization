import Ttc.Exec.CVAdaptiveRadiusQPrimitives
import Ttc.Exec.CVGaussianWarmFallbackCostedPhaseKernel

/-! Radius-`q` warm-fallback kernels parameterized by an arbitrary positive variance schedule. -/

set_option autoImplicit false

namespace Ttc.CVRadiusQGenericFallbackSchedule

open MeasureTheory ProbabilityTheory
open Arlib Arlib.MarkovChains
open Ttc.CVAdaptiveRadiusQPrimitives
open Ttc.CVGaussianWarmFallbackPhaseKernel
open Ttc.CVGaussianWarmFallbackCostedPhaseKernel
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

noncomputable def radiusQWarmFallbackKernelOfSigma
    (hn : 1 ≤ n) (q : Real) (hq : 0 < q)
    (K : Set (State n)) (hK : MeasurableSet K)
    (sigmaSq : Nat → Real) (hsigma : ∀ i, 0 < sigmaSq i)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)] :
    Nat → Kernel (State n) (ScoreSeed n) := fun i ↦
  gaussianWarmFallbackPhaseKernel
    (radiusQBody q K (sigmaSq i)) (measurableSet_radiusQBody hK)
    (radiusQDelta n q (sigmaSq i)) (sigmaSq i)
    (1 - 1 / (2 * (n : Real)))
    (radiusQDelta_pos hn hq (hsigma i))
    (by
      have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
      have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      linarith)
    (steps i) (retries i) (fallback i)

instance radiusQWarmFallbackKernelOfSigma.isMarkovKernel
    (hn : 1 ≤ n) (q : Real) (hq : 0 < q)
    (K : Set (State n)) (hK : MeasurableSet K)
    (sigmaSq : Nat → Real) (hsigma : ∀ i, 0 < sigmaSq i)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)] (i : Nat) :
    IsMarkovKernel (radiusQWarmFallbackKernelOfSigma hn q hq K hK sigmaSq hsigma
      steps retries fallback i) := by
  unfold radiusQWarmFallbackKernelOfSigma
  infer_instance

noncomputable def radiusQWarmFallbackCostedKernelOfSigma
    (hn : 1 ≤ n) (q : Real) (hq : 0 < q)
    (K : Set (State n)) (hK : MeasurableSet K)
    (sigmaSq : Nat → Real) (hsigma : ∀ i, 0 < sigmaSq i)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)] :
    Nat → Kernel (State n) (ENNReal × ScoreSeed n) := fun i ↦
  gaussianWarmFallbackCostedPhaseKernel
    (radiusQBody q K (sigmaSq i)) (measurableSet_radiusQBody hK)
    (radiusQDelta n q (sigmaSq i)) (sigmaSq i)
    (1 - 1 / (2 * (n : Real)))
    (radiusQDelta_pos hn hq (hsigma i))
    (by
      have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
      have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      linarith)
    (steps i) (retries i) (fallback i)

instance radiusQWarmFallbackCostedKernelOfSigma.isMarkovKernel
    (hn : 1 ≤ n) (q : Real) (hq : 0 < q)
    (K : Set (State n)) (hK : MeasurableSet K)
    (sigmaSq : Nat → Real) (hsigma : ∀ i, 0 < sigmaSq i)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)] (i : Nat) :
    IsMarkovKernel (radiusQWarmFallbackCostedKernelOfSigma hn q hq K hK sigmaSq hsigma
      steps retries fallback i) := by
  unfold radiusQWarmFallbackCostedKernelOfSigma
  infer_instance

theorem map_snd_radiusQWarmFallbackCostedKernelOfSigma
    (hn : 1 ≤ n) (q : Real) (hq : 0 < q)
    (K : Set (State n)) (hK : MeasurableSet K)
    (sigmaSq : Nat → Real) (hsigma : ∀ i, 0 < sigmaSq i)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)] (i : Nat) (x : State n) :
    Measure.map Prod.snd
        (radiusQWarmFallbackCostedKernelOfSigma hn q hq K hK sigmaSq hsigma
          steps retries fallback i x) =
      radiusQWarmFallbackKernelOfSigma hn q hq K hK sigmaSq hsigma
        steps retries fallback i x := by
  exact map_snd_gaussianWarmFallbackCostedPhaseKernel
    (measurableSet_radiusQBody hK) (radiusQDelta n q (sigmaSq i)) (sigmaSq i)
    (1 - 1 / (2 * (n : Real))) (radiusQDelta_pos hn hq (hsigma i))
    (by
      have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
      have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      linarith)
    (steps i) (retries i) (fallback i) x

#print axioms map_snd_radiusQWarmFallbackCostedKernelOfSigma

end Ttc.CVRadiusQGenericFallbackSchedule
