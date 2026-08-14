import Ttc.Exec.CVAdaptiveRadiusQPrimitives
import Ttc.Exec.CVGaussianWarmFallbackCostedPhaseKernel

/-! Operational all-phase random-fallback kernels at a globally selected radius `q`. -/

set_option autoImplicit false

namespace Ttc.CVHybridRadiusQFallbackSchedule

open MeasureTheory ProbabilityTheory
open Arlib Arlib.MarkovChains
open Ttc.CVHybridSchedule
open Ttc.CVAdaptiveRadiusQPrimitives
open Ttc.CVGaussianWarmFallbackPhaseKernel
open Ttc.CVGaussianWarmFallbackCostedPhaseKernel
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

noncomputable def hybridRadiusQWarmFallbackKernel
    (hn : 1 ≤ n) (q : Real) (hq : 0 < q)
    (K : Set (State n)) (hK : MeasurableSet K)
    (N s0 : Real) (hN : 0 < N) (hs0 : 0 < s0)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)] :
    Nat → Kernel (State n) (ScoreSeed n) := fun i ↦
  gaussianWarmFallbackPhaseKernel
    (radiusQBody q K (sigmaSq n N s0 i))
    (measurableSet_radiusQBody hK)
    (radiusQDelta n q (sigmaSq n N s0 i))
    (sigmaSq n N s0 i)
    (1 - 1 / (2 * (n : Real)))
    (radiusQDelta_pos hn hq (sigmaSq_pos hn hN hs0 i))
    (by
      have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
      have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      linarith)
    (steps i) (retries i) (fallback i)

instance hybridRadiusQWarmFallbackKernel.isMarkovKernel
    (hn : 1 ≤ n) (q : Real) (hq : 0 < q)
    (K : Set (State n)) (hK : MeasurableSet K)
    (N s0 : Real) (hN : 0 < N) (hs0 : 0 < s0)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)] (i : Nat) :
    IsMarkovKernel (hybridRadiusQWarmFallbackKernel hn q hq K hK N s0 hN hs0
      steps retries fallback i) := by
  unfold hybridRadiusQWarmFallbackKernel
  infer_instance

noncomputable def hybridRadiusQWarmFallbackCostedKernel
    (hn : 1 ≤ n) (q : Real) (hq : 0 < q)
    (K : Set (State n)) (hK : MeasurableSet K)
    (N s0 : Real) (hN : 0 < N) (hs0 : 0 < s0)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)] :
    Nat → Kernel (State n) (ENNReal × ScoreSeed n) := fun i ↦
  gaussianWarmFallbackCostedPhaseKernel
    (radiusQBody q K (sigmaSq n N s0 i))
    (measurableSet_radiusQBody hK)
    (radiusQDelta n q (sigmaSq n N s0 i))
    (sigmaSq n N s0 i)
    (1 - 1 / (2 * (n : Real)))
    (radiusQDelta_pos hn hq (sigmaSq_pos hn hN hs0 i))
    (by
      have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
      have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      linarith)
    (steps i) (retries i) (fallback i)

instance hybridRadiusQWarmFallbackCostedKernel.isMarkovKernel
    (hn : 1 ≤ n) (q : Real) (hq : 0 < q)
    (K : Set (State n)) (hK : MeasurableSet K)
    (N s0 : Real) (hN : 0 < N) (hs0 : 0 < s0)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)] (i : Nat) :
    IsMarkovKernel (hybridRadiusQWarmFallbackCostedKernel hn q hq K hK N s0 hN hs0
      steps retries fallback i) := by
  unfold hybridRadiusQWarmFallbackCostedKernel
  infer_instance

theorem map_snd_hybridRadiusQWarmFallbackCostedKernel
    (hn : 1 ≤ n) (q : Real) (hq : 0 < q)
    (K : Set (State n)) (hK : MeasurableSet K)
    (N s0 : Real) (hN : 0 < N) (hs0 : 0 < s0)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)] (i : Nat) (x : State n) :
    Measure.map Prod.snd
        (hybridRadiusQWarmFallbackCostedKernel hn q hq K hK N s0 hN hs0
          steps retries fallback i x) =
      hybridRadiusQWarmFallbackKernel hn q hq K hK N s0 hN hs0
        steps retries fallback i x := by
  exact map_snd_gaussianWarmFallbackCostedPhaseKernel
    (measurableSet_radiusQBody hK)
    (radiusQDelta n q (sigmaSq n N s0 i)) (sigmaSq n N s0 i)
    (1 - 1 / (2 * (n : Real)))
    (radiusQDelta_pos hn hq (sigmaSq_pos hn hN hs0 i))
    (by
      have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
      have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      linarith)
    (steps i) (retries i) (fallback i) x

#print axioms map_snd_hybridRadiusQWarmFallbackCostedKernel

end Ttc.CVHybridRadiusQFallbackSchedule
