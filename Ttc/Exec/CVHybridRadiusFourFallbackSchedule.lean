import Ttc.Exec.CVAdaptiveRadiusFourCrossWarm
import Ttc.Exec.CVGaussianWarmFallbackCostedPhaseKernel

/-! Operational random-fallback kernels on the hybrid schedule's radius-four bodies. -/

set_option autoImplicit false

namespace Ttc.CVHybridRadiusFourFallbackSchedule

open MeasureTheory ProbabilityTheory
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVHybridSchedule
open Ttc.CVSourceTruncatedFixedCost
open Ttc.CVGaussianWarmFallbackPhaseKernel
open Ttc.CVGaussianWarmFallbackCostedPhaseKernel
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

noncomputable def hybridRadiusFourBody
    (n : Nat) (N s0 : Real) (K : Set (State n)) (i : Nat) : Set (State n) :=
  fixedRadiusFourBody K (sigmaSq n N s0 i)

noncomputable def hybridRadiusFourDelta
    (n : Nat) (N s0 : Real) (i : Nat) : Real :=
  fixedRadiusFourDelta n (sigmaSq n N s0 i)

noncomputable def hybridRadiusFourWarmFallbackKernel
    (hn : 1 <= n) (K : Set (State n)) (hK : MeasurableSet K)
    (N s0 : Real) (hN : 0 < N) (hs0 : 0 < s0)
    (steps : Nat -> Nat -> Nat) (retries : Nat -> Nat)
    (fallback : Nat -> Measure (ScoreSeed n))
    [forall i, IsProbabilityMeasure (fallback i)] :
    Nat -> Kernel (State n) (ScoreSeed n) := fun i =>
  gaussianWarmFallbackPhaseKernel
    (hybridRadiusFourBody n N s0 K i)
    (measurableSet_fixedRadiusFourBody hK _)
    (hybridRadiusFourDelta n N s0 i)
    (sigmaSq n N s0 i)
    (1 - 1 / (2 * (n : Real)))
    (fixedRadiusFourDelta_pos hn (sigmaSq_pos hn hN hs0 i))
    (by
      have hnR : (1 : Real) <= n := by exact_mod_cast hn
      have hhalf : 1 / (2 * (n : Real)) <= 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      linarith)
    (steps i) (retries i) (fallback i)

instance hybridRadiusFourWarmFallbackKernel.isMarkovKernel
    (hn : 1 <= n) (K : Set (State n)) (hK : MeasurableSet K)
    (N s0 : Real) (hN : 0 < N) (hs0 : 0 < s0)
    (steps : Nat -> Nat -> Nat) (retries : Nat -> Nat)
    (fallback : Nat -> Measure (ScoreSeed n))
    [forall i, IsProbabilityMeasure (fallback i)] (i : Nat) :
    IsMarkovKernel (hybridRadiusFourWarmFallbackKernel hn K hK N s0 hN hs0
      steps retries fallback i) := by
  unfold hybridRadiusFourWarmFallbackKernel
  infer_instance

noncomputable def hybridRadiusFourWarmFallbackCostedKernel
    (hn : 1 <= n) (K : Set (State n)) (hK : MeasurableSet K)
    (N s0 : Real) (hN : 0 < N) (hs0 : 0 < s0)
    (steps : Nat -> Nat -> Nat) (retries : Nat -> Nat)
    (fallback : Nat -> Measure (ScoreSeed n))
    [forall i, IsProbabilityMeasure (fallback i)] :
    Nat -> Kernel (State n) (ENNReal × ScoreSeed n) := fun i =>
  gaussianWarmFallbackCostedPhaseKernel
    (hybridRadiusFourBody n N s0 K i)
    (measurableSet_fixedRadiusFourBody hK _)
    (hybridRadiusFourDelta n N s0 i)
    (sigmaSq n N s0 i)
    (1 - 1 / (2 * (n : Real)))
    (fixedRadiusFourDelta_pos hn (sigmaSq_pos hn hN hs0 i))
    (by
      have hnR : (1 : Real) <= n := by exact_mod_cast hn
      have hhalf : 1 / (2 * (n : Real)) <= 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      linarith)
    (steps i) (retries i) (fallback i)

instance hybridRadiusFourWarmFallbackCostedKernel.isMarkovKernel
    (hn : 1 <= n) (K : Set (State n)) (hK : MeasurableSet K)
    (N s0 : Real) (hN : 0 < N) (hs0 : 0 < s0)
    (steps : Nat -> Nat -> Nat) (retries : Nat -> Nat)
    (fallback : Nat -> Measure (ScoreSeed n))
    [forall i, IsProbabilityMeasure (fallback i)] (i : Nat) :
    IsMarkovKernel (hybridRadiusFourWarmFallbackCostedKernel hn K hK N s0 hN hs0
      steps retries fallback i) := by
  unfold hybridRadiusFourWarmFallbackCostedKernel
  infer_instance

theorem map_snd_hybridRadiusFourWarmFallbackCostedKernel
    (hn : 1 <= n) (K : Set (State n)) (hK : MeasurableSet K)
    (N s0 : Real) (hN : 0 < N) (hs0 : 0 < s0)
    (steps : Nat -> Nat -> Nat) (retries : Nat -> Nat)
    (fallback : Nat -> Measure (ScoreSeed n))
    [forall i, IsProbabilityMeasure (fallback i)] (i : Nat) (x : State n) :
    Measure.map Prod.snd
        (hybridRadiusFourWarmFallbackCostedKernel hn K hK N s0 hN hs0
          steps retries fallback i x) =
      hybridRadiusFourWarmFallbackKernel hn K hK N s0 hN hs0
        steps retries fallback i x := by
  exact map_snd_gaussianWarmFallbackCostedPhaseKernel
    (measurableSet_fixedRadiusFourBody hK _)
    (hybridRadiusFourDelta n N s0 i) (sigmaSq n N s0 i)
    (1 - 1 / (2 * (n : Real)))
    (fixedRadiusFourDelta_pos hn (sigmaSq_pos hn hN hs0 i))
    (by
      have hnR : (1 : Real) <= n := by exact_mod_cast hn
      have hhalf : 1 / (2 * (n : Real)) <= 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      linarith)
    (steps i) (retries i) (fallback i) x

#print axioms map_snd_hybridRadiusFourWarmFallbackCostedKernel

end Ttc.CVHybridRadiusFourFallbackSchedule
