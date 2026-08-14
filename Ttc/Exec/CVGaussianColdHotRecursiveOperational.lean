import Ttc.Exec.CVGaussianColdHotRecursiveStep
import Ttc.Exec.CVRecursiveWarmOperational

/-! # Seed-projected operation for the literal recursive cold/hot sampler -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Ttc.CVGaussianColdHotRecursiveOperational

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVCorrected
open Ttc.CVHybridSchedule
open Ttc.CVSequentialPhaseSampler
open Ttc.CVSeedProjectedDependence
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVGaussianColdHotRecursiveStep
open Ttc.CVRecursiveWarmOperational
open Ttc.CVWarmBudgetRecurrence
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVIndependentStreamDependence
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- The caller supplies only the ordinary selective-TV mixing statement and the
statistic decomposition.  The entire changing-body/full-body seed-warm recurrence is
constructed by `isWarm_seed_coldHotWarmFallbackSchedule_step`. -/
noncomputable def seedProjectedOperational_gaussianColdHot_recursive
    (hn : 1 ≤ n) (m : Nat) {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {radius : Real} (hradius : 0 < radius)
    (hradiusShrink : radius < 1 - 1 / (2 * (n : Real)))
    (hcoldStart : 4 * (n : Real) * s0 ≤ radius ^ 2)
    (hrad : ∀ j, j < coldPhases n s0 →
      1 ≤ 4 * Real.sqrt (Ttc.CVCorrectedFixedBlockCost.fixedSigmaSq n s0 j) * Real.sqrt n)
    (hradTwo : ∀ j, j ≤ coldPhases n s0 →
      1 ≤ 2 * Real.sqrt (Ttc.CVCorrectedFixedBlockCost.fixedSigmaSq n s0 j) * Real.sqrt n)
    (coldSteps hotSteps : Nat → Nat → Nat)
    (coldRetries hotRetries : Nat → Nat) (scoreScale : Real)
    (tail : Nat → Measure (ScoreSeed n)) [∀ i, IsProbabilityMeasure (tail i)]
    (mu0 : Measure (ScoreSeed n)) [IsProbabilityMeasure mu0]
    (V : Nat → (Nat → ScoreSeed n) → Real) (eta : Real)
    (tau : Nat → Measure (ScoreSeed n)) [∀ i, IsProbabilityMeasure (tau i)]
    (initialWarm : ENNReal) (hinitialOne : 1 ≤ initialWarm)
    (hstart : IsWarm initialWarm (Measure.map Prod.snd mu0)
      (coldHotSeedTarget n N s0 K 0))
    (htailSeed : ∀ i, Measure.map Prod.snd (tail i) =
      coldHotSeedTarget n N s0 K i)
    (mixError : Nat → ENNReal)
    (hactiveMixTop : ∀ i, i + 1 < m → mixError i ≠ ⊤)
    (hactiveMix : ∀ i, i + 1 < m → ∀ (rho : Measure (State n)),
      IsWarm
          (2 * recursiveWarmBudget initialWarm
            (coldHotAcceptedFactor n N s0 (coldPhases n s0)
              coldRetries hotRetries)
            (coldHotFallbackFactor n N s0 (coldPhases n s0) K) i)
          rho (coldHotSeedTarget n N s0 K i) →
      IsProbabilityMeasure rho →
      TVLe (sampleFromKernel
        (sourceColdHotWarmFallbackSchedule hn hN hs0 K hK hradius
          coldSteps hotSteps coldRetries hotRetries scoreScale i) rho)
        (tau i) (mixError i))
    (u : (i : Nat) → (Finset.Iic i → ScoreSeed n) → Real)
    (v : Nat → State n → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i,
      accuracyU
          (inhomogeneousPathMeasure
            (stateScheduleFromSeed
              (activeReferenceTailSchedule m
                (sourceColdHotWarmFallbackSchedule hn hN hs0 K hK hradius
                  coldSteps hotSteps coldRetries hotRetries scoreScale) tail)) mu0)
          V (correctedAlpha m eta) i =
        fun omega ↦ u i (Preorder.frestrictLe i omega))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (omega (i + 1)).1)
    (hbudget : ∀ i, i + 1 < m →
      2 * (mixError i).toReal ≤ correctedNu m eta) :
    SeedProjectedOperational
      (stateScheduleFromSeed
        (activeReferenceTailSchedule m
          (sourceColdHotWarmFallbackSchedule hn hN hs0 K hK hradius
            coldSteps hotSteps coldRetries hotRetries scoreScale) tail))
      (activeReferenceTailSchedule m
        (sourceColdHotWarmFallbackSchedule hn hN hs0 K hK hradius
          coldSteps hotSteps coldRetries hotRetries scoreScale) tail)
      Prod.snd Prod.fst mu0 V m eta := by
  letI : ∀ j, IsProbabilityMeasure
      (coldFallback n scoreScale s0 radius j) :=
    fun j ↦ isProbabilityMeasure_coldFallback n scoreScale hs0 hradius j
  letI : ∀ j, IsProbabilityMeasure
      (hotFallback n N s0 scoreScale j) :=
    fun j ↦ isProbabilityMeasure_hotFallback hn hN hs0 scoreScale j
  apply seedProjectedOperational_activeReferenceTail_recursiveWarm
    m (sourceColdHotWarmFallbackSchedule hn hN hs0 K hK hradius
      coldSteps hotSteps coldRetries hotRetries scoreScale)
    tail mu0 V eta (coldHotSeedTarget n N s0 K) tau initialWarm
    (coldHotAcceptedFactor n N s0 (coldPhases n s0) coldRetries hotRetries)
    (coldHotFallbackFactor n N s0 (coldPhases n s0) K) mixError
    hinitialOne
    (one_le_coldHotAcceptedFactor n N s0 (coldPhases n s0)
      coldRetries hotRetries)
    hstart
  · intro i hi rho hprob hwarm
    letI : IsProbabilityMeasure rho := hprob
    simpa only [sourceColdHotWarmFallbackSchedule, coldHotFallbackFactor] using
      (isWarm_seed_coldHotWarmFallbackSchedule_step
        (m := m) hn hN hs0 hK hKc hball hfin hradius hradiusShrink
        hcoldStart hrad hradTwo coldSteps hotSteps coldRetries hotRetries
        scoreScale hi rho hwarm)
  · exact htailSeed
  · exact hactiveMixTop
  · exact hactiveMix
  · exact hu
  · exact hv
  · exact hU
  · exact hV
  · exact hbudget

/-- Block lift of the recursive scalar operation.  All `k` streams are independent
complete executions; the remaining premises are only the block statistic identities
and the strengthened `k`-scaled dependence share. -/
noncomputable def independentStreamOperational_gaussianColdHot_recursive
    {k m : Nat} {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (ScoreSeed n)} [IsProbabilityMeasure mu0]
    {Vscalar : Nat → (Nat → ScoreSeed n) → Real} {eta : Real}
    (hop : SeedProjectedOperational (stateScheduleFromSeed Q) Q Prod.snd Prod.fst
      mu0 Vscalar m eta)
    (V : Nat → (Fin k → Nat → ScoreSeed n) → Real)
    (u : (i : Nat) → (Fin k → Finset.Iic i → ScoreSeed n) → Real)
    (v : Nat → (Fin k → ScoreSeed n) → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i,
      accuracyU (independentPathLaw k (stateScheduleFromSeed Q) mu0) V
          (correctedAlpha m eta) i =
        fun omega ↦ u i (fun l ↦ Preorder.frestrictLe i (omega l)))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (fun l ↦ omega l (i + 1)))
    (hbudget : ∀ i,
      (k : Real) * (2 * (hop.mixError i).toReal) ≤ correctedNu m eta) :
    Ttc.CVIndependentStreamDependence.IndependentStreamOperational k
      (stateScheduleFromSeed Q) Q Prod.snd mu0 V m eta :=
  independentStreamOperational_of_seedProjected hop V u v hu hv hU hV hbudget

#print axioms seedProjectedOperational_gaussianColdHot_recursive
#print axioms independentStreamOperational_gaussianColdHot_recursive

end Ttc.CVGaussianColdHotRecursiveOperational
