import Ttc.Exec.CVHybridRadiusQSwitchWarm
import Ttc.Exec.CVHybridRadiusQRecursiveOperational

/-! Recursive operational assembly using the geometric switch-aware warm factor. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Ttc.CVHybridRadiusQSwitchedRecursiveOperational

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVCorrected Ttc.CVHybridSchedule Ttc.CVSequentialPhaseSampler
open Ttc.CVSeedProjectedDependence Ttc.CVScoreSeedPhaseKernel
open Ttc.CVRecursiveWarmOperational Ttc.CVWarmBudgetRecurrence
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVHybridRadiusQRecursiveStep
open Ttc.CVHybridRadiusQSwitchWarm
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

noncomputable def hybridRadiusQSwitchedWarmBudget
    (initialWarm : ENNReal) (n : Nat) (q N s0 : Real) (K : Set (State n))
    (retries : Nat → Nat) : Nat → ENNReal :=
  recursiveWarmBudget initialWarm
    (hybridRadiusQSwitchedAcceptedFactor n q N s0 K retries)
    (hybridRadiusQFallbackFactor n q N s0 K)

/-- The recursive SeedProjected certificate with the switch-aware budget.  Its
operational kernel and phase target are definitionally the same as the existing
all-radius-q certificate; only the deadline warmth budget is sharpened. -/
noncomputable def seedProjectedOperational_hybridRadiusQ_switched_recursive
    (hn : 1 ≤ n) (m : Nat) {q N s0 : Real} (hq : 0 < q)
    (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hrate0 : ∀ i, i + 1 < m → 0 ≤ phaseRate n N s0 i)
    (hrad : ∀ i, i < m →
      1 ≤ q * Real.sqrt (sigmaSq n N s0 i) * Real.sqrt n)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat) (scoreScale : Real)
    (tail : Nat → Measure (ScoreSeed n)) [∀ i, IsProbabilityMeasure (tail i)]
    (mu0 : Measure (ScoreSeed n)) [IsProbabilityMeasure mu0]
    (V : Nat → (Nat → ScoreSeed n) → Real) (eta : Real)
    (tau : Nat → Measure (ScoreSeed n)) [∀ i, IsProbabilityMeasure (tau i)]
    (initialWarm : ENNReal) (hinitialOne : 1 ≤ initialWarm)
    (hstart : IsWarm initialWarm (Measure.map Prod.snd mu0)
      (hybridRadiusQSeedTarget n q N s0 K 0))
    (htailSeed : ∀ i, Measure.map Prod.snd (tail i) =
      hybridRadiusQSeedTarget n q N s0 K i)
    (mixError : Nat → ENNReal)
    (hactiveMixTop : ∀ i, i + 1 < m → mixError i ≠ ⊤)
    (hactiveMix : ∀ i, i + 1 < m → ∀ (rho : Measure (State n)),
      IsWarm
          (2 * hybridRadiusQSwitchedWarmBudget initialWarm n q N s0 K retries i)
          rho (hybridRadiusQSeedTarget n q N s0 K i) →
      IsProbabilityMeasure rho →
      TVLe (sampleFromKernel
        (sourceHybridRadiusQWarmFallbackSchedule hn q hq hN hs0 K hK
          steps retries scoreScale i) rho) (tau i) (mixError i))
    (u : (i : Nat) → (Finset.Iic i → ScoreSeed n) → Real)
    (v : Nat → State n → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i,
      accuracyU
          (inhomogeneousPathMeasure
            (stateScheduleFromSeed
              (activeReferenceTailSchedule m
                (sourceHybridRadiusQWarmFallbackSchedule hn q hq hN hs0 K hK
                  steps retries scoreScale) tail)) mu0)
          V (correctedAlpha m eta) i =
        fun omega ↦ u i (Preorder.frestrictLe i omega))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (omega (i + 1)).1)
    (hbudget : ∀ i, i + 1 < m →
      2 * (mixError i).toReal ≤ correctedNu m eta) :
    SeedProjectedOperational
      (stateScheduleFromSeed
        (activeReferenceTailSchedule m
          (sourceHybridRadiusQWarmFallbackSchedule hn q hq hN hs0 K hK
            steps retries scoreScale) tail))
      (activeReferenceTailSchedule m
        (sourceHybridRadiusQWarmFallbackSchedule hn q hq hN hs0 K hK
          steps retries scoreScale) tail)
      Prod.snd Prod.fst mu0 V m eta := by
  apply seedProjectedOperational_activeReferenceTail_recursiveWarm
    m (sourceHybridRadiusQWarmFallbackSchedule hn q hq hN hs0 K hK
      steps retries scoreScale) tail mu0 V eta
    (hybridRadiusQSeedTarget n q N s0 K) tau initialWarm
    (hybridRadiusQSwitchedAcceptedFactor n q N s0 K retries)
    (hybridRadiusQFallbackFactor n q N s0 K) mixError hinitialOne
    (one_le_hybridRadiusQSwitchedAcceptedFactor n q N s0 K retries) hstart
  · intro i hi rho hprob hwarm
    letI : IsProbabilityMeasure rho := hprob
    exact isWarm_seed_hybridRadiusQWarmFallbackKernel_switched_step
      hn hq hN hs0 hK hKc hball hfin steps retries scoreScale hi
      (hrate0 i hi) (hrad i (Nat.lt_of_succ_lt hi)) (hrad (i + 1) hi) rho hwarm
  · exact htailSeed
  · exact hactiveMixTop
  · simpa only [hybridRadiusQSwitchedWarmBudget] using hactiveMix
  · exact hu
  · exact hv
  · exact hU
  · exact hV
  · exact hbudget

#print axioms seedProjectedOperational_hybridRadiusQ_switched_recursive

end Ttc.CVHybridRadiusQSwitchedRecursiveOperational
