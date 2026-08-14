import Ttc.Exec.CVWarmBudgetRecurrence
import Ttc.Exec.CVGaussianWarmFallbackCappedOperational

/-!
# Capped operational paths with an internal recursive warm budget

This adapter removes the free `warmBudget`/`hgrowth` pair from the active-tail
operational constructor.  The actual-path warmness is the literal recurrence

`M (i+1) = acceptedFactor i * M i + fallbackFactor i`.

It may grow geometrically, but `CVWarmBudgetRecurrence` proves that its logarithm is an
additive phase sum.  Expected query cost is accounted on the separate retained
reference and therefore does not acquire this actual-path multiplier.
-/

set_option autoImplicit false

namespace Ttc.CVRecursiveWarmOperational

open MeasureTheory ProbabilityTheory
open Arlib Arlib.Probability Arlib.MarkovChains
open Arlib.GaussianCooling
open Ttc.CVCorrected
open Ttc.CVSequentialPhaseSampler
open Ttc.CVSeedProjectedDependence
open Ttc.CVFiniteAugmentedSeedOperational
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVIndependentStreamDependence
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVWarmBudgetRecurrence
open scoped ENNReal Classical

variable {Score Seed : Type*} [MeasurableSpace Score] [MeasurableSpace Seed]

/-- Active-tail scalar operation with the actual warmness recurrence fixed internally.
The only transition premise is the honest phase theorem at that exact recursively
computed warmness. -/
noncomputable def seedProjectedOperational_activeReferenceTail_recursiveWarm
    (m : Nat) (Q : Nat → Kernel Seed (Score × Seed)) [∀ i, IsMarkovKernel (Q i)]
    (tail : Nat → Measure (Score × Seed)) [∀ i, IsProbabilityMeasure (tail i)]
    (mu0 : Measure (Score × Seed)) [IsProbabilityMeasure mu0]
    (V : Nat → (Nat → Score × Seed) → Real) (eta : Real)
    (pi : Nat → Measure Seed) (tau : Nat → Measure (Score × Seed))
    [∀ i, IsProbabilityMeasure (tau i)]
    (initialWarm : ENNReal) (acceptedFactor fallbackFactor mixError : Nat → ENNReal)
    (hinitialOne : 1 ≤ initialWarm)
    (hacceptedOne : ∀ i, 1 ≤ acceptedFactor i)
    (hstart : IsWarm initialWarm (Measure.map Prod.snd mu0) (pi 0))
    (hactiveStep : ∀ i, i + 1 < m → ∀ (rho : Measure Seed),
      IsProbabilityMeasure rho →
      IsWarm (recursiveWarmBudget initialWarm acceptedFactor fallbackFactor i)
        rho (pi i) →
      IsWarm
        (acceptedFactor i *
            recursiveWarmBudget initialWarm acceptedFactor fallbackFactor i +
          fallbackFactor i)
        (Measure.map Prod.snd (sampleFromKernel (Q i) rho)) (pi (i + 1)))
    (htailSeed : ∀ i, Measure.map Prod.snd (tail i) = pi i)
    (hactiveMixTop : ∀ i, i + 1 < m → mixError i ≠ ⊤)
    (hactiveMix : ∀ i, i + 1 < m → ∀ (rho : Measure Seed),
      IsWarm
          (2 * recursiveWarmBudget initialWarm acceptedFactor fallbackFactor i)
          rho (pi i) →
      IsProbabilityMeasure rho →
      TVLe (sampleFromKernel (Q i) rho) (tau i) (mixError i))
    (u : (i : Nat) → (Finset.Iic i → Score × Seed) → Real)
    (v : Nat → Score → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i,
      accuracyU
          (inhomogeneousPathMeasure
            (stateScheduleFromSeed (activeReferenceTailSchedule m Q tail)) mu0)
          V (correctedAlpha m eta) i =
        fun omega ↦ u i (Preorder.frestrictLe i omega))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (omega (i + 1)).1)
    (hbudget : ∀ i, i + 1 < m →
      2 * (mixError i).toReal ≤ correctedNu m eta) :
    SeedProjectedOperational
      (stateScheduleFromSeed (activeReferenceTailSchedule m Q tail))
      (activeReferenceTailSchedule m Q tail)
      Prod.snd Prod.fst mu0 V m eta := by
  let warmBudget := recursiveWarmBudget initialWarm acceptedFactor fallbackFactor
  apply seedProjectedOperational_activeReferenceTail m Q tail mu0 V eta pi tau
    warmBudget mixError
  · intro i
    exact one_le_recursiveWarmBudget hinitialOne hacceptedOne i
  · simpa only [warmBudget, recursiveWarmBudget_zero] using hstart
  · intro i hi rho hprob hwarm
    simpa only [warmBudget, recursiveWarmBudget_succ] using
      hactiveStep i hi rho hprob hwarm
  · exact htailSeed
  · exact hactiveMixTop
  · exact hactiveMix
  · exact hu
  · exact hv
  · exact hU
  · exact hV
  · exact hbudget

#print axioms seedProjectedOperational_activeReferenceTail_recursiveWarm

end Ttc.CVRecursiveWarmOperational
