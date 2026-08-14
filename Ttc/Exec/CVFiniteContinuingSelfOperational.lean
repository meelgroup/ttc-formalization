import Ttc.Exec.CVFiniteContinuingSelfSchedule

/-! Operational warm/dependence closure for the self-fallback Gaussian phase schedule. -/

namespace Ttc.CVFiniteContinuingSelfOperational

open MeasureTheory ProbabilityTheory Set
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler
open Ttc.CVDirectSequentialAccuracy
open Ttc.CVCorrected
open Ttc.CVFiniteContinuingSelfSchedule
open Ttc.FiniteContinuingRetrySelfDecomposition
open scoped ENNReal Classical Pointwise

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- One phase maps the declared current warm budget to the declared next warm budget.
The only Gaussian-specific analytic premise is warmth of each unnormalised accepted
first-hit increment; the unresolved self tail is handled automatically. -/
theorem isWarm_selfRetryStateSchedule_of_firstHitBudget
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (pi : Nat → Measure (State n))
    (warmBudget adjacentWarm firstHitFactor : Nat → ENNReal)
    (hadj : ∀ i, IsWarm (adjacentWarm i) (pi i) (pi (i + 1)))
    (hfirstHit : ∀ i (rho : Measure (State n)), IsProbabilityMeasure rho →
      IsWarm (warmBudget i * adjacentWarm i) rho (pi (i + 1)) →
      ∀ j : Fin (retries i),
        IsWarm (firstHitFactor i * (warmBudget i * adjacentWarm i))
          (firstHitIncrement
            (fun q ↦ Ttc.FiniteContinuingRetryGaussian.combinedRoundCostedKernel
              K hK (delta i) (sigmaSq i) (hdelta i) (retrySteps i q))
            (Ttc.FiniteContinuingRetryGaussian.costedCombinedAccept K
              (shrink i) (sigmaSq i))
            (Ttc.FiniteContinuingRetryGaussian.measurableSet_costedCombinedAccept hK
              (hshrink i))
            Ttc.FiniteContinuingRetryGaussian.rejectedNext
            (Ttc.FiniteContinuingRetryGaussian.acceptedOutput (shrink i))
            Ttc.FiniteContinuingRetryGaussian.measurable_rejectedNext
            (Ttc.FiniteContinuingRetryGaussian.measurable_acceptedOutput (shrink i))
            Ttc.FiniteContinuingRetryGaussian.roundQueryCost
            Ttc.FiniteContinuingRetryGaussian.measurable_roundQueryCost rho j)
          (pi (i + 1)))
    (hgrowth : ∀ i,
      (retries i : ENNReal) *
          (firstHitFactor i * (warmBudget i * adjacentWarm i)) +
        warmBudget i * adjacentWarm i ≤ warmBudget (i + 1))
    (i : Nat) (rho : Measure (State n)) [IsProbabilityMeasure rho]
    (hrho : IsWarm (warmBudget i) rho (pi i)) :
    IsWarm (warmBudget (i + 1))
      (sampleFromKernel
        (selfRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink
          retrySteps retries i) rho) (pi (i + 1)) := by
  have hrhoNext : IsWarm (warmBudget i * adjacentWarm i) rho (pi (i + 1)) :=
    hrho.trans (hadj i)
  exact (isWarm_sampleFrom_selfRetryStateSchedule_of_firstHit K hK delta sigmaSq shrink
    hdelta hshrink retrySteps retries rho (pi (i + 1)) i hrhoNext
    (hfirstHit i rho inferInstance hrhoNext)).mono (hgrowth i)

/-- Fully assembled corrected-dependence package.  The surviving binders are local
first-hit domination, adjacent Gaussian comparison, distributional phase mixing, and the
scalar warm-budget recurrence. -/
noncomputable def directSequentialOperational_of_selfRetryFirstHit
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (mu0 : Measure (State n)) [IsProbabilityMeasure mu0]
    (V : Nat → (Nat → State n) → Real) (m : Nat) (eta : Real)
    (pi tau : Nat → Measure (State n))
    [∀ i, IsProbabilityMeasure (pi i)] [∀ i, IsProbabilityMeasure (tau i)]
    (warmBudget adjacentWarm firstHitFactor mixError : Nat → ENNReal)
    (hstart : IsWarm (warmBudget 0) mu0 (pi 0))
    (hadj : ∀ i, IsWarm (adjacentWarm i) (pi i) (pi (i + 1)))
    (hfirstHit : ∀ i (rho : Measure (State n)), IsProbabilityMeasure rho →
      IsWarm (warmBudget i * adjacentWarm i) rho (pi (i + 1)) →
      ∀ j : Fin (retries i),
        IsWarm (firstHitFactor i * (warmBudget i * adjacentWarm i))
          (firstHitIncrement
            (fun q ↦ Ttc.FiniteContinuingRetryGaussian.combinedRoundCostedKernel
              K hK (delta i) (sigmaSq i) (hdelta i) (retrySteps i q))
            (Ttc.FiniteContinuingRetryGaussian.costedCombinedAccept K
              (shrink i) (sigmaSq i))
            (Ttc.FiniteContinuingRetryGaussian.measurableSet_costedCombinedAccept hK
              (hshrink i))
            Ttc.FiniteContinuingRetryGaussian.rejectedNext
            (Ttc.FiniteContinuingRetryGaussian.acceptedOutput (shrink i))
            Ttc.FiniteContinuingRetryGaussian.measurable_rejectedNext
            (Ttc.FiniteContinuingRetryGaussian.measurable_acceptedOutput (shrink i))
            Ttc.FiniteContinuingRetryGaussian.roundQueryCost
            Ttc.FiniteContinuingRetryGaussian.measurable_roundQueryCost rho j)
          (pi (i + 1)))
    (hgrowth : ∀ i,
      (retries i : ENNReal) *
          (firstHitFactor i * (warmBudget i * adjacentWarm i)) +
        warmBudget i * adjacentWarm i ≤ warmBudget (i + 1))
    (hmix_top : ∀ i, mixError i ≠ ⊤)
    (hmix : ∀ i (rho : Measure (State n)),
      IsWarm (2 * warmBudget i) rho (pi i) → IsProbabilityMeasure rho →
        TVLe (sampleFromKernel
          (selfRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink
            retrySteps retries i) rho) (tau i) (mixError i))
    (u : (i : Nat) → (Finset.Iic i → State n) → Real)
    (v : Nat → State n → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i,
      accuracyU
          (inhomogeneousPathMeasure
            (selfRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink
              retrySteps retries) mu0)
          V (Ttc.CVCorrected.correctedAlpha m eta) i =
        fun omega ↦ u i (Preorder.frestrictLe i omega))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (omega (i + 1)))
    (hbudget : ∀ i, 2 * (mixError i).toReal ≤ Ttc.CVCorrected.correctedNu m eta) :
    DirectSequentialOperational
      (selfRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink retrySteps retries)
      mu0 V m eta :=
  selfRetryDirectSequentialOperational_of_budgetRecurrence K hK delta sigmaSq shrink
    hdelta hshrink retrySteps retries mu0 V m eta pi tau warmBudget mixError hstart
    (fun i rho _hrho hprob ↦ by
      letI : IsProbabilityMeasure rho := hprob
      exact isWarm_selfRetryStateSchedule_of_firstHitBudget K hK delta sigmaSq shrink hdelta
        hshrink retrySteps retries pi warmBudget adjacentWarm firstHitFactor hadj hfirstHit
        hgrowth i rho _hrho)
    hmix_top hmix u v hu hv hU hV hbudget

#print axioms isWarm_selfRetryStateSchedule_of_firstHitBudget
#print axioms directSequentialOperational_of_selfRetryFirstHit

end Ttc.CVFiniteContinuingSelfOperational
