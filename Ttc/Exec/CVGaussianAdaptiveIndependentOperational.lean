import Ttc.Exec.CVGaussianAdaptiveBlockOperational

/-! Independent-stream lift of the concrete adaptive block error budget. -/

namespace Ttc.CVGaussianAdaptiveIndependentOperational

open MeasureTheory ProbabilityTheory
open Arlib Arlib.Probability Arlib.GaussianCooling
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVSeedProjectedDependence
open Ttc.CVIndependentStreamDependence
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVGaussianBlockRetryParameters
open Ttc.CVContinuingRetryParameters
open scoped ENNReal Classical

variable {Score Seed : Type*} [MeasurableSpace Score] [MeasurableSpace Seed]

/-- The k-scaled block parameter discharges the independent-coordinate dependence
budget.  The sole equality records that the scalar operation uses the capped block error
on active phases and exact zero error on its reference tail. -/
noncomputable def independentStreamOperational_of_adaptiveBlock
    {k m : Nat} {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {Q : Nat → Kernel Seed (Score × Seed)} [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (Score × Seed)} [IsProbabilityMeasure mu0]
    {Vscalar : Nat → (Nat → Score × Seed) → Real}
    (hop : SeedProjectedOperational (stateScheduleFromSeed Q) Q Prod.snd Prod.fst
      mu0 Vscalar m eps)
    (hmixError : ∀ i, hop.mixError i =
      activeReferenceMixError m (fun _ ↦ blockMixError m k eps) i)
    (V : Nat → (Fin k → Nat → Score × Seed) → Real)
    (u : (i : Nat) → (Fin k → Finset.Iic i → Score × Seed) → Real)
    (v : Nat → (Fin k → Score × Seed) → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i,
      accuracyU (independentPathLaw k (stateScheduleFromSeed Q) mu0) V
          (Ttc.CVCorrected.correctedAlpha m eps) i =
        fun omega ↦ u i (fun l ↦ Preorder.frestrictLe i (omega l)))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (fun l ↦ omega l (i + 1))) :
    IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd mu0 V m eps := by
  apply independentStreamOperational_of_seedProjected hop V u v hu hv hU hV
  intro i
  rw [hmixError i]
  unfold activeReferenceMixError
  by_cases hi : i + 1 < m
  · simp only [if_pos hi]
    exact blockMixError_budget heps heps1
  · simp only [if_neg hi, ENNReal.toReal_zero, mul_zero]
    exact (correctedNu_pos (m := m) heps).le

#print axioms independentStreamOperational_of_adaptiveBlock

end Ttc.CVGaussianAdaptiveIndependentOperational
