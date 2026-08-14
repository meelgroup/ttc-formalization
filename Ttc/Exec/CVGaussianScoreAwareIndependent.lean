import Ttc.Exec.CVGaussianScoreAwareOperational
import Ttc.Exec.CVIndependentStreamDependence

/-! Independent-stream lift of the score-aware scalar operation. -/

namespace Ttc.CVGaussianScoreAwareIndependent

open MeasureTheory ProbabilityTheory
open Arlib.GaussianCooling
open Ttc.CVCorrected Ttc.CVAdaptive Ttc.CVScoreSeedPhaseKernel
open Ttc.CVSeedProjectedDependence Ttc.CVIndependentStreamDependence
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVGaussianScoreAwareParameters
open Ttc.CVContinuingRetryParameters
open scoped ENNReal Classical

variable {Score Seed : Type*} [MeasurableSpace Score] [MeasurableSpace Seed]

noncomputable def independentStreamOperational_of_scoreAware
    {k m : Nat} {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {slack boundSq : Nat → Real} (hslack : ∀ i, 0 < slack i)
    (hboundSq : ∀ i, 0 < boundSq i)
    {Q : Nat → Kernel Seed (Score × Seed)} [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (Score × Seed)} [IsProbabilityMeasure mu0]
    {Vscalar : Nat → (Nat → Score × Seed) → Real}
    (hop : SeedProjectedOperational (stateScheduleFromSeed Q) Q Prod.snd Prod.fst
      mu0 Vscalar m eps)
    (hmixError : ∀ i, hop.mixError i = activeReferenceMixError m
      (scoreAwareMixError m k eps slack boundSq) i)
    (V : Nat → (Fin k → Nat → Score × Seed) → Real)
    (u : (i : Nat) → (Fin k → Finset.Iic i → Score × Seed) → Real)
    (v : Nat → (Fin k → Score × Seed) → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i, accuracyU
      (independentPathLaw k (stateScheduleFromSeed Q) mu0) V
        (correctedAlpha m eps) i =
      fun omega ↦ u i (fun l ↦ Preorder.frestrictLe i (omega l)))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (fun l ↦ omega l (i + 1))) :
    IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd mu0 V m eps := by
  apply independentStreamOperational_of_seedProjected hop V u v hu hv hU hV
  intro i
  rw [hmixError i]
  unfold activeReferenceMixError
  by_cases hi : i + 1 < m
  · simp only [if_pos hi]
    exact scoreAwareMixError_budget heps heps1 hslack hboundSq i
  · simp only [if_neg hi, ENNReal.toReal_zero, mul_zero]
    exact (correctedNu_pos (m := m) heps).le

#print axioms independentStreamOperational_of_scoreAware

end Ttc.CVGaussianScoreAwareIndependent
