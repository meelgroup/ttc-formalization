import Ttc.Exec.CVGaussianScoreSeedPhaseKernel
import Ttc.Volume.CVExceptionalDependence

/-!
# Noncompounding good-path transfer for augmented Gaussian phases

The finite operational schedule may return a fallback pair, whose seed need not be warm.
Dependence and moment estimates are therefore proved for an autonomous ideal augmented
path.  A single coupling event says that every operational phase succeeds and its score
agrees with the ideal score.  The complement of this event is charged once, after the
complete product estimate, rather than once per dependence inequality.
-/

namespace Ttc.CVAugmentedGoodPathAccuracy

open MeasureTheory ProbabilityTheory Set
open Arlib Arlib.GaussianCooling
open Ttc.CVCorrected
open scoped ENNReal Classical

variable {Actual Ideal : Type*}
  [MeasurableSpace Actual] [MeasurableSpace Ideal]

/-- A coupling of an operational law and an autonomous ideal law, together with one
global successful-execution event. -/
structure GoodPathCoupling (muActual : Measure Actual) (muIdeal : Measure Ideal) where
  coupling : Measure (Actual × Ideal)
  coupling_prob : IsProbabilityMeasure coupling
  actual_marginal : Measure.map Prod.fst coupling = muActual
  ideal_marginal : Measure.map Prod.snd coupling = muIdeal
  good : Set (Actual × Ideal)
  measurable_good : MeasurableSet good

attribute [instance] GoodPathCoupling.coupling_prob

/-- A one-line set transfer under a good-path coupling.  The exceptional mass is paid
exactly once, independently of the number of phases. -/
theorem measureReal_le_of_goodPathCoupling
    {muActual : Measure Actual} {muIdeal : Measure Ideal}
    (C : GoodPathCoupling muActual muIdeal)
    {A : Set Actual} {B : Set Ideal} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {delta : Real} (hfail : C.coupling.real C.goodᶜ ≤ delta)
    (htransfer : ∀ z ∈ C.good, z.1 ∈ A → z.2 ∈ B) :
    muActual.real A ≤ muIdeal.real B + delta := by
  have hsub : Prod.fst ⁻¹' A ⊆ Prod.snd ⁻¹' B ∪ C.goodᶜ := by
    intro z hz
    by_cases hg : z ∈ C.good
    · exact Or.inl (htransfer z hg hz)
    · exact Or.inr hg
  calc
    muActual.real A = (Measure.map Prod.fst C.coupling).real A := by
      rw [C.actual_marginal]
    _ = C.coupling.real (Prod.fst ⁻¹' A) := by
      have hmap : (Measure.map Prod.fst C.coupling) A =
          C.coupling (Prod.fst ⁻¹' A) := Measure.map_apply measurable_fst hA
      exact congrArg ENNReal.toReal hmap
    _ ≤ C.coupling.real (Prod.snd ⁻¹' B ∪ C.goodᶜ) :=
      measureReal_mono hsub (measure_ne_top C.coupling _)
    _ ≤ C.coupling.real (Prod.snd ⁻¹' B) + C.coupling.real C.goodᶜ :=
      measureReal_union_le _ _
    _ ≤ C.coupling.real (Prod.snd ⁻¹' B) + delta := by gcongr
    _ = (Measure.map Prod.snd C.coupling).real B + delta := by
      have hmap : (Measure.map Prod.snd C.coupling) B =
          C.coupling (Prod.snd ⁻¹' B) := Measure.map_apply measurable_snd hB
      congr 1
      exact (congrArg ENNReal.toReal hmap).symm
    _ = muIdeal.real B + delta := by rw [C.ideal_marginal]

variable {X : Type*} [MeasurableSpace X]

/-- Transfer a complete phase-product accuracy theorem from the autonomous ideal path
to the finite operational path.  The successful event may include every retry cutoff,
query cutoff, and score-equality coupling simultaneously. -/
theorem phaseProduct_failure_le_of_goodPathCoupling
    {muActual muIdeal : Measure (Nat → X)}
    (C : GoodPathCoupling muActual muIdeal)
    (WActual WIdeal : Nat → (Nat → X) → Real)
    (hWActual : ∀ j, Measurable (WActual j))
    (hWIdeal : ∀ j, Measurable (WIdeal j))
    (m : Nat) (target eps : Real) {idealFailure exceptionalFailure : Real}
    (hideal : muIdeal.real
      {ω | phaseProduct WIdeal m ω ∉ Ttc.relErr eps target} ≤ idealFailure)
    (hfail : C.coupling.real C.goodᶜ ≤ exceptionalFailure)
    (hagrees : ∀ z ∈ C.good,
      phaseProduct WActual m z.1 = phaseProduct WIdeal m z.2) :
    muActual.real {ω | phaseProduct WActual m ω ∉ Ttc.relErr eps target} ≤
      idealFailure + exceptionalFailure := by
  let A : Set (Nat → X) :=
    {ω | phaseProduct WActual m ω ∉ Ttc.relErr eps target}
  let B : Set (Nat → X) :=
    {ω | phaseProduct WIdeal m ω ∉ Ttc.relErr eps target}
  have hmA : Measurable (phaseProduct WActual m) := by
    unfold phaseProduct
    fun_prop
  have hmB : Measurable (phaseProduct WIdeal m) := by
    unfold phaseProduct
    fun_prop
  have hA : MeasurableSet A := measurableSet_Icc.compl.preimage hmA
  have hB : MeasurableSet B := measurableSet_Icc.compl.preimage hmB
  have hmain := measureReal_le_of_goodPathCoupling C hA hB hfail (fun z hz hza ↦ by
    change phaseProduct WActual m z.1 ∉ Ttc.relErr eps target at hza
    change phaseProduct WIdeal m z.2 ∉ Ttc.relErr eps target
    rwa [← hagrees z hz])
  change muActual.real A ≤ idealFailure + exceptionalFailure
  change muIdeal.real B ≤ idealFailure at hideal
  exact hmain.trans (by linarith)

/-- `4/5` success after one global exceptional charge. -/
theorem four_fifths_of_ideal_goodPathCoupling
    {muActual muIdeal : Measure (Nat → X)} [IsProbabilityMeasure muActual]
    (C : GoodPathCoupling muActual muIdeal)
    (WActual WIdeal : Nat → (Nat → X) → Real)
    (hWActual : ∀ j, Measurable (WActual j))
    (hWIdeal : ∀ j, Measurable (WIdeal j))
    (m : Nat) (target eps : Real) {idealFailure exceptionalFailure : Real}
    (hideal : muIdeal.real
      {ω | phaseProduct WIdeal m ω ∉ Ttc.relErr eps target} ≤ idealFailure)
    (hfail : C.coupling.real C.goodᶜ ≤ exceptionalFailure)
    (hagrees : ∀ z ∈ C.good,
      phaseProduct WActual m z.1 = phaseProduct WIdeal m z.2)
    (hbudget : idealFailure + exceptionalFailure ≤ 1 / 5) :
    4 / 5 ≤ muActual.real
      {ω | phaseProduct WActual m ω ∈ Ttc.relErr eps target} := by
  apply corrected_lem_accuracy_four_fifths WActual hWActual
    (phaseProduct_failure_le_of_goodPathCoupling C WActual WIdeal hWActual hWIdeal
      m target eps hideal hfail hagrees)
  exact hbudget

#print axioms measureReal_le_of_goodPathCoupling
#print axioms phaseProduct_failure_le_of_goodPathCoupling
#print axioms four_fifths_of_ideal_goodPathCoupling

end Ttc.CVAugmentedGoodPathAccuracy
