import Arlib.Probability.TVCoupling
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Ttc.Exec.SequentialCostedPathLumping

/-!
# Cost-preserving reset from a coupling

A coupling of the current-state marginal with an exact target can be lifted through a
regular conditional law of the retained history/cost.  The resulting joint reference law
has the old history/cost marginal, the exact target state marginal, and is no farther in TV
than the coupling failure probability.
-/

namespace Ttc.TVCostPreservingResetLift

open MeasureTheory ProbabilityTheory Set
open Arlib
open scoped ENNReal Classical

variable {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
  [StandardBorelSpace X] [Nonempty X]

/-- A measure whose first and second marginals are the prescribed probability laws. -/
def IsCoupling (kappa : Measure (X × X)) (alpha tau : Measure X) : Prop :=
  Measure.map Prod.fst kappa = alpha ∧ Measure.map Prod.snd kappa = tau

/-- Lift a state coupling while sampling the retained coordinate from the operational
joint law.  The conditional kernel of `kappa` samples the reset state from the old state. -/
noncomputable def resetExtension
    (mu : Measure (A × X)) (kappa : Measure (X × X)) [IsFiniteMeasure kappa] :
    Measure ((A × X) × X) :=
  mu ⊗ₘ Kernel.comap kappa.condKernel Prod.snd measurable_snd

instance resetExtension.instIsProbabilityMeasure
    (mu : Measure (A × X)) [IsProbabilityMeasure mu]
    (kappa : Measure (X × X)) [IsProbabilityMeasure kappa] :
    IsProbabilityMeasure (resetExtension mu kappa) := by
  unfold resetExtension
  infer_instance

/-- Replace the state coordinate and retain the old cost/history coordinate. -/
def resetOutput (z : (A × X) × X) : A × X := (z.1.1, z.2)

/-- The old and reset states carried by the extension. -/
def statePair (z : (A × X) × X) : X × X := (z.1.2, z.2)

theorem measurable_resetOutput : Measurable (resetOutput : ((A × X) × X) → A × X) := by
  exact (measurable_fst.comp measurable_fst).prodMk measurable_snd

theorem measurable_statePair : Measurable (statePair : ((A × X) × X) → X × X) := by
  exact (measurable_snd.comp measurable_fst).prodMk measurable_snd

/-- The extension's `(old state, reset state)` marginal is exactly the supplied coupling. -/
theorem map_statePair_resetExtension
    (mu : Measure (A × X)) [IsProbabilityMeasure mu]
    (kappa : Measure (X × X)) [IsProbabilityMeasure kappa]
    (hfst : Measure.map Prod.fst kappa = Measure.map Prod.snd mu) :
    Measure.map statePair (resetExtension mu kappa) = kappa := by
  let R : Kernel (A × X) X := Kernel.comap kappa.condKernel Prod.snd measurable_snd
  have hmap := Ttc.SequentialCostedPathLumping.map_compProd_prodMap_of_pointwise
    mu R kappa.condKernel measurable_snd measurable_id (fun z ↦ by
      dsimp only [R]
      rw [Kernel.comap_apply, Measure.map_id])
  unfold resetExtension
  change Measure.map (Prod.map Prod.snd id) (mu ⊗ₘ R) = kappa
  rw [hmap, ← hfst]
  exact kappa.disintegrate kappa.condKernel

/-- The operational projection of the extension is its original joint law. -/
theorem map_fst_resetExtension
    (mu : Measure (A × X)) [IsProbabilityMeasure mu]
    (kappa : Measure (X × X)) [IsProbabilityMeasure kappa] :
    Measure.map Prod.fst (resetExtension mu kappa) = mu := by
  unfold resetExtension
  exact Measure.fst_compProd _ _

/-- The reset retains the complete old cost/history marginal. -/
theorem map_fst_map_resetOutput
    (mu : Measure (A × X)) [IsProbabilityMeasure mu]
    (kappa : Measure (X × X)) [IsProbabilityMeasure kappa] :
    Measure.map Prod.fst (Measure.map resetOutput (resetExtension mu kappa)) =
      Measure.map Prod.fst mu := by
  rw [Measure.map_map measurable_fst measurable_resetOutput]
  have hfun : Prod.fst ∘ (resetOutput : ((A × X) × X) → A × X) =
      Prod.fst ∘ Prod.fst := by rfl
  rw [hfun, ← Measure.map_map measurable_fst measurable_fst,
    map_fst_resetExtension mu kappa]

/-- The reset state marginal is the second marginal of the coupling. -/
theorem map_snd_map_resetOutput
    (mu : Measure (A × X)) [IsProbabilityMeasure mu]
    (kappa : Measure (X × X)) [IsProbabilityMeasure kappa]
    (hfst : Measure.map Prod.fst kappa = Measure.map Prod.snd mu) :
    Measure.map Prod.snd (Measure.map resetOutput (resetExtension mu kappa)) =
      Measure.map Prod.snd kappa := by
  have hpair := map_statePair_resetExtension mu kappa hfst
  have h := congrArg (Measure.map Prod.snd) hpair
  rw [Measure.map_map measurable_snd measurable_statePair] at h
  rw [Measure.map_map measurable_snd measurable_resetOutput]
  simpa only [Function.comp_def, resetOutput, statePair] using h

/-- **Cost-preserving coupling lift.**  A marginal coupling failing with probability at
most `eps` produces a full joint reset with the same TV bound. -/
theorem exists_costPreserving_reset_of_coupling
    (mu : Measure (A × X)) [IsProbabilityMeasure mu]
    (tau : Measure X) [IsProbabilityMeasure tau]
    (kappa : Measure (X × X)) [IsProbabilityMeasure kappa]
    {eps : ENNReal} (hcouple : IsCoupling kappa (Measure.map Prod.snd mu) tau)
    (hfail : kappa {p | p.1 ≠ p.2} ≤ eps) :
    ∃ nu : Measure (A × X),
      IsProbabilityMeasure nu ∧
      Measure.map Prod.fst nu = Measure.map Prod.fst mu ∧
      Measure.map Prod.snd nu = tau ∧ TVLe mu nu eps := by
  let omega := resetExtension mu kappa
  let nu := Measure.map resetOutput omega
  haveI : IsProbabilityMeasure omega := by
    dsimp only [omega]
    infer_instance
  haveI : IsProbabilityMeasure nu :=
    Measure.isProbabilityMeasure_map measurable_resetOutput.aemeasurable
  refine ⟨nu, inferInstance, ?_, ?_, ?_⟩
  · exact map_fst_map_resetOutput mu kappa
  · exact (map_snd_map_resetOutput mu kappa hcouple.1).trans hcouple.2
  · have hpair := map_statePair_resetExtension mu kappa hcouple.1
    have hne : omega {z | (z.1 : A × X) ≠ resetOutput z} ≤ eps := by
      have hset : {z | (z.1 : A × X) ≠ resetOutput z} =
          statePair ⁻¹' {p : X × X | p.1 ≠ p.2} := by
        ext z
        simp [resetOutput, statePair, Prod.ext_iff]
      have hBad : MeasurableSet {p : X × X | p.1 ≠ p.2} :=
        (measurableSet_eq_fun measurable_fst measurable_snd).compl
      have happ := Measure.map_apply measurable_statePair hBad
        (μ := omega)
      rw [show Measure.map statePair omega = kappa by
        simpa only [omega] using hpair] at happ
      rw [hset, ← happ]
      exact hfail
    have htv := tvLe_map_map_of_measure_ne_le
      (mu := omega) measurable_fst measurable_resetOutput hne
    have hfstOmega : Measure.map Prod.fst omega = mu := by
      simpa only [omega] using map_fst_resetExtension mu kappa
    simpa only [hfstOmega, nu] using htv

#print axioms map_statePair_resetExtension
#print axioms exists_costPreserving_reset_of_coupling

end Ttc.TVCostPreservingResetLift
