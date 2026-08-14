/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Exec.CVRetainedHistoryReferenceInduction

set_option autoImplicit false

/-!
# Independent-history reference audit

Resetting only the current-state marginal is enough to preserve a cost history, but it
does not make that state independent of the retained estimator history.  Exact-law CV
accuracy needs precisely this stronger product property.

This file gives the strongest direct adapter: if every phase's complete
`(updated history, next state)` law is TV-close to the product of its actual updated
history marginal and the next exact target, then induction constructs a reference which
is both cost-preserving and exactly independent at the terminal state.

The new hypothesis `hphaseJoint` is intentionally visible.  A TV theorem only for the
next-state marginal cannot discharge it; `CVSequentialDependence.marginalTV_zero_not_sufficient`
already gives the exact obstruction.  A pointwise conditional-kernel mixing theorem (or
an equivalent joint-product theorem) would discharge it via `TVLe.bind_pointwise`.
-/

namespace Ttc.CVHistoryIndependentReferenceAudit

open MeasureTheory ProbabilityTheory Finset
open Arlib
open Ttc.CVRetainedHistoryReferenceInduction
open scoped ENNReal Classical BigOperators

variable {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]

/-- Replace the current state by a fresh exact target, independently of the complete
retained history. -/
noncomputable def independentHistoryReset
    (mu : Measure (A × X)) (tau : Measure X) : Measure (A × X) :=
  (Measure.map Prod.fst mu).prod tau

instance independentHistoryReset.instIsProbabilityMeasure
    (mu : Measure (A × X)) [IsProbabilityMeasure mu]
    (tau : Measure X) [IsProbabilityMeasure tau] :
    IsProbabilityMeasure (independentHistoryReset mu tau) := by
  unfold independentHistoryReset
  letI : IsProbabilityMeasure (Measure.map Prod.fst mu) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  infer_instance

theorem map_fst_independentHistoryReset
    (mu : Measure (A × X)) [IsProbabilityMeasure mu]
    (tau : Measure X) [IsProbabilityMeasure tau] :
    Measure.map Prod.fst (independentHistoryReset mu tau) =
      Measure.map Prod.fst mu := by
  unfold independentHistoryReset
  simpa using (Measure.map_fst_prod
    (μ := Measure.map Prod.fst mu) (ν := tau))

theorem map_snd_independentHistoryReset
    (mu : Measure (A × X)) [IsProbabilityMeasure mu]
    (tau : Measure X) [IsProbabilityMeasure tau] :
    Measure.map Prod.snd (independentHistoryReset mu tau) = tau := by
  unfold independentHistoryReset
  letI : IsProbabilityMeasure (Measure.map Prod.fst mu) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  simpa using (Measure.map_snd_prod
    (μ := Measure.map Prod.fst mu) (ν := tau))

theorem independentHistoryReset_is_product
    (mu : Measure (A × X)) [IsProbabilityMeasure mu]
    (tau : Measure X) [IsProbabilityMeasure tau] :
    independentHistoryReset mu tau =
      (Measure.map Prod.fst (independentHistoryReset mu tau)).prod tau := by
  rw [map_fst_independentHistoryReset]
  rfl

/-- One complete joint-product reset.  Unlike a marginal maximal-coupling reset, the
new current state is exactly independent of the retained history.  The history marginal
and therefore every history-measurable cost expectation are still preserved exactly. -/
theorem nextIndependentHistoryReference_of_jointTV
    (cost : A → ENNReal) (hcost : Measurable cost)
    (Q : Kernel (A × X) (A × X)) [IsMarkovKernel Q]
    (actual reference : Measure (A × X))
    [IsProbabilityMeasure actual] [IsProbabilityMeasure reference]
    (target : Measure X) [IsProbabilityMeasure target]
    {priorError phaseError priorBudget phaseBudget : ENNReal}
    (hprior : TVLe actual reference priorError)
    (hjoint : TVLe (reference.bind Q)
      (independentHistoryReset (reference.bind Q) target) phaseError)
    (hphaseMean : (∫⁻ z, cost z.1 ∂reference.bind Q) ≤
      priorBudget + phaseBudget) :
    let nextReference := independentHistoryReset (reference.bind Q) target
    IsProbabilityMeasure nextReference ∧
      Measure.map Prod.fst nextReference =
        Measure.map Prod.fst (reference.bind Q) ∧
      Measure.map Prod.snd nextReference = target ∧
      nextReference = (Measure.map Prod.fst nextReference).prod target ∧
      TVLe (actual.bind Q) nextReference (priorError + phaseError) ∧
      (∫⁻ z, cost z.1 ∂nextReference) ≤ priorBudget + phaseBudget := by
  dsimp only
  let raw := reference.bind Q
  let nextReference := independentHistoryReset raw target
  haveI : IsProbabilityMeasure raw := by
    dsimp only [raw]
    infer_instance
  haveI : IsProbabilityMeasure nextReference := by
    dsimp only [nextReference]
    infer_instance
  refine ⟨inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · exact map_fst_independentHistoryReset raw target
  · exact map_snd_independentHistoryReset raw target
  · exact independentHistoryReset_is_product raw target
  · exact (hprior.bind_kernel Q).trans hjoint
  · rw [lintegral_historyCost_eq_of_map_fst_eq cost hcost
      (map_fst_independentHistoryReset raw target)]
    exact hphaseMean

/-- Finite induction under the exact missing phase premise.  At every terminal time the
reference state is a product of the complete retained-history marginal and the exact
current target, while its expected retained cost has the same additive source budget. -/
theorem exists_independentHistoryReference_terminal
    (cost : A → ENNReal) (hcost : Measurable cost)
    (Q : Nat → Kernel (A × X) (A × X)) [∀ i, IsMarkovKernel (Q i)]
    (mu0 nu0 : Measure (A × X))
    [IsProbabilityMeasure mu0] [IsProbabilityMeasure nu0]
    (tau : Nat → Measure X) [∀ i, IsProbabilityMeasure (tau i)]
    (e B : Nat → ENNReal) {d initialBudget : ENNReal}
    (hinitTV : TVLe mu0 nu0 d)
    (hinitState : Measure.map Prod.snd nu0 = tau 0)
    (hinitProduct : nu0 = (Measure.map Prod.fst nu0).prod (tau 0))
    (hinitMean : (∫⁻ z, cost z.1 ∂nu0) ≤ initialBudget)
    (hphaseJoint : ∀ (i : Nat) (nu : Measure (A × X)),
      IsProbabilityMeasure nu → Measure.map Prod.snd nu = tau i →
      nu = (Measure.map Prod.fst nu).prod (tau i) →
      TVLe (nu.bind (Q i))
        (independentHistoryReset (nu.bind (Q i)) (tau (i + 1))) (e i))
    (hphaseMean : ∀ (i : Nat) (nu : Measure (A × X)),
      IsProbabilityMeasure nu → Measure.map Prod.snd nu = tau i →
      (∫⁻ z, cost z.1 ∂nu.bind (Q i)) ≤ (∫⁻ z, cost z.1 ∂nu) + B i)
    (t : Nat) :
    ∃ reference : Measure (A × X),
      IsProbabilityMeasure reference ∧
      Measure.map Prod.snd reference = tau t ∧
      reference = (Measure.map Prod.fst reference).prod (tau t) ∧
      TVLe (retainedPathLaw Q mu0 t) reference
        (d + ∑ i ∈ range t, e i) ∧
      (∫⁻ z, cost z.1 ∂reference) ≤
        initialBudget + ∑ i ∈ range t, B i := by
  induction t with
  | zero =>
      refine ⟨nu0, inferInstance, hinitState, hinitProduct, ?_, ?_⟩
      · simpa [retainedPathLaw] using hinitTV
      · simpa using hinitMean
  | succ t ih =>
      obtain ⟨reference, hprob, hstate, hproduct, htv, hmean⟩ := ih
      letI : IsProbabilityMeasure reference := hprob
      have hjoint := hphaseJoint t reference hprob hstate hproduct
      have hrawMean0 := hphaseMean t reference hprob hstate
      have hrawMean : (∫⁻ z, cost z.1 ∂reference.bind (Q t)) ≤
          (initialBudget + ∑ i ∈ range t, B i) + B t :=
        hrawMean0.trans (add_le_add hmean le_rfl)
      have hnext := nextIndependentHistoryReference_of_jointTV cost hcost (Q t)
        (retainedPathLaw Q mu0 t) reference (tau (t + 1)) htv hjoint hrawMean
      let nextReference := independentHistoryReset (reference.bind (Q t)) (tau (t + 1))
      refine ⟨nextReference, hnext.1, hnext.2.2.1, hnext.2.2.2.1, ?_, ?_⟩
      · simpa only [retainedPathLaw, sum_range_succ, add_assoc] using
          hnext.2.2.2.2.1
      · simpa only [sum_range_succ, add_assoc] using hnext.2.2.2.2.2

#print axioms nextIndependentHistoryReference_of_jointTV
#print axioms exists_independentHistoryReference_terminal

end Ttc.CVHistoryIndependentReferenceAudit
