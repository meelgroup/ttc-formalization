import Ttc.Exec.CVHistoryCostedKernel
import Ttc.Exec.CVRetainedHistoryReferenceInduction

/-!
# Adapter from cost-increment cooling phases to retained-history references

This discharges the two law-quantified hypotheses of the generic reset induction.  For
the concrete history kernel, both the next-state law and phase mean depend only on the
exact current-state marginal.  Therefore ordinary exact-warm per-phase estimates are
sufficient; no assertion about the distribution of the stored estimator history is
needed.
-/

namespace Ttc.CVHistoryReferenceAdapter

open MeasureTheory ProbabilityTheory Finset
open Arlib
open Ttc.CVHistoryCostedKernel
open Ttc.CVRetainedHistoryReferenceInduction
open scoped ENNReal Classical BigOperators

variable {X : Type*} [MeasurableSpace X]

/-- Scalar history-retaining reference construction directly from a cost-increment
schedule.  The remaining analytic inputs have the natural exact-state form: one TV
estimate and one expected phase-cost estimate under `tau i`. -/
theorem exists_historyReference_of_incrementKernels
    [StandardBorelSpace X] [Nonempty X]
    (Q : Nat → Kernel X (ENNReal × X)) [∀ i, IsMarkovKernel (Q i)]
    (mu0 nu0 : Measure (HistoryState X))
    [IsProbabilityMeasure mu0] [IsProbabilityMeasure nu0]
    (tau : Nat → Measure X) [∀ i, IsProbabilityMeasure (tau i)]
    (e B : Nat → ENNReal) {d initialBudget : ENNReal}
    (hinitTV : TVLe mu0 nu0 d)
    (hinitState : Measure.map Prod.snd nu0 = tau 0)
    (hinitMean : (∫⁻ z, z.1.1 ∂nu0) ≤ initialBudget)
    (hphaseTV : ∀ i,
      TVLe ((tau i).bind (Kernel.map (Q i) Prod.snd)) (tau (i + 1)) (e i))
    (hphaseCost : ∀ i,
      (∫⁻ x, Ttc.SequentialCost.stepMean (fun _ ↦ Q i) 0 x ∂tau i) ≤ B i)
    (t : Nat) :
    ∃ reference : Measure (HistoryState X),
      IsProbabilityMeasure reference ∧
      Measure.map Prod.snd reference = tau t ∧
      TVLe
        (retainedPathLaw (fun i ↦ historyCostedKernel (Q i) i) mu0 t)
        reference (d + ∑ i ∈ range t, e i) ∧
      (∫⁻ z, z.1.1 ∂reference) ≤
        initialBudget + ∑ i ∈ range t, B i := by
  apply exists_exactHistoryReference_terminal
    (fun a : HistoryPayload X ↦ a.1) measurable_fst
    (fun i ↦ historyCostedKernel (Q i) i)
    mu0 nu0 tau e B hinitTV hinitState hinitMean
  · intro i nu hprob hstate
    letI : IsProbabilityMeasure nu := hprob
    rw [map_snd_bind_historyCostedKernel, hstate]
    exact hphaseTV i
  · intro i nu hprob hstate
    letI : IsProbabilityMeasure nu := hprob
    rw [lintegral_historyCost_bind_historyCostedKernel, hstate]
    exact add_le_add_right (hphaseCost i) _

/-- Global-timeout form of the scalar adapter. -/
theorem exists_historyReference_globalTimeout_of_incrementKernels
    [StandardBorelSpace X] [Nonempty X]
    (Q : Nat → Kernel X (ENNReal × X)) [∀ i, IsMarkovKernel (Q i)]
    (mu0 nu0 : Measure (HistoryState X))
    [IsProbabilityMeasure mu0] [IsProbabilityMeasure nu0]
    (tau : Nat → Measure X) [∀ i, IsProbabilityMeasure (tau i)]
    (e B : Nat → ENNReal) {d initialBudget cutoff : ENNReal}
    (hinitTV : TVLe mu0 nu0 d)
    (hinitState : Measure.map Prod.snd nu0 = tau 0)
    (hinitMean : (∫⁻ z, z.1.1 ∂nu0) ≤ initialBudget)
    (hphaseTV : ∀ i,
      TVLe ((tau i).bind (Kernel.map (Q i) Prod.snd)) (tau (i + 1)) (e i))
    (hphaseCost : ∀ i,
      (∫⁻ x, Ttc.SequentialCost.stepMean (fun _ ↦ Q i) 0 x ∂tau i) ≤ B i)
    (hcut0 : cutoff ≠ 0) (hcutTop : cutoff ≠ ⊤) (t : Nat) :
    ∃ reference : Measure (HistoryState X),
      IsProbabilityMeasure reference ∧
      Measure.map Prod.snd reference = tau t ∧
      TVLe
        (retainedPathLaw (fun i ↦ historyCostedKernel (Q i) i) mu0 t)
        reference (d + ∑ i ∈ range t, e i) ∧
      (∫⁻ z, z.1.1 ∂reference) ≤
        initialBudget + ∑ i ∈ range t, B i ∧
      retainedPathLaw (fun i ↦ historyCostedKernel (Q i) i) mu0 t
          {z | cutoff ≤ z.1.1} ≤
        (initialBudget + ∑ i ∈ range t, B i) / cutoff +
          (d + ∑ i ∈ range t, e i) := by
  apply exists_exactHistoryReference_globalTimeout
    (fun a : HistoryPayload X ↦ a.1) measurable_fst
    (fun i ↦ historyCostedKernel (Q i) i)
    mu0 nu0 tau e B hinitTV hinitState hinitMean
  · intro i nu hprob hstate
    letI : IsProbabilityMeasure nu := hprob
    rw [map_snd_bind_historyCostedKernel, hstate]
    exact hphaseTV i
  · intro i nu hprob hstate
    letI : IsProbabilityMeasure nu := hprob
    rw [lintegral_historyCost_bind_historyCostedKernel, hstate]
    exact add_le_add_right (hphaseCost i) _
  · exact hcut0
  · exact hcutTop

#print axioms exists_historyReference_of_incrementKernels
#print axioms exists_historyReference_globalTimeout_of_incrementKernels

end Ttc.CVHistoryReferenceAdapter
