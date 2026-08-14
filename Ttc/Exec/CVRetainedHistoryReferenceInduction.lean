import Ttc.Exec.TVMaximalCoupling
import Ttc.Exec.CVExceptionalReferenceGlobalTimeout

/-!
# Exact reference induction retaining arbitrary history

The first coordinate of the phase state may contain the accumulated query cost *and*
the complete estimator history.  A maximal-coupling reset changes only the current
warm seed.  Thus earlier scores, random choices, and the accumulated cost are retained
exactly.  This is the history-preserving version of `CVExactStateReferenceInduction`.
-/

namespace Ttc.CVRetainedHistoryReferenceInduction

open MeasureTheory ProbabilityTheory Set Finset
open Arlib
open Ttc.TVMaximalCoupling
open Ttc.CVExceptionalReferenceGlobalTimeout
open scoped ENNReal Classical BigOperators

variable {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]

/-- Inhomogeneous iteration of phase kernels on `(retained history, current state)`. -/
noncomputable def retainedPathLaw
    (Q : Nat → Kernel (A × X) (A × X))
    (mu : Measure (A × X)) : Nat → Measure (A × X)
  | 0 => mu
  | i + 1 => (retainedPathLaw Q mu i).bind (Q i)

instance retainedPathLaw.instIsProbabilityMeasure
    (Q : Nat → Kernel (A × X) (A × X))
    [∀ i, IsMarkovKernel (Q i)]
    (mu : Measure (A × X)) [IsProbabilityMeasure mu] (i : Nat) :
    IsProbabilityMeasure (retainedPathLaw Q mu i) := by
  induction i with
  | zero => simpa [retainedPathLaw]
  | succ i ih =>
      rw [retainedPathLaw]
      infer_instance

/-- Equality of retained-history marginals transports the expectation of every
measurable cost read from that history. -/
theorem lintegral_historyCost_eq_of_map_fst_eq
    (cost : A → ENNReal) (hcost : Measurable cost)
    {mu nu : Measure (A × X)}
    (h : Measure.map Prod.fst mu = Measure.map Prod.fst nu) :
    (∫⁻ z, cost z.1 ∂mu) = ∫⁻ z, cost z.1 ∂nu := by
  have hmu : (∫⁻ z, cost z.1 ∂mu) = ∫⁻ a, cost a ∂Measure.map Prod.fst mu := by
    rw [lintegral_map hcost measurable_fst]
  have hnu : (∫⁻ z, cost z.1 ∂nu) = ∫⁻ a, cost a ∂Measure.map Prod.fst nu := by
    rw [lintegral_map hcost measurable_fst]
  rw [hmu, hnu, h]

/-- One reset changes only the current state.  The complete history marginal, and hence
any measurable accumulated-cost statistic stored in it, is preserved exactly. -/
theorem exists_nextHistoryReference
    [StandardBorelSpace X] [Nonempty X]
    (cost : A → ENNReal) (hcost : Measurable cost)
    (Q : Kernel (A × X) (A × X)) [IsMarkovKernel Q]
    (actual reference : Measure (A × X))
    [IsProbabilityMeasure actual] [IsProbabilityMeasure reference]
    (target : Measure X) [IsProbabilityMeasure target]
    {priorError phaseError priorBudget phaseBudget : ENNReal}
    (hprior : TVLe actual reference priorError)
    (hstate : TVLe (Measure.map Prod.snd (reference.bind Q)) target phaseError)
    (hphaseMean : (∫⁻ z, cost z.1 ∂reference.bind Q) ≤ priorBudget + phaseBudget) :
    ∃ nextReference : Measure (A × X),
      IsProbabilityMeasure nextReference ∧
      Measure.map Prod.fst nextReference =
        Measure.map Prod.fst (reference.bind Q) ∧
      Measure.map Prod.snd nextReference = target ∧
      TVLe (actual.bind Q) nextReference (priorError + phaseError) ∧
      (∫⁻ z, cost z.1 ∂nextReference) ≤ priorBudget + phaseBudget := by
  let raw := reference.bind Q
  letI : IsProbabilityMeasure raw := by
    dsimp only [raw]
    infer_instance
  obtain ⟨nextReference, hprob, hhistory, htarget, hreset⟩ :=
    exists_costPreserving_reset_of_tvLe raw target hstate
  letI : IsProbabilityMeasure nextReference := hprob
  refine ⟨nextReference, hprob, hhistory, htarget, ?_, ?_⟩
  · exact (hprior.bind_kernel Q).trans hreset
  · rw [lintegral_historyCost_eq_of_map_fst_eq cost hcost hhistory]
    exact hphaseMean

/-- **Finite history-preserving exact-reference induction.**

Unlike the earlier `(cost,current-state)` theorem, `A` is arbitrary.  It can be a
complete cooling prefix (or a tuple of prefixes) carrying every score used by the final
estimator, together with accumulated query cost.  The reset leaves its entire marginal
unchanged and only replaces the current seed marginal by `tau (i+1)`. -/
theorem exists_exactHistoryReference_terminal
    [StandardBorelSpace X] [Nonempty X]
    (cost : A → ENNReal) (hcost : Measurable cost)
    (Q : Nat → Kernel (A × X) (A × X))
    [∀ i, IsMarkovKernel (Q i)]
    (mu0 nu0 : Measure (A × X))
    [IsProbabilityMeasure mu0] [IsProbabilityMeasure nu0]
    (tau : Nat → Measure X) [∀ i, IsProbabilityMeasure (tau i)]
    (e B : Nat → ENNReal) {d initialBudget : ENNReal}
    (hinitTV : TVLe mu0 nu0 d)
    (hinitState : Measure.map Prod.snd nu0 = tau 0)
    (hinitMean : (∫⁻ z, cost z.1 ∂nu0) ≤ initialBudget)
    (hphaseState : ∀ (i : Nat) (nu : Measure (A × X)),
      IsProbabilityMeasure nu → Measure.map Prod.snd nu = tau i →
      TVLe (Measure.map Prod.snd (nu.bind (Q i))) (tau (i + 1)) (e i))
    (hphaseMean : ∀ (i : Nat) (nu : Measure (A × X)),
      IsProbabilityMeasure nu → Measure.map Prod.snd nu = tau i →
      (∫⁻ z, cost z.1 ∂nu.bind (Q i)) ≤ (∫⁻ z, cost z.1 ∂nu) + B i)
    (t : Nat) :
    ∃ reference : Measure (A × X),
      IsProbabilityMeasure reference ∧
      Measure.map Prod.snd reference = tau t ∧
      TVLe (retainedPathLaw Q mu0 t) reference
        (d + ∑ i ∈ range t, e i) ∧
      (∫⁻ z, cost z.1 ∂reference) ≤
        initialBudget + ∑ i ∈ range t, B i := by
  induction t with
  | zero =>
      refine ⟨nu0, inferInstance, hinitState, ?_, ?_⟩
      · simpa [retainedPathLaw] using hinitTV
      · simpa using hinitMean
  | succ t ih =>
      obtain ⟨reference, hprob, hstate, htv, hmean⟩ := ih
      letI : IsProbabilityMeasure reference := hprob
      have hrawState := hphaseState t reference hprob hstate
      have hrawMean0 := hphaseMean t reference hprob hstate
      have hrawMean : (∫⁻ z, cost z.1 ∂reference.bind (Q t)) ≤
          (initialBudget + ∑ i ∈ range t, B i) + B t :=
        hrawMean0.trans (add_le_add hmean le_rfl)
      obtain ⟨nextReference, hnextProb, hnextHistory, hnextState, hnextTV,
          hnextMean⟩ :=
        exists_nextHistoryReference cost hcost (Q t)
          (retainedPathLaw Q mu0 t) reference (tau (t + 1))
          htv hrawState hrawMean
      refine ⟨nextReference, hnextProb, hnextState, ?_, ?_⟩
      · simpa only [retainedPathLaw, sum_range_succ, add_assoc] using hnextTV
      · simpa only [sum_range_succ, add_assoc] using hnextMean

/-- The history-preserving induction feeds into one global timeout.  The timeout reads
the accumulated cost from the retained history; no per-phase cutoff is introduced. -/
theorem exists_exactHistoryReference_globalTimeout
    [StandardBorelSpace X] [Nonempty X]
    (cost : A → ENNReal) (hcost : Measurable cost)
    (Q : Nat → Kernel (A × X) (A × X))
    [∀ i, IsMarkovKernel (Q i)]
    (mu0 nu0 : Measure (A × X))
    [IsProbabilityMeasure mu0] [IsProbabilityMeasure nu0]
    (tau : Nat → Measure X) [∀ i, IsProbabilityMeasure (tau i)]
    (e B : Nat → ENNReal) {d initialBudget cutoff : ENNReal}
    (hinitTV : TVLe mu0 nu0 d)
    (hinitState : Measure.map Prod.snd nu0 = tau 0)
    (hinitMean : (∫⁻ z, cost z.1 ∂nu0) ≤ initialBudget)
    (hphaseState : ∀ (i : Nat) (nu : Measure (A × X)),
      IsProbabilityMeasure nu → Measure.map Prod.snd nu = tau i →
      TVLe (Measure.map Prod.snd (nu.bind (Q i))) (tau (i + 1)) (e i))
    (hphaseMean : ∀ (i : Nat) (nu : Measure (A × X)),
      IsProbabilityMeasure nu → Measure.map Prod.snd nu = tau i →
      (∫⁻ z, cost z.1 ∂nu.bind (Q i)) ≤ (∫⁻ z, cost z.1 ∂nu) + B i)
    (hcut0 : cutoff ≠ 0) (hcutTop : cutoff ≠ ⊤) (t : Nat) :
    ∃ reference : Measure (A × X),
      IsProbabilityMeasure reference ∧
      Measure.map Prod.snd reference = tau t ∧
      TVLe (retainedPathLaw Q mu0 t) reference
        (d + ∑ i ∈ range t, e i) ∧
      (∫⁻ z, cost z.1 ∂reference) ≤
        initialBudget + ∑ i ∈ range t, B i ∧
      retainedPathLaw Q mu0 t {z | cutoff ≤ cost z.1} ≤
        (initialBudget + ∑ i ∈ range t, B i) / cutoff +
          (d + ∑ i ∈ range t, e i) := by
  obtain ⟨reference, hprob, hstate, htv, hmean⟩ :=
    exists_exactHistoryReference_terminal cost hcost Q mu0 nu0 tau e B
      hinitTV hinitState hinitMean hphaseState hphaseMean t
  letI : IsProbabilityMeasure reference := hprob
  letI : IsProbabilityMeasure (retainedPathLaw Q mu0 t) := inferInstance
  refine ⟨reference, hprob, hstate, htv, hmean, ?_⟩
  exact globalTimeout_le_of_jointPathTV htv (fun z ↦ cost z.1)
    (hcost.comp measurable_fst) hcut0 hcutTop hmean

#print axioms exists_nextHistoryReference
#print axioms exists_exactHistoryReference_terminal
#print axioms exists_exactHistoryReference_globalTimeout

end Ttc.CVRetainedHistoryReferenceInduction
