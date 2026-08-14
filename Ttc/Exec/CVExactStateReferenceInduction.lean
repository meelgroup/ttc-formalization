import Ttc.Exec.TVMaximalCoupling
import Ttc.Exec.CVExceptionalReferenceGlobalTimeout

/-!
# Exact-state reference induction with cost-preserving resets

At each phase the actual and reference laws use the same complete cost-recording kernel.
The raw reference output is then reset to the next exact target state by maximal coupling
and disintegration.  The reset retains the accumulated-cost marginal.  Consequently TV
errors telescope, while reference expected costs add rather than compound.
-/

namespace Ttc.CVExactStateReferenceInduction

open MeasureTheory ProbabilityTheory Set Finset
open Arlib
open Ttc.TVMaximalCoupling
open Ttc.CVExceptionalReferenceGlobalTimeout
open scoped ENNReal Classical BigOperators

variable {X : Type*} [MeasurableSpace X]

/-- Inhomogeneous iteration of complete `(accumulated cost, state)` phase kernels. -/
noncomputable def costPathLaw
    (Q : Nat → Kernel (ENNReal × X) (ENNReal × X))
    (mu : Measure (ENNReal × X)) : Nat → Measure (ENNReal × X)
  | 0 => mu
  | i + 1 => (costPathLaw Q mu i).bind (Q i)

instance costPathLaw.instIsProbabilityMeasure
    (Q : Nat → Kernel (ENNReal × X) (ENNReal × X))
    [∀ i, IsMarkovKernel (Q i)]
    (mu : Measure (ENNReal × X)) [IsProbabilityMeasure mu] (i : Nat) :
    IsProbabilityMeasure (costPathLaw Q mu i) := by
  induction i with
  | zero => simpa [costPathLaw]
  | succ i ih =>
      rw [costPathLaw]
      infer_instance

/-- Equality of accumulated-cost marginals implies equality of their expectations. -/
theorem lintegral_fst_eq_of_map_fst_eq
    {mu nu : Measure (ENNReal × X)}
    (h : Measure.map Prod.fst mu = Measure.map Prod.fst nu) :
    (∫⁻ z, z.1 ∂mu) = ∫⁻ z, z.1 ∂nu := by
  have hmu : (∫⁻ z, z.1 ∂mu) = ∫⁻ c, c ∂Measure.map Prod.fst mu := by
    simpa only [Function.comp_apply, id_eq] using
      (lintegral_map (μ := mu) (f := id) (g := Prod.fst)
        measurable_id measurable_fst).symm
  have hnu : (∫⁻ z, z.1 ∂nu) = ∫⁻ c, c ∂Measure.map Prod.fst nu := by
    simpa only [Function.comp_apply, id_eq] using
      (lintegral_map (μ := nu) (f := id) (g := Prod.fst)
        measurable_id measurable_fst).symm
  rw [hmu, hnu, h]

/-- One exact-state reset step.  Running the same phase kernel preserves the accumulated
TV error.  Resetting its state marginal spends `phaseError`, but preserves its complete
accumulated-cost marginal and hence its expected accumulated cost. -/
theorem exists_nextReference
    [StandardBorelSpace X] [Nonempty X]
    (Q : Kernel (ENNReal × X) (ENNReal × X)) [IsMarkovKernel Q]
    (actual reference : Measure (ENNReal × X))
    [IsProbabilityMeasure actual] [IsProbabilityMeasure reference]
    (target : Measure X) [IsProbabilityMeasure target]
    {priorError phaseError priorBudget phaseBudget : ENNReal}
    (hprior : TVLe actual reference priorError)
    (hstate : TVLe (Measure.map Prod.snd (reference.bind Q)) target phaseError)
    (hphaseMean : (∫⁻ z, z.1 ∂reference.bind Q) ≤ priorBudget + phaseBudget) :
    ∃ nextReference : Measure (ENNReal × X),
      IsProbabilityMeasure nextReference ∧
      Measure.map Prod.snd nextReference = target ∧
      TVLe (actual.bind Q) nextReference (priorError + phaseError) ∧
      (∫⁻ z, z.1 ∂nextReference) ≤ priorBudget + phaseBudget := by
  let raw := reference.bind Q
  letI : IsProbabilityMeasure raw := by
    dsimp only [raw]
    infer_instance
  obtain ⟨nextReference, hprob, hcost, htarget, hreset⟩ :=
    exists_costPreserving_reset_of_tvLe raw target hstate
  letI : IsProbabilityMeasure nextReference := hprob
  refine ⟨nextReference, hprob, htarget, ?_, ?_⟩
  · exact (hprior.bind_kernel Q).trans hreset
  · rw [lintegral_fst_eq_of_map_fst_eq hcost]
    exact hphaseMean

/-- **Finite exact-reference induction.**  The phase hypotheses are imposed only on laws
whose current state marginal is the exact target.  Hence phase expected-cost bounds are
the exact-warm bounds `B i`; there is no warmness recurrence and no compounding factor.

The output reference is constructed by repeated maximal-coupling/disintegration resets.
Its state is exactly `tau t`, its accumulated mean is the initial mean plus `sum B`, and
the actual complete path law is within `sum e` in TV. -/
theorem exists_exactReference_terminal
    [StandardBorelSpace X] [Nonempty X]
    (Q : Nat → Kernel (ENNReal × X) (ENNReal × X))
    [∀ i, IsMarkovKernel (Q i)]
    (mu0 nu0 : Measure (ENNReal × X))
    [IsProbabilityMeasure mu0] [IsProbabilityMeasure nu0]
    (tau : Nat → Measure X) [∀ i, IsProbabilityMeasure (tau i)]
    (e B : Nat → ENNReal) {d initialBudget : ENNReal}
    (hinitTV : TVLe mu0 nu0 d)
    (hinitState : Measure.map Prod.snd nu0 = tau 0)
    (hinitMean : (∫⁻ z, z.1 ∂nu0) ≤ initialBudget)
    (hphaseState : ∀ (i : Nat) (nu : Measure (ENNReal × X)),
      IsProbabilityMeasure nu → Measure.map Prod.snd nu = tau i →
      TVLe (Measure.map Prod.snd (nu.bind (Q i))) (tau (i + 1)) (e i))
    (hphaseMean : ∀ (i : Nat) (nu : Measure (ENNReal × X)),
      IsProbabilityMeasure nu → Measure.map Prod.snd nu = tau i →
      (∫⁻ z, z.1 ∂nu.bind (Q i)) ≤ (∫⁻ z, z.1 ∂nu) + B i)
    (t : Nat) :
    ∃ reference : Measure (ENNReal × X),
      IsProbabilityMeasure reference ∧
      Measure.map Prod.snd reference = tau t ∧
      TVLe (costPathLaw Q mu0 t) reference (d + ∑ i ∈ range t, e i) ∧
      (∫⁻ z, z.1 ∂reference) ≤ initialBudget + ∑ i ∈ range t, B i := by
  induction t with
  | zero =>
      refine ⟨nu0, inferInstance, hinitState, ?_, ?_⟩
      · simpa [costPathLaw] using hinitTV
      · simpa using hinitMean
  | succ t ih =>
      obtain ⟨reference, hprob, hstate, htv, hmean⟩ := ih
      letI : IsProbabilityMeasure reference := hprob
      have hrawState := hphaseState t reference hprob hstate
      have hrawMean0 := hphaseMean t reference hprob hstate
      have hrawMean : (∫⁻ z, z.1 ∂reference.bind (Q t)) ≤
          (initialBudget + ∑ i ∈ range t, B i) + B t :=
        hrawMean0.trans (add_le_add hmean le_rfl)
      obtain ⟨nextReference, hnextProb, hnextState, hnextTV, hnextMean⟩ :=
        exists_nextReference (Q t) (costPathLaw Q mu0 t) reference (tau (t + 1))
          htv hrawState hrawMean
      refine ⟨nextReference, hnextProb, hnextState, ?_, ?_⟩
      · simpa only [costPathLaw, sum_range_succ, add_assoc] using hnextTV
      · simpa only [sum_range_succ, add_assoc] using hnextMean

/-- The induction feeds directly into one global timeout.  Markov is applied once to the
terminal exact-state reference, and the whole accumulated TV error is paid once. -/
theorem exists_reference_globalTimeout
    [StandardBorelSpace X] [Nonempty X]
    (Q : Nat → Kernel (ENNReal × X) (ENNReal × X))
    [∀ i, IsMarkovKernel (Q i)]
    (mu0 nu0 : Measure (ENNReal × X))
    [IsProbabilityMeasure mu0] [IsProbabilityMeasure nu0]
    (tau : Nat → Measure X) [∀ i, IsProbabilityMeasure (tau i)]
    (e B : Nat → ENNReal) {d initialBudget cutoff : ENNReal}
    (hinitTV : TVLe mu0 nu0 d)
    (hinitState : Measure.map Prod.snd nu0 = tau 0)
    (hinitMean : (∫⁻ z, z.1 ∂nu0) ≤ initialBudget)
    (hphaseState : ∀ (i : Nat) (nu : Measure (ENNReal × X)),
      IsProbabilityMeasure nu → Measure.map Prod.snd nu = tau i →
      TVLe (Measure.map Prod.snd (nu.bind (Q i))) (tau (i + 1)) (e i))
    (hphaseMean : ∀ (i : Nat) (nu : Measure (ENNReal × X)),
      IsProbabilityMeasure nu → Measure.map Prod.snd nu = tau i →
      (∫⁻ z, z.1 ∂nu.bind (Q i)) ≤ (∫⁻ z, z.1 ∂nu) + B i)
    (hcut0 : cutoff ≠ 0) (hcutTop : cutoff ≠ ⊤) (t : Nat) :
    ∃ reference : Measure (ENNReal × X),
      IsProbabilityMeasure reference ∧
      Measure.map Prod.snd reference = tau t ∧
      TVLe (costPathLaw Q mu0 t) reference (d + ∑ i ∈ range t, e i) ∧
      (∫⁻ z, z.1 ∂reference) ≤ initialBudget + ∑ i ∈ range t, B i ∧
      costPathLaw Q mu0 t {z | cutoff ≤ z.1} ≤
        (initialBudget + ∑ i ∈ range t, B i) / cutoff +
          (d + ∑ i ∈ range t, e i) := by
  obtain ⟨reference, hprob, hstate, htv, hmean⟩ :=
    exists_exactReference_terminal Q mu0 nu0 tau e B hinitTV hinitState hinitMean
      hphaseState hphaseMean t
  letI : IsProbabilityMeasure reference := hprob
  letI : IsProbabilityMeasure (costPathLaw Q mu0 t) := inferInstance
  refine ⟨reference, hprob, hstate, htv, hmean, ?_⟩
  exact globalTimeout_le_of_jointPathTV htv Prod.fst measurable_fst hcut0 hcutTop hmean

#print axioms exists_nextReference
#print axioms exists_exactReference_terminal
#print axioms exists_reference_globalTimeout

end Ttc.CVExactStateReferenceInduction
