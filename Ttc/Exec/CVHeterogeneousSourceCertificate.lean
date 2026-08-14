import Ttc.Exec.CVHeterogeneousHistoryReference
import Ttc.Exec.CVIndependentHistoryReference
import Ttc.Exec.CVSourceReferenceTVCapstone

/-!
# Source certificate from stationary-seed history phases

This is the capstone-facing form of `CVHeterogeneousHistoryReference`.  It tensors
independent scalar streams only after constructing a cost-preserving reference whose
current seed is reset to the exact phase target.  Hence no coarse score/seed warmth
factor occurs in the reference expected-cost premise.
-/

set_option autoImplicit false

namespace Ttc.CVHeterogeneousSourceCertificate

open MeasureTheory ProbabilityTheory Finset Set
open Arlib
open Ttc.CVRetainedHistoryReferenceInduction
open Ttc.CVHeterogeneousHistoryReference
open Ttc.CVIndependentHistoryReference
open Ttc.CVSourceReferenceTVCapstone
open scoped ENNReal Classical BigOperators

variable {Score Seed : Type*} [MeasurableSpace Score] [MeasurableSpace Seed]

/-- A complete source one-run certificate from a seed-targeted phase schedule.

The only phase-distribution premise is on the next seed marginal.  Scores and query
costs are retained untouched by the maximal-coupling reset. -/
theorem exists_sourceReferenceTVOneRunCertificate_of_stationarySeedPhases
    [StandardBorelSpace Seed] [Nonempty Seed]
    (Q : Nat → Kernel Seed (ENNReal × (Score × Seed)))
    [∀ i, IsMarkovKernel (Q i)]
    (mu0 nu0 : Measure (HeterogeneousHistoryState Score Seed))
    [IsProbabilityMeasure mu0] [IsProbabilityMeasure nu0]
    (tau : Nat → Measure Seed) [∀ i, IsProbabilityMeasure (tau i)]
    (e B : Nat → ENNReal) {d initialBudget : ENNReal}
    (hinitTV : TVLe mu0 nu0 d)
    (hinitState : Measure.map Prod.snd nu0 = tau 0)
    (hinitMean : (∫⁻ z, z.1.1 ∂nu0) ≤ initialBudget)
    (hphaseSeedTV : ∀ i,
      TVLe ((tau i).bind
        (Kernel.map (Q i) (fun y : ENNReal × (Score × Seed) ↦ y.2.2)))
        (tau (i + 1)) (e i))
    (hphaseCost : ∀ i,
      (∫⁻ x, heterogeneousStepMean (Q i) x ∂tau i) ≤ B i)
    (dim m k : Nat)
    (value : (Fin k → HeterogeneousHistoryState Score Seed) → Real)
    (hvalue : Measurable value)
    {runtimeConstant R eps lo hi : Real}
    (herror : (k : ENNReal) * (d + ∑ i ∈ range m, e i) ≤
      ENNReal.ofReal (1 / 40 : Real))
    (hbudget : (k : ENNReal) *
        (initialBudget + ∑ i ∈ range m, B i) ≤
      Ttc.CVSourcePolynomialCutoffCapstone.sourceOneRunQueryBudget
        runtimeConstant dim R eps)
    (haccuracy : 4 / 5 ≤
      (Measure.pi (fun _ : Fin k ↦
        retainedPathLaw (fun i ↦ heterogeneousHistoryKernel (Q i) i) mu0 m)).real
      {omega | value omega ∈ Icc lo hi}) :
    ∃ reference : Measure (Fin k → HeterogeneousHistoryState Score Seed),
      SourceReferenceTVOneRunCertificate
        (Measure.pi (fun _ : Fin k ↦
          retainedPathLaw (fun i ↦ heterogeneousHistoryKernel (Q i) i) mu0 m))
        reference (fun omega ↦ ∑ j, (omega j).1.1) value
        runtimeConstant dim R eps lo hi := by
  have hscalar := exists_heterogeneousHistoryReference_of_seedKernels
    Q mu0 nu0 tau e B hinitTV hinitState hinitMean
    hphaseSeedTV hphaseCost m
  obtain ⟨scalarReference, hscalarProb, _hscalarState, hscalarTV, hscalarMean⟩ := hscalar
  letI : IsProbabilityMeasure scalarReference := hscalarProb
  obtain ⟨reference, hrefProb, hrefTV, hrefMean⟩ :=
    exists_product_historyReference (fun z : HeterogeneousHistoryState Score Seed ↦ z.1.1)
      (measurable_fst.comp measurable_fst)
      (fun _ : Fin k ↦
        retainedPathLaw (fun i ↦ heterogeneousHistoryKernel (Q i) i) mu0 m)
      (fun _ : Fin k ↦ d + ∑ i ∈ range m, e i)
      (fun _ : Fin k ↦ initialBudget + ∑ i ∈ range m, B i)
      (fun _ ↦ ⟨scalarReference, hscalarProb, hscalarTV, hscalarMean⟩)
  refine ⟨reference,
    { actual_probability := inferInstance
      reference_probability := hrefProb
      cost_measurable := measurable_totalHistoryCost (measurable_fst.comp measurable_fst)
      value_measurable := hvalue
      path_tv := ?_
      reference_expected_queries := ?_
      accuracy := haccuracy }⟩
  · exact hrefTV.mono (by
      simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] using herror)
  · exact hrefMean.trans (by
      simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] using hbudget)

#print axioms exists_sourceReferenceTVOneRunCertificate_of_stationarySeedPhases

end Ttc.CVHeterogeneousSourceCertificate
