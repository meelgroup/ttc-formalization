import Ttc.Exec.CVRetainedHistoryReferenceInduction

/-!
# Tensorizing cost-preserving history references

The CV estimator runs finitely many independent cooling streams.  Once each scalar
stream has a history-retaining reference law, this file tensors those references while
adding both their TV errors and their expected recorded query costs.
-/

namespace Ttc.CVIndependentHistoryReference

open MeasureTheory ProbabilityTheory Finset
open Arlib
open scoped ENNReal Classical BigOperators

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Total cost of a finite family of complete scalar histories. -/
noncomputable def totalHistoryCost {k : Nat} (cost : Omega → ENNReal)
    (omega : Fin k → Omega) : ENNReal :=
  ∑ l, cost (omega l)

theorem measurable_totalHistoryCost {k : Nat} {cost : Omega → ENNReal}
    (hcost : Measurable cost) :
    Measurable (totalHistoryCost (k := k) cost) := by
  unfold totalHistoryCost
  apply Finset.measurable_fun_sum
  intro l _hl
  exact hcost.comp (measurable_pi_apply l)

/-- Product references add scalar TV errors and scalar reference means. -/
theorem product_historyReference
    {k : Nat} (cost : Omega → ENNReal) (hcost : Measurable cost)
    (actual reference : Fin k → Measure Omega)
    [∀ l, IsProbabilityMeasure (actual l)]
    [∀ l, IsProbabilityMeasure (reference l)]
    (e B : Fin k → ENNReal)
    (htv : ∀ l, TVLe (actual l) (reference l) (e l))
    (hmean : ∀ l, (∫⁻ omega, cost omega ∂reference l) ≤ B l) :
    TVLe (Measure.pi actual) (Measure.pi reference) (∑ l, e l) ∧
      (∫⁻ omega, totalHistoryCost cost omega ∂Measure.pi reference) ≤
        ∑ l, B l := by
  constructor
  · exact TVLe.pi htv
  · unfold totalHistoryCost
    rw [lintegral_finset_sum]
    · apply Finset.sum_le_sum
      intro l _hl
      let hmp := measurePreserving_eval reference l
      have hmap : Measure.map (fun omega : Fin k → Omega ↦ omega l)
          (Measure.pi reference) = reference l := hmp.map_eq
      calc
        (∫⁻ omega, cost (omega l) ∂Measure.pi reference) =
            ∫⁻ omega, cost omega ∂reference l := by
          rw [← lintegral_map hcost (measurable_pi_apply l), hmap]
        _ ≤ B l := hmean l
    · intro l _hl
      exact hcost.comp (measurable_pi_apply l)

/-- Existential form: independently choose the scalar history references and package
them as one complete reference law for all estimator streams. -/
theorem exists_product_historyReference
    {k : Nat} (cost : Omega → ENNReal) (hcost : Measurable cost)
    (actual : Fin k → Measure Omega)
    [∀ l, IsProbabilityMeasure (actual l)]
    (e B : Fin k → ENNReal)
    (hscalar : ∀ l, ∃ reference : Measure Omega,
      IsProbabilityMeasure reference ∧
      TVLe (actual l) reference (e l) ∧
      (∫⁻ omega, cost omega ∂reference) ≤ B l) :
    ∃ reference : Measure (Fin k → Omega),
      IsProbabilityMeasure reference ∧
      TVLe (Measure.pi actual) reference (∑ l, e l) ∧
      (∫⁻ omega, totalHistoryCost cost omega ∂reference) ≤ ∑ l, B l := by
  choose reference hprob htv hmean using hscalar
  letI : ∀ l, IsProbabilityMeasure (reference l) := fun l ↦ hprob l
  obtain ⟨hprodTV, hprodMean⟩ :=
    product_historyReference cost hcost actual reference e B htv hmean
  refine ⟨Measure.pi reference, inferInstance, hprodTV, hprodMean⟩

#print axioms product_historyReference
#print axioms exists_product_historyReference

end Ttc.CVIndependentHistoryReference
