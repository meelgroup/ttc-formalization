import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Mathlib 4.35 compatibility

Mathlib 4.35 removed `MeasureTheory.Measure.isProbabilityMeasure_map`, which took an
`AEMeasurable f μ` hypothesis: under the current definition of `Measure.map`,
`μ.map f` is a probability measure for every `f` (a non-measurable `f` maps to a
Dirac measure), and this is now an instance. This lemma restores the old name and
signature so existing call sites are unchanged; the hypothesis is ignored.
-/

namespace MeasureTheory.Measure

theorem isProbabilityMeasure_map {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} [IsProbabilityMeasure μ] {f : α → β}
    (_hf : AEMeasurable f μ) : IsProbabilityMeasure (μ.map f) :=
  inferInstance

end MeasureTheory.Measure

namespace MeasureTheory.Measure

/-- Mathlib 4.35 defines `μ.prod ν` by cases on `SFinite ν`; for s-finite `ν`
it is the familiar bind. Use this in place of unfolding `Measure.prod`. -/
theorem prod_eq_bind_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν] :
    μ.prod ν = μ.bind (fun x => ν.map (Prod.mk x)) := by
  rw [Measure.prod, ite_eq_left (inferInstance : SFinite ν)]

end MeasureTheory.Measure
