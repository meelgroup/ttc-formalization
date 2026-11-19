import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Measure-theoretic bookkeeping for the model prelude

This module converts an almost-everywhere pointwise equivalence of set membership into
equality of the sets' measures.  It is independent of the model vocabulary so that the
audit surface can import the proof without creating an import cycle.
-/

open MeasureTheory

namespace ttc

/--
Almost-everywhere agreement of membership propositions implies equality of measures.

INTERNAL: Generic bridge from the decomposition's semantic certificate to measure equality.
-/
theorem measure_eq_of_mem_ae_iff {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s t : Set α} (h : ∀ᵐ x ∂μ, x ∈ s ↔ x ∈ t) :
    μ s = μ t := by
  refine MeasureTheory.measure_congr ?_
  filter_upwards [h] with x hx
  exact propext hx

end ttc
