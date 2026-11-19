import ttc.Analysis.OriginSourceStepMeasurable

/-! Joint measurability of the origin-label append operation. -/

namespace ttc

open MeasureTheory

theorem measurable_originAppend_joint :
    Measurable (fun z : (Nat × Nat × Nat) ×
        ((Nat → Nat × Nat) × (Nat → Nat)) =>
      originAppend z.2.1 z.1.1 z.1.2.1 z.1.2.2
        (fun i => z.2.2 i.val)) := by
  apply Measurable.of_eval
  intro label
  apply measurable_from_prod_countable_right
  intro params
  by_cases h : params.2.1 ≤ label ∧
      label < params.2.1 + params.2.2
  · have hindex : Measurable (fun z : (Nat → Nat × Nat) ×
        (Nat → Nat) => z.2 (label - params.2.1)) :=
      (measurable_pi_apply (label - params.2.1)).comp measurable_snd
    simpa [originAppend, h] using
      (measurable_const.prodMk hindex)
  · have horigin : Measurable (fun z : (Nat → Nat × Nat) ×
        (Nat → Nat) => z.1 label) :=
      (measurable_pi_apply label).comp measurable_fst
    simpa [originAppend, h] using horigin

end ttc
