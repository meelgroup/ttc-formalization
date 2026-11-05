import Kr25Ssmxt.Analysis.ManuscriptOriginSourceStepMeasurable

/-! Joint measurability of the origin-label append operation. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem measurable_manuscriptOriginAppend_joint :
    Measurable (fun z : (Nat × Nat × Nat) ×
        ((Nat → Nat × Nat) × (Nat → Nat)) =>
      manuscriptOriginAppend z.2.1 z.1.1 z.1.2.1 z.1.2.2
        (fun i => z.2.2 i.val)) := by
  apply measurable_pi_lambda
  intro label
  apply measurable_from_prod_countable_right
  intro params
  by_cases h : params.2.1 ≤ label ∧
      label < params.2.1 + params.2.2
  · have hindex : Measurable (fun z : (Nat → Nat × Nat) ×
        (Nat → Nat) => z.2 (label - params.2.1)) :=
      (measurable_pi_apply (label - params.2.1)).comp measurable_snd
    simpa [manuscriptOriginAppend, h] using
      (measurable_const.prodMk hindex)
  · have horigin : Measurable (fun z : (Nat → Nat × Nat) ×
        (Nat → Nat) => z.1 label) :=
      (measurable_pi_apply label).comp measurable_fst
    simpa [manuscriptOriginAppend, h] using horigin

end Kr25Ssmxt
