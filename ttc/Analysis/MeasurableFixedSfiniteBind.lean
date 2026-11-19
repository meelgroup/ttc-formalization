import Mathlib.MeasureTheory.Measure.Prod

/-!
# Measurability of a bind against a fixed s-finite measure

This isolates the parameterized-integration fact needed by the component kernel.
-/

namespace ttc

/--
Binding a fixed s-finite measure against a jointly measurable kernel is measurable in
the remaining parameter.

INTERNAL: generic Giry-monad bookkeeping for parameterized sample generation.
-/
lemma measurable_fixed_sfinite_bind {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : MeasureTheory.Measure Y) [MeasureTheory.SFinite μ]
    (K : X × Y → MeasureTheory.Measure Z) (hK : Measurable K) :
    Measurable (fun x => μ.bind fun y => K (x, y)) := by
  apply MeasureTheory.Measure.measurable_of_measurable_coe
  intro s hs
  have hsections : Measurable (fun z : X × Y => K z s) :=
    (MeasureTheory.Measure.measurable_coe hs).comp hK
  have hintegral : Measurable (fun x : X => ∫⁻ y, K (x, y) s ∂μ) :=
    hsections.lintegral_prod_right
  convert hintegral using 1
  funext x
  rw [MeasureTheory.Measure.bind_apply hs]
  exact (hK.comp (measurable_const.prodMk measurable_id)).aemeasurable

end ttc

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · reduced fixed-measure bind measurability to measurable parameterized lintegrals
-/
