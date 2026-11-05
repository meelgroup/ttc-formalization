import Kr25Ssmxt.Analysis.ManuscriptOriginRefreshedKernel
import Kr25Ssmxt.Analysis.ManuscriptProductBindSwap

/-! Exchange independent source draws around a jointly measurable
measure-valued continuation. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem measure_prod_bind_eq_nested
    {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β)
    [SFinite ν]
    (K : α × β → Measure γ) (hK : Measurable K) :
    (μ.prod ν).bind K =
      μ.bind (fun a => ν.bind (fun b => K (a, b))) := by
  rw [Measure.prod]
  rw [Measure.bind_bind Measurable.map_prodMk_left.aemeasurable
    hK.aemeasurable]
  congr 1
  funext a
  exact bind_mapped_measure ν (Prod.mk a) measurable_prodMk_left K hK

theorem measure_independent_bind_comm
    {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : α × β → Measure γ) (hK : Measurable K) :
    μ.bind (fun a => ν.bind (fun b => K (a, b))) =
      ν.bind (fun b => μ.bind (fun a => K (a, b))) := by
  calc
    μ.bind (fun a => ν.bind (fun b => K (a, b))) =
      (μ.prod ν).bind K :=
        (measure_prod_bind_eq_nested μ ν K hK).symm
    _ = (ν.prod μ).bind (fun pair => K pair.swap) :=
      measure_prod_bind_swap μ ν K hK
    _ = ν.bind (fun b => μ.bind (fun a => K (a, b))) :=
      measure_prod_bind_eq_nested ν μ (fun pair => K pair.swap)
        (hK.comp measurable_swap)

end Kr25Ssmxt
