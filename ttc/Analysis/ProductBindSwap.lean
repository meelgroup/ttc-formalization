import ttc.Analysis.MathlibCompat
import ttc.Analysis.FirstPoissonCoupling

/-! Swap two independent draws before a measurable continuation. -/

namespace ttc

open MeasureTheory

theorem measure_prod_bind_swap
    {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : α × β → Measure γ) (hK : Measurable K) :
    (μ.prod ν).bind K =
      (ν.prod μ).bind (fun pair => K pair.swap) := by
  conv_rhs => rw [← Measure.prod_swap]
  rw [bind_mapped_measure (μ.prod ν) Prod.swap measurable_swap
    (fun pair : β × α => K pair.swap)
    (hK.comp measurable_swap)]
  congr 1

/-- Two independent draws may be exchanged when their joint output map is
measurable. -/
theorem measure_bind_map_comm
    {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α × β → γ) (hf : Measurable f) :
    μ.bind (fun a => ν.map (fun b => f (a, b))) =
      ν.bind (fun b => μ.map (fun a => f (a, b))) := by
  have hleft : μ.bind (fun a => ν.map (fun b => f (a, b))) =
      (μ.prod ν).map f := by
    rw [Measure.prod_eq_bind_map]
    rw [map_bind_measure μ
      (fun a => ν.map (Prod.mk a)) f
      Measurable.map_prodMk_left.aemeasurable hf]
    congr 1
    funext a
    rw [Measure.map_map hf measurable_prodMk_left]
    rfl
  have hright : ν.bind (fun b => μ.map (fun a => f (a, b))) =
      (ν.prod μ).map (f ∘ Prod.swap) := by
    rw [Measure.prod_eq_bind_map]
    rw [map_bind_measure ν
      (fun b => μ.map (Prod.mk b)) (f ∘ Prod.swap)
      Measurable.map_prodMk_left.aemeasurable
      (hf.comp measurable_swap)]
    congr 1
    funext b
    rw [Measure.map_map (hf.comp measurable_swap) measurable_prodMk_left]
    rfl
  calc
    μ.bind (fun a => ν.map (fun b => f (a, b))) =
      (μ.prod ν).map f := hleft
    _ = ((ν.prod μ).map Prod.swap).map f := by rw [Measure.prod_swap]
    _ = (ν.prod μ).map (f ∘ Prod.swap) := by
          rw [Measure.map_map hf measurable_swap]
    _ = _ := hright.symm

end ttc
