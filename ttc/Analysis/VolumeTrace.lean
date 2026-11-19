import ttc.Analysis.MathlibCompat
import ttc.Analysis.CostedMeasureMonad
import ttc.Analysis.VolumeOutcomeUnion
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-! Keep the CV18 outcome beside a subsequent randomized continuation.
For a normalized continuation, forgetting the state recovers exactly the
original CV18 law. -/

namespace ttc

open MeasureTheory

noncomputable def volumeTracedContinuation {ω σ : Type*}
    [MeasurableSpace ω] [MeasurableSpace σ]
    (law : Measure ω)
    (next : ω → Measure σ) :
    Measure (ω × σ) :=
  law.bind fun o => (next o).map (fun state => (o, state))

theorem measurable_volumeTrace_map
    {ω σ : Type*} [MeasurableSpace ω] [MeasurableSpace σ]
    (next : ω → Measure σ)
    (hnext : Measurable next)
    (hprob : ∀ o, IsProbabilityMeasure (next o)) :
    Measurable (fun o => (next o).map (fun state => (o, state))) := by
  let κ : ProbabilityTheory.Kernel ω σ := ⟨next, hnext⟩
  letI : ProbabilityTheory.IsMarkovKernel κ := ⟨hprob⟩
  apply Measure.measurable_of_measurable_coe
  intro event hevent
  simp_rw [Measure.map_apply measurable_prodMk_left hevent]
  exact ProbabilityTheory.Kernel.measurable_kernel_prodMk_left (κ := κ) hevent

/-- Mapping a probability kernel with a measurable function that also
depends on its input is measurable. -/
theorem measurable_parametric_probability_map
    {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (law : α → Measure β)
    (hlaw : Measurable law)
    (hprob : ∀ a, IsProbabilityMeasure (law a))
    (f : α × β → γ) (hf : Measurable f) :
    Measurable (fun a => (law a).map (fun b => f (a, b))) := by
  let κ : ProbabilityTheory.Kernel α β := ⟨law, hlaw⟩
  letI : ProbabilityTheory.IsMarkovKernel κ := ⟨hprob⟩
  apply Measure.measurable_of_measurable_coe
  intro event hevent
  have heq : (fun a => ((law a).map (fun b => f (a, b))) event) =
      fun a => law a ((fun b => f (a, b)) ⁻¹' event) := by
    funext a
    have hfa : Measurable (fun b : β => f (a, b)) := by
      simpa only [Function.comp_def] using hf.comp measurable_prodMk_left
    rw [Measure.map_apply hfa hevent]
  rw [heq]
  exact ProbabilityTheory.Kernel.measurable_kernel_prodMk_left
    (κ := κ) (hf hevent)

theorem measurable_parametric_probability_bind
    {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (first : α → Measure β)
    (hfirst : Measurable first)
    (hprob : ∀ a, IsProbabilityMeasure (first a))
    (next : α × β → Measure γ)
    (hnext : Measurable next) :
    Measurable (fun a => (first a).bind fun b => next (a, b)) := by
  let κ : ProbabilityTheory.Kernel α β := ⟨first, hfirst⟩
  letI : ProbabilityTheory.IsMarkovKernel κ := ⟨hprob⟩
  apply Measure.measurable_of_measurable_coe
  intro event hevent
  have hsection : Measurable (fun z : α × β => next z event) :=
    (Measure.measurable_coe hevent).comp hnext
  have hint : Measurable (fun a : α => ∫⁻ b, next (a, b) event ∂first a) :=
    by
      convert (Measurable.lintegral_kernel_prod_right' (κ := κ) hsection) using 1
  convert hint using 1
  funext a
  rw [Measure.bind_apply hevent]
  exact (hnext.comp (measurable_const.prodMk measurable_id)).aemeasurable

theorem bind_mapped_measure
    {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (source : Measure α) (f : α → β) (hf : Measurable f)
    (K : β → Measure γ) (hK : Measurable K) :
    (source.map f).bind K = source.bind fun x => K (f x) := by
  calc
    (source.map f).bind K =
        (source.bind fun x => Measure.dirac (f x)).bind K := by
          rw [Measure.bind_dirac_eq_map source hf]
    _ = source.bind fun x => (Measure.dirac (f x)).bind K :=
      Measure.bind_bind ((Measure.measurable_dirac.comp hf).aemeasurable)
        hK.aemeasurable
    _ = source.bind fun x => K (f x) := by
      simp only [Measure.dirac_bind hK]

theorem volumeTracedContinuation_fst
    {ω σ : Type*} [MeasurableSpace ω] [MeasurableSpace σ]
    (law : Measure ω)
    (next : ω → Measure σ)
    (hnext : Measurable next)
    (hprob : ∀ o, IsProbabilityMeasure (next o)) :
    (volumeTracedContinuation law next).map Prod.fst = law := by
  rw [volumeTracedContinuation]
  rw [map_bind_measure law
    (fun o => (next o).map (fun state => (o, state)))
    Prod.fst]
  · have hconst (o : ω) :
        ((next o).map (fun state => (o, state))).map Prod.fst =
          Measure.dirac o := by
      letI : IsProbabilityMeasure (next o) := hprob o
      rw [Measure.map_map measurable_fst measurable_prodMk_left]
      change (next o).map (fun _ : σ => o) = Measure.dirac o
      rw [Measure.map_const]
      simp
    simp_rw [hconst]
    simp
  · exact (measurable_volumeTrace_map next hnext hprob).aemeasurable
  · exact measurable_fst

theorem volumeTracedContinuation_snd
    {ω σ : Type*} [MeasurableSpace ω] [MeasurableSpace σ]
    (law : Measure ω)
    (next : ω → Measure σ)
    (hnext : Measurable next)
    (hprob : ∀ o, IsProbabilityMeasure (next o)) :
    (volumeTracedContinuation law next).map Prod.snd = law.bind next := by
  rw [volumeTracedContinuation]
  rw [map_bind_measure law
    (fun o => (next o).map (fun state => (o, state)))
    Prod.snd (measurable_volumeTrace_map next hnext hprob).aemeasurable
      measurable_snd]
  congr 1
  funext o
  rw [Measure.map_map measurable_snd measurable_prodMk_left]
  simpa only [Function.comp_def, Prod.snd] using
    (Measure.map_id' (μ := next o))

/-- Keep the first charged result in a `costedBind` while the second
coordinate remains exactly the ordinary charged continuation. -/
noncomputable def costedBindTrace {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (first : Measure (α × Nat))
    (next : α → Measure (β × Nat)) :
    Measure ((α × Nat) × (β × Nat)) :=
  volumeTracedContinuation first fun result =>
    (next result.1).map fun continuation =>
      (continuation.1, result.2 + continuation.2)

theorem measurable_costedTrace_tail {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (next : α → Measure (β × Nat)) (hnext : Measurable next) :
    Measurable (fun result : α × Nat =>
      (next result.1).map fun continuation =>
        (continuation.1, result.2 + continuation.2)) := by
  apply measurable_from_prod_countable_left
  intro cost
  exact (Measure.measurable_map
    (fun continuation : β × Nat =>
      (continuation.1, cost + continuation.2)) (by fun_prop)).comp hnext

theorem costedBindTrace_fst {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (first : Measure (α × Nat))
    (next : α → Measure (β × Nat))
    (hnext : Measurable next)
    (hprob : ∀ x, IsProbabilityMeasure (next x)) :
    (costedBindTrace first next).map Prod.fst = first := by
  exact volumeTracedContinuation_fst first _
    (measurable_costedTrace_tail next hnext)
    (fun result => by
      letI : IsProbabilityMeasure (next result.1) := hprob result.1
      exact Measure.isProbabilityMeasure_map (by fun_prop))

theorem costedBindTrace_snd {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (first : Measure (α × Nat))
    (next : α → Measure (β × Nat))
    (hnext : Measurable next)
    (hprob : ∀ x, IsProbabilityMeasure (next x)) :
    (costedBindTrace first next).map Prod.snd = costedBind first next := by
  exact volumeTracedContinuation_snd first _
    (measurable_costedTrace_tail next hnext)
    (fun result => by
      letI : IsProbabilityMeasure (next result.1) := hprob result.1
      exact Measure.isProbabilityMeasure_map (by fun_prop))

theorem costedBindTrace_isProbabilityMeasure {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (first : Measure (α × Nat)) [IsProbabilityMeasure first]
    (next : α → Measure (β × Nat))
    (hnext : Measurable next)
    (hprob : ∀ x, IsProbabilityMeasure (next x)) :
    IsProbabilityMeasure (costedBindTrace first next) := by
  unfold costedBindTrace volumeTracedContinuation
  let K : (α × Nat) → Measure (β × Nat) := fun result =>
    (next result.1).map fun continuation =>
      (continuation.1, result.2 + continuation.2)
  have hK : Measurable K := measurable_costedTrace_tail next hnext
  apply isProbabilityMeasure_bind
    (measurable_volumeTrace_map K hK (fun result => by
      letI : IsProbabilityMeasure (next result.1) := hprob result.1
      exact Measure.isProbabilityMeasure_map (by fun_prop))).aemeasurable
  filter_upwards with result
  letI : IsProbabilityMeasure (next result.1) := hprob result.1
  haveI : IsProbabilityMeasure (K result) := by
    dsimp only [K]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  exact Measure.isProbabilityMeasure_map (by fun_prop)

end ttc
