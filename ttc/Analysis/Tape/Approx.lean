/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.Estimator

/-!
# Laws with fuel approximate laws without

A family `μ f` of laws that may stop (`none`) *approximates* a law `μ` when, for every fuel,
what it gives is at most `μ`, and its chance of stopping tends to `0` (`Approx`).  This
composes through binds (`Approx.bind`) and maps (`Approx.map`), and gives convergence on
every set (`Approx.tendsto`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace ttc.Tape

open ArlibCommunity.Algorithms.CV18 (measurable_some)

variable {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

theorem measurableEmbedding_some : MeasurableEmbedding (some : α → Option α) :=
  ⟨Option.some_injective _, measurable_some, fun _ hS => measurableSet_image_some hS⟩

/-- **A family of laws with fuel approximates a law.** -/
structure Approx (μf : ℕ → Measure (Option α)) (μ : Measure α) : Prop where
  sub : ∀ f, (μf f).comap some ≤ μ
  stop : Tendsto (fun f => μf f {none}) atTop (𝓝 0)

theorem comap_some_apply (ν : Measure (Option α)) (S : Set α) :
    ν.comap some S = ν (some '' S) :=
  measurableEmbedding_some.comap_apply ν S

/-- An integral over a law that may stop. -/
theorem lintegral_option' (ν : Measure (Option α)) (g : Option α → ENNReal) :
    ∫⁻ o, g o ∂ν = ∫⁻ a, g (some a) ∂(ν.comap some) + g none * ν {none} := by
  have hsplit : ν = ν.restrict (range some) + ν.restrict {none} := by
    rw [← Measure.restrict_union (by
        rw [Set.disjoint_left]; rintro _ ⟨a, rfl⟩ h; cases h) measurableSet_none,
      show range (some : α → Option α) ∪ {none} = univ by
        ext o; rcases o with _ | a <;> simp, Measure.restrict_univ]
  have hz : ∫⁻ o in {none}, g o ∂ν = g none * ν {none} := by
    rw [setLIntegral_congr_fun measurableSet_none (g := fun _ => g none) (fun o ho => by
      rw [Set.mem_singleton_iff] at ho; rw [ho]), setLIntegral_const]
  conv_lhs => rw [hsplit]
  rw [lintegral_add_measure, hz, ← measurableEmbedding_some.map_comap ν,
    measurableEmbedding_some.lintegral_map]

/-- An integral over a law that may stop, of a function that vanishes at `none`. -/
theorem lintegral_option (ν : Measure (Option α)) (g : Option α → ENNReal) (h0 : g none = 0) :
    ∫⁻ o, g o ∂ν = ∫⁻ a, g (some a) ∂(ν.comap some) := by
  rw [lintegral_option', h0, zero_mul, add_zero]

/-- **Approximation composes through a bind.** -/
theorem Approx.bind {μf : ℕ → Measure (Option α)} {μ : Measure α} [IsFiniteMeasure μ]
    (h : Approx μf μ) {Kf : ℕ → α → Measure (Option β)} {K : α → Measure β}
    (hKf : ∀ f, AEMeasurable (fun o => o.elim (Measure.dirac none) (Kf f)) (μf f))
    (hstopm : ∀ f, AEMeasurable (fun a => Kf f a {none}) μ) (hK : AEMeasurable K μ)
    (hsub : ∀ᵐ a ∂μ, ∀ f, (Kf f a).comap some ≤ K a)
    (hstop : ∀ᵐ a ∂μ, Tendsto (fun f => Kf f a {none}) atTop (𝓝 0))
    (hle1 : ∀ f, ∀ᵐ a ∂μ, Kf f a {none} ≤ 1) :
    Approx (fun f => (μf f).bind fun o => o.elim (Measure.dirac none) (Kf f)) (μ.bind K) where
  sub f := by
    rw [Measure.le_iff]
    intro S hS
    rw [comap_some_apply, Measure.bind_apply (measurableSet_image_some hS) (hKf f),
      Measure.bind_apply hS hK, lintegral_option _ _ (by
        simp only [Option.elim]
        rw [Measure.dirac_apply' _ (measurableSet_image_some hS)]
        simp)]
    calc ∫⁻ a, (Kf f a) (some '' S) ∂(μf f).comap some
        ≤ ∫⁻ a, (Kf f a) (some '' S) ∂μ := lintegral_mono' (h.sub f) le_rfl
      _ ≤ ∫⁻ a, K a S ∂μ := by
          refine lintegral_mono_ae (hsub.mono fun a ha => ?_)
          rw [← comap_some_apply]
          exact Measure.le_iff'.mp (ha f) S
  stop := by
    have hbound : ∀ f, ((μf f).bind fun o => o.elim (Measure.dirac none) (Kf f)) {none} ≤
        ∫⁻ a, Kf f a {none} ∂μ + μf f {none} := by
      intro f
      rw [Measure.bind_apply measurableSet_none (hKf f), lintegral_option']
      simp only [Option.elim]
      rw [Measure.dirac_apply' _ measurableSet_none]
      simp only [Set.indicator_of_mem (Set.mem_singleton none), Pi.one_apply, one_mul]
      exact add_le_add (lintegral_mono' (h.sub f) le_rfl) le_rfl
    have hdct : Tendsto (fun f => ∫⁻ a, Kf f a {none} ∂μ) atTop (𝓝 0) := by
      have := tendsto_lintegral_of_dominated_convergence' (fun _ => (1 : ENNReal)) hstopm
        hle1 (by simp [measure_ne_top]) hstop
      simpa using this
    have hsum := hdct.add h.stop
    rw [add_zero] at hsum
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun f => bot_le) hbound

/-- **A law without fuel approximates itself.** -/
theorem Approx.const (μ : Measure α) : Approx (fun _ => μ.map some) μ where
  sub f := by
    rw [Measure.le_iff]
    intro S hS
    rw [comap_some_apply, Measure.map_apply measurable_some (measurableSet_image_some hS),
      Set.preimage_image_eq _ (Option.some_injective _)]
  stop := by
    have : (some : α → Option α) ⁻¹' {none} = ∅ := by ext; simp
    simp only [Measure.map_apply measurable_some measurableSet_none, this, measure_empty]
    exact tendsto_const_nhds

/-- **Approximation survives a map.** -/
theorem Approx.map {μf : ℕ → Measure (Option α)} {μ : Measure α} (h : Approx μf μ) {g : α → β}
    (hg : Measurable g) : Approx (fun f => (μf f).map (Option.map g)) (μ.map g) where
  sub f := by
    rw [Measure.le_iff]
    intro S hS
    rw [comap_some_apply, Measure.map_apply (measurable_optionMap hg) (measurableSet_image_some hS),
      Measure.map_apply hg hS]
    have : Option.map g ⁻¹' (some '' S) = some '' (g ⁻¹' S) := by
      ext o
      rcases o with _ | a <;> simp
    rw [this, ← comap_some_apply]
    exact Measure.le_iff'.mp (h.sub f) _
  stop := by
    have : ∀ f, (μf f).map (Option.map g) {none} = μf f {none} := by
      intro f
      rw [Measure.map_apply (measurable_optionMap hg) measurableSet_none]
      congr 1
      ext o
      rcases o with _ | a <;> simp
    simp only [this]
    exact h.stop

end ttc.Tape
