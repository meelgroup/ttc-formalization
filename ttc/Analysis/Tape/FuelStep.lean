/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.FuelOld

/-!
# The old step with fuel approximates the old step

Composing the pieces: the tail after the rate check (`approx_tail`), the step after the
volume estimate (`approx_gv`) and the step (`approx_step`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace ttc.Tape

open ArlibCommunity.Algorithms.CV18 (measurable_some)
open ttc (TTCState)

variable {d : ℕ}

section Generic

variable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]

/-- **Approximation through a bind against a law without fuel.** -/
theorem Approx.bind_const {μ : Measure α} [IsFiniteMeasure μ] {Kf : ℕ → α → Measure (Option β)}
    {K : α → Measure β} (hKf : ∀ f, AEMeasurable (Kf f) μ)
    (hstopm : ∀ f, AEMeasurable (fun a => Kf f a {none}) μ) (hK : AEMeasurable K μ)
    (hsub : ∀ᵐ a ∂μ, ∀ f, (Kf f a).comap some ≤ K a)
    (hstop : ∀ᵐ a ∂μ, Tendsto (fun f => Kf f a {none}) atTop (𝓝 0))
    (hle1 : ∀ f a, Kf f a {none} ≤ 1) :
    Approx (fun f => μ.bind (Kf f)) (μ.bind K) := by
  have hKf' : ∀ f, AEMeasurable (fun o : Option α => o.elim (Measure.dirac none) (Kf f))
      (μ.map some) := fun f =>
    (measurableEmbedding_some.aemeasurable_map_iff).mpr (hKf f)
  have := (Approx.const μ).bind hKf' hstopm hK hsub hstop hle1
  convert this using 2 with f
  rw [Measure.bind_map measurable_some.aemeasurable (hKf' f)]
  rfl

end Generic

/-! ## The second loop lives on countably many results -/

theorem countable_range_secondLoopResult (Th : ℝ) (s : TTCState d) (N : ℕ) :
    (range (ttcPseudocode.secondLoopResult s N Th)).Countable := by
  refine (countable_range (fun w : ℕ × Finset (ttc.SampleCopy d) × ℕ =>
    ((⟨s.p / 2 ^ w.1, w.2.1, s.nextLabel⟩ : TTCState d), w.2.2))).mono ?_
  rintro _ ⟨c, rfl⟩
  exact ⟨(ttcPseudocode.secondLoopExitRound s N Th c,
    samplesAfter c (ttcPseudocode.secondLoopExitRound s N Th c) s.X,
    pendingAfter c (ttcPseudocode.secondLoopExitRound s N Th c) s.nextLabel N), rfl⟩

theorem aemeasurable_secondLoop (Th : ℝ) (s : TTCState d) (N : ℕ) {β : Type} [MeasurableSpace β]
    (g : TTCState d × ℕ → β) : AEMeasurable g (ttcPseudocode.secondLoop s N Th) :=
  aemeasurable_map_of_countable_range (ttc.measurable_thinningResult s N Th)
    (countable_range_secondLoopResult Th s N) g

/-! ## The step after the volume, for any tail -/

section Gen

variable (P : ttc.PolytopeData d) (Th : ℝ) {β : Type} [MeasurableSpace β]

/-- The step after the volume estimate, with the tail after the Poisson draw left open. -/
def gvGen (H : TTCState d → ℕ → Measure β) (y : TTCState d) (t : NNReal) : Measure β :=
  (ttcPseudocode.rateCheck (y.removeComponent P) t Th).bind fun y1 =>
    (ttc.Poisson (t * y1.p)).bind (H y1)

theorem measurable_gvGen (H : TTCState d → ℕ → Measure β) (y : TTCState d) :
    Measurable (gvGen P Th H y) := by
  classical
  have := ttc.fairCoinStreamLaw_isProbabilityMeasure
  have htail : ∀ y1 : TTCState d, Measurable fun t : NNReal =>
      (ttc.Poisson (t * y1.p)).bind (H y1) := fun y1 =>
    (Measure.measurable_bind' (measurable_of_countable _)).comp
      (ttc.measurable_poissonMeasure.comp (measurable_id.mul_const _))
  rcases hy : y.removeComponent P with ⟨p', X', nl'⟩
  let Φ : NNReal × ℕ → Measure β := fun z =>
    fairCoinStreamLaw.bind fun c =>
      (ttc.Poisson (z.1 * (p' / 2 ^ z.2))).bind (H ⟨p' / 2 ^ z.2, samplesAfter c z.2 X', nl'⟩)
  have hΦ : Measurable Φ := by
    apply measurable_from_prod_countable_left
    intro k
    let Ψ : NNReal × Finset (ttc.SampleCopy d) → Measure β := fun z =>
      (ttc.Poisson (z.1 * (p' / 2 ^ k))).bind (H ⟨p' / 2 ^ k, z.2, nl'⟩)
    have hΨ : Measurable Ψ := by
      refine measurable_from_prod_countable_left fun X => ?_
      exact htail (⟨p' / 2 ^ k, X, nl'⟩ : TTCState d)
    have hpair : Measurable fun z : NNReal × (ℕ × ℕ → Bool) => (z.1, samplesAfter z.2 k X') :=
      measurable_fst.prodMk ((ttc.measurable_samplesAfter_fixed k X').comp measurable_snd)
    exact ttc.measurable_fixed_sfinite_bind fairCoinStreamLaw
      (fun z : NNReal × (ℕ × ℕ → Bool) => Ψ (z.1, samplesAfter z.2 k X')) (hΨ.comp hpair)
  have heq : gvGen P Th H y =
      fun t => Φ (t, ttcPseudocode.rateHalvings ⟨p', X', nl'⟩ t Th) := by
    funext t
    rw [gvGen, hy, ttcPseudocode.rateCheck, Measure.bind_map
      (measurable_rateCheckResult _ t Th).aemeasurable (aemeasurable_rateCheck Th _ t _)]
    rfl
  rw [heq]
  exact hΦ.comp (measurable_id.prodMk (measurable_rateHalvings Th _))

end Gen

/-! ## Composing -/

section Compose

variable (P : ttc.PolytopeData d) (Th : ℝ) (hTh : 0 ≤ Th) (b : ℕ)
  (C : Measure (Fin d → ℤ)) [IsProbabilityMeasure C]
  (ν : ℕ → Measure (Option (Fin d → ℤ))) (hν : Approx ν C) (hprob : ∀ f, IsProbabilityMeasure (ν f))

/-- `GenerateSamples` appended, at the conditioned point law `C`. -/
def appendLaw (C : Measure (Fin d → ℤ)) (b : ℕ) (sec : TTCState d × ℕ) : Measure (TTCState d) :=
  (Measure.pi fun _ : Fin sec.2 => C.map (ttc.encodeInteger b)).map sec.1.addBatch

/-- The old tail after the Poisson draw. -/
def oldInner (Th : ℝ) (C : Measure (Fin d → ℤ)) (b : ℕ) (y1 : TTCState d) (N : ℕ) :
    Measure (TTCState d) :=
  (ttcPseudocode.secondLoop y1 N Th).bind (appendLaw C b)

include hprob in
theorem isProbabilityMeasure_sampleKernel (f : ℕ) (sec : TTCState d × ℕ) :
    IsProbabilityMeasure (sampleKernel (ν f) b sec) := by
  have := hprob f
  have := isProbabilityMeasure_seqLaw (ν f) sec.2
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

include hprob in
theorem isProbabilityMeasure_fuelInner (f : ℕ) (y1 : TTCState d) (N : ℕ) :
    IsProbabilityMeasure ((oldLaw Th f y1 N).bind fun o =>
      o.elim (Measure.dirac none) (sampleKernel (ν f) b)) := by
  have := ttc.fairCoinStreamLaw_isProbabilityMeasure
  have : IsProbabilityMeasure (oldLaw Th f y1 N) :=
    Measure.isProbabilityMeasure_map (measurable_oldTrunc Th f y1 N).aemeasurable
  refine isProbabilityMeasure_bind (aemeasurable_oldLaw Th f y1 N _) (ae_of_all _ fun o => ?_)
  rcases o with _ | sec
  · simp only [Option.elim]; infer_instance
  · exact isProbabilityMeasure_sampleKernel b ν hprob f sec

include hprob in
theorem isProbabilityMeasure_oldTail (f : ℕ) (t : NNReal) (y1 : TTCState d) :
    IsProbabilityMeasure (oldTail Th f (ν f) b t y1) :=
  isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
    (ae_of_all _ fun N => isProbabilityMeasure_fuelInner Th b ν hprob f y1 N)

include hprob in
theorem isProbabilityMeasure_gvF (f : ℕ) (y : TTCState d) (t : NNReal) :
    IsProbabilityMeasure (gvF P Th f (ν f) b y t) := by
  have := ttc.fairCoinStreamLaw_isProbabilityMeasure
  have : IsProbabilityMeasure (ttcPseudocode.rateCheck (y.removeComponent P) t Th) :=
    Measure.isProbabilityMeasure_map (measurable_rateCheckResult _ t Th).aemeasurable
  exact isProbabilityMeasure_bind (aemeasurable_rateCheck Th _ t _)
    (ae_of_all _ fun y1 => isProbabilityMeasure_oldTail Th b ν hprob f t y1)

include hTh hν hprob in
theorem approx_inner (y1 : TTCState d) (N : ℕ) :
    Approx (fun f => (oldLaw Th f y1 N).bind fun o =>
        o.elim (Measure.dirac none) (sampleKernel (ν f) b))
      (oldInner Th C b y1 N) := by
  have := ttc.fairCoinStreamLaw_isProbabilityMeasure
  have : IsProbabilityMeasure (ttcPseudocode.secondLoop y1 N Th) :=
    Measure.isProbabilityMeasure_map (ttc.measurable_thinningResult y1 N Th).aemeasurable
  have hC : ArlibCommunity.Foundations.Convex.condOn C univ = C := by
    rw [ArlibCommunity.Foundations.Convex.condOn, Measure.restrict_univ, measure_univ, inv_one,
      one_smul]
  have hν' : Approx ν (ArlibCommunity.Foundations.Convex.condOn C univ) := by rwa [hC]
  have hsk := fun sec => approx_sampleKernel C univ (by simp) ν hν' hprob b sec
  simp only [hC] at hsk
  exact (approx_oldLaw Th hTh y1 N).bind (fun f => aemeasurable_oldLaw Th f y1 N _)
    (fun f => aemeasurable_secondLoop Th y1 N _) (aemeasurable_secondLoop Th y1 N _)
    (ae_of_all _ fun sec f => (hsk sec).sub f) (ae_of_all _ fun sec => (hsk sec).stop)
    (fun f sec => by have := isProbabilityMeasure_sampleKernel b ν hprob f sec; exact prob_le_one)

include hTh hν hprob in
theorem approx_tail (t : NNReal) (y1 : TTCState d) :
    Approx (fun f => oldTail Th f (ν f) b t y1)
      ((ttc.Poisson (t * y1.p)).bind (oldInner Th C b y1)) :=
  Approx.bind_const (fun f => (measurable_of_countable _).aemeasurable)
    (fun f => (measurable_of_countable _).aemeasurable) (measurable_of_countable _).aemeasurable
    (ae_of_all _ fun N f => (approx_inner Th hTh b C ν hν hprob y1 N).sub f)
    (ae_of_all _ fun N => (approx_inner Th hTh b C ν hν hprob y1 N).stop)
    (fun f N => by have := isProbabilityMeasure_fuelInner Th b ν hprob f y1 N; exact prob_le_one)

include hTh hν hprob in
theorem approx_gv (y : TTCState d) (t : NNReal) :
    Approx (fun f => gvF P Th f (ν f) b y t) (gvGen P Th (oldInner Th C b) y t) := by
  have := ttc.fairCoinStreamLaw_isProbabilityMeasure
  have : IsProbabilityMeasure (ttcPseudocode.rateCheck (y.removeComponent P) t Th) :=
    Measure.isProbabilityMeasure_map (measurable_rateCheckResult _ t Th).aemeasurable
  exact Approx.bind_const (fun f => aemeasurable_rateCheck Th _ t _)
    (fun f => aemeasurable_rateCheck Th _ t _) (aemeasurable_rateCheck Th _ t _)
    (ae_of_all _ fun y1 f => (approx_tail Th hTh b C ν hν hprob t y1).sub f)
    (ae_of_all _ fun y1 => (approx_tail Th hTh b C ν hν hprob t y1).stop)
    (fun f y1 => by have := isProbabilityMeasure_oldTail Th b ν hprob f t y1; exact prob_le_one)

include hTh hν hprob in
/-- **The old step with fuel approximates the old step.** -/
theorem approx_step (hn : 3 ≤ d) (eta delta : ℝ)
    [IsProbabilityMeasure (ttc.communityCV18VolumeLaw hn P eta delta)] (y : TTCState d) :
    Approx (fun f => oldStepF P Th f (ν f) b hn eta delta y)
      ((ttc.communityCV18VolumeLaw hn P eta delta).bind fun vol =>
        gvGen P Th (oldInner Th C b) y (ttcPseudocode.t b d vol.2)) := by
  have ht : Measurable fun vol : ttc.VolumeOutcome => ttcPseudocode.t b d vol.2 := by
    unfold ttcPseudocode.t; fun_prop
  exact Approx.bind_const (fun f => (measurable_gvF_vol P Th f (ν f) b y).aemeasurable)
    (fun f => ((Measure.measurable_coe measurableSet_none).comp
      (measurable_gvF_vol P Th f (ν f) b y)).aemeasurable)
    ((measurable_gvGen P Th _ y).comp ht).aemeasurable
    (ae_of_all _ fun vol f => (approx_gv P Th hTh b C ν hν hprob y _).sub f)
    (ae_of_all _ fun vol => (approx_gv P Th hTh b C ν hν hprob y _).stop)
    (fun f vol => by have := isProbabilityMeasure_gvF P Th b ν hprob f y
                       (ttcPseudocode.t b d vol.2); exact prob_le_one)

end Compose

end ttc.Tape
