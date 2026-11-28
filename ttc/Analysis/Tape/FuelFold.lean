/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.FuelLink

/-!
# The old loop with fuel approximates the old loop

The old step keeps the label invariant and a dyadic `p` (`realStep_dyInv`), so the loop's
kernels are almost everywhere measurable, and the approximation of the step composes over the
components (`approx_fold`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace ttc.Tape

open ArlibCommunity.Algorithms.CV18 (measurable_some)
open ttc (TTCState)

variable {d : ℕ}

/-! ## The old step's states -/

section RealInv

variable (Th : ℝ) (b : ℕ) (C : Measure (Fin d → ℤ)) [IsProbabilityMeasure C]

theorem appendLaw_eq (sec : TTCState d × ℕ) :
    appendLaw C b sec = (Measure.pi fun _ : Fin sec.2 => C).map
      (fun v => sec.1.addBatch fun i => ((b, v i) : ttc.LatticePoint d)) := by
  rw [appendLaw, ← Measure.pi_map_pi (fun _ => (measurable_of_countable _).aemeasurable),
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  rfl

theorem isProbabilityMeasure_appendLaw (sec : TTCState d × ℕ) :
    IsProbabilityMeasure (appendLaw C b sec) := by
  rw [appendLaw_eq]
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

theorem appendLaw_dyInv (c : NNReal) (sec : TTCState d × ℕ) (hs : DyInv b c sec.1) :
    ∀ᵐ s ∂appendLaw C b sec, DyInv b c s := by
  classical
  rw [appendLaw_eq, ae_map_iff (measurable_of_countable _).aemeasurable (measurableSet_dyInv b c)]
  refine ae_of_all _ fun v => ⟨⟨sec.1.labelsFresh_addBatch _ hs.1.1, fun c' hc' => ?_⟩, hs.2⟩
  simp only [ttc.TTCState.addBatch, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
    true_and] at hc'
  rcases hc' with hc' | ⟨i, rfl⟩
  · exact hs.1.2 c' hc'
  · rfl

theorem secondLoop_dyInv (s : TTCState d) (N : ℕ) (c : NNReal) (hs : DyInv b c s) :
    ∀ᵐ a ∂ttcPseudocode.secondLoop s N Th, DyInv b c a.1 := by
  classical
  have hm : MeasurableSet {a : TTCState d × ℕ | DyInv b c a.1} :=
    measurable_fst (measurableSet_dyInv b c)
  rw [ttcPseudocode.secondLoop, ae_map_iff (ttc.measurable_thinningResult s N Th).aemeasurable hm]
  refine ae_of_all _ fun coins => ?_
  obtain ⟨j, hj⟩ := hs.2
  refine ⟨⟨ttc.thinningResult_labelsFresh s N Th coins hs.1.1, fun c' hc' => hs.1.2 c' ?_⟩, ?_⟩
  · exact (Finset.mem_filter.mp hc').1
  · refine ⟨j + ttcPseudocode.secondLoopExitRound s N Th coins, ?_⟩
    show s.p / 2 ^ _ = _
    rw [hj, pow_add, div_div]

theorem oldInner_dyInv (y1 : TTCState d) (N : ℕ) (c : NNReal) (hy : DyInv b c y1) :
    ∀ᵐ s ∂oldInner Th C b y1 N, DyInv b c s :=
  ae_bind_of_ae (aemeasurable_secondLoop Th y1 N _) (measurableSet_dyInv b c)
    (secondLoop_dyInv Th b y1 N c hy) fun sec hsec => appendLaw_dyInv b C c sec hsec

theorem isProbabilityMeasure_oldInner (y1 : TTCState d) (N : ℕ) :
    IsProbabilityMeasure (oldInner Th C b y1 N) := by
  have := ttc.fairCoinStreamLaw_isProbabilityMeasure
  have : IsProbabilityMeasure (ttcPseudocode.secondLoop y1 N Th) :=
    Measure.isProbabilityMeasure_map (ttc.measurable_thinningResult y1 N Th).aemeasurable
  exact isProbabilityMeasure_bind (aemeasurable_secondLoop Th y1 N _)
    (ae_of_all _ fun sec => isProbabilityMeasure_appendLaw b C sec)

variable (P : ttc.PolytopeData d)

theorem gvGen_dyInv (y : TTCState d) (hy : StInv b y) (t : NNReal) :
    ∀ᵐ s ∂gvGen P Th (oldInner Th C b) y t, DyInv b y.p s := by
  refine ae_bind_of_ae (aemeasurable_rateCheck Th _ t _) (measurableSet_dyInv b y.p)
    (rateCheck_dyInv P Th b y t hy) fun y1 hy1 => ?_
  exact ae_bind_of_ae (P := fun _ => True) (measurable_of_countable _).aemeasurable
    (measurableSet_dyInv b y.p) (ae_of_all _ fun _ => trivial)
    fun N _ => oldInner_dyInv Th b C y1 N y.p hy1

theorem isProbabilityMeasure_gvGen (y : TTCState d) (t : NNReal) :
    IsProbabilityMeasure (gvGen P Th (oldInner Th C b) y t) := by
  have := ttc.fairCoinStreamLaw_isProbabilityMeasure
  have : IsProbabilityMeasure (ttcPseudocode.rateCheck (y.removeComponent P) t Th) :=
    Measure.isProbabilityMeasure_map (measurable_rateCheckResult _ t Th).aemeasurable
  exact isProbabilityMeasure_bind (aemeasurable_rateCheck Th _ t _) (ae_of_all _ fun y1 =>
    isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
      (ae_of_all _ fun N => isProbabilityMeasure_oldInner Th b C y1 N))

/-- The old step in the `gvGen` form. -/
abbrev realStep (hn : 3 ≤ d) (eta delta : ℝ) (y : TTCState d) : Measure (TTCState d) :=
  (ttc.communityCV18VolumeLaw hn P eta delta).bind fun vol =>
    gvGen P Th (oldInner Th C b) y (ttcPseudocode.t b d vol.2)

theorem measurable_gvGen_vol (y : TTCState d) :
    Measurable fun vol : ttc.VolumeOutcome =>
      gvGen P Th (oldInner Th C b) y (ttcPseudocode.t b d vol.2) :=
  (measurable_gvGen P Th _ y).comp (by unfold ttcPseudocode.t; fun_prop)

theorem realStep_dyInv (hn : 3 ≤ d) (eta delta : ℝ) (y : TTCState d) (hy : StInv b y) :
    ∀ᵐ s ∂realStep Th b C P hn eta delta y, DyInv b y.p s :=
  ae_bind_of_ae (P := fun _ => True) (measurable_gvGen_vol Th b C P y).aemeasurable
    (measurableSet_dyInv b y.p) (ae_of_all _ fun _ => trivial)
    fun vol _ => gvGen_dyInv Th b C P y hy _

theorem isProbabilityMeasure_realStep (hn : 3 ≤ d) (eta delta : ℝ)
    [IsProbabilityMeasure (ttc.communityCV18VolumeLaw hn P eta delta)] (y : TTCState d) :
    IsProbabilityMeasure (realStep Th b C P hn eta delta y) :=
  isProbabilityMeasure_bind (measurable_gvGen_vol Th b C P y).aemeasurable
    (ae_of_all _ fun vol => isProbabilityMeasure_gvGen Th b C P y _)

end RealInv

/-! ## The loop -/

section FoldApprox

theorem aemeasurable_of_dyadic_state {β : Type} [MeasurableSpace β] {μ : Measure (TTCState d)}
    {c : NNReal} (h : ∀ᵐ s ∂μ, ∃ j : ℕ, s.p = c / 2 ^ j) (f : TTCState d → β) :
    AEMeasurable f μ := by
  refine aemeasurable_of_countable_support (S := {s | ∃ j : ℕ, s.p = c / 2 ^ j}) ?_ (ae_iff.mp h) f
  refine (countable_range (fun w : ℕ × Finset (ttc.SampleCopy d) × ℕ =>
    (⟨c / 2 ^ w.1, w.2.1, w.2.2⟩ : TTCState d))).mono ?_
  rintro s ⟨j, hj⟩
  refine ⟨(j, s.X, s.nextLabel), ?_⟩
  show (⟨c / 2 ^ j, s.X, s.nextLabel⟩ : TTCState d) = s
  rw [← hj]

variable {k : ℕ} {F : ttc.LRAFormula d k} (hn : 3 ≤ d) (prep : ttc.TTCPreprocessor d k)
  (D : ttc.Decomposition F) (p : ttc.ApproxParams) (b' : ℕ)

theorem isProbabilityMeasure_oldFoldF (eta delta Th : ℝ) (fuel b : ℕ)
    (ν : ttc.PolytopeData d → Measure (Option (Fin d → ℤ)))
    (hprob : ∀ P, IsProbabilityMeasure (ν P))
    (hcv : ∀ P ∈ List.ofFn D.component,
      IsProbabilityMeasure (ttc.communityCV18VolumeLaw (by omega) P eta delta)) :
    ∀ Ps : List (ttc.PolytopeData d), (∀ P ∈ Ps, P ∈ List.ofFn D.component) →
      ∀ y, StInv b y → IsProbabilityMeasure (oldFoldF (by omega) eta delta Th fuel b ν Ps y)
  | [], _, y, _ => by
      simp only [oldFoldF]
      infer_instance
  | P :: rest, hPs, y, hy => by
      have := hcv P (hPs P List.mem_cons_self)
      have : IsProbabilityMeasure (oldStepF P Th fuel (ν P) b (by omega) eta delta y) :=
        isProbabilityMeasure_bind (measurable_gvF_vol P Th fuel (ν P) b y).aemeasurable
          (ae_of_all _ fun vol => isProbabilityMeasure_gvF P Th b (fun _ => ν P)
            (fun _ => hprob P) fuel y _)
      have hdy := oldStepF_dyInv (by omega) P Th fuel (ν P) b eta delta y hy
      simp only [oldFoldF]
      refine isProbabilityMeasure_bind (aemeasurable_of_dyadic
        (hdy.mono fun o ho s hs => (ho s hs).2) _) (hdy.mono fun o ho => ?_)
      rcases o with _ | y'
      · simp only [Option.elim]; infer_instance
      · exact isProbabilityMeasure_oldFoldF eta delta Th fuel b ν hprob hcv rest
          (fun Q hQ => hPs Q (List.mem_cons_of_mem P hQ)) y' (ho y' rfl).1

include hn in
/-- **The old loop with fuel approximates the old loop.** -/
theorem approx_fold :
    ∀ Ps : List (ttc.PolytopeData d), (∀ P ∈ Ps, P ∈ List.ofFn D.component) →
      ∀ y, StInv (ttc.GetPrecision D p.precisionEta) y →
        Approx (fun f => oldFoldF (by omega) p.ε' (p.δ' D.componentCount)
            (p.Thresh D.componentCount) f (ttc.GetPrecision D p.precisionEta)
            (samplerLaw (paramsOf D p) f b') Ps y)
          (ttcPseudocode.loop (ttc.ttcSubroutines hn prep) (ttc.GetPrecision D p.precisionEta)
            p.ε' (p.δ' D.componentCount) (p.Thresh D.componentCount) Ps y)
  | [], _, y, _ => by
      have := Approx.const (Measure.dirac y)
      rw [Measure.map_dirac' measurable_some] at this
      exact this
  | P :: rest, hPs, y, hy => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (hPs P List.mem_cons_self)
      set bP := ttc.GetPrecision D p.precisionEta
      set Th := p.Thresh D.componentCount
      have hn3 : 3 ≤ d := by omega
      have hTh : 0 ≤ Th := (p.threshold_pos _).le
      have hcvi := ttc.community_volume_isProbabilityMeasure hn D p prep i
      have hcv : ∀ Q ∈ List.ofFn D.component, IsProbabilityMeasure
          (ttc.communityCV18VolumeLaw (by omega) Q p.ε' (p.δ' D.componentCount)) := by
        intro Q hQ
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hQ
        exact ttc.community_volume_isProbabilityMeasure hn D p prep j
      have : IsProbabilityMeasure (ttc.communityCV18VolumeLaw (by omega) (D.component i) p.ε'
          (p.δ' D.componentCount)) := hcvi
      set C := condLaw (D.component i) bP p.ε'
      have := ttc.normalizedHitAndRunContinuousLaw_isProbabilityMeasure (by omega) (D.component i)
        bP p.ε'
      have := Arlib.KV97.isProbabilityMeasure_roundedMeasureLaw
        (ttc.normalizedHitAndRunContinuousLaw (D.component i) bP p.ε')
      have hC : IsProbabilityMeasure C :=
        isProbabilityMeasure_condOn _ _ (acceptance_pos hn D p i)
      have hroute := route_certified hn D p i
      have hstep : ttcPseudocode.step (ttc.ttcSubroutines hn prep) bP p.ε' (p.δ' D.componentCount)
          Th (D.component i) y = realStep Th bP C (D.component i) (by omega) p.ε'
            (p.δ' D.componentCount) y :=
        step_eq_gvGen hn prep (D.component i) bP p.ε' (p.δ' D.componentCount) Th hroute y
      have hA := approx_step (D.component i) Th hTh bP C
        (fun f => samplerLaw (paramsOf D p) f b' (D.component i)) (approx_samplerLaw hn D p i b')
        (fun f => isProbabilityMeasure_samplerLaw _ f b' _) hn3 p.ε'
        (p.δ' D.componentCount) y
      have := isProbabilityMeasure_realStep Th bP C (D.component i) hn3 p.ε'
        (p.δ' D.componentCount) y
      have hdyR := realStep_dyInv Th bP C (D.component i) (by omega) p.ε' (p.δ' D.componentCount)
        y hy
      show Approx _ ((ttcPseudocode.step (ttc.ttcSubroutines hn prep) bP p.ε'
        (p.δ' D.componentCount) Th (D.component i) y).bind _)
      rw [hstep]
      refine hA.bind (Kf := fun f => oldFoldF (by omega) p.ε' (p.δ' D.componentCount) Th f bP
          (samplerLaw (paramsOf D p) f b') rest) (fun f => ?_) (fun f => ?_) ?_ ?_ ?_ ?_
      · exact aemeasurable_of_dyadic ((oldStepF_dyInv (by omega) (D.component i) Th f _ bP p.ε'
          (p.δ' D.componentCount) y hy).mono fun o ho s hs => (ho s hs).2) _
      · exact aemeasurable_of_dyadic_state (hdyR.mono fun s hs => hs.2) _
      · exact aemeasurable_of_dyadic_state (hdyR.mono fun s hs => hs.2) _
      · exact hdyR.mono fun y' hy' f => (approx_fold rest
          (fun Q hQ => hPs Q (List.mem_cons_of_mem _ hQ)) y' hy'.1).sub f
      · exact hdyR.mono fun y' hy' => (approx_fold rest
          (fun Q hQ => hPs Q (List.mem_cons_of_mem _ hQ)) y' hy'.1).stop
      · intro f
        refine hdyR.mono fun y' hy' => ?_
        have := isProbabilityMeasure_oldFoldF hn D (eta := p.ε') (delta := p.δ' D.componentCount)
          (Th := Th) (fuel := f) (b := bP) (ν := samplerLaw (paramsOf D p) f b')
          (fun Q => isProbabilityMeasure_samplerLaw _ f b' Q) hcv rest
          (fun Q hQ => hPs Q (List.mem_cons_of_mem _ hQ)) y' hy'.1
        exact prob_le_one

end FoldApprox

end ttc.Tape
