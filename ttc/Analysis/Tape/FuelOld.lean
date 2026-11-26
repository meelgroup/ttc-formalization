/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.Approx

/-!
# The old pieces with fuel approximate the old pieces

The sampler with fuel approximates `GenerateSamples` (`approx_sampleKernel`), and the second
loop truncated at the fuel approximates the second loop (`approx_oldLaw`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace ttc.Tape

open ArlibCommunity.Algorithms.CV18 (measurable_some)
open ttc (TTCState)

variable {d : ℕ}

/-! ## Draws in sequence and independent draws -/

section ListLaw

/-- `k` independent draws from `μ`, as a list. -/
def listLaw (μ : Measure (Fin d → ℤ)) : ℕ → Measure (List (Fin d → ℤ))
  | 0 => Measure.dirac []
  | k + 1 => μ.bind fun z => (listLaw μ k).map (z :: ·)

theorem seqLaw_map_some (μ : Measure (Fin d → ℤ)) :
    ∀ k, seqLaw (μ.map some) k = (listLaw μ k).map some
  | 0 => by
      rw [seqLaw, listLaw, Measure.map_dirac' measurable_some]
  | k + 1 => by
      rw [seqLaw, listLaw, Measure.bind_map measurable_some.aemeasurable
        (measurable_of_countable _).aemeasurable, Measure.map_bind
          (measurable_of_countable _).aemeasurable measurable_some.aemeasurable]
      congr 1
      funext z
      simp only [Option.elim]
      rw [seqLaw_map_some μ k, Measure.map_map (measurable_of_countable _) measurable_some,
        Measure.map_map measurable_some (measurable_of_countable _)]
      rfl

theorem listLaw_singleton (μ : Measure (Fin d → ℤ)) :
    ∀ (k : ℕ) (l : List (Fin d → ℤ)),
      listLaw μ k {l} = if l.length = k then (l.map fun z => μ {z}).prod else 0
  | 0, l => by
      rcases l with _ | ⟨z, l⟩
      · simp [listLaw]
      · simp [listLaw, Measure.dirac_apply]
  | k + 1, l => by
      rw [listLaw, Measure.bind_apply (measurableSet_singleton l)
        (measurable_of_countable _).aemeasurable]
      have hm : ∀ z : Fin d → ℤ, Measurable fun l' : List (Fin d → ℤ) => z :: l' :=
        fun z => measurable_of_countable _
      simp_rw [Measure.map_apply (hm _) (measurableSet_singleton _)]
      rcases l with _ | ⟨w, l⟩
      · have h0 : ∀ a : Fin d → ℤ, (fun x : List (Fin d → ℤ) => a :: x) ⁻¹' {[]} = ∅ := by
          intro a; ext x; simp
        simp [h0]
      · have : ∀ z : Fin d → ℤ, listLaw μ k ((fun l' => z :: l') ⁻¹' {w :: l}) =
            ({w} : Set (Fin d → ℤ)).indicator (fun _ => listLaw μ k {l}) z := by
          intro z
          by_cases hz : z = w
          · subst hz
            rw [Set.indicator_of_mem (Set.mem_singleton z)]
            congr 1
            ext l'
            simp
          · rw [Set.indicator_of_notMem (by simpa using hz)]
            have : (fun l' => z :: l') ⁻¹' {w :: l} = ∅ := by
              ext l'
              simp [hz]
            rw [this, measure_empty]
        simp_rw [this]
        rw [lintegral_indicator_const (measurableSet_singleton w), listLaw_singleton μ k l]
        simp only [List.length_cons, Nat.add_right_cancel_iff, List.map_cons, List.prod_cons]
        split_ifs <;> simp [mul_comm]

/-- **Draws in sequence are independent draws.** -/
theorem listLaw_eq_pi (μ : Measure (Fin d → ℤ)) [SigmaFinite μ] (k : ℕ) :
    listLaw μ k = (Measure.pi fun _ : Fin k => μ).map List.ofFn := by
  rw [Measure.ext_iff_singleton]
  intro l
  rw [listLaw_singleton, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton l)]
  split_ifs with h
  · subst h
    have : List.ofFn ⁻¹' {l} = ({l.get} : Set (Fin l.length → Fin d → ℤ)) := by
      ext v
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hv; exact List.ofFn_injective (hv.trans (List.ofFn_get l).symm)
      · rintro rfl; exact List.ofFn_get l
    rw [this, Measure.pi_singleton, ← List.prod_ofFn]
    congr 1
    apply List.ext_get <;> simp
  · have : List.ofFn ⁻¹' {l} = (∅ : Set (Fin k → Fin d → ℤ)) := by
      ext v
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      rintro rfl
      exact h (List.length_ofFn)
    rw [this, measure_empty]

theorem isFiniteMeasure_listLaw (μ : Measure (Fin d → ℤ)) [IsProbabilityMeasure μ] :
    ∀ k, IsProbabilityMeasure (listLaw μ k)
  | 0 => by rw [listLaw]; infer_instance
  | k + 1 => by
      have := isFiniteMeasure_listLaw μ k
      rw [listLaw]
      exact isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
        (ae_of_all _ fun z => Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable)

/-- **`k` draws from approximating laws approximate `k` independent draws.** -/
theorem approx_seqLaw {ν : ℕ → Measure (Option (Fin d → ℤ))} {μ : Measure (Fin d → ℤ)}
    [IsProbabilityMeasure μ] (hν : Approx ν μ) (hprob : ∀ f, IsProbabilityMeasure (ν f)) :
    ∀ k, Approx (fun f => seqLaw (ν f) k) (listLaw μ k)
  | 0 => by
      have := Approx.const (Measure.dirac ([] : List (Fin d → ℤ)))
      rw [Measure.map_dirac' measurable_some] at this
      exact this
  | k + 1 => by
      have := isFiniteMeasure_listLaw μ k
      have ih := approx_seqLaw hν hprob k
      refine Approx.bind hν (fun f => (measurable_of_countable _).aemeasurable)
        (fun f => (measurable_of_countable _).aemeasurable) (measurable_of_countable _).aemeasurable
        (ae_of_all _ fun z f => (ih.map (g := (z :: ·)) (measurable_of_countable _)).sub f)
        (ae_of_all _ fun z => (ih.map (g := (z :: ·)) (measurable_of_countable _)).stop)
        (fun f => ae_of_all _ fun z => ?_)
      have := hprob f
      have := isProbabilityMeasure_seqLaw (ν f) k
      have := Measure.isProbabilityMeasure_map (μ := seqLaw (ν f) k)
        (f := Option.map (z :: ·)) (measurable_of_countable _).aemeasurable
      exact prob_le_one

end ListLaw

/-! ## The sampler with fuel -/

section Retry

/-- **Retrying until accepted with `f` attempts approximates the conditioned law.** -/
theorem approx_retry (R : Measure (Fin d → ℤ)) [IsProbabilityMeasure R] (A : Set (Fin d → ℤ))
    (hA : MeasurableSet A) (hpos : R A ≠ 0) :
    Approx (fun f => (∑ j ∈ Finset.range f, R Aᶜ ^ j) • (R.restrict A).map some +
        R Aᶜ ^ f • Measure.dirac none)
      (ArlibCommunity.Foundations.Convex.condOn R A) := by
  have hc : R Aᶜ = 1 - R A := prob_compl_eq_one_sub hA
  have hRA : R A ≤ 1 := prob_le_one
  have h1c : 1 - R Aᶜ = R A := by
    rw [hc, ENNReal.sub_sub_cancel ENNReal.one_ne_top hRA]
  have hnone : ∀ S : Set (Fin d → ℤ), (Measure.dirac (none : Option (Fin d → ℤ))) (some '' S) = 0 := by
    intro S
    rw [Measure.dirac_apply' _ (measurableSet_image_some (Set.to_countable S).measurableSet)]
    simp
  constructor
  · intro f
    rw [Measure.le_iff]
    intro S hS
    rw [comap_some_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.map_apply measurable_some (measurableSet_image_some hS),
      Set.preimage_image_eq _ (Option.some_injective _), hnone, smul_zero, add_zero,
      ArlibCommunity.Foundations.Convex.condOn, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ bot_le
    calc ∑ j ∈ Finset.range f, R Aᶜ ^ j ≤ ∑' j, R Aᶜ ^ j := ENNReal.sum_le_tsum _
      _ = (R A)⁻¹ := by rw [ENNReal.tsum_geometric, h1c]
  · have hlt : R Aᶜ < 1 := by
      rw [hc]
      exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hpos
    have : ∀ f, ((∑ j ∈ Finset.range f, R Aᶜ ^ j) • (R.restrict A).map some +
        R Aᶜ ^ f • Measure.dirac (none : Option (Fin d → ℤ))) {none} = R Aᶜ ^ f := by
      intro f
      have hs : (some : (Fin d → ℤ) → Option (Fin d → ℤ)) ⁻¹' {none} = ∅ := by ext; simp
      rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
        Measure.map_apply measurable_some measurableSet_none, hs, measure_empty,
        Measure.dirac_apply' _ measurableSet_none]
      simp
    simp only [this]
    exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt

end Retry

/-! ## The second loop with fuel -/

section Loop

/-- **The second loop truncated at the fuel approximates the second loop.** -/
theorem approx_oldLaw (Th : ℝ) (hTh : 0 ≤ Th) (s : TTCState d) (N : ℕ) :
    Approx (fun f => oldLaw Th f s N) (ttcPseudocode.secondLoop s N Th) := by
  classical
  have hres := ttc.measurable_thinningResult s N Th
  constructor
  · intro f
    rw [Measure.le_iff]
    intro S hS
    rw [comap_some_apply, oldLaw, Measure.map_apply (measurable_oldTrunc Th f s N)
      (measurableSet_image_some hS), ttcPseudocode.secondLoop, Measure.map_apply hres hS]
    refine measure_mono fun c hc => ?_
    simp only [Set.mem_preimage, oldTrunc] at hc ⊢
    split_ifs at hc
    · obtain ⟨x, hx, hxe⟩ := hc
      cases hxe
      exact hx
    · obtain ⟨x, _, hxe⟩ := hc
      cases hxe
  · have : ∀ f, oldLaw Th f s N {none} = fairCoinStreamLaw (exitBy Th s N f)ᶜ := by
      intro f
      rw [oldLaw, Measure.map_apply (measurable_oldTrunc Th f s N) measurableSet_none]
      congr 1
      ext c
      simp only [Set.mem_preimage, Set.mem_singleton_iff, oldTrunc, Set.mem_compl_iff, exitBy,
        Set.mem_ofPred_eq]
      split_ifs with h <;> simp [h]
    simp only [this]
    exact tendsto_noExit Th s N hTh

end Loop

/-! ## The samples appended -/

section Samples

theorem addBatch_congr (s : TTCState d) {c1 c2 : ℕ} (h : c1 = c2)
    (p1 : Fin c1 → ttc.LatticePoint d) (p2 : Fin c2 → ttc.LatticePoint d)
    (hp : ∀ i, p1 i = p2 (Fin.cast h i)) : s.addBatch p1 = s.addBatch p2 := by
  subst h
  congr
  funext i
  exact hp i

theorem addList_ofFn (b : ℕ) (s : TTCState d) {k : ℕ} (v : Fin k → Fin d → ℤ) :
    addList b s (List.ofFn v) = s.addBatch fun i => ((b, v i) : ttc.LatticePoint d) :=
  addBatch_congr s List.length_ofFn _ _ fun i => by simp; rfl

theorem isProbabilityMeasure_condOn (R : Measure (Fin d → ℤ)) [IsFiniteMeasure R]
    (A : Set (Fin d → ℤ)) (hpos : R A ≠ 0) :
    IsProbabilityMeasure (ArlibCommunity.Foundations.Convex.condOn R A) := by
  constructor
  rw [ArlibCommunity.Foundations.Convex.condOn, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul, ENNReal.inv_mul_cancel hpos (measure_ne_top R A)]

/-- **The samples appended with fuel approximate `GenerateSamples` appended.** -/
theorem approx_sampleKernel (R : Measure (Fin d → ℤ)) [IsProbabilityMeasure R]
    (A : Set (Fin d → ℤ)) (hpos : R A ≠ 0) (ν : ℕ → Measure (Option (Fin d → ℤ)))
    (hν : Approx ν (ArlibCommunity.Foundations.Convex.condOn R A))
    (hprob : ∀ f, IsProbabilityMeasure (ν f)) (b : ℕ) (sec : TTCState d × ℕ) :
    Approx (fun f => sampleKernel (ν f) b sec)
      ((Measure.pi fun _ : Fin sec.2 =>
        (ArlibCommunity.Foundations.Convex.condOn R A).map (ttc.encodeInteger b)).map
          sec.1.addBatch) := by
  have := isProbabilityMeasure_condOn R A hpos
  rw [← Measure.pi_map_pi (fun _ => (measurable_of_countable _).aemeasurable),
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  have heq : ((Measure.pi fun _ : Fin sec.2 =>
      ArlibCommunity.Foundations.Convex.condOn R A).map
        (sec.1.addBatch ∘ fun v i => ttc.encodeInteger b (v i))) =
      (listLaw (ArlibCommunity.Foundations.Convex.condOn R A) sec.2).map (addList b sec.1) := by
    rw [listLaw_eq_pi, Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    congr 1
    funext v
    simp only [Function.comp_apply, addList_ofFn]
    rfl
  rw [heq]
  exact (approx_seqLaw hν hprob sec.2).map (measurable_of_countable _)

end Samples

end ttc.Tape
