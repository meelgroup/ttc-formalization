/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.FuelMono
import ttc.Analysis.Tape.Bridge
import ttc.Analysis.TTCProbabilityMeasure
import ttc.Analysis.TTCSimulation

/-!
# The sealed program has the old model's output law

With fuel `f` the sealed program's output law approximates the old `ttc` law
(`approx_output`).  Run with the fuel it needs, the program gives on each tape the output of
any run that finishes (`FuelLE`), and the runs that never finish have probability zero; so
its output law is exactly the old one (`estimate_eq_ttc`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ttc.Tape.Tree
open ttc (TTCState)
open ArlibCommunity.Algorithms.CV18 (measurable_some)

variable {d k : ℕ}

/-! ## Convergence on every set -/

theorem Approx.tendsto {α : Type} [MeasurableSpace α] {μf : ℕ → Measure (Option α)}
    {μ : Measure α} [∀ f, IsProbabilityMeasure (μf f)] [IsProbabilityMeasure μ]
    (h : Approx μf μ) {S : Set α} (hS : MeasurableSet S) :
    Tendsto (fun f => μf f (some '' S)) atTop (𝓝 (μ S)) := by
  have hup : ∀ f, μf f (some '' S) ≤ μ S := fun f => by
    rw [← comap_some_apply]; exact Measure.le_iff'.mp (h.sub f) S
  have hlow : ∀ f, μ S ≤ μf f (some '' S) + μf f {none} := by
    intro f
    have hSc : μf f (some '' Sᶜ) ≤ μ Sᶜ := by
      rw [← comap_some_apply]; exact Measure.le_iff'.mp (h.sub f) Sᶜ
    have hpart : μf f (some '' S) + μf f (some '' Sᶜ) + μf f {none} = 1 := by
      rw [← measure_union (by
          rw [Set.disjoint_left]; rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, he⟩
          cases Option.some_injective _ he; exact hb ha)
          (measurableSet_image_some hS.compl),
        ← measure_union (by
          rw [Set.disjoint_left]; rintro _ (⟨a, _, rfl⟩ | ⟨a, _, rfl⟩) h <;> cases h)
          measurableSet_none]
      convert measure_univ (μ := μf f)
      ext o
      rcases o with _ | a
      · simp
      · by_cases ha : a ∈ S <;> simp
    have h2 := measure_add_measure_compl (μ := μ) hS
    rw [measure_univ] at h2
    have : μ S + μ Sᶜ ≤ μf f (some '' S) + μf f {none} + μ Sᶜ := by
      rw [h2, ← hpart, add_right_comm]
      exact add_le_add le_rfl hSc
    exact (ENNReal.add_le_add_iff_right (measure_ne_top μ Sᶜ)).mp this
  have hlim : Tendsto (fun f => μ S - μf f {none}) atTop (𝓝 (μ S - 0)) :=
    ENNReal.Tendsto.sub tendsto_const_nhds h.stop (Or.inl (measure_ne_top μ S))
  rw [tsub_zero] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds
    (fun f => tsub_le_iff_right.mpr (hlow f)) hup

/-! ## The output law with fuel -/

section Output

variable {F : ttc.LRAFormula d k}

/-- The output read off a run. -/
def outOf (o : Option (Num ℝ)) : Option NNReal := o.map fun x => Real.toNNReal x.get

theorem measurable_outOf : Measurable outOf :=
  measurable_optionMap (measurable_real_toNNReal.comp Num.measurable_get)

/-- **With fuel, the sealed program's output law approximates the old `ttc`.** -/
theorem approx_output (hn : 21 ≤ d) (F : ttc.LRAFormula d k)
    (hb : Bornology.IsBounded (ttc.solutionSet F)) (params : ttc.ApproxParams)
    (prep : ttc.TTCPreprocessor d k) :
    Approx (fun f => (vlaw (estimatorT (cv18T d) f
        (ttc.SealedRun.componentsOf (prep.run F hb)) params.epsilon params.delta) 0).map outOf)
      (ttc.ttc hn F hb params prep) := by
  set D := prep.run F hb
  by_cases hm : D.componentCount = 0
  · have hcs : ttc.SealedRun.componentsOf D = [] := by
      simp only [ttc.SealedRun.componentsOf, List.ofFn_eq_nil_iff]; exact hm
    have httc : ttc.ttc hn F hb params prep = Measure.dirac 0 := by
      simp only [ttc.ttc, ttcPseudocode]
      exact ite_eq_left_iff.mpr (fun h => absurd hm h) |>.trans rfl
    rw [hcs, httc]
    have := Approx.const (Measure.dirac (0 : NNReal))
    rw [Measure.map_dirac' measurable_some] at this
    convert this using 2 with f
    show (vlaw (compute (A.lit (0 : ℝ))) 0).map outOf = _
    rw [vlaw_compute, Measure.map_dirac' measurable_outOf]
    simp [outOf, A.lit]
  · have hmpos : 0 < D.componentCount := Nat.pos_of_ne_zero hm
    have heq : (fun f => (vlaw (estimatorT (cv18T d) f (ttc.SealedRun.componentsOf D)
        params.epsilon params.delta) 0).map outOf) = fun f =>
        (oldFoldF (by omega) params.ε' (params.δ' D.componentCount)
          (params.Thresh D.componentCount) f (ttc.GetPrecision D params.precisionEta)
          (samplerLaw (paramsOf D params) f 0) (List.ofFn D.component)
          (TTCState.initial d (params.Thresh D.componentCount))).map
          (Option.map (ttc.Est (ttc.GetPrecision D params.precisionEta))) := by
      funext f
      exact estimator_law (by omega) D params hmpos f 0
    have httc : ttc.ttc hn F hb params prep =
        (ttcPseudocode.loop (ttc.ttcSubroutines hn prep) (ttc.GetPrecision D params.precisionEta)
          params.ε' (params.δ' D.componentCount) (params.Thresh D.componentCount)
          (List.ofFn D.component) (TTCState.initial d (params.Thresh D.componentCount))).map
          (ttc.Est (ttc.GetPrecision D params.precisionEta)) := by
      simp only [ttc.ttc, ttcPseudocode]
      exact ite_eq_right_iff.mpr (fun h => absurd h hm)
    rw [heq, httc]
    refine (approx_fold hn prep D params 0 (List.ofFn D.component) (fun P h => h) _ ?_).map
      (ttc.measurable_Est _)
    refine ⟨?_, fun c hc => by simp [TTCState.initial] at hc⟩
    simp [ttc.TTCState.LabelsFresh, TTCState.initial]

end Output

/-! ## The run with the fuel it needs -/

section Run

open ttc.SealedRun

variable (cs : List (ttc.ComponentInput d)) (eps delta : ℝ)

/-- The result of the tree with fuel `f` on a tape. -/
def res (f : ℕ) (t : Tape d) : Option (Num ℝ) :=
  (exec (estimatorT (cv18T d) f cs eps delta) 0 t).1

theorem measurable_res (f : ℕ) : Measurable (res cs eps delta f) :=
  (measurable_fst.comp (measurable_exec_estimatorT f cs eps delta 0) : Measurable fun t =>
    (outcome ((estimatorT (cv18T d) f cs eps delta).exec 0 t)).1)

theorem finishes_iff (f : ℕ) (t : Tape d) : Finishes f cs eps delta t ↔ (res cs eps delta f t).isSome := by
  rw [Finishes, (execution_eq f cs eps delta t).1]
  rfl

theorem measurable_fuelNeeded : Measurable (fuelNeeded cs eps delta) := by
  refine measurable_nat_sInf fun f => ?_
  have : {t | Finishes f cs eps delta t} = res cs eps delta f ⁻¹' range some := by
    ext t
    rw [Set.mem_ofPred_eq, finishes_iff, Set.mem_preimage]
    rcases res cs eps delta f t with _ | x <;> simp
  rw [this]
  exact measurable_res cs eps delta f measurableSet_range_some

theorem output_eq (t : Tape d) :
    output cs eps delta t = (outOf (res cs eps delta (fuelNeeded cs eps delta t) t)).getD 0 := by
  rw [output, runOn, (execution_eq _ cs eps delta t).1]
  simp only [res]
  rcases (exec (estimatorT (cv18T d) (fuelNeeded cs eps delta t) cs eps delta) 0 t).1 with
    _ | x <;> rfl

theorem measurable_output : Measurable (output cs eps delta) := by
  have hG : Measurable fun z : Tape d × ℕ => (outOf (res cs eps delta z.2 z.1)).getD 0 := by
    refine measurable_from_prod_countable_left fun f => ?_
    have h := measurable_outOf.comp (measurable_res cs eps delta f)
    have hg : Measurable fun o : Option NNReal => o.getD 0 := by
      have : (fun o : Option NNReal => o.getD 0) =
          Sum.elim (fun _ : Unit => (0 : NNReal)) id ∘ ArlibCommunity.Algorithms.CV18.optionToSum := by
        funext o; cases o <;> rfl
      rw [this]
      exact (measurable_const.sumElim measurable_id).comp
        ArlibCommunity.Algorithms.CV18.measurable_optionToSum
    exact hg.comp h
  have : output cs eps delta = fun t => (outOf (res cs eps delta (fuelNeeded cs eps delta t) t)).getD 0 :=
    funext (output_eq cs eps delta)
  rw [this]
  exact hG.comp (f := fun t : Tape d => (t, fuelNeeded cs eps delta t))
    (measurable_id.prodMk (measurable_fuelNeeded cs eps delta))

end Run

/-! ## The law -/

section Law

open ttc.SealedRun

/-- **The sealed program's output law is the old model's `ttc`.** -/
theorem estimate_eq_ttc (hn : 21 ≤ d) (F : ttc.LRAFormula d k)
    (hb : Bornology.IsBounded (ttc.solutionSet F)) (params : ttc.ApproxParams)
    (prep : ttc.TTCPreprocessor d k) :
    estimate F hb params prep = ttc.ttc hn F hb params prep := by
  set cs := componentsOf (prep.run F hb)
  set eps := params.epsilon
  set delta := params.delta
  have : IsProbabilityMeasure (ttc.ttc hn F hb params prep) := by
    rw [ttc.ttc_eq_ttcRef]; exact ttc.community_ttc_isProbabilityMeasure hn F hb params prep
  have hA := approx_output hn F hb params prep
  have hprob : ∀ f, IsProbabilityMeasure
      ((vlaw (estimatorT (cv18T d) f cs eps delta) 0).map outOf) := fun f => by
    have := isProbabilityMeasure_vlaw _ 0 (measurable_exec_estimatorT f cs eps delta 0)
    exact Measure.isProbabilityMeasure_map measurable_outOf.aemeasurable
  -- the law with fuel `f`, as a set of tapes
  have hlaw : ∀ f (T : Set (Option NNReal)), MeasurableSet T →
      (vlaw (estimatorT (cv18T d) f cs eps delta) 0).map outOf T =
        tapeLaw d (res cs eps delta f ⁻¹' (outOf ⁻¹' T)) := by
    intro f T hT
    have hm := measurable_exec_estimatorT f cs eps delta 0
    rw [vlaw, ← tapeLaw_map_exec _ 0 hm, Measure.map_map measurable_fst hm,
      Measure.map_map measurable_outOf (measurable_fst.comp hm),
      Measure.map_apply (measurable_outOf.comp (measurable_fst.comp hm)) hT]
    rfl
  ext S hS
  rw [estimate, Measure.map_apply (measurable_output cs eps delta) hS]
  set E : ℕ → Set (Tape d) := fun f => res cs eps delta f ⁻¹' (outOf ⁻¹' (some '' S))
  have hfin : ∀ f t, (res cs eps delta f t).isSome → Finishes f cs eps delta t := fun f t h =>
    (finishes_iff cs eps delta f t).mpr h
  have hsame : ∀ f t, Finishes f cs eps delta t →
      res cs eps delta (fuelNeeded cs eps delta t) t = res cs eps delta f t ∧
        Finishes (fuelNeeded cs eps delta t) cs eps delta t := by
    intro f t hf
    have hmem : Finishes (fuelNeeded cs eps delta t) cs eps delta t :=
      Nat.sInf_mem (s := {f | Finishes f cs eps delta t}) ⟨f, hf⟩
    have hle : fuelNeeded cs eps delta t ≤ f :=
      Nat.sInf_le (s := {f | Finishes f cs eps delta t}) hf
    refine ⟨?_, hmem⟩
    have := fuelLE_estimatorT hle cs eps delta 0 t ((finishes_iff cs eps delta _ t).mp hmem)
    simp only [res]
    rw [this]
  have hmono : Monotone E := by
    intro f f' hff t ht
    simp only [E, Set.mem_preimage] at ht ⊢
    have hs : (res cs eps delta f t).isSome := by
      rcases h : res cs eps delta f t with _ | x
      · rw [h] at ht; obtain ⟨y, _, hy⟩ := ht; cases hy
      · rfl
    have := fuelLE_estimatorT hff cs eps delta 0 t hs
    simp only [res] at ht ⊢
    rw [this]
    exact ht
  have hsub : (⋃ f, E f) ⊆ output cs eps delta ⁻¹' S := by
    intro t ht
    obtain ⟨f, ht⟩ := Set.mem_iUnion.mp ht
    simp only [E, Set.mem_preimage] at ht
    rcases h : res cs eps delta f t with _ | x
    · rw [h] at ht; obtain ⟨y, _, hy⟩ := ht; cases hy
    · rw [h] at ht
      obtain ⟨y, hy, hyx⟩ := ht
      have := hsame f t (hfin f t (by rw [h]; rfl))
      rw [Set.mem_preimage, output_eq, this.1, h]
      simp only [outOf, Option.map_some, Option.getD_some] at hyx ⊢
      rw [← Option.some_injective _ hyx]
      exact hy
  set never := {t : Tape d | ∀ f, ¬ Finishes f cs eps delta t}
  have hnever : tapeLaw d never = 0 := by
    have hle : ∀ f, tapeLaw d never ≤
        (vlaw (estimatorT (cv18T d) f cs eps delta) 0).map outOf {none} := by
      intro f
      rw [hlaw f _ measurableSet_none]
      refine measure_mono fun t ht => ?_
      have := ht f
      rw [finishes_iff] at this
      simp only [Set.mem_preimage, Set.mem_singleton_iff, outOf]
      rcases h : res cs eps delta f t with _ | x
      · rfl
      · rw [h] at this; simp at this
    exact le_antisymm (ge_of_tendsto' hA.stop hle) bot_le
  have hcover : output cs eps delta ⁻¹' S ⊆ (⋃ f, E f) ∪ never := by
    intro t ht
    by_cases hn' : t ∈ never
    · exact Or.inr hn'
    · left
      simp only [never, Set.mem_ofPred_eq, not_forall, not_not] at hn'
      obtain ⟨f, hf⟩ := hn'
      obtain ⟨-, hmem⟩ := hsame f t hf
      refine Set.mem_iUnion.mpr ⟨fuelNeeded cs eps delta t, ?_⟩
      rw [finishes_iff] at hmem
      simp only [E, Set.mem_preimage]
      rw [Set.mem_preimage, output_eq] at ht
      rcases h : res cs eps delta (fuelNeeded cs eps delta t) t with _ | x
      · rw [h] at hmem; simp at hmem
      · rw [h] at ht
        exact ⟨_, ht, rfl⟩
  have heq : tapeLaw d (output cs eps delta ⁻¹' S) = tapeLaw d (⋃ f, E f) := by
    refine le_antisymm ?_ (measure_mono hsub)
    calc tapeLaw d (output cs eps delta ⁻¹' S) ≤ tapeLaw d ((⋃ f, E f) ∪ never) :=
          measure_mono hcover
      _ ≤ tapeLaw d (⋃ f, E f) + tapeLaw d never := measure_union_le _ _
      _ = tapeLaw d (⋃ f, E f) := by rw [hnever, add_zero]
  rw [heq]
  have hE : ∀ f, (vlaw (estimatorT (cv18T d) f cs eps delta) 0).map outOf (some '' S) =
      tapeLaw d (E f) := fun f => hlaw f _ (measurableSet_image_some hS)
  have h1 := hA.tendsto hS
  rw [funext hE] at h1
  exact tendsto_nhds_unique (tendsto_measure_iUnion_atTop hmono) h1

end Law

end ttc.Tape
