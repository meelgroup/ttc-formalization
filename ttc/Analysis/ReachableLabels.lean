import ttc.Analysis.LabelFreshness
import ttc.Analysis.MeasurableAddBatch

/-! Almost-sure preservation of distinct copy labels through randomized
paper state transitions. -/

namespace ttc

open MeasureTheory

theorem measurableSet_labelsFresh {n : Nat} :
    MeasurableSet {s : TTCState n | s.LabelsFresh} := by
  let good : Set (Finset (SampleCopy n) × Nat) :=
    {x | (∀ c ∈ x.1, c.1 < x.2) ∧
      (∀ c ∈ x.1, ∀ d ∈ x.1, c.1 = d.1 → c = d)}
  have hgood : MeasurableSet good := good.to_countable.measurableSet
  have hpair : Measurable (fun s : TTCState n => (s.X, s.nextLabel)) :=
    measurable_snd.comp
      (comap_measurable (fun s : TTCState n => (s.p, s.X, s.nextLabel)))
  convert hgood.preimage hpair using 1
  ext s
  rfl

theorem ae_bind_labelsFresh_of_forall {n : Nat} {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → Measure (TTCState n)) (hfm : AEMeasurable f μ)
    (hf : ∀ a, ∀ᵐ s ∂f a, s.LabelsFresh) :
    ∀ᵐ s ∂μ.bind f, s.LabelsFresh := by
  rw [ae_iff]
  apply le_antisymm
  · calc
      (μ.bind f) {s | ¬s.LabelsFresh} ≤
          ∫⁻ a, f a {s | ¬s.LabelsFresh} ∂μ :=
        Measure.bind_apply_le hfm measurableSet_labelsFresh.compl
      _ = 0 := by
        have hzero : ∀ a, f a {s | ¬s.LabelsFresh} = 0 := by
          intro a
          exact (ae_iff.mp (hf a))
        simp [hzero]
  · exact zero_le

theorem ae_bind_of_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {f : α → Measure β} {P : α → Prop} {Q : β → Prop}
    (hfm : AEMeasurable f μ) (hQ : MeasurableSet {b | Q b})
    (hP : ∀ᵐ a ∂μ, P a)
    (hf : ∀ a, P a → ∀ᵐ b ∂f a, Q b) :
    ∀ᵐ b ∂μ.bind f, Q b := by
  rw [ae_iff]
  apply le_antisymm
  · calc
      (μ.bind f) {b | ¬Q b} ≤ ∫⁻ a, f a {b | ¬Q b} ∂μ :=
        Measure.bind_apply_le hfm hQ.compl
      _ = 0 := by
        have hzero : (fun a => f a {b | ¬Q b}) =ᵐ[μ] (fun _ => 0) :=
          hP.mono fun a ha => ae_iff.mp (hf a ha)
        rw [lintegral_congr_ae hzero]
        simp
  · exact zero_le

theorem rateThinUntil_labelsFresh {n : Nat} (s : TTCState n)
    (intensity : NNReal) (threshold : Real) (h : s.LabelsFresh) :
    ∀ᵐ t ∂ttcReference.firstLoop s intensity threshold, t.LabelsFresh := by
  unfold ttcReference.firstLoop
  rw [ae_map_iff
    (measurable_rateThinningResult s intensity threshold).aemeasurable
    measurableSet_labelsFresh]
  exact Filter.Eventually.of_forall fun coins =>
    rateThinningResult_labelsFresh s intensity threshold coins h

theorem thinUntil_labelsFresh {n : Nat} (s : TTCState n)
    (pending : Nat) (threshold : Real) (h : s.LabelsFresh) :
    ∀ᵐ result ∂ttcPseudocode.secondLoop s pending threshold, result.1.LabelsFresh := by
  have hset : MeasurableSet
      {result : TTCState n × Nat | result.1.LabelsFresh} :=
    measurableSet_labelsFresh.preimage measurable_fst
  unfold ttcPseudocode.secondLoop
  rw [ae_map_iff (measurable_thinningResult s pending threshold).aemeasurable hset]
  exact Filter.Eventually.of_forall fun coins =>
    thinningResult_labelsFresh s pending threshold coins h

theorem sample_append_labelsFresh {n k : Nat} (O : TTCOracles n k)
    (P : PolytopeData n) (s : TTCState n) (count b : Nat)
    (ε' δ' : Real) (h : s.LabelsFresh) :
    ∀ᵐ result ∂(O.GenerateSamples P count b ε').map
      (fun batch => s.addBatch batch), result.LabelsFresh := by
  have hmap : Measurable (fun batch : SampleBatch n count => s.addBatch batch) :=
    measurable_addBatch.comp (measurable_const.prodMk measurable_id)
  rw [ae_map_iff hmap.aemeasurable measurableSet_labelsFresh]
  exact Filter.Eventually.of_forall fun batch => s.labelsFresh_addBatch batch h

end ttc
