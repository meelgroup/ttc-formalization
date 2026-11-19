import ttc.Analysis.CoinSpliceLaw
import ttc.Analysis.IIDIndexedSelection

/-! Independent fair coin streams may be reindexed from old Poisson copy
labels to the fresh contiguous labels assigned by the executable state. -/

namespace ttc

open MeasureTheory

theorem fairCoinStreamLaw_reindex_labels
    {α : Type*} (labels : α → Nat) (hinj : Function.Injective labels) :
    fairCoinStreamLaw.map
      (fun coins (pair : Nat × α) => coins (pair.1, labels pair.2)) =
    Measure.infinitePi (fun _ : Nat × α => fairCoinLaw) := by
  have hindex : Function.Injective
      (fun pair : Nat × α => (pair.1, labels pair.2)) := by
    intro a b hab
    have hr : a.1 = b.1 :=
      congrArg (fun pair : Nat × Nat => pair.1) hab
    have hl : labels a.2 = labels b.2 :=
      congrArg (fun pair : Nat × Nat => pair.2) hab
    exact Prod.ext hr (hinj hl)
  exact @Measure.map_infinitePi_infinitePi_of_inj
    (Nat × Nat) (Nat × α) (fun _ => Bool)
    (fun _ => inferInstance) (fun _ => fairCoinLaw)
    (fun _ => fairCoinLaw_isProbabilityMeasure)
    (fun pair => (pair.1, labels pair.2)) hindex

theorem fairCoinStreamLaw_relabel_eq
    {α : Type*} (oldLabels freshLabels : α → Nat)
    (hold : Function.Injective oldLabels)
    (hfresh : Function.Injective freshLabels) :
    fairCoinStreamLaw.map
      (fun coins (pair : Nat × α) => coins (pair.1, oldLabels pair.2)) =
    fairCoinStreamLaw.map
      (fun coins (pair : Nat × α) => coins (pair.1, freshLabels pair.2)) := by
  rw [fairCoinStreamLaw_reindex_labels oldLabels hold,
    fairCoinStreamLaw_reindex_labels freshLabels hfresh]

/-- After a fixed pre-thinning outcome, the future fair coins on its surviving
old labels have the same joint law as future fair coins on the contiguous
fresh labels allocated by the TTC state. -/
theorem fairCoinStreamLaw_pending_survivor_relabel
    (preCoins : Nat × Nat → Bool) (rounds oldFirst basePending
      freshFirst : Nat) :
    let count := pendingAfter preCoins rounds oldFirst basePending
    let survivors := pendingSurvivorIndices preCoins rounds oldFirst basePending
    fairCoinStreamLaw.map
      (fun future (pair : Nat × Fin count) =>
        future (pair.1,
          oldFirst + (survivors.orderEmbOfFin
            (pendingSurvivorIndices_card preCoins rounds oldFirst basePending)
            pair.2))) =
    fairCoinStreamLaw.map
      (fun future (pair : Nat × Fin count) =>
        future (pair.1, freshFirst + pair.2.val)) := by
  dsimp only
  let count := pendingAfter preCoins rounds oldFirst basePending
  let survivors := pendingSurvivorIndices preCoins rounds oldFirst basePending
  let oldLabels : Fin count → Nat := fun i =>
    oldFirst + survivors.orderEmbOfFin
      (pendingSurvivorIndices_card preCoins rounds oldFirst basePending) i
  let freshLabels : Fin count → Nat := fun i => freshFirst + i.val
  have hold : Function.Injective oldLabels := by
    intro i j hij
    apply (survivors.orderEmbOfFin
      (pendingSurvivorIndices_card preCoins rounds oldFirst basePending)).injective
    exact Nat.add_left_cancel hij
  have hfresh : Function.Injective freshLabels := by
    intro i j hij
    exact Fin.ext (Nat.add_left_cancel hij)
  exact fairCoinStreamLaw_relabel_eq oldLabels freshLabels hold hfresh

/-- Coin streams and IID point marks can be relabeled together, without
changing their joint law. The two tape families remain independent. -/
theorem fairCoin_pointTape_joint_relabel
    {n count : Nat}
    (pointLaw : Measure (LatticePoint n)) [IsProbabilityMeasure pointLaw]
    (oldLabels freshLabels : Fin count → Nat)
    (hold : Function.Injective oldLabels)
    (hfresh : Function.Injective freshLabels) :
    let tapeLaw := Measure.infinitePi (fun _ : Nat => pointLaw)
    (fairCoinStreamLaw.prod tapeLaw).map
      (fun pair =>
        ((fun index : Nat × Fin count =>
            pair.1 (index.1, oldLabels index.2)),
          fun i : Fin count => pair.2 (oldLabels i))) =
    (fairCoinStreamLaw.prod tapeLaw).map
      (fun pair =>
        ((fun index : Nat × Fin count =>
            pair.1 (index.1, freshLabels index.2)),
          fun i : Fin count => pair.2 (freshLabels i))) := by
  let tapeLaw := Measure.infinitePi (fun _ : Nat => pointLaw)
  let coinOld : (Nat × Nat → Bool) → (Nat × Fin count → Bool) :=
    fun coins index => coins (index.1, oldLabels index.2)
  let coinFresh : (Nat × Nat → Bool) → (Nat × Fin count → Bool) :=
    fun coins index => coins (index.1, freshLabels index.2)
  let markOld : (Nat → LatticePoint n) → (Fin count → LatticePoint n) :=
    fun tape i => tape (oldLabels i)
  let markFresh : (Nat → LatticePoint n) → (Fin count → LatticePoint n) :=
    fun tape i => tape (freshLabels i)
  have hcoinOld : Measurable coinOld :=
    Measurable.of_eval (fun index =>
      measurable_pi_apply (index.1, oldLabels index.2))
  have hcoinFresh : Measurable coinFresh :=
    Measurable.of_eval (fun index =>
      measurable_pi_apply (index.1, freshLabels index.2))
  have hmarkOld : Measurable markOld :=
    Measurable.of_eval (fun i => measurable_pi_apply (oldLabels i))
  have hmarkFresh : Measurable markFresh :=
    Measurable.of_eval (fun i => measurable_pi_apply (freshLabels i))
  have hcoin : fairCoinStreamLaw.map coinOld =
      fairCoinStreamLaw.map coinFresh :=
    fairCoinStreamLaw_relabel_eq oldLabels freshLabels hold hfresh
  have hmark : tapeLaw.map markOld = tapeLaw.map markFresh := by
    rw [iid_tape_injective_selection pointLaw count oldLabels hold]
    rw [iid_tape_injective_selection pointLaw count freshLabels hfresh]
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  letI : IsProbabilityMeasure tapeLaw := inferInstance
  change (fairCoinStreamLaw.prod tapeLaw).map
      (Prod.map coinOld markOld) =
    (fairCoinStreamLaw.prod tapeLaw).map
      (Prod.map coinFresh markFresh)
  rw [← Measure.map_prod_map fairCoinStreamLaw tapeLaw hcoinOld hmarkOld]
  rw [← Measure.map_prod_map fairCoinStreamLaw tapeLaw hcoinFresh hmarkFresh]
  rw [hcoin, hmark]

/-- The joint relabeling law remains valid after a random pre-thinning
history chooses the survivor count and its two injective label enumerations. -/
theorem fairCoin_pointTape_adaptive_relabel
    {n : Nat} {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (preLaw : Measure α)
    (pointLaw : Measure (LatticePoint n)) [IsProbabilityMeasure pointLaw]
    (count : α → Nat)
    (oldLabels freshLabels : (a : α) → Fin (count a) → Nat)
    (hold : ∀ a, Function.Injective (oldLabels a))
    (hfresh : ∀ a, Function.Injective (freshLabels a))
    (g : (a : α) →
      ((Nat × Fin (count a) → Bool) ×
        (Fin (count a) → LatticePoint n)) → β)
    (hg : ∀ a, Measurable (g a)) :
    let tapeLaw := Measure.infinitePi (fun _ : Nat => pointLaw)
    preLaw.bind (fun a =>
      (fairCoinStreamLaw.prod tapeLaw).map fun pair =>
        g a ((fun index : Nat × Fin (count a) =>
          pair.1 (index.1, oldLabels a index.2)),
          fun i : Fin (count a) => pair.2 (oldLabels a i))) =
    preLaw.bind (fun a =>
      (fairCoinStreamLaw.prod tapeLaw).map fun pair =>
        g a ((fun index : Nat × Fin (count a) =>
          pair.1 (index.1, freshLabels a index.2)),
          fun i : Fin (count a) => pair.2 (freshLabels a i))) := by
  dsimp only
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro a
  let tapeLaw := Measure.infinitePi (fun _ : Nat => pointLaw)
  let oldProjection :
      (Nat × Nat → Bool) × (Nat → LatticePoint n) →
        (Nat × Fin (count a) → Bool) × (Fin (count a) → LatticePoint n) :=
    fun pair =>
      ((fun index => pair.1 (index.1, oldLabels a index.2)),
        fun i => pair.2 (oldLabels a i))
  let freshProjection :
      (Nat × Nat → Bool) × (Nat → LatticePoint n) →
        (Nat × Fin (count a) → Bool) × (Fin (count a) → LatticePoint n) :=
    fun pair =>
      ((fun index => pair.1 (index.1, freshLabels a index.2)),
        fun i => pair.2 (freshLabels a i))
  have holdMeas : Measurable oldProjection :=
    (Measurable.of_eval (fun index =>
      (measurable_pi_apply (index.1, oldLabels a index.2)).comp
        measurable_fst)).prodMk
      (Measurable.of_eval (fun i =>
        (measurable_pi_apply (oldLabels a i)).comp measurable_snd))
  have hfreshMeas : Measurable freshProjection :=
    (Measurable.of_eval (fun index =>
      (measurable_pi_apply (index.1, freshLabels a index.2)).comp
        measurable_fst)).prodMk
      (Measurable.of_eval (fun i =>
        (measurable_pi_apply (freshLabels a i)).comp measurable_snd))
  change (fairCoinStreamLaw.prod tapeLaw).map (g a ∘ oldProjection) =
    (fairCoinStreamLaw.prod tapeLaw).map (g a ∘ freshProjection)
  rw [← Measure.map_map (hg a) holdMeas]
  rw [← Measure.map_map (hg a) hfreshMeas]
  rw [fairCoin_pointTape_joint_relabel pointLaw
    (oldLabels a) (freshLabels a) (hold a) (hfresh a)]

end ttc
