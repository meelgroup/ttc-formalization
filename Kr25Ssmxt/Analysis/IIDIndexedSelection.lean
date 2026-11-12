import Kr25Ssmxt.Analysis.ConcreteFixedLevelBounds
import Kr25Ssmxt.Analysis.MeasurableSetSurvives
import Mathlib.Probability.Independence.InfinitePi

/-! A batch drawn after a count-only stopping decision can be coupled to an
independent infinite IID point tape indexed by the surviving pending labels. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem iid_tape_injective_selection
    {α : Type*} [MeasurableSpace α] (pointLaw : Measure α)
    [IsProbabilityMeasure pointLaw] (count : Nat)
    (labels : Fin count → Nat) (hlabels : Function.Injective labels) :
    (Measure.infinitePi (fun _ : Nat => pointLaw)).map
      (fun tape i => tape (labels i)) =
        Measure.pi (fun _ : Fin count => pointLaw) := by
  rw [Measure.map_infinitePi_infinitePi_of_inj hlabels]
  exact Measure.infinitePi_eq_pi (fun _ : Fin count => pointLaw)

/-- The increasing enumeration of any finite set of pending copy labels is
injective; its point marks therefore remain an IID batch. -/
theorem iid_tape_finite_label_selection
    {α : Type*} [MeasurableSpace α] (pointLaw : Measure α)
    [IsProbabilityMeasure pointLaw] (labels : Finset Nat) :
    (Measure.infinitePi (fun _ : Nat => pointLaw)).map
      (fun tape i => tape (labels.orderEmbOfFin rfl i)) =
        Measure.pi (fun _ : Fin labels.card => pointLaw) := by
  exact iid_tape_injective_selection pointLaw labels.card
    (labels.orderEmbOfFin rfl) (labels.orderEmbOfFin rfl).injective

noncomputable def pendingSurvivorIndices
    (coins : Nat × Nat → Bool) (rounds firstLabel pending : Nat) : Finset Nat := by
  classical
  exact (Finset.range pending).filter
    (fun i => survives coins rounds (firstLabel + i))

theorem pendingSurvivorIndices_card
    (coins : Nat × Nat → Bool) (rounds firstLabel pending : Nat) :
    (pendingSurvivorIndices coins rounds firstLabel pending).card =
      pendingAfter coins rounds firstLabel pending := by
  simp only [pendingSurvivorIndices, pendingAfter]

theorem measurable_pendingSurvivorIndices_fixed
    (rounds firstLabel pending : Nat) :
    Measurable (fun coins : Nat × Nat → Bool =>
      pendingSurvivorIndices coins rounds firstLabel pending) := by
  rw [measurable_finset_iff]
  intro i
  apply measurable_to_prop
  by_cases hi : i ∈ Finset.range pending
  · simpa [pendingSurvivorIndices, hi] using
      measurableSet_survives rounds (firstLabel + i)
  · simp [pendingSurvivorIndices, hi]

theorem measurable_pendingAfter_fixed
    (rounds firstLabel pending : Nat) :
    Measurable (fun coins : Nat × Nat → Bool =>
      pendingAfter coins rounds firstLabel pending) := by
  have hcard : Measurable (fun T : Finset Nat => T.card) :=
    measurable_of_countable _
  have h := hcard.comp
    (measurable_pendingSurvivorIndices_fixed rounds firstLabel pending)
  change Measurable (fun coins : Nat × Nat → Bool =>
    (pendingSurvivorIndices coins rounds firstLabel pending).card)
  simpa only [Function.comp_def] using h

/-- Conditional on the Poisson count and all thinning decisions, attaching
marks from an independent infinite point tape to exactly the surviving
pending labels has the IID batch law requested by the paper program. -/
theorem iid_tape_pending_survivors
    {α : Type*} [MeasurableSpace α] (pointLaw : Measure α)
    [IsProbabilityMeasure pointLaw]
    (coins : Nat × Nat → Bool) (rounds firstLabel pending : Nat) :
    (Measure.infinitePi (fun _ : Nat => pointLaw)).map
      (fun tape (i : Fin (pendingAfter coins rounds firstLabel pending)) =>
        tape (firstLabel +
          (pendingSurvivorIndices coins rounds firstLabel pending).orderEmbOfFin
            (pendingSurvivorIndices_card coins rounds firstLabel pending) i)) =
      Measure.pi (fun _ : Fin (pendingAfter coins rounds firstLabel pending) =>
        pointLaw) := by
  let T := pendingSurvivorIndices coins rounds firstLabel pending
  let labels : Fin (pendingAfter coins rounds firstLabel pending) → Nat :=
    fun i => firstLabel +
      T.orderEmbOfFin (pendingSurvivorIndices_card coins rounds firstLabel pending) i
  have hlabels : Function.Injective labels := by
    intro i j hij
    exact (T.orderEmbOfFin
      (pendingSurvivorIndices_card coins rounds firstLabel pending)).injective
        (Nat.add_left_cancel hij)
  exact iid_tape_injective_selection pointLaw _ labels hlabels

theorem iid_tape_pending_survivors_batch
    {n : Nat} (pointLaw : Measure (LatticePoint n))
    [IsProbabilityMeasure pointLaw]
    (coins : Nat × Nat → Bool) (rounds firstLabel pending : Nat) :
    (Measure.infinitePi (fun _ : Nat => pointLaw)).map
      (fun tape => (fun (i : Fin (pendingAfter coins rounds firstLabel pending)) =>
        tape (firstLabel +
          (pendingSurvivorIndices coins rounds firstLabel pending).orderEmbOfFin
            (pendingSurvivorIndices_card coins rounds firstLabel pending) i))) =
      iidSampleBatchLaw pointLaw := by
  let selected : (Nat → LatticePoint n) →
      (Fin (pendingAfter coins rounds firstLabel pending) → LatticePoint n) :=
    fun tape i => tape (firstLabel +
      (pendingSurvivorIndices coins rounds firstLabel pending).orderEmbOfFin
        (pendingSurvivorIndices_card coins rounds firstLabel pending) i)
  have hselected : Measurable selected := by
    exact Measurable.of_eval (fun i => measurable_pi_apply _)
  calc
    (Measure.infinitePi (fun _ : Nat => pointLaw)).map
        (fun tape => (selected tape)) =
      ((Measure.infinitePi (fun _ : Nat => pointLaw)).map selected).map
        (fun samples => samples) := by
          rw [Measure.map_map (by fun_prop) hselected]
          rfl
    _ = iidSampleBatchLaw pointLaw := by
      rw [iid_tape_pending_survivors pointLaw coins rounds firstLabel pending,
        Measure.map_id']
      rfl

/-- The post-stopping concrete sampler can be realized from an IID point tape
whose labels were chosen before seeing any point marks. This is pointwise in
the stopping coins and the incoming state. -/
theorem community_adaptive_batch_from_iid_tape
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (s : TTCState n) (pending : Nat) (coins : Nat × Nat → Bool) :
    let pointLaw := normalizedHitAndRunPointLaw hn P b hroute.1 eta
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
    let rounds := ttcPseudocode.secondLoopExitRound s pending threshold coins
    (Measure.infinitePi (fun _ : Nat => pointLaw)).map
      (fun tape => (fun (i : Fin (ttcPseudocode.secondLoopResult s pending threshold coins).2) =>
        tape (s.nextLabel +
          (pendingSurvivorIndices coins rounds s.nextLabel pending).orderEmbOfFin
            (pendingSurvivorIndices_card coins rounds s.nextLabel pending) i))) =
      (ttcSubroutines hn prep).GenerateSamples P
        (ttcPseudocode.secondLoopResult s pending threshold coins).2 b eta delta := by
  dsimp only
  let pointLaw := normalizedHitAndRunPointLaw hn P b hroute.1 eta
    hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
  letI : IsProbabilityMeasure pointLaw :=
    (P.normalizedHitAndRun_latticePointLaw hn b hroute.1
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2).1
  change (Measure.infinitePi (fun _ : Nat => pointLaw)).map
      (fun tape => (fun (i : Fin
        (pendingAfter coins (ttcPseudocode.secondLoopExitRound s pending threshold coins)
          s.nextLabel pending)) =>
        tape (s.nextLabel +
          (pendingSurvivorIndices coins (ttcPseudocode.secondLoopExitRound s pending threshold coins)
            s.nextLabel pending).orderEmbOfFin
            (pendingSurvivorIndices_card coins
              (ttcPseudocode.secondLoopExitRound s pending threshold coins) s.nextLabel pending) i))) = _
  rw [iid_tape_pending_survivors_batch pointLaw coins
    (ttcPseudocode.secondLoopExitRound s pending threshold coins) s.nextLabel pending]
  exact (community_generateSamples_eq_iid hn prep P _ b eta delta
    hroute).symm

end Kr25Ssmxt
