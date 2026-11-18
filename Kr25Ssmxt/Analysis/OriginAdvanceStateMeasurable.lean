import Kr25Ssmxt.Analysis.OriginAdvanceOriginMeasurable

/-! Measurability of appending marks from a random indexed tape when the
survivor count itself varies. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem measurable_addBatch_indexed_tape_joint {n : Nat} :
    Measurable (fun z : Nat ×
        ((TTCState n × (Nat → Nat)) × (Nat → LatticePoint n)) =>
      z.2.1.1.addBatch (fun i : Fin z.1 => z.2.2 (z.2.1.2 i.val))) := by
  apply measurable_from_prod_countable_right
  intro count
  have heval : Measurable (fun z : (Nat → LatticePoint n) × Nat =>
      z.1 z.2) := by
    apply measurable_from_prod_countable_left
    intro i
    exact measurable_pi_apply i
  have hpoints : Measurable (fun z :
      (TTCState n × (Nat → Nat)) × (Nat → LatticePoint n) =>
      (fun i : Fin count => z.2 (z.1.2 i.val))) := by
    apply Measurable.of_eval
    intro i
    exact heval.comp (measurable_snd.prodMk
      ((measurable_pi_apply i.val).comp
        (measurable_snd.comp measurable_fst)))
  exact measurable_addBatch.comp
    ((measurable_fst.comp measurable_fst).prodMk hpoints)

noncomputable def originAdvanceStateTotal
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool)
    (c : OriginConfiguration n)
    (tape : Nat → LatticePoint n) : TTCState n :=
  (originMergedSecondResult P intensity threshold basePending
    preCoins future c).1.addBatch
      (fun i : Fin (originAdvanceSecondCount P intensity
        threshold basePending preCoins future c) =>
        tape (originAdvanceIndex P intensity threshold
          basePending preCoins future c i.val))

set_option maxHeartbeats 1000000 in
theorem measurable_originAdvanceStateTotal
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (fun z : OriginConfiguration n ×
        (Nat → LatticePoint n) =>
      originAdvanceStateTotal P intensity threshold
        basePending preCoins future z.1 z.2) := by
  have hcount := measurable_originAdvanceSecondCount
    P intensity threshold hthreshold basePending preCoins future
  have hstate : Measurable (fun c : OriginConfiguration n =>
      (originMergedSecondResult P intensity threshold
        basePending preCoins future c).1) :=
    measurable_fst.comp
      (measurable_originMergedSecondResult P intensity threshold
        hthreshold basePending preCoins future)
  have hindex := measurable_originAdvanceIndex
    P intensity threshold hthreshold basePending preCoins future
  exact measurable_addBatch_indexed_tape_joint.comp
    ((hcount.comp measurable_fst).prodMk
      (((hstate.comp measurable_fst).prodMk
        (hindex.comp measurable_fst)).prodMk measurable_snd))

set_option maxHeartbeats 1000000 in
theorem OriginConfiguration.advance_state_eq_total
    {n : Nat} (c : OriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool)
    (tape : Nat → LatticePoint n) :
    (c.advance P intensity threshold basePending preCoins future tape).state =
      originAdvanceStateTotal P intensity threshold
        basePending preCoins future c tape := by
  let deleted := c.state.removeComponent P
  let oldCoins := sourceOldCoins c.origin c.source.coins c.level
  let rounds := ttcReference.firstLoopExit deleted intensity threshold
  let preRounds := c.level + rounds
  let pending := pendingAfter preCoins preRounds deleted.nextLabel basePending
  let activeCoins := originalSurvivorCoinRestriction preCoins preRounds
    deleted.nextLabel basePending future
  let first := ttcReference.firstLoopResult deleted intensity threshold
    oldCoins
  let activeRounds := originSplitExit P intensity threshold
    basePending preCoins future c
  let second := thinningResultSplitFinite first pending threshold
    (shiftCoins rounds oldCoins) activeCoins
  have hsecond : originMergedSecondResult P intensity threshold
      basePending preCoins future c = second :=
    originMergedSecondResult_eq_splitFinite c P intensity
      threshold basePending preCoins future
  have hcount : originAdvanceSecondCount P intensity threshold
      basePending preCoins future c = second.2 := rfl
  change second.1.addBatch
      (fun i : Fin second.2 =>
        tape (twoStageSurvivorLabel preCoins preRounds deleted.nextLabel
          basePending activeCoins activeRounds i)) =
    (originMergedSecondResult P intensity threshold basePending
      preCoins future c).1.addBatch
        (fun i : Fin (originAdvanceSecondCount P intensity
          threshold basePending preCoins future c) =>
          tape (originAdvanceIndex P intensity threshold
            basePending preCoins future c i.val))
  rw [hsecond, hcount]
  congr 1
  funext i
  exact congrArg tape (twoStageSurvivorLabelOrZero_eq preCoins preRounds
    deleted.nextLabel basePending activeRounds activeCoins i).symm

set_option maxHeartbeats 1000000 in
theorem OriginConfiguration.measurable_advance_state_joint
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (fun z : OriginConfiguration n ×
        (Nat → LatticePoint n) =>
      (z.1.advance P intensity threshold basePending preCoins future
        z.2).state) := by
  have heq : (fun z : OriginConfiguration n ×
      (Nat → LatticePoint n) =>
      (z.1.advance P intensity threshold basePending preCoins future
        z.2).state) =
      (fun z => originAdvanceStateTotal P intensity threshold
        basePending preCoins future z.1 z.2) := by
    funext z
    exact z.1.advance_state_eq_total P intensity threshold basePending
      preCoins future z.2
  rw [heq]
  exact measurable_originAdvanceStateTotal P intensity threshold
    hthreshold basePending preCoins future

set_option maxHeartbeats 1000000 in
theorem OriginConfiguration.measurable_advance_joint
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (fun z : OriginConfiguration n ×
        (Nat → LatticePoint n) =>
      z.1.advance P intensity threshold basePending preCoins future z.2) := by
  rw [measurable_comap_iff]
  exact (OriginConfiguration.measurable_advance_state_joint
      P intensity threshold hthreshold basePending preCoins future).prodMk
    ((OriginConfiguration.measurable_advance_source_joint
      P intensity threshold hthreshold basePending preCoins future).prodMk
      ((OriginConfiguration.measurable_advance_origin_joint
        P intensity threshold hthreshold basePending preCoins future).prodMk
        (OriginConfiguration.measurable_advance_level_joint
          P intensity threshold hthreshold basePending preCoins future)))

end Kr25Ssmxt
