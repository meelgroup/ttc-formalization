import Kr25Ssmxt.Analysis.ManuscriptOriginAdvanceOriginMeasurable

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

noncomputable def manuscriptOriginAdvanceStateTotal
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool)
    (c : ManuscriptOriginConfiguration n)
    (tape : Nat → LatticePoint n) : TTCState n :=
  (manuscriptOriginMergedSecondResult P intensity threshold basePending
    preCoins future c).1.addBatch
      (fun i : Fin (manuscriptOriginAdvanceSecondCount P intensity
        threshold basePending preCoins future c) =>
        tape (manuscriptOriginAdvanceIndex P intensity threshold
          basePending preCoins future c i.val))

set_option maxHeartbeats 1000000 in
theorem measurable_manuscriptOriginAdvanceStateTotal
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (fun z : ManuscriptOriginConfiguration n ×
        (Nat → LatticePoint n) =>
      manuscriptOriginAdvanceStateTotal P intensity threshold
        basePending preCoins future z.1 z.2) := by
  have hcount := measurable_manuscriptOriginAdvanceSecondCount
    P intensity threshold hthreshold basePending preCoins future
  have hstate : Measurable (fun c : ManuscriptOriginConfiguration n =>
      (manuscriptOriginMergedSecondResult P intensity threshold
        basePending preCoins future c).1) :=
    measurable_fst.comp
      (measurable_manuscriptOriginMergedSecondResult P intensity threshold
        hthreshold basePending preCoins future)
  have hindex := measurable_manuscriptOriginAdvanceIndex
    P intensity threshold hthreshold basePending preCoins future
  exact measurable_addBatch_indexed_tape_joint.comp
    ((hcount.comp measurable_fst).prodMk
      (((hstate.comp measurable_fst).prodMk
        (hindex.comp measurable_fst)).prodMk measurable_snd))

set_option maxHeartbeats 1000000 in
theorem ManuscriptOriginConfiguration.advance_state_eq_total
    {n : Nat} (c : ManuscriptOriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool)
    (tape : Nat → LatticePoint n) :
    (c.advance P intensity threshold basePending preCoins future tape).state =
      manuscriptOriginAdvanceStateTotal P intensity threshold
        basePending preCoins future c tape := by
  let deleted := c.state.removeComponent P
  let oldCoins := manuscriptSourceOldCoins c.origin c.source.coins c.level
  let rounds := ttcPseudocode.firstLoopExit deleted intensity threshold
  let preRounds := c.level + rounds
  let pending := pendingAfter preCoins preRounds deleted.nextLabel basePending
  let activeCoins := originalSurvivorCoinRestriction preCoins preRounds
    deleted.nextLabel basePending future
  let first := ttcPseudocode.firstLoopResult deleted intensity threshold
    oldCoins
  let activeRounds := manuscriptOriginSplitExit P intensity threshold
    basePending preCoins future c
  let second := thinningResultSplitFinite first pending threshold
    (shiftCoins rounds oldCoins) activeCoins
  have hsecond : manuscriptOriginMergedSecondResult P intensity threshold
      basePending preCoins future c = second :=
    manuscriptOriginMergedSecondResult_eq_splitFinite c P intensity
      threshold basePending preCoins future
  have hcount : manuscriptOriginAdvanceSecondCount P intensity threshold
      basePending preCoins future c = second.2 := rfl
  change second.1.addBatch
      (fun i : Fin second.2 =>
        tape (twoStageSurvivorLabel preCoins preRounds deleted.nextLabel
          basePending activeCoins activeRounds i)) =
    (manuscriptOriginMergedSecondResult P intensity threshold basePending
      preCoins future c).1.addBatch
        (fun i : Fin (manuscriptOriginAdvanceSecondCount P intensity
          threshold basePending preCoins future c) =>
          tape (manuscriptOriginAdvanceIndex P intensity threshold
            basePending preCoins future c i.val))
  rw [hsecond, hcount]
  congr 1
  funext i
  exact congrArg tape (twoStageSurvivorLabelOrZero_eq preCoins preRounds
    deleted.nextLabel basePending activeRounds activeCoins i).symm

set_option maxHeartbeats 1000000 in
theorem ManuscriptOriginConfiguration.measurable_advance_state_joint
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (fun z : ManuscriptOriginConfiguration n ×
        (Nat → LatticePoint n) =>
      (z.1.advance P intensity threshold basePending preCoins future
        z.2).state) := by
  have heq : (fun z : ManuscriptOriginConfiguration n ×
      (Nat → LatticePoint n) =>
      (z.1.advance P intensity threshold basePending preCoins future
        z.2).state) =
      (fun z => manuscriptOriginAdvanceStateTotal P intensity threshold
        basePending preCoins future z.1 z.2) := by
    funext z
    exact z.1.advance_state_eq_total P intensity threshold basePending
      preCoins future z.2
  rw [heq]
  exact measurable_manuscriptOriginAdvanceStateTotal P intensity threshold
    hthreshold basePending preCoins future

set_option maxHeartbeats 1000000 in
theorem ManuscriptOriginConfiguration.measurable_advance_joint
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (fun z : ManuscriptOriginConfiguration n ×
        (Nat → LatticePoint n) =>
      z.1.advance P intensity threshold basePending preCoins future z.2) := by
  rw [measurable_comap_iff]
  exact (ManuscriptOriginConfiguration.measurable_advance_state_joint
      P intensity threshold hthreshold basePending preCoins future).prodMk
    ((ManuscriptOriginConfiguration.measurable_advance_source_joint
      P intensity threshold hthreshold basePending preCoins future).prodMk
      ((ManuscriptOriginConfiguration.measurable_advance_origin_joint
        P intensity threshold hthreshold basePending preCoins future).prodMk
        (ManuscriptOriginConfiguration.measurable_advance_level_joint
          P intensity threshold hthreshold basePending preCoins future)))

end Kr25Ssmxt
