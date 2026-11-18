import Kr25Ssmxt.Analysis.OriginActiveRoundsMeasurable

/-! Measurable survivor count and origin indices for the ghost transition. -/

namespace Kr25Ssmxt

open MeasureTheory

noncomputable def originAdvanceActiveFullCoins
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool)
    (c : OriginConfiguration n) : Nat × Nat → Bool :=
  let deleted := c.state.removeComponent P
  let preRounds := c.level + ttcReference.firstLoopExit deleted intensity threshold
  pendingCoinExtension deleted.nextLabel
    (pendingAfter preCoins preRounds deleted.nextLabel basePending)
    (originalSurvivorCoinRestriction preCoins preRounds deleted.nextLabel
      basePending future)

theorem measurable_originAdvanceActiveFullCoins
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (originAdvanceActiveFullCoins P intensity threshold
      basePending preCoins future) := by
  exact OriginConfiguration.measurable_activeFullCoins
    P intensity threshold hthreshold basePending preCoins future

noncomputable def originAdvanceSecondCount
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool)
    (c : OriginConfiguration n) : Nat :=
  let deleted := c.state.removeComponent P
  let preRounds := c.level + ttcReference.firstLoopExit deleted intensity threshold
  let pending := pendingAfter preCoins preRounds deleted.nextLabel basePending
  pendingAfter
    (originAdvanceActiveFullCoins P intensity threshold
      basePending preCoins future c)
    (originSplitExit P intensity threshold basePending
      preCoins future c) deleted.nextLabel pending

set_option maxHeartbeats 1000000 in
theorem measurable_originAdvanceSecondCount
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (originAdvanceSecondCount P intensity threshold
      basePending preCoins future) := by
  have hcontrols := OriginConfiguration.measurable_advance_controls
    P intensity threshold hthreshold
  have hrounds := OriginConfiguration.measurable_advance_activeRounds
    P intensity threshold hthreshold basePending preCoins future
  have hlabel : Measurable (fun c : OriginConfiguration n =>
      (c.state.removeComponent P).nextLabel) :=
    measurable_snd.comp hcontrols
  have hpending := OriginConfiguration.measurable_advance_pending
    P intensity threshold hthreshold basePending preCoins
  exact measurable_pendingAfter_joint.comp
    ((hrounds.prodMk (hlabel.prodMk hpending)).prodMk
      (measurable_originAdvanceActiveFullCoins P intensity
        threshold hthreshold basePending preCoins future))

noncomputable def originAdvanceIndex
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool)
    (c : OriginConfiguration n) : Nat → Nat := fun i =>
  let deleted := c.state.removeComponent P
  let preRounds := c.level + ttcReference.firstLoopExit deleted intensity threshold
  twoStageSurvivorLabelOrZero preCoins
    (originAdvanceActiveFullCoins P intensity threshold
      basePending preCoins future c)
    preRounds deleted.nextLabel basePending
    (originSplitExit P intensity threshold basePending
      preCoins future c) i

set_option maxHeartbeats 1000000 in
theorem measurable_originAdvanceIndex
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (originAdvanceIndex P intensity threshold
      basePending preCoins future) := by
  have hcontrols := OriginConfiguration.measurable_advance_controls
    P intensity threshold hthreshold
  have hpre : Measurable (fun c : OriginConfiguration n =>
      c.level + ttcReference.firstLoopExit (c.state.removeComponent P)
        intensity threshold) := measurable_fst.comp hcontrols
  have hlabel : Measurable (fun c : OriginConfiguration n =>
      (c.state.removeComponent P).nextLabel) :=
    measurable_snd.comp hcontrols
  have hrounds := OriginConfiguration.measurable_advance_activeRounds
    P intensity threshold hthreshold basePending preCoins future
  have hactive := measurable_originAdvanceActiveFullCoins
    P intensity threshold hthreshold basePending preCoins future
  apply Measurable.of_eval
  intro i
  exact measurable_twoStageSurvivorLabelOrZero_joint.comp
    ((hpre.prodMk
      (hlabel.prodMk
        (measurable_const.prodMk
          (hrounds.prodMk measurable_const)))).prodMk
      (measurable_const.prodMk hactive))

noncomputable def originAdvanceOriginTotal
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool)
    (c : OriginConfiguration n) : Nat → Nat × Nat :=
  originAppend c.origin c.source.processed
    (c.state.removeComponent P).nextLabel
    (originAdvanceSecondCount P intensity threshold
      basePending preCoins future c)
    (fun i => originAdvanceIndex P intensity threshold
      basePending preCoins future c i.val)

set_option maxHeartbeats 1000000 in
theorem measurable_originAdvanceOriginTotal
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (originAdvanceOriginTotal P intensity threshold
      basePending preCoins future) := by
  have hcomponent : Measurable (fun c : OriginConfiguration n =>
      c.source.processed) :=
    measurable_originSourceState_processed.comp
      measurable_originConfiguration_source
  have hlabel : Measurable (fun c : OriginConfiguration n =>
      (c.state.removeComponent P).nextLabel) :=
    measurable_snd.comp
      (OriginConfiguration.measurable_advance_controls
        P intensity threshold hthreshold)
  have hcount := measurable_originAdvanceSecondCount
    P intensity threshold hthreshold basePending preCoins future
  have horigin := measurable_originConfiguration_origin
    (n := n)
  have hindex := measurable_originAdvanceIndex
    P intensity threshold hthreshold basePending preCoins future
  exact measurable_originAppend_joint.comp
    ((hcomponent.prodMk (hlabel.prodMk hcount)).prodMk
      (horigin.prodMk hindex))

set_option maxHeartbeats 1000000 in
theorem OriginConfiguration.advance_origin_eq_total
    {n : Nat} (c : OriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool)
    (tape : Nat → LatticePoint n) :
    (c.advance P intensity threshold basePending preCoins future tape).origin =
      originAdvanceOriginTotal P intensity threshold basePending
        preCoins future c := by
  let deleted := c.state.removeComponent P
  let preRounds := c.level + ttcReference.firstLoopExit deleted intensity threshold
  let pending := pendingAfter preCoins preRounds deleted.nextLabel basePending
  let activeCoins := originalSurvivorCoinRestriction preCoins preRounds
    deleted.nextLabel basePending future
  let first := ttcReference.firstLoopResult deleted intensity threshold
    (sourceOldCoins c.origin c.source.coins c.level)
  let activeRounds := originSplitExit P intensity threshold
    basePending preCoins future c
  let second := thinningResultSplitFinite first pending threshold
    (shiftCoins (ttcReference.firstLoopExit deleted intensity threshold)
      (sourceOldCoins c.origin c.source.coins c.level)) activeCoins
  have hcount : originAdvanceSecondCount P intensity threshold
      basePending preCoins future c = second.2 := rfl
  change originAppend c.origin c.source.processed
      deleted.nextLabel second.2
        (fun i => twoStageSurvivorLabel preCoins preRounds
          deleted.nextLabel basePending activeCoins activeRounds i) =
    originAppend c.origin c.source.processed
      deleted.nextLabel second.2
        (fun i => originAdvanceIndex P intensity threshold
          basePending preCoins future c i.val)
  congr 1
  funext i
  exact (twoStageSurvivorLabelOrZero_eq preCoins preRounds
    deleted.nextLabel basePending activeRounds activeCoins i).symm

set_option maxHeartbeats 1000000 in
theorem OriginConfiguration.measurable_advance_origin_joint
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (fun z : OriginConfiguration n ×
        (Nat → LatticePoint n) =>
      (z.1.advance P intensity threshold basePending preCoins future
        z.2).origin) := by
  have heq : (fun z : OriginConfiguration n ×
      (Nat → LatticePoint n) =>
      (z.1.advance P intensity threshold basePending preCoins future
        z.2).origin) =
      (fun z => originAdvanceOriginTotal P intensity threshold
        basePending preCoins future z.1) := by
    funext z
    exact z.1.advance_origin_eq_total P intensity threshold basePending
      preCoins future z.2
  rw [heq]
  exact (measurable_originAdvanceOriginTotal P intensity
    threshold hthreshold basePending preCoins future).comp measurable_fst

end Kr25Ssmxt
