import Kr25Ssmxt.Analysis.OriginOldCoinsMeasurable

/-! Joint measurability of the split-loop coin merge with a random boundary. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem measurable_mergeCoinsAtLabel_joint :
    Measurable (fun z : Nat ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      mergeCoinsAtLabel z.1 z.2.1 z.2.2) := by
  apply measurable_from_prod_countable_right
  intro boundary
  exact measurable_mergeCoinsAtLabel_pair boundary

set_option maxHeartbeats 1000000 in
theorem OriginConfiguration.measurable_advance_firstState
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold) :
    Measurable (fun c : OriginConfiguration n =>
      ttcPseudocode.firstLoopResult (c.state.removeComponent P)
        intensity threshold
        (sourceOldCoins c.origin c.source.coins c.level)) := by
  have hdeleted : Measurable (fun c : OriginConfiguration n =>
      c.state.removeComponent P) :=
    (measurable_removeComponent P).comp
      measurable_originConfiguration_state
  exact (measurable_rateThinningResult_joint
    threshold hthreshold).comp
      ((hdeleted.prodMk measurable_const).prodMk
        measurable_sourceOldCoins_joint)

theorem OriginConfiguration.measurable_advance_pending
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins : Nat × Nat → Bool) :
    Measurable (fun c : OriginConfiguration n =>
      pendingAfter preCoins
        (c.level + ttcPseudocode.firstLoopExit (c.state.removeComponent P)
          intensity threshold)
        (c.state.removeComponent P).nextLabel basePending) := by
  exact (measurable_of_countable
    (fun params : Nat × Nat =>
      pendingAfter preCoins params.1 params.2 basePending)).comp
        (OriginConfiguration.measurable_advance_controls
          P intensity threshold hthreshold)

set_option maxHeartbeats 1000000 in
theorem OriginConfiguration.measurable_advance_shiftedOldCoins
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold) :
    Measurable (fun c : OriginConfiguration n =>
      shiftCoins
        (ttcPseudocode.firstLoopExit (c.state.removeComponent P) intensity
          threshold)
        (sourceOldCoins c.origin c.source.coins c.level)) := by
  have hdeleted : Measurable (fun c : OriginConfiguration n =>
      c.state.removeComponent P) :=
    (measurable_removeComponent P).comp
      measurable_originConfiguration_state
  have hround : Measurable (fun c : OriginConfiguration n =>
      ttcPseudocode.firstLoopExit (c.state.removeComponent P) intensity
        threshold) :=
    (measurable_rateExit_joint threshold hthreshold).comp
      (hdeleted.prodMk measurable_const)
  exact measurable_shiftCoins_joint.comp
    (hround.prodMk measurable_sourceOldCoins_joint)

set_option maxHeartbeats 1000000 in
theorem OriginConfiguration.measurable_advance_mergedCoins
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (fun c : OriginConfiguration n =>
      let deleted := c.state.removeComponent P
      let preRounds := c.level + ttcPseudocode.firstLoopExit deleted intensity
        threshold
      mergeCoinsAtLabel deleted.nextLabel
        (shiftCoins (ttcPseudocode.firstLoopExit deleted intensity threshold)
          (sourceOldCoins c.origin c.source.coins c.level))
        (pendingCoinExtension deleted.nextLabel
          (pendingAfter preCoins preRounds deleted.nextLabel basePending)
          (originalSurvivorCoinRestriction preCoins preRounds
            deleted.nextLabel basePending future))) := by
  have hlabel : Measurable (fun c : OriginConfiguration n =>
      (c.state.removeComponent P).nextLabel) :=
    measurable_snd.comp
      (OriginConfiguration.measurable_advance_controls
        P intensity threshold hthreshold)
  exact measurable_mergeCoinsAtLabel_joint.comp
    (hlabel.prodMk
      ((OriginConfiguration.measurable_advance_shiftedOldCoins
          P intensity threshold hthreshold).prodMk
        (OriginConfiguration.measurable_activeFullCoins
          P intensity threshold hthreshold basePending preCoins future)))

private noncomputable def originMergedExitInput
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool) :
    OriginConfiguration n →
      (TTCState n × Nat) × (Nat × Nat → Bool) := fun c =>
      let deleted := c.state.removeComponent P
      let rounds := ttcPseudocode.firstLoopExit deleted intensity threshold
      let preRounds := c.level + rounds
      let pending := pendingAfter preCoins preRounds deleted.nextLabel
        basePending
      let first := ttcPseudocode.firstLoopResult deleted intensity
        threshold (sourceOldCoins c.origin c.source.coins c.level)
      ((first, pending),
        (mergeCoinsAtLabel deleted.nextLabel
          (shiftCoins rounds
            (sourceOldCoins c.origin c.source.coins c.level))
          (pendingCoinExtension deleted.nextLabel pending
            (originalSurvivorCoinRestriction preCoins preRounds
              deleted.nextLabel basePending future))))

set_option maxHeartbeats 1000000 in
private theorem measurable_originMergedExitInput
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (originMergedExitInput P intensity threshold
      basePending preCoins future) := by
  unfold originMergedExitInput
  exact
    (((OriginConfiguration.measurable_advance_firstState
        P intensity threshold hthreshold).prodMk
      (OriginConfiguration.measurable_advance_pending
        P intensity threshold hthreshold basePending preCoins)).prodMk
      (OriginConfiguration.measurable_advance_mergedCoins
        P intensity threshold hthreshold basePending preCoins future))

private noncomputable def originMergedExit
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool) :
    OriginConfiguration n → Nat :=
  fun c =>
    let z := originMergedExitInput P intensity threshold
      basePending preCoins future c
    ttcPseudocode.secondLoopExitRound z.1.1 z.1.2 threshold z.2

theorem OriginConfiguration.measurable_advance_mergedExit
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (originMergedExit P intensity threshold
      basePending preCoins future) := by
  change Measurable ((fun z : (TTCState n × Nat) ×
    (Nat × Nat → Bool) => ttcPseudocode.secondLoopExitRound z.1.1 z.1.2 threshold z.2) ∘
      originMergedExitInput P intensity threshold
        basePending preCoins future)
  exact (measurable_firstExitRound_joint threshold).comp
    (measurable_originMergedExitInput P intensity threshold
      hthreshold basePending preCoins future)

noncomputable def originSplitExit
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool) :
    OriginConfiguration n → Nat := fun c =>
  let deleted := c.state.removeComponent P
  let oldCoins := sourceOldCoins c.origin c.source.coins c.level
  let rounds := ttcPseudocode.firstLoopExit deleted intensity threshold
  let preRounds := c.level + rounds
  let pending := pendingAfter preCoins preRounds deleted.nextLabel basePending
  let activeCoins := originalSurvivorCoinRestriction preCoins preRounds
    deleted.nextLabel basePending future
  let first := ttcPseudocode.firstLoopResult deleted intensity threshold
    oldCoins
  firstExitRoundSplit first pending threshold (shiftCoins rounds oldCoins)
    (pendingCoinExtension deleted.nextLabel pending activeCoins)

set_option maxHeartbeats 1000000 in
private theorem originSplitExit_eq_mergedExit
    {n : Nat} (c : OriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool) :
    originSplitExit P intensity threshold basePending
      preCoins future c =
    originMergedExit P intensity threshold basePending
      preCoins future c := by
  let deleted := c.state.removeComponent P
  let oldCoins := sourceOldCoins c.origin c.source.coins c.level
  have hdeleted : deleted.LabelsFresh :=
    c.state.labelsFresh_removeComponent P c.fresh
  have hfirst : (ttcPseudocode.firstLoopResult deleted intensity threshold
      oldCoins).LabelsFresh :=
    rateThinningResult_labelsFresh deleted intensity threshold
      oldCoins hdeleted
  exact (firstExitRound_mergeCoinsAtLabel
    (ttcPseudocode.firstLoopResult deleted intensity threshold oldCoins)
    (pendingAfter preCoins
      (c.level + ttcPseudocode.firstLoopExit deleted intensity threshold)
      deleted.nextLabel basePending) threshold
    (shiftCoins (ttcPseudocode.firstLoopExit deleted intensity threshold) oldCoins)
    (pendingCoinExtension deleted.nextLabel
      (pendingAfter preCoins
        (c.level + ttcPseudocode.firstLoopExit deleted intensity threshold)
        deleted.nextLabel basePending)
      (originalSurvivorCoinRestriction preCoins
        (c.level + ttcPseudocode.firstLoopExit deleted intensity threshold)
        deleted.nextLabel basePending future)) hfirst).symm

theorem OriginConfiguration.measurable_advance_activeRounds
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (originSplitExit P intensity threshold
      basePending preCoins future) := by
  have heq : originSplitExit P intensity threshold
      basePending preCoins future =
      originMergedExit P intensity threshold
        basePending preCoins future := by
    funext c
    exact originSplitExit_eq_mergedExit c P intensity threshold
      basePending preCoins future
  rw [heq]
  exact OriginConfiguration.measurable_advance_mergedExit
    P intensity threshold hthreshold basePending preCoins future

set_option maxHeartbeats 1000000 in
theorem OriginConfiguration.measurable_advance_level_joint
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (fun z : OriginConfiguration n ×
        (Nat → LatticePoint n) =>
      (z.1.advance P intensity threshold basePending preCoins future
        z.2).level) := by
  have hpre : Measurable (fun c : OriginConfiguration n =>
      c.level + ttcPseudocode.firstLoopExit (c.state.removeComponent P)
        intensity threshold) :=
    measurable_fst.comp
      (OriginConfiguration.measurable_advance_controls
        P intensity threshold hthreshold)
  have heq : (fun z : OriginConfiguration n ×
      (Nat → LatticePoint n) =>
      (z.1.advance P intensity threshold basePending preCoins future
        z.2).level) =
      (fun z =>
        z.1.level + ttcPseudocode.firstLoopExit (z.1.state.removeComponent P)
          intensity threshold +
        originSplitExit P intensity threshold basePending
          preCoins future z.1) := by
    funext z
    exact z.1.advance_level P intensity threshold basePending
      preCoins future z.2
  rw [heq]
  exact (hpre.comp measurable_fst).add
    ((OriginConfiguration.measurable_advance_activeRounds
      P intensity threshold hthreshold basePending preCoins future).comp
        measurable_fst)

noncomputable def originMergedSecondResult
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool)
    (c : OriginConfiguration n) : TTCState n × Nat :=
  let z := originMergedExitInput P intensity threshold basePending
    preCoins future c
  ttcPseudocode.secondLoopResult z.1.1 z.1.2 threshold z.2

theorem measurable_originMergedSecondResult
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (originMergedSecondResult P intensity threshold
      basePending preCoins future) := by
  change Measurable ((fun z : (TTCState n × Nat) ×
    (Nat × Nat → Bool) => ttcPseudocode.secondLoopResult z.1.1 z.1.2 threshold z.2) ∘
      originMergedExitInput P intensity threshold
        basePending preCoins future)
  exact (measurable_thinningResult_joint threshold).comp
    (measurable_originMergedExitInput P intensity threshold
      hthreshold basePending preCoins future)

set_option maxHeartbeats 1000000 in
theorem originMergedSecondResult_eq_splitFinite
    {n : Nat} (c : OriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool) :
    originMergedSecondResult P intensity threshold basePending
      preCoins future c =
    let deleted := c.state.removeComponent P
    let oldCoins := sourceOldCoins c.origin c.source.coins c.level
    let rounds := ttcPseudocode.firstLoopExit deleted intensity threshold
    let preRounds := c.level + rounds
    let pending := pendingAfter preCoins preRounds deleted.nextLabel basePending
    let activeCoins := originalSurvivorCoinRestriction preCoins preRounds
      deleted.nextLabel basePending future
    let first := ttcPseudocode.firstLoopResult deleted intensity threshold
      oldCoins
    thinningResultSplitFinite first pending threshold
      (shiftCoins rounds oldCoins) activeCoins := by
  let deleted := c.state.removeComponent P
  let oldCoins := sourceOldCoins c.origin c.source.coins c.level
  let rounds := ttcPseudocode.firstLoopExit deleted intensity threshold
  let preRounds := c.level + rounds
  let pending := pendingAfter preCoins preRounds deleted.nextLabel basePending
  let activeCoins := originalSurvivorCoinRestriction preCoins preRounds
    deleted.nextLabel basePending future
  let first := ttcPseudocode.firstLoopResult deleted intensity threshold
    oldCoins
  have hdeleted : deleted.LabelsFresh :=
    c.state.labelsFresh_removeComponent P c.fresh
  have hfirst : first.LabelsFresh :=
    rateThinningResult_labelsFresh deleted intensity threshold
      oldCoins hdeleted
  exact thinningResult_mergeCoinsAtLabel first pending threshold
    (shiftCoins rounds oldCoins)
    (pendingCoinExtension deleted.nextLabel pending activeCoins) hfirst

end Kr25Ssmxt
