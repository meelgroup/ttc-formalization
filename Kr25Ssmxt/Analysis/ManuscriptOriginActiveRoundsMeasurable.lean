import Kr25Ssmxt.Analysis.ManuscriptOriginOldCoinsMeasurable

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
theorem ManuscriptOriginConfiguration.measurable_advance_firstState
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold) :
    Measurable (fun c : ManuscriptOriginConfiguration n =>
      ttcPseudocode.firstLoopResult (c.state.removeComponent P)
        intensity threshold
        (manuscriptSourceOldCoins c.origin c.source.coins c.level)) := by
  have hdeleted : Measurable (fun c : ManuscriptOriginConfiguration n =>
      c.state.removeComponent P) :=
    (measurable_removeComponent P).comp
      measurable_manuscriptOriginConfiguration_state
  exact (measurable_manuscriptRateThinningResult_joint
    threshold hthreshold).comp
      ((hdeleted.prodMk measurable_const).prodMk
        measurable_manuscriptSourceOldCoins_joint)

theorem ManuscriptOriginConfiguration.measurable_advance_pending
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins : Nat × Nat → Bool) :
    Measurable (fun c : ManuscriptOriginConfiguration n =>
      pendingAfter preCoins
        (c.level + ttcPseudocode.firstLoopExit (c.state.removeComponent P)
          intensity threshold)
        (c.state.removeComponent P).nextLabel basePending) := by
  exact (measurable_of_countable
    (fun params : Nat × Nat =>
      pendingAfter preCoins params.1 params.2 basePending)).comp
        (ManuscriptOriginConfiguration.measurable_advance_controls
          P intensity threshold hthreshold)

set_option maxHeartbeats 1000000 in
theorem ManuscriptOriginConfiguration.measurable_advance_shiftedOldCoins
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold) :
    Measurable (fun c : ManuscriptOriginConfiguration n =>
      shiftCoins
        (ttcPseudocode.firstLoopExit (c.state.removeComponent P) intensity
          threshold)
        (manuscriptSourceOldCoins c.origin c.source.coins c.level)) := by
  have hdeleted : Measurable (fun c : ManuscriptOriginConfiguration n =>
      c.state.removeComponent P) :=
    (measurable_removeComponent P).comp
      measurable_manuscriptOriginConfiguration_state
  have hround : Measurable (fun c : ManuscriptOriginConfiguration n =>
      ttcPseudocode.firstLoopExit (c.state.removeComponent P) intensity
        threshold) :=
    (measurable_manuscriptRateExit_joint threshold hthreshold).comp
      (hdeleted.prodMk measurable_const)
  exact measurable_shiftCoins_joint.comp
    (hround.prodMk measurable_manuscriptSourceOldCoins_joint)

set_option maxHeartbeats 1000000 in
theorem ManuscriptOriginConfiguration.measurable_advance_mergedCoins
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (fun c : ManuscriptOriginConfiguration n =>
      let deleted := c.state.removeComponent P
      let preRounds := c.level + ttcPseudocode.firstLoopExit deleted intensity
        threshold
      mergeCoinsAtLabel deleted.nextLabel
        (shiftCoins (ttcPseudocode.firstLoopExit deleted intensity threshold)
          (manuscriptSourceOldCoins c.origin c.source.coins c.level))
        (pendingCoinExtension deleted.nextLabel
          (pendingAfter preCoins preRounds deleted.nextLabel basePending)
          (originalSurvivorCoinRestriction preCoins preRounds
            deleted.nextLabel basePending future))) := by
  have hlabel : Measurable (fun c : ManuscriptOriginConfiguration n =>
      (c.state.removeComponent P).nextLabel) :=
    measurable_snd.comp
      (ManuscriptOriginConfiguration.measurable_advance_controls
        P intensity threshold hthreshold)
  exact measurable_mergeCoinsAtLabel_joint.comp
    (hlabel.prodMk
      ((ManuscriptOriginConfiguration.measurable_advance_shiftedOldCoins
          P intensity threshold hthreshold).prodMk
        (ManuscriptOriginConfiguration.measurable_activeFullCoins
          P intensity threshold hthreshold basePending preCoins future)))

private noncomputable def manuscriptOriginMergedExitInput
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool) :
    ManuscriptOriginConfiguration n →
      (TTCState n × Nat) × (Nat × Nat → Bool) := fun c =>
      let deleted := c.state.removeComponent P
      let rounds := ttcPseudocode.firstLoopExit deleted intensity threshold
      let preRounds := c.level + rounds
      let pending := pendingAfter preCoins preRounds deleted.nextLabel
        basePending
      let first := ttcPseudocode.firstLoopResult deleted intensity
        threshold (manuscriptSourceOldCoins c.origin c.source.coins c.level)
      ((first, pending),
        (mergeCoinsAtLabel deleted.nextLabel
          (shiftCoins rounds
            (manuscriptSourceOldCoins c.origin c.source.coins c.level))
          (pendingCoinExtension deleted.nextLabel pending
            (originalSurvivorCoinRestriction preCoins preRounds
              deleted.nextLabel basePending future))))

set_option maxHeartbeats 1000000 in
private theorem measurable_manuscriptOriginMergedExitInput
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (manuscriptOriginMergedExitInput P intensity threshold
      basePending preCoins future) := by
  unfold manuscriptOriginMergedExitInput
  exact
    (((ManuscriptOriginConfiguration.measurable_advance_firstState
        P intensity threshold hthreshold).prodMk
      (ManuscriptOriginConfiguration.measurable_advance_pending
        P intensity threshold hthreshold basePending preCoins)).prodMk
      (ManuscriptOriginConfiguration.measurable_advance_mergedCoins
        P intensity threshold hthreshold basePending preCoins future))

private noncomputable def manuscriptOriginMergedExit
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool) :
    ManuscriptOriginConfiguration n → Nat :=
  fun c =>
    let z := manuscriptOriginMergedExitInput P intensity threshold
      basePending preCoins future c
    ttcPseudocode.secondLoopExitRound z.1.1 z.1.2 threshold z.2

theorem ManuscriptOriginConfiguration.measurable_advance_mergedExit
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (manuscriptOriginMergedExit P intensity threshold
      basePending preCoins future) := by
  change Measurable ((fun z : (TTCState n × Nat) ×
    (Nat × Nat → Bool) => ttcPseudocode.secondLoopExitRound z.1.1 z.1.2 threshold z.2) ∘
      manuscriptOriginMergedExitInput P intensity threshold
        basePending preCoins future)
  exact (measurable_firstExitRound_joint threshold).comp
    (measurable_manuscriptOriginMergedExitInput P intensity threshold
      hthreshold basePending preCoins future)

noncomputable def manuscriptOriginSplitExit
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool) :
    ManuscriptOriginConfiguration n → Nat := fun c =>
  let deleted := c.state.removeComponent P
  let oldCoins := manuscriptSourceOldCoins c.origin c.source.coins c.level
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
private theorem manuscriptOriginSplitExit_eq_mergedExit
    {n : Nat} (c : ManuscriptOriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool) :
    manuscriptOriginSplitExit P intensity threshold basePending
      preCoins future c =
    manuscriptOriginMergedExit P intensity threshold basePending
      preCoins future c := by
  let deleted := c.state.removeComponent P
  let oldCoins := manuscriptSourceOldCoins c.origin c.source.coins c.level
  have hdeleted : deleted.LabelsFresh :=
    c.state.labelsFresh_removeComponent P c.fresh
  have hfirst : (ttcPseudocode.firstLoopResult deleted intensity threshold
      oldCoins).LabelsFresh :=
    manuscriptRateThinningResult_labelsFresh deleted intensity threshold
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

theorem ManuscriptOriginConfiguration.measurable_advance_activeRounds
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (manuscriptOriginSplitExit P intensity threshold
      basePending preCoins future) := by
  have heq : manuscriptOriginSplitExit P intensity threshold
      basePending preCoins future =
      manuscriptOriginMergedExit P intensity threshold
        basePending preCoins future := by
    funext c
    exact manuscriptOriginSplitExit_eq_mergedExit c P intensity threshold
      basePending preCoins future
  rw [heq]
  exact ManuscriptOriginConfiguration.measurable_advance_mergedExit
    P intensity threshold hthreshold basePending preCoins future

set_option maxHeartbeats 1000000 in
theorem ManuscriptOriginConfiguration.measurable_advance_level_joint
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (fun z : ManuscriptOriginConfiguration n ×
        (Nat → LatticePoint n) =>
      (z.1.advance P intensity threshold basePending preCoins future
        z.2).level) := by
  have hpre : Measurable (fun c : ManuscriptOriginConfiguration n =>
      c.level + ttcPseudocode.firstLoopExit (c.state.removeComponent P)
        intensity threshold) :=
    measurable_fst.comp
      (ManuscriptOriginConfiguration.measurable_advance_controls
        P intensity threshold hthreshold)
  have heq : (fun z : ManuscriptOriginConfiguration n ×
      (Nat → LatticePoint n) =>
      (z.1.advance P intensity threshold basePending preCoins future
        z.2).level) =
      (fun z =>
        z.1.level + ttcPseudocode.firstLoopExit (z.1.state.removeComponent P)
          intensity threshold +
        manuscriptOriginSplitExit P intensity threshold basePending
          preCoins future z.1) := by
    funext z
    exact z.1.advance_level P intensity threshold basePending
      preCoins future z.2
  rw [heq]
  exact (hpre.comp measurable_fst).add
    ((ManuscriptOriginConfiguration.measurable_advance_activeRounds
      P intensity threshold hthreshold basePending preCoins future).comp
        measurable_fst)

noncomputable def manuscriptOriginMergedSecondResult
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool)
    (c : ManuscriptOriginConfiguration n) : TTCState n × Nat :=
  let z := manuscriptOriginMergedExitInput P intensity threshold basePending
    preCoins future c
  ttcPseudocode.secondLoopResult z.1.1 z.1.2 threshold z.2

theorem measurable_manuscriptOriginMergedSecondResult
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (manuscriptOriginMergedSecondResult P intensity threshold
      basePending preCoins future) := by
  change Measurable ((fun z : (TTCState n × Nat) ×
    (Nat × Nat → Bool) => ttcPseudocode.secondLoopResult z.1.1 z.1.2 threshold z.2) ∘
      manuscriptOriginMergedExitInput P intensity threshold
        basePending preCoins future)
  exact (measurable_thinningResult_joint threshold).comp
    (measurable_manuscriptOriginMergedExitInput P intensity threshold
      hthreshold basePending preCoins future)

set_option maxHeartbeats 1000000 in
theorem manuscriptOriginMergedSecondResult_eq_splitFinite
    {n : Nat} (c : ManuscriptOriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool) :
    manuscriptOriginMergedSecondResult P intensity threshold basePending
      preCoins future c =
    let deleted := c.state.removeComponent P
    let oldCoins := manuscriptSourceOldCoins c.origin c.source.coins c.level
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
  let oldCoins := manuscriptSourceOldCoins c.origin c.source.coins c.level
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
    manuscriptRateThinningResult_labelsFresh deleted intensity threshold
      oldCoins hdeleted
  exact thinningResult_mergeCoinsAtLabel first pending threshold
    (shiftCoins rounds oldCoins)
    (pendingCoinExtension deleted.nextLabel pending activeCoins) hfirst

end Kr25Ssmxt
