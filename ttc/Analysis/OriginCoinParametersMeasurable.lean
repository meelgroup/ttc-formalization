import ttc.Analysis.OriginCountTapeKernel

/-! Measurability when both independent coin arrays are random. -/

namespace ttc

open MeasureTheory

theorem measurable_originalSurvivorCoinExtension_coinPair_fixed
    (preRounds firstLabel basePending : Nat) :
    Measurable (fun coins : (Nat × Nat → Bool) × (Nat × Nat → Bool) =>
      pendingCoinExtension firstLabel
        (pendingAfter coins.1 preRounds firstLabel basePending)
        (originalSurvivorCoinRestriction coins.1 preRounds firstLabel
          basePending coins.2)) := by
  have heval : Measurable (fun z : (Nat × Nat → Bool) × (Nat × Nat) =>
      z.1 z.2) := by
    apply measurable_from_prod_countable_left
    intro index
    exact measurable_pi_apply index
  have hcount : Measurable (fun coins :
      (Nat × Nat → Bool) × (Nat × Nat → Bool) =>
      pendingAfter coins.1 preRounds firstLabel basePending) :=
    (measurable_pendingAfter_fixed preRounds firstLabel basePending).comp
      measurable_fst
  apply Measurable.of_eval
  intro pair
  have hselect : Measurable (fun coins :
      (Nat × Nat → Bool) × (Nat × Nat → Bool) =>
      pendingSurvivorIndexOrZero coins.1 preRounds firstLabel
        basePending (pair.2 - firstLabel)) :=
    (measurable_pendingSurvivorIndexOrZero_fixed preRounds firstLabel
      basePending (pair.2 - firstLabel)).comp measurable_fst
  have hvalue : Measurable (fun coins :
      (Nat × Nat → Bool) × (Nat × Nat → Bool) =>
      coins.2 (pair.1, firstLabel +
        pendingSurvivorIndexOrZero coins.1 preRounds firstLabel
          basePending (pair.2 - firstLabel))) :=
    heval.comp (measurable_snd.prodMk
      (measurable_const.prodMk (measurable_const.add hselect)))
  have hcond : MeasurableSet {coins :
      (Nat × Nat → Bool) × (Nat × Nat → Bool) |
      firstLabel ≤ pair.2 ∧
        pair.2 < firstLabel +
          pendingAfter coins.1 preRounds firstLabel basePending} := by
    exact measurableSet_setOfPred.mpr
      ((measurable_of_countable (fun pending : Nat =>
        firstLabel ≤ pair.2 ∧ pair.2 < firstLabel + pending)).comp hcount)
  have heq : (fun coins :
      (Nat × Nat → Bool) × (Nat × Nat → Bool) =>
      pendingCoinExtension firstLabel
        (pendingAfter coins.1 preRounds firstLabel basePending)
        (originalSurvivorCoinRestriction coins.1 preRounds firstLabel
          basePending coins.2) pair) =
      (fun coins => if firstLabel ≤ pair.2 ∧
          pair.2 < firstLabel +
            pendingAfter coins.1 preRounds firstLabel basePending then
        coins.2 (pair.1, firstLabel +
          pendingSurvivorIndexOrZero coins.1 preRounds firstLabel
            basePending (pair.2 - firstLabel)) else true) := by
    funext coins
    by_cases h : firstLabel ≤ pair.2 ∧
        pair.2 < firstLabel +
          pendingAfter coins.1 preRounds firstLabel basePending
    · have hi : pair.2 - firstLabel <
          pendingAfter coins.1 preRounds firstLabel basePending := by omega
      simp [pendingCoinExtension, originalSurvivorCoinRestriction, h,
        pendingSurvivorIndexOrZero_of_lt coins.1 preRounds firstLabel
          basePending (pair.2 - firstLabel) hi]
    · simp [pendingCoinExtension, h]
  rw [heq]
  exact Measurable.ite hcond hvalue measurable_const

theorem measurable_originalSurvivorCoinExtension_joint
    (basePending : Nat) :
    Measurable (fun z : (Nat × Nat) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      pendingCoinExtension z.1.2
        (pendingAfter z.2.1 z.1.1 z.1.2 basePending)
        (originalSurvivorCoinRestriction z.2.1 z.1.1 z.1.2
          basePending z.2.2)) := by
  apply measurable_from_prod_countable_right
  intro params
  exact measurable_originalSurvivorCoinExtension_coinPair_fixed
    params.1 params.2 basePending

set_option maxHeartbeats 1000000 in
theorem OriginConfiguration.measurable_activeFullCoins_coinPair
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (fun z : OriginConfiguration n ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      let deleted := z.1.state.removeComponent P
      let preRounds := z.1.level + ttcReference.firstLoopExit deleted intensity
        threshold
      pendingCoinExtension deleted.nextLabel
        (pendingAfter z.2.1 preRounds deleted.nextLabel basePending)
        (originalSurvivorCoinRestriction z.2.1 preRounds
          deleted.nextLabel basePending z.2.2)) := by
  exact (measurable_originalSurvivorCoinExtension_joint basePending).comp
    (((OriginConfiguration.measurable_advance_controls
      P intensity threshold hthreshold).comp measurable_fst).prodMk
      measurable_snd)

theorem OriginConfiguration.measurable_pending_coinPair
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (fun z : OriginConfiguration n ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      pendingAfter z.2.1
        (z.1.level + ttcReference.firstLoopExit (z.1.state.removeComponent P)
          intensity threshold)
        (z.1.state.removeComponent P).nextLabel basePending) := by
  have hcontrols : Measurable (fun z : OriginConfiguration n ×
      ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      (z.1.level + ttcReference.firstLoopExit (z.1.state.removeComponent P)
        intensity threshold, (z.1.state.removeComponent P).nextLabel)) :=
    (OriginConfiguration.measurable_advance_controls
      P intensity threshold hthreshold).comp measurable_fst
  exact measurable_pendingAfter_joint.comp
    (((measurable_fst.comp hcontrols).prodMk
      ((measurable_snd.comp hcontrols).prodMk measurable_const)).prodMk
      (measurable_fst.comp measurable_snd))

set_option maxHeartbeats 1000000 in
theorem OriginConfiguration.measurable_mergedCoins_coinPair
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (fun z : OriginConfiguration n ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      let deleted := z.1.state.removeComponent P
      let preRounds := z.1.level + ttcReference.firstLoopExit deleted intensity
        threshold
      mergeCoinsAtLabel deleted.nextLabel
        (shiftCoins (ttcReference.firstLoopExit deleted intensity threshold)
          (sourceOldCoins z.1.origin z.1.source.coins
            z.1.level))
        (pendingCoinExtension deleted.nextLabel
          (pendingAfter z.2.1 preRounds deleted.nextLabel basePending)
          (originalSurvivorCoinRestriction z.2.1 preRounds
            deleted.nextLabel basePending z.2.2))) := by
  have hlabel : Measurable (fun z : OriginConfiguration n ×
      ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      (z.1.state.removeComponent P).nextLabel) :=
    (measurable_snd.comp
      (OriginConfiguration.measurable_advance_controls
        P intensity threshold hthreshold)).comp measurable_fst
  have hshift : Measurable (fun z : OriginConfiguration n ×
      ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      shiftCoins
        (ttcReference.firstLoopExit (z.1.state.removeComponent P) intensity
          threshold)
        (sourceOldCoins z.1.origin z.1.source.coins
          z.1.level)) :=
    (OriginConfiguration.measurable_advance_shiftedOldCoins
      P intensity threshold hthreshold).comp measurable_fst
  exact measurable_mergeCoinsAtLabel_joint.comp
    (hlabel.prodMk
      (hshift.prodMk
        (OriginConfiguration.measurable_activeFullCoins_coinPair
          P intensity threshold hthreshold basePending)))

private noncomputable def originCoinPairMergedInput
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat) :
    OriginConfiguration n ×
      ((Nat × Nat → Bool) × (Nat × Nat → Bool)) →
      (TTCState n × Nat) × (Nat × Nat → Bool) := fun z =>
  let deleted := z.1.state.removeComponent P
  let oldCoins := sourceOldCoins z.1.origin z.1.source.coins
    z.1.level
  let rounds := ttcReference.firstLoopExit deleted intensity threshold
  let preRounds := z.1.level + rounds
  let pending := pendingAfter z.2.1 preRounds deleted.nextLabel basePending
  let first := ttcReference.firstLoopResult deleted intensity threshold
    oldCoins
  ((first, pending),
    mergeCoinsAtLabel deleted.nextLabel (shiftCoins rounds oldCoins)
      (pendingCoinExtension deleted.nextLabel pending
        (originalSurvivorCoinRestriction z.2.1 preRounds
          deleted.nextLabel basePending z.2.2)))

set_option maxHeartbeats 1000000 in
private theorem measurable_originCoinPairMergedInput
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (originCoinPairMergedInput P intensity threshold
      basePending) := by
  unfold originCoinPairMergedInput
  exact (((OriginConfiguration.measurable_advance_firstState
    P intensity threshold hthreshold).comp measurable_fst).prodMk
      (OriginConfiguration.measurable_pending_coinPair
        P intensity threshold hthreshold basePending)).prodMk
      (OriginConfiguration.measurable_mergedCoins_coinPair
        P intensity threshold hthreshold basePending)

noncomputable def originCoinPairMergedExit
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat) :
    OriginConfiguration n ×
      ((Nat × Nat → Bool) × (Nat × Nat → Bool)) → Nat := fun z =>
  let input := originCoinPairMergedInput P intensity threshold
    basePending z
  ttcPseudocode.secondLoopExitRound input.1.1 input.1.2 threshold input.2

theorem measurable_originCoinPairMergedExit
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (originCoinPairMergedExit P intensity threshold
      basePending) := by
  change Measurable ((fun input : (TTCState n × Nat) ×
    (Nat × Nat → Bool) =>
      ttcPseudocode.secondLoopExitRound input.1.1 input.1.2 threshold input.2) ∘
        originCoinPairMergedInput P intensity threshold basePending)
  exact (measurable_firstExitRound_joint threshold).comp
    (measurable_originCoinPairMergedInput P intensity threshold
      hthreshold basePending)

noncomputable def originCoinPairSplitExit
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat) :
    OriginConfiguration n ×
      ((Nat × Nat → Bool) × (Nat × Nat → Bool)) → Nat := fun z =>
  let deleted := z.1.state.removeComponent P
  let oldCoins := sourceOldCoins z.1.origin z.1.source.coins
    z.1.level
  let rounds := ttcReference.firstLoopExit deleted intensity threshold
  let preRounds := z.1.level + rounds
  let pending := pendingAfter z.2.1 preRounds deleted.nextLabel basePending
  let first := ttcReference.firstLoopResult deleted intensity threshold
    oldCoins
  firstExitRoundSplit first pending threshold (shiftCoins rounds oldCoins)
    (pendingCoinExtension deleted.nextLabel pending
      (originalSurvivorCoinRestriction z.2.1 preRounds
        deleted.nextLabel basePending z.2.2))

set_option maxHeartbeats 1000000 in
theorem originCoinPairSplitExit_eq_mergedExit
    {n : Nat} (z : OriginConfiguration n ×
      ((Nat × Nat → Bool) × (Nat × Nat → Bool)))
    (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat) :
    originCoinPairSplitExit P intensity threshold basePending z =
      originCoinPairMergedExit P intensity threshold
        basePending z := by
  let deleted := z.1.state.removeComponent P
  let oldCoins := sourceOldCoins z.1.origin z.1.source.coins
    z.1.level
  let rounds := ttcReference.firstLoopExit deleted intensity threshold
  let preRounds := z.1.level + rounds
  let pending := pendingAfter z.2.1 preRounds deleted.nextLabel basePending
  let first := ttcReference.firstLoopResult deleted intensity threshold
    oldCoins
  have hdeleted : deleted.LabelsFresh :=
    z.1.state.labelsFresh_removeComponent P z.1.fresh
  have hfirst : first.LabelsFresh :=
    rateThinningResult_labelsFresh deleted intensity threshold
      oldCoins hdeleted
  exact (firstExitRound_mergeCoinsAtLabel first pending threshold
    (shiftCoins rounds oldCoins)
    (pendingCoinExtension deleted.nextLabel pending
      (originalSurvivorCoinRestriction z.2.1 preRounds
        deleted.nextLabel basePending z.2.2)) hfirst).symm

theorem measurable_originCoinPairSplitExit
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (originCoinPairSplitExit P intensity threshold
      basePending) := by
  have heq : originCoinPairSplitExit P intensity threshold
      basePending =
      originCoinPairMergedExit P intensity threshold
        basePending := by
    funext z
    exact originCoinPairSplitExit_eq_mergedExit z P intensity
      threshold basePending
  rw [heq]
  exact measurable_originCoinPairMergedExit P intensity
    threshold hthreshold basePending

end ttc
