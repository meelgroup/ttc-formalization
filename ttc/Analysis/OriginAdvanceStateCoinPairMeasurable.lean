import ttc.Analysis.OriginAdvanceCoinPairMeasurable

/-! Executable-state projection of ghost advance with random coin arrays. -/

namespace ttc

open MeasureTheory

private abbrev GhostCoinInput' (n : Nat) :=
  OriginConfiguration n ×
    ((Nat × Nat → Bool) × (Nat × Nat → Bool))

noncomputable def originCoinPairMergedSecondResult
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (z : GhostCoinInput' n) : TTCState n × Nat :=
  let deleted := z.1.state.removeComponent P
  let oldCoins := sourceOldCoins z.1.origin z.1.source.coins
    z.1.level
  let rounds := ttcReference.firstLoopExit deleted intensity threshold
  let preRounds := z.1.level + rounds
  let pending := pendingAfter z.2.1 preRounds deleted.nextLabel basePending
  let first := ttcReference.firstLoopResult deleted intensity threshold
    oldCoins
  ttcPseudocode.secondLoopResult first pending threshold
    (mergeCoinsAtLabel deleted.nextLabel (shiftCoins rounds oldCoins)
      (pendingCoinExtension deleted.nextLabel pending
        (originalSurvivorCoinRestriction z.2.1 preRounds
          deleted.nextLabel basePending z.2.2)))

set_option maxHeartbeats 1000000 in
theorem measurable_originCoinPairMergedSecondResult
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (originCoinPairMergedSecondResult P intensity
      threshold basePending) := by
  have hfirst : Measurable (fun z : GhostCoinInput' n =>
      ttcReference.firstLoopResult (z.1.state.removeComponent P)
        intensity threshold
        (sourceOldCoins z.1.origin z.1.source.coins
          z.1.level)) :=
    (OriginConfiguration.measurable_advance_firstState
      P intensity threshold hthreshold).comp measurable_fst
  have hpending := OriginConfiguration.measurable_pending_coinPair
    P intensity threshold hthreshold basePending
  have hmerged := OriginConfiguration.measurable_mergedCoins_coinPair
    P intensity threshold hthreshold basePending
  exact (measurable_thinningResult_joint threshold).comp
    ((hfirst.prodMk hpending).prodMk hmerged)

set_option maxHeartbeats 1000000 in
theorem originCoinPairMergedSecondResult_eq_splitFinite
    {n : Nat} (z : GhostCoinInput' n)
    (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat) :
    originCoinPairMergedSecondResult P intensity threshold
      basePending z =
    let deleted := z.1.state.removeComponent P
    let oldCoins := sourceOldCoins z.1.origin z.1.source.coins
      z.1.level
    let rounds := ttcReference.firstLoopExit deleted intensity threshold
    let preRounds := z.1.level + rounds
    let pending := pendingAfter z.2.1 preRounds deleted.nextLabel basePending
    let activeCoins := originalSurvivorCoinRestriction z.2.1 preRounds
      deleted.nextLabel basePending z.2.2
    let first := ttcReference.firstLoopResult deleted intensity threshold
      oldCoins
    thinningResultSplitFinite first pending threshold
      (shiftCoins rounds oldCoins) activeCoins := by
  let deleted := z.1.state.removeComponent P
  let oldCoins := sourceOldCoins z.1.origin z.1.source.coins
    z.1.level
  let rounds := ttcReference.firstLoopExit deleted intensity threshold
  let preRounds := z.1.level + rounds
  let pending := pendingAfter z.2.1 preRounds deleted.nextLabel basePending
  let activeCoins := originalSurvivorCoinRestriction z.2.1 preRounds
    deleted.nextLabel basePending z.2.2
  let first := ttcReference.firstLoopResult deleted intensity threshold
    oldCoins
  have hdeleted : deleted.LabelsFresh :=
    z.1.state.labelsFresh_removeComponent P z.1.fresh
  have hfirst : first.LabelsFresh :=
    rateThinningResult_labelsFresh deleted intensity threshold
      oldCoins hdeleted
  exact thinningResult_mergeCoinsAtLabel first pending threshold
    (shiftCoins rounds oldCoins)
    (pendingCoinExtension deleted.nextLabel pending activeCoins) hfirst

noncomputable def originCoinPairStateTotal
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (z : GhostCoinInput' n)
    (tape : Nat → LatticePoint n) : TTCState n :=
  (originCoinPairMergedSecondResult P intensity threshold
    basePending z).1.addBatch
      (fun i : Fin (originCoinPairSecondCount P intensity
        threshold basePending z) =>
        tape (originCoinPairIndex P intensity threshold
          basePending z i.val))

set_option maxHeartbeats 1000000 in
theorem measurable_originCoinPairStateTotal
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (fun z : GhostCoinInput' n ×
        (Nat → LatticePoint n) =>
      originCoinPairStateTotal P intensity threshold
        basePending z.1 z.2) := by
  have hcount := measurable_originCoinPairSecondCount
    P intensity threshold hthreshold basePending
  have hstate : Measurable (fun z : GhostCoinInput' n =>
      (originCoinPairMergedSecondResult P intensity threshold
        basePending z).1) :=
    measurable_fst.comp
      (measurable_originCoinPairMergedSecondResult P intensity
        threshold hthreshold basePending)
  have hindex := measurable_originCoinPairIndex
    P intensity threshold hthreshold basePending
  exact measurable_addBatch_indexed_tape_joint.comp
    ((hcount.comp measurable_fst).prodMk
      (((hstate.comp measurable_fst).prodMk
        (hindex.comp measurable_fst)).prodMk measurable_snd))

set_option maxHeartbeats 1000000 in
theorem OriginConfiguration.advance_state_eq_coinPairTotal
    {n : Nat} (z : GhostCoinInput' n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (tape : Nat → LatticePoint n) :
    (z.1.advance P intensity threshold basePending z.2.1 z.2.2
      tape).state =
      originCoinPairStateTotal P intensity threshold
        basePending z tape := by
  let deleted := z.1.state.removeComponent P
  let oldCoins := sourceOldCoins z.1.origin z.1.source.coins
    z.1.level
  let rounds := ttcReference.firstLoopExit deleted intensity threshold
  let preRounds := z.1.level + rounds
  let pending := pendingAfter z.2.1 preRounds deleted.nextLabel basePending
  let activeCoins := originalSurvivorCoinRestriction z.2.1 preRounds
    deleted.nextLabel basePending z.2.2
  let first := ttcReference.firstLoopResult deleted intensity threshold
    oldCoins
  let activeRounds := originCoinPairSplitExit P intensity threshold
    basePending z
  let second := thinningResultSplitFinite first pending threshold
    (shiftCoins rounds oldCoins) activeCoins
  have hsecond : originCoinPairMergedSecondResult P intensity
      threshold basePending z = second :=
    originCoinPairMergedSecondResult_eq_splitFinite z P intensity
      threshold basePending
  have hcount : originCoinPairSecondCount P intensity threshold
      basePending z = second.2 := rfl
  change second.1.addBatch
      (fun i : Fin second.2 =>
        tape (twoStageSurvivorLabel z.2.1 preRounds deleted.nextLabel
          basePending activeCoins activeRounds i)) =
    (originCoinPairMergedSecondResult P intensity threshold
      basePending z).1.addBatch
        (fun i : Fin (originCoinPairSecondCount P intensity
          threshold basePending z) =>
          tape (originCoinPairIndex P intensity threshold
            basePending z i.val))
  rw [hsecond, hcount]
  congr 1
  funext i
  exact congrArg tape (twoStageSurvivorLabelOrZero_eq z.2.1 preRounds
    deleted.nextLabel basePending activeRounds activeCoins i).symm

set_option maxHeartbeats 1000000 in
theorem OriginConfiguration.measurable_advance_state_coinPair
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (fun z : GhostCoinInput' n ×
        (Nat → LatticePoint n) =>
      (z.1.1.advance P intensity threshold basePending z.1.2.1
        z.1.2.2 z.2).state) := by
  have heq : (fun z : GhostCoinInput' n ×
      (Nat → LatticePoint n) =>
      (z.1.1.advance P intensity threshold basePending z.1.2.1
        z.1.2.2 z.2).state) =
      (fun z => originCoinPairStateTotal P intensity threshold
        basePending z.1 z.2) := by
    funext z
    exact OriginConfiguration.advance_state_eq_coinPairTotal
      z.1 P intensity threshold basePending z.2
  rw [heq]
  exact measurable_originCoinPairStateTotal P intensity threshold
    hthreshold basePending

set_option maxHeartbeats 1000000 in
theorem OriginConfiguration.measurable_advance_coinPair
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (fun z : GhostCoinInput' n ×
        (Nat → LatticePoint n) =>
      z.1.1.advance P intensity threshold basePending z.1.2.1
        z.1.2.2 z.2) := by
  rw [measurable_comap_iff]
  exact (OriginConfiguration.measurable_advance_state_coinPair
      P intensity threshold hthreshold basePending).prodMk
    ((OriginConfiguration.measurable_advance_source_coinPair
      P intensity threshold hthreshold basePending).prodMk
      ((OriginConfiguration.measurable_advance_origin_coinPair
        P intensity threshold hthreshold basePending).prodMk
        (OriginConfiguration.measurable_advance_level_coinPair
          P intensity threshold hthreshold basePending)))

end ttc
