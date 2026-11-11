import Kr25Ssmxt.Analysis.ManuscriptOriginAdvanceCoinPairMeasurable

/-! Executable-state projection of ghost advance with random coin arrays. -/

namespace Kr25Ssmxt

open MeasureTheory

private abbrev ManuscriptGhostCoinInput' (n : Nat) :=
  ManuscriptOriginConfiguration n ×
    ((Nat × Nat → Bool) × (Nat × Nat → Bool))

noncomputable def manuscriptOriginCoinPairMergedSecondResult
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (z : ManuscriptGhostCoinInput' n) : TTCState n × Nat :=
  let deleted := z.1.state.removeComponent P
  let oldCoins := manuscriptSourceOldCoins z.1.origin z.1.source.coins
    z.1.level
  let rounds := ttcPseudocode.firstLoopExit deleted intensity threshold
  let preRounds := z.1.level + rounds
  let pending := pendingAfter z.2.1 preRounds deleted.nextLabel basePending
  let first := ttcPseudocode.firstLoopResult deleted intensity threshold
    oldCoins
  ttcPseudocode.secondLoopResult first pending threshold
    (mergeCoinsAtLabel deleted.nextLabel (shiftCoins rounds oldCoins)
      (pendingCoinExtension deleted.nextLabel pending
        (originalSurvivorCoinRestriction z.2.1 preRounds
          deleted.nextLabel basePending z.2.2)))

set_option maxHeartbeats 1000000 in
theorem measurable_manuscriptOriginCoinPairMergedSecondResult
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (manuscriptOriginCoinPairMergedSecondResult P intensity
      threshold basePending) := by
  have hfirst : Measurable (fun z : ManuscriptGhostCoinInput' n =>
      ttcPseudocode.firstLoopResult (z.1.state.removeComponent P)
        intensity threshold
        (manuscriptSourceOldCoins z.1.origin z.1.source.coins
          z.1.level)) :=
    (ManuscriptOriginConfiguration.measurable_advance_firstState
      P intensity threshold hthreshold).comp measurable_fst
  have hpending := ManuscriptOriginConfiguration.measurable_pending_coinPair
    P intensity threshold hthreshold basePending
  have hmerged := ManuscriptOriginConfiguration.measurable_mergedCoins_coinPair
    P intensity threshold hthreshold basePending
  exact (measurable_thinningResult_joint threshold).comp
    ((hfirst.prodMk hpending).prodMk hmerged)

set_option maxHeartbeats 1000000 in
theorem manuscriptOriginCoinPairMergedSecondResult_eq_splitFinite
    {n : Nat} (z : ManuscriptGhostCoinInput' n)
    (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat) :
    manuscriptOriginCoinPairMergedSecondResult P intensity threshold
      basePending z =
    let deleted := z.1.state.removeComponent P
    let oldCoins := manuscriptSourceOldCoins z.1.origin z.1.source.coins
      z.1.level
    let rounds := ttcPseudocode.firstLoopExit deleted intensity threshold
    let preRounds := z.1.level + rounds
    let pending := pendingAfter z.2.1 preRounds deleted.nextLabel basePending
    let activeCoins := originalSurvivorCoinRestriction z.2.1 preRounds
      deleted.nextLabel basePending z.2.2
    let first := ttcPseudocode.firstLoopResult deleted intensity threshold
      oldCoins
    thinningResultSplitFinite first pending threshold
      (shiftCoins rounds oldCoins) activeCoins := by
  let deleted := z.1.state.removeComponent P
  let oldCoins := manuscriptSourceOldCoins z.1.origin z.1.source.coins
    z.1.level
  let rounds := ttcPseudocode.firstLoopExit deleted intensity threshold
  let preRounds := z.1.level + rounds
  let pending := pendingAfter z.2.1 preRounds deleted.nextLabel basePending
  let activeCoins := originalSurvivorCoinRestriction z.2.1 preRounds
    deleted.nextLabel basePending z.2.2
  let first := ttcPseudocode.firstLoopResult deleted intensity threshold
    oldCoins
  have hdeleted : deleted.LabelsFresh :=
    z.1.state.labelsFresh_removeComponent P z.1.fresh
  have hfirst : first.LabelsFresh :=
    manuscriptRateThinningResult_labelsFresh deleted intensity threshold
      oldCoins hdeleted
  exact thinningResult_mergeCoinsAtLabel first pending threshold
    (shiftCoins rounds oldCoins)
    (pendingCoinExtension deleted.nextLabel pending activeCoins) hfirst

noncomputable def manuscriptOriginCoinPairStateTotal
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (z : ManuscriptGhostCoinInput' n)
    (tape : Nat → LatticePoint n) : TTCState n :=
  (manuscriptOriginCoinPairMergedSecondResult P intensity threshold
    basePending z).1.addBatch
      (fun i : Fin (manuscriptOriginCoinPairSecondCount P intensity
        threshold basePending z) =>
        tape (manuscriptOriginCoinPairIndex P intensity threshold
          basePending z i.val))

set_option maxHeartbeats 1000000 in
theorem measurable_manuscriptOriginCoinPairStateTotal
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (fun z : ManuscriptGhostCoinInput' n ×
        (Nat → LatticePoint n) =>
      manuscriptOriginCoinPairStateTotal P intensity threshold
        basePending z.1 z.2) := by
  have hcount := measurable_manuscriptOriginCoinPairSecondCount
    P intensity threshold hthreshold basePending
  have hstate : Measurable (fun z : ManuscriptGhostCoinInput' n =>
      (manuscriptOriginCoinPairMergedSecondResult P intensity threshold
        basePending z).1) :=
    measurable_fst.comp
      (measurable_manuscriptOriginCoinPairMergedSecondResult P intensity
        threshold hthreshold basePending)
  have hindex := measurable_manuscriptOriginCoinPairIndex
    P intensity threshold hthreshold basePending
  exact measurable_addBatch_indexed_tape_joint.comp
    ((hcount.comp measurable_fst).prodMk
      (((hstate.comp measurable_fst).prodMk
        (hindex.comp measurable_fst)).prodMk measurable_snd))

set_option maxHeartbeats 1000000 in
theorem ManuscriptOriginConfiguration.advance_state_eq_coinPairTotal
    {n : Nat} (z : ManuscriptGhostCoinInput' n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (tape : Nat → LatticePoint n) :
    (z.1.advance P intensity threshold basePending z.2.1 z.2.2
      tape).state =
      manuscriptOriginCoinPairStateTotal P intensity threshold
        basePending z tape := by
  let deleted := z.1.state.removeComponent P
  let oldCoins := manuscriptSourceOldCoins z.1.origin z.1.source.coins
    z.1.level
  let rounds := ttcPseudocode.firstLoopExit deleted intensity threshold
  let preRounds := z.1.level + rounds
  let pending := pendingAfter z.2.1 preRounds deleted.nextLabel basePending
  let activeCoins := originalSurvivorCoinRestriction z.2.1 preRounds
    deleted.nextLabel basePending z.2.2
  let first := ttcPseudocode.firstLoopResult deleted intensity threshold
    oldCoins
  let activeRounds := manuscriptOriginCoinPairSplitExit P intensity threshold
    basePending z
  let second := thinningResultSplitFinite first pending threshold
    (shiftCoins rounds oldCoins) activeCoins
  have hsecond : manuscriptOriginCoinPairMergedSecondResult P intensity
      threshold basePending z = second :=
    manuscriptOriginCoinPairMergedSecondResult_eq_splitFinite z P intensity
      threshold basePending
  have hcount : manuscriptOriginCoinPairSecondCount P intensity threshold
      basePending z = second.2 := rfl
  change second.1.addBatch
      (fun i : Fin second.2 =>
        tape (twoStageSurvivorLabel z.2.1 preRounds deleted.nextLabel
          basePending activeCoins activeRounds i)) =
    (manuscriptOriginCoinPairMergedSecondResult P intensity threshold
      basePending z).1.addBatch
        (fun i : Fin (manuscriptOriginCoinPairSecondCount P intensity
          threshold basePending z) =>
          tape (manuscriptOriginCoinPairIndex P intensity threshold
            basePending z i.val))
  rw [hsecond, hcount]
  congr 1
  funext i
  exact congrArg tape (twoStageSurvivorLabelOrZero_eq z.2.1 preRounds
    deleted.nextLabel basePending activeRounds activeCoins i).symm

set_option maxHeartbeats 1000000 in
theorem ManuscriptOriginConfiguration.measurable_advance_state_coinPair
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (fun z : ManuscriptGhostCoinInput' n ×
        (Nat → LatticePoint n) =>
      (z.1.1.advance P intensity threshold basePending z.1.2.1
        z.1.2.2 z.2).state) := by
  have heq : (fun z : ManuscriptGhostCoinInput' n ×
      (Nat → LatticePoint n) =>
      (z.1.1.advance P intensity threshold basePending z.1.2.1
        z.1.2.2 z.2).state) =
      (fun z => manuscriptOriginCoinPairStateTotal P intensity threshold
        basePending z.1 z.2) := by
    funext z
    exact ManuscriptOriginConfiguration.advance_state_eq_coinPairTotal
      z.1 P intensity threshold basePending z.2
  rw [heq]
  exact measurable_manuscriptOriginCoinPairStateTotal P intensity threshold
    hthreshold basePending

set_option maxHeartbeats 1000000 in
theorem ManuscriptOriginConfiguration.measurable_advance_coinPair
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (fun z : ManuscriptGhostCoinInput' n ×
        (Nat → LatticePoint n) =>
      z.1.1.advance P intensity threshold basePending z.1.2.1
        z.1.2.2 z.2) := by
  rw [measurable_comap_iff]
  exact (ManuscriptOriginConfiguration.measurable_advance_state_coinPair
      P intensity threshold hthreshold basePending).prodMk
    ((ManuscriptOriginConfiguration.measurable_advance_source_coinPair
      P intensity threshold hthreshold basePending).prodMk
      ((ManuscriptOriginConfiguration.measurable_advance_origin_coinPair
        P intensity threshold hthreshold basePending).prodMk
        (ManuscriptOriginConfiguration.measurable_advance_level_coinPair
          P intensity threshold hthreshold basePending)))

end Kr25Ssmxt
