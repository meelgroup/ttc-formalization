import Kr25Ssmxt.Analysis.OriginSourceCoinPairMeasurable

/-! Origin labels and survivor counts with both coin arrays random. -/

namespace Kr25Ssmxt

open MeasureTheory

private abbrev GhostCoinInput (n : Nat) :=
  OriginConfiguration n ×
    ((Nat × Nat → Bool) × (Nat × Nat → Bool))

noncomputable def originCoinPairActiveFull
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (z : GhostCoinInput n) : Nat × Nat → Bool :=
  let deleted := z.1.state.removeComponent P
  let preRounds := z.1.level + ttcPseudocode.firstLoopExit deleted intensity threshold
  pendingCoinExtension deleted.nextLabel
    (pendingAfter z.2.1 preRounds deleted.nextLabel basePending)
    (originalSurvivorCoinRestriction z.2.1 preRounds deleted.nextLabel
      basePending z.2.2)

theorem measurable_originCoinPairActiveFull
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (originCoinPairActiveFull P intensity threshold
      basePending) :=
  OriginConfiguration.measurable_activeFullCoins_coinPair
    P intensity threshold hthreshold basePending

noncomputable def originCoinPairSecondCount
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (z : GhostCoinInput n) : Nat :=
  let deleted := z.1.state.removeComponent P
  let preRounds := z.1.level + ttcPseudocode.firstLoopExit deleted intensity threshold
  let pending := pendingAfter z.2.1 preRounds deleted.nextLabel basePending
  pendingAfter (originCoinPairActiveFull P intensity threshold
    basePending z)
    (originCoinPairSplitExit P intensity threshold basePending z)
    deleted.nextLabel pending

set_option maxHeartbeats 1000000 in
theorem measurable_originCoinPairSecondCount
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (originCoinPairSecondCount P intensity threshold
      basePending) := by
  have hcontrols : Measurable (fun z : GhostCoinInput n =>
      (z.1.level + ttcPseudocode.firstLoopExit (z.1.state.removeComponent P)
        intensity threshold, (z.1.state.removeComponent P).nextLabel)) :=
    (OriginConfiguration.measurable_advance_controls
      P intensity threshold hthreshold).comp measurable_fst
  have hlabel : Measurable (fun z : GhostCoinInput n =>
      (z.1.state.removeComponent P).nextLabel) :=
    measurable_snd.comp hcontrols
  have hpending := OriginConfiguration.measurable_pending_coinPair
    P intensity threshold hthreshold basePending
  have hrounds := measurable_originCoinPairSplitExit
    P intensity threshold hthreshold basePending
  have hactive := measurable_originCoinPairActiveFull
    P intensity threshold hthreshold basePending
  exact measurable_pendingAfter_joint.comp
    ((hrounds.prodMk (hlabel.prodMk hpending)).prodMk hactive)

noncomputable def originCoinPairIndex
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (z : GhostCoinInput n) : Nat → Nat := fun i =>
  let deleted := z.1.state.removeComponent P
  let preRounds := z.1.level + ttcPseudocode.firstLoopExit deleted intensity threshold
  twoStageSurvivorLabelOrZero z.2.1
    (originCoinPairActiveFull P intensity threshold basePending z)
    preRounds deleted.nextLabel basePending
    (originCoinPairSplitExit P intensity threshold basePending z) i

set_option maxHeartbeats 1000000 in
theorem measurable_originCoinPairIndex
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (originCoinPairIndex P intensity threshold
      basePending) := by
  have hcontrols : Measurable (fun z : GhostCoinInput n =>
      (z.1.level + ttcPseudocode.firstLoopExit (z.1.state.removeComponent P)
        intensity threshold, (z.1.state.removeComponent P).nextLabel)) :=
    (OriginConfiguration.measurable_advance_controls
      P intensity threshold hthreshold).comp measurable_fst
  have hpre : Measurable (fun z : GhostCoinInput n =>
      z.1.level + ttcPseudocode.firstLoopExit (z.1.state.removeComponent P)
        intensity threshold) := measurable_fst.comp hcontrols
  have hlabel : Measurable (fun z : GhostCoinInput n =>
      (z.1.state.removeComponent P).nextLabel) :=
    measurable_snd.comp hcontrols
  have hrounds := measurable_originCoinPairSplitExit
    P intensity threshold hthreshold basePending
  have hactive := measurable_originCoinPairActiveFull
    P intensity threshold hthreshold basePending
  apply Measurable.of_eval
  intro i
  exact measurable_twoStageSurvivorLabelOrZero_joint.comp
    ((hpre.prodMk
      (hlabel.prodMk
        (measurable_const.prodMk
          (hrounds.prodMk measurable_const)))).prodMk
      ((measurable_fst.comp measurable_snd).prodMk hactive))

noncomputable def originCoinPairOriginTotal
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (z : GhostCoinInput n) : Nat → Nat × Nat :=
  originAppend z.1.origin z.1.source.processed
    (z.1.state.removeComponent P).nextLabel
    (originCoinPairSecondCount P intensity threshold
      basePending z)
    (fun i => originCoinPairIndex P intensity threshold
      basePending z i.val)

set_option maxHeartbeats 1000000 in
theorem measurable_originCoinPairOriginTotal
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (originCoinPairOriginTotal P intensity threshold
      basePending) := by
  have hcomponent : Measurable (fun z : GhostCoinInput n =>
      z.1.source.processed) :=
    (measurable_originSourceState_processed.comp
      measurable_originConfiguration_source).comp measurable_fst
  have hlabel : Measurable (fun z : GhostCoinInput n =>
      (z.1.state.removeComponent P).nextLabel) :=
    (measurable_snd.comp
      (OriginConfiguration.measurable_advance_controls
        P intensity threshold hthreshold)).comp measurable_fst
  have hcount := measurable_originCoinPairSecondCount
    P intensity threshold hthreshold basePending
  have horigin : Measurable (fun z : GhostCoinInput n =>
      z.1.origin) :=
    measurable_originConfiguration_origin.comp measurable_fst
  have hindex := measurable_originCoinPairIndex
    P intensity threshold hthreshold basePending
  exact measurable_originAppend_joint.comp
    ((hcomponent.prodMk (hlabel.prodMk hcount)).prodMk
      (horigin.prodMk hindex))

set_option maxHeartbeats 1000000 in
theorem OriginConfiguration.advance_origin_eq_coinPairTotal
    {n : Nat} (z : GhostCoinInput n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (tape : Nat → LatticePoint n) :
    (z.1.advance P intensity threshold basePending z.2.1 z.2.2
      tape).origin =
      originCoinPairOriginTotal P intensity threshold
        basePending z := by
  let deleted := z.1.state.removeComponent P
  let preRounds := z.1.level + ttcPseudocode.firstLoopExit deleted intensity threshold
  let pending := pendingAfter z.2.1 preRounds deleted.nextLabel basePending
  let activeCoins := originalSurvivorCoinRestriction z.2.1 preRounds
    deleted.nextLabel basePending z.2.2
  let first := ttcPseudocode.firstLoopResult deleted intensity threshold
    (sourceOldCoins z.1.origin z.1.source.coins z.1.level)
  let activeRounds := originCoinPairSplitExit P intensity threshold
    basePending z
  let second := thinningResultSplitFinite first pending threshold
    (shiftCoins (ttcPseudocode.firstLoopExit deleted intensity threshold)
      (sourceOldCoins z.1.origin z.1.source.coins z.1.level))
    activeCoins
  change originAppend z.1.origin z.1.source.processed
      deleted.nextLabel second.2
        (fun i => twoStageSurvivorLabel z.2.1 preRounds
          deleted.nextLabel basePending activeCoins activeRounds i) =
    originAppend z.1.origin z.1.source.processed
      deleted.nextLabel second.2
        (fun i => originCoinPairIndex P intensity threshold
          basePending z i.val)
  congr 1
  funext i
  exact (twoStageSurvivorLabelOrZero_eq z.2.1 preRounds
    deleted.nextLabel basePending activeRounds activeCoins i).symm

set_option maxHeartbeats 1000000 in
theorem OriginConfiguration.measurable_advance_origin_coinPair
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (fun z : GhostCoinInput n ×
        (Nat → LatticePoint n) =>
      (z.1.1.advance P intensity threshold basePending z.1.2.1
        z.1.2.2 z.2).origin) := by
  have heq : (fun z : GhostCoinInput n ×
      (Nat → LatticePoint n) =>
      (z.1.1.advance P intensity threshold basePending z.1.2.1
        z.1.2.2 z.2).origin) =
      (fun z => originCoinPairOriginTotal P intensity threshold
        basePending z.1) := by
    funext z
    exact OriginConfiguration.advance_origin_eq_coinPairTotal
      z.1 P intensity threshold basePending z.2
  rw [heq]
  exact (measurable_originCoinPairOriginTotal P intensity
    threshold hthreshold basePending).comp measurable_fst

end Kr25Ssmxt
