import Kr25Ssmxt.Analysis.OriginOrderedMarginal

/-! First joint measurability steps for a CV18 outcome whose intensity varies
with the incoming ghost configuration. -/

namespace Kr25Ssmxt

open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem OriginConfiguration.measurable_advance_controls_intensity
    {n : Nat} (P : PolytopeData n)
    (threshold : Real) (hthreshold : 0 < threshold) :
    Measurable (fun z : OriginConfiguration n × NNReal =>
      (z.1.level + ttcPseudocode.firstLoopExit (z.1.state.removeComponent P)
        z.2 threshold, (z.1.state.removeComponent P).nextLabel)) := by
  have hdeleted : Measurable (fun z : OriginConfiguration n ×
      NNReal => z.1.state.removeComponent P) :=
    (measurable_removeComponent P).comp
      (measurable_originConfiguration_state.comp measurable_fst)
  have hround : Measurable (fun z : OriginConfiguration n ×
      NNReal => ttcPseudocode.firstLoopExit (z.1.state.removeComponent P)
        z.2 threshold) :=
    (measurable_rateExit_joint threshold hthreshold).comp
      (hdeleted.prodMk measurable_snd)
  have hlabel : Measurable (fun z : OriginConfiguration n ×
      NNReal => (z.1.state.removeComponent P).nextLabel) :=
    (show Measurable (fun s : TTCState n => s.nextLabel) from
      (measurable_snd.comp measurable_snd).comp
        (comap_measurable (fun s : TTCState n =>
          (s.p, s.X, s.nextLabel)))).comp hdeleted
  exact ((measurable_originConfiguration_level.comp
    measurable_fst).add hround).prodMk hlabel

set_option maxHeartbeats 1000000 in
theorem OriginConfiguration.measurable_advance_firstState_intensity
    {n : Nat} (P : PolytopeData n)
    (threshold : Real) (hthreshold : 0 < threshold) :
    Measurable (fun z : OriginConfiguration n × NNReal =>
      ttcPseudocode.firstLoopResult (z.1.state.removeComponent P)
        z.2 threshold
        (sourceOldCoins z.1.origin z.1.source.coins
          z.1.level)) := by
  have hdeleted : Measurable (fun z : OriginConfiguration n ×
      NNReal => z.1.state.removeComponent P) :=
    (measurable_removeComponent P).comp
      (measurable_originConfiguration_state.comp measurable_fst)
  have hold : Measurable (fun z : OriginConfiguration n ×
      NNReal => sourceOldCoins z.1.origin z.1.source.coins
        z.1.level) :=
    measurable_sourceOldCoins_joint.comp measurable_fst
  exact (measurable_rateThinningResult_joint threshold
    hthreshold).comp ((hdeleted.prodMk measurable_snd).prodMk hold)

set_option maxHeartbeats 1000000 in
theorem OriginConfiguration.measurable_advance_shiftedOldCoins_intensity
    {n : Nat} (P : PolytopeData n)
    (threshold : Real) (hthreshold : 0 < threshold) :
    Measurable (fun z : OriginConfiguration n × NNReal =>
      shiftCoins
        (ttcPseudocode.firstLoopExit (z.1.state.removeComponent P) z.2 threshold)
        (sourceOldCoins z.1.origin z.1.source.coins z.1.level)) := by
  have hdeleted : Measurable (fun z : OriginConfiguration n ×
      NNReal => z.1.state.removeComponent P) :=
    (measurable_removeComponent P).comp
      (measurable_originConfiguration_state.comp measurable_fst)
  have hround : Measurable (fun z : OriginConfiguration n ×
      NNReal => ttcPseudocode.firstLoopExit (z.1.state.removeComponent P)
        z.2 threshold) :=
    (measurable_rateExit_joint threshold hthreshold).comp
      (hdeleted.prodMk measurable_snd)
  exact measurable_shiftCoins_joint.comp
    (hround.prodMk
      (measurable_sourceOldCoins_joint.comp measurable_fst))

set_option maxHeartbeats 1000000 in
theorem OriginConfiguration.measurable_pending_coinPair_intensity
    {n : Nat} (P : PolytopeData n)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (fun z : (OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      pendingAfter z.2.1
        (z.1.1.level + ttcPseudocode.firstLoopExit
          (z.1.1.state.removeComponent P) z.1.2 threshold)
        (z.1.1.state.removeComponent P).nextLabel basePending) := by
  have hcontrols : Measurable (fun z :
      (OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      (z.1.1.level + ttcPseudocode.firstLoopExit
        (z.1.1.state.removeComponent P) z.1.2 threshold,
        (z.1.1.state.removeComponent P).nextLabel)) :=
    (OriginConfiguration.measurable_advance_controls_intensity
      P threshold hthreshold).comp measurable_fst
  exact measurable_pendingAfter_joint.comp
    (((measurable_fst.comp hcontrols).prodMk
      ((measurable_snd.comp hcontrols).prodMk measurable_const)).prodMk
      (measurable_fst.comp measurable_snd))

set_option maxHeartbeats 1000000 in
theorem OriginConfiguration.measurable_activeFullCoins_coinPair_intensity
    {n : Nat} (P : PolytopeData n)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (fun z : (OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      let deleted := z.1.1.state.removeComponent P
      let preRounds := z.1.1.level + ttcPseudocode.firstLoopExit deleted z.1.2
        threshold
      pendingCoinExtension deleted.nextLabel
        (pendingAfter z.2.1 preRounds deleted.nextLabel basePending)
        (originalSurvivorCoinRestriction z.2.1 preRounds
          deleted.nextLabel basePending z.2.2)) := by
  exact (measurable_originalSurvivorCoinExtension_joint basePending).comp
    (((OriginConfiguration.measurable_advance_controls_intensity
      P threshold hthreshold).comp measurable_fst).prodMk measurable_snd)

set_option maxHeartbeats 1000000 in
theorem OriginConfiguration.measurable_mergedCoins_coinPair_intensity
    {n : Nat} (P : PolytopeData n)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (fun z : (OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      let deleted := z.1.1.state.removeComponent P
      let rounds := ttcPseudocode.firstLoopExit deleted z.1.2 threshold
      let preRounds := z.1.1.level + rounds
      mergeCoinsAtLabel deleted.nextLabel
        (shiftCoins rounds
          (sourceOldCoins z.1.1.origin z.1.1.source.coins
            z.1.1.level))
        (pendingCoinExtension deleted.nextLabel
          (pendingAfter z.2.1 preRounds deleted.nextLabel basePending)
          (originalSurvivorCoinRestriction z.2.1 preRounds
            deleted.nextLabel basePending z.2.2))) := by
  have hlabel : Measurable (fun z :
      (OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      (z.1.1.state.removeComponent P).nextLabel) :=
    (measurable_snd.comp
      (OriginConfiguration.measurable_advance_controls_intensity
        P threshold hthreshold)).comp measurable_fst
  have hshift : Measurable (fun z :
      (OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      shiftCoins
        (ttcPseudocode.firstLoopExit (z.1.1.state.removeComponent P)
          z.1.2 threshold)
        (sourceOldCoins z.1.1.origin z.1.1.source.coins
          z.1.1.level)) :=
    (OriginConfiguration.measurable_advance_shiftedOldCoins_intensity
      P threshold hthreshold).comp measurable_fst
  exact measurable_mergeCoinsAtLabel_joint.comp
    (hlabel.prodMk
      (hshift.prodMk
        (OriginConfiguration.measurable_activeFullCoins_coinPair_intensity
          P threshold hthreshold basePending)))

set_option maxHeartbeats 1000000 in
theorem OriginConfiguration.measurable_secondExit_coinPair_intensity
    {n : Nat} (P : PolytopeData n)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (fun z : (OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      originCoinPairSplitExit P z.1.2 threshold basePending
        (z.1.1, z.2)) := by
  have hfirst : Measurable (fun z :
      (OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      ttcPseudocode.firstLoopResult (z.1.1.state.removeComponent P)
        z.1.2 threshold
        (sourceOldCoins z.1.1.origin z.1.1.source.coins
          z.1.1.level)) :=
    (OriginConfiguration.measurable_advance_firstState_intensity
      P threshold hthreshold).comp measurable_fst
  have hpending :=
    OriginConfiguration.measurable_pending_coinPair_intensity
      P threshold hthreshold basePending
  have hcoins :=
    OriginConfiguration.measurable_mergedCoins_coinPair_intensity
      P threshold hthreshold basePending
  have hmerged : Measurable (fun z :
      (OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      originCoinPairMergedExit P z.1.2 threshold basePending
        (z.1.1, z.2)) := by
    exact (measurable_firstExitRound_joint threshold).comp
      ((hfirst.prodMk hpending).prodMk hcoins)
  have heq : (fun z : (OriginConfiguration n × NNReal) ×
      ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      originCoinPairSplitExit P z.1.2 threshold basePending
        (z.1.1, z.2)) =
      (fun z => originCoinPairMergedExit P z.1.2 threshold
        basePending (z.1.1, z.2)) := by
    funext z
    exact originCoinPairSplitExit_eq_mergedExit
      (z.1.1, z.2) P z.1.2 threshold basePending
  rw [heq]
  exact hmerged

set_option maxHeartbeats 1000000 in
theorem OriginConfiguration.measurable_advance_level_coinPair_intensity
    {n : Nat} (P : PolytopeData n)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (fun z :
        ((OriginConfiguration n × NNReal) ×
          ((Nat × Nat → Bool) × (Nat × Nat → Bool))) ×
          (Nat → LatticePoint n) =>
      (z.1.1.1.advance P z.1.1.2 threshold basePending
        z.1.2.1 z.1.2.2 z.2).level) := by
  have hpre : Measurable (fun z :
      ((OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool))) ×
        (Nat → LatticePoint n) =>
      z.1.1.1.level + ttcPseudocode.firstLoopExit
        (z.1.1.1.state.removeComponent P) z.1.1.2 threshold) :=
    (measurable_fst.comp
      (OriginConfiguration.measurable_advance_controls_intensity
        P threshold hthreshold)).comp
      (measurable_fst.comp measurable_fst)
  have hactive : Measurable (fun z :
      ((OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool))) ×
        (Nat → LatticePoint n) =>
      originCoinPairSplitExit P z.1.1.2 threshold
        basePending (z.1.1.1, z.1.2)) :=
    (OriginConfiguration.measurable_secondExit_coinPair_intensity
      P threshold hthreshold basePending).comp measurable_fst
  have heq : (fun z :
      ((OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool))) ×
        (Nat → LatticePoint n) =>
      (z.1.1.1.advance P z.1.1.2 threshold basePending
        z.1.2.1 z.1.2.2 z.2).level) =
      (fun z => z.1.1.1.level + ttcPseudocode.firstLoopExit
        (z.1.1.1.state.removeComponent P) z.1.1.2 threshold +
        originCoinPairSplitExit P z.1.1.2 threshold
          basePending (z.1.1.1, z.1.2)) := by
    funext z
    exact z.1.1.1.advance_level P z.1.1.2 threshold basePending
      z.1.2.1 z.1.2.2 z.2
  rw [heq]
  exact hpre.add hactive

set_option maxHeartbeats 1000000 in
theorem OriginConfiguration.measurable_advance_source_coinPair_intensity
    {n : Nat} (P : PolytopeData n)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (fun z :
        ((OriginConfiguration n × NNReal) ×
          ((Nat × Nat → Bool) × (Nat × Nat → Bool))) ×
          (Nat → LatticePoint n) =>
      (z.1.1.1.advance P z.1.1.2 threshold basePending
        z.1.2.1 z.1.2.2 z.2).source) := by
  have hconfig : Measurable (fun z :
      ((OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool))) ×
        (Nat → LatticePoint n) => z.1.1.1) :=
    measurable_fst.comp (measurable_fst.comp measurable_fst)
  have hcontrols : Measurable (fun z :
      ((OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool))) ×
        (Nat → LatticePoint n) =>
      (z.1.1.1.level + ttcPseudocode.firstLoopExit
        (z.1.1.1.state.removeComponent P) z.1.1.2 threshold,
        (z.1.1.1.state.removeComponent P).nextLabel)) :=
    (OriginConfiguration.measurable_advance_controls_intensity
      P threshold hthreshold).comp
      (measurable_fst.comp measurable_fst)
  have hparams : Measurable (fun z :
      ((OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool))) ×
        (Nat → LatticePoint n) =>
      ((z.1.1.1.state.removeComponent P).nextLabel,
        z.1.1.1.level + ttcPseudocode.firstLoopExit
          (z.1.1.1.state.removeComponent P) z.1.1.2 threshold)) :=
    (measurable_snd.comp hcontrols).prodMk
      (measurable_fst.comp hcontrols)
  have hsourceTape : Measurable (fun z :
      ((OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool))) ×
        (Nat → LatticePoint n) => (z.1.1.1.source, z.2)) :=
    (measurable_originConfiguration_source.comp hconfig).prodMk
      measurable_snd
  have hinput :=
    (measurable_originSourceStepCoinPair P basePending).comp
      (hparams.prodMk
        (hsourceTape.prodMk (measurable_snd.comp measurable_fst)))
  have heq : (fun z :
      ((OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool))) ×
        (Nat → LatticePoint n) =>
      (z.1.1.1.advance P z.1.1.2 threshold basePending
        z.1.2.1 z.1.2.2 z.2).source) =
      (fun z => originSourceStepCoinPair P basePending
        (((z.1.1.1.state.removeComponent P).nextLabel,
            z.1.1.1.level + ttcPseudocode.firstLoopExit
              (z.1.1.1.state.removeComponent P) z.1.1.2 threshold),
          ((z.1.1.1.source, z.2), z.1.2))) := by
    funext z
    exact z.1.1.1.advance_source P z.1.1.2 threshold basePending
      z.1.2.1 z.1.2.2 z.2
  rw [heq]
  exact hinput

set_option maxHeartbeats 1000000 in
theorem measurable_originCoinPairSecondCountFormula_intensity
    {n : Nat} (P : PolytopeData n)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (fun z : (OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      pendingAfter
        (originCoinPairActiveFull P z.1.2 threshold basePending
          (z.1.1, z.2))
        (originCoinPairSplitExit P z.1.2 threshold basePending
          (z.1.1, z.2))
        (z.1.1.state.removeComponent P).nextLabel
        (pendingAfter z.2.1
          (z.1.1.level + ttcPseudocode.firstLoopExit
            (z.1.1.state.removeComponent P) z.1.2 threshold)
          (z.1.1.state.removeComponent P).nextLabel basePending)) := by
  have hcontrols : Measurable (fun z :
      (OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      (z.1.1.level + ttcPseudocode.firstLoopExit
        (z.1.1.state.removeComponent P) z.1.2 threshold,
        (z.1.1.state.removeComponent P).nextLabel)) :=
    (OriginConfiguration.measurable_advance_controls_intensity
      P threshold hthreshold).comp measurable_fst
  have hlabel : Measurable (fun z :
      (OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      (z.1.1.state.removeComponent P).nextLabel) :=
    measurable_snd.comp hcontrols
  have hpending :=
    OriginConfiguration.measurable_pending_coinPair_intensity
      P threshold hthreshold basePending
  have hrounds :=
    OriginConfiguration.measurable_secondExit_coinPair_intensity
      P threshold hthreshold basePending
  have hactive :=
    OriginConfiguration.measurable_activeFullCoins_coinPair_intensity
      P threshold hthreshold basePending
  exact measurable_pendingAfter_joint.comp
    ((hrounds.prodMk (hlabel.prodMk hpending)).prodMk hactive)

set_option maxHeartbeats 1000000 in
theorem measurable_originCoinPairSecondCount_intensity
    {n : Nat} (P : PolytopeData n)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (fun z : (OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      originCoinPairSecondCount P z.1.2 threshold basePending
        (z.1.1, z.2)) := by
  have heq : (fun z : (OriginConfiguration n × NNReal) ×
      ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      originCoinPairSecondCount P z.1.2 threshold basePending
        (z.1.1, z.2)) =
      (fun z => pendingAfter
        (originCoinPairActiveFull P z.1.2 threshold basePending
          (z.1.1, z.2))
        (originCoinPairSplitExit P z.1.2 threshold basePending
          (z.1.1, z.2))
        (z.1.1.state.removeComponent P).nextLabel
        (pendingAfter z.2.1
          (z.1.1.level + ttcPseudocode.firstLoopExit
            (z.1.1.state.removeComponent P) z.1.2 threshold)
          (z.1.1.state.removeComponent P).nextLabel basePending)) := by
    funext z
    rfl
  rw [heq]
  exact measurable_originCoinPairSecondCountFormula_intensity
    P threshold hthreshold basePending

set_option maxHeartbeats 1000000 in
theorem measurable_originCoinPairIndex_intensity
    {n : Nat} (P : PolytopeData n)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (fun z : (OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      originCoinPairIndex P z.1.2 threshold basePending
        (z.1.1, z.2)) := by
  have hcontrols : Measurable (fun z :
      (OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      (z.1.1.level + ttcPseudocode.firstLoopExit
        (z.1.1.state.removeComponent P) z.1.2 threshold,
        (z.1.1.state.removeComponent P).nextLabel)) :=
    (OriginConfiguration.measurable_advance_controls_intensity
      P threshold hthreshold).comp measurable_fst
  have hpre : Measurable (fun z :
      (OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      z.1.1.level + ttcPseudocode.firstLoopExit
        (z.1.1.state.removeComponent P) z.1.2 threshold) :=
    measurable_fst.comp hcontrols
  have hlabel : Measurable (fun z :
      (OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      (z.1.1.state.removeComponent P).nextLabel) :=
    measurable_snd.comp hcontrols
  have hrounds :=
    OriginConfiguration.measurable_secondExit_coinPair_intensity
      P threshold hthreshold basePending
  have hactive :=
    OriginConfiguration.measurable_activeFullCoins_coinPair_intensity
      P threshold hthreshold basePending
  have hformula : Measurable (fun z :
      (OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      fun i : Nat => twoStageSurvivorLabelOrZero z.2.1
        (originCoinPairActiveFull P z.1.2 threshold
          basePending (z.1.1, z.2))
        (z.1.1.level + ttcPseudocode.firstLoopExit
          (z.1.1.state.removeComponent P) z.1.2 threshold)
        (z.1.1.state.removeComponent P).nextLabel basePending
        (originCoinPairSplitExit P z.1.2 threshold
          basePending (z.1.1, z.2)) i) := by
    apply Measurable.of_eval
    intro i
    exact measurable_twoStageSurvivorLabelOrZero_joint.comp
      ((hpre.prodMk
        (hlabel.prodMk
          (measurable_const.prodMk
            (hrounds.prodMk measurable_const)))).prodMk
        ((measurable_fst.comp measurable_snd).prodMk hactive))
  have heq : (fun z : (OriginConfiguration n × NNReal) ×
      ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      originCoinPairIndex P z.1.2 threshold basePending
        (z.1.1, z.2)) =
      (fun z => fun i : Nat => twoStageSurvivorLabelOrZero z.2.1
        (originCoinPairActiveFull P z.1.2 threshold
          basePending (z.1.1, z.2))
        (z.1.1.level + ttcPseudocode.firstLoopExit
          (z.1.1.state.removeComponent P) z.1.2 threshold)
        (z.1.1.state.removeComponent P).nextLabel basePending
        (originCoinPairSplitExit P z.1.2 threshold
          basePending (z.1.1, z.2)) i) := by
    funext z
    rfl
  rw [heq]
  exact hformula

set_option maxHeartbeats 1000000 in
theorem measurable_originCoinPairOriginTotal_intensity
    {n : Nat} (P : PolytopeData n)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (fun z : (OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      originCoinPairOriginTotal P z.1.2 threshold basePending
        (z.1.1, z.2)) := by
  have hcomponent : Measurable (fun z :
      (OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      z.1.1.source.processed) :=
    (measurable_originSourceState_processed.comp
      measurable_originConfiguration_source).comp
        (measurable_fst.comp measurable_fst)
  have hlabel : Measurable (fun z :
      (OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      (z.1.1.state.removeComponent P).nextLabel) :=
    (measurable_snd.comp
      (OriginConfiguration.measurable_advance_controls_intensity
        P threshold hthreshold)).comp measurable_fst
  have hcount := measurable_originCoinPairSecondCount_intensity
    P threshold hthreshold basePending
  have horigin : Measurable (fun z :
      (OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      z.1.1.origin) :=
    measurable_originConfiguration_origin.comp
      (measurable_fst.comp measurable_fst)
  have hindex := measurable_originCoinPairIndex_intensity
    P threshold hthreshold basePending
  have hformula : Measurable (fun z :
      (OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      originAppend z.1.1.origin z.1.1.source.processed
        (z.1.1.state.removeComponent P).nextLabel
        (originCoinPairSecondCount P z.1.2 threshold
          basePending (z.1.1, z.2))
        (fun i => originCoinPairIndex P z.1.2 threshold
          basePending (z.1.1, z.2) i.val)) :=
    measurable_originAppend_joint.comp
      ((hcomponent.prodMk (hlabel.prodMk hcount)).prodMk
        (horigin.prodMk hindex))
  have heq : (fun z : (OriginConfiguration n × NNReal) ×
      ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      originCoinPairOriginTotal P z.1.2 threshold basePending
        (z.1.1, z.2)) =
      (fun z => originAppend z.1.1.origin z.1.1.source.processed
        (z.1.1.state.removeComponent P).nextLabel
        (originCoinPairSecondCount P z.1.2 threshold
          basePending (z.1.1, z.2))
        (fun i => originCoinPairIndex P z.1.2 threshold
          basePending (z.1.1, z.2) i.val)) := by
    funext z
    rfl
  rw [heq]
  exact hformula

set_option maxHeartbeats 1000000 in
theorem OriginConfiguration.measurable_advance_origin_coinPair_intensity
    {n : Nat} (P : PolytopeData n)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (fun z :
        ((OriginConfiguration n × NNReal) ×
          ((Nat × Nat → Bool) × (Nat × Nat → Bool))) ×
          (Nat → LatticePoint n) =>
      (z.1.1.1.advance P z.1.1.2 threshold basePending
        z.1.2.1 z.1.2.2 z.2).origin) := by
  have heq : (fun z :
      ((OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool))) ×
        (Nat → LatticePoint n) =>
      (z.1.1.1.advance P z.1.1.2 threshold basePending
        z.1.2.1 z.1.2.2 z.2).origin) =
      (fun z => originCoinPairOriginTotal P z.1.1.2 threshold
        basePending (z.1.1.1, z.1.2)) := by
    funext z
    exact OriginConfiguration.advance_origin_eq_coinPairTotal
      (z.1.1.1, z.1.2) P z.1.1.2 threshold basePending z.2
  rw [heq]
  exact (measurable_originCoinPairOriginTotal_intensity P
    threshold hthreshold basePending).comp measurable_fst

set_option maxHeartbeats 1000000 in
theorem measurable_originCoinPairMergedSecondResult_intensity
    {n : Nat} (P : PolytopeData n)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (fun z : (OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      originCoinPairMergedSecondResult P z.1.2 threshold
        basePending (z.1.1, z.2)) := by
  have hfirst : Measurable (fun z :
      (OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      ttcPseudocode.firstLoopResult (z.1.1.state.removeComponent P)
        z.1.2 threshold
        (sourceOldCoins z.1.1.origin z.1.1.source.coins
          z.1.1.level)) :=
    (OriginConfiguration.measurable_advance_firstState_intensity
      P threshold hthreshold).comp measurable_fst
  have hpending :=
    OriginConfiguration.measurable_pending_coinPair_intensity
      P threshold hthreshold basePending
  have hmerged :=
    OriginConfiguration.measurable_mergedCoins_coinPair_intensity
      P threshold hthreshold basePending
  have hformula : Measurable (fun z :
      (OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      ttcPseudocode.secondLoopResult
        (ttcPseudocode.firstLoopResult (z.1.1.state.removeComponent P)
          z.1.2 threshold
          (sourceOldCoins z.1.1.origin z.1.1.source.coins
            z.1.1.level))
        (pendingAfter z.2.1
          (z.1.1.level + ttcPseudocode.firstLoopExit
            (z.1.1.state.removeComponent P) z.1.2 threshold)
          (z.1.1.state.removeComponent P).nextLabel basePending)
        threshold
        (mergeCoinsAtLabel (z.1.1.state.removeComponent P).nextLabel
          (shiftCoins
            (ttcPseudocode.firstLoopExit (z.1.1.state.removeComponent P)
              z.1.2 threshold)
            (sourceOldCoins z.1.1.origin z.1.1.source.coins
              z.1.1.level))
          (originCoinPairActiveFull P z.1.2 threshold
            basePending (z.1.1, z.2)))) :=
    (measurable_thinningResult_joint threshold).comp
      ((hfirst.prodMk hpending).prodMk hmerged)
  have heq : (fun z : (OriginConfiguration n × NNReal) ×
      ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      originCoinPairMergedSecondResult P z.1.2 threshold
        basePending (z.1.1, z.2)) =
      (fun z => ttcPseudocode.secondLoopResult
        (ttcPseudocode.firstLoopResult (z.1.1.state.removeComponent P)
          z.1.2 threshold
          (sourceOldCoins z.1.1.origin z.1.1.source.coins
            z.1.1.level))
        (pendingAfter z.2.1
          (z.1.1.level + ttcPseudocode.firstLoopExit
            (z.1.1.state.removeComponent P) z.1.2 threshold)
          (z.1.1.state.removeComponent P).nextLabel basePending)
        threshold
        (mergeCoinsAtLabel (z.1.1.state.removeComponent P).nextLabel
          (shiftCoins
            (ttcPseudocode.firstLoopExit (z.1.1.state.removeComponent P)
              z.1.2 threshold)
            (sourceOldCoins z.1.1.origin z.1.1.source.coins
              z.1.1.level))
          (originCoinPairActiveFull P z.1.2 threshold
            basePending (z.1.1, z.2)))) := by
    funext z
    rfl
  rw [heq]
  exact hformula

set_option maxHeartbeats 1000000 in
theorem measurable_originCoinPairStateTotal_intensity
    {n : Nat} (P : PolytopeData n)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (fun z :
        ((OriginConfiguration n × NNReal) ×
          ((Nat × Nat → Bool) × (Nat × Nat → Bool))) ×
          (Nat → LatticePoint n) =>
      originCoinPairStateTotal P z.1.1.2 threshold
        basePending (z.1.1.1, z.1.2) z.2) := by
  have hcount := measurable_originCoinPairSecondCount_intensity
    P threshold hthreshold basePending
  have hstate : Measurable (fun z :
      (OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      (originCoinPairMergedSecondResult P z.1.2 threshold
        basePending (z.1.1, z.2)).1) :=
    measurable_fst.comp
      (measurable_originCoinPairMergedSecondResult_intensity
        P threshold hthreshold basePending)
  have hindex := measurable_originCoinPairIndex_intensity
    P threshold hthreshold basePending
  exact measurable_addBatch_indexed_tape_joint.comp
    ((hcount.comp measurable_fst).prodMk
      (((hstate.comp measurable_fst).prodMk
        (hindex.comp measurable_fst)).prodMk measurable_snd))

set_option maxHeartbeats 1000000 in
theorem OriginConfiguration.measurable_advance_state_coinPair_intensity
    {n : Nat} (P : PolytopeData n)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (fun z :
        ((OriginConfiguration n × NNReal) ×
          ((Nat × Nat → Bool) × (Nat × Nat → Bool))) ×
          (Nat → LatticePoint n) =>
      (z.1.1.1.advance P z.1.1.2 threshold basePending
        z.1.2.1 z.1.2.2 z.2).state) := by
  have heq : (fun z :
      ((OriginConfiguration n × NNReal) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool))) ×
        (Nat → LatticePoint n) =>
      (z.1.1.1.advance P z.1.1.2 threshold basePending
        z.1.2.1 z.1.2.2 z.2).state) =
      (fun z => originCoinPairStateTotal P z.1.1.2 threshold
        basePending (z.1.1.1, z.1.2) z.2) := by
    funext z
    exact OriginConfiguration.advance_state_eq_coinPairTotal
      (z.1.1.1, z.1.2) P z.1.1.2 threshold basePending z.2
  rw [heq]
  exact measurable_originCoinPairStateTotal_intensity
    P threshold hthreshold basePending

set_option maxHeartbeats 1000000 in
theorem OriginConfiguration.measurable_advance_coinPair_intensity
    {n : Nat} (P : PolytopeData n)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (fun z :
        ((OriginConfiguration n × NNReal) ×
          ((Nat × Nat → Bool) × (Nat × Nat → Bool))) ×
          (Nat → LatticePoint n) =>
      z.1.1.1.advance P z.1.1.2 threshold basePending
        z.1.2.1 z.1.2.2 z.2) := by
  rw [measurable_comap_iff]
  exact (OriginConfiguration.measurable_advance_state_coinPair_intensity
      P threshold hthreshold basePending).prodMk
    ((OriginConfiguration.measurable_advance_source_coinPair_intensity
      P threshold hthreshold basePending).prodMk
      ((OriginConfiguration.measurable_advance_origin_coinPair_intensity
        P threshold hthreshold basePending).prodMk
        (OriginConfiguration.measurable_advance_level_coinPair_intensity
          P threshold hthreshold basePending)))

end Kr25Ssmxt
