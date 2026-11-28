import ttc.Analysis.SampleAppendTape
import ttc.Analysis.AbsoluteSplitSource

/-! A full concrete component kernel with absolute Poisson pre-draw, separate
old/new active coins, and an IID point tape for its sampling call. -/

namespace ttc

open MeasureTheory ProbabilityTheory

set_option maxHeartbeats 800000 in

theorem communityComponentGivenVolume_absolute_split_tape
    {n k : Nat} (hn : 3 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (outcome : VolumeOutcome) (state : TTCState n)
    (level : Nat) (hrate : state.p = 1 / (2 : NNReal) ^ level)
    (hfresh : state.LabelsFresh) :
    let intensity := ttcReference.t b n threshold outcome.2
    let deleted := state.removeComponent P
    let pointLaw := normalizedHitAndRunPointLaw hn P b eta hroute.1
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
    communityComponentGivenVolume hn prep P b eta delta threshold
      outcome state =
    ((poissonMeasure intensity).bind fun basePending =>
      fairCoinStreamLaw.bind fun preCoins =>
        (fairCoinStreamLaw.prod fairCoinStreamLaw).map fun pair =>
          thinningResultSplit
            (ttcReference.firstLoopResult deleted intensity threshold pair.1)
            (pendingAfter preCoins
              (level + ttcReference.firstLoopExit deleted intensity threshold)
              deleted.nextLabel basePending)
            threshold
            (shiftCoins (ttcReference.firstLoopExit deleted intensity threshold) pair.1)
            (shiftCoins (ttcReference.firstLoopExit deleted intensity threshold) pair.2)).bind
      fun second =>
        (Measure.infinitePi (fun _ : Nat => pointLaw)).map fun tape =>
          second.1.addBatch
            (fun i : Fin second.2 => tape (second.1.nextLabel + i.val)) := by
  let pointLaw := normalizedHitAndRunPointLaw hn P b eta hroute.1
    hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
  let K : TTCState n × Nat → Measure (TTCState n) := fun second =>
    (Measure.infinitePi (fun _ : Nat => pointLaw)).map fun tape =>
      second.1.addBatch
        (fun i : Fin second.2 => tape (second.1.nextLabel + i.val))
  let deleted := state.removeComponent P
  let intensity := ttcReference.t b n threshold outcome.2
  let source : Measure (TTCState n × Nat) :=
    (poissonMeasure intensity).bind fun basePending =>
      fairCoinStreamLaw.bind fun preCoins =>
        fairCoinStreamLaw.map fun activeCoins =>
          ttcPseudocode.secondLoopResult
            (ttcReference.firstLoopResult deleted intensity threshold activeCoins)
            (pendingAfter preCoins
              (level + ttcReference.firstLoopExit deleted intensity threshold)
              deleted.nextLabel basePending)
            threshold
            (shiftCoins (ttcReference.firstLoopExit deleted intensity threshold)
              activeCoins)
  let splitSource : Measure (TTCState n × Nat) :=
    (poissonMeasure intensity).bind fun basePending =>
      fairCoinStreamLaw.bind fun preCoins =>
        (fairCoinStreamLaw.prod fairCoinStreamLaw).map fun pair =>
          thinningResultSplit
            (ttcReference.firstLoopResult deleted intensity threshold pair.1)
            (pendingAfter preCoins
              (level + ttcReference.firstLoopExit deleted intensity threshold)
              deleted.nextLabel basePending)
            threshold
            (shiftCoins (ttcReference.firstLoopExit deleted intensity threshold) pair.1)
            (shiftCoins (ttcReference.firstLoopExit deleted intensity threshold) pair.2)
  have hsource : source = splitSource :=
    poisson_twoLoops_absolute_split deleted intensity threshold
      level (state.labelsFresh_removeComponent P hfresh)
  have hbase : communityComponentGivenVolume hn prep P b eta delta
      threshold outcome state = source.bind K := by
    exact communityComponentGivenVolume_absolute_tape
      hn prep P b eta delta threshold hroute outcome state level hrate
  have hfinal := hbase.trans (congrArg (fun μ : Measure (TTCState n × Nat) =>
    μ.bind K) hsource)
  exact hfinal

end ttc
