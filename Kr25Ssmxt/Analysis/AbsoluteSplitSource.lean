import Kr25Ssmxt.Analysis.CoinLabelMergeLaw
import Kr25Ssmxt.Analysis.AbsoluteComponentSource

/-! The absolute-level Poisson pre-draw can use independent fair arrays for
stored copies and the component's newly drawn copies. -/

namespace Kr25Ssmxt

open MeasureTheory ProbabilityTheory

theorem poisson_twoLoops_absolute_split
    {n : Nat} (s : TTCState n) (intensity : NNReal)
    (threshold : Real) (level : Nat) (hfresh : s.LabelsFresh) :
    ((poissonMeasure intensity).bind fun basePending =>
      fairCoinStreamLaw.bind fun preCoins =>
        fairCoinStreamLaw.map fun activeCoins =>
          ttcPseudocode.secondLoopResult
            (ttcReference.firstLoopResult s intensity threshold activeCoins)
            (pendingAfter preCoins
              (level + ttcReference.firstLoopExit s intensity threshold)
              s.nextLabel basePending)
            threshold
            (shiftCoins (ttcReference.firstLoopExit s intensity threshold)
              activeCoins)) =
    ((poissonMeasure intensity).bind fun basePending =>
      fairCoinStreamLaw.bind fun preCoins =>
        (fairCoinStreamLaw.prod fairCoinStreamLaw).map fun pair =>
          thinningResultSplit
            (ttcReference.firstLoopResult s intensity threshold pair.1)
            (pendingAfter preCoins
              (level + ttcReference.firstLoopExit s intensity threshold)
              s.nextLabel basePending)
            threshold
            (shiftCoins (ttcReference.firstLoopExit s intensity threshold) pair.1)
            (shiftCoins (ttcReference.firstLoopExit s intensity threshold) pair.2)) := by
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro basePending
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro preCoins
  exact absolute_active_split_law s intensity threshold
    (pendingAfter preCoins
      (level + ttcReference.firstLoopExit s intensity threshold)
      s.nextLabel basePending) hfresh

end Kr25Ssmxt
