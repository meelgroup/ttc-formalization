import Kr25Ssmxt.Analysis.PoissonTwoLoopLaw
import Kr25Ssmxt.Analysis.PoissonPreDraw

/-! At an incoming dyadic rate, a component's actual pending Poisson count
can be obtained from a level-zero Poisson draw and independent absolute-level
thinning before the two executable loops. -/

namespace Kr25Ssmxt

open MeasureTheory ProbabilityTheory

theorem poisson_twoLoops_absolute_predraw
    {n : Nat} (s : TTCState n) (intensity : NNReal)
    (threshold : Real) (level : Nat)
    (hrate : s.p = 1 / (2 : NNReal) ^ level) :
    (ttcPseudocode.firstLoop s intensity threshold).bind (fun first =>
      (poissonMeasure (intensity * first.p)).bind fun pending =>
        ttcPseudocode.secondLoop first pending threshold) =
    (poissonMeasure intensity).bind fun basePending =>
      fairCoinStreamLaw.bind fun preCoins =>
        fairCoinStreamLaw.map fun activeCoins =>
          ttcPseudocode.secondLoopResult
            (ttcPseudocode.firstLoopResult s intensity threshold activeCoins)
            (pendingAfter preCoins
              (level + ttcPseudocode.firstLoopExit s intensity threshold)
              s.nextLabel basePending)
            threshold
            (shiftCoins (ttcPseudocode.firstLoopExit s intensity threshold)
              activeCoins) := by
  let rounds := ttcPseudocode.firstLoopExit s intensity threshold
  let K : Nat → Measure (TTCState n × Nat) := fun pending =>
    fairCoinStreamLaw.map fun coins =>
      ttcPseudocode.secondLoopResult
        (ttcPseudocode.firstLoopResult s intensity threshold coins)
        pending threshold (shiftCoins rounds coins)
  have hK : Measurable K := Measurable.of_discrete
  have hmean : intensity * (s.p / (2 : NNReal) ^ rounds) =
      intensity / (2 : NNReal) ^ (level + rounds) := by
    rw [hrate, pow_add]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ac_rfl
  calc
    (ttcPseudocode.firstLoop s intensity threshold).bind (fun first =>
        (poissonMeasure (intensity * first.p)).bind fun pending =>
          ttcPseudocode.secondLoop first pending threshold) =
      (poissonMeasure (intensity * (s.p / (2 : NNReal) ^ rounds))).bind K := by
        exact poisson_twoLoops_oneCoinStream s intensity threshold
    _ = (poissonMeasure (intensity / (2 : NNReal) ^ (level + rounds))).bind K := by
          rw [hmean]
    _ = ((poissonMeasure intensity).bind fun basePending =>
          fairCoinStreamLaw.map fun preCoins =>
            pendingAfter preCoins (level + rounds) s.nextLabel basePending).bind K := by
          rw [poisson_absolute_level intensity s.nextLabel
            (level + rounds)]
    _ = _ := by
          rw [Measure.bind_bind
            (Measurable.of_discrete : Measurable (fun basePending : Nat =>
              fairCoinStreamLaw.map fun preCoins =>
                pendingAfter preCoins (level + rounds) s.nextLabel basePending)).aemeasurable
            hK.aemeasurable]
          congr 1
          funext basePending
          rw [bind_mapped_measure fairCoinStreamLaw
            (fun preCoins => pendingAfter preCoins
              (level + rounds) s.nextLabel basePending)
            (measurable_pendingAfter_fixed (level + rounds)
              s.nextLabel basePending) K hK]

end Kr25Ssmxt
