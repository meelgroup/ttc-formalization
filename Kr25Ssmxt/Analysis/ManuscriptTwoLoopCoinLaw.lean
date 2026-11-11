import Kr25Ssmxt.Analysis.MathlibCompat
import Kr25Ssmxt.Analysis.ManuscriptCoinSpliceLaw
import Kr25Ssmxt.Analysis.ThinUntilKernelMeasurable
import Kr25Ssmxt.Analysis.CostedMeasureMonad

/-! With a fixed pending count, the manuscript's two independent thinning
loops have the law of one fair stream at consecutive absolute rounds. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem measurable_shiftCoins (rounds : Nat) :
    Measurable (shiftCoins rounds) := by
  apply Measurable.of_eval
  intro pair
  exact measurable_pi_apply (pair.1 + rounds, pair.2)

theorem manuscript_twoLoops_givenPending_eq_oneCoinStream
    {n : Nat} (s : TTCState n) (intensity : NNReal)
    (threshold : Real) (pending : Nat) :
    (ttcPseudocode.firstLoop s intensity threshold).bind
      (fun first => ttcPseudocode.secondLoop first pending threshold) =
    fairCoinStreamLaw.map (fun coins =>
      ttcPseudocode.secondLoopResult
        (ttcPseudocode.firstLoopResult s intensity threshold coins)
        pending threshold
        (shiftCoins (ttcPseudocode.firstLoopExit s intensity threshold) coins)) := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  let rounds := ttcPseudocode.firstLoopExit s intensity threshold
  let firstResult := ttcPseudocode.firstLoopResult s intensity threshold
  let K := fun first : TTCState n => ttcPseudocode.secondLoop first pending threshold
  have hK : Measurable K :=
    (thinUntil_kernel_measurable threshold).comp
      (measurable_id.prodMk measurable_const)
  have hfirst : Measurable firstResult :=
    measurable_manuscriptRateThinningResult s intensity threshold
  let pairResult :
      (Nat × Nat → Bool) × (Nat × Nat → Bool) → TTCState n × Nat :=
    fun pair => ttcPseudocode.secondLoopResult (firstResult pair.1) pending threshold pair.2
  have hpair : Measurable pairResult :=
    (measurable_thinningResult_joint threshold).comp
      (((hfirst.comp measurable_fst).prodMk measurable_const).prodMk
        measurable_snd)
  let oneResult : (Nat × Nat → Bool) → TTCState n × Nat :=
    fun coins => ttcPseudocode.secondLoopResult (firstResult coins) pending threshold
      (shiftCoins rounds coins)
  have hone : Measurable oneResult :=
    (measurable_thinningResult_joint threshold).comp
      ((hfirst.prodMk measurable_const).prodMk
        (measurable_shiftCoins rounds))
  have hpairLaw :
      (fairCoinStreamLaw.map firstResult).bind K =
        (fairCoinStreamLaw.prod fairCoinStreamLaw).map pairResult := by
    rw [bind_mapped_measure fairCoinStreamLaw firstResult hfirst K hK]
    rw [Measure.prod_eq_bind_map]
    rw [map_bind_measure fairCoinStreamLaw
      (fun first : Nat × Nat → Bool =>
        fairCoinStreamLaw.map (Prod.mk first)) pairResult
      (Measurable.map_prodMk_left.aemeasurable) hpair]
    congr 1
    funext first
    rw [Measure.map_map hpair measurable_prodMk_left]
    rfl
  have hpath (pair : (Nat × Nat → Bool) × (Nat × Nat → Bool)) :
      pairResult pair = oneResult (spliceCoins pair.1 pair.2 rounds) := by
    dsimp only [pairResult, oneResult, firstResult]
    rw [manuscriptRateThinningResult_spliceCoins s intensity threshold
      pair.1 pair.2]
    rw [shiftCoins_spliceCoins pair.1 pair.2 rounds]
  change (fairCoinStreamLaw.map firstResult).bind K =
    fairCoinStreamLaw.map oneResult
  calc
    (fairCoinStreamLaw.map firstResult).bind K =
      (fairCoinStreamLaw.prod fairCoinStreamLaw).map pairResult := hpairLaw
    _ = (fairCoinStreamLaw.prod fairCoinStreamLaw).map
        (oneResult ∘ fun pair => spliceCoins pair.1 pair.2 rounds) := by
          congr 1
          funext pair
          exact hpath pair
    _ = ((fairCoinStreamLaw.prod fairCoinStreamLaw).map
        (fun pair => spliceCoins pair.1 pair.2 rounds)).map oneResult := by
          rw [Measure.map_map hone (measurable_spliceCoins_pair rounds)]
    _ = fairCoinStreamLaw.map oneResult := by
          rw [fairCoinStreamLaw_splice rounds]

end Kr25Ssmxt
