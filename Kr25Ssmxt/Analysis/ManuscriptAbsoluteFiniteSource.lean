import Kr25Ssmxt.Analysis.ManuscriptActiveFiniteCoinLaw
import Kr25Ssmxt.Analysis.ManuscriptAbsoluteComponentSource

/-! The absolute Poisson pre-draw and active loop use a finite survivor-indexed
fresh-coin block. -/

namespace Kr25Ssmxt

open MeasureTheory ProbabilityTheory

noncomputable def manuscriptAbsoluteFinitePreKernel
    {n : Nat} (s : TTCState n) (intensity : NNReal)
    (threshold : Real) (level basePending : Nat)
    (preCoins : Nat × Nat → Bool) : Measure (TTCState n × Nat) :=
  let pending := pendingAfter preCoins
    (level + ttcPseudocode.firstLoopExit s intensity threshold)
    s.nextLabel basePending
  (fairCoinStreamLaw.prod
    (Measure.infinitePi (fun _ : Nat × Fin pending => fairCoinLaw))).map
    fun pair =>
      thinningResultSplitFinite
        (ttcPseudocode.firstLoopResult s intensity threshold pair.1)
        pending threshold
        (shiftCoins (ttcPseudocode.firstLoopExit s intensity threshold) pair.1)
        pair.2

theorem measurable_manuscript_absolute_finite_preKernel
    {n : Nat} (s : TTCState n) (intensity : NNReal)
    (threshold : Real) (level basePending : Nat) (hfresh : s.LabelsFresh) :
    Measurable (manuscriptAbsoluteFinitePreKernel s intensity threshold
      level basePending) := by
  let rounds := ttcPseudocode.firstLoopExit s intensity threshold
  let pending : (Nat × Nat → Bool) → Nat :=
    fun preCoins => pendingAfter preCoins (level + rounds)
      s.nextLabel basePending
  let K : Nat → Measure (TTCState n × Nat) := fun count =>
    fairCoinStreamLaw.map fun activeCoins =>
      ttcPseudocode.secondLoopResult
        (ttcPseudocode.firstLoopResult s intensity threshold activeCoins)
        count threshold (shiftCoins rounds activeCoins)
  have hK : Measurable K := Measurable.of_discrete
  have hpending : Measurable pending :=
    measurable_pendingAfter_fixed (level + rounds) s.nextLabel basePending
  have heq : manuscriptAbsoluteFinitePreKernel s intensity threshold
      level basePending = fun preCoins => K (pending preCoins) := by
    funext preCoins
    exact (manuscript_absolute_active_finite_coin_law s intensity threshold
      (pending preCoins) hfresh).symm
  rw [heq]
  exact hK.comp hpending

theorem manuscriptAbsoluteFiniteSource_bind
    {n : Nat} (s : TTCState n) (intensity : NNReal)
    (threshold : Real) (level : Nat) (hfresh : s.LabelsFresh)
    {β : Type*} [MeasurableSpace β]
    (K : TTCState n × Nat → Measure β) (hK : Measurable K) :
    (((poissonMeasure intensity).bind fun basePending =>
      fairCoinStreamLaw.bind
        (manuscriptAbsoluteFinitePreKernel s intensity threshold
          level basePending)).bind K =
    (poissonMeasure intensity).bind fun basePending =>
      fairCoinStreamLaw.bind fun preCoins =>
        (manuscriptAbsoluteFinitePreKernel s intensity threshold
          level basePending preCoins).bind K) := by
  let outer : Nat → Measure (TTCState n × Nat) := fun basePending =>
    fairCoinStreamLaw.bind
      (manuscriptAbsoluteFinitePreKernel s intensity threshold
        level basePending)
  have houter : Measurable outer := Measurable.of_discrete
  change ((poissonMeasure intensity).bind outer).bind K = _
  rw [Measure.bind_bind houter.aemeasurable hK.aemeasurable]
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro basePending
  change (fairCoinStreamLaw.bind
      (manuscriptAbsoluteFinitePreKernel s intensity threshold
        level basePending)).bind K =
    fairCoinStreamLaw.bind fun preCoins =>
      (manuscriptAbsoluteFinitePreKernel s intensity threshold
        level basePending preCoins).bind K
  rw [Measure.bind_bind
    (measurable_manuscript_absolute_finite_preKernel s intensity threshold
      level basePending hfresh).aemeasurable hK.aemeasurable]

theorem manuscript_poisson_twoLoops_absolute_finite
    {n : Nat} (s : TTCState n) (intensity : NNReal)
    (threshold : Real) (level : Nat) (hfresh : s.LabelsFresh) :
    ((poissonMeasure intensity).bind fun basePending =>
      fairCoinStreamLaw.bind fun preCoins =>
        fairCoinStreamLaw.map fun activeCoins =>
          ttcPseudocode.secondLoopResult
            (ttcPseudocode.firstLoopResult s intensity threshold activeCoins)
            (pendingAfter preCoins
              (level + ttcPseudocode.firstLoopExit s intensity threshold)
              s.nextLabel basePending)
            threshold
            (shiftCoins (ttcPseudocode.firstLoopExit s intensity threshold)
              activeCoins)) =
    ((poissonMeasure intensity).bind fun basePending =>
      fairCoinStreamLaw.bind fun preCoins =>
        let pending := pendingAfter preCoins
          (level + ttcPseudocode.firstLoopExit s intensity threshold)
          s.nextLabel basePending
        (fairCoinStreamLaw.prod
          (Measure.infinitePi (fun _ : Nat × Fin pending => fairCoinLaw))).map
          fun pair =>
            thinningResultSplitFinite
              (ttcPseudocode.firstLoopResult s intensity threshold pair.1)
              pending threshold
              (shiftCoins (ttcPseudocode.firstLoopExit s intensity threshold) pair.1)
              pair.2) := by
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro basePending
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro preCoins
  exact manuscript_absolute_active_finite_coin_law s intensity threshold
    (pendingAfter preCoins
      (level + ttcPseudocode.firstLoopExit s intensity threshold)
      s.nextLabel basePending) hfresh

end Kr25Ssmxt
