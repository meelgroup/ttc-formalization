import Kr25Ssmxt.Analysis.ManuscriptStoppedPrefixSource

/-! The merged thinning stop leaves an independent fair tail available to
any measurable continuation of its complete stopped coin prefix. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem firstExitRoundSplit_stoppedPrefix_shift_bind
    {n : Nat} (s : TTCState n) (pending : Nat) (threshold : Real)
    (hthreshold : 0 ≤ threshold) (hfresh : s.LabelsFresh)
    {β : Type*} [MeasurableSpace β]
    (K : ((Nat × Nat → Bool) × (Nat × Nat → Bool)) → Measure β)
    (hK : Measurable K) :
    (fairCoinStreamLaw.prod fairCoinStreamLaw).bind
      (fun pair =>
        let merged := mergeCoinsAtLabel s.nextLabel pair.1 pair.2
        let rounds := firstExitRoundSplit s pending threshold pair.1 pair.2
        K (coinPrefix rounds merged, shiftCoins rounds merged)) =
    ((fairCoinStreamLaw.prod fairCoinStreamLaw).map
      (fun pair =>
        coinPrefix (firstExitRoundSplit s pending threshold pair.1 pair.2)
          (mergeCoinsAtLabel s.nextLabel pair.1 pair.2))).bind
      (fun pre => fairCoinStreamLaw.bind (fun tail => K (pre, tail))) := by
  let μ := fairCoinStreamLaw.prod fairCoinStreamLaw
  let merge : ((Nat × Nat → Bool) × (Nat × Nat → Bool)) →
      Nat × Nat → Bool := fun pair =>
    mergeCoinsAtLabel s.nextLabel pair.1 pair.2
  let observed : ((Nat × Nat → Bool) × (Nat × Nat → Bool)) →
      Nat × Nat → Bool := fun pair =>
    coinPrefix (firstExitRoundSplit s pending threshold pair.1 pair.2)
      (merge pair)
  let tail : ((Nat × Nat → Bool) × (Nat × Nat → Bool)) →
      Nat × Nat → Bool := fun pair =>
    shiftCoins (firstExitRoundSplit s pending threshold pair.1 pair.2)
      (merge pair)
  let split : ((Nat × Nat → Bool) × (Nat × Nat → Bool)) →
      (Nat × Nat → Bool) × (Nat × Nat → Bool) :=
    fun pair => (observed pair, tail pair)
  have hmerge : Measurable merge :=
    measurable_mergeCoinsAtLabel_pair s.nextLabel
  have hsplit : Measurable split := by
    let H : (Nat × Nat → Bool) →
        (Nat × Nat → Bool) × (Nat × Nat → Bool) :=
      fun coins =>
        (stoppedCoinPrefix s pending threshold coins,
          shiftCoins (firstExitRound s pending threshold coins) coins)
    have hH : Measurable H :=
      (measurable_stoppedCoinPrefix s pending threshold).prodMk
        ((measurable_stoppedCoinPair
          (firstExitRound s pending threshold)
          (measurable_firstExitRound s pending threshold)).snd)
    have hpath : split = H ∘ merge := by
      funext pair
      have hround := firstExitRound_mergeCoinsAtLabel s pending threshold
        pair.1 pair.2 hfresh
      simp only [split, observed, tail, H, Function.comp_apply,
        stoppedCoinPrefix]
      rw [hround]
    rw [hpath]
    exact hH.comp hmerge
  have hlaw : μ.map split =
      (μ.map observed).prod fairCoinStreamLaw :=
    firstExitRoundSplit_stoppedPrefix_shift_law s pending threshold
      hthreshold hfresh
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  have hprod : Measurable
      (fun pre : Nat × Nat → Bool =>
        fairCoinStreamLaw.map (Prod.mk pre)) :=
    Measurable.map_prodMk_left
  calc
    μ.bind (fun pair => K (split pair)) =
      (μ.map split).bind K :=
        (bind_mapped_measure μ split hsplit K hK).symm
    _ = ((μ.map observed).prod fairCoinStreamLaw).bind K := by rw [hlaw]
    _ = (μ.map observed).bind
        (fun pre => fairCoinStreamLaw.bind (fun tail => K (pre, tail))) := by
      rw [Measure.prod]
      rw [Measure.bind_bind hprod.aemeasurable hK.aemeasurable]
      congr 1
      funext pre
      exact bind_mapped_measure fairCoinStreamLaw (Prod.mk pre)
        measurable_prodMk_left K hK

end Kr25Ssmxt
