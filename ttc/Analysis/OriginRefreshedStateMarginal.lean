import ttc.Analysis.IndependentBindSwap

/-! Reorder the independent source refresh and Poisson count so the ghost
state marginal can be compared with the executable component law. -/

namespace ttc

open MeasureTheory

theorem originRefreshedComponentLaw_swap_count
    {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (c : OriginConfiguration n) :
    originRefreshedComponentLaw hn P b eta threshold hroute
      intensity c =
    (ProbabilityTheory.poissonMeasure intensity).bind fun basePending =>
      c.refreshLaw.bind fun refreshed =>
        originFairCoinTapeLaw hn P b eta threshold hroute
          intensity basePending refreshed := by
  letI : IsProbabilityMeasure c.refreshLaw :=
    c.refreshLaw_isProbabilityMeasure
  have hK : Measurable (fun z : OriginConfiguration n × Nat =>
      originFairCoinTapeLaw hn P b eta threshold hroute
        intensity z.2 z.1) := by
    apply measurable_from_prod_countable_left
    intro basePending
    exact measurable_originFairCoinTapeLaw hn P b eta
      threshold hthreshold hroute intensity basePending
  exact measure_independent_bind_comm c.refreshLaw
    (ProbabilityTheory.poissonMeasure intensity)
    (fun z : OriginConfiguration n × Nat =>
      originFairCoinTapeLaw hn P b eta threshold hroute
        intensity z.2 z.1) hK

noncomputable def originFutureTapeLaw
    {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (z : OriginConfiguration n × (Nat × Nat → Bool)) :
    Measure (OriginConfiguration n) :=
  fairCoinStreamLaw.bind fun future =>
    originCoinPairTapeLaw hn P b eta threshold hroute
      intensity basePending (z.1, (z.2, future))

theorem measurable_originFutureTapeLaw
    {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat) :
    Measurable (originFutureTapeLaw hn P b eta threshold
      hroute intensity basePending) := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  have hnext : Measurable (fun z :
      (OriginConfiguration n × (Nat × Nat → Bool)) ×
        (Nat × Nat → Bool) =>
      originCoinPairTapeLaw hn P b eta threshold hroute
        intensity basePending (z.1.1, (z.1.2, z.2))) :=
    (measurable_originCoinPairTapeLaw hn P b eta threshold
      hthreshold hroute intensity basePending).comp
        ((measurable_fst.comp measurable_fst).prodMk
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  exact measurable_parametric_probability_bind
    (fun _ : OriginConfiguration n × (Nat × Nat → Bool) =>
      fairCoinStreamLaw) measurable_const (fun _ => inferInstance)
    (fun z : (OriginConfiguration n × (Nat × Nat → Bool)) ×
      (Nat × Nat → Bool) =>
      originCoinPairTapeLaw hn P b eta threshold hroute
        intensity basePending (z.1.1, (z.1.2, z.2))) hnext

theorem originFairCoinTapeLaw_eq_nested
    {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (c : OriginConfiguration n) :
    originFairCoinTapeLaw hn P b eta threshold hroute
      intensity basePending c =
    fairCoinStreamLaw.bind fun preCoins =>
      originFutureTapeLaw hn P b eta threshold hroute
        intensity basePending (c, preCoins) := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  have hK : Measurable (fun coins :
      (Nat × Nat → Bool) × (Nat × Nat → Bool) =>
      originCoinPairTapeLaw hn P b eta threshold hroute
        intensity basePending (c, coins)) :=
    (measurable_originCoinPairTapeLaw hn P b eta threshold
      hthreshold hroute intensity basePending).comp
        (measurable_const.prodMk measurable_id)
  exact measure_prod_bind_eq_nested fairCoinStreamLaw fairCoinStreamLaw
    (fun coins => originCoinPairTapeLaw hn P b eta threshold
      hroute intensity basePending (c, coins)) hK

theorem originRefreshedComponentLaw_swap_preCoins
    {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (c : OriginConfiguration n) :
    c.refreshLaw.bind
      (originFairCoinTapeLaw hn P b eta threshold hroute
        intensity basePending) =
    fairCoinStreamLaw.bind fun preCoins =>
      c.refreshLaw.bind fun refreshed =>
        originFutureTapeLaw hn P b eta threshold hroute
          intensity basePending (refreshed, preCoins) := by
  letI : IsProbabilityMeasure c.refreshLaw :=
    c.refreshLaw_isProbabilityMeasure
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  have hK : Measurable (fun z : OriginConfiguration n ×
      (Nat × Nat → Bool) =>
      originFutureTapeLaw hn P b eta threshold hroute
        intensity basePending z) :=
    measurable_originFutureTapeLaw hn P b eta threshold
      hthreshold hroute intensity basePending
  calc
    c.refreshLaw.bind
        (originFairCoinTapeLaw hn P b eta threshold hroute
          intensity basePending) =
      c.refreshLaw.bind fun refreshed => fairCoinStreamLaw.bind
        (fun preCoins => originFutureTapeLaw hn P b eta
          threshold hroute intensity basePending (refreshed, preCoins)) := by
            apply Measure.bind_congr_right
            exact Filter.Eventually.of_forall (fun refreshed =>
              originFairCoinTapeLaw_eq_nested hn P b eta
                threshold hthreshold hroute intensity basePending refreshed)
    _ = _ := measure_independent_bind_comm c.refreshLaw
      fairCoinStreamLaw (fun z => originFutureTapeLaw hn P b
        eta threshold hroute intensity basePending z) hK

theorem originRefreshFutureTape_eq_product
    {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (preCoins : Nat × Nat → Bool)
    (c : OriginConfiguration n) :
    c.refreshLaw.bind (fun refreshed =>
      originFutureTapeLaw hn P b eta threshold hroute
        intensity basePending (refreshed, preCoins)) =
    ((Measure.infinitePi (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
      fairCoinStreamLaw).bind (fun pair =>
        originCoinPairTapeLaw hn P b eta threshold hroute
          intensity basePending
          (c.refreshFuture pair.1, (preCoins, pair.2))) := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  letI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
    fun _ => fairCoinLaw_isProbabilityMeasure
  letI : IsProbabilityMeasure sourceLaw := by
    dsimp [sourceLaw]
    infer_instance
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  have hfuture : Measurable (fun refreshed : OriginConfiguration n =>
      originFutureTapeLaw hn P b eta threshold hroute
        intensity basePending (refreshed, preCoins)) :=
    (measurable_originFutureTapeLaw hn P b eta threshold
      hthreshold hroute intensity basePending).comp
        (measurable_id.prodMk measurable_const)
  have hK : Measurable (fun pair :
      (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool) =>
      originCoinPairTapeLaw hn P b eta threshold hroute
        intensity basePending
        (c.refreshFuture pair.1, (preCoins, pair.2))) :=
    (measurable_originCoinPairTapeLaw hn P b eta threshold
      hthreshold hroute intensity basePending).comp
        (((c.measurable_refreshFuture).comp measurable_fst).prodMk
          (measurable_const.prodMk measurable_snd))
  change (sourceLaw.map c.refreshFuture).bind
      (fun refreshed => originFutureTapeLaw hn P b eta
        threshold hroute intensity basePending (refreshed, preCoins)) =
    (sourceLaw.prod fairCoinStreamLaw).bind
      (fun pair => originCoinPairTapeLaw hn P b eta threshold
        hroute intensity basePending
        (c.refreshFuture pair.1, (preCoins, pair.2)))
  rw [bind_mapped_measure sourceLaw c.refreshFuture
    c.measurable_refreshFuture _ hfuture]
  exact (measure_prod_bind_eq_nested sourceLaw fairCoinStreamLaw _ hK).symm

noncomputable def originOrderedComponentLaw
    {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (c : OriginConfiguration n) :
    Measure (OriginConfiguration n) :=
  (ProbabilityTheory.poissonMeasure intensity).bind fun basePending =>
    fairCoinStreamLaw.bind fun preCoins =>
      ((Measure.infinitePi
        (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
        fairCoinStreamLaw).bind fun pair =>
          originCoinPairTapeLaw hn P b eta threshold hroute
            intensity basePending
            (c.refreshFuture pair.1, (preCoins, pair.2))

theorem originRefreshedComponentLaw_eq_ordered
    {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (c : OriginConfiguration n) :
    originRefreshedComponentLaw hn P b eta threshold hroute
      intensity c =
    originOrderedComponentLaw hn P b eta threshold hroute
      intensity c := by
  rw [originRefreshedComponentLaw_swap_count hn P b eta
    threshold hthreshold hroute intensity c]
  unfold originOrderedComponentLaw
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro basePending
  change c.refreshLaw.bind
      (originFairCoinTapeLaw hn P b eta threshold hroute
        intensity basePending) =
    fairCoinStreamLaw.bind (fun preCoins =>
      ((Measure.infinitePi
        (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
        fairCoinStreamLaw).bind (fun pair =>
          originCoinPairTapeLaw hn P b eta threshold hroute
            intensity basePending
            (c.refreshFuture pair.1, (preCoins, pair.2))))
  rw [originRefreshedComponentLaw_swap_preCoins hn P b eta
    threshold hthreshold hroute intensity basePending c]
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro preCoins
  exact originRefreshFutureTape_eq_product hn P b eta
    threshold hthreshold hroute intensity basePending preCoins c

end ttc
