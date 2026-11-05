import Kr25Ssmxt.Analysis.ManuscriptIndependentBindSwap

/-! Reorder the independent source refresh and Poisson count so the ghost
state marginal can be compared with the executable component law. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem manuscriptOriginRefreshedComponentLaw_swap_count
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (c : ManuscriptOriginConfiguration n) :
    manuscriptOriginRefreshedComponentLaw hn P b eta threshold hroute
      intensity c =
    (ProbabilityTheory.poissonMeasure intensity).bind fun basePending =>
      c.refreshLaw.bind fun refreshed =>
        manuscriptOriginFairCoinTapeLaw hn P b eta threshold hroute
          intensity basePending refreshed := by
  letI : IsProbabilityMeasure c.refreshLaw :=
    c.refreshLaw_isProbabilityMeasure
  have hK : Measurable (fun z : ManuscriptOriginConfiguration n × Nat =>
      manuscriptOriginFairCoinTapeLaw hn P b eta threshold hroute
        intensity z.2 z.1) := by
    apply measurable_from_prod_countable_left
    intro basePending
    exact measurable_manuscriptOriginFairCoinTapeLaw hn P b eta
      threshold hthreshold hroute intensity basePending
  exact measure_independent_bind_comm c.refreshLaw
    (ProbabilityTheory.poissonMeasure intensity)
    (fun z : ManuscriptOriginConfiguration n × Nat =>
      manuscriptOriginFairCoinTapeLaw hn P b eta threshold hroute
        intensity z.2 z.1) hK

noncomputable def manuscriptOriginFutureTapeLaw
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (z : ManuscriptOriginConfiguration n × (Nat × Nat → Bool)) :
    Measure (ManuscriptOriginConfiguration n) :=
  fairCoinStreamLaw.bind fun future =>
    manuscriptOriginCoinPairTapeLaw hn P b eta threshold hroute
      intensity basePending (z.1, (z.2, future))

theorem measurable_manuscriptOriginFutureTapeLaw
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat) :
    Measurable (manuscriptOriginFutureTapeLaw hn P b eta threshold
      hroute intensity basePending) := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  have hnext : Measurable (fun z :
      (ManuscriptOriginConfiguration n × (Nat × Nat → Bool)) ×
        (Nat × Nat → Bool) =>
      manuscriptOriginCoinPairTapeLaw hn P b eta threshold hroute
        intensity basePending (z.1.1, (z.1.2, z.2))) :=
    (measurable_manuscriptOriginCoinPairTapeLaw hn P b eta threshold
      hthreshold hroute intensity basePending).comp
        ((measurable_fst.comp measurable_fst).prodMk
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  exact measurable_parametric_probability_bind
    (fun _ : ManuscriptOriginConfiguration n × (Nat × Nat → Bool) =>
      fairCoinStreamLaw) measurable_const (fun _ => inferInstance)
    (fun z : (ManuscriptOriginConfiguration n × (Nat × Nat → Bool)) ×
      (Nat × Nat → Bool) =>
      manuscriptOriginCoinPairTapeLaw hn P b eta threshold hroute
        intensity basePending (z.1.1, (z.1.2, z.2))) hnext

theorem manuscriptOriginFairCoinTapeLaw_eq_nested
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (c : ManuscriptOriginConfiguration n) :
    manuscriptOriginFairCoinTapeLaw hn P b eta threshold hroute
      intensity basePending c =
    fairCoinStreamLaw.bind fun preCoins =>
      manuscriptOriginFutureTapeLaw hn P b eta threshold hroute
        intensity basePending (c, preCoins) := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  have hK : Measurable (fun coins :
      (Nat × Nat → Bool) × (Nat × Nat → Bool) =>
      manuscriptOriginCoinPairTapeLaw hn P b eta threshold hroute
        intensity basePending (c, coins)) :=
    (measurable_manuscriptOriginCoinPairTapeLaw hn P b eta threshold
      hthreshold hroute intensity basePending).comp
        (measurable_const.prodMk measurable_id)
  exact measure_prod_bind_eq_nested fairCoinStreamLaw fairCoinStreamLaw
    (fun coins => manuscriptOriginCoinPairTapeLaw hn P b eta threshold
      hroute intensity basePending (c, coins)) hK

theorem manuscriptOriginRefreshedComponentLaw_swap_preCoins
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (c : ManuscriptOriginConfiguration n) :
    c.refreshLaw.bind
      (manuscriptOriginFairCoinTapeLaw hn P b eta threshold hroute
        intensity basePending) =
    fairCoinStreamLaw.bind fun preCoins =>
      c.refreshLaw.bind fun refreshed =>
        manuscriptOriginFutureTapeLaw hn P b eta threshold hroute
          intensity basePending (refreshed, preCoins) := by
  letI : IsProbabilityMeasure c.refreshLaw :=
    c.refreshLaw_isProbabilityMeasure
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  have hK : Measurable (fun z : ManuscriptOriginConfiguration n ×
      (Nat × Nat → Bool) =>
      manuscriptOriginFutureTapeLaw hn P b eta threshold hroute
        intensity basePending z) :=
    measurable_manuscriptOriginFutureTapeLaw hn P b eta threshold
      hthreshold hroute intensity basePending
  calc
    c.refreshLaw.bind
        (manuscriptOriginFairCoinTapeLaw hn P b eta threshold hroute
          intensity basePending) =
      c.refreshLaw.bind fun refreshed => fairCoinStreamLaw.bind
        (fun preCoins => manuscriptOriginFutureTapeLaw hn P b eta
          threshold hroute intensity basePending (refreshed, preCoins)) := by
            apply Measure.bind_congr_right
            exact Filter.Eventually.of_forall (fun refreshed =>
              manuscriptOriginFairCoinTapeLaw_eq_nested hn P b eta
                threshold hthreshold hroute intensity basePending refreshed)
    _ = _ := measure_independent_bind_comm c.refreshLaw
      fairCoinStreamLaw (fun z => manuscriptOriginFutureTapeLaw hn P b
        eta threshold hroute intensity basePending z) hK

theorem manuscriptOriginRefreshFutureTape_eq_product
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (preCoins : Nat × Nat → Bool)
    (c : ManuscriptOriginConfiguration n) :
    c.refreshLaw.bind (fun refreshed =>
      manuscriptOriginFutureTapeLaw hn P b eta threshold hroute
        intensity basePending (refreshed, preCoins)) =
    ((Measure.infinitePi (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
      fairCoinStreamLaw).bind (fun pair =>
        manuscriptOriginCoinPairTapeLaw hn P b eta threshold hroute
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
  have hfuture : Measurable (fun refreshed : ManuscriptOriginConfiguration n =>
      manuscriptOriginFutureTapeLaw hn P b eta threshold hroute
        intensity basePending (refreshed, preCoins)) :=
    (measurable_manuscriptOriginFutureTapeLaw hn P b eta threshold
      hthreshold hroute intensity basePending).comp
        (measurable_id.prodMk measurable_const)
  have hK : Measurable (fun pair :
      (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool) =>
      manuscriptOriginCoinPairTapeLaw hn P b eta threshold hroute
        intensity basePending
        (c.refreshFuture pair.1, (preCoins, pair.2))) :=
    (measurable_manuscriptOriginCoinPairTapeLaw hn P b eta threshold
      hthreshold hroute intensity basePending).comp
        (((c.measurable_refreshFuture).comp measurable_fst).prodMk
          (measurable_const.prodMk measurable_snd))
  change (sourceLaw.map c.refreshFuture).bind
      (fun refreshed => manuscriptOriginFutureTapeLaw hn P b eta
        threshold hroute intensity basePending (refreshed, preCoins)) =
    (sourceLaw.prod fairCoinStreamLaw).bind
      (fun pair => manuscriptOriginCoinPairTapeLaw hn P b eta threshold
        hroute intensity basePending
        (c.refreshFuture pair.1, (preCoins, pair.2)))
  rw [bind_mapped_measure sourceLaw c.refreshFuture
    c.measurable_refreshFuture _ hfuture]
  exact (measure_prod_bind_eq_nested sourceLaw fairCoinStreamLaw _ hK).symm

noncomputable def manuscriptOriginOrderedComponentLaw
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (c : ManuscriptOriginConfiguration n) :
    Measure (ManuscriptOriginConfiguration n) :=
  (ProbabilityTheory.poissonMeasure intensity).bind fun basePending =>
    fairCoinStreamLaw.bind fun preCoins =>
      ((Measure.infinitePi
        (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
        fairCoinStreamLaw).bind fun pair =>
          manuscriptOriginCoinPairTapeLaw hn P b eta threshold hroute
            intensity basePending
            (c.refreshFuture pair.1, (preCoins, pair.2))

theorem manuscriptOriginRefreshedComponentLaw_eq_ordered
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (c : ManuscriptOriginConfiguration n) :
    manuscriptOriginRefreshedComponentLaw hn P b eta threshold hroute
      intensity c =
    manuscriptOriginOrderedComponentLaw hn P b eta threshold hroute
      intensity c := by
  rw [manuscriptOriginRefreshedComponentLaw_swap_count hn P b eta
    threshold hthreshold hroute intensity c]
  unfold manuscriptOriginOrderedComponentLaw
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro basePending
  change c.refreshLaw.bind
      (manuscriptOriginFairCoinTapeLaw hn P b eta threshold hroute
        intensity basePending) =
    fairCoinStreamLaw.bind (fun preCoins =>
      ((Measure.infinitePi
        (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
        fairCoinStreamLaw).bind (fun pair =>
          manuscriptOriginCoinPairTapeLaw hn P b eta threshold hroute
            intensity basePending
            (c.refreshFuture pair.1, (preCoins, pair.2))))
  rw [manuscriptOriginRefreshedComponentLaw_swap_preCoins hn P b eta
    threshold hthreshold hroute intensity basePending c]
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro preCoins
  exact manuscriptOriginRefreshFutureTape_eq_product hn P b eta
    threshold hthreshold hroute intensity basePending preCoins c

end Kr25Ssmxt
