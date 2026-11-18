import Kr25Ssmxt.Analysis.OriginRefreshedStateMarginal

/-! State projection of the ordered refreshed ghost component law. -/

namespace Kr25Ssmxt

open MeasureTheory

noncomputable def originOrderedInnerLaw
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (c : OriginConfiguration n)
    (preCoins : Nat × Nat → Bool) :
    Measure (OriginConfiguration n) :=
  ((Measure.infinitePi
    (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
    fairCoinStreamLaw).bind fun pair =>
      originCoinPairTapeLaw hn P b eta threshold hroute
        intensity basePending
        (c.refreshFuture pair.1, (preCoins, pair.2))

theorem measurable_originOrderedInnerLaw_preCoins
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (c : OriginConfiguration n) :
    Measurable (originOrderedInnerLaw hn P b eta threshold
      hroute intensity basePending c) := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  letI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
    fun _ => fairCoinLaw_isProbabilityMeasure
  letI : IsProbabilityMeasure sourceLaw := by
    dsimp [sourceLaw]
    infer_instance
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  let pairLaw := sourceLaw.prod fairCoinStreamLaw
  letI : IsProbabilityMeasure pairLaw := by
    dsimp [pairLaw]
    infer_instance
  have hnext : Measurable (fun z : (Nat × Nat → Bool) ×
      ((Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool)) =>
      originCoinPairTapeLaw hn P b eta threshold hroute
        intensity basePending
        (c.refreshFuture z.2.1, (z.1, z.2.2))) :=
    (measurable_originCoinPairTapeLaw hn P b eta threshold
      hthreshold hroute intensity basePending).comp
        (((c.measurable_refreshFuture).comp
          (measurable_fst.comp measurable_snd)).prodMk
          (measurable_fst.prodMk
            (measurable_snd.comp measurable_snd)))
  exact measurable_parametric_probability_bind
    (fun _ : Nat × Nat → Bool => pairLaw) measurable_const
    (fun _ => inferInstance)
    (fun z : (Nat × Nat → Bool) ×
      ((Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool)) =>
      originCoinPairTapeLaw hn P b eta threshold hroute
        intensity basePending
        (c.refreshFuture z.2.1, (z.1, z.2.2))) hnext

theorem originCoinPairTapeLaw_map_state
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (z : OriginConfiguration n ×
      ((Nat × Nat → Bool) × (Nat × Nat → Bool))) :
    (originCoinPairTapeLaw hn P b eta threshold hroute
      intensity basePending z).map
        (fun next : OriginConfiguration n => next.state) =
    (Measure.infinitePi (fun _ : Nat =>
      normalizedHitAndRunPointLaw hn P b eta hroute.1
        hroute.2.1 hroute.2.2.1 hroute.2.2.2.1
          hroute.2.2.2.2)).map
      (fun tape => (z.1.advance P intensity threshold basePending
        z.2.1 z.2.2 tape).state) := by
  unfold originCoinPairTapeLaw
  rw [Measure.map_map measurable_originConfiguration_state
    (z.1.measurable_advance_tape P intensity threshold basePending
      z.2.1 z.2.2)]
  rfl

theorem originOrderedInnerLaw_map_state
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (c : OriginConfiguration n)
    (preCoins : Nat × Nat → Bool) :
    (originOrderedInnerLaw hn P b eta threshold hroute
      intensity basePending c preCoins).map
        (fun next : OriginConfiguration n => next.state) =
    ((Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
      fairCoinStreamLaw).bind (fun pair =>
        (Measure.infinitePi (fun _ : Nat =>
          normalizedHitAndRunPointLaw hn P b eta hroute.1
            hroute.2.1 hroute.2.2.1 hroute.2.2.2.1
              hroute.2.2.2.2)).map
          (fun tape =>
            ((c.refreshFuture pair.1).advance P intensity threshold
              basePending preCoins pair.2 tape).state)) := by
  let pairLaw := ((Measure.infinitePi
    (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod fairCoinStreamLaw)
  let K : ((Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool)) →
      Measure (OriginConfiguration n) := fun pair =>
    originCoinPairTapeLaw hn P b eta threshold hroute
      intensity basePending
      (c.refreshFuture pair.1, (preCoins, pair.2))
  have hK : Measurable K :=
    (measurable_originCoinPairTapeLaw hn P b eta threshold
      hthreshold hroute intensity basePending).comp
        (((c.measurable_refreshFuture).comp measurable_fst).prodMk
          (measurable_const.prodMk measurable_snd))
  change (pairLaw.bind K).map
      (fun next : OriginConfiguration n => next.state) = _
  rw [map_bind_measure pairLaw K
    (fun next : OriginConfiguration n => next.state)
    hK.aemeasurable measurable_originConfiguration_state]
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro pair
  exact originCoinPairTapeLaw_map_state hn P b eta threshold
    hroute intensity basePending
    (c.refreshFuture pair.1, (preCoins, pair.2))

theorem originOrderedComponentLaw_map_state
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (c : OriginConfiguration n) :
    (originOrderedComponentLaw hn P b eta threshold hroute
      intensity c).map
        (fun next : OriginConfiguration n => next.state) =
    (ProbabilityTheory.poissonMeasure intensity).bind (fun basePending =>
      fairCoinStreamLaw.bind (fun preCoins =>
        ((Measure.infinitePi
          (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
          fairCoinStreamLaw).bind (fun pair =>
            (Measure.infinitePi (fun _ : Nat =>
              normalizedHitAndRunPointLaw hn P b eta hroute.1
                hroute.2.1 hroute.2.2.1 hroute.2.2.2.1
                  hroute.2.2.2.2)).map (fun tape =>
                    ((c.refreshFuture pair.1).advance P intensity threshold
                      basePending preCoins pair.2 tape).state)))) := by
  let K₂ (basePending : Nat) (preCoins : Nat × Nat → Bool) :=
    originOrderedInnerLaw hn P b eta threshold hroute
      intensity basePending c preCoins
  have hK₂ (basePending : Nat) : Measurable (K₂ basePending) :=
    measurable_originOrderedInnerLaw_preCoins hn P b eta
      threshold hthreshold hroute intensity basePending c
  let K₁ (basePending : Nat) := fairCoinStreamLaw.bind (K₂ basePending)
  have hK₁ : Measurable K₁ := measurable_of_countable _
  change ((ProbabilityTheory.poissonMeasure intensity).bind K₁).map
      (fun next : OriginConfiguration n => next.state) = _
  rw [map_bind_measure (ProbabilityTheory.poissonMeasure intensity) K₁
    (fun next : OriginConfiguration n => next.state)
    hK₁.aemeasurable measurable_originConfiguration_state]
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro basePending
  change (fairCoinStreamLaw.bind (K₂ basePending)).map
      (fun next : OriginConfiguration n => next.state) = _
  rw [map_bind_measure fairCoinStreamLaw (K₂ basePending)
    (fun next : OriginConfiguration n => next.state)
    (hK₂ basePending).aemeasurable
    measurable_originConfiguration_state]
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro preCoins
  exact originOrderedInnerLaw_map_state hn P b eta threshold
    hthreshold hroute intensity basePending c preCoins

theorem originOrderedComponentLaw_map_state_eq_givenVolume
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (c : OriginConfiguration n) (outcome : VolumeOutcome) :
    (originOrderedComponentLaw hn P b eta threshold hroute
      (ttcReference.t b n threshold outcome.2) c).map
        (fun next : OriginConfiguration n => next.state) =
    communityComponentGivenVolume hn prep P b eta delta
      threshold outcome c.state := by
  rw [originOrderedComponentLaw_map_state hn P b eta threshold
    hthreshold hroute (ttcReference.t b n threshold outcome.2) c]
  exact c.refreshFuture_component_state_law hn prep P b eta delta
    threshold hroute outcome

theorem originRefreshedComponentLaw_map_state_eq_givenVolume
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (c : OriginConfiguration n) (outcome : VolumeOutcome) :
    (originRefreshedComponentLaw hn P b eta threshold hroute
      (ttcReference.t b n threshold outcome.2) c).map
        (fun next : OriginConfiguration n => next.state) =
    communityComponentGivenVolume hn prep P b eta delta
      threshold outcome c.state := by
  rw [originRefreshedComponentLaw_eq_ordered hn P b eta
    threshold hthreshold hroute
    (ttcReference.t b n threshold outcome.2) c]
  exact originOrderedComponentLaw_map_state_eq_givenVolume hn
    prep P b eta delta threshold hthreshold hroute c outcome

end Kr25Ssmxt
