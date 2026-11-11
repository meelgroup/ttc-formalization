import Kr25Ssmxt.Analysis.ManuscriptOriginRefreshedStateMarginal

/-! State projection of the ordered refreshed ghost component law. -/

namespace Kr25Ssmxt

open MeasureTheory

noncomputable def manuscriptOriginOrderedInnerLaw
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (c : ManuscriptOriginConfiguration n)
    (preCoins : Nat × Nat → Bool) :
    Measure (ManuscriptOriginConfiguration n) :=
  ((Measure.infinitePi
    (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
    fairCoinStreamLaw).bind fun pair =>
      manuscriptOriginCoinPairTapeLaw hn P b eta threshold hroute
        intensity basePending
        (c.refreshFuture pair.1, (preCoins, pair.2))

theorem measurable_manuscriptOriginOrderedInnerLaw_preCoins
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (c : ManuscriptOriginConfiguration n) :
    Measurable (manuscriptOriginOrderedInnerLaw hn P b eta threshold
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
      manuscriptOriginCoinPairTapeLaw hn P b eta threshold hroute
        intensity basePending
        (c.refreshFuture z.2.1, (z.1, z.2.2))) :=
    (measurable_manuscriptOriginCoinPairTapeLaw hn P b eta threshold
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
      manuscriptOriginCoinPairTapeLaw hn P b eta threshold hroute
        intensity basePending
        (c.refreshFuture z.2.1, (z.1, z.2.2))) hnext

theorem manuscriptOriginCoinPairTapeLaw_map_state
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (z : ManuscriptOriginConfiguration n ×
      ((Nat × Nat → Bool) × (Nat × Nat → Bool))) :
    (manuscriptOriginCoinPairTapeLaw hn P b eta threshold hroute
      intensity basePending z).map
        (fun next : ManuscriptOriginConfiguration n => next.state) =
    (Measure.infinitePi (fun _ : Nat =>
      normalizedHitAndRunPointLaw hn P b hroute.1 eta
        hroute.2.1 hroute.2.2.1 hroute.2.2.2.1
          hroute.2.2.2.2)).map
      (fun tape => (z.1.advance P intensity threshold basePending
        z.2.1 z.2.2 tape).state) := by
  unfold manuscriptOriginCoinPairTapeLaw
  rw [Measure.map_map measurable_manuscriptOriginConfiguration_state
    (z.1.measurable_advance_tape P intensity threshold basePending
      z.2.1 z.2.2)]
  rfl

theorem manuscriptOriginOrderedInnerLaw_map_state
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (c : ManuscriptOriginConfiguration n)
    (preCoins : Nat × Nat → Bool) :
    (manuscriptOriginOrderedInnerLaw hn P b eta threshold hroute
      intensity basePending c preCoins).map
        (fun next : ManuscriptOriginConfiguration n => next.state) =
    ((Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
      fairCoinStreamLaw).bind (fun pair =>
        (Measure.infinitePi (fun _ : Nat =>
          normalizedHitAndRunPointLaw hn P b hroute.1 eta
            hroute.2.1 hroute.2.2.1 hroute.2.2.2.1
              hroute.2.2.2.2)).map
          (fun tape =>
            ((c.refreshFuture pair.1).advance P intensity threshold
              basePending preCoins pair.2 tape).state)) := by
  let pairLaw := ((Measure.infinitePi
    (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod fairCoinStreamLaw)
  let K : ((Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool)) →
      Measure (ManuscriptOriginConfiguration n) := fun pair =>
    manuscriptOriginCoinPairTapeLaw hn P b eta threshold hroute
      intensity basePending
      (c.refreshFuture pair.1, (preCoins, pair.2))
  have hK : Measurable K :=
    (measurable_manuscriptOriginCoinPairTapeLaw hn P b eta threshold
      hthreshold hroute intensity basePending).comp
        (((c.measurable_refreshFuture).comp measurable_fst).prodMk
          (measurable_const.prodMk measurable_snd))
  change (pairLaw.bind K).map
      (fun next : ManuscriptOriginConfiguration n => next.state) = _
  rw [map_bind_measure pairLaw K
    (fun next : ManuscriptOriginConfiguration n => next.state)
    hK.aemeasurable measurable_manuscriptOriginConfiguration_state]
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro pair
  exact manuscriptOriginCoinPairTapeLaw_map_state hn P b eta threshold
    hroute intensity basePending
    (c.refreshFuture pair.1, (preCoins, pair.2))

theorem manuscriptOriginOrderedComponentLaw_map_state
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (c : ManuscriptOriginConfiguration n) :
    (manuscriptOriginOrderedComponentLaw hn P b eta threshold hroute
      intensity c).map
        (fun next : ManuscriptOriginConfiguration n => next.state) =
    (ProbabilityTheory.poissonMeasure intensity).bind (fun basePending =>
      fairCoinStreamLaw.bind (fun preCoins =>
        ((Measure.infinitePi
          (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
          fairCoinStreamLaw).bind (fun pair =>
            (Measure.infinitePi (fun _ : Nat =>
              normalizedHitAndRunPointLaw hn P b hroute.1 eta
                hroute.2.1 hroute.2.2.1 hroute.2.2.2.1
                  hroute.2.2.2.2)).map (fun tape =>
                    ((c.refreshFuture pair.1).advance P intensity threshold
                      basePending preCoins pair.2 tape).state)))) := by
  let K₂ (basePending : Nat) (preCoins : Nat × Nat → Bool) :=
    manuscriptOriginOrderedInnerLaw hn P b eta threshold hroute
      intensity basePending c preCoins
  have hK₂ (basePending : Nat) : Measurable (K₂ basePending) :=
    measurable_manuscriptOriginOrderedInnerLaw_preCoins hn P b eta
      threshold hthreshold hroute intensity basePending c
  let K₁ (basePending : Nat) := fairCoinStreamLaw.bind (K₂ basePending)
  have hK₁ : Measurable K₁ := measurable_of_countable _
  change ((ProbabilityTheory.poissonMeasure intensity).bind K₁).map
      (fun next : ManuscriptOriginConfiguration n => next.state) = _
  rw [map_bind_measure (ProbabilityTheory.poissonMeasure intensity) K₁
    (fun next : ManuscriptOriginConfiguration n => next.state)
    hK₁.aemeasurable measurable_manuscriptOriginConfiguration_state]
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro basePending
  change (fairCoinStreamLaw.bind (K₂ basePending)).map
      (fun next : ManuscriptOriginConfiguration n => next.state) = _
  rw [map_bind_measure fairCoinStreamLaw (K₂ basePending)
    (fun next : ManuscriptOriginConfiguration n => next.state)
    (hK₂ basePending).aemeasurable
    measurable_manuscriptOriginConfiguration_state]
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro preCoins
  exact manuscriptOriginOrderedInnerLaw_map_state hn P b eta threshold
    hthreshold hroute intensity basePending c preCoins

theorem manuscriptOriginOrderedComponentLaw_map_state_eq_givenVolume
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (c : ManuscriptOriginConfiguration n) (outcome : VolumeOutcome) :
    (manuscriptOriginOrderedComponentLaw hn P b eta threshold hroute
      (ttcPseudocode.t b n threshold outcome.2) c).map
        (fun next : ManuscriptOriginConfiguration n => next.state) =
    communityManuscriptComponentGivenVolume hn prep P b eta delta
      threshold outcome c.state := by
  rw [manuscriptOriginOrderedComponentLaw_map_state hn P b eta threshold
    hthreshold hroute (ttcPseudocode.t b n threshold outcome.2) c]
  exact c.refreshFuture_component_state_law hn prep P b eta delta
    threshold hroute outcome

theorem manuscriptOriginRefreshedComponentLaw_map_state_eq_givenVolume
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (c : ManuscriptOriginConfiguration n) (outcome : VolumeOutcome) :
    (manuscriptOriginRefreshedComponentLaw hn P b eta threshold hroute
      (ttcPseudocode.t b n threshold outcome.2) c).map
        (fun next : ManuscriptOriginConfiguration n => next.state) =
    communityManuscriptComponentGivenVolume hn prep P b eta delta
      threshold outcome c.state := by
  rw [manuscriptOriginRefreshedComponentLaw_eq_ordered hn P b eta
    threshold hthreshold hroute
    (ttcPseudocode.t b n threshold outcome.2) c]
  exact manuscriptOriginOrderedComponentLaw_map_state_eq_givenVolume hn
    prep P b eta delta threshold hthreshold hroute c outcome

end Kr25Ssmxt
