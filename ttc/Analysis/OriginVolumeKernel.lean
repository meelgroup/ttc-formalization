import ttc.Analysis.OriginVaryingRefreshKernel

/-! Integrate the varying-intensity refreshed ghost transition over one
CV18 volume-outcome law. -/

namespace ttc

open MeasureTheory

noncomputable def originComponentVolumeLaw
    {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (volumeLaw : Measure VolumeOutcome)
    (c : OriginConfiguration n) :
    Measure (OriginConfiguration n) :=
  volumeLaw.bind fun outcome =>
    originRefreshedComponentLaw hn P b eta threshold hroute
      (ttcReference.t b n threshold outcome.2) c

theorem measurable_intensity_outcome
    {n : Nat} (b : Nat) (threshold : Real) :
    Measurable (fun z : OriginConfiguration n × VolumeOutcome =>
      ttcReference.t b n threshold z.2.2) := by
  unfold ttcReference.t
  exact (measurable_const.mul measurable_const).mul
    (measurable_snd.comp measurable_snd)

set_option maxHeartbeats 1000000 in
theorem measurable_originComponentVolumeLaw
    {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (volumeLaw : Measure VolumeOutcome)
    (hvolume : IsProbabilityMeasure volumeLaw) :
    Measurable (originComponentVolumeLaw hn P b eta threshold
      hroute volumeLaw) := by
  have hpair : Measurable (fun z :
      OriginConfiguration n × VolumeOutcome =>
      (z.1, ttcReference.t b n threshold z.2.2)) :=
    measurable_fst.prodMk
      (measurable_intensity_outcome b threshold)
  have hnext : Measurable (fun z :
      OriginConfiguration n × VolumeOutcome =>
      originRefreshedComponentLaw hn P b eta threshold hroute
        (ttcReference.t b n threshold z.2.2) z.1) := by
    have hcomp :=
      (measurable_originRefreshedComponentLaw_intensity hn P b
        eta threshold hthreshold hroute).comp hpair
    simpa only [Function.comp_def] using hcomp
  exact measurable_parametric_probability_bind
    (fun _ : OriginConfiguration n => volumeLaw)
    measurable_const (fun _ => hvolume)
    (fun z : OriginConfiguration n × VolumeOutcome =>
      originRefreshedComponentLaw hn P b eta threshold hroute
        (ttcReference.t b n threshold z.2.2) z.1) hnext

theorem measurable_originRefreshedComponentLaw_outcome
    {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (c : OriginConfiguration n) :
    Measurable (fun outcome : VolumeOutcome =>
      originRefreshedComponentLaw hn P b eta threshold hroute
        (ttcReference.t b n threshold outcome.2) c) := by
  have hpair : Measurable (fun outcome : VolumeOutcome =>
      (c, ttcReference.t b n threshold outcome.2)) := by
    apply measurable_const.prodMk
    unfold ttcReference.t
    exact (measurable_const.mul measurable_const).mul measurable_snd
  have hcomp :=
    (measurable_originRefreshedComponentLaw_intensity hn P b
      eta threshold hthreshold hroute).comp hpair
  simpa only [Function.comp_def] using hcomp

theorem originComponentVolumeLaw_isProbabilityMeasure
    {n : Nat} (hn : 3 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (volumeLaw : Measure VolumeOutcome)
    (hvolume : IsProbabilityMeasure volumeLaw)
    (c : OriginConfiguration n) :
    IsProbabilityMeasure (originComponentVolumeLaw hn P b eta
      threshold hroute volumeLaw c) := by
  letI : IsProbabilityMeasure volumeLaw := hvolume
  unfold originComponentVolumeLaw
  exact isProbabilityMeasure_bind
    (measurable_originRefreshedComponentLaw_outcome hn P b
      eta threshold hthreshold hroute c).aemeasurable
    (Filter.Eventually.of_forall (fun outcome =>
      originRefreshedComponentLaw_isProbabilityMeasure hn P b
        eta threshold hthreshold hroute
        (ttcReference.t b n threshold outcome.2) c))

set_option maxHeartbeats 1000000 in
theorem originComponentVolumeLaw_map_state
    {n k : Nat} (hn : 3 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (volumeLaw : Measure VolumeOutcome)
    (c : OriginConfiguration n) :
    (originComponentVolumeLaw hn P b eta threshold hroute
      volumeLaw c).map
        (fun next : OriginConfiguration n => next.state) =
    volumeLaw.bind (fun outcome =>
      communityComponentGivenVolume hn prep P b eta delta
        threshold outcome c.state) := by
  let K : VolumeOutcome → Measure (OriginConfiguration n) :=
    fun outcome => originRefreshedComponentLaw hn P b eta
      threshold hroute (ttcReference.t b n threshold outcome.2) c
  have hK : Measurable K :=
    measurable_originRefreshedComponentLaw_outcome hn P b eta
      threshold hthreshold hroute c
  change (volumeLaw.bind K).map
    (fun next : OriginConfiguration n => next.state) = _
  rw [map_bind_measure volumeLaw K
    (fun next : OriginConfiguration n => next.state)
    hK.aemeasurable measurable_originConfiguration_state]
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro outcome
  exact originRefreshedComponentLaw_map_state_eq_givenVolume
    hn prep P b eta delta threshold hthreshold hroute c outcome

noncomputable def communityOriginComponentLaw
    {n k : Nat} (hn : 3 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (c : OriginConfiguration n) :
    Measure (OriginConfiguration n) :=
  originComponentVolumeLaw hn P b eta threshold hroute
    ((ttcSubroutines hn prep).ComputeVolume P eta delta) c

theorem communityOriginComponentLaw_map_state
    {n k : Nat} (hn : 3 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (c : OriginConfiguration n) :
    (communityOriginComponentLaw hn prep P b eta delta
      threshold hroute c).map
        (fun next : OriginConfiguration n => next.state) =
    ttcReference.step (ttcSubroutines hn prep)
      b eta delta threshold P c.state := by
  unfold communityOriginComponentLaw
  rw [originComponentVolumeLaw_map_state hn prep P b eta delta
    threshold hthreshold hroute
    ((ttcSubroutines hn prep).ComputeVolume P eta delta) c]
  rfl

end ttc
