import Kr25Ssmxt.Analysis.ManuscriptOriginVaryingRefreshKernel

/-! Integrate the varying-intensity refreshed ghost transition over one
CV18 volume-outcome law. -/

namespace Kr25Ssmxt

open MeasureTheory

noncomputable def manuscriptOriginComponentVolumeLaw
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (volumeLaw : Measure VolumeOutcome)
    (c : ManuscriptOriginConfiguration n) :
    Measure (ManuscriptOriginConfiguration n) :=
  volumeLaw.bind fun outcome =>
    manuscriptOriginRefreshedComponentLaw hn P b eta threshold hroute
      (ttc.t b n threshold outcome.2) c

theorem measurable_manuscriptIntensity_outcome
    {n : Nat} (b : Nat) (threshold : Real) :
    Measurable (fun z : ManuscriptOriginConfiguration n × VolumeOutcome =>
      ttc.t b n threshold z.2.2) := by
  unfold ttc.t
  exact (measurable_const.mul measurable_const).mul
    (measurable_snd.comp measurable_snd)

set_option maxHeartbeats 1000000 in
theorem measurable_manuscriptOriginComponentVolumeLaw
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (volumeLaw : Measure VolumeOutcome)
    (hvolume : IsProbabilityMeasure volumeLaw) :
    Measurable (manuscriptOriginComponentVolumeLaw hn P b eta threshold
      hroute volumeLaw) := by
  have hpair : Measurable (fun z :
      ManuscriptOriginConfiguration n × VolumeOutcome =>
      (z.1, ttc.t b n threshold z.2.2)) :=
    measurable_fst.prodMk
      (measurable_manuscriptIntensity_outcome b threshold)
  have hnext : Measurable (fun z :
      ManuscriptOriginConfiguration n × VolumeOutcome =>
      manuscriptOriginRefreshedComponentLaw hn P b eta threshold hroute
        (ttc.t b n threshold z.2.2) z.1) := by
    have hcomp :=
      (measurable_manuscriptOriginRefreshedComponentLaw_intensity hn P b
        eta threshold hthreshold hroute).comp hpair
    simpa only [Function.comp_def] using hcomp
  exact measurable_parametric_probability_bind
    (fun _ : ManuscriptOriginConfiguration n => volumeLaw)
    measurable_const (fun _ => hvolume)
    (fun z : ManuscriptOriginConfiguration n × VolumeOutcome =>
      manuscriptOriginRefreshedComponentLaw hn P b eta threshold hroute
        (ttc.t b n threshold z.2.2) z.1) hnext

theorem measurable_manuscriptOriginRefreshedComponentLaw_outcome
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (c : ManuscriptOriginConfiguration n) :
    Measurable (fun outcome : VolumeOutcome =>
      manuscriptOriginRefreshedComponentLaw hn P b eta threshold hroute
        (ttc.t b n threshold outcome.2) c) := by
  have hpair : Measurable (fun outcome : VolumeOutcome =>
      (c, ttc.t b n threshold outcome.2)) := by
    apply measurable_const.prodMk
    unfold ttc.t
    exact (measurable_const.mul measurable_const).mul measurable_snd
  have hcomp :=
    (measurable_manuscriptOriginRefreshedComponentLaw_intensity hn P b
      eta threshold hthreshold hroute).comp hpair
  simpa only [Function.comp_def] using hcomp

theorem manuscriptOriginComponentVolumeLaw_isProbabilityMeasure
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (volumeLaw : Measure VolumeOutcome)
    (hvolume : IsProbabilityMeasure volumeLaw)
    (c : ManuscriptOriginConfiguration n) :
    IsProbabilityMeasure (manuscriptOriginComponentVolumeLaw hn P b eta
      threshold hroute volumeLaw c) := by
  letI : IsProbabilityMeasure volumeLaw := hvolume
  unfold manuscriptOriginComponentVolumeLaw
  exact isProbabilityMeasure_bind
    (measurable_manuscriptOriginRefreshedComponentLaw_outcome hn P b
      eta threshold hthreshold hroute c).aemeasurable
    (Filter.Eventually.of_forall (fun outcome =>
      manuscriptOriginRefreshedComponentLaw_isProbabilityMeasure hn P b
        eta threshold hthreshold hroute
        (ttc.t b n threshold outcome.2) c))

set_option maxHeartbeats 1000000 in
theorem manuscriptOriginComponentVolumeLaw_map_state
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (volumeLaw : Measure VolumeOutcome)
    (c : ManuscriptOriginConfiguration n) :
    (manuscriptOriginComponentVolumeLaw hn P b eta threshold hroute
      volumeLaw c).map
        (fun next : ManuscriptOriginConfiguration n => next.state) =
    volumeLaw.bind (fun outcome =>
      communityManuscriptComponentGivenVolume hn prep P b eta delta
        threshold outcome c.state) := by
  let K : VolumeOutcome → Measure (ManuscriptOriginConfiguration n) :=
    fun outcome => manuscriptOriginRefreshedComponentLaw hn P b eta
      threshold hroute (ttc.t b n threshold outcome.2) c
  have hK : Measurable K :=
    measurable_manuscriptOriginRefreshedComponentLaw_outcome hn P b eta
      threshold hthreshold hroute c
  change (volumeLaw.bind K).map
    (fun next : ManuscriptOriginConfiguration n => next.state) = _
  rw [map_bind_measure volumeLaw K
    (fun next : ManuscriptOriginConfiguration n => next.state)
    hK.aemeasurable measurable_manuscriptOriginConfiguration_state]
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro outcome
  exact manuscriptOriginRefreshedComponentLaw_map_state_eq_givenVolume
    hn prep P b eta delta threshold hthreshold hroute c outcome

noncomputable def communityManuscriptOriginComponentLaw
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (c : ManuscriptOriginConfiguration n) :
    Measure (ManuscriptOriginConfiguration n) :=
  manuscriptOriginComponentVolumeLaw hn P b eta threshold hroute
    ((communityManuscriptOracles hn prep).ComputeVolume P eta delta) c

theorem communityManuscriptOriginComponentLaw_map_state
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (c : ManuscriptOriginConfiguration n) :
    (communityManuscriptOriginComponentLaw hn prep P b eta delta
      threshold hroute c).map
        (fun next : ManuscriptOriginConfiguration n => next.state) =
    manuscriptProcessComponent (communityManuscriptOracles hn prep)
      b eta delta threshold P c.state := by
  unfold communityManuscriptOriginComponentLaw
  rw [manuscriptOriginComponentVolumeLaw_map_state hn prep P b eta delta
    threshold hthreshold hroute
    ((communityManuscriptOracles hn prep).ComputeVolume P eta delta) c]
  rfl

end Kr25Ssmxt
