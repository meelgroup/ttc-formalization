import Kr25Ssmxt.Analysis.OriginMeasurable
import Kr25Ssmxt.Analysis.GivenVolumeFold

/-! The one-component source transition remains correct after averaging over
an arbitrary distribution of incoming ghost configurations. -/

namespace Kr25Ssmxt

open MeasureTheory

noncomputable def communityGhostStateStep
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (c : OriginConfiguration n) : Measure (TTCState n) :=
  ((ttcSubroutines hn prep).ComputeVolume P eta delta).bind
    (fun outcome =>
      let intensity := ttcReference.t b n threshold outcome.2
      let pointLaw := normalizedHitAndRunPointLaw hn P b eta hroute.1
        hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
      (ProbabilityTheory.poissonMeasure intensity).bind
        (fun basePending =>
          fairCoinStreamLaw.bind (fun preCoins =>
            ((Measure.infinitePi
              (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
              fairCoinStreamLaw).bind (fun pair =>
                (Measure.infinitePi (fun _ : Nat => pointLaw)).map
                  (fun tape =>
                    ((c.refreshFuture pair.1).advance P intensity threshold
                      basePending preCoins pair.2 tape).state)))))

theorem communityGhostStateStep_eq_program
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (c : OriginConfiguration n) :
    communityGhostStateStep hn prep P b eta delta threshold
      hroute c =
    ttcReference.step (ttcSubroutines hn prep)
      b eta delta threshold P c.state :=
  c.refreshFuture_programComponent_law hn prep P b eta delta threshold
    hroute

theorem measurable_community_programComponent
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hthreshold : 0 < threshold)
    (hvolume : IsProbabilityMeasure
      ((ttcSubroutines hn prep).ComputeVolume P eta delta)) :
    Measurable (ttcReference.step
      (ttcSubroutines hn prep) b eta delta threshold P) := by
  let volumeLaw := (ttcSubroutines hn prep).ComputeVolume
    P eta delta
  have hbase := measurable_parametric_probability_bind
    (fun _ : TTCState n => volumeLaw) measurable_const
    (fun _ => hvolume)
    (fun z : TTCState n × VolumeOutcome =>
      communityComponentGivenVolume hn prep P b eta delta
        threshold z.2 z.1)
    (measurable_communityComponentGivenVolume hn prep P b
      eta delta threshold hthreshold)
  change Measurable (fun state : TTCState n =>
    volumeLaw.bind fun outcome =>
      communityComponentGivenVolume hn prep P b eta delta
        threshold outcome state)
  exact hbase

/-- State projection commutes with an arbitrary incoming ghost law for a
single concrete paper component. -/
theorem communityGhostStateStep_bind_eq_program
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (hthreshold : 0 < threshold)
    (hvolume : IsProbabilityMeasure
      ((ttcSubroutines hn prep).ComputeVolume P eta delta))
    (μ : Measure (OriginConfiguration n)) :
    μ.bind (communityGhostStateStep hn prep P b eta delta
      threshold hroute) =
    (μ.map (fun c => c.state)).bind
      (ttcReference.step (ttcSubroutines hn prep)
        b eta delta threshold P) := by
  let program := ttcReference.step (ttcSubroutines hn prep)
    b eta delta threshold P
  have hprogram : Measurable program :=
    measurable_community_programComponent hn prep P b eta delta
      threshold hthreshold hvolume
  calc
    μ.bind (communityGhostStateStep hn prep P b eta delta
        threshold hroute) = μ.bind (fun c => program c.state) := by
          exact Measure.bind_congr_right (Filter.Eventually.of_forall
            (fun c => communityGhostStateStep_eq_program
              hn prep P b eta delta threshold hroute c))
    _ = (μ.map (fun c => c.state)).bind program := by
          exact (bind_mapped_measure μ (fun c => c.state)
            measurable_originConfiguration_state
            program hprogram).symm

end Kr25Ssmxt
