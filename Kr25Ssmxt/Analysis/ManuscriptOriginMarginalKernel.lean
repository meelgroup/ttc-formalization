import Kr25Ssmxt.Analysis.ManuscriptOriginMeasurable
import Kr25Ssmxt.Analysis.ManuscriptGivenVolumeFold

/-! The one-component source transition remains correct after averaging over
an arbitrary distribution of incoming ghost configurations. -/

namespace Kr25Ssmxt

open MeasureTheory

noncomputable def communityManuscriptGhostStateStep
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (c : ManuscriptOriginConfiguration n) : Measure (TTCState n) :=
  ((communityManuscriptOracles hn prep).ComputeVolume P eta delta).bind
    (fun outcome =>
      let intensity := ttc.t b n threshold outcome.2
      let pointLaw := normalizedHitAndRunPointLaw hn P b hroute.1 eta
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

theorem communityManuscriptGhostStateStep_eq_program
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (c : ManuscriptOriginConfiguration n) :
    communityManuscriptGhostStateStep hn prep P b eta delta threshold
      hroute c =
    manuscriptProcessComponent (communityManuscriptOracles hn prep)
      b eta delta threshold P c.state :=
  c.refreshFuture_programComponent_law hn prep P b eta delta threshold
    hroute

theorem measurable_communityManuscript_programComponent
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hthreshold : 0 < threshold)
    (hvolume : IsProbabilityMeasure
      ((communityManuscriptOracles hn prep).ComputeVolume P eta delta)) :
    Measurable (manuscriptProcessComponent
      (communityManuscriptOracles hn prep) b eta delta threshold P) := by
  let volumeLaw := (communityManuscriptOracles hn prep).ComputeVolume
    P eta delta
  have hbase := measurable_parametric_probability_bind
    (fun _ : TTCState n => volumeLaw) measurable_const
    (fun _ => hvolume)
    (fun z : TTCState n × VolumeOutcome =>
      communityManuscriptComponentGivenVolume hn prep P b eta delta
        threshold z.2 z.1)
    (measurable_communityManuscriptComponentGivenVolume hn prep P b
      eta delta threshold hthreshold)
  change Measurable (fun state : TTCState n =>
    volumeLaw.bind fun outcome =>
      communityManuscriptComponentGivenVolume hn prep P b eta delta
        threshold outcome state)
  exact hbase

/-- State projection commutes with an arbitrary incoming ghost law for a
single concrete manuscript component. -/
theorem communityManuscriptGhostStateStep_bind_eq_program
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (hthreshold : 0 < threshold)
    (hvolume : IsProbabilityMeasure
      ((communityManuscriptOracles hn prep).ComputeVolume P eta delta))
    (μ : Measure (ManuscriptOriginConfiguration n)) :
    μ.bind (communityManuscriptGhostStateStep hn prep P b eta delta
      threshold hroute) =
    (μ.map (fun c => c.state)).bind
      (manuscriptProcessComponent (communityManuscriptOracles hn prep)
        b eta delta threshold P) := by
  let program := manuscriptProcessComponent (communityManuscriptOracles hn prep)
    b eta delta threshold P
  have hprogram : Measurable program :=
    measurable_communityManuscript_programComponent hn prep P b eta delta
      threshold hthreshold hvolume
  calc
    μ.bind (communityManuscriptGhostStateStep hn prep P b eta delta
        threshold hroute) = μ.bind (fun c => program c.state) := by
          exact Measure.bind_congr_right (Filter.Eventually.of_forall
            (fun c => communityManuscriptGhostStateStep_eq_program
              hn prep P b eta delta threshold hroute c))
    _ = (μ.map (fun c => c.state)).bind program := by
          exact (bind_mapped_measure μ (fun c => c.state)
            measurable_manuscriptOriginConfiguration_state
            program hprogram).symm

end Kr25Ssmxt
