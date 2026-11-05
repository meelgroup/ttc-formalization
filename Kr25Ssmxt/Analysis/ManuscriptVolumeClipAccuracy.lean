import Kr25Ssmxt.Analysis.MathlibCompat
import Kr25Ssmxt.Analysis.ManuscriptComponentExpectation

/-! Clipping a volume outcome to geometric bounds preserves its relative
accuracy whenever the true volume lies between those bounds. -/

namespace Kr25Ssmxt

theorem manuscript_volume_clip_preserves_relErr
    (estimate lower upper trueVolume eta : Real)
    (htrue : 0 ≤ trueVolume) (heta : 0 ≤ eta)
    (hlower : lower ≤ trueVolume) (hupper : trueVolume ≤ upper)
    (hestimate : estimate ∈ Arlib.relErr eta trueVolume) :
    max lower (min upper estimate) ∈ Arlib.relErr eta trueVolume := by
  have hinside : (1 - eta) * trueVolume ≤ trueVolume := by
    nlinarith
  have houtside : trueVolume ≤ (1 + eta) * trueVolume := by
    nlinarith
  change (1 - eta) * trueVolume ≤ max lower (min upper estimate) ∧
    max lower (min upper estimate) ≤ (1 + eta) * trueVolume
  change (1 - eta) * trueVolume ≤ estimate ∧
    estimate ≤ (1 + eta) * trueVolume at hestimate
  constructor
  · exact (le_min (hinside.trans hupper) hestimate.1).trans (le_max_right _ _)
  · exact max_le (hlower.trans houtside)
      ((min_le_right _ _).trans hestimate.2)

open MeasureTheory

theorem PolytopeData.clipManuscriptVolumeLaw_spec {n : Nat}
    (P : PolytopeData n) (mu : Measure VolumeOutcome)
    [IsProbabilityMeasure mu] (eta delta : Real) (heta : 0 ≤ eta)
    (hlower : (P.manuscriptVolumeLower eta : Real) ≤
      (volume P.carrier).toReal)
    (hupper : (volume P.carrier).toReal ≤
      (P.manuscriptVolumeUpper eta : Real))
    (hfail : mu.real {o | o.1 = false} ≤ delta)
    (hacc : ∀ᵐ o ∂mu, o.1 = true →
      (o.2 : Real) ∈ Arlib.relErr eta (volume P.carrier).toReal) :
    IsProbabilityMeasure (mu.map (P.clipManuscriptVolume eta)) ∧
      (mu.map (P.clipManuscriptVolume eta)).real {o | o.1 = false} ≤ delta ∧
      ∀ᵐ o ∂mu.map (P.clipManuscriptVolume eta), o.1 = true →
        (o.2 : Real) ∈ Arlib.relErr eta (volume P.carrier).toReal := by
  have hmap : Measurable (P.clipManuscriptVolume eta) :=
    P.measurable_clipManuscriptVolume eta
  refine ⟨Measure.isProbabilityMeasure_map hmap.aemeasurable, ?_, ?_⟩
  · rw [Measure.real, Measure.map_apply hmap (by measurability)]
    simpa [Measure.real, PolytopeData.clipManuscriptVolume] using hfail
  · rw [ae_map_iff hmap.aemeasurable (by measurability)]
    filter_upwards [hacc] with o ho
    intro htag
    have htrue : 0 ≤ (volume P.carrier).toReal := ENNReal.toReal_nonneg
    have hraw := ho htag
    change ((max (P.manuscriptVolumeLower eta)
      (min (P.manuscriptVolumeUpper eta) o.2) : NNReal) : Real) ∈
        Arlib.relErr eta (volume P.carrier).toReal
    simpa only [NNReal.coe_max, NNReal.coe_min] using
      (manuscript_volume_clip_preserves_relErr _ _ _ _ _
        htrue heta hlower hupper hraw)

theorem community_manuscript_volume_contract_of_bounds
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F)) (p : ApproxParams)
    (hbounds :
      let D := prep.run F hbounded
      ∀ i : Fin D.componentCount,
        ((D.component i).manuscriptVolumeLower p.epsilonPrime : Real) ≤
          (volume (D.component i).carrier).toReal ∧
        (volume (D.component i).carrier).toReal ≤
          ((D.component i).manuscriptVolumeUpper p.epsilonPrime : Real)) :
    ComputeVolumeContract (communityManuscriptOracles hn prep)
      F hbounded p := by
  let D := prep.run F hbounded
  intro i
  have hn3 : 3 ≤ n := by omega
  have hspec := CommunityCV18.communityCV18VolumeLaw_spec
    hn3 (D.component i) p.epsilonPrime
    (p.deltaPrime D.componentCount)
    (PaperRuntime.ttc_request_admissible D p i)
  letI : IsProbabilityMeasure
      (communityCV18VolumeLaw hn3 (D.component i) p.epsilonPrime
        (p.deltaPrime D.componentCount)) := hspec.1
  have hclip := (D.component i).clipManuscriptVolumeLaw_spec
    (communityCV18VolumeLaw hn3 (D.component i) p.epsilonPrime
      (p.deltaPrime D.componentCount))
    p.epsilonPrime (p.deltaPrime D.componentCount)
    (div_nonneg p.epsilon_pos.le (by norm_num))
    (hbounds i).1 (hbounds i).2 hspec.2.1 hspec.2.2
  simpa only [communityManuscriptOracles, communityCV18HitAndRunOracles,
    hitAndRunSamplingOracles, D] using hclip

end Kr25Ssmxt
