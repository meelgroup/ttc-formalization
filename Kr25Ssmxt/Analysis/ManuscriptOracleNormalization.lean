import Kr25Ssmxt.Analysis.ManuscriptComponentExpectation
import Kr25Ssmxt.Analysis.HitAndRunSamplingOracle

/-! Normalization of the two concrete oracle laws used by manuscript TTC. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem community_manuscript_volume_isProbabilityMeasure
    {n k : Nat} (hn : 21 ≤ n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (prep : TTCPreprocessor n k)
    (i : Fin D.componentCount) :
    IsProbabilityMeasure
      ((communityManuscriptOracles hn prep).computeVolume
        (D.component i) p.epsilonPrime (p.deltaPrime D.componentCount)) := by
  letI : IsProbabilityMeasure
      (communityCV18VolumeLaw (by omega) (D.component i) p.epsilonPrime
        (p.deltaPrime D.componentCount)) :=
    (CommunityCV18.communityCV18VolumeLaw_spec (by omega) (D.component i)
      p.epsilonPrime (p.deltaPrime D.componentCount)
      (PaperRuntime.ttc_request_admissible D p i)).1
  change IsProbabilityMeasure
    ((communityCV18VolumeLaw (by omega) (D.component i) p.epsilonPrime
      (p.deltaPrime D.componentCount)).map
      ((D.component i).clipManuscriptVolume p.epsilonPrime))
  exact Measure.isProbabilityMeasure_map
    ((D.component i).measurable_clipManuscriptVolume p.epsilonPrime).aemeasurable

theorem community_manuscript_samples_isProbabilityMeasure
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (count b : Nat) (eta delta : Real) :
    IsProbabilityMeasure
      ((communityManuscriptOracles hn prep).generateSamples
        P count b eta delta) := by
  classical
  by_cases h : 1 ≤ decimalScale b * P.inradius ∧ 0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧ (codedLatticePoints P b).Nonempty
  · have hpoint := P.normalizedHitAndRun_latticePointLaw hn b h.1
      h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
    letI : IsProbabilityMeasure
        (normalizedHitAndRunPointLaw hn P b h.1 eta
          h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2) := hpoint.1
    simpa only [communityManuscriptOracles, dif_pos h] using
      (iidSampleBatchLaw_isProbabilityMeasure
        (normalizedHitAndRunPointLaw hn P b h.1 eta
          h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2))
  · simp only [communityManuscriptOracles, dif_neg h]
    unfold failedSampleBatchLaw
    infer_instance

theorem community_manuscript_costed_volume_isProbabilityMeasure
    {n k : Nat} (hn : 21 ≤ n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (prep : TTCPreprocessor n k)
    (factor : Nat) (i : Fin D.componentCount) :
    IsProbabilityMeasure
      ((communityManuscriptCostedOracles hn prep factor).computeVolumeWithCost
        (D.component i) p.epsilonPrime (p.deltaPrime D.componentCount)) := by
  apply costed_probability_of_fst
  rw [communityManuscriptCosted_volume_fst]
  exact community_manuscript_volume_isProbabilityMeasure hn D p prep i

theorem community_manuscript_costed_samples_isProbabilityMeasure
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (count b : Nat)
    (eta delta : Real) :
    IsProbabilityMeasure
      ((communityManuscriptCostedOracles hn prep factor).generateSamplesWithCost
        P count b eta delta) := by
  apply costed_probability_of_fst
  rw [communityManuscriptCosted_samples_fst]
  exact community_manuscript_samples_isProbabilityMeasure hn prep P count b eta delta

end Kr25Ssmxt
