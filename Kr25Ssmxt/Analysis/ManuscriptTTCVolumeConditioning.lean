import Kr25Ssmxt.Analysis.ManuscriptGivenVolumeFold
import Kr25Ssmxt.Analysis.ManuscriptVolumeGeometry
import Kr25Ssmxt.Analysis.ManuscriptRunMarginal

/-! The manuscript TTC output distribution conditioned on the complete
independent vector of clipped CV18 volume outcomes. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem communityManuscriptTTC_eq_volumeVector_bind
    {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (hnonempty : (prep.run F hbounded).componentCount ≠ 0) :
    let D := prep.run F hbounded
    let b := (prep.choosePrecision D p).value
    let threshold := p.threshold D.componentCount
    let components := List.ofFn D.component
    communityManuscriptTTC hn F hbounded p prep =
      (communityManuscriptVolumeVectorLaw hn prep p.epsilonPrime
        (p.deltaPrime D.componentCount) components).bind fun outcomes =>
          (communityManuscriptComponentsGivenVolumes hn prep b
            p.epsilonPrime (p.deltaPrime D.componentCount) threshold
            components outcomes (TTCState.initial n)).map
              (manuscriptEstimate b threshold) := by
  dsimp only
  let D := prep.run F hbounded
  let b := (prep.choosePrecision D p).value
  let threshold := p.threshold D.componentCount
  let components := List.ofFn D.component
  have hvolume : ∀ P ∈ components, IsProbabilityMeasure
      ((communityManuscriptOracles hn prep).computeVolume P p.epsilonPrime
        (p.deltaPrime D.componentCount)) := by
    intro P hP
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hP
    exact ((community_manuscript_volume_contract hn prep F hbounded p) i).1
  have hrun : communityManuscriptTTC hn F hbounded p prep =
      (manuscriptProcessComponents (communityManuscriptOracles hn prep)
        b p.epsilonPrime (p.deltaPrime D.componentCount) threshold
        components (TTCState.initial n)).map
          (manuscriptEstimate b threshold) := by
    simp [communityManuscriptTTC, manuscriptTTC,
      communityManuscriptOracles, communityCV18HitAndRunOracles,
      hitAndRunSamplingOracles, D, b, threshold, components, hnonempty]
  let law := communityManuscriptVolumeVectorLaw hn prep p.epsilonPrime
    (p.deltaPrime D.componentCount) components
  let K : (Fin components.length → VolumeOutcome) → Measure (TTCState n) :=
    fun outcomes => communityManuscriptComponentsGivenVolumes hn prep b
      p.epsilonPrime (p.deltaPrime D.componentCount) threshold components
      outcomes (TTCState.initial n)
  have hK : Measurable K := by
    have hcoords : Measurable
        (fun outcomes : Fin components.length → VolumeOutcome =>
          (outcomes, TTCState.initial n)) :=
      measurable_id.prodMk measurable_const
    have h := (measurable_communityManuscriptComponentsGivenVolumes
      hn prep b p.epsilonPrime (p.deltaPrime D.componentCount) threshold
      (p.threshold_pos D.componentCount) components).comp hcoords
    exact h
  rw [hrun, communityManuscriptProcessComponents_eq_volumeVector_bind
    hn prep b p.epsilonPrime (p.deltaPrime D.componentCount) threshold
    (p.threshold_pos D.componentCount) components hvolume
    (TTCState.initial n)]
  exact map_bind_measure law K (manuscriptEstimate b threshold)
    hK.aemeasurable (measurable_manuscriptEstimate b threshold)

end Kr25Ssmxt
