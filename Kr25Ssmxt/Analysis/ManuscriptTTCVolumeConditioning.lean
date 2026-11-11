import Kr25Ssmxt.Analysis.PrecisionChoice
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
    let threshold := p.Thresh D.componentCount
    let components := List.ofFn D.component
    ttc hn F hbounded p prep =
      (communityManuscriptVolumeVectorLaw hn prep p.ε'
        (p.δ' D.componentCount) components).bind fun outcomes =>
          (communityManuscriptComponentsGivenVolumes hn prep b
            p.ε' (p.δ' D.componentCount) threshold
            components outcomes (TTCState.initial n)).map
              (Est b threshold) := by
  dsimp only
  let D := prep.run F hbounded
  let b := (prep.choosePrecision D p).value
  let threshold := p.Thresh D.componentCount
  let components := List.ofFn D.component
  have hvolume : ∀ P ∈ components, IsProbabilityMeasure
      ((ttcSubroutines hn prep).ComputeVolume P p.ε'
        (p.δ' D.componentCount)) := by
    intro P hP
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hP
    exact ((community_manuscript_volume_contract hn prep F hbounded p) i).1
  have hrun : ttc hn F hbounded p prep =
      (ttcPseudocode.loop (ttcSubroutines hn prep)
        b p.ε' (p.δ' D.componentCount) threshold
        components (TTCState.initial n)).map
          (Est b threshold) := by
    simp [ttc, ttcPseudocode,
      ttcSubroutines, TTCPreprocessor.choosePrecision, D, b, threshold,
      components, hnonempty]
  let law := communityManuscriptVolumeVectorLaw hn prep p.ε'
    (p.δ' D.componentCount) components
  let K : (Fin components.length → VolumeOutcome) → Measure (TTCState n) :=
    fun outcomes => communityManuscriptComponentsGivenVolumes hn prep b
      p.ε' (p.δ' D.componentCount) threshold components
      outcomes (TTCState.initial n)
  have hK : Measurable K := by
    have hcoords : Measurable
        (fun outcomes : Fin components.length → VolumeOutcome =>
          (outcomes, TTCState.initial n)) :=
      measurable_id.prodMk measurable_const
    have h := (measurable_communityManuscriptComponentsGivenVolumes
      hn prep b p.ε' (p.δ' D.componentCount) threshold
      (p.threshold_pos D.componentCount) components).comp hcoords
    exact h
  rw [hrun, communityManuscriptProcessComponents_eq_volumeVector_bind
    hn prep b p.ε' (p.δ' D.componentCount) threshold
    (p.threshold_pos D.componentCount) components hvolume
    (TTCState.initial n)]
  exact map_bind_measure law K (Est b threshold)
    hK.aemeasurable (measurable_manuscriptEstimate b threshold)

end Kr25Ssmxt
