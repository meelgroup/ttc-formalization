import Kr25Ssmxt.Analysis.PrecisionChoice
import Kr25Ssmxt.Analysis.MathlibCompat
import Kr25Ssmxt.Analysis.ManuscriptRunMarginal
import Kr25Ssmxt.Analysis.ManuscriptOracleNormalization

/-! The concrete manuscript TTC run has total probability one, independently
of its accuracy analysis. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem community_manuscriptTTC_isProbabilityMeasure
    {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k) :
    IsProbabilityMeasure (ttc hn F hbounded p prep) := by
  let D := prep.run F hbounded
  by_cases hempty : D.componentCount = 0
  · simp [ttc, ttcPseudocode,
      ttcSubroutines, D, hempty]
    infer_instance
  · let b := (prep.choosePrecision D p).value
    let threshold := p.Thresh D.componentCount
    let components := List.ofFn D.component
    have hvolume : ∀ P ∈ components,
        IsProbabilityMeasure
          ((ttcCostedSubroutines hn prep 1).computeVolumeWithCost
            P p.ε' (p.δ' D.componentCount)) := by
      intro P hP
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hP
      exact community_manuscript_costed_volume_isProbabilityMeasure
        hn D p prep 1 i
    let core := ttcPseudocode.loopWithCost
      (ttcCostedSubroutines hn prep 1) b p.ε'
      (p.δ' D.componentCount) threshold components (TTCState.initial n)
    letI : IsProbabilityMeasure core :=
      ⟨community_manuscript_components_mass_one hn prep 1 b p.ε'
        (p.δ' D.componentCount) threshold (p.threshold_pos D.componentCount)
        components hvolume (TTCState.initial n)⟩
    have hvolumeMass : ∀ P ∈ components,
        ((ttcCostedSubroutines hn prep 1).computeVolumeWithCost
          P p.ε' (p.δ' D.componentCount)) Set.univ ≤ 1 := by
      intro P hP
      letI := hvolume P hP
      simp
    have hcoreEq := community_manuscript_components_fst hn prep 1 b
      p.ε' (p.δ' D.componentCount) threshold
      (p.threshold_pos D.componentCount) components hvolumeMass
      (TTCState.initial n)
    have hcore : IsProbabilityMeasure
        (ttcPseudocode.loop (ttcSubroutines hn prep)
          b p.ε' (p.δ' D.componentCount) threshold
          components (TTCState.initial n)) := by
      rw [← hcoreEq]
      exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    have hprep : (ttcSubroutines hn prep).preprocessing = prep := rfl
    have hempty' :
        ((ttcSubroutines hn prep).preprocessing.run F hbounded).componentCount
          ≠ 0 := by simpa only [hprep, D] using hempty
    have hrunequality : ttc hn F hbounded p prep =
        (ttcPseudocode.loop (ttcSubroutines hn prep)
          b p.ε' (p.δ' D.componentCount) threshold
          components (TTCState.initial n)).map
            (Est b threshold) := by
      simp [ttc, ttcPseudocode, ttcSubroutines,
        TTCPreprocessor.choosePrecision, D, b, threshold, components, hempty]
    rw [hrunequality]
    letI := hcore
    exact Measure.isProbabilityMeasure_map
      (measurable_manuscriptEstimate b threshold).aemeasurable

#print axioms community_manuscriptTTC_isProbabilityMeasure

end Kr25Ssmxt
