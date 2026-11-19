import ttc.Analysis.PrecisionChoice
import ttc.Analysis.ComponentExpectation
import ttc.Analysis.SampleAppendMarginal

namespace ttc

open MeasureTheory

theorem measurable_estimate {n : Nat} (b : Nat)
    (threshold : Real) :
    Measurable (EstReference (n := n) b threshold) := by
  have hcoords : Measurable (fun s : TTCState n =>
      (s.p, s.X, s.nextLabel)) := comap_measurable _
  have hrate : Measurable (fun s : TTCState n => s.p) :=
    measurable_fst.comp hcoords
  have hsamples : Measurable (fun s : TTCState n => s.X) :=
    (measurable_fst.comp measurable_snd).comp hcoords
  have hcount : Measurable (fun s : TTCState n =>
      (s.X.card : NNReal)) :=
    (measurable_of_countable (fun copies : Finset (SampleCopy n) =>
      (copies.card : NNReal))).comp hsamples
  unfold EstReference
  exact hcount.div ((hrate.mul_const _).mul_const _)

/-- Forgetting arithmetic-operation charges recovers exactly the paper
TTC output distribution. -/
theorem community_costed_output_fst {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations factor : Nat) :
    (ttcRefWithCost hn F hbounded p prep
      preprocessingOperations factor).map Prod.fst =
      ttcRef hn F hbounded p prep := by
  let D := prep.run F hbounded
  have hprep : (ttcSubroutines hn prep).preprocessing = prep := rfl
  by_cases hempty : D.componentCount = 0
  · have hempty' :
        ((ttcSubroutines hn prep).preprocessing.run F hbounded).componentCount
          = 0 := by simpa only [hprep, D] using hempty
    simp [ttcRefWithCost, ttcRef,
      ttcReferenceWithCost, ttcReference, ttcCostedSubroutines,
      hempty']
  · let b := (prep.choosePrecision D p).value
    let threshold := p.Thresh D.componentCount
    have hvolume : ∀ P ∈ List.ofFn D.component,
        ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
          P p.ε' (p.δ' D.componentCount)) Set.univ ≤ 1 := by
      intro P hP
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hP
      apply costedCharge_mass_le_one
      dsimp only [ttcSubroutines]
      exact certified_community_volume_mass_le_one hn D p i
    have hseq := community_components_fst hn prep factor b
      p.ε' (p.δ' D.componentCount) threshold
      (p.threshold_pos D.componentCount) (List.ofFn D.component) hvolume
      (TTCState.unitInitial n)
    have hempty' :
        ((ttcSubroutines hn prep).preprocessing.run F hbounded).componentCount
          ≠ 0 := by simpa only [hprep, D] using hempty
    simp only [ttcRefWithCost, ttcRef,
      ttcReferenceWithCost, ttcReference, ttcCostedSubroutines,
      if_neg hempty']
    simp only [hempty', ↓reduceIte]
    change ((ttcReference.loopWithCost
      (ttcCostedSubroutines hn prep factor)
      b p.ε' (p.δ' D.componentCount) threshold
      (List.ofFn D.component) (TTCState.unitInitial n)).map
        (fun result => (EstReference b threshold result.1,
          preprocessingOperations + result.2))).map Prod.fst =
      (ttcReference.loop (ttcSubroutines hn prep)
        b p.ε' (p.δ' D.componentCount) threshold
        (List.ofFn D.component) (TTCState.unitInitial n)).map
          (EstReference b threshold)
    have hestimate : Measurable (EstReference (n := n) b threshold) :=
      measurable_estimate (n := n) b threshold
    have houtput : Measurable (fun result : TTCState n × Nat =>
        (EstReference b threshold result.1,
          preprocessingOperations + result.2)) :=
      (hestimate.comp measurable_fst).prodMk
        (measurable_const.add measurable_snd)
    rw [Measure.map_map measurable_fst houtput]
    change (ttcReference.loopWithCost
      (ttcCostedSubroutines hn prep factor)
      b p.ε' (p.δ' D.componentCount) threshold
      (List.ofFn D.component) (TTCState.unitInitial n)).map
        (EstReference b threshold ∘ Prod.fst) = _
    rw [← Measure.map_map hestimate measurable_fst]
    simpa only [Function.comp_def] using
      congrArg (fun law : Measure (TTCState n) =>
        law.map (EstReference b threshold)) hseq


end ttc
