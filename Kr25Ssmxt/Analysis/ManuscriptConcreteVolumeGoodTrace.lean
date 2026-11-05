import Kr25Ssmxt.Analysis.ManuscriptComponentsVolumeTrace
import Kr25Ssmxt.Analysis.ManuscriptVolumeOutcomeUnion

/-! The CV18 success event on the volume outcomes recorded by the actual
charged manuscript component fold. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem communityManuscriptComponentsVolumeTrace_good_accurate
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor b : Nat) (eta delta threshold budget : Real)
    (hthreshold : 0 < threshold)
    (components : List (PolytopeData n))
    (hvolume : ∀ P ∈ components, IsProbabilityMeasure
      ((communityManuscriptCostedOracles hn prep factor).computeVolumeWithCost
        P eta delta))
    (hfail : ∀ P ∈ components,
      ((communityManuscriptOracles hn prep).computeVolume P eta delta).real
        {o | o.1 = false} ≤ budget)
    (haccuracy : ∀ P ∈ components,
      ∀ᵐ o ∂(communityManuscriptOracles hn prep).computeVolume P eta delta,
        o.1 = true → (o.2 : Real) ∈ Arlib.relErr eta (volume P.carrier).toReal)
    (state : TTCState n) :
    (communityManuscriptComponentsVolumeTrace hn prep factor b eta delta
      threshold components state).real
      {z | ∀ i : Fin components.length,
        (z.1 i).1 = true ∧
          ((z.1 i).2 : Real) ∈
            Arlib.relErr eta (volume (components.get i).carrier).toReal} ≥
      1 - components.length * budget := by
  classical
  let law : Fin components.length → Measure VolumeOutcome :=
    fun i => (communityManuscriptOracles hn prep).computeVolume
      (components.get i) eta delta
  let good : Set (Fin components.length → VolumeOutcome) :=
    {outcomes | ∀ i : Fin components.length,
      (outcomes i).1 = true ∧
        ((outcomes i).2 : Real) ∈
          Arlib.relErr eta (volume (components.get i).carrier).toReal}
  have hgoodMeas : MeasurableSet good := by
    have heq : good = ⋂ i : Fin components.length,
        {outcomes : Fin components.length → VolumeOutcome |
          (outcomes i).1 = true ∧
            ((outcomes i).2 : Real) ∈
              Arlib.relErr eta (volume (components.get i).carrier).toReal} := by
      ext outcomes
      simp [good]
    rw [heq]
    apply MeasurableSet.iInter
    intro i
    simp only [Arlib.relErr]
    measurability
  have hpi := communityManuscriptComponentsVolumeTrace_volume_pi hn prep
    factor b eta delta threshold hthreshold components hvolume state
  have hprob (i : Fin components.length) : IsProbabilityMeasure (law i) := by
    letI : IsProbabilityMeasure
        ((communityManuscriptCostedOracles hn prep factor).computeVolumeWithCost
          (components.get i) eta delta) :=
      hvolume (components.get i) (List.get_mem components i)
    change IsProbabilityMeasure
      ((communityManuscriptOracles hn prep).computeVolume
        (components.get i) eta delta)
    rw [← communityManuscriptCosted_volume_fst hn prep factor
      (components.get i) eta delta]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hprod := manuscript_independent_volume_outcomes_good_accurate
    components.length law (fun _ => budget)
    (fun i => (volume (components.get i).carrier).toReal) eta hprob
    (fun i => hfail (components.get i) (List.get_mem components i))
    (fun i => haccuracy (components.get i) (List.get_mem components i))
  have hsum : (∑ _i : Fin components.length, budget) =
      components.length * budget := by simp
  have hmap :
      (communityManuscriptComponentsVolumeTrace hn prep factor b eta delta
        threshold components state).real (Prod.fst ⁻¹' good) =
        (Measure.pi law).real good := by
    unfold Measure.real
    rw [← Measure.map_apply measurable_fst hgoodMeas]
    rw [hpi]
  change (communityManuscriptComponentsVolumeTrace hn prep factor b eta delta
    threshold components state).real (Prod.fst ⁻¹' good) ≥ _
  rw [hmap]
  simpa only [hsum] using hprod

/-- The concrete TTC component trace spends at most `δ/4` on inaccurate or
failed CV18 outcomes, with no extra oracle premise. -/
theorem communityManuscript_components_volume_trace_good_accurate
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (factor : Nat)
    (hcomponents : 0 < (prep.run F hbounded).componentCount) :
    let D := prep.run F hbounded
    let b := (prep.choosePrecision D p).value
    let components := List.ofFn D.component
    (communityManuscriptComponentsVolumeTrace hn prep factor b p.epsilonPrime
      (p.deltaPrime D.componentCount) (p.threshold D.componentCount)
      components (TTCState.initial n)).real
      {z | ∀ i : Fin components.length,
        (z.1 i).1 = true ∧
          ((z.1 i).2 : Real) ∈ Arlib.relErr p.epsilonPrime
            (volume (components.get i).carrier).toReal} ≥
      1 - p.delta / 4 := by
  dsimp only
  let D := prep.run F hbounded
  let b := (prep.choosePrecision D p).value
  let components : List (PolytopeData n) := List.ofFn D.component
  have hvolume : ∀ P ∈ components, IsProbabilityMeasure
      ((communityManuscriptCostedOracles hn prep factor).computeVolumeWithCost
        P p.epsilonPrime (p.deltaPrime D.componentCount)) := by
    intro P hP
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hP
    exact community_manuscript_costed_volume_isProbabilityMeasure hn D p prep
      factor i
  have hcontract := community_manuscript_volume_contract hn prep F hbounded p
  have hfail : ∀ P ∈ components,
      ((communityManuscriptOracles hn prep).computeVolume P p.epsilonPrime
        (p.deltaPrime D.componentCount)).real {o | o.1 = false} ≤
          p.deltaPrime D.componentCount := by
    intro P hP
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hP
    exact (hcontract i).2.1
  have haccuracy : ∀ P ∈ components,
      ∀ᵐ o ∂(communityManuscriptOracles hn prep).computeVolume P p.epsilonPrime
        (p.deltaPrime D.componentCount),
        o.1 = true →
          (o.2 : Real) ∈ Arlib.relErr p.epsilonPrime (volume P.carrier).toReal := by
    intro P hP
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hP
    exact (hcontract i).2.2
  have htrace := communityManuscriptComponentsVolumeTrace_good_accurate
    hn prep factor b p.epsilonPrime (p.deltaPrime D.componentCount)
    (p.threshold D.componentCount) (p.deltaPrime D.componentCount)
    (p.threshold_pos D.componentCount) components hvolume hfail haccuracy
    (TTCState.initial n)
  have hbudget : (components.length : Real) *
      p.deltaPrime D.componentCount = p.delta / 4 := by
    have hm : (D.componentCount : Real) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hcomponents)
    simp only [components, List.length_ofFn, ApproxParams.deltaPrime]
    field_simp
  simpa only [hbudget] using htrace

end Kr25Ssmxt
