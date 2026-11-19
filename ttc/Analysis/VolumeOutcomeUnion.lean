import ttc.Analysis.VolumeGeometry

/-! The independent CV18 component calls spend their combined failure budget
before the adaptive TTC state is considered. -/

namespace ttc

open MeasureTheory

theorem independent_volume_outcomes_good
    (m : Nat) (law : Fin m → Measure VolumeOutcome)
    (budget : Fin m → Real)
    (hprob : ∀ i, IsProbabilityMeasure (law i))
    (hfail : ∀ i, (law i).real {o | o.1 = false} ≤ budget i) :
    (Measure.pi law).real
      {outcomes | ∀ i : Fin m, (outcomes i).1 = true} ≥
      1 - ∑ i, budget i := by
  classical
  letI : ∀ i, IsProbabilityMeasure (law i) := hprob
  letI : IsProbabilityMeasure (Measure.pi law) := inferInstance
  let good : Set (Fin m → VolumeOutcome) :=
    {outcomes | ∀ i : Fin m, (outcomes i).1 = true}
  let bad : Fin m → Set (Fin m → VolumeOutcome) :=
    fun i => {outcomes | (outcomes i).1 = false}
  have hcompl : goodᶜ = ⋃ i, bad i := by
    ext outcomes
    simp only [good, bad, Set.mem_compl_iff, Set.mem_setOf_eq,
      Set.mem_iUnion, not_forall]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, by cases h : (outcomes i).1 <;> simp_all⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, by simpa [hi]⟩
  have hmeas : MeasurableSet good := by
    have heq : good = ⋂ i : Fin m,
        {outcomes : Fin m → VolumeOutcome | (outcomes i).1 = true} := by
      ext outcomes
      simp [good]
    rw [heq]
    exact MeasurableSet.iInter fun i => by measurability
  have hmarg (i : Fin m) :
      (Measure.pi law).real (bad i) =
        (law i).real {o | o.1 = false} := by
    unfold Measure.real
    change ((Measure.pi law) ((Function.eval i) ⁻¹'
      {o : VolumeOutcome | o.1 = false})).toReal = _
    rw [← Measure.map_apply (measurable_pi_apply i) (by measurability)]
    rw [Measure.pi_map_eval]
    simp
  have hsum : (Measure.pi law).real (⋃ i, bad i) ≤
      ∑ i, budget i := by
    calc
      (Measure.pi law).real (⋃ i, bad i) ≤
          ∑ i, (Measure.pi law).real (bad i) :=
        measureReal_iUnion_fintype_le bad
      _ ≤ ∑ i, budget i := by
        apply Finset.sum_le_sum
        intro i hi
        rw [hmarg]
        exact hfail i
  have hprobGood : (Measure.pi law).real good =
      1 - (Measure.pi law).real (⋃ i, bad i) := by
    rw [← hcompl, probReal_compl_eq_one_sub hmeas]
    ring
  simpa only [good, hprobGood] using sub_le_sub_left hsum 1

theorem independent_volume_outcomes_good_accurate
    (m : Nat) (law : Fin m → Measure VolumeOutcome)
    (budget target : Fin m → Real) (eta : Real)
    (hprob : ∀ i, IsProbabilityMeasure (law i))
    (hfail : ∀ i, (law i).real {o | o.1 = false} ≤ budget i)
    (haccuracy : ∀ i, ∀ᵐ o ∂law i, o.1 = true →
      (o.2 : Real) ∈ Arlib.relErr eta (target i)) :
    (Measure.pi law).real
      {outcomes | ∀ i : Fin m,
        (outcomes i).1 = true ∧
          ((outcomes i).2 : Real) ∈ Arlib.relErr eta (target i)} ≥
      1 - ∑ i, budget i := by
  letI : ∀ i, IsProbabilityMeasure (law i) := hprob
  letI : IsProbabilityMeasure (Measure.pi law) := inferInstance
  have hgood := independent_volume_outcomes_good m law budget
    hprob hfail
  have hae : ∀ᵐ outcomes ∂Measure.pi law,
      ∀ i : Fin m, (outcomes i).1 = true →
        ((outcomes i).2 : Real) ∈ Arlib.relErr eta (target i) :=
    Filter.eventually_all.2 fun i =>
      (Measure.tendsto_eval_ae_ae (μ := law) (i := i)).eventually
        (haccuracy i)
  have hmono : (Measure.pi law).real
      {outcomes | ∀ i : Fin m, (outcomes i).1 = true} ≤
      (Measure.pi law).real
        {outcomes | ∀ i : Fin m,
          (outcomes i).1 = true ∧
            ((outcomes i).2 : Real) ∈ Arlib.relErr eta (target i)} := by
    unfold Measure.real
    apply ENNReal.toReal_mono (by finiteness)
    apply measure_mono_ae
    filter_upwards [hae] with outcomes hgoodacc
    intro htags i
    exact ⟨htags i, hgoodacc i (htags i)⟩
  exact hgood.trans hmono

/-- All concrete CV18 component estimates are simultaneously tagged good
with probability at least `1 - δ/4` in their independent product law. -/
theorem community_volume_outcomes_good
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams)
    (hcomponents : 0 < (prep.run F hbounded).componentCount) :
    let D := prep.run F hbounded
    let law : Fin D.componentCount → Measure VolumeOutcome :=
      fun i => (ttcSubroutines hn prep).ComputeVolume
        (D.component i) p.ε'
        (p.δ' D.componentCount)
    (Measure.pi law).real
      {outcomes | ∀ i : Fin D.componentCount,
        (outcomes i).1 = true} ≥
      1 - p.delta / 4 := by
  dsimp only
  let D := prep.run F hbounded
  let law : Fin D.componentCount → Measure VolumeOutcome :=
    fun i => (ttcSubroutines hn prep).ComputeVolume
      (D.component i) p.ε'
      (p.δ' D.componentCount)
  have hcontract := community_volume_contract hn prep F hbounded p
  have hgood := independent_volume_outcomes_good
    D.componentCount law (fun _ => p.δ' D.componentCount)
    (fun i => (hcontract i).1)
    (fun i => (hcontract i).2.1)
  have hsum : (∑ _i : Fin D.componentCount,
      p.δ' D.componentCount) = p.delta / 4 := by
    have hm : (D.componentCount : Real) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hcomponents)
    simp only [Finset.sum_const, Finset.card_fin,
      nsmul_eq_mul, ApproxParams.δ']
    field_simp
  simpa only [hsum] using hgood

/-- On the same product law, every good tag has its promised relative
volume accuracy, simultaneously across the finite component family. -/
theorem community_volume_outcomes_accurate
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) :
    let D := prep.run F hbounded
    let law : Fin D.componentCount → Measure VolumeOutcome :=
      fun i => (ttcSubroutines hn prep).ComputeVolume
        (D.component i) p.ε'
        (p.δ' D.componentCount)
    ∀ᵐ outcomes ∂Measure.pi law,
      ∀ i : Fin D.componentCount,
        (outcomes i).1 = true →
          ((outcomes i).2 : Real) ∈ Arlib.relErr p.ε'
            (volume (D.component i).carrier).toReal := by
  dsimp only
  let D := prep.run F hbounded
  let law : Fin D.componentCount → Measure VolumeOutcome :=
    fun i => (ttcSubroutines hn prep).ComputeVolume
      (D.component i) p.ε'
      (p.δ' D.componentCount)
  have hcontract := community_volume_contract hn prep F hbounded p
  letI : ∀ i, IsProbabilityMeasure (law i) := fun i => by
    simpa [law, D, ttcSubroutines] using
      (hcontract i).1
  exact Filter.eventually_all.2 fun i => by
    have hi : ∀ᵐ o ∂law i, o.1 = true →
        (o.2 : Real) ∈ Arlib.relErr p.ε'
          (volume (D.component i).carrier).toReal := by
      simpa [law, D, ttcSubroutines] using
        (hcontract i).2.2
    exact (Measure.tendsto_eval_ae_ae (μ := law) (i := i)).eventually hi

/-- The concrete independent CV18 outcomes meet every component's volume
premise simultaneously within the allocated `δ/4` failure budget. -/
theorem community_volume_outcomes_good_accurate
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams)
    (hcomponents : 0 < (prep.run F hbounded).componentCount) :
    let D := prep.run F hbounded
    let law : Fin D.componentCount → Measure VolumeOutcome :=
      fun i => (ttcSubroutines hn prep).ComputeVolume
        (D.component i) p.ε'
        (p.δ' D.componentCount)
    (Measure.pi law).real
      {outcomes | ∀ i : Fin D.componentCount,
        (outcomes i).1 = true ∧
          ((outcomes i).2 : Real) ∈ Arlib.relErr p.ε'
            (volume (D.component i).carrier).toReal} ≥
      1 - p.delta / 4 := by
  dsimp only
  let D := prep.run F hbounded
  let law : Fin D.componentCount → Measure VolumeOutcome :=
    fun i => (ttcSubroutines hn prep).ComputeVolume
      (D.component i) p.ε'
      (p.δ' D.componentCount)
  have hcontract := community_volume_contract hn prep F hbounded p
  letI : ∀ i, IsProbabilityMeasure (law i) := fun i => by
    simpa [law, D, ttcSubroutines] using
      (hcontract i).1
  letI : IsProbabilityMeasure (Measure.pi law) := inferInstance
  have hgood := community_volume_outcomes_good hn prep F hbounded p
    hcomponents
  have hacc := community_volume_outcomes_accurate
    hn prep F hbounded p
  have hmono : (Measure.pi law).real
      {outcomes | ∀ i : Fin D.componentCount, (outcomes i).1 = true} ≤
      (Measure.pi law).real
        {outcomes | ∀ i : Fin D.componentCount,
          (outcomes i).1 = true ∧
            ((outcomes i).2 : Real) ∈ Arlib.relErr p.ε'
              (volume (D.component i).carrier).toReal} := by
    unfold Measure.real
    apply ENNReal.toReal_mono (by finiteness)
    apply measure_mono_ae
    filter_upwards [hacc] with outcomes haccuracy
    intro htags i
    exact ⟨htags i, haccuracy i (htags i)⟩
  exact hgood.trans hmono

end ttc
