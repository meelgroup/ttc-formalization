import Kr25Ssmxt.Model.Run
import Kr25Ssmxt.Analysis.TheoremProof

/-! The exact zero-component branch of the current manuscript TTC program. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem manuscriptTTC_empty_accuracy
    {n k : Nat} (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (O : TTCOracles n k)
    (hempty : (O.preprocessing.run F hbounded).componentCount = 0) :
    IsProbabilityMeasure (ttcWith F hbounded p O) ∧
    (ttcWith F hbounded p O).real
      {estimate | (estimate : Real) ∈
        Arlib.relErr p.epsilon (volume (solutionSet F)).toReal} ≥
      1 - p.delta := by
  let D := O.preprocessing.run F hbounded
  have hD : D.componentCount = 0 := hempty
  have hunion : D.union = ∅ := by
    ext x
    constructor
    · intro hx
      simp only [Decomposition.union, Set.mem_iUnion] at hx
      obtain ⟨i, hi⟩ := hx
      have : i.val < 0 := by simpa [hD] using i.isLt
      omega
    · simp
  have hvolume : volume (solutionSet F) = 0 := by
    rw [← D.volume_eq_solutionSet, hunion]
    simp
  have hzero : (0 : Real) ∈ Arlib.relErr p.epsilon 0 := by
    simp [Arlib.relErr]
  have hset : MeasurableSet
      {estimate : NNReal | (estimate : Real) ∈ Arlib.relErr p.epsilon 0} :=
    measurableSet_Icc.preimage (by fun_prop)
  simp only [ttcWith, hempty, if_pos, hvolume]
  constructor
  · infer_instance
  · have hmem : (0 : NNReal) ∈
        {estimate : NNReal | (estimate : Real) ∈ Arlib.relErr p.epsilon 0} :=
      hzero
    simp only [ENNReal.toReal_zero]
    rw [Measure.real, Measure.dirac_apply' 0 hset, Set.indicator_of_mem hmem]
    simp only [Pi.one_apply, ENNReal.toReal_one]
    linarith [p.delta_pos, p.delta_le_one]

end Kr25Ssmxt
