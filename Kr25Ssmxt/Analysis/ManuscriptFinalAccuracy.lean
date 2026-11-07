import Kr25Ssmxt.Analysis.PrecisionRequirements
import Kr25Ssmxt.Analysis.ManuscriptEstimateFromCount
import Kr25Ssmxt.Analysis.ManuscriptProbabilityMeasure
import Kr25Ssmxt.Analysis.TtcVolumeAccuracyLatticeComparison
import Kr25Ssmxt.Analysis.TheoremProof

/-! Deterministic final assembly for manuscript Theorem 1. The outstanding
stochastic statement is a lattice-count estimate for the actual adaptive run. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem community_manuscriptTTC_volume_accuracy_empty
    {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (hempty : (prep.run F hbounded).componentCount = 0) :
    (communityManuscriptTTC hn F hbounded p prep).real
      {estimate | (estimate : Real) ∈
        Arlib.relErr p.epsilon (volume (solutionSet F)).toReal} ≥
      1 - p.delta := by
  let D := prep.run F hbounded
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
  have hset : MeasurableSet
      {estimate : NNReal | (estimate : Real) ∈ Arlib.relErr p.epsilon 0} :=
    measurableSet_Icc.preimage (by fun_prop)
  have hzero : (0 : NNReal) ∈
      {estimate : NNReal | (estimate : Real) ∈ Arlib.relErr p.epsilon 0} := by
    simp [Arlib.relErr]
  have hrun : communityManuscriptTTC hn F hbounded p prep =
      Measure.dirac 0 := by
    simp [communityManuscriptTTC, manuscriptTTC,
      communityManuscriptOracles, hempty]
  rw [hrun, hvolume]
  simp only [ENNReal.toReal_zero]
  rw [Measure.real, Measure.dirac_apply' 0 hset,
    Set.indicator_of_mem hzero]
  simp
  exact p.delta_pos.le

/-- The union lattice comparison upgrades the manuscript's intermediate
`ε/2` lattice-count estimate to the headline `ε` volume estimate. -/
theorem community_manuscriptTTC_volume_accuracy_of_lattice_estimate
    {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (hlatticeEstimate :
      let D := prep.run F hbounded
      let b := (prep.choosePrecision D p).value
      (communityManuscriptTTC hn F hbounded p prep).real
        {estimate | (estimate : Real) ∈
          Arlib.relErr (p.epsilon / 2)
            ((D.latticePoints b).ncard / (10 : Real) ^ (b * n))} ≥
        1 - p.delta) :
    (communityManuscriptTTC hn F hbounded p prep).real
      {estimate | (estimate : Real) ∈
        Arlib.relErr p.epsilon (volume (solutionSet F)).toReal} ≥
      1 - p.delta := by
  let D := prep.run F hbounded
  let b := (prep.choosePrecision D p).value
  let O := communityManuscriptOracles hn prep
  have hcomparison := ttc_volume_accuracy_lattice_comparison
    (lt_of_lt_of_le (by norm_num) hn) D p b
    (prep.choosePrecision D p).adequate
  have hunion : (volume D.union).toReal ∈
      Arlib.relErr p.latticeEta
        ((D.latticePoints b).ncard / (10 : Real) ^ (b * n)) := hcomparison.2
  let μ := communityManuscriptTTC hn F hbounded p prep
  letI : IsProbabilityMeasure μ :=
    community_manuscriptTTC_isProbabilityMeasure hn F hbounded p prep
  have htarget : μ.real
      {estimate | (estimate : Real) ∈
        Arlib.relErr p.epsilon (volume D.union).toReal} ≥
      1 - p.delta := by
    apply hlatticeEstimate.trans
    refine measureReal_mono ?_
    intro estimate hestimate
    change (1 - p.epsilon / 2) *
        ((D.latticePoints b).ncard / (10 : Real) ^ (b * n)) ≤
          (estimate : Real) ∧
        (estimate : Real) ≤ (1 + p.epsilon / 2) *
          ((D.latticePoints b).ncard / (10 : Real) ^ (b * n)) at hestimate
    change (1 - p.epsilon) * (volume D.union).toReal ≤
        (estimate : Real) ∧
      (estimate : Real) ≤ (1 + p.epsilon) * (volume D.union).toReal
    have hq : 0 ≤ ((D.latticePoints b).ncard : Real) /
        (10 : Real) ^ (b * n) :=
      div_nonneg (Nat.cast_nonneg _) (by positivity)
    have hone_sub : 0 ≤ 1 - p.epsilon := sub_nonneg.mpr p.epsilon_le_one
    have hone_add : 0 ≤ 1 + p.epsilon := by linarith [p.epsilon_pos]
    constructor
    · calc
        (1 - p.epsilon) * (volume D.union).toReal ≤
            (1 - p.epsilon) *
              ((1 + p.epsilon / 8) *
                ((D.latticePoints b).ncard / (10 : Real) ^ (b * n))) :=
          mul_le_mul_of_nonneg_left hunion.2 hone_sub
        _ ≤ (1 - p.epsilon / 2) *
            ((D.latticePoints b).ncard / (10 : Real) ^ (b * n)) := by
          nlinarith [p.epsilon_pos, p.epsilon_le_one]
        _ ≤ (estimate : Real) := hestimate.1
    · calc
        (estimate : Real) ≤ (1 + p.epsilon / 2) *
            ((D.latticePoints b).ncard / (10 : Real) ^ (b * n)) := hestimate.2
        _ ≤ (1 + p.epsilon) *
            ((1 - p.epsilon / 8) *
              ((D.latticePoints b).ncard / (10 : Real) ^ (b * n))) := by
          nlinarith [p.epsilon_pos, p.epsilon_le_one]
        _ ≤ (1 + p.epsilon) * (volume D.union).toReal :=
          mul_le_mul_of_nonneg_left hunion.1 hone_add
  simpa only [D.volume_eq_solutionSet] using htarget

end Kr25Ssmxt
