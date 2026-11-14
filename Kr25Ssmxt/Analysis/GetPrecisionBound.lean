import Kr25Ssmxt.Analysis.PrecisionChoice
import Kr25Ssmxt.Analysis.PrecisionRequirements
import Kr25Ssmxt.Analysis.RuntimeBounds

/-! The precision chosen by `getprec` at `ε / 96` is bounded by input data
alone, which removes `b` from the Theorem 3 runtime bound. -/

noncomputable section

namespace Kr25Ssmxt

open MeasureTheory

theorem latticeRadiusRequirement_precisionEta_nonneg {n k : Nat}
    {F : LRAFormula n k} (D : Decomposition F) (p : ApproxParams) :
    0 ≤ latticeRadiusRequirement D p.precisionEta := by
  have hε := p.epsilon_pos
  unfold latticeRadiusRequirement ApproxParams.precisionEta
  positivity

/-- `getprec`'s output is at most `1 + log₁₀⁺ γ + log₁₀⁺ (1 / minᵢ γᵢ)`. -/
theorem getPrecision_le_theorem3PrecisionBound {n k : Nat}
    {F : LRAFormula n k} (D : Decomposition F) (p : ApproxParams) :
    (GetPrecision D p.precisionEta : Real) ≤
      TTCRuntime.theorem3PrecisionBound D p := by
  set γ := latticeRadiusRequirement D p.precisionEta with hγdef
  set c := TTCRuntime.theorem3InverseInradiusMax D with hcdef
  have hγ0 : 0 ≤ γ := latticeRadiusRequirement_precisionEta_nonneg D p
  have hc0 : 0 ≤ c := by rw [hcdef]; unfold TTCRuntime.theorem3InverseInradiusMax; positivity
  have h10 : (1 : Real) < 10 := by norm_num
  have hratio1 : (1 : Real) ≤ getPrecisionRatio D p.precisionEta := le_max_left _ _
  have hratio : getPrecisionRatio D p.precisionEta ≤ max 1 (γ * c) := by
    unfold getPrecisionRatio
    apply max_le_max le_rfl
    rw [← Real.coe_toNNReal (γ * c) (mul_nonneg hγ0 hc0)]
    apply NNReal.coe_le_coe.mpr
    apply Finset.sup_le
    intro i _
    apply Real.toNNReal_le_toNNReal
    have hinv : 1 / (D.component i).inradius ≤ c := by
      rw [hcdef]
      unfold TTCRuntime.theorem3InverseInradiusMax
      refine (Real.le_coe_toNNReal _).trans (NNReal.coe_le_coe.mpr ?_)
      exact Finset.le_sup
        (f := fun i : Fin D.componentCount =>
          Real.toNNReal (1 / (D.component i).inradius)) (Finset.mem_univ i)
    rw [(D.component i).MaxInscribedBall_eq_inradius, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hinv hγ0
  have hlog : Real.logb 10 (max 1 (γ * c)) ≤
      max 0 (Real.logb 10 γ) + max 0 (Real.logb 10 c) := by
    by_cases h : γ * c ≤ 1
    · rw [max_eq_left h, Real.logb_one]
      exact add_nonneg (le_max_left _ _) (le_max_left _ _)
    · replace h := not_le.mp h
      rw [max_eq_right h.le]
      have hγpos : 0 < γ := by
        rcases hγ0.lt_or_eq with hlt | heq
        · exact hlt
        · rw [← heq, zero_mul] at h; linarith
      have hcpos : 0 < c := by
        rcases hc0.lt_or_eq with hlt | heq
        · exact hlt
        · rw [← heq, mul_zero] at h; linarith
      rw [Real.logb_mul hγpos.ne' hcpos.ne']
      exact add_le_add (le_max_right _ _) (le_max_right _ _)
  have hceil : (GetPrecision D p.precisionEta : Real) <
      Real.logb 10 (getPrecisionRatio D p.precisionEta) + 1 :=
    Nat.ceil_lt_add_one (Real.logb_nonneg h10 hratio1)
  have hmono : Real.logb 10 (getPrecisionRatio D p.precisionEta) ≤
      Real.logb 10 (max 1 (γ * c)) :=
    Real.logb_le_logb_of_le h10 (by linarith) hratio
  unfold TTCRuntime.theorem3PrecisionBound
  rw [← hγdef, ← hcdef]
  linarith

theorem theorem3PrecisionScale_le_inputScale {n k : Nat}
    {F : LRAFormula n k} (prep : TTCPreprocessor n k) (D : Decomposition F)
    (p : ApproxParams) :
    TTCRuntime.theorem3PrecisionScale (prep.choosePrecision D p).value
        (TTCRuntime.theorem3OuterRadiusMax D) ≤
      TTCRuntime.theorem3InputScale D p := by
  have h := getPrecision_le_theorem3PrecisionBound D p
  unfold TTCRuntime.theorem3PrecisionScale TTCRuntime.theorem3InputScale
  change 1 + (GetPrecision D p.precisionEta : Real) + _ ≤ _
  linarith

theorem theorem3ParameterFactor_add_one_nonneg {n k : Nat} (hn : 21 ≤ n)
    {F : LRAFormula n k} (D : Decomposition F) (p : ApproxParams) :
    0 ≤ TTCRuntime.theorem3ParameterFactorCV18 hn D p + 1 := by
  have hLog : 0 ≤ TTCRuntime.theorem3CV18LogMax hn D p := by
    unfold TTCRuntime.theorem3CV18LogMax
    positivity
  have hrho : 1 ≤ TTCRuntime.Rho D := le_max_left _ _
  have hlogrho : 0 ≤ Real.log (4 * TTCRuntime.Rho D + 1) :=
    Real.log_nonneg (by linarith)
  have heps : 0 < p.ε' := by
    dsimp [ApproxParams.ε']
    positivity [p.epsilon_pos]
  have hlogeta : 0 ≤ Real.log (1 + 8 / p.ε') := by
    apply Real.log_nonneg
    have : 0 ≤ 8 / p.ε' := div_nonneg (by norm_num) heps.le
    linarith
  have hL : 0 ≤ TTCRuntime.theorem3ParameterFactorCV18 hn D p := by
    unfold TTCRuntime.theorem3ParameterFactorCV18
    positivity [ArlibCommunity.Algorithms.CV18.runCostConstant_pos]
  linarith

/-- Theorem 3 with the precision `b` replaced by its input-only bound. -/
theorem ttc_expected_runtime_theorem3_input_scale {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations : Nat) :
    let D := prep.run F hbounded
    ∫⁻ result, (result.2 : ENNReal) ∂
      ttcWithCost hn F hbounded p prep
        preprocessingOperations 1 ≤
      preprocessingOperations + (D.componentCount : ENNReal) *
        ENNReal.ofReal (30 * (n : Real) ^ 5 *
          (TTCRuntime.RMax D : Real) *
          (TTCRuntime.Rho D) ^ 2 *
          TTCRuntime.theorem3InputScale D p *
          ((TTCRuntime.ThresholdCap p D.componentCount : Real) + 1) *
          (TTCRuntime.theorem3ParameterFactorCV18 hn D p + 1)) := by
  dsimp only
  refine (ttc_expected_runtime_theorem3_headline_scale hn F hbounded p prep
    preprocessingOperations).trans ?_
  have hscale := theorem3PrecisionScale_le_inputScale prep (prep.run F hbounded) p
  have hparam := theorem3ParameterFactor_add_one_nonneg hn (prep.run F hbounded) p
  gcongr
  all_goals first | exact hscale | exact hparam | positivity

end Kr25Ssmxt
