import Kr25Ssmxt.Analysis.GetPrecisionBound
import Kr25Ssmxt.Analysis.CV18RoundnessBound
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledLogEnvelope

/-! # Theorem 3 with an explicit CV18 factor

arlib-community's `figureOneScheduledLogEnvelope_le` bounds CV18's six scheduled
logarithmic factors by `14113440000 · Λ¹⁰` with `Λ = protectedLog (n · max(1, roundness) /
(ε · p))`. At TTC's calls `ε = ε'/2`, `p = δ'/2`, and the roundness of a normalized
component is at most `4ρ² + 1 ≤ 5ρ²`, so `Λ ≤ max 1 (log (20 n ρ² / (ε' δ')))`. Hence the
parameter factor computed from CV18's definitions is at most the explicit
`TTCRuntime.theorem3ParameterFactor` of `Model/Prelude.lean`. -/

namespace Kr25Ssmxt

open MeasureTheory

/-- The explicit factors suppressed in the corrected Theorem 3 headline: the CV18 query
rate's constant `45 · (64 · 10³⁰ + 1)` and logarithmic bound, the Hit-and-Run constant
`2⁶⁸` with its logarithms, and the thinning counter. -/
noncomputable def TTCRuntime.theorem3ParameterFactor {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) : Real :=
  45 * (64 * 10 ^ 30 + 1) *
      TTCRuntime.theorem3CV18LogBound n (TTCRuntime.Rho D) p.ε' (p.δ' D.componentCount) / (p.ε' / 2) ^ 2 +
    (2 : Real) ^ 68 *
      (Real.log 8 + Real.log (4 * TTCRuntime.Rho D + 1) +
        2 * (Real.log 10 + Real.log 6 + 1 +
          Real.log (1 + 8 / p.ε') + 2)) + 20

/-- TTC's name for CV18's scheduled logarithmic product is arlib-community's. -/
theorem TTCRuntime.theorem3CV18LogEnvelope_eq
    (q : ArlibCommunity.Algorithms.CV18.VolumeParams) :
    TTCRuntime.theorem3CV18LogEnvelope q =
      ArlibCommunity.Algorithms.CV18.figureOneScheduledLogEnvelope q := rfl

theorem TTCRuntime.theorem3CV18LogBound_nonneg (n : Nat) (rho ε' δ' : Real) :
    0 ≤ TTCRuntime.theorem3CV18LogBound n rho ε' δ' := by
  unfold TTCRuntime.theorem3CV18LogBound
  have h : (0 : Real) ≤ max 1 (Real.log (20 * n * rho ^ 2 / (ε' * δ'))) :=
    le_trans zero_le_one (le_max_left _ _)
  positivity

/-- At one component, CV18's scheduled logarithmic product is at most the explicit bound. -/
theorem TTCRuntime.theorem3CV18LogEnvelope_params_le {n k : Nat} (hn : 21 ≤ n)
    {F : LRAFormula n k} (D : Decomposition F) (p : ApproxParams)
    (i : Fin D.componentCount)
    (h : CommunityCV18.AdmissibleCV18Request p.ε' (p.δ' D.componentCount)) :
    TTCRuntime.theorem3CV18LogEnvelope
        (CommunityCV18.params (by omega) (D.component i) p.ε' (p.δ' D.componentCount) h) ≤
      TTCRuntime.theorem3CV18LogBound n (TTCRuntime.Rho D) p.ε'
        (p.δ' D.componentCount) := by
  set q := CommunityCV18.params (by omega) (D.component i) p.ε' (p.δ' D.componentCount) h
  set rho := TTCRuntime.Rho D
  have hrho : 1 ≤ rho := le_max_left _ _
  have he : 0 < p.ε' := h.1
  have hd : 0 < p.δ' D.componentCount := h.2.2.1
  have hround := D.communityCV18_roundness_le_rho i
  have hM : max 1 (CommunityCV18.roundness (D.component i)) ≤ 5 * rho ^ 2 := by
    apply max_le <;> nlinarith
  have hsize : ArlibCommunity.Algorithms.CV18.volumeParamSize q =
      4 * n * max 1 (CommunityCV18.roundness (D.component i)) /
        (p.ε' * p.δ' D.componentCount) := by
    simp only [ArlibCommunity.Algorithms.CV18.volumeParamSize, q, CommunityCV18.params]
    field_simp
    ring
  have hsize_pos : 0 < ArlibCommunity.Algorithms.CV18.volumeParamSize q := by
    rw [hsize]
    have : (0 : Real) < max 1 (CommunityCV18.roundness (D.component i)) :=
      lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hn0 : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  have hsize_le : ArlibCommunity.Algorithms.CV18.volumeParamSize q ≤
      20 * n * rho ^ 2 / (p.ε' * p.δ' D.componentCount) := by
    rw [hsize]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hn0 : (0 : Real) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hlog : ArlibCommunity.Algorithms.CV18.volumeParamLog q ≤
      max 1 (Real.log (20 * n * rho ^ 2 / (p.ε' * p.δ' D.componentCount))) :=
    max_le_max le_rfl (Real.log_le_log hsize_pos hsize_le)
  have hlog0 : 0 ≤ ArlibCommunity.Algorithms.CV18.volumeParamLog q :=
    le_trans zero_le_one (le_max_left _ _)
  rw [TTCRuntime.theorem3CV18LogEnvelope_eq]
  refine (ArlibCommunity.Algorithms.CV18.figureOneScheduledLogEnvelope_le q).trans ?_
  unfold TTCRuntime.theorem3CV18LogBound
  gcongr

/-- The maximum over components of CV18's logarithmic product is at most the explicit
bound. -/
theorem TTCRuntime.theorem3CV18LogMax_le {n k : Nat} (hn : 21 ≤ n)
    {F : LRAFormula n k} (D : Decomposition F) (p : ApproxParams) :
    TTCRuntime.theorem3CV18LogMax hn D p ≤
      TTCRuntime.theorem3CV18LogBound n (TTCRuntime.Rho D) p.ε'
        (p.δ' D.componentCount) := by
  have hB := TTCRuntime.theorem3CV18LogBound_nonneg n (TTCRuntime.Rho D) p.ε'
    (p.δ' D.componentCount)
  unfold TTCRuntime.theorem3CV18LogMax
  rw [← Real.coe_toNNReal _ hB]
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro i _
  apply Real.toNNReal_le_toNNReal
  split
  · exact TTCRuntime.theorem3CV18LogEnvelope_params_le hn D p i _
  · exact absurd (CommunityCV18.admissibleTTCRequest D p i) ‹_›

/-- The parameter factor computed from CV18's definitions is at most the explicit one. -/
theorem TTCRuntime.theorem3ParameterFactorCV18_le {n k : Nat} (hn : 21 ≤ n)
    {F : LRAFormula n k} (D : Decomposition F) (p : ApproxParams) :
    TTCRuntime.theorem3ParameterFactorCV18 hn D p ≤ TTCRuntime.theorem3ParameterFactor D p := by
  have hmax := TTCRuntime.theorem3CV18LogMax_le hn D p
  unfold TTCRuntime.theorem3ParameterFactorCV18 TTCRuntime.theorem3ParameterFactor
  simp only [ArlibCommunity.Algorithms.CV18.figureOneFinalScheduledExpectedCostConstant]
  gcongr

theorem TTCRuntime.theorem3InputScale_nonneg {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) : 0 ≤ TTCRuntime.theorem3InputScale D p := by
  unfold TTCRuntime.theorem3InputScale TTCRuntime.theorem3PrecisionBound
  have h1 := le_max_left 0 (Real.logb 10 (latticeRadiusRequirement D p.precisionEta))
  have h2 := le_max_left 0 (Real.logb 10 (TTCRuntime.theorem3InverseInradiusMax D))
  have h3 := le_max_left 0 (Real.log (TTCRuntime.theorem3OuterRadiusMax D))
  linarith

/-- The explicit factor, after pulling out `ε⁻²`, is `polylogFactors`. -/
theorem TTCRuntime.inputScale_mul_factor_le {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) :
    TTCRuntime.theorem3InputScale D p * (TTCRuntime.theorem3ParameterFactor D p + 1) ≤
      TTCRuntime.polylogFactors D p / p.epsilon ^ 2 := by
  set L := TTCRuntime.theorem3CV18LogBound n (TTCRuntime.Rho D) p.ε' (p.δ' D.componentCount)
  set H := (2 : Real) ^ 68 *
    (Real.log 8 + Real.log (4 * TTCRuntime.Rho D + 1) +
      2 * (Real.log 10 + Real.log 6 + 1 + Real.log (1 + 8 / p.ε') + 2))
  set A : Real := 45 * (64 * 10 ^ 30 + 1)
  have hS := TTCRuntime.theorem3InputScale_nonneg D p
  have hL : 0 ≤ L := TTCRuntime.theorem3CV18LogBound_nonneg _ _ _ _
  have he := p.epsilon_pos
  have he1 := p.epsilon_le_one
  have hrho : 1 ≤ TTCRuntime.Rho D := le_max_left _ _
  have hε' : 0 < p.ε' := by unfold ApproxParams.ε'; positivity
  have hH : 0 ≤ H := by
    have h8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    have hr : 0 ≤ Real.log (4 * TTCRuntime.Rho D + 1) := Real.log_nonneg (by linarith)
    have h10 : 0 ≤ Real.log 10 := Real.log_nonneg (by norm_num)
    have h6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
    have hε : 0 ≤ Real.log (1 + 8 / p.ε') := Real.log_nonneg (by
      have : 0 ≤ 8 / p.ε' := by positivity
      linarith)
    positivity
  have hA : 0 ≤ A := by positivity
  have he2 : 0 < p.epsilon ^ 2 := by positivity
  have he21 : p.epsilon ^ 2 ≤ 1 := pow_le_one₀ he.le he1
  have hfac : TTCRuntime.theorem3ParameterFactor D p + 1 ≤
      (576 * A * L + H + 21) / p.epsilon ^ 2 := by
    have hdef : TTCRuntime.theorem3ParameterFactor D p = A * L / (p.ε' / 2) ^ 2 + H + 20 := rfl
    have hq : (p.ε' / 2) ^ 2 = p.epsilon ^ 2 / 576 := by unfold ApproxParams.ε'; ring
    rw [hdef, hq, le_div_iff₀ he2]
    have : A * L / (p.epsilon ^ 2 / 576) * p.epsilon ^ 2 = 576 * A * L := by
      field_simp
    have hHe : (H + 21) * p.epsilon ^ 2 ≤ H + 21 := by
      have := mul_le_mul_of_nonneg_left he21 (by linarith : (0 : Real) ≤ H + 21)
      linarith
    nlinarith
  calc TTCRuntime.theorem3InputScale D p * (TTCRuntime.theorem3ParameterFactor D p + 1)
      ≤ TTCRuntime.theorem3InputScale D p * ((576 * A * L + H + 21) / p.epsilon ^ 2) :=
        mul_le_mul_of_nonneg_left hfac hS
    _ = TTCRuntime.polylogFactors D p / p.epsilon ^ 2 := by
        unfold TTCRuntime.polylogFactors
        ring

/-- Theorem 3 with every constant explicit in Prelude terms. -/
theorem ttc_expected_runtime_theorem3_explicit {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations : Nat) :
    let D := prep.run F hbounded
    ∫⁻ result, (result.2 : ENNReal) ∂
      ttcWithCost hn F hbounded p prep preprocessingOperations 1 ≤
      preprocessingOperations + (D.componentCount : ENNReal) *
        ENNReal.ofReal (30 * (n : Real) ^ 5 *
          (TTCRuntime.RMax D : Real) *
          (TTCRuntime.Rho D) ^ 2 *
          ((TTCRuntime.ThresholdCap p D.componentCount : Real) + 1) / p.epsilon ^ 2 *
          TTCRuntime.polylogFactors D p) := by
  dsimp only
  refine (ttc_expected_runtime_theorem3_input_scale hn F hbounded p prep
    preprocessingOperations).trans ?_
  set D := prep.run F hbounded
  have hpf := TTCRuntime.theorem3ParameterFactorCV18_le hn D p
  have hS := TTCRuntime.theorem3InputScale_nonneg D p
  have hkey : TTCRuntime.theorem3InputScale D p *
      (TTCRuntime.theorem3ParameterFactorCV18 hn D p + 1) ≤
      TTCRuntime.polylogFactors D p / p.epsilon ^ 2 :=
    (mul_le_mul_of_nonneg_left (by linarith) hS).trans
      (TTCRuntime.inputScale_mul_factor_le D p)
  have hC : 0 ≤ 30 * (n : Real) ^ 5 * (TTCRuntime.RMax D : Real) * (TTCRuntime.Rho D) ^ 2 *
      ((TTCRuntime.ThresholdCap p D.componentCount : Real) + 1) := by positivity
  refine add_le_add le_rfl (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_))
  calc 30 * (n : Real) ^ 5 * (TTCRuntime.RMax D : Real) * (TTCRuntime.Rho D) ^ 2 *
        TTCRuntime.theorem3InputScale D p *
        ((TTCRuntime.ThresholdCap p D.componentCount : Real) + 1) *
        (TTCRuntime.theorem3ParameterFactorCV18 hn D p + 1)
      = (30 * (n : Real) ^ 5 * (TTCRuntime.RMax D : Real) * (TTCRuntime.Rho D) ^ 2 *
          ((TTCRuntime.ThresholdCap p D.componentCount : Real) + 1)) *
        (TTCRuntime.theorem3InputScale D p *
          (TTCRuntime.theorem3ParameterFactorCV18 hn D p + 1)) := by ring
    _ ≤ (30 * (n : Real) ^ 5 * (TTCRuntime.RMax D : Real) * (TTCRuntime.Rho D) ^ 2 *
          ((TTCRuntime.ThresholdCap p D.componentCount : Real) + 1)) *
        (TTCRuntime.polylogFactors D p / p.epsilon ^ 2) := mul_le_mul_of_nonneg_left hkey hC
    _ = 30 * (n : Real) ^ 5 * (TTCRuntime.RMax D : Real) * (TTCRuntime.Rho D) ^ 2 *
          ((TTCRuntime.ThresholdCap p D.componentCount : Real) + 1) / p.epsilon ^ 2 *
          TTCRuntime.polylogFactors D p := by ring

end Kr25Ssmxt
