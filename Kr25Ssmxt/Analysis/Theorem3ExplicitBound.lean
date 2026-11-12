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
      TTCRuntime.theorem3CV18LogBound n (TTCRuntime.theorem3Rho D) p.ε'
        (p.δ' D.componentCount) := by
  set q := CommunityCV18.params (by omega) (D.component i) p.ε' (p.δ' D.componentCount) h
  set rho := TTCRuntime.theorem3Rho D
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
      TTCRuntime.theorem3CV18LogBound n (TTCRuntime.theorem3Rho D) p.ε'
        (p.δ' D.componentCount) := by
  have hB := TTCRuntime.theorem3CV18LogBound_nonneg n (TTCRuntime.theorem3Rho D) p.ε'
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
          (TTCRuntime.theorem3RMax D : Real) *
          (TTCRuntime.theorem3Rho D) ^ 2 *
          TTCRuntime.theorem3InputScale D p *
          ((TTCRuntime.sampleCap p D.componentCount : Real) + 1) *
          (TTCRuntime.theorem3ParameterFactor D p + 1)) := by
  dsimp only
  refine (ttc_expected_runtime_theorem3_input_scale hn F hbounded p prep
    preprocessingOperations).trans ?_
  have hpf := TTCRuntime.theorem3ParameterFactorCV18_le hn (prep.run F hbounded) p
  have hscale := TTCRuntime.theorem3InputScale_nonneg (prep.run F hbounded) p
  have hparam := theorem3ParameterFactor_add_one_nonneg hn (prep.run F hbounded) p
  gcongr

end Kr25Ssmxt
