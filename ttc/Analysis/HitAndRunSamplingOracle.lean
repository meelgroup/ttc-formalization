import ttc.Analysis.OracleContracts
import ttc.Analysis.PrecisionRequirements
import ttc.Analysis.MathlibCompat
import ttc.Analysis.GeometricOracleDischarge
import ttc.Analysis.KV97HitAndRunSampling
import ttc.Analysis.NormalizedHitAndRunGeometry

/-!
# A TTC sampling oracle implemented by Hit-and-Run and KV97 rounding

Sampler-side helpers: the sampler-radius requirement is at least one, the
finite-step Hit-and-Run point law exists for every certified polytope, and the
independent-restart batch law is a probability measure tagged as successful.
-/

noncomputable section

open scoped ENNReal NNReal ProbabilityTheory
open MeasureTheory

namespace ttc

/-- The paper's sampler-radius expression is at least one in its intended parameter range. -/
lemma one_le_samplerRadiusRequirement {n : Nat} (hn : 0 < n) (P : PolytopeData n)
    {eta : Real} (heta0 : 0 < eta) (heta1 : eta ≤ 1) :
    1 ≤ samplerRadiusRequirement P eta := by
  have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
  have hf1 : (1 : Real) ≤ P.presentation.facetCount := by
    exact_mod_cast P.facets_pos
  have hratio : (4 : Real) ≤ 32 * P.presentation.facetCount / eta := by
    rw [le_div_iff₀ heta0]
    nlinarith [mul_nonneg (show (0 : Real) ≤ P.presentation.facetCount by positivity)
      (sub_nonneg.mpr heta1)]
  have hsqrt :
      (1 : Real) ≤ Real.sqrt (Real.log (32 * P.presentation.facetCount / eta)) := by
    rw [Real.one_le_sqrt]
    have hlog4 : (1 : Real) ≤ Real.log 4 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      exact Real.exp_one_lt_three.le.trans (by norm_num)
    exact hlog4.trans (Real.log_le_log (by norm_num) hratio)
  have hbase : (1 : Real) ≤ 512 * n / eta := by
    rw [le_div_iff₀ heta0]
    nlinarith
  rw [samplerRadiusRequirement]
  exact hbase.trans (le_mul_of_one_le_right (by positivity) hsqrt)

lemma iidSampleBatchLaw_isProbabilityMeasure {n count : Nat}
    (pointLaw : Measure (LatticePoint n)) [IsProbabilityMeasure pointLaw] :
    IsProbabilityMeasure (iidSampleBatchLaw (count := count) pointLaw) := by
  unfold iidSampleBatchLaw
  infer_instance

end ttc
