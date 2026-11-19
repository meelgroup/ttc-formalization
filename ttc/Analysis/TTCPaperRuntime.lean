import ttc.Analysis.CommunityCV18VolumeProvider
import ttc.Analysis.HitAndRunSamplingOracle
import ttc.Analysis.ThinningCosts
import ttc.Model.Prelude

/-!
# Runtime helper lemmas

Markov's inequality in the form used for a high-probability runtime bound, and
admissibility of every CV18 request TTC makes.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace ttc
namespace PaperRuntime

open TTCRuntime

/-- Markov's inequality in the form needed for a high-probability runtime bound.
The cutoff is the expected-cost budget divided by the allowed failure probability,
so its dependence on that probability is polynomial of degree one. This lemma
requires a costed run law; `communityTTC` currently records only its estimate. -/
theorem runtime_tail_le_of_expected_cost
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (cost : Ω → ENNReal) (hcost : Measurable cost)
    (budget failure : ENNReal)
    (hbudget0 : budget ≠ 0) (hbudgetTop : budget ≠ ∞)
    (hfailure0 : failure ≠ 0) (hfailureTop : failure ≠ ∞)
    (hexpected : ∫⁻ ω, cost ω ∂μ ≤ budget) :
    μ {ω | budget / failure ≤ cost ω} ≤ failure := by
  have hcutoff0 : budget / failure ≠ 0 :=
    ENNReal.div_ne_zero.mpr ⟨hbudget0, hfailureTop⟩
  have hcutoffTop : budget / failure ≠ ∞ :=
    ENNReal.div_ne_top hbudgetTop hfailure0
  apply (ENNReal.mul_le_mul_iff_right hcutoff0 hcutoffTop).mp
  calc
    (budget / failure) * μ {ω | budget / failure ≤ cost ω} ≤
        ∫⁻ ω, cost ω ∂μ :=
      MeasureTheory.mul_meas_ge_le_lintegral hcost (budget / failure)
    _ ≤ budget := hexpected
    _ = (budget / failure) * failure :=
      (ENNReal.div_mul_cancel hfailure0 hfailureTop).symm

theorem ttc_request_admissible {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (i : Fin D.componentCount) :
    CommunityCV18.AdmissibleCV18Request
      p.ε' (p.δ' D.componentCount) := by
  have hcount : 0 < D.componentCount := lt_of_le_of_lt (Nat.zero_le i) i.isLt
  have hdenom : 0 < (4 * D.componentCount : Real) := by
    exact_mod_cast Nat.mul_pos (by norm_num : 0 < 4) hcount
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact div_pos p.epsilon_pos (by norm_num)
  · dsimp only [ApproxParams.ε']
    linarith [p.epsilon_le_one]
  · exact div_pos p.delta_pos hdenom
  · dsimp only [ApproxParams.δ']
    rw [div_le_iff₀ hdenom]
    have hcountR : (1 : Real) ≤ D.componentCount := by exact_mod_cast hcount
    nlinarith [p.delta_le_one]

end PaperRuntime
end ttc
