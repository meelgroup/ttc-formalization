import Kr25Ssmxt.Analysis.CommunityCV18VolumeProvider
import Kr25Ssmxt.Analysis.HitAndRunSamplingOracle

/-!
# TTC with a CV18 volume provider and Hit-and-Run/KV97 sampling

This module combines the two concrete geometric routes without changing TTC's algorithm:

* the volume field is supplied by a normalized CV18 estimator provider and rescaled by the
  proved affine Jacobian;
* the sampling field is the already proved finite-step Hit-and-Run plus KV97
  rounding/rejection construction.

The concrete bundle below uses the current `arlib-community` CV18 capstone directly.
-/

noncomputable section

open MeasureTheory

namespace Kr25Ssmxt

/-- The combined TTC oracle bundle. -/
def cv18HitAndRunOracles {n k : Nat} (hn : 21 <= n) (prep : TTCPreprocessor n k)
    (V : NormalizedCV18VolumeProvider n) : TTCOracles n k :=
  (hitAndRunSamplingOracles hn prep).withNormalizedCV18Volume V

theorem cv18HitAndRun_volume_contract {n k : Nat} (hn : 21 <= n)
    (prep : TTCPreprocessor n k) (V : NormalizedCV18VolumeProvider n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (params : ApproxParams) :
    ComputeVolumeContract (cv18HitAndRunOracles hn prep V) F hbounded params :=
  withNormalizedCV18Volume_volume_contract (hitAndRunSamplingOracles hn prep) V
    F hbounded params

theorem cv18HitAndRun_samples_contract {n k : Nat} (hn : 21 <= n)
    (prep : TTCPreprocessor n k) (V : NormalizedCV18VolumeProvider n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (params : ApproxParams) :
    GenerateSamplesContract (cv18HitAndRunOracles hn prep V) F hbounded params :=
  withNormalizedCV18Volume_samples_contract (hitAndRunSamplingOracles hn prep) V
    F hbounded params (hitAndRun_samples_contract hn prep F hbounded params)

theorem communityCV18HitAndRun_volume_contract {n k : Nat} (hn : 21 <= n)
    (prep : TTCPreprocessor n k) (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F)) (params : ApproxParams) :
    ComputeVolumeContract (communityCV18HitAndRunOracles hn prep) F hbounded params := by
  let D := prep.run F hbounded
  intro i
  have hcount : 0 < D.componentCount := lt_of_le_of_lt (Nat.zero_le i) i.isLt
  have heta0 : 0 < params.epsilonPrime :=
    div_pos params.epsilon_pos (by norm_num)
  have heta1 : params.epsilonPrime ≤ 1 := by
    dsimp only [ApproxParams.epsilonPrime]
    linarith [params.epsilon_le_one]
  have hdenom : 0 < (4 * D.componentCount : Real) := by
    exact_mod_cast Nat.mul_pos (by norm_num : 0 < 4) hcount
  have hdelta0 : 0 < params.deltaPrime D.componentCount := by
    exact div_pos params.delta_pos hdenom
  have hdelta1 : params.deltaPrime D.componentCount ≤ 1 := by
    dsimp only [ApproxParams.deltaPrime]
    rw [div_le_iff₀ hdenom]
    have hcountR : (1 : Real) ≤ D.componentCount := by exact_mod_cast hcount
    nlinarith [params.delta_le_one]
  simpa only [communityCV18HitAndRunOracles, hitAndRunSamplingOracles] using
    CommunityCV18.communityCV18VolumeLaw_spec (by omega) (D.component i)
      params.epsilonPrime (params.deltaPrime D.componentCount)
      ⟨heta0, heta1, hdelta0, hdelta1⟩

theorem communityCV18HitAndRun_samples_contract {n k : Nat} (hn : 21 <= n)
    (prep : TTCPreprocessor n k) (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F)) (params : ApproxParams) :
    GenerateSamplesContract (communityCV18HitAndRunOracles hn prep) F hbounded params := by
  simpa only [communityCV18HitAndRunOracles, GenerateSamplesContract] using
    hitAndRun_samples_contract hn prep F hbounded params

#print axioms cv18HitAndRun_volume_contract
#print axioms cv18HitAndRun_samples_contract
#print axioms communityCV18HitAndRun_volume_contract
#print axioms communityCV18HitAndRun_samples_contract

end Kr25Ssmxt
