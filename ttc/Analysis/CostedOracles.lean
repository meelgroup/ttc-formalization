import ttc.Analysis.MathlibCompat
import ttc.Analysis.NormalizedHitAndRunGeometry
import ttc.Analysis.CostedMeasureMonad
import ttc.Analysis.GeometricRetryExpectation

/-!
# Marginals of the charged paper oracles

The fixed CV18 budget charge and the random retry charge leave their output
distributions equal to the uncharged paper oracle laws.
-/

namespace ttc

open MeasureTheory

theorem communityCosted_volume_fst {n k : Nat} (hn : 21 ≤ n)
    (prep : TTCPreprocessor n k) (factor : Nat)
    (P : PolytopeData n) (eta delta : Real) :
    ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost P eta delta).map
        Prod.fst =
      (ttcSubroutines hn prep).ComputeVolume P eta delta := by
  simp only [ttcCostedSubroutines]
  exact costedCharge_fst _ _

theorem communityCosted_volume_expected_cost {n k : Nat}
    (hn : 21 ≤ n) (prep : TTCPreprocessor n k) (factor : Nat)
    (P : PolytopeData n) (eta delta : Real)
    [IsProbabilityMeasure
      ((ttcSubroutines hn prep).ComputeVolume P eta delta)] :
    ∫⁻ result, (result.2 : ENNReal) ∂
      (ttcCostedSubroutines hn prep factor).computeVolumeWithCost
        P eta delta =
      TTCRuntime.membershipQueryOperations n P.presentation.facetCount
        (CommunityCV18.queryBudgetFor (by omega) P eta delta) +
      factor * TTCRuntime.membershipQueryOperations n P.presentation.facetCount
        (CommunityCV18.queryBudgetFor (by omega) P eta delta + 1) := by
  simpa only [ttcCostedSubroutines, Nat.cast_add, Nat.cast_mul] using
    (costedCharge_expected_cost
    ((ttcSubroutines hn prep).ComputeVolume P eta delta)
    (TTCRuntime.membershipQueryOperations n P.presentation.facetCount
      (CommunityCV18.queryBudgetFor (by omega) P eta delta) +
      factor * TTCRuntime.membershipQueryOperations n P.presentation.facetCount
        (CommunityCV18.queryBudgetFor (by omega) P eta delta + 1)))

theorem communityCosted_samples_fst {n k : Nat} (hn : 21 ≤ n)
    (prep : TTCPreprocessor n k) (factor : Nat)
    (P : PolytopeData n) (count b : Nat) (eta delta : Real) :
    ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
      P count b eta).map Prod.fst =
      (ttcSubroutines hn prep).GenerateSamples P count b eta := by
  classical
  by_cases h : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧ 0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧ (codedLatticePoints P b).Nonempty
  · have halmost := P.normalizedHitAndRun_latticePointLaw hn b h.1
      h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
    letI : IsProbabilityMeasure
        (acceptedRoundedLatticeLaw (normalizedHitAndRunContinuousLaw P b eta) P b) :=
      halmost.1
    simpa only [ttcCostedSubroutines, ttcSubroutines,
      dif_pos h, normalizedHitAndRunPointLaw] using
      normalizedHitAndRunBatchWithCostLaw_fst P count b eta
  · simpa only [ttcCostedSubroutines, ttcSubroutines,
      dif_neg h] using (costedCharge_fst (failedSampleBatchLaw (n := n) (count := count)) 0)

theorem communityCosted_samples_expected_cost {n k : Nat}
    (hn : 21 ≤ n) (prep : TTCPreprocessor n k) (factor : Nat)
    (P : PolytopeData n) (count b : Nat) (eta delta : Real)
    (h : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧ 0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧ (codedLatticePoints P b).Nonempty)
    (haccept : (1 / 2 : Real) ≤
      (roundedAcceptanceProbability (normalizedHitAndRunContinuousLaw P b eta) P b : Real)) :
    ∫⁻ result, (result.2 : ENNReal) ∂
      (ttcCostedSubroutines hn prep factor).generateSamplesWithCost
        P count b eta ≤
      count * (2 * TTCRuntime.samplingAttemptOperations n
        P.presentation.facetCount (normalizedHitAndRunSteps P b eta)) := by
  have halmost := P.normalizedHitAndRun_latticePointLaw hn b h.1
    h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
  letI : IsProbabilityMeasure
      (acceptedRoundedLatticeLaw (normalizedHitAndRunContinuousLaw P b eta) P b) :=
    halmost.1
  simpa only [ttcCostedSubroutines, dif_pos h] using
    normalizedHitAndRunBatchWithCost_expected_bound P count b eta haccept

theorem communityCosted_samples_mass_le_one {n k : Nat}
    (hn : 21 ≤ n) (prep : TTCPreprocessor n k) (factor : Nat)
    (P : PolytopeData n) (count b : Nat) (eta delta : Real)
    (h : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧ 0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧ (codedLatticePoints P b).Nonempty) :
    ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
      P count b eta) Set.univ ≤ 1 := by
  have halmost := P.normalizedHitAndRun_latticePointLaw hn b h.1
    h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
  letI : IsProbabilityMeasure
      (acceptedRoundedLatticeLaw (normalizedHitAndRunContinuousLaw P b eta) P b) :=
    halmost.1
  letI : IsProbabilityMeasure
      (acceptedRoundedWithAttempts (normalizedHitAndRunContinuousLaw P b eta) P b) := by
    unfold acceptedRoundedWithAttempts
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  let μ := normalizedHitAndRunPointWithCostLaw P b eta
  letI : IsProbabilityMeasure μ := by
    unfold μ normalizedHitAndRunPointWithCostLaw
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  letI : ∀ _ : Fin count, IsProbabilityMeasure μ := fun _ => inferInstance
  have hbatch : (normalizedHitAndRunBatchWithCostLaw P count b eta) Set.univ ≤ 1 := by
    unfold normalizedHitAndRunBatchWithCostLaw
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
    simp
  simpa only [ttcCostedSubroutines, dif_pos h] using
    hbatch

end ttc
