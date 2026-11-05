import Kr25Ssmxt.Analysis.MathlibCompat
import Kr25Ssmxt.Analysis.NormalizedHitAndRunGeometry
import Kr25Ssmxt.Analysis.CostedMeasureMonad
import Kr25Ssmxt.Analysis.GeometricRetryExpectation

/-!
# Marginals of the charged manuscript oracles

The fixed CV18 budget charge and the random retry charge leave their output
distributions equal to the uncharged manuscript oracle laws.
-/

namespace Kr25Ssmxt

open MeasureTheory

theorem communityManuscriptCosted_volume_fst {n k : Nat} (hn : 21 ≤ n)
    (prep : TTCPreprocessor n k) (factor : Nat)
    (P : PolytopeData n) (eta delta : Real) :
    ((communityManuscriptCostedOracles hn prep factor).computeVolumeWithCost P eta delta).map
        Prod.fst =
      (communityManuscriptOracles hn prep).computeVolume P eta delta := by
  simp only [communityManuscriptCostedOracles]
  exact costedCharge_fst _ _

theorem communityManuscriptCosted_volume_expected_cost {n k : Nat}
    (hn : 21 ≤ n) (prep : TTCPreprocessor n k) (factor : Nat)
    (P : PolytopeData n) (eta delta : Real)
    [IsProbabilityMeasure
      ((communityManuscriptOracles hn prep).computeVolume P eta delta)] :
    ∫⁻ result, (result.2 : ENNReal) ∂
      (communityManuscriptCostedOracles hn prep factor).computeVolumeWithCost
        P eta delta =
      TTCRuntime.membershipQueryOperations n P.presentation.facetCount
        (CommunityCV18.queryBudgetFor (by omega) P eta delta) +
      factor * TTCRuntime.membershipQueryOperations n P.presentation.facetCount
        (CommunityCV18.queryBudgetFor (by omega) P eta delta + 1) := by
  simpa only [communityManuscriptCostedOracles, Nat.cast_add, Nat.cast_mul] using
    (costedCharge_expected_cost
    ((communityManuscriptOracles hn prep).computeVolume P eta delta)
    (TTCRuntime.membershipQueryOperations n P.presentation.facetCount
      (CommunityCV18.queryBudgetFor (by omega) P eta delta) +
      factor * TTCRuntime.membershipQueryOperations n P.presentation.facetCount
        (CommunityCV18.queryBudgetFor (by omega) P eta delta + 1)))

theorem communityManuscriptCosted_samples_fst {n k : Nat} (hn : 21 ≤ n)
    (prep : TTCPreprocessor n k) (factor : Nat)
    (P : PolytopeData n) (count b : Nat) (eta delta : Real) :
    ((communityManuscriptCostedOracles hn prep factor).generateSamplesWithCost
      P count b eta delta).map Prod.fst =
      (communityManuscriptOracles hn prep).generateSamples P count b eta delta := by
  classical
  by_cases h : 1 ≤ decimalScale b * P.inradius ∧ 0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧ (codedLatticePoints P b).Nonempty
  · have halmost := P.normalizedHitAndRun_latticePointLaw hn b h.1
      h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
    letI : IsProbabilityMeasure
        (acceptedRoundedLatticeLaw (normalizedHitAndRunContinuousLaw P b eta) P b) :=
      halmost.1
    simpa only [communityManuscriptCostedOracles, communityManuscriptOracles,
      dif_pos h, normalizedHitAndRunPointLaw] using
      normalizedHitAndRunBatchWithCostLaw_fst P count b eta
  · simpa only [communityManuscriptCostedOracles, communityManuscriptOracles,
      dif_neg h] using (costedCharge_fst (failedSampleBatchLaw (n := n) (count := count)) 0)

theorem communityManuscriptCosted_samples_expected_cost {n k : Nat}
    (hn : 21 ≤ n) (prep : TTCPreprocessor n k) (factor : Nat)
    (P : PolytopeData n) (count b : Nat) (eta delta : Real)
    (h : 1 ≤ decimalScale b * P.inradius ∧ 0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧ (codedLatticePoints P b).Nonempty)
    (haccept : (1 / 2 : Real) ≤
      (roundedAcceptanceProbability (normalizedHitAndRunContinuousLaw P b eta) P b : Real)) :
    ∫⁻ result, (result.2 : ENNReal) ∂
      (communityManuscriptCostedOracles hn prep factor).generateSamplesWithCost
        P count b eta delta ≤
      count * (2 * TTCRuntime.samplingAttemptOperations n
        P.presentation.facetCount (normalizedHitAndRunSteps P b eta)) := by
  have halmost := P.normalizedHitAndRun_latticePointLaw hn b h.1
    h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
  letI : IsProbabilityMeasure
      (acceptedRoundedLatticeLaw (normalizedHitAndRunContinuousLaw P b eta) P b) :=
    halmost.1
  simpa only [communityManuscriptCostedOracles, dif_pos h] using
    normalizedHitAndRunBatchWithCost_expected_bound P count b eta haccept

theorem communityManuscriptCosted_samples_mass_le_one {n k : Nat}
    (hn : 21 ≤ n) (prep : TTCPreprocessor n k) (factor : Nat)
    (P : PolytopeData n) (count b : Nat) (eta delta : Real)
    (h : 1 ≤ decimalScale b * P.inradius ∧ 0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧ (codedLatticePoints P b).Nonempty) :
    ((communityManuscriptCostedOracles hn prep factor).generateSamplesWithCost
      P count b eta delta) Set.univ ≤ 1 := by
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
  simpa only [communityManuscriptCostedOracles, dif_pos h] using
    hbatch

end Kr25Ssmxt
