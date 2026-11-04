import Kr25Ssmxt.Analysis.PoissonMean
import Kr25Ssmxt.Analysis.ScaledVolumeBridge
import Kr25Ssmxt.Analysis.TTCPaperRuntime

/-! Expected cost of the manuscript's adaptive rate and count thinning stages. -/

namespace Kr25Ssmxt

open MeasureTheory ProbabilityTheory

theorem PolytopeData.clipManuscriptVolume_le_max {n : Nat}
    (P : PolytopeData n) (eta : Real) (o : VolumeOutcome) :
    (P.clipManuscriptVolume eta o).2 ≤
      max (P.manuscriptVolumeLower eta) (P.manuscriptVolumeUpper eta) := by
  unfold PolytopeData.clipManuscriptVolume
  dsimp only
  exact max_le_max_left _ (min_le_left _ _)

theorem PolytopeData.measurable_clipManuscriptVolume {n : Nat}
    (P : PolytopeData n) (eta : Real) :
    Measurable (P.clipManuscriptVolume eta) := by
  unfold PolytopeData.clipManuscriptVolume
  fun_prop

theorem manuscriptIntensity_mono_volume (b n : Nat) (threshold : Real)
    {small large : NNReal} (hvol : small ≤ large) :
    manuscriptIntensity b n threshold small ≤
      manuscriptIntensity b n threshold large := by
  unfold manuscriptIntensity
  gcongr

theorem clipped_manuscriptRateThinningCost_le {n : Nat}
    (s : TTCState n) (P : PolytopeData n) (b : Nat)
    (threshold eta : Real) (hthreshold : 0 < threshold)
    (outcome : VolumeOutcome) :
    manuscriptRateThinningCost s
      (manuscriptIntensity b n threshold (P.clipManuscriptVolume eta outcome).2)
      threshold ≤
    manuscriptRateThinningCost s
      (manuscriptIntensity b n threshold
        (max (P.manuscriptVolumeLower eta) (P.manuscriptVolumeUpper eta)))
      threshold := by
  apply manuscriptRateThinningCost_mono_intensity s _ hthreshold
  exact manuscriptIntensity_mono_volume b n threshold
    (P.clipManuscriptVolume_le_max eta outcome)

theorem certified_community_volume_mass_le_one {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (i : Fin D.componentCount) :
    (communityCV18VolumeLaw (by omega) (D.component i) p.epsilonPrime
      (p.deltaPrime D.componentCount)) Set.univ ≤ 1 := by
  letI : IsProbabilityMeasure
      (communityCV18VolumeLaw (by omega) (D.component i) p.epsilonPrime
        (p.deltaPrime D.componentCount)) :=
    (CommunityCV18.communityCV18VolumeLaw_spec (by omega) (D.component i)
      p.epsilonPrime (p.deltaPrime D.componentCount)
      (PaperRuntime.ttc_request_admissible D p i)).1
  simp

theorem certified_community_volume_continuation_bound {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) (f : VolumeOutcome → ENNReal)
    {budget : ENNReal}
    (hbudget : ∀ outcome : VolumeOutcome,
      f ((D.component i).clipManuscriptVolume p.epsilonPrime outcome) ≤ budget) :
    (∫⁻ result, (result.2 : ENNReal) + f result.1 ∂
      (communityManuscriptCostedOracles hn prep factor).computeVolumeWithCost
        (D.component i) p.epsilonPrime (p.deltaPrime D.componentCount)) ≤
      (TTCRuntime.membershipQueryOperations n
          (D.component i).presentation.facetCount
          (CommunityCV18.queryBudgetFor (by omega) (D.component i)
            p.epsilonPrime (p.deltaPrime D.componentCount)) +
        factor * TTCRuntime.membershipQueryOperations n
          (D.component i).presentation.facetCount
          (CommunityCV18.queryBudgetFor (by omega) (D.component i)
            p.epsilonPrime (p.deltaPrime D.componentCount) + 1) : ENNReal) + budget := by
  have hbase := costedCharge_map_continuation_bound
    (communityCV18VolumeLaw (by omega) (D.component i) p.epsilonPrime
      (p.deltaPrime D.componentCount))
    ((D.component i).clipManuscriptVolume p.epsilonPrime)
    (TTCRuntime.membershipQueryOperations n
      (D.component i).presentation.facetCount
      (CommunityCV18.queryBudgetFor (by omega) (D.component i)
        p.epsilonPrime (p.deltaPrime D.componentCount)) +
      factor * TTCRuntime.membershipQueryOperations n
        (D.component i).presentation.facetCount
        (CommunityCV18.queryBudgetFor (by omega) (D.component i)
          p.epsilonPrime (p.deltaPrime D.componentCount) + 1))
    f (certified_community_volume_mass_le_one hn D p i) hbudget
  simpa only [communityManuscriptCostedOracles, communityManuscriptOracles,
    Nat.cast_add, Nat.cast_mul] using hbase

private noncomputable def componentNonVolumeBudget {n : Nat} (p : ApproxParams) (m b : Nat)
    (P : PolytopeData n) (state : TTCState n) : ENNReal :=
  let deleted := state.removeComponent P
  state.samples.card * (TTCRuntime.facetScanOperations n P.presentation.facetCount + 1) +
  manuscriptRateThinningCost deleted
    (manuscriptIntensity b n (p.threshold m)
      (max (P.manuscriptVolumeLower p.epsilonPrime)
        (P.manuscriptVolumeUpper p.epsilonPrime))) (p.threshold m) +
  TTCRuntime.poissonDrawOperations +
  4 * TTCRuntime.countThinningRoundOperations state.samples.card +
  (TTCRuntime.sampleCap p m : ENNReal) *
    (2 * TTCRuntime.samplingAttemptOperations n P.presentation.facetCount
      (normalizedHitAndRunSteps P b p.epsilonPrime) +
      TTCRuntime.appendCopyOperations)

private noncomputable def componentUniformBudget {n : Nat} (p : ApproxParams)
    (m b : Nat) (P : PolytopeData n) : ENNReal :=
  let cap := TTCRuntime.sampleCap p m
  let upperIntensity := manuscriptIntensity b n (p.threshold m)
    (max (P.manuscriptVolumeLower p.epsilonPrime)
      (P.manuscriptVolumeUpper p.epsilonPrime))
  cap * (TTCRuntime.facetScanOperations n P.presentation.facetCount + 1) +
  (Nat.clog 2 (Nat.ceil ((upperIntensity : Real) / p.threshold m) + 1) : ENNReal) *
    TTCRuntime.rateThinningRoundOperations cap +
  TTCRuntime.poissonDrawOperations +
  4 * TTCRuntime.countThinningRoundOperations cap +
  (cap : ENNReal) *
    (2 * TTCRuntime.samplingAttemptOperations n P.presentation.facetCount
      (normalizedHitAndRunSteps P b p.epsilonPrime) +
      TTCRuntime.appendCopyOperations)

private noncomputable def uniformComponentCost {n : Nat} (hn : 21 ≤ n)
    (p : ApproxParams) (m b factor : Nat) (P : PolytopeData n) : ENNReal :=
  (TTCRuntime.membershipQueryOperations n P.presentation.facetCount
      (CommunityCV18.queryBudgetFor (by omega) P p.epsilonPrime (p.deltaPrime m)) +
    factor * TTCRuntime.membershipQueryOperations n P.presentation.facetCount
      (CommunityCV18.queryBudgetFor (by omega) P p.epsilonPrime (p.deltaPrime m) + 1) :
      ENNReal) +
    componentUniformBudget p m b P

private theorem uniformComponentCost_eq_model {n : Nat} (hn : 21 ≤ n)
    (p : ApproxParams) (m b factor : Nat) (P : PolytopeData n) :
    uniformComponentCost hn p m b factor P =
      TTCRuntime.manuscriptExpectedComponentBudget hn p m b factor P := by
  unfold uniformComponentCost componentUniformBudget
    TTCRuntime.manuscriptExpectedComponentBudget
  simp only [Nat.cast_add, Nat.cast_mul, add_assoc]

theorem manuscriptRatePoissonCount_expected_cost_le {n : Nat}
    (s : TTCState n) (intensity : NNReal) (threshold : Real)
    (hthreshold : 0 < threshold)
    (hsamples : (s.samples.card : Real) ≤ threshold) :
    ∫⁻ result, (result.2 : ENNReal) ∂
      costedBind (manuscriptRateThinWithCost s intensity threshold)
        (fun firstThinned =>
          costedBind
            (costedCharge
              (poissonMeasure (intensity * firstThinned.rate))
              TTCRuntime.poissonDrawOperations)
            (fun pending => manuscriptCountThinWithCost firstThinned pending threshold)) ≤
      manuscriptRateThinningCost s intensity threshold +
        (TTCRuntime.poissonDrawOperations +
          4 * TTCRuntime.countThinningRoundOperations s.samples.card) := by
  let next : TTCState n → Measure ((TTCState n × Nat) × Nat) := fun firstThinned =>
    costedBind
      (costedCharge
        (poissonMeasure (intensity * firstThinned.rate))
        TTCRuntime.poissonDrawOperations)
      (fun pending => manuscriptCountThinWithCost firstThinned pending threshold)
  have hnextMass (firstThinned : TTCState n) :
      (next firstThinned) Set.univ ≤ 1 := by
    apply costedBind_mass_le_one
    · apply costedCharge_mass_le_one
      simp
    · intro pending
      exact manuscriptCountThinWithCost_mass_le_one firstThinned pending threshold
  apply (costedBind_lintegral_cost_le _ next hnextMass).trans
  unfold manuscriptRateThinWithCost
  apply (lintegral_map_le _ _).trans
  simp only
  rw [lintegral_add_left (by fun_prop)]
  haveI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  simp only [lintegral_const, measure_univ, mul_one]
  apply add_le_add_right
  calc
    _ ≤ ∫⁻ _coins : Nat × Nat → Bool,
        ((TTCRuntime.poissonDrawOperations : ENNReal) +
          4 * TTCRuntime.countThinningRoundOperations s.samples.card)
          ∂fairCoinStreamLaw := by
      apply lintegral_mono
      intro coins
      have hcard := manuscriptRateThinningResult_card_le s intensity threshold coins
      have hcardReal :
          ((manuscriptRateThinningResult s intensity threshold coins).samples.card : Real) ≤
            threshold := (Nat.cast_le.mpr hcard).trans hsamples
      have hguard := manuscriptRateThinningResult_guard s intensity hthreshold coins
      have hcost := manuscriptPoissonCountThin_expected_cost_le
        (manuscriptRateThinningResult s intensity threshold coins)
        (intensity * (manuscriptRateThinningResult s intensity threshold coins).rate)
        threshold hthreshold.le hcardReal hguard
      have hround :
          TTCRuntime.countThinningRoundOperations
              (manuscriptRateThinningResult s intensity threshold coins).samples.card ≤
            TTCRuntime.countThinningRoundOperations s.samples.card := by
        unfold TTCRuntime.countThinningRoundOperations TTCRuntime.fairCoinOperations
          TTCRuntime.binomialDrawOperations TTCRuntime.scalarOperationCost
        omega
      exact hcost.trans (add_le_add_right
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hround) (by positivity)) _)
    _ = _ := by simp

/-- Appending a generated batch adds exactly one charge per requested copy;
this bound composes with any certified sample oracle. -/
theorem manuscriptSampleAppend_expected_cost_le {n : Nat} {count : Nat}
    (state : TTCState n) (sampleLaw : Measure (SampleBatch n count × Nat))
    (hsampleMass : sampleLaw Set.univ ≤ 1)
    {sampleBudget : ENNReal}
    (hsampleCost : (∫⁻ result, (result.2 : ENNReal) ∂sampleLaw) ≤
      sampleBudget) :
    (∫⁻ result, (result.2 : ENNReal) ∂
      costedBind sampleLaw (fun batch =>
        costedCharge (Measure.dirac (state.addBatch batch.2))
          (count * TTCRuntime.appendCopyOperations))) ≤
      sampleBudget + count * TTCRuntime.appendCopyOperations := by
  apply costedBind_expected_cost_le_add sampleLaw _ hsampleMass
  · intro batch
    apply costedCharge_mass_le_one
    simp
  · exact hsampleCost
  · intro batch
    letI : IsProbabilityMeasure (Measure.dirac (state.addBatch batch.2)) :=
      inferInstance
    simpa only [Nat.cast_mul] using
      (costedCharge_expected_cost
        (Measure.dirac (state.addBatch batch.2))
        (count * TTCRuntime.appendCopyOperations)).le

theorem certified_community_sample_append_expected_cost {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.latticeEta p.epsilonPrime)
    (prep : TTCPreprocessor n k) (factor count : Nat)
    (delta : Real) (i : Fin D.componentCount) (state : TTCState n) :
    ∫⁻ result, (result.2 : ENNReal) ∂
      costedBind
        ((communityManuscriptCostedOracles hn prep factor).generateSamplesWithCost
          (D.component i) count b p.epsilonPrime delta)
        (fun batch => costedCharge (Measure.dirac (state.addBatch batch.2))
          (count * TTCRuntime.appendCopyOperations)) ≤
      count * (2 * TTCRuntime.samplingAttemptOperations n
        (D.component i).presentation.facetCount
        (normalizedHitAndRunSteps (D.component i) b p.epsilonPrime)) +
        count * TTCRuntime.appendCopyOperations := by
  exact manuscriptSampleAppend_expected_cost_le state _
    (certified_community_sampler_mass_le_one hn D p b hprecision prep factor
      count delta i)
    (certified_community_sampler_expected_cost hn D p b hprecision prep factor
      count delta i)

/-- One charged second loop, followed by the actual sampler and append,
costs at most its thinning charge plus the threshold-sized sampling budget. -/
theorem certified_count_sample_append_expected_cost {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.latticeEta p.epsilonPrime)
    (prep : TTCPreprocessor n k) (factor pending : Nat)
    (i : Fin D.componentCount) (state : TTCState n) :
    ∫⁻ result, (result.2 : ENNReal) ∂
      costedBind
        (manuscriptCountThinWithCost state pending (p.threshold D.componentCount))
        (fun secondThinned =>
          costedBind
            ((communityManuscriptCostedOracles hn prep factor).generateSamplesWithCost
              (D.component i) secondThinned.2 b p.epsilonPrime
              (p.deltaPrime D.componentCount))
            (fun batch => costedCharge
              (Measure.dirac (secondThinned.1.addBatch batch.2))
              (secondThinned.2 * TTCRuntime.appendCopyOperations))) ≤
      (∫⁻ result, (result.2 : ENNReal) ∂
        manuscriptCountThinWithCost state pending (p.threshold D.componentCount)) +
      (TTCRuntime.sampleCap p D.componentCount : ENNReal) *
        (2 * TTCRuntime.samplingAttemptOperations n
          (D.component i).presentation.facetCount
          (normalizedHitAndRunSteps (D.component i) b p.epsilonPrime) +
          TTCRuntime.appendCopyOperations) := by
  let threshold := p.threshold D.componentCount
  let stepCost : ENNReal := 2 * TTCRuntime.samplingAttemptOperations n
    (D.component i).presentation.facetCount
    (normalizedHitAndRunSteps (D.component i) b p.epsilonPrime) +
    TTCRuntime.appendCopyOperations
  let next : (TTCState n × Nat) → Measure (TTCState n × Nat) :=
    fun secondThinned =>
      costedBind
        ((communityManuscriptCostedOracles hn prep factor).generateSamplesWithCost
          (D.component i) secondThinned.2 b p.epsilonPrime
          (p.deltaPrime D.componentCount))
        (fun batch => costedCharge
          (Measure.dirac (secondThinned.1.addBatch batch.2))
          (secondThinned.2 * TTCRuntime.appendCopyOperations))
  have hnextMass (secondThinned : TTCState n × Nat) :
      (next secondThinned) Set.univ ≤ 1 := by
    apply costedBind_mass_le_one
    · exact certified_community_sampler_mass_le_one hn D p b hprecision
        prep factor secondThinned.2 (p.deltaPrime D.componentCount) i
    · intro batch
      apply costedCharge_mass_le_one
      simp
  apply (costedBind_lintegral_cost_le _ next hnextMass).trans
  rw [lintegral_add_left (by fun_prop)]
  apply add_le_add_right
  have hnextCost (secondThinned : TTCState n × Nat) :
      (∫⁻ result, (result.2 : ENNReal) ∂next secondThinned) ≤
        secondThinned.2 * stepCost := by
    have h := certified_community_sample_append_expected_cost hn D p b
      hprecision prep factor secondThinned.2 (p.deltaPrime D.componentCount)
      i secondThinned.1
    calc
      _ ≤ (secondThinned.2 : ENNReal) *
          (2 * TTCRuntime.samplingAttemptOperations n
            (D.component i).presentation.facetCount
            (normalizedHitAndRunSteps (D.component i) b p.epsilonPrime)) +
          (secondThinned.2 : ENNReal) * TTCRuntime.appendCopyOperations := h
      _ = secondThinned.2 * stepCost := by ring
  calc
    (∫⁻ result,
        (∫⁻ future, (future.2 : ENNReal) ∂next result.1) ∂
          manuscriptCountThinWithCost state pending threshold) ≤
      ∫⁻ result, (result.1.2 : ENNReal) * stepCost ∂
        manuscriptCountThinWithCost state pending threshold := by
      exact lintegral_mono (fun result => hnextCost result.1)
    _ ≤ ∫⁻ _result, (TTCRuntime.sampleCap p D.componentCount : ENNReal) *
        stepCost ∂manuscriptCountThinWithCost state pending threshold := by
      apply lintegral_mono_ae
      filter_upwards [manuscriptCountThinWithCost_population_le_ae state pending
        threshold (p.threshold_pos D.componentCount).le] with result hguard
      have hcount : result.1.2 ≤ TTCRuntime.sampleCap p D.componentCount := by
        have hreal : (result.1.2 : Real) ≤ threshold := by
          have hnonneg : (0 : Real) ≤ result.1.1.samples.card := by positivity
          exact (le_add_of_nonneg_left hnonneg).trans
            (by simpa only [Nat.cast_add] using hguard)
        exact_mod_cast hreal.trans (Nat.le_ceil threshold)
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcount) (by positivity)
    _ ≤ (TTCRuntime.sampleCap p D.componentCount : ENNReal) * stepCost := by
      simp only [lintegral_const]
      exact mul_le_of_le_one_right (by positivity)
        (manuscriptCountThinWithCost_mass_le_one state pending threshold)

theorem certified_count_sample_append_mass_le_one {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.latticeEta p.epsilonPrime)
    (prep : TTCPreprocessor n k) (factor pending : Nat)
    (i : Fin D.componentCount) (state : TTCState n) :
    (costedBind
      (manuscriptCountThinWithCost state pending (p.threshold D.componentCount))
      (fun secondThinned =>
        costedBind
          ((communityManuscriptCostedOracles hn prep factor).generateSamplesWithCost
            (D.component i) secondThinned.2 b p.epsilonPrime
            (p.deltaPrime D.componentCount))
          (fun batch => costedCharge
            (Measure.dirac (secondThinned.1.addBatch batch.2))
            (secondThinned.2 * TTCRuntime.appendCopyOperations)))) Set.univ ≤ 1 := by
  apply costedBind_mass_le_one
  · exact manuscriptCountThinWithCost_mass_le_one state pending _
  · intro secondThinned
    apply costedBind_mass_le_one
    · exact certified_community_sampler_mass_le_one hn D p b hprecision
        prep factor secondThinned.2 (p.deltaPrime D.componentCount) i
    · intro batch
      apply costedCharge_mass_le_one
      simp

/-- Poisson draw, count thinning, sampling and append have a per-component
budget once the first rate guard has been reached. -/
theorem certified_poisson_count_sample_expected_cost {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.latticeEta p.epsilonPrime)
    (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) (state : TTCState n) (rate : NNReal)
    (hsamples : (state.samples.card : Real) ≤ p.threshold D.componentCount)
    (hrate : (rate : Real) < p.threshold D.componentCount) :
    ∫⁻ result, (result.2 : ENNReal) ∂
      costedBind
        (costedCharge (poissonMeasure rate) TTCRuntime.poissonDrawOperations)
        (fun pending =>
          costedBind
            (manuscriptCountThinWithCost state pending (p.threshold D.componentCount))
            (fun secondThinned =>
              costedBind
                ((communityManuscriptCostedOracles hn prep factor).generateSamplesWithCost
                  (D.component i) secondThinned.2 b p.epsilonPrime
                  (p.deltaPrime D.componentCount))
                (fun batch => costedCharge
                  (Measure.dirac (secondThinned.1.addBatch batch.2))
                  (secondThinned.2 * TTCRuntime.appendCopyOperations)))) ≤
      TTCRuntime.poissonDrawOperations +
        4 * TTCRuntime.countThinningRoundOperations state.samples.card +
        (TTCRuntime.sampleCap p D.componentCount : ENNReal) *
          (2 * TTCRuntime.samplingAttemptOperations n
            (D.component i).presentation.facetCount
            (normalizedHitAndRunSteps (D.component i) b p.epsilonPrime) +
            TTCRuntime.appendCopyOperations) := by
  let threshold := p.threshold D.componentCount
  let sampleBudget : ENNReal := (TTCRuntime.sampleCap p D.componentCount : ENNReal) *
    (2 * TTCRuntime.samplingAttemptOperations n
      (D.component i).presentation.facetCount
      (normalizedHitAndRunSteps (D.component i) b p.epsilonPrime) +
      TTCRuntime.appendCopyOperations)
  let next : Nat → Measure (TTCState n × Nat) := fun pending =>
    costedBind (manuscriptCountThinWithCost state pending threshold)
      (fun secondThinned =>
        costedBind
          ((communityManuscriptCostedOracles hn prep factor).generateSamplesWithCost
            (D.component i) secondThinned.2 b p.epsilonPrime
            (p.deltaPrime D.componentCount))
          (fun batch => costedCharge
            (Measure.dirac (secondThinned.1.addBatch batch.2))
            (secondThinned.2 * TTCRuntime.appendCopyOperations)))
  have hnextMass (pending : Nat) : (next pending) Set.univ ≤ 1 :=
    certified_count_sample_append_mass_le_one hn D p b hprecision prep factor
      pending i state
  apply (costedBind_lintegral_cost_le _ next hnextMass).trans
  unfold costedCharge
  apply (lintegral_map_le _ _).trans
  simp only
  rw [lintegral_add_left (by fun_prop)]
  simp only [lintegral_const, measure_univ, mul_one]
  have hpoint (pending : Nat) :
      (∫⁻ result, (result.2 : ENNReal) ∂next pending) ≤
      (∫⁻ result, (result.2 : ENNReal) ∂
        manuscriptCountThinWithCost state pending threshold) + sampleBudget :=
    certified_count_sample_append_expected_cost hn D p b hprecision prep factor
      pending i state
  have hmean := poisson_averaged_countThinCost_le_four_of_guard state rate
    threshold (p.threshold_pos D.componentCount).le hsamples hrate
  calc
    _ ≤ (TTCRuntime.poissonDrawOperations : ENNReal) +
        ∫⁻ pending : Nat,
          ((∫⁻ result, (result.2 : ENNReal) ∂
              manuscriptCountThinWithCost state pending threshold) + sampleBudget)
            ∂poissonMeasure rate := by
      exact add_le_add_right (lintegral_mono hpoint) _
    _ = TTCRuntime.poissonDrawOperations +
        (∫⁻ pending : Nat, (∫⁻ result, (result.2 : ENNReal) ∂
          manuscriptCountThinWithCost state pending threshold) ∂poissonMeasure rate) +
        sampleBudget := by
      rw [lintegral_add_left (measurable_of_countable _)]
      simp only [lintegral_const, measure_univ, mul_one]
      ring
    _ ≤ _ := by
      simpa only [add_assoc] using
        add_le_add_right
          (add_le_add_left hmean sampleBudget)
          (TTCRuntime.poissonDrawOperations : ENNReal)

theorem certified_rate_poisson_count_sample_expected_cost {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.latticeEta p.epsilonPrime)
    (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) (state : TTCState n) (intensity : NNReal)
    (hsamples : (state.samples.card : Real) ≤ p.threshold D.componentCount) :
    ∫⁻ result, (result.2 : ENNReal) ∂
      costedBind
        (manuscriptRateThinWithCost state intensity (p.threshold D.componentCount))
        (fun firstThinned =>
          costedBind
            (costedCharge
              (poissonMeasure (intensity * firstThinned.rate))
              TTCRuntime.poissonDrawOperations)
            (fun pending =>
              costedBind
                (manuscriptCountThinWithCost firstThinned pending
                  (p.threshold D.componentCount))
                (fun secondThinned =>
                  costedBind
                    ((communityManuscriptCostedOracles hn prep factor).generateSamplesWithCost
                      (D.component i) secondThinned.2 b p.epsilonPrime
                      (p.deltaPrime D.componentCount))
                    (fun batch => costedCharge
                      (Measure.dirac (secondThinned.1.addBatch batch.2))
                      (secondThinned.2 * TTCRuntime.appendCopyOperations))))) ≤
      manuscriptRateThinningCost state intensity (p.threshold D.componentCount) +
        TTCRuntime.poissonDrawOperations +
        4 * TTCRuntime.countThinningRoundOperations state.samples.card +
        (TTCRuntime.sampleCap p D.componentCount : ENNReal) *
          (2 * TTCRuntime.samplingAttemptOperations n
            (D.component i).presentation.facetCount
            (normalizedHitAndRunSteps (D.component i) b p.epsilonPrime) +
            TTCRuntime.appendCopyOperations) := by
  let threshold := p.threshold D.componentCount
  let sampleBudget : ENNReal := (TTCRuntime.sampleCap p D.componentCount : ENNReal) *
    (2 * TTCRuntime.samplingAttemptOperations n
      (D.component i).presentation.facetCount
      (normalizedHitAndRunSteps (D.component i) b p.epsilonPrime) +
      TTCRuntime.appendCopyOperations)
  let next : TTCState n → Measure (TTCState n × Nat) := fun firstThinned =>
    costedBind
      (costedCharge
        (poissonMeasure (intensity * firstThinned.rate))
        TTCRuntime.poissonDrawOperations)
      (fun pending =>
        costedBind
          (manuscriptCountThinWithCost firstThinned pending threshold)
          (fun secondThinned =>
            costedBind
              ((communityManuscriptCostedOracles hn prep factor).generateSamplesWithCost
                (D.component i) secondThinned.2 b p.epsilonPrime
                (p.deltaPrime D.componentCount))
              (fun batch => costedCharge
                (Measure.dirac (secondThinned.1.addBatch batch.2))
                (secondThinned.2 * TTCRuntime.appendCopyOperations))))
  have hnextMass (firstThinned : TTCState n) :
      (next firstThinned) Set.univ ≤ 1 := by
    apply costedBind_mass_le_one
    · apply costedCharge_mass_le_one
      simp
    · intro pending
      exact certified_count_sample_append_mass_le_one hn D p b hprecision
        prep factor pending i firstThinned
  apply (costedBind_lintegral_cost_le _ next hnextMass).trans
  unfold manuscriptRateThinWithCost
  apply (lintegral_map_le _ _).trans
  simp only
  rw [lintegral_add_left (by fun_prop)]
  haveI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  simp only [lintegral_const, measure_univ, mul_one]
  simp only [add_assoc]
  apply add_le_add_right
  calc
    _ ≤ ∫⁻ _coins : Nat × Nat → Bool,
        ((TTCRuntime.poissonDrawOperations : ENNReal) +
          4 * TTCRuntime.countThinningRoundOperations state.samples.card +
          sampleBudget) ∂fairCoinStreamLaw := by
      apply lintegral_mono
      intro coins
      have hcard := manuscriptRateThinningResult_card_le state intensity threshold coins
      have hcardReal :
          ((manuscriptRateThinningResult state intensity threshold coins).samples.card :
            Real) ≤ threshold := (Nat.cast_le.mpr hcard).trans hsamples
      have hguard := manuscriptRateThinningResult_guard state intensity
        (p.threshold_pos D.componentCount) coins
      have hcost := certified_poisson_count_sample_expected_cost hn D p b
        hprecision prep factor i
        (manuscriptRateThinningResult state intensity threshold coins)
        (intensity * (manuscriptRateThinningResult state intensity threshold coins).rate)
        hcardReal hguard
      have hround :
          TTCRuntime.countThinningRoundOperations
              (manuscriptRateThinningResult state intensity threshold coins).samples.card ≤
            TTCRuntime.countThinningRoundOperations state.samples.card := by
        unfold TTCRuntime.countThinningRoundOperations TTCRuntime.fairCoinOperations
          TTCRuntime.binomialDrawOperations TTCRuntime.scalarOperationCost
        omega
      exact hcost.trans (add_le_add_left
        (add_le_add_right
          (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hround) (by positivity))
          (TTCRuntime.poissonDrawOperations : ENNReal)) sampleBudget)
    _ = _ := by
      simp only [lintegral_const, measure_univ, mul_one, sampleBudget, add_assoc]

theorem certified_rate_rest_mass_le_one {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.latticeEta p.epsilonPrime)
    (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) (state : TTCState n) (intensity : NNReal) :
    (costedBind
      (manuscriptRateThinWithCost state intensity (p.threshold D.componentCount))
      (fun firstThinned =>
        costedBind
          (costedCharge
            (poissonMeasure (intensity * firstThinned.rate))
            TTCRuntime.poissonDrawOperations)
          (fun pending =>
            costedBind
              (manuscriptCountThinWithCost firstThinned pending
                (p.threshold D.componentCount))
              (fun secondThinned =>
                costedBind
                  ((communityManuscriptCostedOracles hn prep factor).generateSamplesWithCost
                    (D.component i) secondThinned.2 b p.epsilonPrime
                    (p.deltaPrime D.componentCount))
                  (fun batch => costedCharge
                    (Measure.dirac (secondThinned.1.addBatch batch.2))
                    (secondThinned.2 * TTCRuntime.appendCopyOperations))))))
        Set.univ ≤ 1 := by
  apply costedBind_mass_le_one
  · exact manuscriptRateThinWithCost_mass_le_one state intensity _
  · intro firstThinned
    apply costedBind_mass_le_one
    · apply costedCharge_mass_le_one
      simp
    · intro pending
      exact certified_count_sample_append_mass_le_one hn D p b hprecision
        prep factor pending i firstThinned

/-- The deletion pass and all later stages, conditional on one clipped volume
estimate, have an explicit expected-operation bound. -/
theorem certified_deleted_component_expected_cost {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.latticeEta p.epsilonPrime)
    (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) (state : TTCState n) (volumeEstimate : NNReal)
    (hsamples : (state.samples.card : Real) ≤ p.threshold D.componentCount) :
    let deleted := state.removeComponent (D.component i)
    let intensity := manuscriptIntensity b n (p.threshold D.componentCount) volumeEstimate
    let deletionCost := TTCRuntime.deletionPassOperations n
      (D.component i).presentation.facetCount state.samples.card
      (state.samples.card - deleted.samples.card)
    ∫⁻ result, (result.2 : ENNReal) ∂
      costedBind (costedCharge (Measure.dirac deleted) deletionCost)
        (fun deleted =>
          costedBind
            (manuscriptRateThinWithCost deleted intensity
              (p.threshold D.componentCount))
            (fun firstThinned =>
              costedBind
                (costedCharge
                  (poissonMeasure (intensity * firstThinned.rate))
                  TTCRuntime.poissonDrawOperations)
                (fun pending =>
                  costedBind
                    (manuscriptCountThinWithCost firstThinned pending
                      (p.threshold D.componentCount))
                    (fun secondThinned =>
                      costedBind
                        ((communityManuscriptCostedOracles hn prep factor).generateSamplesWithCost
                          (D.component i) secondThinned.2 b p.epsilonPrime
                          (p.deltaPrime D.componentCount))
                        (fun batch => costedCharge
                          (Measure.dirac (secondThinned.1.addBatch batch.2))
                          (secondThinned.2 * TTCRuntime.appendCopyOperations)))))) ≤
      deletionCost +
        manuscriptRateThinningCost deleted intensity (p.threshold D.componentCount) +
        TTCRuntime.poissonDrawOperations +
        4 * TTCRuntime.countThinningRoundOperations deleted.samples.card +
        (TTCRuntime.sampleCap p D.componentCount : ENNReal) *
          (2 * TTCRuntime.samplingAttemptOperations n
            (D.component i).presentation.facetCount
            (normalizedHitAndRunSteps (D.component i) b p.epsilonPrime) +
            TTCRuntime.appendCopyOperations) := by
  dsimp only
  let deleted := state.removeComponent (D.component i)
  let intensity := manuscriptIntensity b n (p.threshold D.componentCount) volumeEstimate
  let deletionCost := TTCRuntime.deletionPassOperations n
    (D.component i).presentation.facetCount state.samples.card
    (state.samples.card - deleted.samples.card)
  let next : TTCState n → Measure (TTCState n × Nat) := fun deleted =>
    costedBind
      (manuscriptRateThinWithCost deleted intensity (p.threshold D.componentCount))
      (fun firstThinned =>
        costedBind
          (costedCharge
            (poissonMeasure (intensity * firstThinned.rate))
            TTCRuntime.poissonDrawOperations)
          (fun pending =>
            costedBind
              (manuscriptCountThinWithCost firstThinned pending
                (p.threshold D.componentCount))
              (fun secondThinned =>
                costedBind
                  ((communityManuscriptCostedOracles hn prep factor).generateSamplesWithCost
                    (D.component i) secondThinned.2 b p.epsilonPrime
                    (p.deltaPrime D.componentCount))
                  (fun batch => costedCharge
                    (Measure.dirac (secondThinned.1.addBatch batch.2))
                    (secondThinned.2 * TTCRuntime.appendCopyOperations)))))
  have hmass (x : TTCState n) : (next x) Set.univ ≤ 1 :=
    certified_rate_rest_mass_le_one hn D p b hprecision prep factor i x intensity
  have hdeleted : (deleted.samples.card : Real) ≤ p.threshold D.componentCount :=
    (Nat.cast_le.mpr (TTCState.removeComponent_card_le state (D.component i))).trans
      hsamples
  have hcost := certified_rate_poisson_count_sample_expected_cost hn D p b
    hprecision prep factor i deleted intensity hdeleted
  have hstep := costedBind_charge_dirac_expected_cost_le deleted deletionCost next hmass
  calc
    _ ≤ (deletionCost : ENNReal) +
        (∫⁻ result, (result.2 : ENNReal) ∂next deleted) := hstep
    _ ≤ (deletionCost : ENNReal) +
        ((manuscriptRateThinningCost deleted intensity
          (p.threshold D.componentCount) : ENNReal) +
          TTCRuntime.poissonDrawOperations +
          4 * TTCRuntime.countThinningRoundOperations deleted.samples.card +
          (TTCRuntime.sampleCap p D.componentCount : ENNReal) *
            (2 * TTCRuntime.samplingAttemptOperations n
              (D.component i).presentation.facetCount
              (normalizedHitAndRunSteps (D.component i) b p.epsilonPrime) +
              TTCRuntime.appendCopyOperations)) := add_le_add_right hcost _
    _ = _ := by simp only [deletionCost, deleted, intensity, add_assoc]

theorem certified_deleted_component_expected_cost_le_budget {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.latticeEta p.epsilonPrime)
    (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) (state : TTCState n) (outcome : VolumeOutcome)
    (hsamples : (state.samples.card : Real) ≤ p.threshold D.componentCount) :
    let P := D.component i
    let deleted := state.removeComponent P
    let intensity := manuscriptIntensity b n (p.threshold D.componentCount)
      (P.clipManuscriptVolume p.epsilonPrime outcome).2
    let deletionCost := TTCRuntime.deletionPassOperations n
      P.presentation.facetCount state.samples.card
      (state.samples.card - deleted.samples.card)
    ∫⁻ result, (result.2 : ENNReal) ∂
      costedBind (costedCharge (Measure.dirac deleted) deletionCost)
        (fun deleted =>
          costedBind
            (manuscriptRateThinWithCost deleted intensity
              (p.threshold D.componentCount))
            (fun firstThinned =>
              costedBind
                (costedCharge
                  (poissonMeasure (intensity * firstThinned.rate))
                  TTCRuntime.poissonDrawOperations)
                (fun pending =>
                  costedBind
                    (manuscriptCountThinWithCost firstThinned pending
                      (p.threshold D.componentCount))
                    (fun secondThinned =>
                      costedBind
                        ((communityManuscriptCostedOracles hn prep factor).generateSamplesWithCost
                          P secondThinned.2 b p.epsilonPrime
                          (p.deltaPrime D.componentCount))
                        (fun batch => costedCharge
                          (Measure.dirac (secondThinned.1.addBatch batch.2))
                          (secondThinned.2 * TTCRuntime.appendCopyOperations)))))) ≤
      componentNonVolumeBudget p D.componentCount b P state := by
  dsimp only
  let P := D.component i
  let deleted := state.removeComponent P
  let intensity := manuscriptIntensity b n (p.threshold D.componentCount)
    (P.clipManuscriptVolume p.epsilonPrime outcome).2
  have hbase := certified_deleted_component_expected_cost hn D p b hprecision
    prep factor i state (P.clipManuscriptVolume p.epsilonPrime outcome).2 hsamples
  have hdeletion := deletionPassOperations_le state P
  have hrate := clipped_manuscriptRateThinningCost_le deleted P b
    (p.threshold D.componentCount) p.epsilonPrime
    (p.threshold_pos D.componentCount) outcome
  have hcount :
      TTCRuntime.countThinningRoundOperations deleted.samples.card ≤
        TTCRuntime.countThinningRoundOperations state.samples.card := by
    have hcard : deleted.samples.card ≤ state.samples.card := by
      simpa only [deleted] using TTCState.removeComponent_card_le state P
    unfold TTCRuntime.countThinningRoundOperations TTCRuntime.fairCoinOperations
      TTCRuntime.binomialDrawOperations TTCRuntime.scalarOperationCost
    omega
  calc
    _ ≤ (TTCRuntime.deletionPassOperations n P.presentation.facetCount
          state.samples.card (state.samples.card - deleted.samples.card) : ENNReal) +
        manuscriptRateThinningCost deleted intensity (p.threshold D.componentCount) +
        TTCRuntime.poissonDrawOperations +
        4 * TTCRuntime.countThinningRoundOperations deleted.samples.card +
        (TTCRuntime.sampleCap p D.componentCount : ENNReal) *
          (2 * TTCRuntime.samplingAttemptOperations n P.presentation.facetCount
            (normalizedHitAndRunSteps P b p.epsilonPrime) +
            TTCRuntime.appendCopyOperations) := hbase
    _ ≤ componentNonVolumeBudget p D.componentCount b P state := by
      dsimp only [componentNonVolumeBudget]
      gcongr
      exact_mod_cast hdeletion

private theorem componentNonVolumeBudget_le_uniform {n : Nat}
    (p : ApproxParams) (m b : Nat) (P : PolytopeData n)
    (state : TTCState n)
    (hcard : (state.samples.card : Real) ≤ p.threshold m)
    (hrate : state.rate ≤ 1) :
    componentNonVolumeBudget p m b P state ≤
      componentUniformBudget p m b P := by
  let cap := TTCRuntime.sampleCap p m
  let deleted := state.removeComponent P
  let upperIntensity := manuscriptIntensity b n (p.threshold m)
    (max (P.manuscriptVolumeLower p.epsilonPrime)
      (P.manuscriptVolumeUpper p.epsilonPrime))
  have hcap : state.samples.card ≤ cap := by
    exact_mod_cast hcard.trans (Nat.le_ceil (p.threshold m))
  have hdeleted : deleted.samples.card ≤ cap :=
    (TTCState.removeComponent_card_le state P).trans hcap
  have hrateDeleted : deleted.rate ≤ 1 := by
    simpa only [deleted, TTCState.removeComponent] using hrate
  have hmeanNN : upperIntensity * deleted.rate ≤ upperIntensity := by
    calc
      upperIntensity * deleted.rate ≤ upperIntensity * 1 :=
        mul_le_mul_of_nonneg_left hrateDeleted (by positivity)
      _ = upperIntensity := mul_one _
  have hmean : ((upperIntensity * deleted.rate : NNReal) : Real) /
      p.threshold m ≤ (upperIntensity : Real) / p.threshold m := by
    apply div_le_div_of_nonneg_right
    · exact_mod_cast hmeanNN
    · exact (p.threshold_pos m).le
  have hlog : Nat.clog 2
      (Nat.ceil (((upperIntensity * deleted.rate : NNReal) : Real) /
        p.threshold m) + 1) ≤
      Nat.clog 2 (Nat.ceil ((upperIntensity : Real) / p.threshold m) + 1) := by
    apply Nat.clog_mono_right
    exact Nat.add_le_add_right (Nat.ceil_mono hmean) 1
  have hrateCost : manuscriptRateThinningCost deleted upperIntensity
      (p.threshold m) ≤
      Nat.clog 2 (Nat.ceil ((upperIntensity : Real) / p.threshold m) + 1) *
        TTCRuntime.rateThinningRoundOperations cap := by
    calc
      _ ≤ Nat.clog 2 (Nat.ceil (((upperIntensity * deleted.rate : NNReal) : Real) /
            p.threshold m) + 1) *
          TTCRuntime.rateThinningRoundOperations deleted.samples.card :=
        manuscriptRateThinningCost_le_clog deleted upperIntensity (p.threshold_pos m)
      _ ≤ Nat.clog 2 (Nat.ceil ((upperIntensity : Real) / p.threshold m) + 1) *
          TTCRuntime.rateThinningRoundOperations cap := by
        have hround : TTCRuntime.rateThinningRoundOperations deleted.samples.card ≤
            TTCRuntime.rateThinningRoundOperations cap := by
          unfold TTCRuntime.rateThinningRoundOperations TTCRuntime.fairCoinOperations
            TTCRuntime.scalarOperationCost
          omega
        exact Nat.mul_le_mul hlog hround
  have hdelete : state.samples.card *
      (TTCRuntime.facetScanOperations n P.presentation.facetCount + 1) ≤
      cap * (TTCRuntime.facetScanOperations n P.presentation.facetCount + 1) :=
    Nat.mul_le_mul_right _ hcap
  have hcount : TTCRuntime.countThinningRoundOperations state.samples.card ≤
      TTCRuntime.countThinningRoundOperations cap := by
    unfold TTCRuntime.countThinningRoundOperations TTCRuntime.fairCoinOperations
      TTCRuntime.binomialDrawOperations TTCRuntime.scalarOperationCost
    omega
  unfold componentNonVolumeBudget componentUniformBudget
  dsimp only
  gcongr
  · exact_mod_cast hrateCost

theorem certified_manuscript_component_expected_cost {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.latticeEta p.epsilonPrime)
    (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) (state : TTCState n)
    (hsamples : (state.samples.card : Real) ≤ p.threshold D.componentCount) :
    ∫⁻ result, (result.2 : ENNReal) ∂
      manuscriptProcessComponentWithCost
        (communityManuscriptCostedOracles hn prep factor) b p.epsilonPrime
        (p.deltaPrime D.componentCount) (p.threshold D.componentCount)
        (D.component i) state ≤
      (TTCRuntime.membershipQueryOperations n
          (D.component i).presentation.facetCount
          (CommunityCV18.queryBudgetFor (by omega) (D.component i)
            p.epsilonPrime (p.deltaPrime D.componentCount)) +
        factor * TTCRuntime.membershipQueryOperations n
          (D.component i).presentation.facetCount
          (CommunityCV18.queryBudgetFor (by omega) (D.component i)
            p.epsilonPrime (p.deltaPrime D.componentCount) + 1) : ENNReal) +
        componentNonVolumeBudget p D.componentCount b (D.component i) state := by
  let P := D.component i
  let O := communityManuscriptCostedOracles hn prep factor
  let step : VolumeOutcome → Measure (TTCState n × Nat) := fun volumeOutcome =>
    let intensity := manuscriptIntensity b n (p.threshold D.componentCount)
      volumeOutcome.2
    let deleted := state.removeComponent P
    let deletionCost := TTCRuntime.deletionPassOperations n
      P.presentation.facetCount state.samples.card
      (state.samples.card - deleted.samples.card)
    costedBind (costedCharge (Measure.dirac deleted) deletionCost)
      (fun deleted =>
        costedBind
          (manuscriptRateThinWithCost deleted intensity
            (p.threshold D.componentCount))
          (fun firstThinned =>
            costedBind
              (costedCharge
                (poissonMeasure (intensity * firstThinned.rate))
                TTCRuntime.poissonDrawOperations)
              (fun pending =>
                costedBind
                  (manuscriptCountThinWithCost firstThinned pending
                    (p.threshold D.componentCount))
                  (fun secondThinned =>
                    costedBind
                      (O.generateSamplesWithCost P secondThinned.2 b p.epsilonPrime
                        (p.deltaPrime D.componentCount))
                      (fun batch => costedCharge
                        (Measure.dirac (secondThinned.1.addBatch batch.2))
                        (secondThinned.2 * TTCRuntime.appendCopyOperations))))))
  have hstepMass (volumeOutcome : VolumeOutcome) :
      (step volumeOutcome) Set.univ ≤ 1 := by
    dsimp only [step]
    apply costedBind_mass_le_one
    · apply costedCharge_mass_le_one
      simp
    · intro deleted
      exact certified_rate_rest_mass_le_one hn D p b hprecision prep factor
        i deleted (manuscriptIntensity b n (p.threshold D.componentCount)
          volumeOutcome.2)
  have hstepCost (outcome : VolumeOutcome) :
      (∫⁻ result, (result.2 : ENNReal) ∂
        step (P.clipManuscriptVolume p.epsilonPrime outcome)) ≤
        componentNonVolumeBudget p D.componentCount b P state := by
    exact certified_deleted_component_expected_cost_le_budget hn D p b hprecision
      prep factor i state outcome hsamples
  change (∫⁻ result, (result.2 : ENNReal) ∂
    costedBind (O.computeVolumeWithCost P p.epsilonPrime
      (p.deltaPrime D.componentCount)) step) ≤ _
  apply (costedBind_lintegral_cost_le _ step hstepMass).trans
  exact certified_community_volume_continuation_bound hn D p prep factor i
    (fun outcome => ∫⁻ result, (result.2 : ENNReal) ∂step outcome)
    hstepCost

theorem certified_manuscript_component_expected_cost_uniform {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.latticeEta p.epsilonPrime)
    (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) (state : TTCState n)
    (hcard : (state.samples.card : Real) ≤ p.threshold D.componentCount)
    (hrate : state.rate ≤ 1) :
    ∫⁻ result, (result.2 : ENNReal) ∂
      manuscriptProcessComponentWithCost
        (communityManuscriptCostedOracles hn prep factor) b p.epsilonPrime
        (p.deltaPrime D.componentCount) (p.threshold D.componentCount)
        (D.component i) state ≤
      (TTCRuntime.membershipQueryOperations n
          (D.component i).presentation.facetCount
          (CommunityCV18.queryBudgetFor (by omega) (D.component i)
            p.epsilonPrime (p.deltaPrime D.componentCount)) +
        factor * TTCRuntime.membershipQueryOperations n
          (D.component i).presentation.facetCount
          (CommunityCV18.queryBudgetFor (by omega) (D.component i)
            p.epsilonPrime (p.deltaPrime D.componentCount) + 1) : ENNReal) +
        componentUniformBudget p D.componentCount b (D.component i) := by
  apply (certified_manuscript_component_expected_cost hn D p b hprecision prep
    factor i state hcard).trans
  exact add_le_add_right
    (componentNonVolumeBudget_le_uniform p D.componentCount b (D.component i)
      state hcard hrate) _

theorem certified_manuscript_component_mass_le_one {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.latticeEta p.epsilonPrime)
    (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) (state : TTCState n) :
    (manuscriptProcessComponentWithCost
      (communityManuscriptCostedOracles hn prep factor) b p.epsilonPrime
      (p.deltaPrime D.componentCount) (p.threshold D.componentCount)
      (D.component i) state) Set.univ ≤ 1 := by
  have hcv : (communityCV18VolumeLaw (by omega) (D.component i)
      p.epsilonPrime (p.deltaPrime D.componentCount)) Set.univ ≤ 1 :=
    certified_community_volume_mass_le_one hn D p i
  have hvol :
      ((communityManuscriptCostedOracles hn prep factor).computeVolumeWithCost
        (D.component i) p.epsilonPrime
        (p.deltaPrime D.componentCount)) Set.univ ≤ 1 := by
    apply costedCharge_mass_le_one
    dsimp only [communityManuscriptOracles]
    rw [Measure.map_apply
      ((D.component i).measurable_clipManuscriptVolume p.epsilonPrime)
      MeasurableSet.univ]
    simpa using hcv
  unfold manuscriptProcessComponentWithCost
  apply costedBind_mass_le_one _ _ hvol
  intro volumeOutcome
  apply costedBind_mass_le_one
  · apply costedCharge_mass_le_one
    simp
  · intro deleted
    exact certified_rate_rest_mass_le_one hn D p b hprecision prep factor
      i deleted (manuscriptIntensity b n (p.threshold D.componentCount)
        volumeOutcome.2)

/-- The concrete charged manuscript component has a deterministic expected
budget once its incoming stored population is below the TTC threshold. -/
private theorem measurableSet_state_card_le {n : Nat} (threshold : Real) :
    MeasurableSet {state : TTCState n | (state.samples.card : Real) ≤ threshold} := by
  have hcoords : Measurable (fun state : TTCState n =>
      (state.rate, state.samples, state.nextLabel)) := comap_measurable _
  have hsamples : Measurable (fun state : TTCState n => state.samples) :=
    (measurable_fst.comp measurable_snd).comp hcoords
  have hcard : Measurable (fun state : TTCState n => state.samples.card) :=
    (measurable_of_countable (fun copies : Finset (SampleCopy n) => copies.card)).comp
      hsamples
  exact ((measurable_of_countable (fun q : Nat => (q : Real))).comp hcard)
    measurableSet_Iic

private theorem measurableSet_state_rate_le_one {n : Nat} :
    MeasurableSet {state : TTCState n | state.rate ≤ 1} := by
  have hcoords : Measurable (fun state : TTCState n =>
      (state.rate, state.samples, state.nextLabel)) := comap_measurable _
  have hrate : Measurable (fun state : TTCState n => state.rate) :=
    measurable_fst.comp hcoords
  exact hrate measurableSet_Iic

private theorem manuscriptRateThinningResult_rate_le_one {n : Nat}
    (state : TTCState n) (intensity : NNReal) (threshold : Real)
    (coins : Nat × Nat → Bool) (hrate : state.rate ≤ 1) :
    (manuscriptRateThinningResult state intensity threshold coins).rate ≤ 1 := by
  dsimp only [manuscriptRateThinningResult]
  have hdenom : (1 : NNReal) ≤ (2 : NNReal) ^ manuscriptRateExit state intensity
      threshold := one_le_pow₀ (by norm_num)
  exact (div_le_self (by positivity) hdenom).trans hrate

private theorem manuscriptRateThinWithCost_rate_le_one_ae {n : Nat}
    (state : TTCState n) (intensity : NNReal) (threshold : Real)
    (hrate : state.rate ≤ 1) :
    ∀ᵐ result ∂manuscriptRateThinWithCost state intensity threshold,
      result.1.rate ≤ 1 := by
  have hset : MeasurableSet {s : TTCState n | s.rate ≤ 1} :=
    measurableSet_state_rate_le_one
  have hbase : ∀ᵐ result ∂manuscriptRateThinUntil state intensity threshold,
      result.rate ≤ 1 := by
    unfold manuscriptRateThinUntil
    rw [ae_map_iff
      (measurable_manuscriptRateThinningResult state intensity threshold).aemeasurable
      hset]
    exact Filter.Eventually.of_forall fun coins =>
      manuscriptRateThinningResult_rate_le_one state intensity threshold coins hrate
  rw [← manuscriptRateThinWithCost_fst state intensity threshold] at hbase
  exact (ae_map_iff measurable_fst.aemeasurable hset).mp hbase

private theorem manuscriptCountThinWithCost_rate_le_one_ae {n : Nat}
    (state : TTCState n) (pending : Nat) (threshold : Real)
    (hrate : state.rate ≤ 1) :
    ∀ᵐ result ∂manuscriptCountThinWithCost state pending threshold,
      result.1.1.rate ≤ 1 := by
  have hset : MeasurableSet {result : TTCState n × Nat | result.1.rate ≤ 1} :=
    (measurableSet_state_rate_le_one).preimage measurable_fst
  have hbase : ∀ᵐ result ∂thinUntil state pending threshold,
      result.1.rate ≤ 1 := by
    unfold thinUntil
    rw [ae_map_iff (measurable_thinningResult state pending threshold).aemeasurable
      hset]
    apply Filter.Eventually.of_forall
    intro coins
    dsimp only [thinningResult]
    have hdenom : (1 : NNReal) ≤
        (2 : NNReal) ^ firstExitRound state pending threshold coins :=
      one_le_pow₀ (by norm_num)
    exact (div_le_self (by positivity) hdenom).trans hrate
  rw [← manuscriptCountThinWithCost_fst state pending threshold] at hbase
  exact (ae_map_iff measurable_fst.aemeasurable hset).mp hbase

private theorem sample_append_card_le_ae {n : Nat} {count : Nat}
    (state : TTCState n) (threshold : Real)
    (hguard : ((state.samples.card + count : Nat) : Real) ≤ threshold)
    (sampleLaw : Measure (SampleBatch n count × Nat)) :
    ∀ᵐ result ∂costedBind sampleLaw
      (fun batch => costedCharge (Measure.dirac (state.addBatch batch.2))
        (count * TTCRuntime.appendCopyOperations)),
      (result.1.samples.card : Real) ≤ threshold := by
  apply costedBind_ae_state_of_ae sampleLaw _ (fun _ => True)
    (fun s : TTCState n => (s.samples.card : Real) ≤ threshold)
    (measurableSet_state_card_le threshold)
  · exact Filter.Eventually.of_forall (fun _ => trivial)
  · intro batch _
    apply costedCharge_dirac_ae_state _ _ _
      (measurableSet_state_card_le threshold)
    have hcard := TTCState.addBatch_card_le state batch.2
    exact (Nat.cast_le.mpr hcard).trans hguard

private theorem count_sample_append_card_le_ae {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat) (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) (state : TTCState n) (pending : Nat) :
    ∀ᵐ result ∂
      costedBind
        (manuscriptCountThinWithCost state pending (p.threshold D.componentCount))
        (fun secondThinned =>
          costedBind
            ((communityManuscriptCostedOracles hn prep factor).generateSamplesWithCost
              (D.component i) secondThinned.2 b p.epsilonPrime
              (p.deltaPrime D.componentCount))
            (fun batch => costedCharge
              (Measure.dirac (secondThinned.1.addBatch batch.2))
              (secondThinned.2 * TTCRuntime.appendCopyOperations))),
        (result.1.samples.card : Real) ≤ p.threshold D.componentCount := by
  apply costedBind_ae_state_of_ae _ _
    (fun secondThinned : TTCState n × Nat =>
      ((secondThinned.1.samples.card + secondThinned.2 : Nat) : Real) ≤
        p.threshold D.componentCount)
    (fun s : TTCState n => (s.samples.card : Real) ≤ p.threshold D.componentCount)
    (measurableSet_state_card_le _)
  · exact manuscriptCountThinWithCost_population_le_ae state pending _
      (p.threshold_pos D.componentCount).le
  · intro secondThinned hguard
    exact sample_append_card_le_ae secondThinned.1
      (p.threshold D.componentCount) hguard _

theorem certified_manuscript_component_card_le_ae {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat) (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) (state : TTCState n) :
    ∀ᵐ result ∂
      manuscriptProcessComponentWithCost
        (communityManuscriptCostedOracles hn prep factor) b p.epsilonPrime
        (p.deltaPrime D.componentCount) (p.threshold D.componentCount)
        (D.component i) state,
      (result.1.samples.card : Real) ≤ p.threshold D.componentCount := by
  unfold manuscriptProcessComponentWithCost
  apply costedBind_ae_state_of_forall _ _
    (fun s : TTCState n => (s.samples.card : Real) ≤ p.threshold D.componentCount)
    (measurableSet_state_card_le _)
  intro volumeOutcome
  dsimp only
  apply costedBind_ae_state_of_forall _ _
    (fun s : TTCState n => (s.samples.card : Real) ≤ p.threshold D.componentCount)
    (measurableSet_state_card_le _)
  intro deleted
  apply costedBind_ae_state_of_forall _ _
    (fun s : TTCState n => (s.samples.card : Real) ≤ p.threshold D.componentCount)
    (measurableSet_state_card_le _)
  intro firstThinned
  apply costedBind_ae_state_of_forall _ _
    (fun s : TTCState n => (s.samples.card : Real) ≤ p.threshold D.componentCount)
    (measurableSet_state_card_le _)
  intro pending
  exact count_sample_append_card_le_ae hn D p b prep factor i firstThinned pending

private theorem sample_append_rate_le_one_ae {n : Nat} {count : Nat}
    (state : TTCState n) (sampleLaw : Measure (SampleBatch n count × Nat))
    (hrate : state.rate ≤ 1) :
    ∀ᵐ result ∂costedBind sampleLaw
      (fun batch => costedCharge (Measure.dirac (state.addBatch batch.2))
        (count * TTCRuntime.appendCopyOperations)),
      result.1.rate ≤ 1 := by
  apply costedBind_ae_state_of_forall _ _
    (fun s : TTCState n => s.rate ≤ 1) measurableSet_state_rate_le_one
  intro batch
  apply costedCharge_dirac_ae_state _ _ _ measurableSet_state_rate_le_one
  simpa only [TTCState.addBatch] using hrate

private theorem count_sample_append_rate_le_one_ae {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat) (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) (state : TTCState n) (pending : Nat)
    (hrate : state.rate ≤ 1) :
    ∀ᵐ result ∂
      costedBind
        (manuscriptCountThinWithCost state pending (p.threshold D.componentCount))
        (fun secondThinned =>
          costedBind
            ((communityManuscriptCostedOracles hn prep factor).generateSamplesWithCost
              (D.component i) secondThinned.2 b p.epsilonPrime
              (p.deltaPrime D.componentCount))
            (fun batch => costedCharge
              (Measure.dirac (secondThinned.1.addBatch batch.2))
              (secondThinned.2 * TTCRuntime.appendCopyOperations))),
        result.1.rate ≤ 1 := by
  apply costedBind_ae_state_of_ae _ _
    (fun secondThinned : TTCState n × Nat => secondThinned.1.rate ≤ 1)
    (fun s : TTCState n => s.rate ≤ 1) measurableSet_state_rate_le_one
  · exact manuscriptCountThinWithCost_rate_le_one_ae state pending _ hrate
  · intro secondThinned hsecond
    exact sample_append_rate_le_one_ae secondThinned.1 _ hsecond

private theorem poisson_count_sample_rate_le_one_ae {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat) (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) (state : TTCState n) (intensity : NNReal)
    (hrate : state.rate ≤ 1) :
    ∀ᵐ result ∂costedBind
      (costedCharge (poissonMeasure (intensity * state.rate))
        TTCRuntime.poissonDrawOperations)
      (fun pending =>
        costedBind
          (manuscriptCountThinWithCost state pending (p.threshold D.componentCount))
          (fun secondThinned =>
            costedBind
              ((communityManuscriptCostedOracles hn prep factor).generateSamplesWithCost
                (D.component i) secondThinned.2 b p.epsilonPrime
                (p.deltaPrime D.componentCount))
              (fun batch => costedCharge
                (Measure.dirac (secondThinned.1.addBatch batch.2))
                (secondThinned.2 * TTCRuntime.appendCopyOperations)))),
      result.1.rate ≤ 1 := by
  apply costedBind_ae_state_of_forall _ _
    (fun s : TTCState n => s.rate ≤ 1) measurableSet_state_rate_le_one
  intro pending
  exact count_sample_append_rate_le_one_ae hn D p b prep factor i state pending hrate

private theorem rate_poisson_count_sample_rate_le_one_ae {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat) (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) (state : TTCState n) (intensity : NNReal)
    (hrate : state.rate ≤ 1) :
    ∀ᵐ result ∂costedBind
      (manuscriptRateThinWithCost state intensity (p.threshold D.componentCount))
      (fun firstThinned =>
        costedBind
          (costedCharge (poissonMeasure (intensity * firstThinned.rate))
            TTCRuntime.poissonDrawOperations)
          (fun pending =>
            costedBind
              (manuscriptCountThinWithCost firstThinned pending
                (p.threshold D.componentCount))
              (fun secondThinned =>
                costedBind
                  ((communityManuscriptCostedOracles hn prep factor).generateSamplesWithCost
                    (D.component i) secondThinned.2 b p.epsilonPrime
                    (p.deltaPrime D.componentCount))
                  (fun batch => costedCharge
                    (Measure.dirac (secondThinned.1.addBatch batch.2))
                    (secondThinned.2 * TTCRuntime.appendCopyOperations))))),
      result.1.rate ≤ 1 := by
  apply costedBind_ae_state_of_ae _ _ (fun s : TTCState n => s.rate ≤ 1)
    (fun s : TTCState n => s.rate ≤ 1) measurableSet_state_rate_le_one
  · exact manuscriptRateThinWithCost_rate_le_one_ae state intensity _ hrate
  · intro firstThinned hfirst
    exact poisson_count_sample_rate_le_one_ae hn D p b prep factor i firstThinned
      intensity hfirst

theorem certified_manuscript_component_rate_le_one_ae {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat) (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) (state : TTCState n)
    (hrate : state.rate ≤ 1) :
    ∀ᵐ result ∂
      manuscriptProcessComponentWithCost
        (communityManuscriptCostedOracles hn prep factor) b p.epsilonPrime
        (p.deltaPrime D.componentCount) (p.threshold D.componentCount)
        (D.component i) state,
      result.1.rate ≤ 1 := by
  unfold manuscriptProcessComponentWithCost
  apply costedBind_ae_state_of_forall _ _
    (fun s : TTCState n => s.rate ≤ 1) measurableSet_state_rate_le_one
  intro volumeOutcome
  dsimp only
  apply costedBind_ae_state_of_ae _ _
    (fun s : TTCState n => s.rate ≤ 1)
    (fun s : TTCState n => s.rate ≤ 1) measurableSet_state_rate_le_one
  · apply costedCharge_dirac_ae_state _ _ _ measurableSet_state_rate_le_one
    simpa only [TTCState.removeComponent] using hrate
  · intro deleted hdeleted
    exact rate_poisson_count_sample_rate_le_one_ae hn D p b prep factor i
      deleted _ hdeleted

private theorem certified_component_list_mass_le_one {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.latticeEta p.epsilonPrime)
    (prep : TTCPreprocessor n k) (factor : Nat)
    (components : List (PolytopeData n))
    (hcomponents : ∀ P ∈ components, ∃ i : Fin D.componentCount,
      D.component i = P) (state : TTCState n) :
    (manuscriptProcessComponentsWithCost
      (communityManuscriptCostedOracles hn prep factor) b p.epsilonPrime
      (p.deltaPrime D.componentCount) (p.threshold D.componentCount)
      components state) Set.univ ≤ 1 := by
  induction components generalizing state with
  | nil =>
      simp only [manuscriptProcessComponentsWithCost]
      simp
  | cons P rest ih =>
      obtain ⟨i, rfl⟩ := hcomponents P (by simp)
      have hrest : ∀ Q ∈ rest, ∃ j : Fin D.componentCount,
          D.component j = Q := by
        intro Q hQ
        exact hcomponents Q (by simp [hQ])
      change (costedBind
        (manuscriptProcessComponentWithCost
          (communityManuscriptCostedOracles hn prep factor) b p.epsilonPrime
          (p.deltaPrime D.componentCount) (p.threshold D.componentCount)
          (D.component i) state)
        (manuscriptProcessComponentsWithCost
          (communityManuscriptCostedOracles hn prep factor) b p.epsilonPrime
          (p.deltaPrime D.componentCount) (p.threshold D.componentCount)
          rest)) Set.univ ≤ 1
      apply costedBind_mass_le_one
      · exact certified_manuscript_component_mass_le_one hn D p b hprecision
          prep factor i state
      · intro nextState
        exact ih hrest nextState

theorem certified_component_list_expected_cost {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.latticeEta p.epsilonPrime)
    (prep : TTCPreprocessor n k) (factor : Nat)
    (components : List (PolytopeData n))
    (hcomponents : ∀ P ∈ components, ∃ i : Fin D.componentCount,
      D.component i = P) (state : TTCState n)
    (hcard : (state.samples.card : Real) ≤ p.threshold D.componentCount)
    (hrate : state.rate ≤ 1) :
    ∫⁻ result, (result.2 : ENNReal) ∂
      manuscriptProcessComponentsWithCost
        (communityManuscriptCostedOracles hn prep factor) b p.epsilonPrime
        (p.deltaPrime D.componentCount) (p.threshold D.componentCount)
        components state ≤
      (components.map (uniformComponentCost hn p D.componentCount b factor)).sum := by
  induction components generalizing state with
  | nil =>
      simp only [manuscriptProcessComponentsWithCost, List.map_nil, List.sum_nil]
      simp
  | cons P rest ih =>
      obtain ⟨i, rfl⟩ := hcomponents P (by simp)
      have hrest : ∀ Q ∈ rest, ∃ j : Fin D.componentCount,
          D.component j = Q := by
        intro Q hQ
        exact hcomponents Q (by simp [hQ])
      let first := manuscriptProcessComponentWithCost
        (communityManuscriptCostedOracles hn prep factor) b p.epsilonPrime
        (p.deltaPrime D.componentCount) (p.threshold D.componentCount)
        (D.component i) state
      let next := manuscriptProcessComponentsWithCost
        (communityManuscriptCostedOracles hn prep factor) b p.epsilonPrime
        (p.deltaPrime D.componentCount) (p.threshold D.componentCount) rest
      have hfirstMass : first Set.univ ≤ 1 :=
        certified_manuscript_component_mass_le_one hn D p b hprecision
          prep factor i state
      have hnextMass (s : TTCState n) : (next s) Set.univ ≤ 1 :=
        certified_component_list_mass_le_one hn D p b hprecision prep factor
          rest hrest s
      have hfirstCost :
          (∫⁻ result, (result.2 : ENNReal) ∂first) ≤
            uniformComponentCost hn p D.componentCount b factor (D.component i) := by
        simpa only [uniformComponentCost] using
          certified_manuscript_component_expected_cost_uniform hn D p b
            hprecision prep factor i state hcard hrate
      have hnextCost : ∀ᵐ result ∂first,
          (∫⁻ future, (future.2 : ENNReal) ∂next result.1) ≤
            (rest.map (uniformComponentCost hn p D.componentCount b factor)).sum := by
        have hcard' := certified_manuscript_component_card_le_ae hn D p b prep factor
          i state
        have hrate' := certified_manuscript_component_rate_le_one_ae hn D p b prep factor
          i state hrate
        filter_upwards [hcard', hrate'] with result hc hr
        exact ih hrest result.1 hc hr
      change (∫⁻ result, (result.2 : ENNReal) ∂costedBind first next) ≤ _
      simpa only [List.map_cons, List.sum_cons] using
        costedBind_expected_cost_le_add_ae first next hfirstMass hnextMass
          hfirstCost hnextCost

/-- Exact finite expected-operation bound for the charged manuscript TTC run,
including the caller-supplied preprocessing charge. -/
private theorem communityCosted_preprocessing_eq {n k : Nat} (hn : 21 ≤ n)
    (prep : TTCPreprocessor n k) (factor : Nat) :
    (communityManuscriptCostedOracles hn prep factor).base.preprocessing = prep := by
  rfl

theorem community_manuscript_expected_cost_finite_sum {n k : Nat}
    (hn : 21 ≤ n) (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations factor : Nat) :
    let D := prep.run F hbounded
    let b := (prep.choosePrecision D p).value
    ∫⁻ result, (result.2 : ENNReal) ∂
      communityManuscriptTTCWithCost hn F hbounded p prep
        preprocessingOperations factor ≤
      preprocessingOperations +
        ((List.ofFn D.component).map
          (uniformComponentCost hn p D.componentCount b factor)).sum := by
  dsimp only
  unfold communityManuscriptTTCWithCost manuscriptTTCWithCost
  rw [communityCosted_preprocessing_eq]
  let D := prep.run F hbounded
  let b := (prep.choosePrecision D p).value
  have hprecision : PrecisionAdequate D b p.latticeEta p.epsilonPrime :=
    (prep.choosePrecision D p).adequate
  by_cases hempty : D.componentCount = 0
  · simp [communityManuscriptTTCWithCost, manuscriptTTCWithCost,
      D, hempty]
  · have hcomponents : ∀ P ∈ List.ofFn D.component,
        ∃ i : Fin D.componentCount, D.component i = P := by
      intro P hP
      exact (List.mem_ofFn' D.component P).mp hP
    have hinitialCard :
        (((TTCState.initial n).samples.card : Nat) : Real) ≤
          p.threshold D.componentCount := by
      simp only [TTCState.initial, Finset.card_empty, Nat.cast_zero]
      exact (p.threshold_pos D.componentCount).le
    have hinitialRate : (TTCState.initial n).rate ≤ 1 := by
      simp only [TTCState.initial, le_refl]
    have hcoreCost := certified_component_list_expected_cost hn D p b
      hprecision prep factor (List.ofFn D.component) hcomponents
      (TTCState.initial n) hinitialCard hinitialRate
    have hcoreMass := certified_component_list_mass_le_one hn D p b
      hprecision prep factor (List.ofFn D.component) hcomponents
      (TTCState.initial n)
    let core := manuscriptProcessComponentsWithCost
      (communityManuscriptCostedOracles hn prep factor) b p.epsilonPrime
      (p.deltaPrime D.componentCount) (p.threshold D.componentCount)
      (List.ofFn D.component) (TTCState.initial n)
    have hempty' : (prep.run F hbounded).componentCount ≠ 0 := by
      simpa only [D] using hempty
    rw [if_neg hempty']
    change (∫⁻ result, (result.2 : ENNReal) ∂
      core.map (fun result =>
        (manuscriptEstimate b (p.threshold D.componentCount) result.1,
          preprocessingOperations + result.2))) ≤ _
    apply (lintegral_map_le _ _).trans
    simp only [Nat.cast_add]
    rw [lintegral_add_left (by fun_prop)]
    simp only [lintegral_const]
    exact add_le_add
      (mul_le_of_le_one_right (by positivity) hcoreMass) hcoreCost

theorem community_manuscript_expected_cost_explicit {n k : Nat}
    (hn : 21 ≤ n) (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations factor : Nat) :
    let D := prep.run F hbounded
    let b := (prep.choosePrecision D p).value
    ∫⁻ result, (result.2 : ENNReal) ∂
      communityManuscriptTTCWithCost hn F hbounded p prep
        preprocessingOperations factor ≤
      preprocessingOperations +
        ∑ i : Fin D.componentCount,
          TTCRuntime.manuscriptExpectedComponentBudget hn p D.componentCount b
            factor (D.component i) := by
  simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply,
    uniformComponentCost_eq_model] using
    community_manuscript_expected_cost_finite_sum hn F hbounded p prep
      preprocessingOperations factor

end Kr25Ssmxt
