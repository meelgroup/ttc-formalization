import ttc.Analysis.RateKernelMeasurable
import ttc.Analysis.CostedOracles
import ttc.Analysis.MeasurableAddBatch
import ttc.Analysis.MeasurableFixedSfiniteBind
import ttc.Analysis.MeasurablePoissonMeasure
import ttc.Analysis.MeasurableRemoveComponent
import ttc.Analysis.OracleNormalization

/-! The charged sampling-and-append tail has the paper's state marginal. -/

namespace ttc

open MeasureTheory

theorem community_costed_samples_mass_le_one_all
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (count b : Nat)
    (eta delta : Real) :
    ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
      P count b eta) Set.univ ≤ 1 := by
  classical
  by_cases h : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧ 0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧ (codedLatticePoints P b).Nonempty
  · exact communityCosted_samples_mass_le_one hn prep factor
      P count b eta delta h
  · simp [ttcCostedSubroutines, h, costedCharge,
      failedSampleBatchLaw]

theorem community_sample_append_fst {n k : Nat} (hn : 21 ≤ n)
    (prep : TTCPreprocessor n k) (factor : Nat)
    (P : PolytopeData n) (count b : Nat) (eta delta : Real)
    (state : TTCState n) :
    (costedBind
      ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
        P count b eta)
      (fun batch => costedCharge (Measure.dirac (state.addBatch batch))
        (count * TTCRuntime.appendCopyOperations))).map Prod.fst =
      ((ttcSubroutines hn prep).GenerateSamples
        P count b eta).map (fun batch => state.addBatch batch) := by
  let f : SampleBatch n count → TTCState n := fun batch => state.addBatch batch
  have hf : Measurable f := by
    exact measurable_addBatch.comp
      (measurable_const.prodMk measurable_id)
  let μ := (ttcCostedSubroutines hn prep factor).generateSamplesWithCost
    P count b eta
  have hbridge := costedBind_dirac_eq_map μ f
    (fun _ => count * TTCRuntime.appendCopyOperations) hf measurable_const
  calc
    _ = (μ.map (fun result => (f result.1,
        result.2 + count * TTCRuntime.appendCopyOperations))).map Prod.fst := by
      rw [hbridge]
    _ = (μ.map Prod.fst).map f := by
      rw [Measure.map_map measurable_fst (by fun_prop)]
      rw [Measure.map_map hf measurable_fst]
      rfl
    _ = _ := by
      rw [communityCosted_samples_fst hn prep factor P count b eta delta]

theorem community_sample_append_kernel_measurable
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta : Real) :
    Measurable (fun z : TTCState n × Nat =>
      costedBind
        ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
          P z.2 b eta)
        (fun batch => costedCharge (Measure.dirac (z.1.addBatch batch))
          (z.2 * TTCRuntime.appendCopyOperations))) := by
  apply measurable_from_prod_countable_left
  intro count
  let μ := (ttcCostedSubroutines hn prep factor).generateSamplesWithCost
    P count b eta
  have hmass : μ Set.univ ≤ 1 :=
    community_costed_samples_mass_le_one_all hn prep factor
      P count b eta delta
  letI : IsFiniteMeasure μ := ⟨lt_of_le_of_lt hmass (by norm_num)⟩
  let G : TTCState n × (SampleBatch n count × Nat) → TTCState n × Nat :=
    fun z => (z.1.addBatch z.2.1,
      z.2.2 + count * TTCRuntime.appendCopyOperations)
  have hpoints : Measurable
      (fun z : TTCState n × (SampleBatch n count × Nat) => z.2.1) :=
    (measurable_fst.comp measurable_snd)
  have hadded : Measurable
      (fun z : TTCState n × (SampleBatch n count × Nat) =>
        z.1.addBatch z.2.1) :=
    measurable_addBatch.comp (measurable_fst.prodMk hpoints)
  have hcost : Measurable
      (fun z : TTCState n × (SampleBatch n count × Nat) =>
        z.2.2 + count * TTCRuntime.appendCopyOperations) :=
    (measurable_of_countable (fun c : Nat =>
      c + count * TTCRuntime.appendCopyOperations)).comp
      (measurable_snd.comp measurable_snd)
  have hG : Measurable G := hadded.prodMk hcost
  have hpair : Measurable (fun state : TTCState n => μ.map (Prod.mk state)) :=
    Measurable.map_prodMk_left
  have hmap : Measurable (fun state : TTCState n =>
      μ.map fun result => (state.addBatch result.1,
        result.2 + count * TTCRuntime.appendCopyOperations)) := by
    have h := (Measure.measurable_map G hG).comp hpair
    convert h using 1
    funext state
    change μ.map (fun result => (state.addBatch result.1,
        result.2 + count * TTCRuntime.appendCopyOperations)) =
      (μ.map (Prod.mk state)).map G
    rw [Measure.map_map hG measurable_prodMk_left]
    rfl
  convert hmap using 1
  funext state
  exact costedBind_dirac_eq_map μ
    (fun batch => state.addBatch batch)
    (fun _ => count * TTCRuntime.appendCopyOperations)
    (measurable_addBatch.comp
      (measurable_const.prodMk measurable_id)) measurable_const

theorem community_count_sample_append_fst
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (state : TTCState n) (pending : Nat) :
    (costedBind (ttcPseudocode.secondLoopWithCost state pending threshold)
      (fun second => costedBind
        ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
          P second.2 b eta)
        (fun batch => costedCharge
          (Measure.dirac (second.1.addBatch batch))
          (second.2 * TTCRuntime.appendCopyOperations)))).map Prod.fst =
      (ttcPseudocode.secondLoop state pending threshold).bind fun second =>
        ((ttcSubroutines hn prep).GenerateSamples
          P second.2 b eta).map (fun batch => second.1.addBatch batch) := by
  rw [costedBind_fst _ _
    (community_sample_append_kernel_measurable hn prep factor P b eta delta)]
  rw [countThinWithCost_fst]
  congr 1
  funext second
  exact community_sample_append_fst hn prep factor P second.2 b
    eta delta second.1

theorem community_count_sample_append_kernel_measurable
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) :
    Measurable (fun z : TTCState n × Nat =>
      costedBind (ttcPseudocode.secondLoopWithCost z.1 z.2 threshold)
        (fun second => costedBind
          ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
            P second.2 b eta)
          (fun batch => costedCharge
            (Measure.dirac (second.1.addBatch batch))
            (second.2 * TTCRuntime.appendCopyOperations)))) := by
  exact costedBind_kernel_measurable
    (fun z : TTCState n × Nat => ttcPseudocode.secondLoopWithCost z.1 z.2 threshold)
    (fun second => costedBind
      ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
        P second.2 b eta)
      (fun batch => costedCharge
        (Measure.dirac (second.1.addBatch batch))
        (second.2 * TTCRuntime.appendCopyOperations)))
    (countThinWithCost_kernel_measurable threshold)
    (community_sample_append_kernel_measurable hn prep factor P b eta delta)

theorem community_poisson_count_sample_append_fst
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (state : TTCState n)
    (intensity : NNReal) :
    (costedBind
      (costedCharge (ProbabilityTheory.poissonMeasure (intensity * state.p))
        TTCRuntime.poissonDrawOperations)
      (fun pending => costedBind
        (ttcPseudocode.secondLoopWithCost state pending threshold)
        (fun second => costedBind
          ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
            P second.2 b eta)
          (fun batch => costedCharge
            (Measure.dirac (second.1.addBatch batch))
            (second.2 * TTCRuntime.appendCopyOperations))))).map Prod.fst =
      (ProbabilityTheory.poissonMeasure (intensity * state.p)).bind fun pending =>
        (ttcPseudocode.secondLoop state pending threshold).bind fun second =>
          ((ttcSubroutines hn prep).GenerateSamples
            P second.2 b eta).map (fun batch => second.1.addBatch batch) := by
  let μ := ProbabilityTheory.poissonMeasure (intensity * state.p)
  let next : Nat → Measure (TTCState n × Nat) := fun pending =>
    costedBind (ttcPseudocode.secondLoopWithCost state pending threshold)
      (fun second => costedBind
        ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
          P second.2 b eta)
        (fun batch => costedCharge
          (Measure.dirac (second.1.addBatch batch))
          (second.2 * TTCRuntime.appendCopyOperations)))
  have hnext : Measurable next := Measurable.of_discrete
  have hshift (pending : Nat) : Measurable
      (fun future : TTCState n × Nat =>
        (future.1, TTCRuntime.poissonDrawOperations + future.2)) := by fun_prop
  calc
    _ = (μ.bind fun pending => (next pending).map fun future =>
        (future.1, TTCRuntime.poissonDrawOperations + future.2)).map Prod.fst := by
      rw [costedBind_costedCharge_eq_bind μ TTCRuntime.poissonDrawOperations
        next hnext]
    _ = μ.bind fun pending => (next pending).map Prod.fst := by
      rw [map_bind_measure μ
        (fun pending : Nat => (next pending).map fun future : TTCState n × Nat =>
          (future.1, TTCRuntime.poissonDrawOperations + future.2))
        (Prod.fst : TTCState n × Nat → TTCState n)
        (Measurable.of_discrete.aemeasurable)
        measurable_fst]
      congr 1
      funext pending
      rw [Measure.map_map measurable_fst (hshift pending)]
      rfl
    _ = _ := by
      congr 1
      funext pending
      exact community_count_sample_append_fst hn prep factor P b
        eta delta threshold state pending

private noncomputable def communityCostedCountSampleAppend
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (z : TTCState n × Nat) :
    Measure (TTCState n × Nat) :=
  costedBind (ttcPseudocode.secondLoopWithCost z.1 z.2 threshold)
    (fun second => costedBind
      ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
        P second.2 b eta)
      (fun batch => costedCharge
        (Measure.dirac (second.1.addBatch batch))
        (second.2 * TTCRuntime.appendCopyOperations)))

private noncomputable def communityCostedPoissonCountSampleAppend
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (state : TTCState n)
    (intensity : NNReal) : Measure (TTCState n × Nat) :=
  costedBind
    (costedCharge (ProbabilityTheory.poissonMeasure (intensity * state.p))
      TTCRuntime.poissonDrawOperations)
    (fun pending => communityCostedCountSampleAppend hn prep factor P b eta delta
      threshold (state, pending))

theorem community_costed_count_tail_measurable
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) :
    Measurable (communityCostedCountSampleAppend hn prep factor P b eta delta
      threshold) :=
  community_count_sample_append_kernel_measurable hn prep factor P b
    eta delta threshold

theorem community_poisson_count_sample_append_kernel_measurable
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) :
    Measurable (fun z : TTCState n × NNReal =>
      communityCostedPoissonCountSampleAppend hn prep factor P b eta delta
        threshold z.1 z.2) := by
  let X := TTCState n × NNReal
  let law : X → Measure Nat := fun z =>
    ProbabilityTheory.poissonMeasure (z.2 * z.1.p)
  let next : X × Nat → Measure (TTCState n × Nat) := fun z =>
    communityCostedCountSampleAppend hn prep factor P b eta delta threshold
      (z.1.1, z.2)
  have hcoords : Measurable (fun z : X =>
      (z.1.p, z.1.X, z.1.nextLabel)) :=
    (comap_measurable _).comp measurable_fst
  have hrate : Measurable (fun z : X => z.1.p) :=
    measurable_fst.comp hcoords
  have hlaw : Measurable law :=
    measurable_poissonMeasure.comp (measurable_snd.mul hrate)
  have hnext : Measurable next :=
    (community_costed_count_tail_measurable hn prep factor P b
      eta delta threshold).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  exact measurable_nat_costedCharge_bind_kernel law next
    TTCRuntime.poissonDrawOperations hlaw hnext

private noncomputable def communityCostedRateTail
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (state : TTCState n)
    (intensity : NNReal) : Measure (TTCState n × Nat) :=
  costedBind (ttcReference.firstLoopWithCost state intensity threshold)
    (fun first => communityCostedPoissonCountSampleAppend hn prep factor P b
      eta delta threshold first intensity)

private noncomputable def communityRateDraw {n : Nat} (threshold : Real)
    (z : (TTCState n × NNReal) × (Nat × Nat → Bool)) : TTCState n × Nat :=
  (ttcReference.firstLoopResult z.1.1 z.1.2 threshold z.2,
    ttcReference.firstLoopCost z.1.1 z.1.2 threshold)

private noncomputable def communityRateNext
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real)
    (z : (TTCState n × NNReal) × TTCState n) :
    Measure (TTCState n × Nat) :=
  communityCostedPoissonCountSampleAppend hn prep factor P b eta delta
    threshold z.2 z.1.2

private theorem communityRateDraw_measurable {n : Nat}
    (threshold : Real) (hthreshold : 0 < threshold) :
    Measurable (communityRateDraw (n := n) threshold) :=
  (measurable_rateThinningResult_joint threshold hthreshold).prodMk
    ((measurable_rateThinningCost_joint threshold hthreshold).comp
      measurable_fst)

set_option maxHeartbeats 800000 in
private theorem communityRateNext_measurable
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) :
    Measurable (communityRateNext hn prep factor P b eta delta threshold) := by
  unfold communityRateNext
  change Measurable
    ((fun z : TTCState n × NNReal =>
      communityCostedPoissonCountSampleAppend hn prep factor P b eta delta
        threshold z.1 z.2) ∘
      (fun z : (TTCState n × NNReal) × TTCState n => (z.2, z.1.2)))
  exact (community_poisson_count_sample_append_kernel_measurable hn prep
    factor P b eta delta threshold).comp
    (measurable_snd.prodMk (measurable_snd.comp measurable_fst))

set_option maxHeartbeats 800000 in
theorem community_rate_tail_kernel_measurable
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (hthreshold : 0 < threshold) :
    Measurable (fun z : TTCState n × NNReal =>
      costedBind
        (fairCoinStreamLaw.map fun coins => communityRateDraw threshold (z, coins))
        (fun first => communityRateNext hn prep factor P b eta delta threshold
          (z, first))) := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  exact measurable_costedBind_fixed_source_map_kernel
    fairCoinStreamLaw (communityRateDraw threshold)
    (communityRateNext hn prep factor P b eta delta threshold)
    (communityRateDraw_measurable threshold hthreshold)
    (communityRateNext_measurable hn prep factor P b eta delta threshold)

theorem community_costed_rate_tail_measurable
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (hthreshold : 0 < threshold) :
    Measurable (fun z : TTCState n × NNReal =>
      communityCostedRateTail hn prep factor P b eta delta threshold z.1 z.2) := by
  have hbase := community_rate_tail_kernel_measurable hn prep factor
    P b eta delta threshold hthreshold
  have heq :
      (fun z : TTCState n × NNReal =>
        communityCostedRateTail hn prep factor P b eta delta threshold z.1 z.2) =
      (fun z : TTCState n × NNReal =>
        costedBind
          (fairCoinStreamLaw.map fun coins => communityRateDraw threshold (z, coins))
          (fun first => communityRateNext hn prep factor P b eta delta threshold
            (z, first))) := by
    funext z
    rfl
  rw [heq]
  exact hbase

set_option maxHeartbeats 800000 in
theorem community_rate_poisson_tail_fst
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (state : TTCState n)
    (intensity : NNReal) :
    (communityCostedRateTail hn prep factor P b eta delta threshold
      state intensity).map Prod.fst =
      (ttcReference.firstLoop state intensity threshold).bind fun first =>
        (ProbabilityTheory.poissonMeasure (intensity * first.p)).bind fun pending =>
          (ttcPseudocode.secondLoop first pending threshold).bind fun second =>
            ((ttcSubroutines hn prep).GenerateSamples
              P second.2 b eta).map
              (fun batch => second.1.addBatch batch) := by
  unfold communityCostedRateTail
  have hpair : Measurable (fun first : TTCState n => (first, intensity)) :=
    measurable_id.prodMk measurable_const
  have hbase := community_poisson_count_sample_append_kernel_measurable
    hn prep factor P b eta delta threshold
  have hnext : Measurable (fun first : TTCState n =>
      communityCostedPoissonCountSampleAppend hn prep factor P b eta delta
        threshold first intensity) := by
    have hcomp := hbase.comp hpair
    change Measurable
      ((fun z : TTCState n × NNReal =>
        communityCostedPoissonCountSampleAppend hn prep factor P b eta delta
          threshold z.1 z.2) ∘
        (fun first : TTCState n => (first, intensity)))
    exact hcomp
  rw [costedBind_fst _ _ hnext, rateThinWithCost_fst]
  congr 1
  funext first
  exact community_poisson_count_sample_append_fst hn prep factor P b
    eta delta threshold first intensity

private noncomputable def communityCostedDeletionTail
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (state : TTCState n)
    (intensity : NNReal) : Measure (TTCState n × Nat) :=
  let deleted := state.removeComponent P
  let deletionCost := TTCRuntime.deletionPassOperations n
    P.presentation.facetCount state.X.card
      (state.X.card - deleted.X.card)
  costedBind (costedCharge (Measure.dirac deleted) deletionCost)
    (fun afterDeletion => communityCostedRateTail hn prep factor P b eta delta
      threshold afterDeletion intensity)

theorem community_deletion_pair_measurable {n : Nat}
    (P : PolytopeData n) :
    Measurable (fun state : TTCState n =>
      (state.removeComponent P,
        TTCRuntime.deletionPassOperations n P.presentation.facetCount
          state.X.card
          (state.X.card - (state.removeComponent P).X.card))) := by
  have hcoords : Measurable (fun s : TTCState n =>
      (s.p, s.X, s.nextLabel)) := comap_measurable _
  have hsamples : Measurable (fun s : TTCState n => s.X) :=
    (measurable_fst.comp measurable_snd).comp hcoords
  have hcard : Measurable (fun s : TTCState n => s.X.card) :=
    (measurable_of_countable (fun copies : Finset (SampleCopy n) =>
      copies.card)).comp hsamples
  have hdeleted : Measurable (fun s : TTCState n => s.removeComponent P) :=
    measurable_removeComponent P
  have hcost : Measurable (fun s : TTCState n =>
      TTCRuntime.deletionPassOperations n P.presentation.facetCount
        s.X.card
        (s.X.card - (s.removeComponent P).X.card)) := by
    let f : Nat × Nat → Nat := fun counts =>
      TTCRuntime.deletionPassOperations n P.presentation.facetCount counts.1
        (counts.1 - counts.2)
    have hf : Measurable f := measurable_of_countable f
    exact hf.comp (hcard.prodMk (hcard.comp hdeleted))
  exact hdeleted.prodMk hcost

theorem community_deletion_tail_joint_measurable
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (hthreshold : 0 < threshold) :
    Measurable (fun z : TTCState n × NNReal =>
      communityCostedDeletionTail hn prep factor P b eta delta threshold
        z.1 z.2) := by
  let first : TTCState n × NNReal → Measure (TTCState n × Nat) := fun z =>
    let deleted := z.1.removeComponent P
    let cost := TTCRuntime.deletionPassOperations n P.presentation.facetCount
      z.1.X.card (z.1.X.card - deleted.X.card)
    costedCharge (Measure.dirac deleted) cost
  let next : (TTCState n × NNReal) × TTCState n →
      Measure (TTCState n × Nat) := fun z =>
    communityCostedRateTail hn prep factor P b eta delta threshold z.2 z.1.2
  have hpair : Measurable (fun z : TTCState n × NNReal =>
      (z.1.removeComponent P,
        TTCRuntime.deletionPassOperations n P.presentation.facetCount
          z.1.X.card
          (z.1.X.card - (z.1.removeComponent P).X.card))) :=
    (community_deletion_pair_measurable P).comp measurable_fst
  have hfirst : Measurable first := by
    have hdirac := Measure.measurable_dirac.comp hpair
    have heq : first = (fun z : TTCState n × NNReal =>
        Measure.dirac
          (z.1.removeComponent P,
            TTCRuntime.deletionPassOperations n P.presentation.facetCount
              z.1.X.card
              (z.1.X.card - (z.1.removeComponent P).X.card))) := by
      funext z
      simp only [first, costedCharge, Measure.map_dirac]
    rw [heq]
    exact hdirac
  have hnext : Measurable next := by
    have hpairnext : Measurable
        (fun z : (TTCState n × NNReal) × TTCState n => (z.2, z.1.2)) :=
      measurable_snd.prodMk (measurable_snd.comp measurable_fst)
    have hcomp := (community_costed_rate_tail_measurable hn prep
      factor P b eta delta threshold hthreshold).comp hpairnext
    change Measurable
      ((fun z : TTCState n × NNReal =>
        communityCostedRateTail hn prep factor P b eta delta threshold z.1 z.2) ∘
        (fun z : (TTCState n × NNReal) × TTCState n => (z.2, z.1.2)))
    exact hcomp
  have hmass : ∀ z, first z Set.univ ≤ 1 := by
    intro z
    dsimp [first]
    apply costedCharge_mass_le_one
    simp
  have hbase := measurable_costedBind_dependent_finite first next hfirst hnext hmass
  have heq :
      (fun z : TTCState n × NNReal =>
        communityCostedDeletionTail hn prep factor P b eta delta threshold
          z.1 z.2) =
      (fun z => costedBind (first z) (fun state => next (z, state))) := by
    funext z
    rfl
  rw [heq]
  exact hbase

theorem community_deletion_tail_fst
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (hthreshold : 0 < threshold)
    (state : TTCState n) (intensity : NNReal) :
    (communityCostedDeletionTail hn prep factor P b eta delta threshold
      state intensity).map Prod.fst =
      (ttcReference.firstLoop (state.removeComponent P) intensity threshold).bind
        fun first =>
          (ProbabilityTheory.poissonMeasure (intensity * first.p)).bind
            fun pending =>
              (ttcPseudocode.secondLoop first pending threshold).bind fun second =>
                ((ttcSubroutines hn prep).GenerateSamples
                  P second.2 b eta).map
                  (fun batch => second.1.addBatch batch) := by
  let deleted := state.removeComponent P
  let deletionCost := TTCRuntime.deletionPassOperations n
    P.presentation.facetCount state.X.card
      (state.X.card - deleted.X.card)
  have hpair : Measurable (fun s : TTCState n => (s, intensity)) :=
    measurable_id.prodMk measurable_const
  have hnext : Measurable (fun s : TTCState n =>
      communityCostedRateTail hn prep factor P b eta delta threshold
        s intensity) := by
    have hcomp := (community_costed_rate_tail_measurable hn prep factor
      P b eta delta threshold hthreshold).comp hpair
    change Measurable
      ((fun z : TTCState n × NNReal =>
        communityCostedRateTail hn prep factor P b eta delta threshold
          z.1 z.2) ∘ (fun s : TTCState n => (s, intensity)))
    exact hcomp
  unfold communityCostedDeletionTail
  rw [costedBind_fst _ _ hnext, costedCharge_fst]
  have hmap : Measurable (fun s : TTCState n =>
      (communityCostedRateTail hn prep factor P b eta delta threshold
        s intensity).map Prod.fst) :=
    (Measure.measurable_map _ measurable_fst).comp hnext
  rw [Measure.dirac_bind hmap]
  exact community_rate_poisson_tail_fst hn prep factor P b eta
    delta threshold deleted intensity

theorem community_deletion_tail_kernel_measurable
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (hthreshold : 0 < threshold)
    (state : TTCState n) :
    Measurable (fun intensity : NNReal =>
      communityCostedDeletionTail hn prep factor P b eta delta threshold
        state intensity) := by
  let deleted := state.removeComponent P
  let deletionCost := TTCRuntime.deletionPassOperations n
    P.presentation.facetCount state.X.card
      (state.X.card - deleted.X.card)
  let shift : TTCState n × Nat → TTCState n × Nat :=
    fun future => (future.1, deletionCost + future.2)
  have htail : Measurable (fun intensity : NNReal =>
      communityCostedRateTail hn prep factor P b eta delta threshold
        deleted intensity) := by
    have hcomp := (community_costed_rate_tail_measurable hn prep factor
      P b eta delta threshold hthreshold).comp
      (measurable_const.prodMk measurable_id : Measurable
        (fun intensity : NNReal => (deleted, intensity)))
    change Measurable
      ((fun z : TTCState n × NNReal =>
        communityCostedRateTail hn prep factor P b eta delta threshold
          z.1 z.2) ∘ (fun intensity : NNReal => (deleted, intensity)))
    exact hcomp
  have hmap : Measurable (fun intensity : NNReal =>
      (communityCostedRateTail hn prep factor P b eta delta threshold
        deleted intensity).map shift) :=
    (Measure.measurable_map shift (by fun_prop)).comp htail
  have heq :
      (fun intensity : NNReal =>
        communityCostedDeletionTail hn prep factor P b eta delta threshold
          state intensity) =
      (fun intensity : NNReal =>
        (communityCostedRateTail hn prep factor P b eta delta threshold
          deleted intensity).map shift) := by
    funext intensity
    have hnext : Measurable (fun s : TTCState n =>
        communityCostedRateTail hn prep factor P b eta delta threshold
          s intensity) := by
      have hcomp := (community_costed_rate_tail_measurable hn prep factor
        P b eta delta threshold hthreshold).comp
        (measurable_id.prodMk measurable_const : Measurable
          (fun s : TTCState n => (s, intensity)))
      change Measurable
        ((fun z : TTCState n × NNReal =>
          communityCostedRateTail hn prep factor P b eta delta threshold
            z.1 z.2) ∘ (fun s : TTCState n => (s, intensity)))
      exact hcomp
    unfold communityCostedDeletionTail
    exact costedBind_costedCharge_dirac_eq_map deleted deletionCost _ hnext
  rw [heq]
  exact hmap

noncomputable def communityCostedComponentTail
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (state : TTCState n)
    (outcome : VolumeOutcome) : Measure (TTCState n × Nat) :=
  communityCostedDeletionTail hn prep factor P b eta delta threshold state
    (ttcReference.t b n threshold outcome.2)

theorem community_component_tail_measurable
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (hthreshold : 0 < threshold)
    (state : TTCState n) :
    Measurable (communityCostedComponentTail hn prep factor P b eta delta
      threshold state) := by
  have hintensity : Measurable (fun outcome : VolumeOutcome =>
      ttcReference.t b n threshold outcome.2) := by
    unfold ttcReference.t
    exact (measurable_const.mul measurable_snd)
  exact (community_deletion_tail_kernel_measurable hn prep factor P b
    eta delta threshold hthreshold state).comp hintensity

theorem community_component_tail_joint_measurable
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (hthreshold : 0 < threshold) :
    Measurable (fun z : TTCState n × VolumeOutcome =>
      communityCostedComponentTail hn prep factor P b eta delta threshold
        z.1 z.2) := by
  have hintensity : Measurable (fun outcome : VolumeOutcome =>
      ttcReference.t b n threshold outcome.2) := by
    unfold ttcReference.t
    exact measurable_const.mul measurable_snd
  have hpair : Measurable (fun z : TTCState n × VolumeOutcome =>
      (z.1, ttcReference.t b n threshold z.2.2)) :=
    measurable_fst.prodMk (hintensity.comp measurable_snd)
  have hcomp := (community_deletion_tail_joint_measurable hn prep
    factor P b eta delta threshold hthreshold).comp hpair
  change Measurable
    ((fun z : TTCState n × NNReal =>
      communityCostedDeletionTail hn prep factor P b eta delta threshold
        z.1 z.2) ∘
      (fun z : TTCState n × VolumeOutcome =>
        (z.1, ttcReference.t b n threshold z.2.2)))
  exact hcomp

theorem community_component_fst
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (hthreshold : 0 < threshold)
    (state : TTCState n) :
    (ttcReference.stepWithCost
      (ttcCostedSubroutines hn prep factor)
      b eta delta threshold P state).map Prod.fst =
      ttcReference.step (ttcSubroutines hn prep)
        b eta delta threshold P state := by
  have htail := community_component_tail_measurable hn prep factor P
    b eta delta threshold hthreshold state
  change (costedBind
      ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
        P eta delta)
      (communityCostedComponentTail hn prep factor P b eta delta threshold
        state)).map Prod.fst = _
  rw [costedBind_fst _ _ htail,
    communityCosted_volume_fst]
  unfold ttcReference.step
  congr 1
  funext outcome
  exact community_deletion_tail_fst hn prep factor P b eta delta
    threshold hthreshold state (ttcReference.t b n threshold outcome.2)

theorem community_component_kernel_measurable
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (hthreshold : 0 < threshold)
    (hvolume : ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
      P eta delta) Set.univ ≤ 1) :
    Measurable (fun state : TTCState n =>
      ttcReference.stepWithCost
        (ttcCostedSubroutines hn prep factor)
        b eta delta threshold P state) := by
  let first : TTCState n → Measure (VolumeOutcome × Nat) := fun _ =>
    (ttcCostedSubroutines hn prep factor).computeVolumeWithCost
      P eta delta
  let next : TTCState n × VolumeOutcome → Measure (TTCState n × Nat) :=
    fun z => communityCostedComponentTail hn prep factor P b eta delta
      threshold z.1 z.2
  have hfirst : Measurable first := measurable_const
  have hnext : Measurable next :=
    community_component_tail_joint_measurable hn prep factor P b
      eta delta threshold hthreshold
  have hmass : ∀ state, first state Set.univ ≤ 1 := fun _ => hvolume
  have hbase := measurable_costedBind_dependent_finite first next hfirst hnext hmass
  have heq :
      (fun state : TTCState n =>
        ttcReference.stepWithCost
          (ttcCostedSubroutines hn prep factor)
          b eta delta threshold P state) =
      (fun state => costedBind (first state) (fun outcome => next (state, outcome))) := by
    funext state
    rfl
  rw [heq]
  exact hbase

theorem community_components_fst_of_measurable
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor b : Nat) (eta delta threshold : Real)
    (hthreshold : 0 < threshold)
    (hkernel : ∀ components : List (PolytopeData n),
      Measurable (fun state : TTCState n =>
        ttcReference.loopWithCost
          (ttcCostedSubroutines hn prep factor)
          b eta delta threshold components state))
    (components : List (PolytopeData n)) (state : TTCState n) :
    (ttcReference.loopWithCost
      (ttcCostedSubroutines hn prep factor)
      b eta delta threshold components state).map Prod.fst =
      ttcReference.loop (ttcSubroutines hn prep)
        b eta delta threshold components state := by
  induction components generalizing state with
  | nil =>
      simp [ttcReference.loopWithCost, ttcReference.loop]
  | cons P rest ih =>
      change (costedBind
        (ttcReference.stepWithCost
          (ttcCostedSubroutines hn prep factor)
          b eta delta threshold P state)
        (ttcReference.loopWithCost
          (ttcCostedSubroutines hn prep factor)
          b eta delta threshold rest)).map Prod.fst = _
      rw [costedBind_fst _ _ (hkernel rest)]
      rw [community_component_fst hn prep factor P b eta delta
        threshold hthreshold state]
      unfold ttcReference.loop
      congr 1
      funext nextState
      exact ih nextState

theorem community_components_kernel_measurable
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor b : Nat) (eta delta threshold : Real)
    (hthreshold : 0 < threshold)
    (components : List (PolytopeData n))
    (hvolume : ∀ P ∈ components,
      ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
        P eta delta) Set.univ ≤ 1) :
    Measurable (fun state : TTCState n =>
      ttcReference.loopWithCost
        (ttcCostedSubroutines hn prep factor)
        b eta delta threshold components state) := by
  induction components with
  | nil =>
      change Measurable (fun state : TTCState n => Measure.dirac (state, 0))
      exact Measure.measurable_dirac.comp (measurable_id.prodMk measurable_const)
  | cons P rest ih =>
      have hP := hvolume P (by simp)
      have hrest : ∀ Q ∈ rest,
          ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
            Q eta delta) Set.univ ≤ 1 := by
        intro Q hQ
        exact hvolume Q (by simp [hQ])
      have hfirst := community_component_kernel_measurable hn prep
        factor P b eta delta threshold hthreshold hP
      have hnext := ih hrest
      change Measurable (fun state : TTCState n =>
        costedBind
          (ttcReference.stepWithCost
            (ttcCostedSubroutines hn prep factor)
            b eta delta threshold P state)
          (ttcReference.loopWithCost
            (ttcCostedSubroutines hn prep factor)
            b eta delta threshold rest))
      exact costedBind_kernel_measurable _ _ hfirst hnext

theorem community_components_fst
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor b : Nat) (eta delta threshold : Real)
    (hthreshold : 0 < threshold)
    (components : List (PolytopeData n))
    (hvolume : ∀ P ∈ components,
      ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
        P eta delta) Set.univ ≤ 1)
    (state : TTCState n) :
    (ttcReference.loopWithCost
      (ttcCostedSubroutines hn prep factor)
      b eta delta threshold components state).map Prod.fst =
      ttcReference.loop (ttcSubroutines hn prep)
        b eta delta threshold components state := by
  induction components generalizing state with
  | nil =>
      simp [ttcReference.loopWithCost, ttcReference.loop]
  | cons P rest ih =>
      have hrest : ∀ Q ∈ rest,
          ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
            Q eta delta) Set.univ ≤ 1 := by
        intro Q hQ
        exact hvolume Q (by simp [hQ])
      have hnext := community_components_kernel_measurable hn prep
        factor b eta delta threshold hthreshold rest hrest
      change (costedBind
        (ttcReference.stepWithCost
          (ttcCostedSubroutines hn prep factor)
          b eta delta threshold P state)
        (ttcReference.loopWithCost
          (ttcCostedSubroutines hn prep factor)
          b eta delta threshold rest)).map Prod.fst = _
      rw [costedBind_fst _ _ hnext]
      rw [community_component_fst hn prep factor P b eta delta
        threshold hthreshold state]
      unfold ttcReference.loop
      congr 1
      funext nextState
      exact ih hrest nextState

/-- The concrete sampler and deterministic append preserve total mass. -/
theorem community_sample_append_isProbabilityMeasure
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (count b : Nat)
    (eta delta : Real) (state : TTCState n) :
    IsProbabilityMeasure
      (costedBind
        ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
          P count b eta)
        (fun batch => costedCharge (Measure.dirac (state.addBatch batch))
          (count * TTCRuntime.appendCopyOperations))) := by
  letI : IsProbabilityMeasure
      ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
        P count b eta) :=
    community_costed_samples_isProbabilityMeasure hn prep factor
      P count b eta delta
  apply costedBind_isProbabilityMeasure
  · have hstate : Measurable (fun batch : SampleBatch n count =>
        state.addBatch batch) :=
      measurable_addBatch.comp (measurable_const.prodMk measurable_id)
    simp only [costedCharge, Measure.map_dirac]
    exact Measure.measurable_dirac.comp (hstate.prodMk measurable_const)
  · intro batch
    exact costedCharge_isProbabilityMeasure
      (Measure.dirac (state.addBatch batch)) _

/-- Count thinning followed by sampling and append is normalized. -/
theorem community_count_sample_append_isProbabilityMeasure
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (state : TTCState n) (pending : Nat) :
    IsProbabilityMeasure
      (communityCostedCountSampleAppend hn prep factor P b eta delta
        threshold (state, pending)) := by
  letI : IsProbabilityMeasure
      (ttcPseudocode.secondLoopWithCost state pending threshold) :=
    countThinWithCost_isProbabilityMeasure state pending threshold
  unfold communityCostedCountSampleAppend
  apply costedBind_isProbabilityMeasure
  · exact community_sample_append_kernel_measurable hn prep factor
      P b eta delta
  · intro second
    exact community_sample_append_isProbabilityMeasure hn prep factor
      P second.2 b eta delta second.1

theorem community_poisson_count_sample_append_isProbabilityMeasure
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (state : TTCState n) (intensity : NNReal) :
    IsProbabilityMeasure
      (communityCostedPoissonCountSampleAppend hn prep factor P b eta delta
        threshold state intensity) := by
  letI : IsProbabilityMeasure
      (costedCharge (ProbabilityTheory.poissonMeasure (intensity * state.p))
        TTCRuntime.poissonDrawOperations) :=
    costedCharge_isProbabilityMeasure _ _
  unfold communityCostedPoissonCountSampleAppend
  apply costedBind_isProbabilityMeasure
  · exact (community_costed_count_tail_measurable hn prep factor P b
      eta delta threshold).comp (measurable_const.prodMk measurable_id)
  · intro pending
    exact community_count_sample_append_isProbabilityMeasure hn prep
      factor P b eta delta threshold state pending

set_option maxHeartbeats 800000 in
theorem community_rate_tail_mass_one
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (state : TTCState n) (intensity : NNReal) :
    (communityCostedRateTail hn prep factor P b eta delta threshold
      state intensity) Set.univ = 1 := by
  letI : IsProbabilityMeasure
      (ttcReference.firstLoopWithCost state intensity threshold) :=
    rateThinWithCost_isProbabilityMeasure state intensity threshold
  have hpair : Measurable (fun first : TTCState n => (first, intensity)) :=
    measurable_id.prodMk measurable_const
  have hbase := community_poisson_count_sample_append_kernel_measurable
    hn prep factor P b eta delta threshold
  have hnext : Measurable (fun first : TTCState n =>
      communityCostedPoissonCountSampleAppend hn prep factor P b eta delta
        threshold first intensity) := by
    have hcomp := hbase.comp hpair
    change Measurable
      ((fun z : TTCState n × NNReal =>
        communityCostedPoissonCountSampleAppend hn prep factor P b eta delta
          threshold z.1 z.2) ∘
        (fun first : TTCState n => (first, intensity)))
    exact hcomp
  have hprob : IsProbabilityMeasure
      (costedBind (ttcReference.firstLoopWithCost state intensity threshold)
        (fun first => communityCostedPoissonCountSampleAppend hn prep factor P b
          eta delta threshold first intensity)) :=
    costedBind_isProbabilityMeasure _ _ hnext (fun first =>
      community_poisson_count_sample_append_isProbabilityMeasure
        hn prep factor P b eta delta threshold first intensity)
  exact hprob.measure_univ

set_option maxHeartbeats 800000 in
theorem community_deletion_tail_mass_one
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (hthreshold : 0 < threshold)
    (state : TTCState n) (intensity : NNReal) :
    (communityCostedDeletionTail hn prep factor P b eta delta threshold
      state intensity) Set.univ = 1 := by
  let deleted := state.removeComponent P
  let deletionCost := TTCRuntime.deletionPassOperations n
    P.presentation.facetCount state.X.card
      (state.X.card - deleted.X.card)
  have hpair : Measurable (fun s : TTCState n => (s, intensity)) :=
    measurable_id.prodMk measurable_const
  have hbase := community_costed_rate_tail_measurable hn prep factor
    P b eta delta threshold hthreshold
  have hnext : Measurable (fun s : TTCState n =>
      communityCostedRateTail hn prep factor P b eta delta threshold
        s intensity) := by
    have hcomp := hbase.comp hpair
    change Measurable
      ((fun z : TTCState n × NNReal =>
        communityCostedRateTail hn prep factor P b eta delta threshold
          z.1 z.2) ∘ (fun s : TTCState n => (s, intensity)))
    exact hcomp
  letI : IsProbabilityMeasure
      (costedCharge (Measure.dirac deleted) deletionCost) :=
    costedCharge_isProbabilityMeasure _ _
  have hprob : IsProbabilityMeasure
      (costedBind (costedCharge (Measure.dirac deleted) deletionCost)
        (fun afterDeletion => communityCostedRateTail hn prep factor P b eta
          delta threshold afterDeletion intensity)) :=
    costedBind_isProbabilityMeasure _ _ hnext (fun afterDeletion =>
      ⟨community_rate_tail_mass_one hn prep factor P b eta delta
        threshold afterDeletion intensity⟩)
  exact hprob.measure_univ

set_option maxHeartbeats 800000 in
theorem community_component_mass_one
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (hthreshold : 0 < threshold)
    (state : TTCState n)
    (hvolume : IsProbabilityMeasure
      ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
        P eta delta)) :
    (ttcReference.stepWithCost
      (ttcCostedSubroutines hn prep factor)
      b eta delta threshold P state) Set.univ = 1 := by
  letI : IsProbabilityMeasure
      ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
        P eta delta) := hvolume
  have hnext := community_component_tail_measurable hn prep factor P
    b eta delta threshold hthreshold state
  have hprob : IsProbabilityMeasure
      (costedBind
        ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
          P eta delta)
        (communityCostedComponentTail hn prep factor P b eta delta threshold
          state)) :=
    costedBind_isProbabilityMeasure _ _ hnext (fun outcome =>
      ⟨community_deletion_tail_mass_one hn prep factor P b eta delta
        threshold hthreshold state (ttcReference.t b n threshold outcome.2)⟩)
  exact hprob.measure_univ

set_option maxHeartbeats 800000 in
theorem community_components_mass_one
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor b : Nat) (eta delta threshold : Real)
    (hthreshold : 0 < threshold)
    (components : List (PolytopeData n))
    (hvolume : ∀ P ∈ components,
      IsProbabilityMeasure
        ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
          P eta delta))
    (state : TTCState n) :
    (ttcReference.loopWithCost
      (ttcCostedSubroutines hn prep factor)
      b eta delta threshold components state) Set.univ = 1 := by
  induction components generalizing state with
  | nil =>
      simp [ttcReference.loopWithCost]
  | cons P rest ih =>
      have hrest : ∀ Q ∈ rest,
          IsProbabilityMeasure
            ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
              Q eta delta) := by
        intro Q hQ
        exact hvolume Q (by simp [hQ])
      have hrestMass : ∀ Q ∈ rest,
          ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
            Q eta delta) Set.univ ≤ 1 := by
        intro Q hQ
        letI := hrest Q hQ
        simp
      have hmeas := community_components_kernel_measurable hn prep
        factor b eta delta threshold hthreshold rest hrestMass
      letI : IsProbabilityMeasure
          (ttcReference.stepWithCost
            (ttcCostedSubroutines hn prep factor)
            b eta delta threshold P state) :=
        ⟨community_component_mass_one hn prep factor P b eta delta
          threshold hthreshold state (hvolume P (by simp))⟩
      have hprob : IsProbabilityMeasure
          (costedBind
            (ttcReference.stepWithCost
              (ttcCostedSubroutines hn prep factor)
              b eta delta threshold P state)
            (ttcReference.loopWithCost
              (ttcCostedSubroutines hn prep factor)
              b eta delta threshold rest)) :=
        costedBind_isProbabilityMeasure _ _ hmeas (fun nextState =>
          ⟨ih hrest nextState⟩)
      exact hprob.measure_univ

end ttc
