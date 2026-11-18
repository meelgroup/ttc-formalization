import Kr25Ssmxt.Analysis.PrecisionRequirements
import Kr25Ssmxt.Analysis.RuntimeBudgets
import Kr25Ssmxt.Analysis.PrecisionChoice
import Kr25Ssmxt.Analysis.PoissonMean
import Kr25Ssmxt.Analysis.ScaledVolumeBridge
import Kr25Ssmxt.Analysis.TTCPaperRuntime
import Kr25Ssmxt.Analysis.RateKernelMeasurable
import Kr25Ssmxt.Analysis.MeasurableAddBatch
import Kr25Ssmxt.Analysis.MeasurablePoissonMeasure
import Kr25Ssmxt.Analysis.MeasurableRemoveComponent

/-! Expected cost of the paper's adaptive rate and count thinning stages. -/

namespace Kr25Ssmxt

open MeasureTheory ProbabilityTheory

/-! ### Kernel measurability of the charged component stages

Mathlib's `Measure.bind` and `Measure.map` accounting lemmas require
measurable continuations. These private lemmas supply them for the concrete
community oracles; they mirror the output-marginal proofs downstream. -/

private theorem ce_samples_mass_le_one_all
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (count b : Nat)
    (eta delta : Real) :
    ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
      P count b eta) Set.univ ≤ 1 := by
  classical
  by_cases h : 1 ≤ decimalScale b * P.inradius ∧ 0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧ (codedLatticePoints P b).Nonempty
  · exact communityCosted_samples_mass_le_one hn prep factor
      P count b eta delta h
  · simp [ttcCostedSubroutines, h, costedCharge,
      failedSampleBatchLaw]

private theorem ce_append_charge_measurable {n count : Nat}
    (state : TTCState n) (charge : Nat) :
    Measurable (fun batch : SampleBatch n count =>
      costedCharge (Measure.dirac (state.addBatch batch)) charge) := by
  have hf : Measurable (fun batch : SampleBatch n count => state.addBatch batch) :=
    measurable_addBatch.comp
      (measurable_const.prodMk measurable_id)
  exact (Measure.measurable_map _ (by fun_prop)).comp
    (Measure.measurable_dirac.comp hf)

private theorem ce_sample_append_kernel_measurable
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
    ce_samples_mass_le_one_all hn prep factor P count b eta delta
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

private theorem ce_count_sample_append_kernel_measurable
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) :
    Measurable (fun z : TTCState n × Nat =>
      costedBind (ttcPseudocode.secondLoopWithCost z.1 z.2 threshold)
        (fun secondThinned => costedBind
          ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
            P secondThinned.2 b eta)
          (fun batch => costedCharge
            (Measure.dirac (secondThinned.1.addBatch batch))
            (secondThinned.2 * TTCRuntime.appendCopyOperations)))) := by
  have h := costedBind_kernel_measurable
      (fun z : TTCState n × Nat => ttcPseudocode.secondLoopWithCost z.1 z.2 threshold) _
      (countThinWithCost_kernel_measurable threshold)
      (ce_sample_append_kernel_measurable hn prep factor P b eta delta)
  exact h

private theorem ce_state_rate_measurable {n : Nat} :
    Measurable (fun s : TTCState n => s.p) :=
  measurable_fst.comp (comap_measurable _ : Measurable (fun s : TTCState n =>
    (s.p, s.X, s.nextLabel)))

private theorem ce_poisson_count_kernel_measurable {n : Nat}
    (intensity : NNReal) (threshold : Real) :
    Measurable (fun firstThinned : TTCState n =>
      costedBind
        (costedCharge (poissonMeasure (intensity * firstThinned.p))
          TTCRuntime.poissonDrawOperations)
        (fun pending => ttcPseudocode.secondLoopWithCost firstThinned pending threshold)) := by
  have h := measurable_nat_costedCharge_bind_kernel
      (fun firstThinned : TTCState n => poissonMeasure (intensity * firstThinned.p))
      (fun z : TTCState n × Nat => ttcPseudocode.secondLoopWithCost z.1 z.2 threshold)
      TTCRuntime.poissonDrawOperations
      (measurable_poissonMeasure.comp (measurable_const.mul ce_state_rate_measurable))
      (countThinWithCost_kernel_measurable threshold)
  exact h

private theorem ce_poisson_count_sample_joint_measurable
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) :
    Measurable (fun z : TTCState n × NNReal =>
      costedBind
        (costedCharge (poissonMeasure (z.2 * z.1.p))
          TTCRuntime.poissonDrawOperations)
        (fun pending =>
          costedBind (ttcPseudocode.secondLoopWithCost z.1 pending threshold)
            (fun secondThinned => costedBind
              ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
                P secondThinned.2 b eta)
              (fun batch => costedCharge
                (Measure.dirac (secondThinned.1.addBatch batch))
                (secondThinned.2 * TTCRuntime.appendCopyOperations))))) := by
  have hlaw : Measurable (fun z : TTCState n × NNReal => poissonMeasure (z.2 * z.1.p)) := by
    have h := measurable_poissonMeasure.comp
      ((measurable_snd : Measurable (fun z : TTCState n × NNReal => z.2)).mul
        ((ce_state_rate_measurable (n := n)).comp measurable_fst))
    exact h
  have hnext : Measurable (fun w : (TTCState n × NNReal) × Nat =>
      costedBind (ttcPseudocode.secondLoopWithCost w.1.1 w.2 threshold)
        (fun secondThinned => costedBind
          ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
            P secondThinned.2 b eta)
          (fun batch => costedCharge
            (Measure.dirac (secondThinned.1.addBatch batch))
            (secondThinned.2 * TTCRuntime.appendCopyOperations)))) := by
    have h := (ce_count_sample_append_kernel_measurable hn prep factor P b eta delta
      threshold).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd :
        Measurable (fun w : (TTCState n × NNReal) × Nat => (w.1.1, w.2)))
    exact h
  have h := measurable_nat_costedCharge_bind_kernel _ _
    TTCRuntime.poissonDrawOperations hlaw hnext
  exact h

private theorem ce_rate_tail_joint_measurable
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (hthreshold : 0 < threshold) :
    Measurable (fun z : TTCState n × NNReal =>
      costedBind (ttcReference.firstLoopWithCost z.1 z.2 threshold)
        (fun firstThinned =>
          costedBind
            (costedCharge (poissonMeasure (z.2 * firstThinned.p))
              TTCRuntime.poissonDrawOperations)
            (fun pending =>
              costedBind (ttcPseudocode.secondLoopWithCost firstThinned pending threshold)
                (fun secondThinned => costedBind
                  ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
                    P secondThinned.2 b eta)
                  (fun batch => costedCharge
                    (Measure.dirac (secondThinned.1.addBatch batch))
                    (secondThinned.2 * TTCRuntime.appendCopyOperations)))))) := by
  have hnext : Measurable (fun w : (TTCState n × NNReal) × TTCState n =>
      costedBind
        (costedCharge (poissonMeasure (w.1.2 * w.2.p))
          TTCRuntime.poissonDrawOperations)
        (fun pending =>
          costedBind (ttcPseudocode.secondLoopWithCost w.2 pending threshold)
            (fun secondThinned => costedBind
              ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
                P secondThinned.2 b eta)
              (fun batch => costedCharge
                (Measure.dirac (secondThinned.1.addBatch batch))
                (secondThinned.2 * TTCRuntime.appendCopyOperations))))) := by
    have h := (ce_poisson_count_sample_joint_measurable hn prep factor P b eta delta
      threshold).comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst) :
        Measurable (fun w : (TTCState n × NNReal) × TTCState n => (w.2, w.1.2)))
    exact h
  have h := measurable_costedBind_dependent_finite _ _
    (rateThinWithCost_kernel_measurable threshold hthreshold) hnext
    (fun z => rateThinWithCost_mass_le_one z.1 z.2 threshold)
  exact h

private theorem ce_poisson_count_sample_measurable
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (intensity : NNReal) :
    Measurable (fun firstThinned : TTCState n =>
      costedBind
        (costedCharge (poissonMeasure (intensity * firstThinned.p))
          TTCRuntime.poissonDrawOperations)
        (fun pending =>
          costedBind (ttcPseudocode.secondLoopWithCost firstThinned pending threshold)
            (fun secondThinned => costedBind
              ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
                P secondThinned.2 b eta)
              (fun batch => costedCharge
                (Measure.dirac (secondThinned.1.addBatch batch))
                (secondThinned.2 * TTCRuntime.appendCopyOperations))))) := by
  have h := (ce_poisson_count_sample_joint_measurable hn prep factor P b eta delta
    threshold).comp (measurable_id.prodMk measurable_const :
      Measurable (fun s : TTCState n => (s, intensity)))
  exact h

private theorem ce_rate_tail_measurable
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (hthreshold : 0 < threshold) (intensity : NNReal) :
    Measurable (fun deleted : TTCState n =>
      costedBind (ttcReference.firstLoopWithCost deleted intensity threshold)
        (fun firstThinned =>
          costedBind
            (costedCharge (poissonMeasure (intensity * firstThinned.p))
              TTCRuntime.poissonDrawOperations)
            (fun pending =>
              costedBind (ttcPseudocode.secondLoopWithCost firstThinned pending threshold)
                (fun secondThinned => costedBind
                  ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
                    P secondThinned.2 b eta)
                  (fun batch => costedCharge
                    (Measure.dirac (secondThinned.1.addBatch batch))
                    (secondThinned.2 * TTCRuntime.appendCopyOperations)))))) := by
  have h := (ce_rate_tail_joint_measurable hn prep factor P b eta delta threshold
    hthreshold).comp (measurable_id.prodMk measurable_const :
      Measurable (fun s : TTCState n => (s, intensity)))
  exact h

private theorem ce_deletion_pair_measurable {n : Nat}
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

private theorem ce_deletion_tail_joint_measurable
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (hthreshold : 0 < threshold) :
    Measurable (fun z : TTCState n × NNReal =>
      costedBind
        (costedCharge (Measure.dirac (z.1.removeComponent P))
          (TTCRuntime.deletionPassOperations n P.presentation.facetCount
            z.1.X.card
            (z.1.X.card - (z.1.removeComponent P).X.card)))
        (fun deleted =>
          costedBind (ttcReference.firstLoopWithCost deleted z.2 threshold)
            (fun firstThinned =>
              costedBind
                (costedCharge (poissonMeasure (z.2 * firstThinned.p))
                  TTCRuntime.poissonDrawOperations)
                (fun pending =>
                  costedBind (ttcPseudocode.secondLoopWithCost firstThinned pending threshold)
                    (fun secondThinned => costedBind
                      ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
                        P secondThinned.2 b eta)
                      (fun batch => costedCharge
                        (Measure.dirac (secondThinned.1.addBatch batch))
                        (secondThinned.2 * TTCRuntime.appendCopyOperations))))))) := by
  have hpair := (ce_deletion_pair_measurable P).comp
    (measurable_fst : Measurable (fun z : TTCState n × NNReal => z.1))
  have hfirst : Measurable (fun z : TTCState n × NNReal =>
      costedCharge (Measure.dirac (z.1.removeComponent P))
        (TTCRuntime.deletionPassOperations n P.presentation.facetCount
          z.1.X.card
          (z.1.X.card - (z.1.removeComponent P).X.card))) := by
    have heq : (fun z : TTCState n × NNReal =>
        costedCharge (Measure.dirac (z.1.removeComponent P))
          (TTCRuntime.deletionPassOperations n P.presentation.facetCount
            z.1.X.card
            (z.1.X.card - (z.1.removeComponent P).X.card))) =
        (fun z : TTCState n × NNReal => Measure.dirac
          (z.1.removeComponent P,
            TTCRuntime.deletionPassOperations n P.presentation.facetCount
              z.1.X.card
              (z.1.X.card - (z.1.removeComponent P).X.card))) := by
      funext z
      simp only [costedCharge, Measure.map_dirac' (by fun_prop :
        Measurable (fun result : TTCState n => (result,
          TTCRuntime.deletionPassOperations n P.presentation.facetCount
            z.1.X.card
            (z.1.X.card - (z.1.removeComponent P).X.card)))) _]
    rw [heq]
    exact Measure.measurable_dirac.comp hpair
  have hnext : Measurable (fun w : (TTCState n × NNReal) × TTCState n =>
      costedBind (ttcReference.firstLoopWithCost w.2 w.1.2 threshold)
        (fun firstThinned =>
          costedBind
            (costedCharge (poissonMeasure (w.1.2 * firstThinned.p))
              TTCRuntime.poissonDrawOperations)
            (fun pending =>
              costedBind (ttcPseudocode.secondLoopWithCost firstThinned pending threshold)
                (fun secondThinned => costedBind
                  ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
                    P secondThinned.2 b eta)
                  (fun batch => costedCharge
                    (Measure.dirac (secondThinned.1.addBatch batch))
                    (secondThinned.2 * TTCRuntime.appendCopyOperations)))))) := by
    have h := (ce_rate_tail_joint_measurable hn prep factor P b eta delta threshold
      hthreshold).comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst) :
        Measurable (fun w : (TTCState n × NNReal) × TTCState n => (w.2, w.1.2)))
    exact h
  have h := measurable_costedBind_dependent_finite _ _ hfirst hnext
    (fun z => costedCharge_mass_le_one _ _ (by simp))
  exact h

private theorem ce_intensity_measurable (b n : Nat) (threshold : Real) :
    Measurable (fun outcome : VolumeOutcome =>
      ttcReference.t b n threshold outcome.2) := by
  unfold ttcReference.t
  exact measurable_const.mul measurable_snd

private theorem ce_component_tail_joint_measurable
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (hthreshold : 0 < threshold) :
    Measurable (fun z : TTCState n × VolumeOutcome =>
      costedBind
        (costedCharge (Measure.dirac (z.1.removeComponent P))
          (TTCRuntime.deletionPassOperations n P.presentation.facetCount
            z.1.X.card
            (z.1.X.card - (z.1.removeComponent P).X.card)))
        (fun deleted =>
          costedBind (ttcReference.firstLoopWithCost deleted
              (ttcReference.t b n threshold z.2.2) threshold)
            (fun firstThinned =>
              costedBind
                (costedCharge (poissonMeasure
                  (ttcReference.t b n threshold z.2.2 * firstThinned.p))
                  TTCRuntime.poissonDrawOperations)
                (fun pending =>
                  costedBind (ttcPseudocode.secondLoopWithCost firstThinned pending threshold)
                    (fun secondThinned => costedBind
                      ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
                        P secondThinned.2 b eta)
                      (fun batch => costedCharge
                        (Measure.dirac (secondThinned.1.addBatch batch))
                        (secondThinned.2 * TTCRuntime.appendCopyOperations))))))) := by
  have h := (ce_deletion_tail_joint_measurable hn prep factor P b eta delta threshold
      hthreshold).comp
      (measurable_fst.prodMk ((ce_intensity_measurable b n threshold).comp measurable_snd))
  exact h

private theorem ce_component_step_measurable
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (hthreshold : 0 < threshold)
    (state : TTCState n) :
    Measurable (fun volumeOutcome : VolumeOutcome =>
      costedBind
        (costedCharge (Measure.dirac (state.removeComponent P))
          (TTCRuntime.deletionPassOperations n P.presentation.facetCount
            state.X.card
            (state.X.card - (state.removeComponent P).X.card)))
        (fun deleted =>
          costedBind (ttcReference.firstLoopWithCost deleted
              (ttcReference.t b n threshold volumeOutcome.2) threshold)
            (fun firstThinned =>
              costedBind
                (costedCharge (poissonMeasure
                  (ttcReference.t b n threshold volumeOutcome.2 * firstThinned.p))
                  TTCRuntime.poissonDrawOperations)
                (fun pending =>
                  costedBind (ttcPseudocode.secondLoopWithCost firstThinned pending threshold)
                    (fun secondThinned => costedBind
                      ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
                        P secondThinned.2 b eta)
                      (fun batch => costedCharge
                        (Measure.dirac (secondThinned.1.addBatch batch))
                        (secondThinned.2 * TTCRuntime.appendCopyOperations))))))) := by
  have h := (ce_component_tail_joint_measurable hn prep factor P b eta delta threshold
      hthreshold).comp (measurable_const.prodMk measurable_id :
        Measurable (fun volumeOutcome : VolumeOutcome => (state, volumeOutcome)))
  exact h

private theorem ce_component_kernel_measurable
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (factor : Nat) (P : PolytopeData n) (b : Nat)
    (eta delta threshold : Real) (hthreshold : 0 < threshold)
    (hvolume : ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
      P eta delta) Set.univ ≤ 1) :
    Measurable (fun state : TTCState n =>
      ttcReference.stepWithCost
        (ttcCostedSubroutines hn prep factor)
        b eta delta threshold P state) := by
  have h := measurable_costedBind_dependent_finite
      (fun _ : TTCState n =>
        (ttcCostedSubroutines hn prep factor).computeVolumeWithCost
          P eta delta) _
      measurable_const
      (ce_component_tail_joint_measurable hn prep factor P b eta delta threshold
        hthreshold)
      (fun _ => hvolume)
  exact h

private theorem ce_components_kernel_measurable
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
      have hrest : ∀ Q ∈ rest,
          ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
            Q eta delta) Set.univ ≤ 1 := by
        intro Q hQ
        exact hvolume Q (by simp [hQ])
      change Measurable (fun state : TTCState n =>
        costedBind
          (ttcReference.stepWithCost
            (ttcCostedSubroutines hn prep factor)
            b eta delta threshold P state)
          (ttcReference.loopWithCost
            (ttcCostedSubroutines hn prep factor)
            b eta delta threshold rest))
      exact costedBind_kernel_measurable _ _
        (ce_component_kernel_measurable hn prep factor P b eta delta threshold
          hthreshold (hvolume P (by simp)))
        (ih hrest)

private theorem ce_estimate_measurable {n : Nat} (b : Nat)
    (threshold : Real) :
    Measurable (EstReference (n := n) b threshold) := by
  have hcoords : Measurable (fun s : TTCState n =>
      (s.p, s.X, s.nextLabel)) := comap_measurable _
  have hrate : Measurable (fun s : TTCState n => s.p) :=
    measurable_fst.comp hcoords
  have hsamples : Measurable (fun s : TTCState n => s.X) :=
    (measurable_fst.comp measurable_snd).comp hcoords
  have hcount : Measurable (fun s : TTCState n =>
      (s.X.card : NNReal)) :=
    (measurable_of_countable (fun copies : Finset (SampleCopy n) =>
      (copies.card : NNReal))).comp hsamples
  unfold EstReference
  exact hcount.div ((hrate.mul_const _).mul_const _)


theorem intensity_mono_volume (b n : Nat) (threshold : Real)
    {small large : NNReal} (hvol : small ≤ large) :
    ttcReference.t b n threshold small ≤
      ttcReference.t b n threshold large := by
  unfold ttcReference.t
  gcongr

/-- The rate check is charged at most one thinning pass. -/
theorem rateThinningCost_le_round {n : Nat}
    (s : TTCState n) (intensity : NNReal) (threshold : Real) :
    ttcReference.firstLoopCost s intensity threshold ≤
      TTCRuntime.rateThinningRoundOperations s.X.card := by
  unfold ttcReference.firstLoopCost
  split_ifs <;> omega

theorem certified_community_volume_mass_le_one {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (i : Fin D.componentCount) :
    (communityCV18VolumeLaw (by omega) (D.component i) p.ε'
      (p.δ' D.componentCount)) Set.univ ≤ 1 := by
  letI : IsProbabilityMeasure
      (communityCV18VolumeLaw (by omega) (D.component i) p.ε'
        (p.δ' D.componentCount)) :=
    (CommunityCV18.communityCV18VolumeLaw_spec (by omega) (D.component i)
      p.ε' (p.δ' D.componentCount)
      (PaperRuntime.ttc_request_admissible D p i)).1
  simp

theorem certified_community_volume_continuation_bound {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) (f : VolumeOutcome → ENNReal)
    {budget : ENNReal}
    (hbudget : ∀ outcome : VolumeOutcome, f outcome ≤ budget) :
    (∫⁻ result, (result.2 : ENNReal) + f result.1 ∂
      (ttcCostedSubroutines hn prep factor).computeVolumeWithCost
        (D.component i) p.ε' (p.δ' D.componentCount)) ≤
      (TTCRuntime.membershipQueryOperations n
          (D.component i).presentation.facetCount
          (CommunityCV18.queryBudgetFor (by omega) (D.component i)
            p.ε' (p.δ' D.componentCount)) +
        factor * TTCRuntime.membershipQueryOperations n
          (D.component i).presentation.facetCount
          (CommunityCV18.queryBudgetFor (by omega) (D.component i)
            p.ε' (p.δ' D.componentCount) + 1) : ENNReal) + budget := by
  have hbase := costedCharge_map_continuation_bound
    (communityCV18VolumeLaw (by omega) (D.component i) p.ε'
      (p.δ' D.componentCount))
    id aemeasurable_id
    (TTCRuntime.membershipQueryOperations n
      (D.component i).presentation.facetCount
      (CommunityCV18.queryBudgetFor (by omega) (D.component i)
        p.ε' (p.δ' D.componentCount)) +
      factor * TTCRuntime.membershipQueryOperations n
        (D.component i).presentation.facetCount
        (CommunityCV18.queryBudgetFor (by omega) (D.component i)
          p.ε' (p.δ' D.componentCount) + 1))
    f (certified_community_volume_mass_le_one hn D p i) hbudget
  simpa only [ttcCostedSubroutines, ttcSubroutines, Measure.map_id,
    Nat.cast_add, Nat.cast_mul] using hbase

private noncomputable def componentNonVolumeBudget {n : Nat} (p : ApproxParams) (m b : Nat)
    (P : PolytopeData n) (state : TTCState n) : ENNReal :=
  let deleted := state.removeComponent P
  state.X.card * (TTCRuntime.facetScanOperations n P.presentation.facetCount + 1) +
  TTCRuntime.rateThinningRoundOperations deleted.X.card +
  TTCRuntime.poissonDrawOperations +
  4 * TTCRuntime.countThinningRoundOperations state.X.card +
  (TTCRuntime.ThresholdCap p m : ENNReal) *
    (2 * TTCRuntime.samplingAttemptOperations n P.presentation.facetCount
      (normalizedHitAndRunSteps P b p.ε') +
      TTCRuntime.appendCopyOperations)

private noncomputable def componentUniformBudget {n : Nat} (p : ApproxParams)
    (m b : Nat) (P : PolytopeData n) : ENNReal :=
  let cap := TTCRuntime.ThresholdCap p m
  let upperIntensity := ttcReference.t b n (p.Thresh m)
    (max (P.volumeClipLower p.ε')
      (P.volumeClipUpper p.ε'))
  cap * (TTCRuntime.facetScanOperations n P.presentation.facetCount + 1) +
  (Nat.clog 2 (Nat.ceil ((upperIntensity : Real) / p.Thresh m) + 1) : ENNReal) *
    TTCRuntime.rateThinningRoundOperations cap +
  TTCRuntime.poissonDrawOperations +
  4 * TTCRuntime.countThinningRoundOperations cap +
  (cap : ENNReal) *
    (2 * TTCRuntime.samplingAttemptOperations n P.presentation.facetCount
      (normalizedHitAndRunSteps P b p.ε') +
      TTCRuntime.appendCopyOperations)

private noncomputable def uniformComponentCost {n : Nat} (hn : 21 ≤ n)
    (p : ApproxParams) (m b factor : Nat) (P : PolytopeData n) : ENNReal :=
  (TTCRuntime.membershipQueryOperations n P.presentation.facetCount
      (CommunityCV18.queryBudgetFor (by omega) P p.ε' (p.δ' m)) +
    factor * TTCRuntime.membershipQueryOperations n P.presentation.facetCount
      (CommunityCV18.queryBudgetFor (by omega) P p.ε' (p.δ' m) + 1) :
      ENNReal) +
    componentUniformBudget p m b P

private theorem uniformComponentCost_eq_model {n : Nat} (hn : 21 ≤ n)
    (p : ApproxParams) (m b factor : Nat) (P : PolytopeData n) :
    uniformComponentCost hn p m b factor P =
      TTCRuntime.expectedComponentBudget hn p m b factor P := by
  unfold uniformComponentCost componentUniformBudget
    TTCRuntime.expectedComponentBudget
  simp only [Nat.cast_add, Nat.cast_mul, add_assoc]

theorem ratePoissonCount_expected_cost_le {n : Nat}
    (s : TTCState n) (intensity : NNReal) (threshold : Real)
    (hthreshold : 0 < threshold)
    (hsamples : (s.X.card : Real) ≤ threshold) :
    ∫⁻ result, (result.2 : ENNReal) ∂
      costedBind (ttcReference.firstLoopWithCost s intensity threshold)
        (fun firstThinned =>
          costedBind
            (costedCharge
              (poissonMeasure (intensity * firstThinned.p))
              TTCRuntime.poissonDrawOperations)
            (fun pending => ttcPseudocode.secondLoopWithCost firstThinned pending threshold)) ≤
      ttcReference.firstLoopCost s intensity threshold +
        (TTCRuntime.poissonDrawOperations +
          4 * TTCRuntime.countThinningRoundOperations s.X.card) := by
  let next : TTCState n → Measure ((TTCState n × Nat) × Nat) := fun firstThinned =>
    costedBind
      (costedCharge
        (poissonMeasure (intensity * firstThinned.p))
        TTCRuntime.poissonDrawOperations)
      (fun pending => ttcPseudocode.secondLoopWithCost firstThinned pending threshold)
  have hnextMass (firstThinned : TTCState n) :
      (next firstThinned) Set.univ ≤ 1 := by
    refine costedBind_mass_le_one _ _ (measurable_of_countable _) ?_ ?_
    · apply costedCharge_mass_le_one
      simp
    · intro pending
      exact countThinWithCost_mass_le_one firstThinned pending threshold
  have hnextMeas : Measurable next :=
    ce_poisson_count_kernel_measurable intensity threshold
  apply (costedBind_lintegral_cost_le _ next hnextMeas hnextMass).trans
  unfold ttcReference.firstLoopWithCost
  apply (lintegral_map_le _
    ((measurable_rateThinningResult s intensity threshold).prodMk
      measurable_const).aemeasurable).trans
  simp only
  rw [lintegral_add_left (by fun_prop)]
  haveI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  simp only [lintegral_const, measure_univ, mul_one]
  apply add_le_add_right
  calc
    _ ≤ ∫⁻ _coins : Nat × Nat → Bool,
        ((TTCRuntime.poissonDrawOperations : ENNReal) +
          4 * TTCRuntime.countThinningRoundOperations s.X.card)
          ∂fairCoinStreamLaw := by
      apply lintegral_mono
      intro coins
      have hcard := rateThinningResult_card_le s intensity threshold coins
      have hcardReal :
          ((ttcReference.firstLoopResult s intensity threshold coins).X.card : Real) ≤
            threshold := (Nat.cast_le.mpr hcard).trans hsamples
      have hguard := rateThinningResult_guard s intensity hthreshold coins
      have hcost := poissonCountThin_expected_cost_le
        (ttcReference.firstLoopResult s intensity threshold coins)
        (intensity * (ttcReference.firstLoopResult s intensity threshold coins).p)
        threshold hthreshold.le hcardReal hguard
      have hround :
          TTCRuntime.countThinningRoundOperations
              (ttcReference.firstLoopResult s intensity threshold coins).X.card ≤
            TTCRuntime.countThinningRoundOperations s.X.card := by
        unfold TTCRuntime.countThinningRoundOperations TTCRuntime.fairCoinOperations
          TTCRuntime.binomialDrawOperations TTCRuntime.scalarOperationCost
        omega
      exact hcost.trans (add_le_add_right
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hround) (by positivity)) _)
    _ = _ := by simp

/-- Appending a generated batch adds exactly one charge per requested copy;
this bound composes with any certified sample oracle. -/
theorem sampleAppend_expected_cost_le {n : Nat} {count : Nat}
    (state : TTCState n) (sampleLaw : Measure (SampleBatch n count × Nat))
    (hsampleMass : sampleLaw Set.univ ≤ 1)
    {sampleBudget : ENNReal}
    (hsampleCost : (∫⁻ result, (result.2 : ENNReal) ∂sampleLaw) ≤
      sampleBudget) :
    (∫⁻ result, (result.2 : ENNReal) ∂
      costedBind sampleLaw (fun batch =>
        costedCharge (Measure.dirac (state.addBatch batch))
          (count * TTCRuntime.appendCopyOperations))) ≤
      sampleBudget + count * TTCRuntime.appendCopyOperations := by
  apply costedBind_expected_cost_le_add sampleLaw _
    (ce_append_charge_measurable state _) hsampleMass
  · intro batch
    apply costedCharge_mass_le_one
    simp
  · exact hsampleCost
  · intro batch
    letI : IsProbabilityMeasure (Measure.dirac (state.addBatch batch)) :=
      inferInstance
    simpa only [Nat.cast_mul] using
      (costedCharge_expected_cost
        (Measure.dirac (state.addBatch batch))
        (count * TTCRuntime.appendCopyOperations)).le

theorem certified_community_sample_append_expected_cost {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (prep : TTCPreprocessor n k) (factor count : Nat)
    (delta : Real) (i : Fin D.componentCount) (state : TTCState n) :
    ∫⁻ result, (result.2 : ENNReal) ∂
      costedBind
        ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
          (D.component i) count b p.ε')
        (fun batch => costedCharge (Measure.dirac (state.addBatch batch))
          (count * TTCRuntime.appendCopyOperations)) ≤
      count * (2 * TTCRuntime.samplingAttemptOperations n
        (D.component i).presentation.facetCount
        (normalizedHitAndRunSteps (D.component i) b p.ε')) +
        count * TTCRuntime.appendCopyOperations := by
  exact sampleAppend_expected_cost_le state _
    (certified_community_sampler_mass_le_one hn D p b hprecision prep factor
      count delta i)
    (certified_community_sampler_expected_cost hn D p b hprecision prep factor
      count delta i)

/-- One charged second loop, followed by the actual sampler and append,
costs at most its thinning charge plus the threshold-sized sampling budget. -/
theorem certified_count_sample_append_expected_cost {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (prep : TTCPreprocessor n k) (factor pending : Nat)
    (i : Fin D.componentCount) (state : TTCState n) :
    ∫⁻ result, (result.2 : ENNReal) ∂
      costedBind
        (ttcPseudocode.secondLoopWithCost state pending (p.Thresh D.componentCount))
        (fun secondThinned =>
          costedBind
            ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
              (D.component i) secondThinned.2 b p.ε')
            (fun batch => costedCharge
              (Measure.dirac (secondThinned.1.addBatch batch))
              (secondThinned.2 * TTCRuntime.appendCopyOperations))) ≤
      (∫⁻ result, (result.2 : ENNReal) ∂
        ttcPseudocode.secondLoopWithCost state pending (p.Thresh D.componentCount)) +
      (TTCRuntime.ThresholdCap p D.componentCount : ENNReal) *
        (2 * TTCRuntime.samplingAttemptOperations n
          (D.component i).presentation.facetCount
          (normalizedHitAndRunSteps (D.component i) b p.ε') +
          TTCRuntime.appendCopyOperations) := by
  let threshold := p.Thresh D.componentCount
  let stepCost : ENNReal := 2 * TTCRuntime.samplingAttemptOperations n
    (D.component i).presentation.facetCount
    (normalizedHitAndRunSteps (D.component i) b p.ε') +
    TTCRuntime.appendCopyOperations
  let next : (TTCState n × Nat) → Measure (TTCState n × Nat) :=
    fun secondThinned =>
      costedBind
        ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
          (D.component i) secondThinned.2 b p.ε')
        (fun batch => costedCharge
          (Measure.dirac (secondThinned.1.addBatch batch))
          (secondThinned.2 * TTCRuntime.appendCopyOperations))
  have hnextMass (secondThinned : TTCState n × Nat) :
      (next secondThinned) Set.univ ≤ 1 := by
    refine costedBind_mass_le_one _ _ (ce_append_charge_measurable _ _) ?_ ?_
    · exact certified_community_sampler_mass_le_one hn D p b hprecision
        prep factor secondThinned.2 (p.δ' D.componentCount) i
    · intro batch
      apply costedCharge_mass_le_one
      simp
  have hnextMeas : Measurable next :=
    ce_sample_append_kernel_measurable hn prep factor (D.component i) b
      p.ε' (p.δ' D.componentCount)
  apply (costedBind_lintegral_cost_le _ next hnextMeas hnextMass).trans
  rw [lintegral_add_left (by fun_prop)]
  apply add_le_add_right
  have hnextCost (secondThinned : TTCState n × Nat) :
      (∫⁻ result, (result.2 : ENNReal) ∂next secondThinned) ≤
        secondThinned.2 * stepCost := by
    have h := certified_community_sample_append_expected_cost hn D p b
      hprecision prep factor secondThinned.2 (p.δ' D.componentCount)
      i secondThinned.1
    calc
      _ ≤ (secondThinned.2 : ENNReal) *
          (2 * TTCRuntime.samplingAttemptOperations n
            (D.component i).presentation.facetCount
            (normalizedHitAndRunSteps (D.component i) b p.ε')) +
          (secondThinned.2 : ENNReal) * TTCRuntime.appendCopyOperations := h
      _ = secondThinned.2 * stepCost := by ring
  calc
    (∫⁻ result,
        (∫⁻ future, (future.2 : ENNReal) ∂next result.1) ∂
          ttcPseudocode.secondLoopWithCost state pending threshold) ≤
      ∫⁻ result, (result.1.2 : ENNReal) * stepCost ∂
        ttcPseudocode.secondLoopWithCost state pending threshold := by
      exact lintegral_mono (fun result => hnextCost result.1)
    _ ≤ ∫⁻ _result, (TTCRuntime.ThresholdCap p D.componentCount : ENNReal) *
        stepCost ∂ttcPseudocode.secondLoopWithCost state pending threshold := by
      apply lintegral_mono_ae
      filter_upwards [countThinWithCost_population_le_ae state pending
        threshold (p.threshold_pos D.componentCount).le] with result hguard
      have hcount : result.1.2 ≤ TTCRuntime.ThresholdCap p D.componentCount := by
        have hreal : (result.1.2 : Real) ≤ threshold := by
          have hnonneg : (0 : Real) ≤ result.1.1.X.card := by positivity
          exact (le_add_of_nonneg_left hnonneg).trans
            (by simpa only [Nat.cast_add] using hguard)
        exact_mod_cast hreal.trans (Nat.le_ceil threshold)
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcount) (by positivity)
    _ ≤ (TTCRuntime.ThresholdCap p D.componentCount : ENNReal) * stepCost := by
      simp only [lintegral_const]
      exact mul_le_of_le_one_right (by positivity)
        (countThinWithCost_mass_le_one state pending threshold)

theorem certified_count_sample_append_mass_le_one {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (prep : TTCPreprocessor n k) (factor pending : Nat)
    (i : Fin D.componentCount) (state : TTCState n) :
    (costedBind
      (ttcPseudocode.secondLoopWithCost state pending (p.Thresh D.componentCount))
      (fun secondThinned =>
        costedBind
          ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
            (D.component i) secondThinned.2 b p.ε')
          (fun batch => costedCharge
            (Measure.dirac (secondThinned.1.addBatch batch))
            (secondThinned.2 * TTCRuntime.appendCopyOperations)))) Set.univ ≤ 1 := by
  refine costedBind_mass_le_one _ _
    (ce_sample_append_kernel_measurable hn prep factor (D.component i) b
      p.ε' (p.δ' D.componentCount)) ?_ ?_
  · exact countThinWithCost_mass_le_one state pending _
  · intro secondThinned
    refine costedBind_mass_le_one _ _ (ce_append_charge_measurable _ _) ?_ ?_
    · exact certified_community_sampler_mass_le_one hn D p b hprecision
        prep factor secondThinned.2 (p.δ' D.componentCount) i
    · intro batch
      apply costedCharge_mass_le_one
      simp

/-- Poisson draw, count thinning, sampling and append have a per-component
budget once the first rate guard has been reached. -/
theorem certified_poisson_count_sample_expected_cost {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) (state : TTCState n) (rate : NNReal)
    (hsamples : (state.X.card : Real) ≤ p.Thresh D.componentCount)
    (hrate : (rate : Real) ≤ p.Thresh D.componentCount) :
    ∫⁻ result, (result.2 : ENNReal) ∂
      costedBind
        (costedCharge (poissonMeasure rate) TTCRuntime.poissonDrawOperations)
        (fun pending =>
          costedBind
            (ttcPseudocode.secondLoopWithCost state pending (p.Thresh D.componentCount))
            (fun secondThinned =>
              costedBind
                ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
                  (D.component i) secondThinned.2 b p.ε')
                (fun batch => costedCharge
                  (Measure.dirac (secondThinned.1.addBatch batch))
                  (secondThinned.2 * TTCRuntime.appendCopyOperations)))) ≤
      TTCRuntime.poissonDrawOperations +
        4 * TTCRuntime.countThinningRoundOperations state.X.card +
        (TTCRuntime.ThresholdCap p D.componentCount : ENNReal) *
          (2 * TTCRuntime.samplingAttemptOperations n
            (D.component i).presentation.facetCount
            (normalizedHitAndRunSteps (D.component i) b p.ε') +
            TTCRuntime.appendCopyOperations) := by
  let threshold := p.Thresh D.componentCount
  let sampleBudget : ENNReal := (TTCRuntime.ThresholdCap p D.componentCount : ENNReal) *
    (2 * TTCRuntime.samplingAttemptOperations n
      (D.component i).presentation.facetCount
      (normalizedHitAndRunSteps (D.component i) b p.ε') +
      TTCRuntime.appendCopyOperations)
  let next : Nat → Measure (TTCState n × Nat) := fun pending =>
    costedBind (ttcPseudocode.secondLoopWithCost state pending threshold)
      (fun secondThinned =>
        costedBind
          ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
            (D.component i) secondThinned.2 b p.ε')
          (fun batch => costedCharge
            (Measure.dirac (secondThinned.1.addBatch batch))
            (secondThinned.2 * TTCRuntime.appendCopyOperations)))
  have hnextMass (pending : Nat) : (next pending) Set.univ ≤ 1 :=
    certified_count_sample_append_mass_le_one hn D p b hprecision prep factor
      pending i state
  apply (costedBind_lintegral_cost_le _ next (measurable_of_countable _) hnextMass).trans
  unfold costedCharge
  apply (lintegral_map_le _ (measurable_id.prodMk measurable_const).aemeasurable).trans
  simp only
  rw [lintegral_add_left (by fun_prop)]
  simp only [lintegral_const, measure_univ, mul_one]
  have hpoint (pending : Nat) :
      (∫⁻ result, (result.2 : ENNReal) ∂next pending) ≤
      (∫⁻ result, (result.2 : ENNReal) ∂
        ttcPseudocode.secondLoopWithCost state pending threshold) + sampleBudget :=
    certified_count_sample_append_expected_cost hn D p b hprecision prep factor
      pending i state
  have hmean := poisson_averaged_countThinCost_le_four_of_guard state rate
    threshold (p.threshold_pos D.componentCount).le hsamples hrate
  calc
    _ ≤ (TTCRuntime.poissonDrawOperations : ENNReal) +
        ∫⁻ pending : Nat,
          ((∫⁻ result, (result.2 : ENNReal) ∂
              ttcPseudocode.secondLoopWithCost state pending threshold) + sampleBudget)
            ∂poissonMeasure rate := by
      exact add_le_add_right (lintegral_mono hpoint) _
    _ = TTCRuntime.poissonDrawOperations +
        (∫⁻ pending : Nat, (∫⁻ result, (result.2 : ENNReal) ∂
          ttcPseudocode.secondLoopWithCost state pending threshold) ∂poissonMeasure rate) +
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
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) (state : TTCState n) (intensity : NNReal)
    (hsamples : (state.X.card : Real) ≤ p.Thresh D.componentCount) :
    ∫⁻ result, (result.2 : ENNReal) ∂
      costedBind
        (ttcReference.firstLoopWithCost state intensity (p.Thresh D.componentCount))
        (fun firstThinned =>
          costedBind
            (costedCharge
              (poissonMeasure (intensity * firstThinned.p))
              TTCRuntime.poissonDrawOperations)
            (fun pending =>
              costedBind
                (ttcPseudocode.secondLoopWithCost firstThinned pending
                  (p.Thresh D.componentCount))
                (fun secondThinned =>
                  costedBind
                    ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
                      (D.component i) secondThinned.2 b p.ε')
                    (fun batch => costedCharge
                      (Measure.dirac (secondThinned.1.addBatch batch))
                      (secondThinned.2 * TTCRuntime.appendCopyOperations))))) ≤
      ttcReference.firstLoopCost state intensity (p.Thresh D.componentCount) +
        TTCRuntime.poissonDrawOperations +
        4 * TTCRuntime.countThinningRoundOperations state.X.card +
        (TTCRuntime.ThresholdCap p D.componentCount : ENNReal) *
          (2 * TTCRuntime.samplingAttemptOperations n
            (D.component i).presentation.facetCount
            (normalizedHitAndRunSteps (D.component i) b p.ε') +
            TTCRuntime.appendCopyOperations) := by
  let threshold := p.Thresh D.componentCount
  let sampleBudget : ENNReal := (TTCRuntime.ThresholdCap p D.componentCount : ENNReal) *
    (2 * TTCRuntime.samplingAttemptOperations n
      (D.component i).presentation.facetCount
      (normalizedHitAndRunSteps (D.component i) b p.ε') +
      TTCRuntime.appendCopyOperations)
  let next : TTCState n → Measure (TTCState n × Nat) := fun firstThinned =>
    costedBind
      (costedCharge
        (poissonMeasure (intensity * firstThinned.p))
        TTCRuntime.poissonDrawOperations)
      (fun pending =>
        costedBind
          (ttcPseudocode.secondLoopWithCost firstThinned pending threshold)
          (fun secondThinned =>
            costedBind
              ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
                (D.component i) secondThinned.2 b p.ε')
              (fun batch => costedCharge
                (Measure.dirac (secondThinned.1.addBatch batch))
                (secondThinned.2 * TTCRuntime.appendCopyOperations))))
  have hnextMass (firstThinned : TTCState n) :
      (next firstThinned) Set.univ ≤ 1 := by
    refine costedBind_mass_le_one _ _ (measurable_of_countable _) ?_ ?_
    · apply costedCharge_mass_le_one
      simp
    · intro pending
      exact certified_count_sample_append_mass_le_one hn D p b hprecision
        prep factor pending i firstThinned
  have hnextMeas : Measurable next :=
    ce_poisson_count_sample_measurable hn prep factor (D.component i) b
      p.ε' (p.δ' D.componentCount) threshold intensity
  apply (costedBind_lintegral_cost_le _ next hnextMeas hnextMass).trans
  unfold ttcReference.firstLoopWithCost
  apply (lintegral_map_le _
    ((measurable_rateThinningResult state intensity threshold).prodMk
      measurable_const).aemeasurable).trans
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
          4 * TTCRuntime.countThinningRoundOperations state.X.card +
          sampleBudget) ∂fairCoinStreamLaw := by
      apply lintegral_mono
      intro coins
      have hcard := rateThinningResult_card_le state intensity threshold coins
      have hcardReal :
          ((ttcReference.firstLoopResult state intensity threshold coins).X.card :
            Real) ≤ threshold := (Nat.cast_le.mpr hcard).trans hsamples
      have hguard := rateThinningResult_guard state intensity
        (p.threshold_pos D.componentCount) coins
      have hcost := certified_poisson_count_sample_expected_cost hn D p b
        hprecision prep factor i
        (ttcReference.firstLoopResult state intensity threshold coins)
        (intensity * (ttcReference.firstLoopResult state intensity threshold coins).p)
        hcardReal hguard
      have hround :
          TTCRuntime.countThinningRoundOperations
              (ttcReference.firstLoopResult state intensity threshold coins).X.card ≤
            TTCRuntime.countThinningRoundOperations state.X.card := by
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
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) (state : TTCState n) (intensity : NNReal) :
    (costedBind
      (ttcReference.firstLoopWithCost state intensity (p.Thresh D.componentCount))
      (fun firstThinned =>
        costedBind
          (costedCharge
            (poissonMeasure (intensity * firstThinned.p))
            TTCRuntime.poissonDrawOperations)
          (fun pending =>
            costedBind
              (ttcPseudocode.secondLoopWithCost firstThinned pending
                (p.Thresh D.componentCount))
              (fun secondThinned =>
                costedBind
                  ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
                    (D.component i) secondThinned.2 b p.ε')
                  (fun batch => costedCharge
                    (Measure.dirac (secondThinned.1.addBatch batch))
                    (secondThinned.2 * TTCRuntime.appendCopyOperations))))))
        Set.univ ≤ 1 := by
  refine costedBind_mass_le_one _ _
    (ce_poisson_count_sample_measurable hn prep factor (D.component i) b
      p.ε' (p.δ' D.componentCount) (p.Thresh D.componentCount)
      intensity) ?_ ?_
  · exact rateThinWithCost_mass_le_one state intensity _
  · intro firstThinned
    refine costedBind_mass_le_one _ _ (measurable_of_countable _) ?_ ?_
    · apply costedCharge_mass_le_one
      simp
    · intro pending
      exact certified_count_sample_append_mass_le_one hn D p b hprecision
        prep factor pending i firstThinned

/-- The deletion pass and all later stages, conditional on one volume
estimate, have an explicit expected-operation bound. -/
theorem certified_deleted_component_expected_cost {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) (state : TTCState n) (volumeEstimate : NNReal)
    (hsamples : (state.X.card : Real) ≤ p.Thresh D.componentCount) :
    let deleted := state.removeComponent (D.component i)
    let intensity := ttcReference.t b n (p.Thresh D.componentCount) volumeEstimate
    let deletionCost := TTCRuntime.deletionPassOperations n
      (D.component i).presentation.facetCount state.X.card
      (state.X.card - deleted.X.card)
    ∫⁻ result, (result.2 : ENNReal) ∂
      costedBind (costedCharge (Measure.dirac deleted) deletionCost)
        (fun deleted =>
          costedBind
            (ttcReference.firstLoopWithCost deleted intensity
              (p.Thresh D.componentCount))
            (fun firstThinned =>
              costedBind
                (costedCharge
                  (poissonMeasure (intensity * firstThinned.p))
                  TTCRuntime.poissonDrawOperations)
                (fun pending =>
                  costedBind
                    (ttcPseudocode.secondLoopWithCost firstThinned pending
                      (p.Thresh D.componentCount))
                    (fun secondThinned =>
                      costedBind
                        ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
                          (D.component i) secondThinned.2 b p.ε')
                        (fun batch => costedCharge
                          (Measure.dirac (secondThinned.1.addBatch batch))
                          (secondThinned.2 * TTCRuntime.appendCopyOperations)))))) ≤
      deletionCost +
        ttcReference.firstLoopCost deleted intensity (p.Thresh D.componentCount) +
        TTCRuntime.poissonDrawOperations +
        4 * TTCRuntime.countThinningRoundOperations deleted.X.card +
        (TTCRuntime.ThresholdCap p D.componentCount : ENNReal) *
          (2 * TTCRuntime.samplingAttemptOperations n
            (D.component i).presentation.facetCount
            (normalizedHitAndRunSteps (D.component i) b p.ε') +
            TTCRuntime.appendCopyOperations) := by
  dsimp only
  let deleted := state.removeComponent (D.component i)
  let intensity := ttcReference.t b n (p.Thresh D.componentCount) volumeEstimate
  let deletionCost := TTCRuntime.deletionPassOperations n
    (D.component i).presentation.facetCount state.X.card
    (state.X.card - deleted.X.card)
  let next : TTCState n → Measure (TTCState n × Nat) := fun deleted =>
    costedBind
      (ttcReference.firstLoopWithCost deleted intensity (p.Thresh D.componentCount))
      (fun firstThinned =>
        costedBind
          (costedCharge
            (poissonMeasure (intensity * firstThinned.p))
            TTCRuntime.poissonDrawOperations)
          (fun pending =>
            costedBind
              (ttcPseudocode.secondLoopWithCost firstThinned pending
                (p.Thresh D.componentCount))
              (fun secondThinned =>
                costedBind
                  ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
                    (D.component i) secondThinned.2 b p.ε')
                  (fun batch => costedCharge
                    (Measure.dirac (secondThinned.1.addBatch batch))
                    (secondThinned.2 * TTCRuntime.appendCopyOperations)))))
  have hmass (x : TTCState n) : (next x) Set.univ ≤ 1 :=
    certified_rate_rest_mass_le_one hn D p b hprecision prep factor i x intensity
  have hdeleted : (deleted.X.card : Real) ≤ p.Thresh D.componentCount :=
    (Nat.cast_le.mpr (TTCState.removeComponent_card_le state (D.component i))).trans
      hsamples
  have hcost := certified_rate_poisson_count_sample_expected_cost hn D p b
    hprecision prep factor i deleted intensity hdeleted
  have hnextMeas : Measurable next :=
    ce_rate_tail_measurable hn prep factor (D.component i) b p.ε'
      (p.δ' D.componentCount) (p.Thresh D.componentCount)
      (p.threshold_pos D.componentCount) intensity
  have hstep := costedBind_charge_dirac_expected_cost_le deleted deletionCost next
    hnextMeas hmass
  calc
    _ ≤ (deletionCost : ENNReal) +
        (∫⁻ result, (result.2 : ENNReal) ∂next deleted) := hstep
    _ ≤ (deletionCost : ENNReal) +
        ((ttcReference.firstLoopCost deleted intensity
          (p.Thresh D.componentCount) : ENNReal) +
          TTCRuntime.poissonDrawOperations +
          4 * TTCRuntime.countThinningRoundOperations deleted.X.card +
          (TTCRuntime.ThresholdCap p D.componentCount : ENNReal) *
            (2 * TTCRuntime.samplingAttemptOperations n
              (D.component i).presentation.facetCount
              (normalizedHitAndRunSteps (D.component i) b p.ε') +
              TTCRuntime.appendCopyOperations)) := add_le_add_right hcost _
    _ = _ := by simp only [deletionCost, deleted, intensity, add_assoc]

theorem certified_deleted_component_expected_cost_le_budget {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) (state : TTCState n) (outcome : VolumeOutcome)
    (hsamples : (state.X.card : Real) ≤ p.Thresh D.componentCount) :
    let P := D.component i
    let deleted := state.removeComponent P
    let intensity := ttcReference.t b n (p.Thresh D.componentCount)
      outcome.2
    let deletionCost := TTCRuntime.deletionPassOperations n
      P.presentation.facetCount state.X.card
      (state.X.card - deleted.X.card)
    ∫⁻ result, (result.2 : ENNReal) ∂
      costedBind (costedCharge (Measure.dirac deleted) deletionCost)
        (fun deleted =>
          costedBind
            (ttcReference.firstLoopWithCost deleted intensity
              (p.Thresh D.componentCount))
            (fun firstThinned =>
              costedBind
                (costedCharge
                  (poissonMeasure (intensity * firstThinned.p))
                  TTCRuntime.poissonDrawOperations)
                (fun pending =>
                  costedBind
                    (ttcPseudocode.secondLoopWithCost firstThinned pending
                      (p.Thresh D.componentCount))
                    (fun secondThinned =>
                      costedBind
                        ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
                          P secondThinned.2 b p.ε')
                        (fun batch => costedCharge
                          (Measure.dirac (secondThinned.1.addBatch batch))
                          (secondThinned.2 * TTCRuntime.appendCopyOperations)))))) ≤
      componentNonVolumeBudget p D.componentCount b P state := by
  dsimp only
  let P := D.component i
  let deleted := state.removeComponent P
  let intensity := ttcReference.t b n (p.Thresh D.componentCount)
    outcome.2
  have hbase := certified_deleted_component_expected_cost hn D p b hprecision
    prep factor i state outcome.2 hsamples
  have hdeletion := deletionPassOperations_le state P
  have hrate := rateThinningCost_le_round deleted
    (ttcReference.t b n (p.Thresh D.componentCount) outcome.2)
    (p.Thresh D.componentCount)
  have hcount :
      TTCRuntime.countThinningRoundOperations deleted.X.card ≤
        TTCRuntime.countThinningRoundOperations state.X.card := by
    have hcard : deleted.X.card ≤ state.X.card := by
      simpa only [deleted] using TTCState.removeComponent_card_le state P
    unfold TTCRuntime.countThinningRoundOperations TTCRuntime.fairCoinOperations
      TTCRuntime.binomialDrawOperations TTCRuntime.scalarOperationCost
    omega
  calc
    _ ≤ (TTCRuntime.deletionPassOperations n P.presentation.facetCount
          state.X.card (state.X.card - deleted.X.card) : ENNReal) +
        ttcReference.firstLoopCost deleted intensity (p.Thresh D.componentCount) +
        TTCRuntime.poissonDrawOperations +
        4 * TTCRuntime.countThinningRoundOperations deleted.X.card +
        (TTCRuntime.ThresholdCap p D.componentCount : ENNReal) *
          (2 * TTCRuntime.samplingAttemptOperations n P.presentation.facetCount
            (normalizedHitAndRunSteps P b p.ε') +
            TTCRuntime.appendCopyOperations) := hbase
    _ ≤ componentNonVolumeBudget p D.componentCount b P state := by
      dsimp only [componentNonVolumeBudget]
      gcongr
      exact_mod_cast hdeletion

private theorem componentNonVolumeBudget_le_uniform {n : Nat}
    (p : ApproxParams) (m b : Nat) (P : PolytopeData n)
    (state : TTCState n)
    (hcard : (state.X.card : Real) ≤ p.Thresh m)
    (hrate : state.p ≤ 1) :
    componentNonVolumeBudget p m b P state ≤
      componentUniformBudget p m b P := by
  let cap := TTCRuntime.ThresholdCap p m
  let deleted := state.removeComponent P
  let upperIntensity := ttcReference.t b n (p.Thresh m)
    (max (P.volumeClipLower p.ε')
      (P.volumeClipUpper p.ε'))
  have hcap : state.X.card ≤ cap := by
    exact_mod_cast hcard.trans (Nat.le_ceil (p.Thresh m))
  have hdeleted : deleted.X.card ≤ cap :=
    (TTCState.removeComponent_card_le state P).trans hcap
  have hlowerPos : 0 < (P.volumeClipLower p.ε' : Real) := by
    have heps : p.ε' < 1 := by
      unfold ApproxParams.ε'
      linarith [p.epsilon_le_one]
    have hbase : 0 < (2 * P.inradius / Real.sqrt n) ^ n := by
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0
        simp
      · have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hnpos)
        exact pow_pos (div_pos (by linarith [P.inradius_pos]) hsqrt) n
    unfold PolytopeData.volumeClipLower
    rw [Real.coe_toNNReal _ (by nlinarith)]
    nlinarith
  have hupperPos : 0 < (upperIntensity : Real) := by
    have hT := p.threshold_pos m
    have hmax : (0 : NNReal) < max (P.volumeClipLower p.ε') (P.volumeClipUpper p.ε') :=
      lt_max_of_lt_left (by exact_mod_cast hlowerPos)
    have hpos : (0 : NNReal) < upperIntensity := by
      dsimp only [upperIntensity, ttcReference.t]
      exact mul_pos (mul_pos (Real.toNNReal_pos.mpr hT) (by positivity)) hmax
    exact_mod_cast hpos
  have hlogPos : 1 ≤ Nat.clog 2 (Nat.ceil ((upperIntensity : Real) / p.Thresh m) + 1) := by
    have hceil : 0 < Nat.ceil ((upperIntensity : Real) / p.Thresh m) :=
      Nat.ceil_pos.mpr (div_pos hupperPos (p.threshold_pos m))
    exact Nat.clog_pos (by norm_num) (by omega)
  have hrateCost : TTCRuntime.rateThinningRoundOperations deleted.X.card ≤
      Nat.clog 2 (Nat.ceil ((upperIntensity : Real) / p.Thresh m) + 1) *
        TTCRuntime.rateThinningRoundOperations cap := by
    have hround : TTCRuntime.rateThinningRoundOperations deleted.X.card ≤
        TTCRuntime.rateThinningRoundOperations cap := by
      unfold TTCRuntime.rateThinningRoundOperations TTCRuntime.fairCoinOperations
        TTCRuntime.scalarOperationCost
      omega
    calc
      _ ≤ TTCRuntime.rateThinningRoundOperations cap := hround
      _ = 1 * TTCRuntime.rateThinningRoundOperations cap := (one_mul _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ hlogPos
  have hdelete : state.X.card *
      (TTCRuntime.facetScanOperations n P.presentation.facetCount + 1) ≤
      cap * (TTCRuntime.facetScanOperations n P.presentation.facetCount + 1) :=
    Nat.mul_le_mul_right _ hcap
  have hcount : TTCRuntime.countThinningRoundOperations state.X.card ≤
      TTCRuntime.countThinningRoundOperations cap := by
    unfold TTCRuntime.countThinningRoundOperations TTCRuntime.fairCoinOperations
      TTCRuntime.binomialDrawOperations TTCRuntime.scalarOperationCost
    omega
  unfold componentNonVolumeBudget componentUniformBudget
  dsimp only
  gcongr
  · exact_mod_cast hrateCost

theorem certified_component_expected_cost {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) (state : TTCState n)
    (hsamples : (state.X.card : Real) ≤ p.Thresh D.componentCount) :
    ∫⁻ result, (result.2 : ENNReal) ∂
      ttcReference.stepWithCost
        (ttcCostedSubroutines hn prep factor) b p.ε'
        (p.δ' D.componentCount) (p.Thresh D.componentCount)
        (D.component i) state ≤
      (TTCRuntime.membershipQueryOperations n
          (D.component i).presentation.facetCount
          (CommunityCV18.queryBudgetFor (by omega) (D.component i)
            p.ε' (p.δ' D.componentCount)) +
        factor * TTCRuntime.membershipQueryOperations n
          (D.component i).presentation.facetCount
          (CommunityCV18.queryBudgetFor (by omega) (D.component i)
            p.ε' (p.δ' D.componentCount) + 1) : ENNReal) +
        componentNonVolumeBudget p D.componentCount b (D.component i) state := by
  let P := D.component i
  let O := ttcCostedSubroutines hn prep factor
  let step : VolumeOutcome → Measure (TTCState n × Nat) := fun volumeOutcome =>
    let intensity := ttcReference.t b n (p.Thresh D.componentCount)
      volumeOutcome.2
    let deleted := state.removeComponent P
    let deletionCost := TTCRuntime.deletionPassOperations n
      P.presentation.facetCount state.X.card
      (state.X.card - deleted.X.card)
    costedBind (costedCharge (Measure.dirac deleted) deletionCost)
      (fun deleted =>
        costedBind
          (ttcReference.firstLoopWithCost deleted intensity
            (p.Thresh D.componentCount))
          (fun firstThinned =>
            costedBind
              (costedCharge
                (poissonMeasure (intensity * firstThinned.p))
                TTCRuntime.poissonDrawOperations)
              (fun pending =>
                costedBind
                  (ttcPseudocode.secondLoopWithCost firstThinned pending
                    (p.Thresh D.componentCount))
                  (fun secondThinned =>
                    costedBind
                      (O.generateSamplesWithCost P secondThinned.2 b p.ε')
                      (fun batch => costedCharge
                        (Measure.dirac (secondThinned.1.addBatch batch))
                        (secondThinned.2 * TTCRuntime.appendCopyOperations))))))
  have hstepMass (volumeOutcome : VolumeOutcome) :
      (step volumeOutcome) Set.univ ≤ 1 := by
    dsimp only [step]
    refine costedBind_mass_le_one _ _
      (ce_rate_tail_measurable hn prep factor P b p.ε'
        (p.δ' D.componentCount) (p.Thresh D.componentCount)
        (p.threshold_pos D.componentCount)
        (ttcReference.t b n (p.Thresh D.componentCount) volumeOutcome.2))
      ?_ ?_
    · apply costedCharge_mass_le_one
      simp
    · intro deleted
      exact certified_rate_rest_mass_le_one hn D p b hprecision prep factor
        i deleted (ttcReference.t b n (p.Thresh D.componentCount)
          volumeOutcome.2)
  have hstepCost (outcome : VolumeOutcome) :
      (∫⁻ result, (result.2 : ENNReal) ∂
        step outcome) ≤
        componentNonVolumeBudget p D.componentCount b P state := by
    exact certified_deleted_component_expected_cost_le_budget hn D p b hprecision
      prep factor i state outcome hsamples
  change (∫⁻ result, (result.2 : ENNReal) ∂
    costedBind (O.computeVolumeWithCost P p.ε'
      (p.δ' D.componentCount)) step) ≤ _
  have hstepMeas : Measurable step :=
    ce_component_step_measurable hn prep factor P b p.ε'
      (p.δ' D.componentCount) (p.Thresh D.componentCount)
      (p.threshold_pos D.componentCount) state
  apply (costedBind_lintegral_cost_le _ step hstepMeas hstepMass).trans
  exact certified_community_volume_continuation_bound hn D p prep factor i
    (fun outcome => ∫⁻ result, (result.2 : ENNReal) ∂step outcome)
    hstepCost

theorem certified_component_expected_cost_uniform {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) (state : TTCState n)
    (hcard : (state.X.card : Real) ≤ p.Thresh D.componentCount)
    (hrate : state.p ≤ 1) :
    ∫⁻ result, (result.2 : ENNReal) ∂
      ttcReference.stepWithCost
        (ttcCostedSubroutines hn prep factor) b p.ε'
        (p.δ' D.componentCount) (p.Thresh D.componentCount)
        (D.component i) state ≤
      (TTCRuntime.membershipQueryOperations n
          (D.component i).presentation.facetCount
          (CommunityCV18.queryBudgetFor (by omega) (D.component i)
            p.ε' (p.δ' D.componentCount)) +
        factor * TTCRuntime.membershipQueryOperations n
          (D.component i).presentation.facetCount
          (CommunityCV18.queryBudgetFor (by omega) (D.component i)
            p.ε' (p.δ' D.componentCount) + 1) : ENNReal) +
        componentUniformBudget p D.componentCount b (D.component i) := by
  apply (certified_component_expected_cost hn D p b hprecision prep
    factor i state hcard).trans
  exact add_le_add_right
    (componentNonVolumeBudget_le_uniform p D.componentCount b (D.component i)
      state hcard hrate) _

theorem certified_component_mass_le_one {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) (state : TTCState n) :
    (ttcReference.stepWithCost
      (ttcCostedSubroutines hn prep factor) b p.ε'
      (p.δ' D.componentCount) (p.Thresh D.componentCount)
      (D.component i) state) Set.univ ≤ 1 := by
  have hcv : (communityCV18VolumeLaw (by omega) (D.component i)
      p.ε' (p.δ' D.componentCount)) Set.univ ≤ 1 :=
    certified_community_volume_mass_le_one hn D p i
  have hvol :
      ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
        (D.component i) p.ε'
        (p.δ' D.componentCount)) Set.univ ≤ 1 := by
    apply costedCharge_mass_le_one
    dsimp only [ttcSubroutines]
    exact hcv
  unfold ttcReference.stepWithCost
  refine costedBind_mass_le_one _ _
    (ce_component_step_measurable hn prep factor (D.component i) b p.ε'
      (p.δ' D.componentCount) (p.Thresh D.componentCount)
      (p.threshold_pos D.componentCount) state) hvol ?_
  intro volumeOutcome
  refine costedBind_mass_le_one _ _
    (ce_rate_tail_measurable hn prep factor (D.component i) b p.ε'
      (p.δ' D.componentCount) (p.Thresh D.componentCount)
      (p.threshold_pos D.componentCount)
      (ttcReference.t b n (p.Thresh D.componentCount) volumeOutcome.2))
    ?_ ?_
  · apply costedCharge_mass_le_one
    simp
  · intro deleted
    exact certified_rate_rest_mass_le_one hn D p b hprecision prep factor
      i deleted (ttcReference.t b n (p.Thresh D.componentCount)
        volumeOutcome.2)

/-- The concrete charged paper component has a deterministic expected
budget once its incoming stored population is below the TTC threshold. -/
private theorem measurableSet_state_card_le {n : Nat} (threshold : Real) :
    MeasurableSet {state : TTCState n | (state.X.card : Real) ≤ threshold} := by
  have hcoords : Measurable (fun state : TTCState n =>
      (state.p, state.X, state.nextLabel)) := comap_measurable _
  have hsamples : Measurable (fun state : TTCState n => state.X) :=
    (measurable_fst.comp measurable_snd).comp hcoords
  have hcard : Measurable (fun state : TTCState n => state.X.card) :=
    (measurable_of_countable (fun copies : Finset (SampleCopy n) => copies.card)).comp
      hsamples
  exact ((measurable_of_countable (fun q : Nat => (q : Real))).comp hcard)
    measurableSet_Iic

private theorem measurableSet_state_rate_le_one {n : Nat} :
    MeasurableSet {state : TTCState n | state.p ≤ 1} := by
  have hcoords : Measurable (fun state : TTCState n =>
      (state.p, state.X, state.nextLabel)) := comap_measurable _
  have hrate : Measurable (fun state : TTCState n => state.p) :=
    measurable_fst.comp hcoords
  exact hrate measurableSet_Iic

private theorem rateThinningResult_rate_le_one {n : Nat}
    (state : TTCState n) (intensity : NNReal) (threshold : Real)
    (coins : Nat × Nat → Bool) (hrate : state.p ≤ 1) :
    (ttcReference.firstLoopResult state intensity threshold coins).p ≤ 1 := by
  dsimp only [ttcReference.firstLoopResult]
  have hdenom : (1 : NNReal) ≤ (2 : NNReal) ^ ttcReference.firstLoopExit state intensity
      threshold := one_le_pow₀ (by norm_num)
  exact (div_le_self (by positivity) hdenom).trans hrate

private theorem rateThinWithCost_rate_le_one_ae {n : Nat}
    (state : TTCState n) (intensity : NNReal) (threshold : Real)
    (hrate : state.p ≤ 1) :
    ∀ᵐ result ∂ttcReference.firstLoopWithCost state intensity threshold,
      result.1.p ≤ 1 := by
  have hset : MeasurableSet {s : TTCState n | s.p ≤ 1} :=
    measurableSet_state_rate_le_one
  have hbase : ∀ᵐ result ∂ttcReference.firstLoop state intensity threshold,
      result.p ≤ 1 := by
    unfold ttcReference.firstLoop
    rw [ae_map_iff
      (measurable_rateThinningResult state intensity threshold).aemeasurable
      hset]
    exact Filter.Eventually.of_forall fun coins =>
      rateThinningResult_rate_le_one state intensity threshold coins hrate
  rw [← rateThinWithCost_fst state intensity threshold] at hbase
  exact (ae_map_iff measurable_fst.aemeasurable hset).mp hbase

private theorem countThinWithCost_rate_le_one_ae {n : Nat}
    (state : TTCState n) (pending : Nat) (threshold : Real)
    (hrate : state.p ≤ 1) :
    ∀ᵐ result ∂ttcPseudocode.secondLoopWithCost state pending threshold,
      result.1.1.p ≤ 1 := by
  have hset : MeasurableSet {result : TTCState n × Nat | result.1.p ≤ 1} :=
    (measurableSet_state_rate_le_one).preimage measurable_fst
  have hbase : ∀ᵐ result ∂ttcPseudocode.secondLoop state pending threshold,
      result.1.p ≤ 1 := by
    unfold ttcPseudocode.secondLoop
    rw [ae_map_iff (measurable_thinningResult state pending threshold).aemeasurable
      hset]
    apply Filter.Eventually.of_forall
    intro coins
    dsimp only [ttcPseudocode.secondLoopResult]
    have hdenom : (1 : NNReal) ≤
        (2 : NNReal) ^ ttcPseudocode.secondLoopExitRound state pending threshold coins :=
      one_le_pow₀ (by norm_num)
    exact (div_le_self (by positivity) hdenom).trans hrate
  rw [← countThinWithCost_fst state pending threshold] at hbase
  exact (ae_map_iff measurable_fst.aemeasurable hset).mp hbase

private theorem sample_append_card_le_ae {n : Nat} {count : Nat}
    (state : TTCState n) (threshold : Real)
    (hguard : ((state.X.card + count : Nat) : Real) ≤ threshold)
    (sampleLaw : Measure (SampleBatch n count × Nat)) :
    ∀ᵐ result ∂costedBind sampleLaw
      (fun batch => costedCharge (Measure.dirac (state.addBatch batch))
        (count * TTCRuntime.appendCopyOperations)),
      (result.1.X.card : Real) ≤ threshold := by
  apply costedBind_ae_state_of_ae sampleLaw _ (ce_append_charge_measurable state _)
    (fun _ => True)
    (fun s : TTCState n => (s.X.card : Real) ≤ threshold)
    (measurableSet_state_card_le threshold)
  · exact Filter.Eventually.of_forall (fun _ => trivial)
  · intro batch _
    apply costedCharge_dirac_ae_state _ _ _
      (measurableSet_state_card_le threshold)
    have hcard := TTCState.addBatch_card_le state batch
    exact (Nat.cast_le.mpr hcard).trans hguard

private theorem count_sample_append_card_le_ae {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat) (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) (state : TTCState n) (pending : Nat) :
    ∀ᵐ result ∂
      costedBind
        (ttcPseudocode.secondLoopWithCost state pending (p.Thresh D.componentCount))
        (fun secondThinned =>
          costedBind
            ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
              (D.component i) secondThinned.2 b p.ε')
            (fun batch => costedCharge
              (Measure.dirac (secondThinned.1.addBatch batch))
              (secondThinned.2 * TTCRuntime.appendCopyOperations))),
        (result.1.X.card : Real) ≤ p.Thresh D.componentCount := by
  apply costedBind_ae_state_of_ae _ _
    (ce_sample_append_kernel_measurable hn prep factor (D.component i) b
      p.ε' (p.δ' D.componentCount))
    (fun secondThinned : TTCState n × Nat =>
      ((secondThinned.1.X.card + secondThinned.2 : Nat) : Real) ≤
        p.Thresh D.componentCount)
    (fun s : TTCState n => (s.X.card : Real) ≤ p.Thresh D.componentCount)
    (measurableSet_state_card_le _)
  · exact countThinWithCost_population_le_ae state pending _
      (p.threshold_pos D.componentCount).le
  · intro secondThinned hguard
    exact sample_append_card_le_ae secondThinned.1
      (p.Thresh D.componentCount) hguard _

theorem certified_component_card_le_ae {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat) (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) (state : TTCState n) :
    ∀ᵐ result ∂
      ttcReference.stepWithCost
        (ttcCostedSubroutines hn prep factor) b p.ε'
        (p.δ' D.componentCount) (p.Thresh D.componentCount)
        (D.component i) state,
      (result.1.X.card : Real) ≤ p.Thresh D.componentCount := by
  unfold ttcReference.stepWithCost
  apply costedBind_ae_state_of_forall _ _
    (ce_component_step_measurable hn prep factor (D.component i) b p.ε'
      (p.δ' D.componentCount) (p.Thresh D.componentCount)
      (p.threshold_pos D.componentCount) state)
    (fun s : TTCState n => (s.X.card : Real) ≤ p.Thresh D.componentCount)
    (measurableSet_state_card_le _)
  intro volumeOutcome
  apply costedBind_ae_state_of_forall _ _
    (ce_rate_tail_measurable hn prep factor (D.component i) b p.ε'
      (p.δ' D.componentCount) (p.Thresh D.componentCount)
      (p.threshold_pos D.componentCount)
      (ttcReference.t b n (p.Thresh D.componentCount) volumeOutcome.2))
    (fun s : TTCState n => (s.X.card : Real) ≤ p.Thresh D.componentCount)
    (measurableSet_state_card_le _)
  intro deleted
  apply costedBind_ae_state_of_forall _ _
    (ce_poisson_count_sample_measurable hn prep factor (D.component i) b
      p.ε' (p.δ' D.componentCount) (p.Thresh D.componentCount)
      (ttcReference.t b n (p.Thresh D.componentCount) volumeOutcome.2))
    (fun s : TTCState n => (s.X.card : Real) ≤ p.Thresh D.componentCount)
    (measurableSet_state_card_le _)
  intro firstThinned
  apply costedBind_ae_state_of_forall _ _ (measurable_of_countable _)
    (fun s : TTCState n => (s.X.card : Real) ≤ p.Thresh D.componentCount)
    (measurableSet_state_card_le _)
  intro pending
  exact count_sample_append_card_le_ae hn D p b prep factor i firstThinned pending

private theorem sample_append_rate_le_one_ae {n : Nat} {count : Nat}
    (state : TTCState n) (sampleLaw : Measure (SampleBatch n count × Nat))
    (hrate : state.p ≤ 1) :
    ∀ᵐ result ∂costedBind sampleLaw
      (fun batch => costedCharge (Measure.dirac (state.addBatch batch))
        (count * TTCRuntime.appendCopyOperations)),
      result.1.p ≤ 1 := by
  apply costedBind_ae_state_of_forall _ _ (ce_append_charge_measurable state _)
    (fun s : TTCState n => s.p ≤ 1) measurableSet_state_rate_le_one
  intro batch
  apply costedCharge_dirac_ae_state _ _ _ measurableSet_state_rate_le_one
  simpa only [TTCState.addBatch] using hrate

private theorem count_sample_append_rate_le_one_ae {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat) (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) (state : TTCState n) (pending : Nat)
    (hrate : state.p ≤ 1) :
    ∀ᵐ result ∂
      costedBind
        (ttcPseudocode.secondLoopWithCost state pending (p.Thresh D.componentCount))
        (fun secondThinned =>
          costedBind
            ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
              (D.component i) secondThinned.2 b p.ε')
            (fun batch => costedCharge
              (Measure.dirac (secondThinned.1.addBatch batch))
              (secondThinned.2 * TTCRuntime.appendCopyOperations))),
        result.1.p ≤ 1 := by
  apply costedBind_ae_state_of_ae _ _
    (ce_sample_append_kernel_measurable hn prep factor (D.component i) b
      p.ε' (p.δ' D.componentCount))
    (fun secondThinned : TTCState n × Nat => secondThinned.1.p ≤ 1)
    (fun s : TTCState n => s.p ≤ 1) measurableSet_state_rate_le_one
  · exact countThinWithCost_rate_le_one_ae state pending _ hrate
  · intro secondThinned hsecond
    exact sample_append_rate_le_one_ae secondThinned.1 _ hsecond

private theorem poisson_count_sample_rate_le_one_ae {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat) (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) (state : TTCState n) (intensity : NNReal)
    (hrate : state.p ≤ 1) :
    ∀ᵐ result ∂costedBind
      (costedCharge (poissonMeasure (intensity * state.p))
        TTCRuntime.poissonDrawOperations)
      (fun pending =>
        costedBind
          (ttcPseudocode.secondLoopWithCost state pending (p.Thresh D.componentCount))
          (fun secondThinned =>
            costedBind
              ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
                (D.component i) secondThinned.2 b p.ε')
              (fun batch => costedCharge
                (Measure.dirac (secondThinned.1.addBatch batch))
                (secondThinned.2 * TTCRuntime.appendCopyOperations)))),
      result.1.p ≤ 1 := by
  apply costedBind_ae_state_of_forall _ _ (measurable_of_countable _)
    (fun s : TTCState n => s.p ≤ 1) measurableSet_state_rate_le_one
  intro pending
  exact count_sample_append_rate_le_one_ae hn D p b prep factor i state pending hrate

private theorem rate_poisson_count_sample_rate_le_one_ae {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat) (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) (state : TTCState n) (intensity : NNReal)
    (hrate : state.p ≤ 1) :
    ∀ᵐ result ∂costedBind
      (ttcReference.firstLoopWithCost state intensity (p.Thresh D.componentCount))
      (fun firstThinned =>
        costedBind
          (costedCharge (poissonMeasure (intensity * firstThinned.p))
            TTCRuntime.poissonDrawOperations)
          (fun pending =>
            costedBind
              (ttcPseudocode.secondLoopWithCost firstThinned pending
                (p.Thresh D.componentCount))
              (fun secondThinned =>
                costedBind
                  ((ttcCostedSubroutines hn prep factor).generateSamplesWithCost
                    (D.component i) secondThinned.2 b p.ε')
                  (fun batch => costedCharge
                    (Measure.dirac (secondThinned.1.addBatch batch))
                    (secondThinned.2 * TTCRuntime.appendCopyOperations))))),
      result.1.p ≤ 1 := by
  apply costedBind_ae_state_of_ae _ _
    (ce_poisson_count_sample_measurable hn prep factor (D.component i) b
      p.ε' (p.δ' D.componentCount) (p.Thresh D.componentCount)
      intensity)
    (fun s : TTCState n => s.p ≤ 1)
    (fun s : TTCState n => s.p ≤ 1) measurableSet_state_rate_le_one
  · exact rateThinWithCost_rate_le_one_ae state intensity _ hrate
  · intro firstThinned hfirst
    exact poisson_count_sample_rate_le_one_ae hn D p b prep factor i firstThinned
      intensity hfirst

theorem certified_component_rate_le_one_ae {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat) (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) (state : TTCState n)
    (hrate : state.p ≤ 1) :
    ∀ᵐ result ∂
      ttcReference.stepWithCost
        (ttcCostedSubroutines hn prep factor) b p.ε'
        (p.δ' D.componentCount) (p.Thresh D.componentCount)
        (D.component i) state,
      result.1.p ≤ 1 := by
  unfold ttcReference.stepWithCost
  apply costedBind_ae_state_of_forall _ _
    (ce_component_step_measurable hn prep factor (D.component i) b p.ε'
      (p.δ' D.componentCount) (p.Thresh D.componentCount)
      (p.threshold_pos D.componentCount) state)
    (fun s : TTCState n => s.p ≤ 1) measurableSet_state_rate_le_one
  intro volumeOutcome
  apply costedBind_ae_state_of_ae _ _
    (ce_rate_tail_measurable hn prep factor (D.component i) b p.ε'
      (p.δ' D.componentCount) (p.Thresh D.componentCount)
      (p.threshold_pos D.componentCount)
      (ttcReference.t b n (p.Thresh D.componentCount) volumeOutcome.2))
    (fun s : TTCState n => s.p ≤ 1)
    (fun s : TTCState n => s.p ≤ 1) measurableSet_state_rate_le_one
  · apply costedCharge_dirac_ae_state _ _ _ measurableSet_state_rate_le_one
    simpa only [TTCState.removeComponent] using hrate
  · intro deleted hdeleted
    exact rate_poisson_count_sample_rate_le_one_ae hn D p b prep factor i
      deleted _ hdeleted

private theorem ce_certified_volume_mass_le_one {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (prep : TTCPreprocessor n k) (factor : Nat)
    (i : Fin D.componentCount) :
    ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
      (D.component i) p.ε'
      (p.δ' D.componentCount)) Set.univ ≤ 1 := by
  apply costedCharge_mass_le_one
  dsimp only [ttcSubroutines]
  exact certified_community_volume_mass_le_one hn D p i

private theorem ce_certified_components_kernel_measurable {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat) (prep : TTCPreprocessor n k) (factor : Nat)
    (components : List (PolytopeData n))
    (hcomponents : ∀ P ∈ components, ∃ i : Fin D.componentCount,
      D.component i = P) :
    Measurable (fun state : TTCState n =>
      ttcReference.loopWithCost
        (ttcCostedSubroutines hn prep factor) b p.ε'
        (p.δ' D.componentCount) (p.Thresh D.componentCount)
        components state) :=
  ce_components_kernel_measurable hn prep factor b p.ε'
    (p.δ' D.componentCount) (p.Thresh D.componentCount)
    (p.threshold_pos D.componentCount) components (fun P hP => by
      obtain ⟨i, rfl⟩ := hcomponents P hP
      exact ce_certified_volume_mass_le_one hn D p prep factor i)

private theorem certified_component_list_mass_le_one {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (prep : TTCPreprocessor n k) (factor : Nat)
    (components : List (PolytopeData n))
    (hcomponents : ∀ P ∈ components, ∃ i : Fin D.componentCount,
      D.component i = P) (state : TTCState n) :
    (ttcReference.loopWithCost
      (ttcCostedSubroutines hn prep factor) b p.ε'
      (p.δ' D.componentCount) (p.Thresh D.componentCount)
      components state) Set.univ ≤ 1 := by
  induction components generalizing state with
  | nil =>
      simp only [ttcReference.loopWithCost]
      simp
  | cons P rest ih =>
      obtain ⟨i, rfl⟩ := hcomponents P (by simp)
      have hrest : ∀ Q ∈ rest, ∃ j : Fin D.componentCount,
          D.component j = Q := by
        intro Q hQ
        exact hcomponents Q (by simp [hQ])
      change (costedBind
        (ttcReference.stepWithCost
          (ttcCostedSubroutines hn prep factor) b p.ε'
          (p.δ' D.componentCount) (p.Thresh D.componentCount)
          (D.component i) state)
        (ttcReference.loopWithCost
          (ttcCostedSubroutines hn prep factor) b p.ε'
          (p.δ' D.componentCount) (p.Thresh D.componentCount)
          rest)) Set.univ ≤ 1
      refine costedBind_mass_le_one _ _
        (ce_certified_components_kernel_measurable hn D p b prep factor rest hrest)
        ?_ ?_
      · exact certified_component_mass_le_one hn D p b hprecision
          prep factor i state
      · intro nextState
        exact ih hrest nextState

theorem certified_component_list_expected_cost {n k : Nat}
    (hn : 21 ≤ n) {F : LRAFormula n k} (D : Decomposition F)
    (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (prep : TTCPreprocessor n k) (factor : Nat)
    (components : List (PolytopeData n))
    (hcomponents : ∀ P ∈ components, ∃ i : Fin D.componentCount,
      D.component i = P) (state : TTCState n)
    (hcard : (state.X.card : Real) ≤ p.Thresh D.componentCount)
    (hrate : state.p ≤ 1) :
    ∫⁻ result, (result.2 : ENNReal) ∂
      ttcReference.loopWithCost
        (ttcCostedSubroutines hn prep factor) b p.ε'
        (p.δ' D.componentCount) (p.Thresh D.componentCount)
        components state ≤
      (components.map (uniformComponentCost hn p D.componentCount b factor)).sum := by
  induction components generalizing state with
  | nil =>
      simp only [ttcReference.loopWithCost, List.map_nil, List.sum_nil]
      simp
  | cons P rest ih =>
      obtain ⟨i, rfl⟩ := hcomponents P (by simp)
      have hrest : ∀ Q ∈ rest, ∃ j : Fin D.componentCount,
          D.component j = Q := by
        intro Q hQ
        exact hcomponents Q (by simp [hQ])
      let first := ttcReference.stepWithCost
        (ttcCostedSubroutines hn prep factor) b p.ε'
        (p.δ' D.componentCount) (p.Thresh D.componentCount)
        (D.component i) state
      let next := ttcReference.loopWithCost
        (ttcCostedSubroutines hn prep factor) b p.ε'
        (p.δ' D.componentCount) (p.Thresh D.componentCount) rest
      have hfirstMass : first Set.univ ≤ 1 :=
        certified_component_mass_le_one hn D p b hprecision
          prep factor i state
      have hnextMass (s : TTCState n) : (next s) Set.univ ≤ 1 :=
        certified_component_list_mass_le_one hn D p b hprecision prep factor
          rest hrest s
      have hfirstCost :
          (∫⁻ result, (result.2 : ENNReal) ∂first) ≤
            uniformComponentCost hn p D.componentCount b factor (D.component i) := by
        simpa only [uniformComponentCost] using
          certified_component_expected_cost_uniform hn D p b
            hprecision prep factor i state hcard hrate
      have hnextCost : ∀ᵐ result ∂first,
          (∫⁻ future, (future.2 : ENNReal) ∂next result.1) ≤
            (rest.map (uniformComponentCost hn p D.componentCount b factor)).sum := by
        have hcard' := certified_component_card_le_ae hn D p b prep factor
          i state
        have hrate' := certified_component_rate_le_one_ae hn D p b prep factor
          i state hrate
        filter_upwards [hcard', hrate'] with result hc hr
        exact ih hrest result.1 hc hr
      change (∫⁻ result, (result.2 : ENNReal) ∂costedBind first next) ≤ _
      simpa only [List.map_cons, List.sum_cons] using
        costedBind_expected_cost_le_add_ae first next
          (ce_certified_components_kernel_measurable hn D p b prep factor rest hrest)
          hfirstMass hnextMass
          hfirstCost hnextCost

/-- Exact finite expected-operation bound for the charged paper TTC run,
including the caller-supplied preprocessing charge. -/
private theorem communityCosted_preprocessing_eq {n k : Nat} (hn : 21 ≤ n)
    (prep : TTCPreprocessor n k) (factor : Nat) :
    (ttcCostedSubroutines hn prep factor).base.preprocessing = prep := by
  rfl

theorem community_expected_cost_finite_sum {n k : Nat}
    (hn : 21 ≤ n) (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations factor : Nat) :
    let D := prep.run F hbounded
    let b := (prep.choosePrecision D p).value
    ∫⁻ result, (result.2 : ENNReal) ∂
      ttcRefWithCost hn F hbounded p prep
        preprocessingOperations factor ≤
      preprocessingOperations +
        ((List.ofFn D.component).map
          (uniformComponentCost hn p D.componentCount b factor)).sum := by
  dsimp only
  unfold ttcRefWithCost ttcReferenceWithCost
  rw [communityCosted_preprocessing_eq]
  let D := prep.run F hbounded
  let b := (prep.choosePrecision D p).value
  have hprecision : PrecisionAdequate D b p.precisionEta :=
    (prep.choosePrecision D p).adequate
  by_cases hempty : D.componentCount = 0
  · simp [ttcRefWithCost, ttcReferenceWithCost,
      D, hempty]
  · have hcomponents : ∀ P ∈ List.ofFn D.component,
        ∃ i : Fin D.componentCount, D.component i = P := by
      intro P hP
      exact (List.mem_ofFn' D.component P).mp hP
    have hinitialCard :
        (((TTCState.unitInitial n).X.card : Nat) : Real) ≤
          p.Thresh D.componentCount := by
      simp only [TTCState.unitInitial, Finset.card_empty, Nat.cast_zero]
      exact (p.threshold_pos D.componentCount).le
    have hinitialRate : (TTCState.unitInitial n).p ≤ 1 := by
      simp only [TTCState.unitInitial, le_refl]
    have hcoreCost := certified_component_list_expected_cost hn D p b
      hprecision prep factor (List.ofFn D.component) hcomponents
      (TTCState.unitInitial n) hinitialCard hinitialRate
    have hcoreMass := certified_component_list_mass_le_one hn D p b
      hprecision prep factor (List.ofFn D.component) hcomponents
      (TTCState.unitInitial n)
    let core := ttcReference.loopWithCost
      (ttcCostedSubroutines hn prep factor) b p.ε'
      (p.δ' D.componentCount) (p.Thresh D.componentCount)
      (List.ofFn D.component) (TTCState.unitInitial n)
    have hempty' : (prep.run F hbounded).componentCount ≠ 0 := by
      simpa only [D] using hempty
    rw [if_neg hempty']
    change (∫⁻ result, (result.2 : ENNReal) ∂
      core.map (fun result =>
        (EstReference b (p.Thresh D.componentCount) result.1,
          preprocessingOperations + result.2))) ≤ _
    apply (lintegral_map_le _
      (((ce_estimate_measurable b (p.Thresh D.componentCount)).comp
        measurable_fst).prodMk
        (measurable_snd.const_add preprocessingOperations)).aemeasurable).trans
    simp only [Nat.cast_add]
    rw [lintegral_add_left (by fun_prop)]
    simp only [lintegral_const]
    exact add_le_add
      (mul_le_of_le_one_right (by positivity) hcoreMass) hcoreCost

theorem community_expected_cost_explicit {n k : Nat}
    (hn : 21 ≤ n) (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations factor : Nat) :
    let D := prep.run F hbounded
    let b := (prep.choosePrecision D p).value
    ∫⁻ result, (result.2 : ENNReal) ∂
      ttcRefWithCost hn F hbounded p prep
        preprocessingOperations factor ≤
      preprocessingOperations +
        ∑ i : Fin D.componentCount,
          TTCRuntime.expectedComponentBudget hn p D.componentCount b
            factor (D.component i) := by
  simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply,
    uniformComponentCost_eq_model] using
    community_expected_cost_finite_sum hn F hbounded p prep
      preprocessingOperations factor

end Kr25Ssmxt
