import Kr25Ssmxt.Analysis.ThinningCosts
import Kr25Ssmxt.Analysis.MeasurableThinningResultJoint

/-! Joint measurability of the paper's first thinning counter. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem measurable_rateExit_joint {n : Nat}
    (threshold : Real) (hthreshold : 0 < threshold) :
    Measurable (fun z : TTCState n × NNReal =>
      ttcReference.firstLoopExit z.1 z.2 threshold) := by
  let guard (j : Nat) : TTCState n × NNReal → Prop := fun z =>
    ((z.2 * z.1.p / (2 : NNReal) ^ j : NNReal) : Real) ≤ threshold
  have hguard (j : Nat) : MeasurableSet {z | guard j z} := by
    have hcoords : Measurable (fun z : TTCState n × NNReal =>
        (z.1.p, z.1.X, z.1.nextLabel)) :=
      (comap_measurable _).comp measurable_fst
    have hrate : Measurable (fun z : TTCState n × NNReal => z.1.p) :=
      measurable_fst.comp hcoords
    have hval : Measurable (fun z : TTCState n × NNReal =>
        ((z.2 * z.1.p / (2 : NNReal) ^ j : NNReal) : Real)) := by
      fun_prop
    exact hval measurableSet_Iic
  have hfiber (k : Nat) :
      (fun z : TTCState n × NNReal => ttcReference.firstLoopExit z.1 z.2 threshold) ⁻¹' {k} =
        {z | guard k z} ∩ ⋂ j : Nat,
          (if j < k then {z | guard j z}ᶜ else Set.univ) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
      Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hk
      have hg := rateExit_guard z.1 z.2 hthreshold
      rw [hk] at hg
      refine ⟨hg, ?_⟩
      intro j
      split_ifs with hj
      · simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
        intro hjg
        have hle : ttcReference.firstLoopExit z.1 z.2 threshold ≤ j := by
          unfold ttcReference.firstLoopExit
          exact Nat.sInf_le hjg
        omega
      · simp
    · rintro ⟨hg, hprior⟩
      apply le_antisymm
      · unfold ttcReference.firstLoopExit
        exact Nat.sInf_le hg
      · unfold ttcReference.firstLoopExit
        have hnonempty : {rounds : Nat |
            ((z.2 * z.1.p / (2 : NNReal) ^ rounds : NNReal) : Real) ≤ threshold}.Nonempty :=
          rateExit_exists z.1 z.2 hthreshold
        have hmem := Nat.sInf_mem hnonempty
        by_contra hnot
        have hjk : sInf {rounds : Nat |
            ((z.2 * z.1.p / (2 : NNReal) ^ rounds : NNReal) : Real) ≤ threshold} < k := by
          omega
        have hbad : ¬guard
            (sInf {rounds : Nat |
              ((z.2 * z.1.p / (2 : NNReal) ^ rounds : NNReal) : Real) ≤ threshold}) z := by
          simpa only [if_pos hjk, Set.mem_compl_iff, Set.mem_setOf_eq] using
            hprior (sInf {rounds : Nat |
              ((z.2 * z.1.p / (2 : NNReal) ^ rounds : NNReal) : Real) ≤ threshold})
        exact hbad hmem
  apply measurable_to_countable'
  intro k
  rw [hfiber]
  apply (hguard k).inter
  apply MeasurableSet.iInter
  intro j
  split_ifs
  · exact (hguard j).compl
  · exact MeasurableSet.univ

theorem measurable_rateThinningResult_joint {n : Nat}
    (threshold : Real) (hthreshold : 0 < threshold) :
    Measurable (fun z : (TTCState n × NNReal) × (Nat × Nat → Bool) =>
      ttcReference.firstLoopResult z.1.1 z.1.2 threshold z.2) := by
  classical
  let rounds := fun z : (TTCState n × NNReal) × (Nat × Nat → Bool) =>
    ttcReference.firstLoopExit z.1.1 z.1.2 threshold
  have hrounds : Measurable rounds :=
    (measurable_rateExit_joint threshold hthreshold).comp measurable_fst
  have hstate : Measurable
      (fun z : (TTCState n × NNReal) × (Nat × Nat → Bool) => z.1.1) :=
    measurable_fst.comp measurable_fst
  have hcoords : Measurable
      (fun z : (TTCState n × NNReal) × (Nat × Nat → Bool) =>
        (z.1.1.p, z.1.1.X, z.1.1.nextLabel)) :=
    (comap_measurable _).comp hstate
  have hrate : Measurable
      (fun z : (TTCState n × NNReal) × (Nat × Nat → Bool) => z.1.1.p) :=
    measurable_fst.comp hcoords
  have hsamples : Measurable
      (fun z : (TTCState n × NNReal) × (Nat × Nat → Bool) => z.1.1.X) :=
    (measurable_fst.comp measurable_snd).comp hcoords
  have hnext : Measurable
      (fun z : (TTCState n × NNReal) × (Nat × Nat → Bool) => z.1.1.nextLabel) :=
    (measurable_snd.comp measurable_snd).comp hcoords
  have hcoins : Measurable
      (fun z : (TTCState n × NNReal) × (Nat × Nat → Bool) => z.2) :=
    measurable_snd
  have hsurvives (label : Nat) : Measurable
      (fun q : (Nat × Nat → Bool) × Nat => survives q.1 q.2 label) := by
    apply measurable_from_prod_countable_left
    intro j
    apply measurable_to_prop
    have hevent :
        (fun coins : Nat × Nat → Bool => survives coins j label) ⁻¹' {True} =
          {coins : Nat × Nat → Bool | survives coins j label} := by
      ext coins
      simp
    rw [hevent]
    exact measurableSet_survives j label
  have hretained : Measurable
      (fun z : (TTCState n × NNReal) × (Nat × Nat → Bool) =>
        samplesAfter z.2 (rounds z) z.1.1.X) := by
    rw [measurable_finset_iff]
    intro copy
    have hmem := (measurable_finset_mem copy).comp hsamples
    have hcoin := (hsurvives copy.1).comp (hcoins.prodMk hrounds)
    simpa only [samplesAfter, Finset.mem_filter, Function.comp_apply] using
      hmem.and hcoin
  have hrateJoint : Measurable (fun q : NNReal × Nat =>
      q.1 / (2 : NNReal) ^ q.2) := by
    apply measurable_from_prod_countable_left
    intro j
    exact measurable_id.div_const ((2 : NNReal) ^ j)
  have hnewRate : Measurable
      (fun z : (TTCState n × NNReal) × (Nat × Nat → Bool) =>
        z.1.1.p / (2 : NNReal) ^ rounds z) :=
    hrateJoint.comp (hrate.prodMk hrounds)
  change Measurable (fun z : (TTCState n × NNReal) × (Nat × Nat → Bool) =>
    { p := z.1.1.p / (2 : NNReal) ^ rounds z
      X := samplesAfter z.2 (rounds z) z.1.1.X
      nextLabel := z.1.1.nextLabel : TTCState n })
  rw [measurable_comap_iff]
  exact hnewRate.prodMk (hretained.prodMk hnext)

theorem measurable_rateThinningCost_joint {n : Nat}
    (threshold : Real) (hthreshold : 0 < threshold) :
    Measurable (fun z : TTCState n × NNReal =>
      ttcReference.firstLoopCost z.1 z.2 threshold) := by
  have hcoords : Measurable (fun z : TTCState n × NNReal =>
      (z.1.p, z.1.X, z.1.nextLabel)) :=
    (comap_measurable _).comp measurable_fst
  have hsamples : Measurable (fun z : TTCState n × NNReal => z.1.X) :=
    (measurable_fst.comp measurable_snd).comp hcoords
  have hcard : Measurable (fun z : TTCState n × NNReal => z.1.X.card) :=
    (measurable_of_countable (fun s : Finset (SampleCopy n) => s.card)).comp hsamples
  have hexit := measurable_rateExit_joint (n := n) threshold hthreshold
  have hpair : Measurable (fun z : TTCState n × NNReal =>
      (ttcReference.firstLoopExit z.1 z.2 threshold, z.1.X.card)) :=
    hexit.prodMk hcard
  have hf : Measurable (fun q : Nat × Nat =>
      if q.1 = 0 then 0 else TTCRuntime.rateThinningRoundOperations q.2) :=
    measurable_of_countable _
  unfold ttcReference.firstLoopCost
  exact hf.comp hpair

theorem rateThinWithCost_kernel_measurable {n : Nat}
    (threshold : Real) (hthreshold : 0 < threshold) :
    Measurable (fun z : TTCState n × NNReal =>
      ttcReference.firstLoopWithCost z.1 z.2 threshold) := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  let G := fun z : (TTCState n × NNReal) × (Nat × Nat → Bool) =>
    (ttcReference.firstLoopResult z.1.1 z.1.2 threshold z.2,
      ttcReference.firstLoopCost z.1.1 z.1.2 threshold)
  have hG : Measurable G :=
    (measurable_rateThinningResult_joint threshold hthreshold).prodMk
      ((measurable_rateThinningCost_joint threshold hthreshold).comp measurable_fst)
  have hpair : Measurable
      (fun z : TTCState n × NNReal => fairCoinStreamLaw.map (Prod.mk z)) :=
    Measurable.map_prodMk_left
  have hmap : Measurable
      (fun z : TTCState n × NNReal =>
        (fairCoinStreamLaw.map (Prod.mk z)).map G) :=
    (Measure.measurable_map G hG).comp hpair
  have heq :
      (fun z : TTCState n × NNReal =>
        (fairCoinStreamLaw.map (Prod.mk z)).map G) =
      (fun z : TTCState n × NNReal =>
        ttcReference.firstLoopWithCost z.1 z.2 threshold) := by
    funext z
    rw [Measure.map_map hG measurable_prodMk_left]
    unfold ttcReference.firstLoopWithCost
    rfl
  rw [← heq]
  exact hmap

theorem measurable_countThinningCost_joint {n : Nat}
    (threshold : Real) :
    Measurable (fun z : (TTCState n × Nat) × (Nat × Nat → Bool) =>
      ttcPseudocode.secondLoopCost z.1.1 z.1.2 threshold z.2) := by
  have hrounds : Measurable
      (fun z : (TTCState n × Nat) × (Nat × Nat → Bool) =>
        ttcPseudocode.secondLoopExitRound z.1.1 z.1.2 threshold z.2) :=
    measurable_firstExitRound_joint threshold
  have hcoords : Measurable
      (fun z : (TTCState n × Nat) × (Nat × Nat → Bool) =>
        (z.1.1.p, z.1.1.X, z.1.1.nextLabel)) :=
    (comap_measurable _).comp (measurable_fst.comp measurable_fst)
  have hsamples : Measurable
      (fun z : (TTCState n × Nat) × (Nat × Nat → Bool) => z.1.1.X) :=
    (measurable_fst.comp measurable_snd).comp hcoords
  have hcard : Measurable
      (fun z : (TTCState n × Nat) × (Nat × Nat → Bool) => z.1.1.X.card) :=
    (measurable_of_countable (fun s : Finset (SampleCopy n) => s.card)).comp hsamples
  unfold ttcPseudocode.secondLoopCost
  exact hrounds.mul
    ((measurable_of_countable TTCRuntime.countThinningRoundOperations).comp hcard)

theorem countThinWithCost_kernel_measurable {n : Nat}
    (threshold : Real) :
    Measurable (fun z : TTCState n × Nat =>
      ttcPseudocode.secondLoopWithCost z.1 z.2 threshold) := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  let G := fun z : (TTCState n × Nat) × (Nat × Nat → Bool) =>
    (ttcPseudocode.secondLoopResult z.1.1 z.1.2 threshold z.2,
      ttcPseudocode.secondLoopCost z.1.1 z.1.2 threshold z.2)
  have hG : Measurable G :=
    (measurable_thinningResult_joint threshold).prodMk
      (measurable_countThinningCost_joint threshold)
  have hpair : Measurable
      (fun z : TTCState n × Nat => fairCoinStreamLaw.map (Prod.mk z)) :=
    Measurable.map_prodMk_left
  have hmap : Measurable
      (fun z : TTCState n × Nat =>
        (fairCoinStreamLaw.map (Prod.mk z)).map G) :=
    (Measure.measurable_map G hG).comp hpair
  have heq :
      (fun z : TTCState n × Nat =>
        (fairCoinStreamLaw.map (Prod.mk z)).map G) =
      (fun z : TTCState n × Nat =>
        ttcPseudocode.secondLoopWithCost z.1 z.2 threshold) := by
    funext z
    rw [Measure.map_map hG measurable_prodMk_left]
    unfold ttcPseudocode.secondLoopWithCost
    rfl
  rw [← heq]
  exact hmap

end Kr25Ssmxt
