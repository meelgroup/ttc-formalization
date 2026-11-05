import Kr25Ssmxt.Analysis.ManuscriptOriginActiveRoundsMeasurable

/-! Measurable survivor count and origin indices for the ghost transition. -/

namespace Kr25Ssmxt

open MeasureTheory

noncomputable def manuscriptOriginAdvanceActiveFullCoins
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool)
    (c : ManuscriptOriginConfiguration n) : Nat × Nat → Bool :=
  let deleted := c.state.removeComponent P
  let preRounds := c.level + manuscriptRateExit deleted intensity threshold
  pendingCoinExtension deleted.nextLabel
    (pendingAfter preCoins preRounds deleted.nextLabel basePending)
    (originalSurvivorCoinRestriction preCoins preRounds deleted.nextLabel
      basePending future)

theorem measurable_manuscriptOriginAdvanceActiveFullCoins
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (manuscriptOriginAdvanceActiveFullCoins P intensity threshold
      basePending preCoins future) := by
  exact ManuscriptOriginConfiguration.measurable_activeFullCoins
    P intensity threshold hthreshold basePending preCoins future

noncomputable def manuscriptOriginAdvanceSecondCount
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool)
    (c : ManuscriptOriginConfiguration n) : Nat :=
  let deleted := c.state.removeComponent P
  let preRounds := c.level + manuscriptRateExit deleted intensity threshold
  let pending := pendingAfter preCoins preRounds deleted.nextLabel basePending
  pendingAfter
    (manuscriptOriginAdvanceActiveFullCoins P intensity threshold
      basePending preCoins future c)
    (manuscriptOriginSplitExit P intensity threshold basePending
      preCoins future c) deleted.nextLabel pending

set_option maxHeartbeats 1000000 in
theorem measurable_manuscriptOriginAdvanceSecondCount
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (manuscriptOriginAdvanceSecondCount P intensity threshold
      basePending preCoins future) := by
  have hcontrols := ManuscriptOriginConfiguration.measurable_advance_controls
    P intensity threshold hthreshold
  have hrounds := ManuscriptOriginConfiguration.measurable_advance_activeRounds
    P intensity threshold hthreshold basePending preCoins future
  have hlabel : Measurable (fun c : ManuscriptOriginConfiguration n =>
      (c.state.removeComponent P).nextLabel) :=
    measurable_snd.comp hcontrols
  have hpending := ManuscriptOriginConfiguration.measurable_advance_pending
    P intensity threshold hthreshold basePending preCoins
  exact measurable_pendingAfter_joint.comp
    ((hrounds.prodMk (hlabel.prodMk hpending)).prodMk
      (measurable_manuscriptOriginAdvanceActiveFullCoins P intensity
        threshold hthreshold basePending preCoins future))

noncomputable def manuscriptOriginAdvanceIndex
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool)
    (c : ManuscriptOriginConfiguration n) : Nat → Nat := fun i =>
  let deleted := c.state.removeComponent P
  let preRounds := c.level + manuscriptRateExit deleted intensity threshold
  twoStageSurvivorLabelOrZero preCoins
    (manuscriptOriginAdvanceActiveFullCoins P intensity threshold
      basePending preCoins future c)
    preRounds deleted.nextLabel basePending
    (manuscriptOriginSplitExit P intensity threshold basePending
      preCoins future c) i

set_option maxHeartbeats 1000000 in
theorem measurable_manuscriptOriginAdvanceIndex
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (manuscriptOriginAdvanceIndex P intensity threshold
      basePending preCoins future) := by
  have hcontrols := ManuscriptOriginConfiguration.measurable_advance_controls
    P intensity threshold hthreshold
  have hpre : Measurable (fun c : ManuscriptOriginConfiguration n =>
      c.level + manuscriptRateExit (c.state.removeComponent P)
        intensity threshold) := measurable_fst.comp hcontrols
  have hlabel : Measurable (fun c : ManuscriptOriginConfiguration n =>
      (c.state.removeComponent P).nextLabel) :=
    measurable_snd.comp hcontrols
  have hrounds := ManuscriptOriginConfiguration.measurable_advance_activeRounds
    P intensity threshold hthreshold basePending preCoins future
  have hactive := measurable_manuscriptOriginAdvanceActiveFullCoins
    P intensity threshold hthreshold basePending preCoins future
  apply Measurable.of_eval
  intro i
  exact measurable_twoStageSurvivorLabelOrZero_joint.comp
    ((hpre.prodMk
      (hlabel.prodMk
        (measurable_const.prodMk
          (hrounds.prodMk measurable_const)))).prodMk
      (measurable_const.prodMk hactive))

noncomputable def manuscriptOriginAdvanceOriginTotal
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool)
    (c : ManuscriptOriginConfiguration n) : Nat → Nat × Nat :=
  manuscriptOriginAppend c.origin c.source.processed
    (c.state.removeComponent P).nextLabel
    (manuscriptOriginAdvanceSecondCount P intensity threshold
      basePending preCoins future c)
    (fun i => manuscriptOriginAdvanceIndex P intensity threshold
      basePending preCoins future c i.val)

set_option maxHeartbeats 1000000 in
theorem measurable_manuscriptOriginAdvanceOriginTotal
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (manuscriptOriginAdvanceOriginTotal P intensity threshold
      basePending preCoins future) := by
  have hcomponent : Measurable (fun c : ManuscriptOriginConfiguration n =>
      c.source.processed) :=
    measurable_manuscriptOriginSourceState_processed.comp
      measurable_manuscriptOriginConfiguration_source
  have hlabel : Measurable (fun c : ManuscriptOriginConfiguration n =>
      (c.state.removeComponent P).nextLabel) :=
    measurable_snd.comp
      (ManuscriptOriginConfiguration.measurable_advance_controls
        P intensity threshold hthreshold)
  have hcount := measurable_manuscriptOriginAdvanceSecondCount
    P intensity threshold hthreshold basePending preCoins future
  have horigin := measurable_manuscriptOriginConfiguration_origin
    (n := n)
  have hindex := measurable_manuscriptOriginAdvanceIndex
    P intensity threshold hthreshold basePending preCoins future
  exact measurable_manuscriptOriginAppend_joint.comp
    ((hcomponent.prodMk (hlabel.prodMk hcount)).prodMk
      (horigin.prodMk hindex))

set_option maxHeartbeats 1000000 in
theorem ManuscriptOriginConfiguration.advance_origin_eq_total
    {n : Nat} (c : ManuscriptOriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool)
    (tape : Nat → LatticePoint n) :
    (c.advance P intensity threshold basePending preCoins future tape).origin =
      manuscriptOriginAdvanceOriginTotal P intensity threshold basePending
        preCoins future c := by
  let deleted := c.state.removeComponent P
  let preRounds := c.level + manuscriptRateExit deleted intensity threshold
  let pending := pendingAfter preCoins preRounds deleted.nextLabel basePending
  let activeCoins := originalSurvivorCoinRestriction preCoins preRounds
    deleted.nextLabel basePending future
  let first := manuscriptRateThinningResult deleted intensity threshold
    (manuscriptSourceOldCoins c.origin c.source.coins c.level)
  let activeRounds := manuscriptOriginSplitExit P intensity threshold
    basePending preCoins future c
  let second := thinningResultSplitFinite first pending threshold
    (shiftCoins (manuscriptRateExit deleted intensity threshold)
      (manuscriptSourceOldCoins c.origin c.source.coins c.level)) activeCoins
  have hcount : manuscriptOriginAdvanceSecondCount P intensity threshold
      basePending preCoins future c = second.2 := rfl
  change manuscriptOriginAppend c.origin c.source.processed
      deleted.nextLabel second.2
        (fun i => twoStageSurvivorLabel preCoins preRounds
          deleted.nextLabel basePending activeCoins activeRounds i) =
    manuscriptOriginAppend c.origin c.source.processed
      deleted.nextLabel second.2
        (fun i => manuscriptOriginAdvanceIndex P intensity threshold
          basePending preCoins future c i.val)
  congr 1
  funext i
  exact (twoStageSurvivorLabelOrZero_eq preCoins preRounds
    deleted.nextLabel basePending activeRounds activeCoins i).symm

set_option maxHeartbeats 1000000 in
theorem ManuscriptOriginConfiguration.measurable_advance_origin_joint
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (fun z : ManuscriptOriginConfiguration n ×
        (Nat → LatticePoint n) =>
      (z.1.advance P intensity threshold basePending preCoins future
        z.2).origin) := by
  have heq : (fun z : ManuscriptOriginConfiguration n ×
      (Nat → LatticePoint n) =>
      (z.1.advance P intensity threshold basePending preCoins future
        z.2).origin) =
      (fun z => manuscriptOriginAdvanceOriginTotal P intensity threshold
        basePending preCoins future z.1) := by
    funext z
    exact z.1.advance_origin_eq_total P intensity threshold basePending
      preCoins future z.2
  rw [heq]
  exact (measurable_manuscriptOriginAdvanceOriginTotal P intensity
    threshold hthreshold basePending preCoins future).comp measurable_fst

end Kr25Ssmxt
