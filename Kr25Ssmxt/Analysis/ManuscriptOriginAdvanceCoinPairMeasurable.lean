import Kr25Ssmxt.Analysis.ManuscriptOriginSourceCoinPairMeasurable

/-! Origin labels and survivor counts with both coin arrays random. -/

namespace Kr25Ssmxt

open MeasureTheory

private abbrev ManuscriptGhostCoinInput (n : Nat) :=
  ManuscriptOriginConfiguration n ×
    ((Nat × Nat → Bool) × (Nat × Nat → Bool))

noncomputable def manuscriptOriginCoinPairActiveFull
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (z : ManuscriptGhostCoinInput n) : Nat × Nat → Bool :=
  let deleted := z.1.state.removeComponent P
  let preRounds := z.1.level + manuscriptRateExit deleted intensity threshold
  pendingCoinExtension deleted.nextLabel
    (pendingAfter z.2.1 preRounds deleted.nextLabel basePending)
    (originalSurvivorCoinRestriction z.2.1 preRounds deleted.nextLabel
      basePending z.2.2)

theorem measurable_manuscriptOriginCoinPairActiveFull
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (manuscriptOriginCoinPairActiveFull P intensity threshold
      basePending) :=
  ManuscriptOriginConfiguration.measurable_activeFullCoins_coinPair
    P intensity threshold hthreshold basePending

noncomputable def manuscriptOriginCoinPairSecondCount
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (z : ManuscriptGhostCoinInput n) : Nat :=
  let deleted := z.1.state.removeComponent P
  let preRounds := z.1.level + manuscriptRateExit deleted intensity threshold
  let pending := pendingAfter z.2.1 preRounds deleted.nextLabel basePending
  pendingAfter (manuscriptOriginCoinPairActiveFull P intensity threshold
    basePending z)
    (manuscriptOriginCoinPairSplitExit P intensity threshold basePending z)
    deleted.nextLabel pending

set_option maxHeartbeats 1000000 in
theorem measurable_manuscriptOriginCoinPairSecondCount
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (manuscriptOriginCoinPairSecondCount P intensity threshold
      basePending) := by
  have hcontrols : Measurable (fun z : ManuscriptGhostCoinInput n =>
      (z.1.level + manuscriptRateExit (z.1.state.removeComponent P)
        intensity threshold, (z.1.state.removeComponent P).nextLabel)) :=
    (ManuscriptOriginConfiguration.measurable_advance_controls
      P intensity threshold hthreshold).comp measurable_fst
  have hlabel : Measurable (fun z : ManuscriptGhostCoinInput n =>
      (z.1.state.removeComponent P).nextLabel) :=
    measurable_snd.comp hcontrols
  have hpending := ManuscriptOriginConfiguration.measurable_pending_coinPair
    P intensity threshold hthreshold basePending
  have hrounds := measurable_manuscriptOriginCoinPairSplitExit
    P intensity threshold hthreshold basePending
  have hactive := measurable_manuscriptOriginCoinPairActiveFull
    P intensity threshold hthreshold basePending
  exact measurable_pendingAfter_joint.comp
    ((hrounds.prodMk (hlabel.prodMk hpending)).prodMk hactive)

noncomputable def manuscriptOriginCoinPairIndex
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (z : ManuscriptGhostCoinInput n) : Nat → Nat := fun i =>
  let deleted := z.1.state.removeComponent P
  let preRounds := z.1.level + manuscriptRateExit deleted intensity threshold
  twoStageSurvivorLabelOrZero z.2.1
    (manuscriptOriginCoinPairActiveFull P intensity threshold basePending z)
    preRounds deleted.nextLabel basePending
    (manuscriptOriginCoinPairSplitExit P intensity threshold basePending z) i

set_option maxHeartbeats 1000000 in
theorem measurable_manuscriptOriginCoinPairIndex
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (manuscriptOriginCoinPairIndex P intensity threshold
      basePending) := by
  have hcontrols : Measurable (fun z : ManuscriptGhostCoinInput n =>
      (z.1.level + manuscriptRateExit (z.1.state.removeComponent P)
        intensity threshold, (z.1.state.removeComponent P).nextLabel)) :=
    (ManuscriptOriginConfiguration.measurable_advance_controls
      P intensity threshold hthreshold).comp measurable_fst
  have hpre : Measurable (fun z : ManuscriptGhostCoinInput n =>
      z.1.level + manuscriptRateExit (z.1.state.removeComponent P)
        intensity threshold) := measurable_fst.comp hcontrols
  have hlabel : Measurable (fun z : ManuscriptGhostCoinInput n =>
      (z.1.state.removeComponent P).nextLabel) :=
    measurable_snd.comp hcontrols
  have hrounds := measurable_manuscriptOriginCoinPairSplitExit
    P intensity threshold hthreshold basePending
  have hactive := measurable_manuscriptOriginCoinPairActiveFull
    P intensity threshold hthreshold basePending
  apply measurable_pi_lambda
  intro i
  exact measurable_twoStageSurvivorLabelOrZero_joint.comp
    ((hpre.prodMk
      (hlabel.prodMk
        (measurable_const.prodMk
          (hrounds.prodMk measurable_const)))).prodMk
      ((measurable_fst.comp measurable_snd).prodMk hactive))

noncomputable def manuscriptOriginCoinPairOriginTotal
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (basePending : Nat)
    (z : ManuscriptGhostCoinInput n) : Nat → Nat × Nat :=
  manuscriptOriginAppend z.1.origin z.1.source.processed
    (z.1.state.removeComponent P).nextLabel
    (manuscriptOriginCoinPairSecondCount P intensity threshold
      basePending z)
    (fun i => manuscriptOriginCoinPairIndex P intensity threshold
      basePending z i.val)

set_option maxHeartbeats 1000000 in
theorem measurable_manuscriptOriginCoinPairOriginTotal
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (manuscriptOriginCoinPairOriginTotal P intensity threshold
      basePending) := by
  have hcomponent : Measurable (fun z : ManuscriptGhostCoinInput n =>
      z.1.source.processed) :=
    (measurable_manuscriptOriginSourceState_processed.comp
      measurable_manuscriptOriginConfiguration_source).comp measurable_fst
  have hlabel : Measurable (fun z : ManuscriptGhostCoinInput n =>
      (z.1.state.removeComponent P).nextLabel) :=
    (measurable_snd.comp
      (ManuscriptOriginConfiguration.measurable_advance_controls
        P intensity threshold hthreshold)).comp measurable_fst
  have hcount := measurable_manuscriptOriginCoinPairSecondCount
    P intensity threshold hthreshold basePending
  have horigin : Measurable (fun z : ManuscriptGhostCoinInput n =>
      z.1.origin) :=
    measurable_manuscriptOriginConfiguration_origin.comp measurable_fst
  have hindex := measurable_manuscriptOriginCoinPairIndex
    P intensity threshold hthreshold basePending
  exact measurable_manuscriptOriginAppend_joint.comp
    ((hcomponent.prodMk (hlabel.prodMk hcount)).prodMk
      (horigin.prodMk hindex))

set_option maxHeartbeats 1000000 in
theorem ManuscriptOriginConfiguration.advance_origin_eq_coinPairTotal
    {n : Nat} (z : ManuscriptGhostCoinInput n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (tape : Nat → LatticePoint n) :
    (z.1.advance P intensity threshold basePending z.2.1 z.2.2
      tape).origin =
      manuscriptOriginCoinPairOriginTotal P intensity threshold
        basePending z := by
  let deleted := z.1.state.removeComponent P
  let preRounds := z.1.level + manuscriptRateExit deleted intensity threshold
  let pending := pendingAfter z.2.1 preRounds deleted.nextLabel basePending
  let activeCoins := originalSurvivorCoinRestriction z.2.1 preRounds
    deleted.nextLabel basePending z.2.2
  let first := manuscriptRateThinningResult deleted intensity threshold
    (manuscriptSourceOldCoins z.1.origin z.1.source.coins z.1.level)
  let activeRounds := manuscriptOriginCoinPairSplitExit P intensity threshold
    basePending z
  let second := thinningResultSplitFinite first pending threshold
    (shiftCoins (manuscriptRateExit deleted intensity threshold)
      (manuscriptSourceOldCoins z.1.origin z.1.source.coins z.1.level))
    activeCoins
  change manuscriptOriginAppend z.1.origin z.1.source.processed
      deleted.nextLabel second.2
        (fun i => twoStageSurvivorLabel z.2.1 preRounds
          deleted.nextLabel basePending activeCoins activeRounds i) =
    manuscriptOriginAppend z.1.origin z.1.source.processed
      deleted.nextLabel second.2
        (fun i => manuscriptOriginCoinPairIndex P intensity threshold
          basePending z i.val)
  congr 1
  funext i
  exact (twoStageSurvivorLabelOrZero_eq z.2.1 preRounds
    deleted.nextLabel basePending activeRounds activeCoins i).symm

set_option maxHeartbeats 1000000 in
theorem ManuscriptOriginConfiguration.measurable_advance_origin_coinPair
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (fun z : ManuscriptGhostCoinInput n ×
        (Nat → LatticePoint n) =>
      (z.1.1.advance P intensity threshold basePending z.1.2.1
        z.1.2.2 z.2).origin) := by
  have heq : (fun z : ManuscriptGhostCoinInput n ×
      (Nat → LatticePoint n) =>
      (z.1.1.advance P intensity threshold basePending z.1.2.1
        z.1.2.2 z.2).origin) =
      (fun z => manuscriptOriginCoinPairOriginTotal P intensity threshold
        basePending z.1) := by
    funext z
    exact ManuscriptOriginConfiguration.advance_origin_eq_coinPairTotal
      z.1 P intensity threshold basePending z.2
  rw [heq]
  exact (measurable_manuscriptOriginCoinPairOriginTotal P intensity
    threshold hthreshold basePending).comp measurable_fst

end Kr25Ssmxt
