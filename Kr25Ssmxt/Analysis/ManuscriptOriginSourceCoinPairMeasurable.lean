import Kr25Ssmxt.Analysis.ManuscriptOriginCoinParametersMeasurable

/-! Source coin splicing with a random incoming source and random independent
coin arrays. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem measurable_spliceCoins_joint :
    Measurable (fun z : Nat ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      spliceCoins z.2.1 z.2.2 z.1) := by
  apply measurable_from_prod_countable_right
  intro rounds
  exact measurable_spliceCoins_pair rounds

theorem measurable_manuscriptCoinsAppend_joint {n : Nat} :
    Measurable (fun z :
        (ManuscriptOriginSourceState n × Nat) ×
          ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      manuscriptCoinsAppend z.1.1.coins z.1.1.processed
        z.2.1 z.2.2 z.1.2) := by
  apply Measurable.of_eval
  intro component
  apply Measurable.of_eval
  intro pair
  have hsource : Measurable (fun z :
      (ManuscriptOriginSourceState n × Nat) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) => z.1.1) :=
    measurable_fst.comp measurable_fst
  have hprocessed : Measurable (fun z :
      (ManuscriptOriginSourceState n × Nat) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      z.1.1.processed) :=
    measurable_manuscriptOriginSourceState_processed.comp hsource
  have hcond : MeasurableSet {z :
      (ManuscriptOriginSourceState n × Nat) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) |
      component = z.1.1.processed} :=
    measurableSet_eq_fun measurable_const hprocessed
  have hsplice : Measurable (fun z :
      (ManuscriptOriginSourceState n × Nat) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      spliceCoins z.2.1 z.2.2 z.1.2 pair) :=
    (measurable_pi_apply pair).comp
      (measurable_spliceCoins_joint.comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hold : Measurable (fun z :
      (ManuscriptOriginSourceState n × Nat) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      z.1.1.coins component pair) :=
    (measurable_pi_apply pair).comp
      ((measurable_pi_apply component).comp
        (measurable_manuscriptOriginSourceState_coins.comp hsource))
  have heq : (fun z :
      (ManuscriptOriginSourceState n × Nat) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      manuscriptCoinsAppend z.1.1.coins z.1.1.processed
        z.2.1 z.2.2 z.1.2 component pair) =
      (fun z => if component = z.1.1.processed then
        spliceCoins z.2.1 z.2.2 z.1.2 pair
        else z.1.1.coins component pair) := by
    funext z
    by_cases h : component = z.1.1.processed <;>
      simp [manuscriptCoinsAppend, h]
  rw [heq]
  exact Measurable.ite hcond hsplice hold

noncomputable def manuscriptOriginSourceStepCoinPair
    {n : Nat} (P : PolytopeData n) (basePending : Nat) :
    (Nat × Nat) ×
        ((ManuscriptOriginSourceState n × (Nat → LatticePoint n)) ×
          ((Nat × Nat → Bool) × (Nat × Nat → Bool))) →
      ManuscriptOriginSourceState n := fun z =>
      z.2.1.1.step
        { component := P
          firstLabel := z.1.1
          basePending := basePending
          preRounds := z.1.2
          preCoins := z.2.2.1
          futureCoins := z.2.2.2
          tape := z.2.1.2 }

theorem measurable_manuscriptValidUpdate_label_source
    {n : Nat} (P : PolytopeData n) (basePending : Nat) :
    Measurable (fun w : Nat × ManuscriptOriginSourceState n =>
      manuscriptValidUpdate w.2.valid w.2.marks P w.2.processed
        w.1 basePending) := by
  apply measurable_from_prod_countable_right
  intro firstLabel
  exact measurable_manuscriptValidUpdate_source P firstLabel basePending

private abbrev ManuscriptSourceCoinInput (n : Nat) :=
  (Nat × Nat) ×
    ((ManuscriptOriginSourceState n × (Nat → LatticePoint n)) ×
      ((Nat × Nat → Bool) × (Nat × Nat → Bool)))

private theorem measurable_sourceCoinInput_source {n : Nat} :
    Measurable (fun z : ManuscriptSourceCoinInput n => z.2.1.1) :=
  measurable_fst.comp (measurable_fst.comp measurable_snd)

private theorem measurable_sourceCoinInput_processed {n : Nat} :
    Measurable (fun z : ManuscriptSourceCoinInput n =>
      z.2.1.1.processed + 1) :=
  (measurable_of_countable (fun r : Nat => r + 1)).comp
    (measurable_manuscriptOriginSourceState_processed.comp
      measurable_sourceCoinInput_source)

set_option maxHeartbeats 1000000 in
private theorem measurable_sourceCoinInput_valid {n : Nat}
    (P : PolytopeData n) (basePending : Nat) :
    Measurable (fun z : ManuscriptSourceCoinInput n =>
      manuscriptValidUpdate z.2.1.1.valid z.2.1.1.marks P
        z.2.1.1.processed z.1.1 basePending) := by
  classical
  rw [measurable_finset_iff]
  intro tag
  have hvalid : Measurable (fun z : ManuscriptSourceCoinInput n =>
      tag ∈ z.2.1.1.valid) :=
    (measurable_finset_mem tag).comp
      (measurable_manuscriptOriginSourceState_valid.comp
        measurable_sourceCoinInput_source)
  have hmark : Measurable (fun z : ManuscriptSourceCoinInput n =>
      z.2.1.1.marks tag) :=
    (measurable_pi_apply tag).comp
      (measurable_manuscriptOriginSourceState_marks.comp
        measurable_sourceCoinInput_source)
  have hout : Measurable (fun z : ManuscriptSourceCoinInput n =>
      (z.2.1.1.marks tag).toPoint ∉ P.carrier) :=
    (measurable_of_countable
      (fun mark : LatticePoint n => mark.toPoint ∉ P.carrier)).comp
        hmark
  have hprocessed : Measurable (fun z : ManuscriptSourceCoinInput n =>
      z.2.1.1.processed) :=
    measurable_manuscriptOriginSourceState_processed.comp
      measurable_sourceCoinInput_source
  have hfirst : Measurable (fun z : ManuscriptSourceCoinInput n =>
      z.1.1) := measurable_fst.comp measurable_fst
  have hnew : Measurable (fun z : ManuscriptSourceCoinInput n =>
      tag ∈ manuscriptSourceTags z.2.1.1.processed z.1.1
        basePending) :=
    (measurable_of_countable
      (fun q : Nat × Nat =>
        tag ∈ manuscriptSourceTags q.1 q.2 basePending)).comp
      (hprocessed.prodMk hfirst)
  simpa only [manuscriptValidUpdate, Finset.mem_union,
    Finset.mem_filter] using (hvalid.and hout).or hnew

private theorem measurable_sourceCoinInput_marks {n : Nat} :
    Measurable (fun z : ManuscriptSourceCoinInput n =>
      manuscriptMarksAppend z.2.1.1.marks z.2.1.1.processed
        z.2.1.2) :=
  measurable_manuscriptMarksAppend_source_tape.comp
    (measurable_fst.comp measurable_snd)

private theorem measurable_sourceCoinInput_coins {n : Nat} :
    Measurable (fun z : ManuscriptSourceCoinInput n =>
      manuscriptCoinsAppend z.2.1.1.coins z.2.1.1.processed
        z.2.2.1 z.2.2.2 z.1.2) :=
  measurable_manuscriptCoinsAppend_joint.comp
    ((measurable_sourceCoinInput_source.prodMk
      (measurable_snd.comp measurable_fst)).prodMk
        (measurable_snd.comp measurable_snd))

private theorem measurable_sourceCoinInput_data {n : Nat}
    (P : PolytopeData n) (basePending : Nat) :
    Measurable (fun z : ManuscriptSourceCoinInput n =>
      (z.2.1.1.processed + 1,
        manuscriptValidUpdate z.2.1.1.valid z.2.1.1.marks P
          z.2.1.1.processed z.1.1 basePending,
        manuscriptMarksAppend z.2.1.1.marks z.2.1.1.processed z.2.1.2,
        manuscriptCoinsAppend z.2.1.1.coins z.2.1.1.processed
          z.2.2.1 z.2.2.2 z.1.2)) :=
  measurable_sourceCoinInput_processed.prodMk
    ((measurable_sourceCoinInput_valid P basePending).prodMk
      (measurable_sourceCoinInput_marks.prodMk
        measurable_sourceCoinInput_coins))

set_option maxHeartbeats 1000000 in
theorem measurable_manuscriptOriginSourceStepCoinPair
    {n : Nat} (P : PolytopeData n) (basePending : Nat) :
    Measurable (manuscriptOriginSourceStepCoinPair P basePending) := by
  rw [measurable_comap_iff]
  exact measurable_sourceCoinInput_data P basePending

set_option maxHeartbeats 1000000 in
theorem ManuscriptOriginConfiguration.measurable_advance_source_coinPair
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (fun z :
        (ManuscriptOriginConfiguration n ×
          ((Nat × Nat → Bool) × (Nat × Nat → Bool))) ×
          (Nat → LatticePoint n) =>
      (z.1.1.advance P intensity threshold basePending z.1.2.1
        z.1.2.2 z.2).source) := by
  have hconfig : Measurable (fun z :
      (ManuscriptOriginConfiguration n ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool))) ×
        (Nat → LatticePoint n) => z.1.1) :=
    measurable_fst.comp measurable_fst
  have hcontrols :=
    (ManuscriptOriginConfiguration.measurable_advance_controls
      P intensity threshold hthreshold).comp hconfig
  have hparams : Measurable (fun z :
      (ManuscriptOriginConfiguration n ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool))) ×
        (Nat → LatticePoint n) =>
      ((z.1.1.state.removeComponent P).nextLabel,
        z.1.1.level + ttcPseudocode.firstLoopExit
          (z.1.1.state.removeComponent P) intensity threshold)) :=
    (measurable_snd.comp hcontrols).prodMk
      (measurable_fst.comp hcontrols)
  have hsourceTape : Measurable (fun z :
      (ManuscriptOriginConfiguration n ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool))) ×
        (Nat → LatticePoint n) => (z.1.1.source, z.2)) :=
    (measurable_manuscriptOriginConfiguration_source.comp hconfig).prodMk
      measurable_snd
  have hinput :=
    (measurable_manuscriptOriginSourceStepCoinPair P basePending).comp
      (hparams.prodMk
        (hsourceTape.prodMk (measurable_snd.comp measurable_fst)))
  have heq : (fun z :
      (ManuscriptOriginConfiguration n ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool))) ×
        (Nat → LatticePoint n) =>
      (z.1.1.advance P intensity threshold basePending z.1.2.1
        z.1.2.2 z.2).source) =
      (fun z => manuscriptOriginSourceStepCoinPair P basePending
        (((z.1.1.state.removeComponent P).nextLabel,
            z.1.1.level + ttcPseudocode.firstLoopExit
              (z.1.1.state.removeComponent P) intensity threshold),
          ((z.1.1.source, z.2), z.1.2))) := by
    funext z
    exact z.1.1.advance_source P intensity threshold basePending
      z.1.2.1 z.1.2.2 z.2
  rw [heq]
  exact hinput

set_option maxHeartbeats 1000000 in
theorem ManuscriptOriginConfiguration.measurable_advance_level_coinPair
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) :
    Measurable (fun z :
        (ManuscriptOriginConfiguration n ×
          ((Nat × Nat → Bool) × (Nat × Nat → Bool))) ×
          (Nat → LatticePoint n) =>
      (z.1.1.advance P intensity threshold basePending z.1.2.1
        z.1.2.2 z.2).level) := by
  have hpre : Measurable (fun z :
      (ManuscriptOriginConfiguration n ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool))) ×
        (Nat → LatticePoint n) =>
      z.1.1.level + ttcPseudocode.firstLoopExit
        (z.1.1.state.removeComponent P) intensity threshold) :=
    (measurable_fst.comp
      (ManuscriptOriginConfiguration.measurable_advance_controls
        P intensity threshold hthreshold)).comp
      (measurable_fst.comp measurable_fst)
  have hactive : Measurable (fun z :
      (ManuscriptOriginConfiguration n ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool))) ×
        (Nat → LatticePoint n) =>
      manuscriptOriginCoinPairSplitExit P intensity threshold
        basePending z.1) :=
    (measurable_manuscriptOriginCoinPairSplitExit P intensity threshold
      hthreshold basePending).comp measurable_fst
  have heq : (fun z :
      (ManuscriptOriginConfiguration n ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool))) ×
        (Nat → LatticePoint n) =>
      (z.1.1.advance P intensity threshold basePending z.1.2.1
        z.1.2.2 z.2).level) =
      (fun z => z.1.1.level + ttcPseudocode.firstLoopExit
          (z.1.1.state.removeComponent P) intensity threshold +
        manuscriptOriginCoinPairSplitExit P intensity threshold
          basePending z.1) := by
    funext z
    exact z.1.1.advance_level P intensity threshold basePending
      z.1.2.1 z.1.2.2 z.2
  rw [heq]
  exact hpre.add hactive

end Kr25Ssmxt
