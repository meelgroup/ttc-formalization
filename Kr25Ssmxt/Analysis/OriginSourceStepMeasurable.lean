import Kr25Ssmxt.Analysis.OriginMarginalKernel

/-! Joint measurability of the ghost source update when its incoming source
state and the appended point tape are random. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem measurable_validUpdate_source
    {n : Nat} (P : PolytopeData n) (firstLabel basePending : Nat) :
    Measurable (fun g : OriginSourceState n =>
      validUpdate g.valid g.marks P g.processed
        firstLabel basePending) := by
  classical
  rw [measurable_finset_iff]
  intro tag
  have hvalid : Measurable (fun g : OriginSourceState n =>
      tag ∈ g.valid) :=
    (measurable_finset_mem tag).comp
      measurable_originSourceState_valid
  have hmark : Measurable (fun g : OriginSourceState n =>
      g.marks tag) :=
    (measurable_pi_apply tag).comp
      measurable_originSourceState_marks
  have hout : Measurable (fun g : OriginSourceState n =>
      (g.marks tag).toPoint ∉ P.carrier) :=
    (measurable_of_countable
      (fun mark : LatticePoint n => mark.toPoint ∉ P.carrier)).comp hmark
  have hprocessed : Measurable
      (fun g : OriginSourceState n => g.processed) :=
    measurable_originSourceState_processed
  have hnew : Measurable (fun g : OriginSourceState n =>
      tag ∈ originSourceTags g.processed firstLabel basePending) :=
    (measurable_of_countable
      (fun component : Nat =>
        tag ∈ originSourceTags component firstLabel basePending)).comp
      hprocessed
  change Measurable (fun g : OriginSourceState n =>
    tag ∈ validUpdate g.valid g.marks P g.processed
      firstLabel basePending)
  simpa only [validUpdate, Finset.mem_union,
    Finset.mem_filter] using (hvalid.and hout).or hnew

theorem measurable_marksAppend_source_tape
    {n : Nat} :
    Measurable (fun z : OriginSourceState n ×
        (Nat → LatticePoint n) =>
      marksAppend z.1.marks z.1.processed z.2) := by
  apply Measurable.of_eval
  intro tag
  have hprocessed : Measurable (fun z : OriginSourceState n ×
      (Nat → LatticePoint n) => z.1.processed) :=
    measurable_originSourceState_processed.comp measurable_fst
  have hcond : MeasurableSet
      {z : OriginSourceState n × (Nat → LatticePoint n) |
        tag.1 = z.1.processed} :=
    measurableSet_eq_fun measurable_const hprocessed
  change Measurable (fun z : OriginSourceState n ×
      (Nat → LatticePoint n) =>
    if tag.1 = z.1.processed then z.2 tag.2 else z.1.marks tag)
  exact Measurable.ite hcond
    ((measurable_pi_apply tag.2).comp measurable_snd)
    ((measurable_pi_apply tag).comp
      (measurable_originSourceState_marks.comp measurable_fst))

theorem measurable_coinsAppend_source
    {n : Nat} (preCoins future : Nat × Nat → Bool) (preRounds : Nat) :
    Measurable (fun g : OriginSourceState n =>
      coinsAppend g.coins g.processed preCoins future preRounds) := by
  apply Measurable.of_eval
  intro component
  apply Measurable.of_eval
  intro pair
  have hcond : MeasurableSet
      {g : OriginSourceState n | component = g.processed} :=
    measurableSet_eq_fun measurable_const
      measurable_originSourceState_processed
  have heq : (fun g : OriginSourceState n =>
      coinsAppend g.coins g.processed preCoins future
        preRounds component pair) =
      (fun g => if component = g.processed then
        spliceCoins preCoins future preRounds pair
        else g.coins component pair) := by
    funext g
    by_cases h : component = g.processed <;>
      simp [coinsAppend, h]
  rw [heq]
  exact Measurable.ite hcond measurable_const
    ((measurable_pi_apply pair).comp
      ((measurable_pi_apply component).comp
        measurable_originSourceState_coins))

theorem OriginSourceState.measurable_step_source_tape
    {n : Nat} (P : PolytopeData n)
    (firstLabel basePending preRounds : Nat)
    (preCoins future : Nat × Nat → Bool) :
    Measurable (fun z : OriginSourceState n ×
        (Nat → LatticePoint n) =>
      z.1.step
        { component := P
          firstLabel := firstLabel
          basePending := basePending
          preRounds := preRounds
          preCoins := preCoins
          futureCoins := future
          tape := z.2 }) := by
  rw [measurable_comap_iff]
  change Measurable (fun z : OriginSourceState n ×
      (Nat → LatticePoint n) =>
    (z.1.processed + 1,
      validUpdate z.1.valid z.1.marks P z.1.processed
        firstLabel basePending,
      marksAppend z.1.marks z.1.processed z.2,
      coinsAppend z.1.coins z.1.processed preCoins future
        preRounds))
  have hprocessed : Measurable (fun z : OriginSourceState n ×
      (Nat → LatticePoint n) => z.1.processed + 1) :=
    (measurable_of_countable (fun q : Nat => q + 1)).comp
      (measurable_originSourceState_processed.comp measurable_fst)
  exact hprocessed.prodMk
    (((measurable_validUpdate_source P firstLabel basePending).comp
      measurable_fst).prodMk
      (measurable_marksAppend_source_tape.prodMk
        ((measurable_coinsAppend_source preCoins future preRounds).comp
          measurable_fst)))

/-- The finite label and round parameters may themselves be random. This is
the form needed when the incoming ghost configuration varies in a fold. -/
theorem OriginSourceState.measurable_step_parameters_source_tape
    {n : Nat} (P : PolytopeData n) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool) :
    Measurable (fun z : (Nat × Nat) ×
        (OriginSourceState n × (Nat → LatticePoint n)) =>
      z.2.1.step
        { component := P
          firstLabel := z.1.1
          basePending := basePending
          preRounds := z.1.2
          preCoins := preCoins
          futureCoins := future
          tape := z.2.2 }) := by
  apply measurable_from_prod_countable_right
  intro params
  exact OriginSourceState.measurable_step_source_tape P
    params.1 basePending params.2 preCoins future

theorem OriginConfiguration.measurable_advance_source_joint_of_parameters
    {n : Nat} (P : PolytopeData n) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool)
    (firstLabel preRounds : OriginConfiguration n → Nat)
    (hfirst : Measurable firstLabel) (hrounds : Measurable preRounds) :
    Measurable (fun z : OriginConfiguration n ×
        (Nat → LatticePoint n) =>
      z.1.source.step
        { component := P
          firstLabel := firstLabel z.1
          basePending := basePending
          preRounds := preRounds z.1
          preCoins := preCoins
          futureCoins := future
          tape := z.2 }) := by
  let hparameters : Measurable (fun z : OriginConfiguration n ×
      (Nat → LatticePoint n) => (firstLabel z.1, preRounds z.1)) :=
    (hfirst.comp measurable_fst).prodMk
      (hrounds.comp measurable_fst)
  let hsourceTape : Measurable (fun z : OriginConfiguration n ×
      (Nat → LatticePoint n) => (z.1.source, z.2)) :=
    (measurable_originConfiguration_source.comp
      measurable_fst).prodMk measurable_snd
  exact (OriginSourceState.measurable_step_parameters_source_tape
    P basePending preCoins future).comp
      (hparameters.prodMk hsourceTape)

set_option maxHeartbeats 1000000 in
/-- The source projection of the actual ghost advance is jointly measurable
in the incoming configuration and the sampler tape. -/
theorem OriginConfiguration.measurable_advance_source_joint
    {n : Nat} (P : PolytopeData n) (intensity : NNReal)
    (threshold : Real) (hthreshold : 0 < threshold)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool) :
    Measurable (fun z : OriginConfiguration n ×
        (Nat → LatticePoint n) =>
      (z.1.advance P intensity threshold basePending preCoins future
        z.2).source) := by
  have hstate : Measurable (fun c : OriginConfiguration n =>
      c.state) := measurable_originConfiguration_state
  have hfirst : Measurable (fun c : OriginConfiguration n =>
      c.state.nextLabel) :=
    ((measurable_snd.comp measurable_snd).comp
      (comap_measurable (fun s : TTCState n =>
        (s.p, s.X, s.nextLabel)))).comp hstate
  have hround : Measurable (fun c : OriginConfiguration n =>
      ttcPseudocode.firstLoopExit (c.state.removeComponent P) intensity
        threshold) :=
    (measurable_rateExit_joint threshold hthreshold).comp
      (((measurable_removeComponent P).comp hstate).prodMk
        measurable_const)
  have hpre : Measurable (fun c : OriginConfiguration n =>
      c.level + ttcPseudocode.firstLoopExit (c.state.removeComponent P)
        intensity threshold) :=
    measurable_originConfiguration_level.add hround
  have heq : (fun z : OriginConfiguration n ×
      (Nat → LatticePoint n) =>
      (z.1.advance P intensity threshold basePending preCoins future
        z.2).source) =
      (fun z => z.1.source.step
        { component := P
          firstLabel := z.1.state.nextLabel
          basePending := basePending
          preRounds := z.1.level + ttcPseudocode.firstLoopExit
            (z.1.state.removeComponent P) intensity threshold
          preCoins := preCoins
          futureCoins := future
          tape := z.2 }) := by
    funext z
    exact z.1.advance_source P intensity threshold basePending
      preCoins future z.2
  rw [heq]
  exact OriginConfiguration.measurable_advance_source_joint_of_parameters
    P basePending preCoins future _ _ hfirst hpre

end Kr25Ssmxt
