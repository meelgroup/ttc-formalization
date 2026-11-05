import Kr25Ssmxt.Analysis.ManuscriptSplicedSourcePointLaw

/-! A ghost configuration links the executable TTC state to the permanent
component source tapes through all processed components. -/

namespace Kr25Ssmxt

open Classical

structure ManuscriptOriginConfiguration (n : Nat) where
  state : TTCState n
  source : ManuscriptOriginSourceState n
  origin : Nat → Nat × Nat
  level : Nat
  rate : state.rate = 1 / (2 : NNReal) ^ level
  fresh : state.LabelsFresh
  history : ManuscriptOriginHistory state.nextLabel source.processed origin
  valid : ManuscriptOriginValid state origin source.valid
  marked : ManuscriptOriginMarked state origin source.marks
  survives : ManuscriptOriginSurvives state origin source.coins level
  complete : ManuscriptOriginComplete state origin source.valid
    source.coins level
  bound : ManuscriptValidBound source.valid source.processed

noncomputable def ManuscriptOriginConfiguration.initial (n : Nat) :
    ManuscriptOriginConfiguration n where
  state := TTCState.initial n
  source := ManuscriptOriginSourceState.initial
  origin := fun _ => (0, 0)
  level := 0
  rate := by simp [TTCState.initial]
  fresh := TTCState.initial_labelsFresh n
  history := manuscriptOriginHistory_initial _
  valid := manuscriptOriginValid_initial _
  marked := manuscriptOriginMarked_initial _ _
  survives := manuscriptOriginSurvives_initial _ _
  complete := manuscriptOriginComplete_initial _ _
  bound := manuscriptValidBound_initial

theorem ManuscriptOriginConfiguration.pointCounts_eq_source
    {n : Nat} (c : ManuscriptOriginConfiguration n)
    (S : Finset (LatticePoint n)) :
    c.state.pointCounts S = c.source.pointCounts c.level S := by
  exact manuscriptState_pointCounts_eq_originSource c.state c.origin
    c.source.valid c.source.marks c.source.coins c.level
    c.source.processed S c.fresh c.history c.valid c.marked
    c.survives c.complete

noncomputable def ManuscriptOriginConfiguration.advance
    {n : Nat} (c : ManuscriptOriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool)
    (tape : Nat → LatticePoint n) :
    ManuscriptOriginConfiguration n := by
  let deleted := c.state.removeComponent P
  let oldCoins := manuscriptSourceOldCoins c.origin c.source.coins c.level
  let rounds := manuscriptRateExit deleted intensity threshold
  let preRounds := c.level + rounds
  let pending := pendingAfter preCoins preRounds deleted.nextLabel basePending
  let activeCoins := originalSurvivorCoinRestriction preCoins preRounds
    deleted.nextLabel basePending future
  let first := manuscriptRateThinningResult deleted intensity threshold oldCoins
  let second := thinningResultSplitFinite first pending threshold
    (shiftCoins rounds oldCoins) activeCoins
  let activeRounds := firstExitRoundSplit first pending threshold
    (shiftCoins rounds oldCoins)
    (pendingCoinExtension deleted.nextLabel pending activeCoins)
  let index : Fin second.2 → Nat :=
    twoStageSurvivorLabel preCoins preRounds deleted.nextLabel basePending
      activeCoins activeRounds
  let points : Fin second.2 → LatticePoint n := fun i => tape (index i)
  let step : ManuscriptOriginSourceStep n :=
    { component := P
      firstLabel := c.state.nextLabel
      basePending := basePending
      preRounds := preRounds
      preCoins := preCoins
      futureCoins := future
      tape := tape }
  let nextOrigin := manuscriptOriginAppend c.origin c.source.processed
    second.1.nextLabel second.2 index
  let nextState := second.1.addBatch points
  let nextSource := c.source.step step
  have hnextRate : nextState.rate =
      1 / (2 : NNReal) ^ (preRounds + activeRounds) := by
    change (c.state.rate / (2 : NNReal) ^ rounds) /
      (2 : NNReal) ^ activeRounds =
      1 / (2 : NNReal) ^ (c.level + rounds + activeRounds)
    rw [c.rate]
    simp only [pow_add, div_eq_mul_inv, mul_inv_rev]
    ac_rfl
  have hdeletedFresh : deleted.LabelsFresh :=
    c.state.labelsFresh_removeComponent P c.fresh
  have hfirstFresh : first.LabelsFresh :=
    manuscriptRateThinningResult_labelsFresh deleted intensity threshold
      oldCoins hdeletedFresh
  have hsecondFresh : second.1.LabelsFresh :=
    thinningResultSplitFinite_labelsFresh first pending threshold
      (shiftCoins rounds oldCoins) activeCoins hfirstFresh
  have hnextFresh : nextState.LabelsFresh :=
    second.1.labelsFresh_addBatch points hsecondFresh
  have hsecondHistory : ManuscriptOriginHistory second.1.nextLabel
      c.source.processed c.origin := by
    change ManuscriptOriginHistory c.state.nextLabel
      c.source.processed c.origin
    exact c.history
  have hnextHistory : ManuscriptOriginHistory nextState.nextLabel
      nextSource.processed nextOrigin := by
    exact manuscriptOriginHistory_append c.origin c.source.processed
      second.1.nextLabel second.2 index
      (twoStageSurvivorLabel_injective preCoins preRounds
        deleted.nextLabel basePending activeCoins activeRounds)
      hsecondHistory
  have hdeletedMarked : ManuscriptOriginMarked deleted c.origin
      c.source.marks :=
    manuscriptOriginMarked_removeComponent c.state P c.origin
      c.source.marks c.marked
  have hfirstMarked : ManuscriptOriginMarked first c.origin
      c.source.marks :=
    manuscriptOriginMarked_rateThinningResult deleted c.origin
      c.source.marks hdeletedMarked intensity threshold oldCoins
  have hsecondMarked : ManuscriptOriginMarked second.1 c.origin
      c.source.marks :=
    manuscriptOriginMarked_splitThinningResult first c.origin
      c.source.marks hfirstMarked pending threshold
      (shiftCoins rounds oldCoins) activeCoins
  have hnextMarked : ManuscriptOriginMarked nextState nextOrigin
      nextSource.marks := by
    exact manuscriptOriginMarked_appendSource second.1 c.origin
      c.source.marks c.source.processed index tape hsecondFresh
      hsecondHistory hsecondMarked
  have hdeletedValid : ManuscriptOriginValid deleted c.origin
      c.source.valid :=
    manuscriptOriginValid_removeComponent c.state P c.origin
      c.source.valid c.valid
  have hfirstValid : ManuscriptOriginValid first c.origin
      c.source.valid :=
    manuscriptOriginValid_rateThinningResult deleted c.origin
      c.source.valid hdeletedValid intensity threshold oldCoins
  have hsecondValid : ManuscriptOriginValid second.1 c.origin
      c.source.valid :=
    manuscriptOriginValid_splitThinningResult first c.origin
      c.source.valid hfirstValid pending threshold
      (shiftCoins rounds oldCoins) activeCoins
  have hnextValid : ManuscriptOriginValid nextState nextOrigin
      nextSource.valid := by
    have hfiltered : ManuscriptOriginValid second.1 c.origin
        (c.source.valid.filter fun tag =>
          (c.source.marks tag).toPoint ∉ P.carrier) := by
      intro copy hcopy
      have hcopyFirst : copy ∈ first.samples := by
        have h := hcopy
        change copy ∈ samplesAfter (shiftCoins rounds oldCoins)
          activeRounds first.samples at h
        exact (Finset.mem_filter.mp h).1
      have hcopyDeleted : copy ∈ deleted.samples := by
        have h := hcopyFirst
        change copy ∈ samplesAfter oldCoins rounds deleted.samples at h
        exact (Finset.mem_filter.mp h).1
      apply Finset.mem_filter.mpr
      constructor
      · exact hsecondValid copy hcopy
      · have hout : copy.2.toPoint ∉ P.carrier :=
          (Finset.mem_filter.mp hcopyDeleted).2
        have hmark := hdeletedMarked copy hcopyDeleted
        rwa [hmark] at hout
    exact manuscriptOriginValid_appendSource second.1 c.origin
      (c.source.valid.filter fun tag =>
        (c.source.marks tag).toPoint ∉ P.carrier)
      (manuscriptSourceTags c.source.processed second.1.nextLabel
        basePending) c.source.processed index points hsecondFresh
      hfiltered (fun i => twoStageSurvivorLabel_mem_sourceTags
        c.source.processed preCoins preRounds deleted.nextLabel
        basePending activeCoins activeRounds i)
  have hnextSurvives : ManuscriptOriginSurvives nextState nextOrigin
      nextSource.coins (preRounds + activeRounds) := by
    have hdeletedSurvives : ManuscriptOriginSurvives deleted c.origin
        c.source.coins c.level :=
      manuscriptOriginSurvives_removeComponent c.state P c.origin
        c.source.coins c.level c.survives
    have hsecondSurvives : ManuscriptOriginSurvives second.1 c.origin
        c.source.coins (preRounds + activeRounds) := by
      exact manuscriptOriginSurvives_twoLoops deleted c.origin
        c.source.coins c.level intensity threshold pending activeCoins
        hdeletedSurvives
    exact manuscriptOriginSurvives_appendSource second.1 c.origin
      c.source.coins c.source.processed (preRounds + activeRounds)
      index points preCoins future preRounds hsecondFresh hsecondHistory
      hsecondSurvives (fun i =>
        twoStageSurvivorLabel_survives_splice preCoins future preRounds
          deleted.nextLabel basePending activeRounds i)
  have hnextComplete : ManuscriptOriginComplete nextState nextOrigin
      nextSource.valid nextSource.coins (preRounds + activeRounds) := by
    let filtered := c.source.valid.filter fun tag =>
      (c.source.marks tag).toPoint ∉ P.carrier
    have hdeletedComplete : ManuscriptOriginComplete deleted c.origin
        filtered c.source.coins c.level :=
      manuscriptOriginComplete_removeComponent c.state P c.origin
        c.source.marks c.source.valid c.source.coins c.level c.marked
        c.complete
    have hfirstComplete : ManuscriptOriginComplete first c.origin
        filtered c.source.coins preRounds := by
      exact manuscriptOriginComplete_thin_of_samples deleted first c.origin
        filtered c.source.coins c.level rounds rfl hdeletedComplete
    have hsecondComplete : ManuscriptOriginComplete second.1 c.origin
        filtered c.source.coins (preRounds + activeRounds) := by
      have hshift : shiftCoins rounds oldCoins =
          manuscriptSourceOldCoins c.origin c.source.coins preRounds :=
        shiftCoins_sourceOldCoins c.origin c.source.coins c.level rounds
      have hsamples : second.1.samples = samplesAfter
          (manuscriptSourceOldCoins c.origin c.source.coins preRounds)
          activeRounds first.samples := by
        rw [← hshift]
        rfl
      exact manuscriptOriginComplete_thin_of_samples first second.1
        c.origin filtered c.source.coins preRounds activeRounds hsamples
        hfirstComplete
    have hfilteredBound : ManuscriptValidBound filtered
        c.source.processed :=
      manuscriptValidBound_filter c.source.valid c.source.processed _ c.bound
    have hcover : ∀ k < basePending,
        Kr25Ssmxt.survives (spliceCoins preCoins future preRounds)
          (preRounds + activeRounds) (second.1.nextLabel + k) →
        ∃ i : Fin second.2, index i = second.1.nextLabel + k := by
      intro k hk hsurv
      exact exists_twoStageSurvivorLabel_of_survives_splice
        preCoins future preRounds deleted.nextLabel basePending
        activeRounds k hk hsurv
    exact manuscriptOriginComplete_appendSource second.1 c.origin
      filtered c.source.coins c.source.processed preCoins future
      preRounds basePending activeRounds index points hsecondFresh
      hfilteredBound hsecondComplete hcover
  have hnextBound : ManuscriptValidBound nextSource.valid
      nextSource.processed := c.source.step_validBound step c.bound
  exact { state := nextState
          source := nextSource
          origin := nextOrigin
          level := preRounds + activeRounds
          rate := hnextRate
          fresh := hnextFresh
          history := hnextHistory
          valid := hnextValid
          marked := hnextMarked
          survives := hnextSurvives
          complete := hnextComplete
          bound := hnextBound }

theorem ManuscriptOriginConfiguration.advance_source
    {n : Nat} (c : ManuscriptOriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool)
    (tape : Nat → LatticePoint n) :
    (c.advance P intensity threshold basePending preCoins future tape).source =
      c.source.step
        { component := P
          firstLabel := c.state.nextLabel
          basePending := basePending
          preRounds := c.level + manuscriptRateExit
            (c.state.removeComponent P) intensity threshold
          preCoins := preCoins
          futureCoins := future
          tape := tape } := rfl

theorem ManuscriptOriginConfiguration.advance_level
    {n : Nat} (c : ManuscriptOriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool)
    (tape : Nat → LatticePoint n) :
    (c.advance P intensity threshold basePending preCoins future tape).level =
      let deleted := c.state.removeComponent P
      let rounds := manuscriptRateExit deleted intensity threshold
      let preRounds := c.level + rounds
      let pending := pendingAfter preCoins preRounds deleted.nextLabel
        basePending
      let oldCoins := manuscriptSourceOldCoins c.origin c.source.coins c.level
      let activeCoins := originalSurvivorCoinRestriction preCoins preRounds
        deleted.nextLabel basePending future
      let first := manuscriptRateThinningResult deleted intensity threshold
        oldCoins
      preRounds + firstExitRoundSplit first pending threshold
        (shiftCoins rounds oldCoins)
        (pendingCoinExtension deleted.nextLabel pending activeCoins) := rfl

/-- The executable component transition has the exact fixed-level source
delete-and-append recurrence at its reached absolute level. -/
theorem ManuscriptOriginConfiguration.advance_pointCounts
    {n : Nat} (c : ManuscriptOriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool)
    (tape : Nat → LatticePoint n) (S : Finset (LatticePoint n)) :
    let next := c.advance P intensity threshold basePending preCoins future tape
    next.state.pointCounts S = fun x : S =>
      (if x.1.toPoint ∈ P.carrier then 0 else
        c.source.pointCounts next.level S x) +
      manuscriptPoissonTapePointCounts S c.state.nextLabel next.level
        (basePending,
          spliceCoins preCoins future
            (c.level + manuscriptRateExit (c.state.removeComponent P)
              intensity threshold), tape) x := by
  dsimp only
  let next := c.advance P intensity threshold basePending preCoins future tape
  have hcounts := next.pointCounts_eq_source S
  rw [hcounts, c.advance_source P intensity threshold basePending
    preCoins future tape]
  exact c.source.step_pointCounts
    { component := P
      firstLabel := c.state.nextLabel
      basePending := basePending
      preRounds := c.level + manuscriptRateExit
        (c.state.removeComponent P) intensity threshold
      preCoins := preCoins
      futureCoins := future
      tape := tape } next.level S c.bound

end Kr25Ssmxt
