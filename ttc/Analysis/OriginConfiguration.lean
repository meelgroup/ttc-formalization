import ttc.Analysis.SplicedSourcePointLaw

/-! A ghost configuration links the executable TTC state to the permanent
component source tapes through all processed components. -/

namespace ttc

open Classical

structure OriginConfiguration (n : Nat) where
  state : TTCState n
  source : OriginSourceState n
  origin : Nat → Nat × Nat
  level : Nat
  p : state.p = 1 / (2 : NNReal) ^ level
  fresh : state.LabelsFresh
  history : OriginHistory state.nextLabel source.processed origin
  valid : OriginValid state origin source.valid
  marked : OriginMarked state origin source.marks
  survives : OriginSurvives state origin source.coins level
  complete : OriginComplete state origin source.valid
    source.coins level
  bound : ValidBound source.valid source.processed

noncomputable def OriginConfiguration.initial (n : Nat) :
    OriginConfiguration n where
  state := TTCState.unitInitial n
  source := OriginSourceState.initial
  origin := fun _ => (0, 0)
  level := 0
  p := by simp [TTCState.unitInitial]
  fresh := TTCState.initial_labelsFresh n
  history := originHistory_initial _
  valid := originValid_initial _
  marked := originMarked_initial _ _
  survives := originSurvives_initial _ _
  complete := originComplete_initial _ _
  bound := validBound_initial

theorem OriginConfiguration.pointCounts_eq_source
    {n : Nat} (c : OriginConfiguration n)
    (S : Finset (LatticePoint n)) :
    c.state.pointCounts S = c.source.pointCounts c.level S := by
  exact state_pointCounts_eq_originSource c.state c.origin
    c.source.valid c.source.marks c.source.coins c.level
    c.source.processed S c.fresh c.history c.valid c.marked
    c.survives c.complete

noncomputable def OriginConfiguration.advance
    {n : Nat} (c : OriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool)
    (tape : Nat → LatticePoint n) :
    OriginConfiguration n := by
  let deleted := c.state.removeComponent P
  let oldCoins := sourceOldCoins c.origin c.source.coins c.level
  let rounds := ttcReference.firstLoopExit deleted intensity threshold
  let preRounds := c.level + rounds
  let pending := pendingAfter preCoins preRounds deleted.nextLabel basePending
  let activeCoins := originalSurvivorCoinRestriction preCoins preRounds
    deleted.nextLabel basePending future
  let first := ttcReference.firstLoopResult deleted intensity threshold oldCoins
  let second := thinningResultSplitFinite first pending threshold
    (shiftCoins rounds oldCoins) activeCoins
  let activeRounds := firstExitRoundSplit first pending threshold
    (shiftCoins rounds oldCoins)
    (pendingCoinExtension deleted.nextLabel pending activeCoins)
  let index : Fin second.2 → Nat :=
    twoStageSurvivorLabel preCoins preRounds deleted.nextLabel basePending
      activeCoins activeRounds
  let points : Fin second.2 → LatticePoint n := fun i => tape (index i)
  let step : OriginSourceStep n :=
    { component := P
      firstLabel := c.state.nextLabel
      basePending := basePending
      preRounds := preRounds
      preCoins := preCoins
      futureCoins := future
      tape := tape }
  let nextOrigin := originAppend c.origin c.source.processed
    second.1.nextLabel second.2 index
  let nextState := second.1.addBatch points
  let nextSource := c.source.step step
  have hnextRate : nextState.p =
      1 / (2 : NNReal) ^ (preRounds + activeRounds) := by
    change (c.state.p / (2 : NNReal) ^ rounds) /
      (2 : NNReal) ^ activeRounds =
      1 / (2 : NNReal) ^ (c.level + rounds + activeRounds)
    rw [c.p]
    simp only [pow_add, div_eq_mul_inv, mul_inv_rev]
    ac_rfl
  have hdeletedFresh : deleted.LabelsFresh :=
    c.state.labelsFresh_removeComponent P c.fresh
  have hfirstFresh : first.LabelsFresh :=
    rateThinningResult_labelsFresh deleted intensity threshold
      oldCoins hdeletedFresh
  have hsecondFresh : second.1.LabelsFresh :=
    thinningResultSplitFinite_labelsFresh first pending threshold
      (shiftCoins rounds oldCoins) activeCoins hfirstFresh
  have hnextFresh : nextState.LabelsFresh :=
    second.1.labelsFresh_addBatch points hsecondFresh
  have hsecondHistory : OriginHistory second.1.nextLabel
      c.source.processed c.origin := by
    change OriginHistory c.state.nextLabel
      c.source.processed c.origin
    exact c.history
  have hnextHistory : OriginHistory nextState.nextLabel
      nextSource.processed nextOrigin := by
    exact originHistory_append c.origin c.source.processed
      second.1.nextLabel second.2 index
      (twoStageSurvivorLabel_injective preCoins preRounds
        deleted.nextLabel basePending activeCoins activeRounds)
      hsecondHistory
  have hdeletedMarked : OriginMarked deleted c.origin
      c.source.marks :=
    originMarked_removeComponent c.state P c.origin
      c.source.marks c.marked
  have hfirstMarked : OriginMarked first c.origin
      c.source.marks :=
    originMarked_rateThinningResult deleted c.origin
      c.source.marks hdeletedMarked intensity threshold oldCoins
  have hsecondMarked : OriginMarked second.1 c.origin
      c.source.marks :=
    originMarked_splitThinningResult first c.origin
      c.source.marks hfirstMarked pending threshold
      (shiftCoins rounds oldCoins) activeCoins
  have hnextMarked : OriginMarked nextState nextOrigin
      nextSource.marks := by
    exact originMarked_appendSource second.1 c.origin
      c.source.marks c.source.processed index tape hsecondFresh
      hsecondHistory hsecondMarked
  have hdeletedValid : OriginValid deleted c.origin
      c.source.valid :=
    originValid_removeComponent c.state P c.origin
      c.source.valid c.valid
  have hfirstValid : OriginValid first c.origin
      c.source.valid :=
    originValid_rateThinningResult deleted c.origin
      c.source.valid hdeletedValid intensity threshold oldCoins
  have hsecondValid : OriginValid second.1 c.origin
      c.source.valid :=
    originValid_splitThinningResult first c.origin
      c.source.valid hfirstValid pending threshold
      (shiftCoins rounds oldCoins) activeCoins
  have hnextValid : OriginValid nextState nextOrigin
      nextSource.valid := by
    have hfiltered : OriginValid second.1 c.origin
        (c.source.valid.filter fun tag =>
          (c.source.marks tag).toPoint ∉ P.carrier) := by
      intro copy hcopy
      have hcopyFirst : copy ∈ first.X := by
        have h := hcopy
        change copy ∈ samplesAfter (shiftCoins rounds oldCoins)
          activeRounds first.X at h
        exact (Finset.mem_filter.mp h).1
      have hcopyDeleted : copy ∈ deleted.X := by
        have h := hcopyFirst
        change copy ∈ samplesAfter oldCoins rounds deleted.X at h
        exact (Finset.mem_filter.mp h).1
      apply Finset.mem_filter.mpr
      constructor
      · exact hsecondValid copy hcopy
      · have hout : copy.2.toPoint ∉ P.carrier :=
          (Finset.mem_filter.mp hcopyDeleted).2
        have hmark := hdeletedMarked copy hcopyDeleted
        rwa [hmark] at hout
    exact originValid_appendSource second.1 c.origin
      (c.source.valid.filter fun tag =>
        (c.source.marks tag).toPoint ∉ P.carrier)
      (originSourceTags c.source.processed second.1.nextLabel
        basePending) c.source.processed index points hsecondFresh
      hfiltered (fun i => twoStageSurvivorLabel_mem_sourceTags
        c.source.processed preCoins preRounds deleted.nextLabel
        basePending activeCoins activeRounds i)
  have hnextSurvives : OriginSurvives nextState nextOrigin
      nextSource.coins (preRounds + activeRounds) := by
    have hdeletedSurvives : OriginSurvives deleted c.origin
        c.source.coins c.level :=
      originSurvives_removeComponent c.state P c.origin
        c.source.coins c.level c.survives
    have hsecondSurvives : OriginSurvives second.1 c.origin
        c.source.coins (preRounds + activeRounds) := by
      exact originSurvives_twoLoops deleted c.origin
        c.source.coins c.level intensity threshold pending activeCoins
        hdeletedSurvives
    exact originSurvives_appendSource second.1 c.origin
      c.source.coins c.source.processed (preRounds + activeRounds)
      index points preCoins future preRounds hsecondFresh hsecondHistory
      hsecondSurvives (fun i =>
        twoStageSurvivorLabel_survives_splice preCoins future preRounds
          deleted.nextLabel basePending activeRounds i)
  have hnextComplete : OriginComplete nextState nextOrigin
      nextSource.valid nextSource.coins (preRounds + activeRounds) := by
    let filtered := c.source.valid.filter fun tag =>
      (c.source.marks tag).toPoint ∉ P.carrier
    have hdeletedComplete : OriginComplete deleted c.origin
        filtered c.source.coins c.level :=
      originComplete_removeComponent c.state P c.origin
        c.source.marks c.source.valid c.source.coins c.level c.marked
        c.complete
    have hfirstComplete : OriginComplete first c.origin
        filtered c.source.coins preRounds := by
      exact originComplete_thin_of_samples deleted first c.origin
        filtered c.source.coins c.level rounds rfl hdeletedComplete
    have hsecondComplete : OriginComplete second.1 c.origin
        filtered c.source.coins (preRounds + activeRounds) := by
      have hshift : shiftCoins rounds oldCoins =
          sourceOldCoins c.origin c.source.coins preRounds :=
        shiftCoins_sourceOldCoins c.origin c.source.coins c.level rounds
      have hsamples : second.1.X = samplesAfter
          (sourceOldCoins c.origin c.source.coins preRounds)
          activeRounds first.X := by
        rw [← hshift]
        rfl
      exact originComplete_thin_of_samples first second.1
        c.origin filtered c.source.coins preRounds activeRounds hsamples
        hfirstComplete
    have hfilteredBound : ValidBound filtered
        c.source.processed :=
      validBound_filter c.source.valid c.source.processed _ c.bound
    have hcover : ∀ k < basePending,
        ttc.survives (spliceCoins preCoins future preRounds)
          (preRounds + activeRounds) (second.1.nextLabel + k) →
        ∃ i : Fin second.2, index i = second.1.nextLabel + k := by
      intro k hk hsurv
      exact exists_twoStageSurvivorLabel_of_survives_splice
        preCoins future preRounds deleted.nextLabel basePending
        activeRounds k hk hsurv
    exact originComplete_appendSource second.1 c.origin
      filtered c.source.coins c.source.processed preCoins future
      preRounds basePending activeRounds index points hsecondFresh
      hfilteredBound hsecondComplete hcover
  have hnextBound : ValidBound nextSource.valid
      nextSource.processed := c.source.step_validBound step c.bound
  exact { state := nextState
          source := nextSource
          origin := nextOrigin
          level := preRounds + activeRounds
          p := hnextRate
          fresh := hnextFresh
          history := hnextHistory
          valid := hnextValid
          marked := hnextMarked
          survives := hnextSurvives
          complete := hnextComplete
          bound := hnextBound }

theorem OriginConfiguration.advance_source
    {n : Nat} (c : OriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool)
    (tape : Nat → LatticePoint n) :
    (c.advance P intensity threshold basePending preCoins future tape).source =
      c.source.step
        { component := P
          firstLabel := c.state.nextLabel
          basePending := basePending
          preRounds := c.level + ttcReference.firstLoopExit
            (c.state.removeComponent P) intensity threshold
          preCoins := preCoins
          futureCoins := future
          tape := tape } := rfl

theorem OriginConfiguration.advance_level
    {n : Nat} (c : OriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool)
    (tape : Nat → LatticePoint n) :
    (c.advance P intensity threshold basePending preCoins future tape).level =
      let deleted := c.state.removeComponent P
      let rounds := ttcReference.firstLoopExit deleted intensity threshold
      let preRounds := c.level + rounds
      let pending := pendingAfter preCoins preRounds deleted.nextLabel
        basePending
      let oldCoins := sourceOldCoins c.origin c.source.coins c.level
      let activeCoins := originalSurvivorCoinRestriction preCoins preRounds
        deleted.nextLabel basePending future
      let first := ttcReference.firstLoopResult deleted intensity threshold
        oldCoins
      preRounds + firstExitRoundSplit first pending threshold
        (shiftCoins rounds oldCoins)
        (pendingCoinExtension deleted.nextLabel pending activeCoins) := rfl

/-- The executable component transition has the exact fixed-level source
delete-and-append recurrence at its reached absolute level. -/
theorem OriginConfiguration.advance_pointCounts
    {n : Nat} (c : OriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool)
    (tape : Nat → LatticePoint n) (S : Finset (LatticePoint n)) :
    let next := c.advance P intensity threshold basePending preCoins future tape
    next.state.pointCounts S = fun x : S =>
      (if x.1.toPoint ∈ P.carrier then 0 else
        c.source.pointCounts next.level S x) +
      poissonTapePointCounts S c.state.nextLabel next.level
        (basePending,
          spliceCoins preCoins future
            (c.level + ttcReference.firstLoopExit (c.state.removeComponent P)
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
      preRounds := c.level + ttcReference.firstLoopExit
        (c.state.removeComponent P) intensity threshold
      preCoins := preCoins
      futureCoins := future
      tape := tape } next.level S c.bound

end ttc
