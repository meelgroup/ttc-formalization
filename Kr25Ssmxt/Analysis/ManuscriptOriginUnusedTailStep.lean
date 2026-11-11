import Kr25Ssmxt.Analysis.ManuscriptSourceRefresh

/-! Exact relative-time unused source tails after one deterministic ghost
component transition. -/

namespace Kr25Ssmxt

theorem ManuscriptOriginConfiguration.advance_unusedTail_newComponent
    {n : Nat} (c : ManuscriptOriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool)
    (tape : Nat → LatticePoint n) (round label : Nat) :
    let preRounds := c.level + ttcPseudocode.firstLoopExit
      (c.state.removeComponent P) intensity threshold
    let next := c.advance P intensity threshold basePending preCoins future tape
    next.unusedTail (c.source.processed, (round, label)) =
      future (next.level - preRounds + round, label) := by
  let preRounds := c.level + ttcPseudocode.firstLoopExit
    (c.state.removeComponent P) intensity threshold
  let next := c.advance P intensity threshold basePending preCoins future tape
  change next.unusedTail (c.source.processed, (round, label)) =
    future (next.level - preRounds + round, label)
  have hlevel : preRounds ≤ next.level := by
    rw [c.advance_level]
    dsimp only [preRounds]
    omega
  have hnot : ¬ next.level + round < preRounds := by omega
  have hsub : next.level + round - preRounds =
      next.level - preRounds + round := by omega
  change (next.source.coins c.source.processed
      (next.level + round, label)) = _
  rw [c.advance_source]
  change (manuscriptCoinsAppend c.source.coins c.source.processed
      preCoins future preRounds c.source.processed)
      (next.level + round, label) = _
  rw [manuscriptCoinsAppend_new]
  simp [spliceCoins, hnot, hsub]

theorem ManuscriptOriginConfiguration.advance_unusedTail_otherComponent
    {n : Nat} (c : ManuscriptOriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool)
    (tape : Nat → LatticePoint n) (component round label : Nat)
    (hne : component ≠ c.source.processed) :
    let next := c.advance P intensity threshold basePending preCoins future tape
    next.unusedTail (component, (round, label)) =
      c.source.coins component (next.level + round, label) := by
  let next := c.advance P intensity threshold basePending preCoins future tape
  change next.unusedTail (component, (round, label)) =
    c.source.coins component (next.level + round, label)
  change next.source.coins component (next.level + round, label) = _
  rw [c.advance_source]
  change manuscriptCoinsAppend c.source.coins c.source.processed
      preCoins future
      (c.level + ttcPseudocode.firstLoopExit (c.state.removeComponent P)
        intensity threshold) component (next.level + round, label) = _
  simp [manuscriptCoinsAppend, hne]

theorem ManuscriptOriginConfiguration.refreshAdvance_unusedTail_otherComponent
    {n : Nat} (c : ManuscriptOriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool)
    (oldFuture : Nat × (Nat × Nat) → Bool)
    (tape : Nat → LatticePoint n) (component round label : Nat)
    (hne : component ≠ c.source.processed) :
    let refreshed := c.refreshFuture oldFuture
    let next := refreshed.advance P intensity threshold basePending
      preCoins future tape
    next.unusedTail (component, (round, label)) =
      oldFuture (component, (next.level - c.level + round, label)) := by
  let refreshed := c.refreshFuture oldFuture
  let next := refreshed.advance P intensity threshold basePending
    preCoins future tape
  change next.unusedTail (component, (round, label)) =
    oldFuture (component, (next.level - c.level + round, label))
  have hlevel : c.level ≤ next.level := by
    rw [refreshed.advance_level]
    change c.level ≤ c.level + ttcPseudocode.firstLoopExit
        (c.state.removeComponent P) intensity threshold + _
    omega
  have hne' : component ≠ refreshed.source.processed := hne
  rw [refreshed.advance_unusedTail_otherComponent P intensity threshold
    basePending preCoins future tape component round label hne']
  have hnot : ¬ next.level + round < c.level := by omega
  have hsub : next.level + round - c.level =
      next.level - c.level + round := by omega
  change manuscriptRefreshedSourceCoins c.source.coins c.level oldFuture
      component (next.level + round, label) = _
  simp [manuscriptRefreshedSourceCoins, spliceCoins, hnot, hsub]

/-- The entire unused source after a refreshed component step consists of
the shifted old global source on every other component and the shifted fresh
coin stream on the appended component. -/
theorem ManuscriptOriginConfiguration.refreshAdvance_unusedTail
    {n : Nat} (c : ManuscriptOriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool)
    (oldFuture : Nat × (Nat × Nat) → Bool)
    (tape : Nat → LatticePoint n) :
    let refreshed := c.refreshFuture oldFuture
    let next := refreshed.advance P intensity threshold basePending
      preCoins future tape
    let preRounds := c.level + ttcPseudocode.firstLoopExit
      (c.state.removeComponent P) intensity threshold
    next.unusedTail = fun index =>
      if index.1 = c.source.processed then
        future (next.level - preRounds + index.2.1, index.2.2)
      else
        oldFuture (index.1,
          (next.level - c.level + index.2.1, index.2.2)) := by
  let refreshed := c.refreshFuture oldFuture
  let next := refreshed.advance P intensity threshold basePending
    preCoins future tape
  let preRounds := c.level + ttcPseudocode.firstLoopExit
    (c.state.removeComponent P) intensity threshold
  change next.unusedTail = fun index =>
    if index.1 = c.source.processed then
      future (next.level - preRounds + index.2.1, index.2.2)
    else oldFuture (index.1,
      (next.level - c.level + index.2.1, index.2.2))
  funext index
  by_cases hnew : index.1 = c.source.processed
  · have hpoint := refreshed.advance_unusedTail_newComponent P intensity
      threshold basePending preCoins future tape index.2.1 index.2.2
    change next.unusedTail (c.source.processed,
        (index.2.1, index.2.2)) =
      future (next.level - preRounds + index.2.1, index.2.2) at hpoint
    have hindex : index = (c.source.processed, index.2) :=
      Prod.ext hnew rfl
    rw [hindex]
    simpa [hnew] using hpoint
  · have hpoint := c.refreshAdvance_unusedTail_otherComponent P intensity
      threshold basePending preCoins future oldFuture tape index.1
      index.2.1 index.2.2 hnew
    change next.unusedTail (index.1, (index.2.1, index.2.2)) =
      oldFuture (index.1,
        (next.level - c.level + index.2.1, index.2.2)) at hpoint
    simpa [hnew] using hpoint

end Kr25Ssmxt
