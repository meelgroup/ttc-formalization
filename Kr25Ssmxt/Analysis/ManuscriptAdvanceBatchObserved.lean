import Kr25Ssmxt.Analysis.ManuscriptAdvanceObserved

/-! Reconstruct the state after the second thinning loop and point-batch
append from its complete stopped source observation. -/

namespace Kr25Ssmxt

noncomputable def manuscriptObservedBatchState
    {n : Nat} (s : TTCState n) (threshold : Real)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat)
    (origin : Nat → Nat × Nat) (tape : Nat → LatticePoint n)
    (z : (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool)) :
    TTCState n := by
  let pending := pendingAfter preCoins preRounds s.nextLabel basePending
  let old := fun pair : Nat × Nat => z.1
    ((origin pair.2).1, (pair.1, (origin pair.2).2))
  let active := originalSurvivorCoinRestriction preCoins preRounds
    s.nextLabel basePending z.2
  let second := thinningResultSplitFinite s pending threshold old active
  let rounds := firstExitRoundSplit s pending threshold old
    (pendingCoinExtension s.nextLabel pending active)
  let index : Fin second.2 → Nat :=
    twoStageSurvivorLabel preCoins preRounds s.nextLabel basePending
      active rounds
  exact second.1.addBatch (fun i => tape (index i))

theorem manuscriptObservedBatchState_eq_of_fullObservation_eq
    {n : Nat} (s : TTCState n) (threshold : Real)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat)
    (origin : Nat → Nat × Nat) (tape : Nat → LatticePoint n)
    (a b : (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool))
    (hfresh : s.LabelsFresh)
    (hobs : manuscriptSurvivorPairFullObservation s threshold preCoins
        preRounds basePending origin a =
      manuscriptSurvivorPairFullObservation s threshold preCoins
        preRounds basePending origin b) :
    manuscriptObservedBatchState s threshold preCoins preRounds
        basePending origin tape a =
      manuscriptObservedBatchState s threshold preCoins preRounds
        basePending origin tape b := by
  let pending := pendingAfter preCoins preRounds s.nextLabel basePending
  let active := fun z : (Nat × (Nat × Nat) → Bool) ×
      (Nat × Nat → Bool) =>
    originalSurvivorCoinRestriction preCoins preRounds
      s.nextLabel basePending z.2
  let old := fun z : (Nat × (Nat × Nat) → Bool) ×
      (Nat × Nat → Bool) => fun pair : Nat × Nat => z.1
        ((origin pair.2).1, (pair.1, (origin pair.2).2))
  let second := fun z => thinningResultSplitFinite s pending threshold
    (old z) (active z)
  let rounds := fun z => firstExitRoundSplit s pending threshold
    (old z) (pendingCoinExtension s.nextLabel pending (active z))
  have hsecond : second a = second b :=
    thinningResultSplitFinite_eq_of_fullObservation_eq s threshold
      preCoins preRounds basePending origin a b hfresh hobs
  have hroundA : rounds a = manuscriptSurvivorPairStop s threshold
      preCoins preRounds basePending origin a :=
    firstExitRoundSplit_pairRead s threshold preCoins preRounds
      basePending origin a hfresh
  have hroundB : rounds b = manuscriptSurvivorPairStop s threshold
      preCoins preRounds basePending origin b :=
    firstExitRoundSplit_pairRead s threshold preCoins preRounds
      basePending origin b hfresh
  have hstop : manuscriptSurvivorPairStop s threshold preCoins
      preRounds basePending origin a =
      manuscriptSurvivorPairStop s threshold preCoins preRounds
        basePending origin b := congrArg Prod.fst hobs
  have hrounds : rounds a = rounds b := by
    rw [hroundA, hroundB]
    exact hstop
  have hfreshObs : coinPrefix (rounds a) a.2 =
      coinPrefix (rounds a) b.2 := by
    have h := congrArg (fun o => o.2.2) hobs
    change coinPrefix
        (manuscriptSurvivorPairStop s threshold preCoins preRounds
          basePending origin a) a.2 =
      coinPrefix
        (manuscriptSurvivorPairStop s threshold preCoins preRounds
          basePending origin b) b.2 at h
    rw [← hstop, ← hroundA] at h
    exact h
  have hcount : (second a).2 = (second b).2 :=
    congrArg Prod.snd hsecond
  have hcount' : pendingAfter
        (pendingCoinExtension s.nextLabel pending (active a))
        (rounds a) s.nextLabel pending =
      pendingAfter
        (pendingCoinExtension s.nextLabel pending (active b))
        (rounds a) s.nextLabel pending := by
    have h := hcount
    change pendingAfter
        (pendingCoinExtension s.nextLabel pending (active a))
        (rounds a) s.nextLabel pending =
      pendingAfter
        (pendingCoinExtension s.nextLabel pending (active b))
        (rounds b) s.nextLabel pending at h
    rw [← hrounds] at h
    exact h
  have hstate : (second a).1 = (second b).1 :=
    congrArg Prod.fst hsecond
  have hpoints (i : Fin (second a).2) :
      tape (twoStageSurvivorLabel preCoins preRounds s.nextLabel
          basePending (active a) (rounds a) i) =
      tape (twoStageSurvivorLabel preCoins preRounds s.nextLabel
          basePending (active b) (rounds b) (Fin.cast hcount i)) := by
    have hlabel := twoStageSurvivorLabel_eq_of_freshPrefix_eq
      preCoins preRounds s.nextLabel basePending (rounds a)
      a.2 b.2 hfreshObs hcount' i
    have htransport :
        twoStageSurvivorLabel preCoins preRounds s.nextLabel
            basePending (active b) (rounds a) (Fin.cast hcount' i) =
          twoStageSurvivorLabel preCoins preRounds s.nextLabel
            basePending (active b) (rounds b) (Fin.cast hcount i) := by
      have hcountB : pendingAfter
          (pendingCoinExtension s.nextLabel pending (active b))
          (rounds a) s.nextLabel pending =
        pendingAfter
          (pendingCoinExtension s.nextLabel pending (active b))
          (rounds b) s.nextLabel pending := by rw [hrounds]
      have htransport' := twoStageSurvivorLabel_round_congr
        preCoins preRounds s.nextLabel basePending
        (rounds a) (rounds b) (active b) hrounds hcountB
        (Fin.cast hcount' i)
      have hcast : Fin.cast hcountB (Fin.cast hcount' i) =
          Fin.cast hcount i := Fin.ext rfl
      rw [hcast] at htransport'
      exact htransport'
    exact (congrArg tape hlabel).trans (congrArg tape htransport)
  change (second a).1.addBatch
      (fun i => tape (twoStageSurvivorLabel preCoins preRounds
        s.nextLabel basePending (active a) (rounds a) i)) =
    (second b).1.addBatch
      (fun i => tape (twoStageSurvivorLabel preCoins preRounds
        s.nextLabel basePending (active b) (rounds b) i))
  exact TTCState.addBatch_eq_of_cast (second a).1 (second b).1
    hstate hcount _ _ hpoints

theorem ManuscriptOriginConfiguration.refreshed_advance_state_eq_observedBatch
    {n : Nat} (c : ManuscriptOriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins fresh : Nat × Nat → Bool)
    (oldFuture : Nat × (Nat × Nat) → Bool)
    (tape : Nat → LatticePoint n) :
    let deleted := c.state.removeComponent P
    let rounds := manuscriptRateExit deleted intensity threshold
    let preRounds := c.level + rounds
    let old := manuscriptSourceOldCoins c.origin
      (c.refreshFuture oldFuture).source.coins c.level
    let first := manuscriptRateThinningResult deleted intensity threshold old
    ((c.refreshFuture oldFuture).advance P intensity threshold
      basePending preCoins fresh tape).state =
    manuscriptObservedBatchState first threshold preCoins preRounds
      basePending c.origin tape
      (manuscriptGlobalSourceShift rounds oldFuture, fresh) := by
  let deleted := c.state.removeComponent P
  let rounds := manuscriptRateExit deleted intensity threshold
  let preRounds := c.level + rounds
  let old := manuscriptSourceOldCoins c.origin
    (c.refreshFuture oldFuture).source.coins c.level
  let first := manuscriptRateThinningResult deleted intensity threshold old
  have hshift : shiftCoins rounds old =
      (fun pair : Nat × Nat =>
        manuscriptGlobalSourceShift rounds oldFuture
          ((c.origin pair.2).1, (pair.1, (c.origin pair.2).2))) := by
    change shiftCoins rounds
      (manuscriptSourceOldCoins c.origin
        (c.refreshFuture oldFuture).source.coins c.level) = _
    rw [c.refreshFuture_shift_oldCoins oldFuture rounds]
    funext pair
    simp [manuscriptGlobalSourceShift, Nat.add_comm]
  dsimp only
  unfold manuscriptObservedBatchState
  dsimp only [ManuscriptOriginConfiguration.advance]
  rw [show (c.refreshFuture oldFuture).state = c.state from rfl,
    show (c.refreshFuture oldFuture).origin = c.origin from rfl,
    show (c.refreshFuture oldFuture).level = c.level from rfl]
  rw [hshift]
  rfl

end Kr25Ssmxt
