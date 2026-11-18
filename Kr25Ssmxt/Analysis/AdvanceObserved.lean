import Kr25Ssmxt.Analysis.SurvivorFullPrefixTail
import Kr25Ssmxt.Analysis.FirstLoopObservation
import Kr25Ssmxt.Analysis.OriginJointSourceBridge

/-! Pathwise bridges from the global fair source observations to the
rate-thinning and count-thinning operations in `advance`. -/

namespace Kr25Ssmxt

theorem coinsAppend_refreshed_observedPrefix_eq_of_twoPieces
    (sources : Nat → Nat × Nat → Bool)
    (level component rounds activeRounds : Nat)
    (preCoins freshA freshB : Nat × Nat → Bool)
    (oldA oldB : Nat × (Nat × Nat) → Bool)
    (hfirst : globalSourcePrefix rounds oldA =
      globalSourcePrefix rounds oldB)
    (hsecond : globalSourcePrefix activeRounds
        (globalSourceShift rounds oldA) =
      globalSourcePrefix activeRounds
        (globalSourceShift rounds oldB))
    (hfresh : coinPrefix activeRounds freshA =
      coinPrefix activeRounds freshB) :
    originCoinPrefix (level + rounds + activeRounds)
      (coinsAppend
        (refreshedSourceCoins sources level oldA)
        component preCoins freshA (level + rounds)) =
    originCoinPrefix (level + rounds + activeRounds)
      (coinsAppend
        (refreshedSourceCoins sources level oldB)
        component preCoins freshB (level + rounds)) := by
  have hglobal : globalSourcePrefix (rounds + activeRounds) oldA =
      globalSourcePrefix (rounds + activeRounds) oldB :=
    globalSourcePrefix_add_eq_of_pieces oldA oldB rounds
      activeRounds hfirst hsecond
  have hold := refreshedSourceCoins_observedPrefix_eq_of_futurePrefix
    sources level (rounds + activeRounds) oldA oldB hglobal
  have happend := coinsAppend_observedPrefix_eq_of_prefix_eq
    (refreshedSourceCoins sources level oldA)
    (refreshedSourceCoins sources level oldB)
    component (level + rounds) activeRounds preCoins freshA freshB
    (by simpa only [Nat.add_assoc] using hold) hfresh
  exact happend

theorem twoStageSurvivorLabel_eq_of_freshPrefix_eq
    (preCoins : Nat × Nat → Bool)
    (preRounds firstLabel basePending rounds : Nat)
    (freshA freshB : Nat × Nat → Bool)
    (hfresh : coinPrefix rounds freshA = coinPrefix rounds freshB)
    (hcount :
      pendingAfter
        (pendingCoinExtension firstLabel
          (pendingAfter preCoins preRounds firstLabel basePending)
          (originalSurvivorCoinRestriction preCoins preRounds
            firstLabel basePending freshA))
        rounds firstLabel
        (pendingAfter preCoins preRounds firstLabel basePending) =
      pendingAfter
        (pendingCoinExtension firstLabel
          (pendingAfter preCoins preRounds firstLabel basePending)
          (originalSurvivorCoinRestriction preCoins preRounds
            firstLabel basePending freshB))
        rounds firstLabel
        (pendingAfter preCoins preRounds firstLabel basePending))
    (i : Fin (pendingAfter
      (pendingCoinExtension firstLabel
        (pendingAfter preCoins preRounds firstLabel basePending)
        (originalSurvivorCoinRestriction preCoins preRounds
          firstLabel basePending freshA))
      rounds firstLabel
      (pendingAfter preCoins preRounds firstLabel basePending))) :
    twoStageSurvivorLabel preCoins preRounds firstLabel basePending
      (originalSurvivorCoinRestriction preCoins preRounds
        firstLabel basePending freshA) rounds i =
    twoStageSurvivorLabel preCoins preRounds firstLabel basePending
      (originalSurvivorCoinRestriction preCoins preRounds
        firstLabel basePending freshB) rounds (Fin.cast hcount i) := by
  have hactive := originalSurvivorExtension_prefix_eq_of_futurePrefix
    preCoins preRounds firstLabel basePending rounds freshA freshB hfresh
  have hlabel := twoStageSurvivorLabel_eq_of_active_prefix_eq
    preCoins preRounds firstLabel basePending
    (originalSurvivorCoinRestriction preCoins preRounds
      firstLabel basePending freshA)
    (originalSurvivorCoinRestriction preCoins preRounds
      firstLabel basePending freshB) rounds hactive i
  simpa only [Fin.cast, Fin.val_mk] using hlabel

theorem twoStageSurvivorLabel_round_congr
    (preCoins : Nat × Nat → Bool)
    (preRounds firstLabel basePending rounds rounds' : Nat)
    (active : Nat × Fin
      (pendingAfter preCoins preRounds firstLabel basePending) → Bool)
    (hrounds : rounds = rounds')
    (hcount : pendingAfter
        (pendingCoinExtension firstLabel
          (pendingAfter preCoins preRounds firstLabel basePending) active)
        rounds firstLabel
        (pendingAfter preCoins preRounds firstLabel basePending) =
      pendingAfter
        (pendingCoinExtension firstLabel
          (pendingAfter preCoins preRounds firstLabel basePending) active)
        rounds' firstLabel
        (pendingAfter preCoins preRounds firstLabel basePending))
    (i : Fin (pendingAfter
      (pendingCoinExtension firstLabel
        (pendingAfter preCoins preRounds firstLabel basePending) active)
      rounds firstLabel
      (pendingAfter preCoins preRounds firstLabel basePending))) :
    twoStageSurvivorLabel preCoins preRounds firstLabel basePending
        active rounds i =
      twoStageSurvivorLabel preCoins preRounds firstLabel basePending
        active rounds' (Fin.cast hcount i) := by
  cases hrounds
  have hcast : Fin.cast hcount i = i := Fin.ext rfl
  rw [hcast]

theorem TTCState.addBatch_eq_of_cast
    {n countA countB : Nat} (sA sB : TTCState n)
    (hstate : sA = sB) (hcount : countA = countB)
    (pointsA : Fin countA → LatticePoint n)
    (pointsB : Fin countB → LatticePoint n)
    (hpoints : ∀ i, pointsA i = pointsB (Fin.cast hcount i)) :
    sA.addBatch pointsA = sB.addBatch pointsB := by
  cases hstate
  cases hcount
  have heq : pointsA = pointsB := by
    funext i
    simpa using hpoints i
  rw [heq]

theorem OriginConfiguration.refreshed_rateThinningResult_eq_of_prefix_eq
    {n : Nat} (c : OriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (a b : Nat × (Nat × Nat) → Bool)
    (hprefix : globalSourcePrefix
        (ttcReference.firstLoopExit (c.state.removeComponent P)
          intensity threshold) a =
      globalSourcePrefix
        (ttcReference.firstLoopExit (c.state.removeComponent P)
          intensity threshold) b) :
    ttcReference.firstLoopResult (c.state.removeComponent P)
      intensity threshold
      (sourceOldCoins c.origin
        (c.refreshFuture a).source.coins c.level) =
    ttcReference.firstLoopResult (c.state.removeComponent P)
      intensity threshold
      (sourceOldCoins c.origin
        (c.refreshFuture b).source.coins c.level) := by
  let rounds := ttcReference.firstLoopExit (c.state.removeComponent P)
    intensity threshold
  have ha := c.refreshFuture_oldCoins a
  have hb := c.refreshFuture_oldCoins b
  change sourceOldCoins c.origin
      (c.refreshFuture a).source.coins c.level =
      (fun pair => a ((c.origin pair.2).1,
        (pair.1, (c.origin pair.2).2))) at ha
  change sourceOldCoins c.origin
      (c.refreshFuture b).source.coins c.level =
      (fun pair => b ((c.origin pair.2).1,
        (pair.1, (c.origin pair.2).2))) at hb
  have hread : coinPrefix rounds
      (fun pair : Nat × Nat => a
        ((c.origin pair.2).1, (pair.1, (c.origin pair.2).2))) =
    coinPrefix rounds
      (fun pair : Nat × Nat => b
        ((c.origin pair.2).1, (pair.1, (c.origin pair.2).2))) := by
    calc
      _ = coinPrefix rounds
          (fun pair : Nat × Nat =>
            globalSourcePrefix rounds a
              ((c.origin pair.2).1,
                (pair.1, (c.origin pair.2).2))) :=
            oldRead_globalPrefix c.origin rounds a
      _ = coinPrefix rounds
          (fun pair : Nat × Nat =>
            globalSourcePrefix rounds b
              ((c.origin pair.2).1,
                (pair.1, (c.origin pair.2).2))) := by rw [hprefix]
      _ = _ := (oldRead_globalPrefix c.origin rounds b).symm
  apply rateThinningResult_eq_of_prefix_eq
  rw [ha, hb]
  exact hread

theorem OriginConfiguration.refreshed_secondResult_eq_of_observations
    {n : Nat} (c : OriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins freshA freshB : Nat × Nat → Bool)
    (oldA oldB : Nat × (Nat × Nat) → Bool)
    (hfirst : globalSourcePrefix
        (ttcReference.firstLoopExit (c.state.removeComponent P)
          intensity threshold) oldA =
      globalSourcePrefix
        (ttcReference.firstLoopExit (c.state.removeComponent P)
          intensity threshold) oldB)
    (hsecond :
      let deleted := c.state.removeComponent P
      let rounds := ttcReference.firstLoopExit deleted intensity threshold
      let first := ttcReference.firstLoopResult deleted intensity threshold
        (sourceOldCoins c.origin
          (c.refreshFuture oldA).source.coins c.level)
      let preRounds := c.level + rounds
      survivorPairFullObservation first threshold preCoins
          preRounds basePending c.origin
          (globalSourceShift rounds oldA, freshA) =
        survivorPairFullObservation first threshold preCoins
          preRounds basePending c.origin
          (globalSourceShift rounds oldB, freshB)) :
    let deleted := c.state.removeComponent P
    let rounds := ttcReference.firstLoopExit deleted intensity threshold
    let preRounds := c.level + rounds
    let pending := pendingAfter preCoins preRounds deleted.nextLabel basePending
    let active := fun fresh => originalSurvivorCoinRestriction preCoins
      preRounds deleted.nextLabel basePending fresh
    let old := fun global => sourceOldCoins c.origin
      (c.refreshFuture global).source.coins c.level
    thinningResultSplitFinite
      (ttcReference.firstLoopResult deleted intensity threshold (old oldA))
      pending threshold (shiftCoins rounds (old oldA)) (active freshA) =
    thinningResultSplitFinite
      (ttcReference.firstLoopResult deleted intensity threshold (old oldB))
      pending threshold (shiftCoins rounds (old oldB)) (active freshB) := by
  let deleted := c.state.removeComponent P
  let rounds := ttcReference.firstLoopExit deleted intensity threshold
  let preRounds := c.level + rounds
  let old := fun global => sourceOldCoins c.origin
    (c.refreshFuture global).source.coins c.level
  let firstA := ttcReference.firstLoopResult deleted intensity threshold
    (old oldA)
  let firstB := ttcReference.firstLoopResult deleted intensity threshold
    (old oldB)
  have hfirstState : firstA = firstB :=
    c.refreshed_rateThinningResult_eq_of_prefix_eq P intensity threshold
      oldA oldB hfirst
  have hshiftA : shiftCoins rounds (old oldA) =
      (fun pair : Nat × Nat =>
        globalSourceShift rounds oldA
          ((c.origin pair.2).1, (pair.1, (c.origin pair.2).2))) := by
    change shiftCoins rounds
      (sourceOldCoins c.origin
        (c.refreshFuture oldA).source.coins c.level) = _
    rw [c.refreshFuture_shift_oldCoins oldA rounds]
    funext pair
    simp [globalSourceShift, Nat.add_comm]
  have hshiftB : shiftCoins rounds (old oldB) =
      (fun pair : Nat × Nat =>
        globalSourceShift rounds oldB
          ((c.origin pair.2).1, (pair.1, (c.origin pair.2).2))) := by
    change shiftCoins rounds
      (sourceOldCoins c.origin
        (c.refreshFuture oldB).source.coins c.level) = _
    rw [c.refreshFuture_shift_oldCoins oldB rounds]
    funext pair
    simp [globalSourceShift, Nat.add_comm]
  have hfirstFresh : firstA.LabelsFresh := by
    exact rateThinningResult_labelsFresh deleted intensity
      threshold (old oldA)
        (c.state.labelsFresh_removeComponent P c.fresh)
  have hpair :=
    thinningResultSplitFinite_eq_of_fullObservation_eq firstA threshold
      preCoins preRounds basePending c.origin
      (globalSourceShift rounds oldA, freshA)
      (globalSourceShift rounds oldB, freshB)
      hfirstFresh hsecond
  change thinningResultSplitFinite firstA
      (pendingAfter preCoins preRounds deleted.nextLabel basePending)
      threshold (shiftCoins rounds (old oldA))
      (originalSurvivorCoinRestriction preCoins preRounds
        deleted.nextLabel basePending freshA) =
    thinningResultSplitFinite firstB
      (pendingAfter preCoins preRounds deleted.nextLabel basePending)
      threshold (shiftCoins rounds (old oldB))
      (originalSurvivorCoinRestriction preCoins preRounds
        deleted.nextLabel basePending freshB)
  rw [← hfirstState, hshiftA, hshiftB]
  exact hpair

theorem OriginConfiguration.refreshed_activeRounds_eq_pairStop
    {n : Nat} (c : OriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins fresh : Nat × Nat → Bool)
    (oldFuture : Nat × (Nat × Nat) → Bool) :
    let deleted := c.state.removeComponent P
    let rounds := ttcReference.firstLoopExit deleted intensity threshold
    let preRounds := c.level + rounds
    let old := sourceOldCoins c.origin
      (c.refreshFuture oldFuture).source.coins c.level
    let first := ttcReference.firstLoopResult deleted intensity threshold old
    let pending := pendingAfter preCoins preRounds deleted.nextLabel basePending
    let active := originalSurvivorCoinRestriction preCoins preRounds
      deleted.nextLabel basePending fresh
    firstExitRoundSplit first pending threshold (shiftCoins rounds old)
        (pendingCoinExtension deleted.nextLabel pending active) =
      survivorPairStop first threshold preCoins preRounds
        basePending c.origin
        (globalSourceShift rounds oldFuture, fresh) := by
  let deleted := c.state.removeComponent P
  let rounds := ttcReference.firstLoopExit deleted intensity threshold
  let preRounds := c.level + rounds
  let old := sourceOldCoins c.origin
    (c.refreshFuture oldFuture).source.coins c.level
  let first := ttcReference.firstLoopResult deleted intensity threshold old
  have hshift : shiftCoins rounds old =
      (fun pair : Nat × Nat =>
        globalSourceShift rounds oldFuture
          ((c.origin pair.2).1, (pair.1, (c.origin pair.2).2))) := by
    change shiftCoins rounds
      (sourceOldCoins c.origin
        (c.refreshFuture oldFuture).source.coins c.level) = _
    rw [c.refreshFuture_shift_oldCoins oldFuture rounds]
    funext pair
    simp [globalSourceShift, Nat.add_comm]
  have hfresh : first.LabelsFresh :=
    rateThinningResult_labelsFresh deleted intensity threshold old
      (c.state.labelsFresh_removeComponent P c.fresh)
  change firstExitRoundSplit first
      (pendingAfter preCoins preRounds deleted.nextLabel basePending)
      threshold (shiftCoins rounds old)
      (pendingCoinExtension deleted.nextLabel
        (pendingAfter preCoins preRounds deleted.nextLabel basePending)
        (originalSurvivorCoinRestriction preCoins preRounds
          deleted.nextLabel basePending fresh)) = _
  rw [hshift]
  exact firstExitRoundSplit_pairRead first threshold preCoins preRounds
    basePending c.origin
    (globalSourceShift rounds oldFuture, fresh) hfresh

theorem OriginConfiguration.refreshed_advance_level_eq_of_observations
    {n : Nat} (c : OriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins freshA freshB : Nat × Nat → Bool)
    (oldA oldB : Nat × (Nat × Nat) → Bool)
    (tape : Nat → LatticePoint n)
    (hfirst : globalSourcePrefix
        (ttcReference.firstLoopExit (c.state.removeComponent P)
          intensity threshold) oldA =
      globalSourcePrefix
        (ttcReference.firstLoopExit (c.state.removeComponent P)
          intensity threshold) oldB)
    (hsecond :
      let deleted := c.state.removeComponent P
      let rounds := ttcReference.firstLoopExit deleted intensity threshold
      let first := ttcReference.firstLoopResult deleted intensity threshold
        (sourceOldCoins c.origin
          (c.refreshFuture oldA).source.coins c.level)
      let preRounds := c.level + rounds
      survivorPairFullObservation first threshold preCoins
          preRounds basePending c.origin
          (globalSourceShift rounds oldA, freshA) =
        survivorPairFullObservation first threshold preCoins
          preRounds basePending c.origin
          (globalSourceShift rounds oldB, freshB)) :
    ((c.refreshFuture oldA).advance P intensity threshold basePending
      preCoins freshA tape).level =
    ((c.refreshFuture oldB).advance P intensity threshold basePending
      preCoins freshB tape).level := by
  let deleted := c.state.removeComponent P
  let rounds := ttcReference.firstLoopExit deleted intensity threshold
  let preRounds := c.level + rounds
  let old := fun global => sourceOldCoins c.origin
    (c.refreshFuture global).source.coins c.level
  let firstA := ttcReference.firstLoopResult deleted intensity threshold
    (old oldA)
  let firstB := ttcReference.firstLoopResult deleted intensity threshold
    (old oldB)
  let pending := pendingAfter preCoins preRounds deleted.nextLabel basePending
  let active := fun fresh => originalSurvivorCoinRestriction preCoins
    preRounds deleted.nextLabel basePending fresh
  have hfirstState : firstA = firstB :=
    c.refreshed_rateThinningResult_eq_of_prefix_eq P intensity threshold
      oldA oldB hfirst
  have hstopA := c.refreshed_activeRounds_eq_pairStop P intensity
    threshold basePending preCoins freshA oldA
  have hstopB := c.refreshed_activeRounds_eq_pairStop P intensity
    threshold basePending preCoins freshB oldB
  change firstExitRoundSplit firstA pending threshold
      (shiftCoins rounds (old oldA))
      (pendingCoinExtension deleted.nextLabel pending (active freshA)) =
    survivorPairStop firstA threshold preCoins preRounds
      basePending c.origin
      (globalSourceShift rounds oldA, freshA) at hstopA
  change firstExitRoundSplit firstB pending threshold
      (shiftCoins rounds (old oldB))
      (pendingCoinExtension deleted.nextLabel pending (active freshB)) =
    survivorPairStop firstB threshold preCoins preRounds
      basePending c.origin
      (globalSourceShift rounds oldB, freshB) at hstopB
  have hstopObs := congrArg Prod.fst hsecond
  change survivorPairStop firstA threshold preCoins preRounds
      basePending c.origin
      (globalSourceShift rounds oldA, freshA) =
    survivorPairStop firstA threshold preCoins preRounds
      basePending c.origin
      (globalSourceShift rounds oldB, freshB) at hstopObs
  have hrounds : firstExitRoundSplit firstA pending threshold
      (shiftCoins rounds (old oldA))
      (pendingCoinExtension deleted.nextLabel pending (active freshA)) =
    firstExitRoundSplit firstB pending threshold
      (shiftCoins rounds (old oldB))
      (pendingCoinExtension deleted.nextLabel pending (active freshB)) := by
    rw [hstopA, hstopB, ← hfirstState]
    exact hstopObs
  have ha := (c.refreshFuture oldA).advance_level P intensity
    threshold basePending preCoins freshA tape
  have hb := (c.refreshFuture oldB).advance_level P intensity
    threshold basePending preCoins freshB tape
  change ((c.refreshFuture oldA).advance P intensity threshold
      basePending preCoins freshA tape).level =
    preRounds + firstExitRoundSplit firstA pending threshold
      (shiftCoins rounds (old oldA))
      (pendingCoinExtension deleted.nextLabel pending (active freshA)) at ha
  change ((c.refreshFuture oldB).advance P intensity threshold
      basePending preCoins freshB tape).level =
    preRounds + firstExitRoundSplit firstB pending threshold
      (shiftCoins rounds (old oldB))
      (pendingCoinExtension deleted.nextLabel pending (active freshB)) at hb
  rw [ha, hb, hrounds]

theorem OriginConfiguration.refreshed_advance_sourcePrefix_eq_of_observations
    {n : Nat} (c : OriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins freshA freshB : Nat × Nat → Bool)
    (oldA oldB : Nat × (Nat × Nat) → Bool)
    (tape : Nat → LatticePoint n)
    (hfirst : globalSourcePrefix
        (ttcReference.firstLoopExit (c.state.removeComponent P)
          intensity threshold) oldA =
      globalSourcePrefix
        (ttcReference.firstLoopExit (c.state.removeComponent P)
          intensity threshold) oldB)
    (hsecond :
      let deleted := c.state.removeComponent P
      let rounds := ttcReference.firstLoopExit deleted intensity threshold
      let first := ttcReference.firstLoopResult deleted intensity threshold
        (sourceOldCoins c.origin
          (c.refreshFuture oldA).source.coins c.level)
      let preRounds := c.level + rounds
      survivorPairFullObservation first threshold preCoins
          preRounds basePending c.origin
          (globalSourceShift rounds oldA, freshA) =
        survivorPairFullObservation first threshold preCoins
          preRounds basePending c.origin
          (globalSourceShift rounds oldB, freshB)) :
    let nextA := (c.refreshFuture oldA).advance P intensity threshold
      basePending preCoins freshA tape
    let nextB := (c.refreshFuture oldB).advance P intensity threshold
      basePending preCoins freshB tape
    originCoinPrefix nextA.level nextA.source.coins =
      originCoinPrefix nextB.level nextB.source.coins := by
  let deleted := c.state.removeComponent P
  let rounds := ttcReference.firstLoopExit deleted intensity threshold
  let preRounds := c.level + rounds
  let old := fun global => sourceOldCoins c.origin
    (c.refreshFuture global).source.coins c.level
  let firstA := ttcReference.firstLoopResult deleted intensity threshold
    (old oldA)
  let firstB := ttcReference.firstLoopResult deleted intensity threshold
    (old oldB)
  let stopA := survivorPairStop firstA threshold preCoins
    preRounds basePending c.origin
      (globalSourceShift rounds oldA, freshA)
  let stopB := survivorPairStop firstB threshold preCoins
    preRounds basePending c.origin
      (globalSourceShift rounds oldB, freshB)
  let nextA := (c.refreshFuture oldA).advance P intensity threshold
    basePending preCoins freshA tape
  let nextB := (c.refreshFuture oldB).advance P intensity threshold
    basePending preCoins freshB tape
  have hfirstState : firstA = firstB :=
    c.refreshed_rateThinningResult_eq_of_prefix_eq P intensity threshold
      oldA oldB hfirst
  have hstopObs := congrArg Prod.fst hsecond
  change stopA = survivorPairStop firstA threshold preCoins
      preRounds basePending c.origin
      (globalSourceShift rounds oldB, freshB) at hstopObs
  have hstop : stopA = stopB := by
    change stopA = survivorPairStop firstB threshold preCoins
      preRounds basePending c.origin
      (globalSourceShift rounds oldB, freshB)
    rw [← hfirstState]
    exact hstopObs
  have hprefixObs := congrArg Prod.snd hsecond
  change (globalSourcePrefix stopA
        (globalSourceShift rounds oldA),
      coinPrefix stopA freshA) =
    (globalSourcePrefix
        (survivorPairStop firstA threshold preCoins preRounds
          basePending c.origin
          (globalSourceShift rounds oldB, freshB))
        (globalSourceShift rounds oldB),
      coinPrefix
        (survivorPairStop firstA threshold preCoins preRounds
          basePending c.origin
          (globalSourceShift rounds oldB, freshB))
        freshB) at hprefixObs
  rw [← hstopObs] at hprefixObs
  have hsourcePrefix :=
    coinsAppend_refreshed_observedPrefix_eq_of_twoPieces
      c.source.coins c.level c.source.processed rounds stopA
      preCoins freshA freshB oldA oldB hfirst
      (congrArg Prod.fst hprefixObs)
      (congrArg Prod.snd hprefixObs)
  have hsourceA := congrArg OriginSourceState.coins
    ((c.refreshFuture oldA).advance_source P intensity threshold
      basePending preCoins freshA tape)
  have hsourceB := congrArg OriginSourceState.coins
    ((c.refreshFuture oldB).advance_source P intensity threshold
      basePending preCoins freshB tape)
  change nextA.source.coins = coinsAppend
      (refreshedSourceCoins c.source.coins c.level oldA)
      c.source.processed preCoins freshA preRounds at hsourceA
  change nextB.source.coins = coinsAppend
      (refreshedSourceCoins c.source.coins c.level oldB)
      c.source.processed preCoins freshB preRounds at hsourceB
  have hlevelA := (c.refreshFuture oldA).advance_level P intensity
    threshold basePending preCoins freshA tape
  have hlevelB := (c.refreshFuture oldB).advance_level P intensity
    threshold basePending preCoins freshB tape
  have hactiveA := c.refreshed_activeRounds_eq_pairStop P intensity
    threshold basePending preCoins freshA oldA
  have hactiveB := c.refreshed_activeRounds_eq_pairStop P intensity
    threshold basePending preCoins freshB oldB
  change nextA.level = preRounds + firstExitRoundSplit firstA
      (pendingAfter preCoins preRounds deleted.nextLabel basePending)
      threshold (shiftCoins rounds (old oldA))
      (pendingCoinExtension deleted.nextLabel
        (pendingAfter preCoins preRounds deleted.nextLabel basePending)
        (originalSurvivorCoinRestriction preCoins preRounds
          deleted.nextLabel basePending freshA)) at hlevelA
  change nextB.level = preRounds + firstExitRoundSplit firstB
      (pendingAfter preCoins preRounds deleted.nextLabel basePending)
      threshold (shiftCoins rounds (old oldB))
      (pendingCoinExtension deleted.nextLabel
        (pendingAfter preCoins preRounds deleted.nextLabel basePending)
        (originalSurvivorCoinRestriction preCoins preRounds
          deleted.nextLabel basePending freshB)) at hlevelB
  change firstExitRoundSplit firstA
      (pendingAfter preCoins preRounds deleted.nextLabel basePending)
      threshold (shiftCoins rounds (old oldA))
      (pendingCoinExtension deleted.nextLabel
        (pendingAfter preCoins preRounds deleted.nextLabel basePending)
        (originalSurvivorCoinRestriction preCoins preRounds
          deleted.nextLabel basePending freshA)) = stopA at hactiveA
  change firstExitRoundSplit firstB
      (pendingAfter preCoins preRounds deleted.nextLabel basePending)
      threshold (shiftCoins rounds (old oldB))
      (pendingCoinExtension deleted.nextLabel
        (pendingAfter preCoins preRounds deleted.nextLabel basePending)
        (originalSurvivorCoinRestriction preCoins preRounds
          deleted.nextLabel basePending freshB)) = stopB at hactiveB
  rw [hactiveA] at hlevelA
  rw [hactiveB] at hlevelB
  change originCoinPrefix nextA.level nextA.source.coins =
    originCoinPrefix nextB.level nextB.source.coins
  rw [hlevelA, hlevelB, hstop, hsourceA, hsourceB]
  simpa [preRounds, hstop] using hsourcePrefix

end Kr25Ssmxt
