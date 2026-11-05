import Kr25Ssmxt.Analysis.ManuscriptObservationReconstruct
import Kr25Ssmxt.Analysis.ManuscriptOriginUnusedTailStep

/-! The observed representative after a refreshed component step is
determined by the first-loop prefix and the second-loop stopped observation,
and its unused tail is a fixed recombination of the remaining sources. -/

namespace Kr25Ssmxt

open MeasureTheory

noncomputable def manuscriptObservedOrigin
    {n : Nat} (s : TTCState n) (threshold : Real)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat)
    (origin : Nat → Nat × Nat) (processed : Nat)
    (z : (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool)) :
    Nat → Nat × Nat := by
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
  exact manuscriptOriginAppend origin processed second.1.nextLabel
    second.2 index

theorem manuscriptOriginAppend_eq_of_cast (origin : Nat → Nat × Nat)
    (component firstLabel : Nat) {countA countB : Nat}
    (hcount : countA = countB)
    (indexA : Fin countA → Nat) (indexB : Fin countB → Nat)
    (hindex : ∀ i, indexA i = indexB (Fin.cast hcount i)) :
    manuscriptOriginAppend origin component firstLabel countA indexA =
      manuscriptOriginAppend origin component firstLabel countB indexB := by
  cases hcount
  have heq : indexA = indexB := by
    funext i
    simpa using hindex i
  rw [heq]

theorem manuscriptObservedOrigin_eq_of_fullObservation_eq
    {n : Nat} (s : TTCState n) (threshold : Real)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat)
    (origin : Nat → Nat × Nat) (processed : Nat)
    (a b : (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool))
    (hfresh : s.LabelsFresh)
    (hobs : manuscriptSurvivorPairFullObservation s threshold preCoins
        preRounds basePending origin a =
      manuscriptSurvivorPairFullObservation s threshold preCoins
        preRounds basePending origin b) :
    manuscriptObservedOrigin s threshold preCoins preRounds
        basePending origin processed a =
      manuscriptObservedOrigin s threshold preCoins preRounds
        basePending origin processed b := by
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
      twoStageSurvivorLabel preCoins preRounds s.nextLabel
          basePending (active a) (rounds a) i =
      twoStageSurvivorLabel preCoins preRounds s.nextLabel
          basePending (active b) (rounds b) (Fin.cast hcount i) := by
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
    exact hlabel.trans htransport
  change manuscriptOriginAppend origin processed (second a).1.nextLabel
      (second a).2 (twoStageSurvivorLabel preCoins preRounds
        s.nextLabel basePending (active a) (rounds a)) =
    manuscriptOriginAppend origin processed (second b).1.nextLabel
      (second b).2 (twoStageSurvivorLabel preCoins preRounds
        s.nextLabel basePending (active b) (rounds b))
  rw [hstate]
  exact manuscriptOriginAppend_eq_of_cast origin processed
    (second b).1.nextLabel hcount _ _ hpoints

theorem ManuscriptOriginConfiguration.refreshed_advance_origin_eq_observed
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
      basePending preCoins fresh tape).origin =
    manuscriptObservedOrigin first threshold preCoins preRounds
      basePending c.origin c.source.processed
      (manuscriptGlobalSourceShift rounds oldFuture, fresh) := by
  let deleted := c.state.removeComponent P
  let rounds := manuscriptRateExit deleted intensity threshold
  let old := manuscriptSourceOldCoins c.origin
    (c.refreshFuture oldFuture).source.coins c.level
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
  unfold manuscriptObservedOrigin
  dsimp only [ManuscriptOriginConfiguration.advance]
  rw [show (c.refreshFuture oldFuture).state = c.state from rfl,
    show (c.refreshFuture oldFuture).origin = c.origin from rfl,
    show (c.refreshFuture oldFuture).level = c.level from rfl]
  rw [hshift]
  rfl

/-- Equal first-loop prefixes and equal complete second-loop observations
give equal observed representatives after the refreshed component step. -/
theorem ManuscriptOriginConfiguration.refreshed_advance_observedRepresentative_eq
    {n : Nat} (c : ManuscriptOriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins freshA freshB : Nat × Nat → Bool)
    (oldA oldB : Nat × (Nat × Nat) → Bool)
    (tape : Nat → LatticePoint n)
    (hfirst : manuscriptGlobalSourcePrefix
        (manuscriptRateExit (c.state.removeComponent P)
          intensity threshold) oldA =
      manuscriptGlobalSourcePrefix
        (manuscriptRateExit (c.state.removeComponent P)
          intensity threshold) oldB)
    (hsecond :
      let deleted := c.state.removeComponent P
      let rounds := manuscriptRateExit deleted intensity threshold
      let first := manuscriptRateThinningResult deleted intensity threshold
        (manuscriptSourceOldCoins c.origin
          (c.refreshFuture oldA).source.coins c.level)
      let preRounds := c.level + rounds
      manuscriptSurvivorPairFullObservation first threshold preCoins
          preRounds basePending c.origin
          (manuscriptGlobalSourceShift rounds oldA, freshA) =
        manuscriptSurvivorPairFullObservation first threshold preCoins
          preRounds basePending c.origin
          (manuscriptGlobalSourceShift rounds oldB, freshB)) :
    ((c.refreshFuture oldA).advance P intensity threshold basePending
        preCoins freshA tape).observedRepresentative =
      ((c.refreshFuture oldB).advance P intensity threshold basePending
        preCoins freshB tape).observedRepresentative := by
  let deleted := c.state.removeComponent P
  let rounds := manuscriptRateExit deleted intensity threshold
  let preRounds := c.level + rounds
  let firstA := manuscriptRateThinningResult deleted intensity threshold
    (manuscriptSourceOldCoins c.origin
      (c.refreshFuture oldA).source.coins c.level)
  let firstB := manuscriptRateThinningResult deleted intensity threshold
    (manuscriptSourceOldCoins c.origin
      (c.refreshFuture oldB).source.coins c.level)
  have hF : firstA = firstB :=
    c.refreshed_rateThinningResult_eq_of_prefix_eq P intensity threshold
      oldA oldB hfirst
  have hfreshA : firstA.LabelsFresh :=
    manuscriptRateThinningResult_labelsFresh deleted intensity threshold _
      (c.state.labelsFresh_removeComponent P c.fresh)
  have hobs : manuscriptSurvivorPairFullObservation firstA threshold
      preCoins preRounds basePending c.origin
      (manuscriptGlobalSourceShift rounds oldA, freshA) =
    manuscriptSurvivorPairFullObservation firstA threshold preCoins
      preRounds basePending c.origin
      (manuscriptGlobalSourceShift rounds oldB, freshB) := hsecond
  have hlevel := c.refreshed_advance_level_eq_of_observations P intensity
    threshold basePending preCoins freshA freshB oldA oldB tape hfirst hsecond
  have hprefix := c.refreshed_advance_sourcePrefix_eq_of_observations P
    intensity threshold basePending preCoins freshA freshB oldA oldB tape
    hfirst hsecond
  apply ManuscriptOriginConfiguration.observedRepresentative_eq_of_data
  · have hA := c.refreshed_advance_state_eq_observedBatch P intensity
      threshold basePending preCoins freshA oldA tape
    have hB := c.refreshed_advance_state_eq_observedBatch P intensity
      threshold basePending preCoins freshB oldB tape
    change _ = manuscriptObservedBatchState firstA threshold preCoins
      preRounds basePending c.origin tape
      (manuscriptGlobalSourceShift rounds oldA, freshA) at hA
    change _ = manuscriptObservedBatchState firstB threshold preCoins
      preRounds basePending c.origin tape
      (manuscriptGlobalSourceShift rounds oldB, freshB) at hB
    rw [hA, hB, ← hF]
    exact manuscriptObservedBatchState_eq_of_fullObservation_eq firstA
      threshold preCoins preRounds basePending c.origin tape _ _ hfreshA hobs
  · rfl
  · rfl
  · rfl
  · have hA := c.refreshed_advance_origin_eq_observed P intensity
      threshold basePending preCoins freshA oldA tape
    have hB := c.refreshed_advance_origin_eq_observed P intensity
      threshold basePending preCoins freshB oldB tape
    change _ = manuscriptObservedOrigin firstA threshold preCoins
      preRounds basePending c.origin c.source.processed
      (manuscriptGlobalSourceShift rounds oldA, freshA) at hA
    change _ = manuscriptObservedOrigin firstB threshold preCoins
      preRounds basePending c.origin c.source.processed
      (manuscriptGlobalSourceShift rounds oldB, freshB) at hB
    rw [hA, hB, ← hF]
    exact manuscriptObservedOrigin_eq_of_fullObservation_eq firstA
      threshold preCoins preRounds basePending c.origin c.source.processed
      _ _ hfreshA hobs
  · exact hlevel
  · exact hprefix.trans (by rw [hlevel])

/-- Replace one component of a global source by a fresh stream. -/
def manuscriptCombinedTail (component : Nat)
    (z : (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool)) :
    Nat × (Nat × Nat) → Bool :=
  fun index =>
    if index.1 = component then
      z.2 (0 + index.2.1, index.2.2)
    else
      z.1 (index.1, (0 + index.2.1, index.2.2))

theorem measurable_manuscriptCombinedTail (component : Nat) :
    Measurable (manuscriptCombinedTail component) := by
  apply Measurable.of_eval
  intro index
  by_cases h : index.1 = component
  · simp only [manuscriptCombinedTail, h, if_true]
    exact (measurable_pi_apply (0 + index.2.1, index.2.2)).comp
      measurable_snd
  · simp only [manuscriptCombinedTail, h, if_false]
    exact (measurable_pi_apply (index.1, (0 + index.2.1, index.2.2))).comp
      measurable_fst

theorem manuscriptCombinedTail_law (component : Nat) :
    ((Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
        fairCoinStreamLaw).map (manuscriptCombinedTail component) =
    Measure.infinitePi (fun _ : Nat × (Nat × Nat) => fairCoinLaw) :=
  manuscriptCombinedTail_fixedShift_law component 0 0

/-- After a refreshed step, the unused tail is the combined remaining old and
new sources at the adaptive second-loop stop. -/
theorem ManuscriptOriginConfiguration.refreshed_advance_unusedTail_eq_combined
    {n : Nat} (c : ManuscriptOriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins fresh : Nat × Nat → Bool)
    (oldFuture : Nat × (Nat × Nat) → Bool)
    (tape : Nat → LatticePoint n) :
    let deleted := c.state.removeComponent P
    let rounds := manuscriptRateExit deleted intensity threshold
    let preRounds := c.level + rounds
    let first := manuscriptRateThinningResult deleted intensity threshold
      (manuscriptSourceOldCoins c.origin
        (c.refreshFuture oldFuture).source.coins c.level)
    ((c.refreshFuture oldFuture).advance P intensity threshold
        basePending preCoins fresh tape).unusedTail =
      manuscriptCombinedTail c.source.processed
        (manuscriptSurvivorPairRemaining first threshold preCoins preRounds
          basePending c.origin
          (manuscriptGlobalSourceShift rounds oldFuture, fresh)) := by
  let deleted := c.state.removeComponent P
  let rounds := manuscriptRateExit deleted intensity threshold
  let preRounds := c.level + rounds
  let first := manuscriptRateThinningResult deleted intensity threshold
    (manuscriptSourceOldCoins c.origin
      (c.refreshFuture oldFuture).source.coins c.level)
  let stop := manuscriptSurvivorPairStop first threshold preCoins preRounds
    basePending c.origin (manuscriptGlobalSourceShift rounds oldFuture, fresh)
  let next := (c.refreshFuture oldFuture).advance P intensity threshold
    basePending preCoins fresh tape
  have hlevel : next.level = preRounds + stop := by
    have h1 := (c.refreshFuture oldFuture).advance_level P intensity
      threshold basePending preCoins fresh tape
    have h2 := c.refreshed_activeRounds_eq_pairStop P intensity
      threshold basePending preCoins fresh oldFuture
    change next.level = preRounds + firstExitRoundSplit first
      (pendingAfter preCoins preRounds deleted.nextLabel basePending)
      threshold (shiftCoins rounds (manuscriptSourceOldCoins c.origin
        (c.refreshFuture oldFuture).source.coins c.level))
      (pendingCoinExtension deleted.nextLabel
        (pendingAfter preCoins preRounds deleted.nextLabel basePending)
        (originalSurvivorCoinRestriction preCoins preRounds
          deleted.nextLabel basePending fresh)) at h1
    change firstExitRoundSplit first
      (pendingAfter preCoins preRounds deleted.nextLabel basePending)
      threshold (shiftCoins rounds (manuscriptSourceOldCoins c.origin
        (c.refreshFuture oldFuture).source.coins c.level))
      (pendingCoinExtension deleted.nextLabel
        (pendingAfter preCoins preRounds deleted.nextLabel basePending)
        (originalSurvivorCoinRestriction preCoins preRounds
          deleted.nextLabel basePending fresh)) = stop at h2
    rw [h1, h2]
  have htail := c.refreshAdvance_unusedTail P intensity threshold
    basePending preCoins fresh oldFuture tape
  change next.unusedTail = _ at htail
  change next.unusedTail = _
  rw [htail]
  funext index
  by_cases hnew : index.1 = c.source.processed
  · simp only [hnew, if_true, manuscriptCombinedTail,
      manuscriptSurvivorPairRemaining, shiftCoins]
    rw [hlevel]
    congr 1
    change (preRounds + stop - preRounds + index.2.1, index.2.2) =
      (0 + index.2.1 + stop, index.2.2)
    ext <;> (try simp only) <;> omega
  · simp only [hnew, if_false, manuscriptCombinedTail,
      manuscriptSurvivorPairRemaining, manuscriptGlobalSourceShift]
    rw [hlevel]
    congr 1
    change (index.1, (c.level + rounds + stop - c.level + index.2.1,
        index.2.2)) =
      (index.1, (0 + index.2.1 + stop + rounds, index.2.2))
    ext <;> (try simp only) <;> omega

end Kr25Ssmxt
