import ttc.Analysis.JointSourceEncoding
import ttc.Analysis.CombinedTailLaw

/-! Extend the finite survivor indexing of newly drawn copies to an
injective relabelling of every fresh coin coordinate. -/

namespace ttc

open MeasureTheory

noncomputable def survivorRelabel
    (preCoins : Nat × Nat → Bool) (preRounds firstLabel basePending : Nat)
    (i : Nat) : Nat :=
  if h : i < pendingAfter preCoins preRounds firstLabel basePending then
    (pendingSurvivorFin preCoins preRounds firstLabel basePending
      ⟨i, h⟩).val
  else basePending +
    (i - pendingAfter preCoins preRounds firstLabel basePending)

theorem survivorRelabel_active
    (preCoins : Nat × Nat → Bool) (preRounds firstLabel basePending : Nat)
    (i : Fin (pendingAfter preCoins preRounds firstLabel basePending)) :
    survivorRelabel preCoins preRounds firstLabel basePending
      i.val =
    (pendingSurvivorFin preCoins preRounds firstLabel basePending i).val := by
  simp [survivorRelabel, i.isLt]

theorem survivorRelabel_injective
    (preCoins : Nat × Nat → Bool) (preRounds firstLabel basePending : Nat) :
    Function.Injective
      (survivorRelabel preCoins preRounds firstLabel
        basePending) := by
  let pending := pendingAfter preCoins preRounds firstLabel basePending
  intro i j hij
  by_cases hi : i < pending <;> by_cases hj : j < pending
  · have hfin :
        pendingSurvivorFin preCoins preRounds firstLabel basePending
            ⟨i, hi⟩ =
          pendingSurvivorFin preCoins preRounds firstLabel basePending
            ⟨j, hj⟩ := by
        apply Fin.ext
        simpa [survivorRelabel, pending, hi, hj] using hij
    exact congrArg Fin.val
      ((pendingSurvivorFin_injective preCoins preRounds firstLabel
        basePending) hfin)
  · have hbound :=
      (pendingSurvivorFin preCoins preRounds firstLabel basePending
        ⟨i, hi⟩).isLt
    have heq :
        (pendingSurvivorFin preCoins preRounds firstLabel basePending
          ⟨i, hi⟩).val = basePending + (j - pending) := by
      simpa [survivorRelabel, pending, hi, hj] using hij
    omega
  · have hbound :=
      (pendingSurvivorFin preCoins preRounds firstLabel basePending
        ⟨j, hj⟩).isLt
    have heq : basePending + (i - pending) =
        (pendingSurvivorFin preCoins preRounds firstLabel basePending
          ⟨j, hj⟩).val := by
      simpa [survivorRelabel, pending, hi, hj] using hij
    omega
  · have heq : basePending + (i - pending) =
        basePending + (j - pending) := by
      simpa [survivorRelabel, pending, hi, hj] using hij
    omega

noncomputable def jointSurvivorRead
    (preCoins : Nat × Nat → Bool) (preRounds firstLabel basePending : Nat)
    (origin : Nat → Nat × Nat) (coins : Nat × Nat → Bool) :
    Nat × Nat → Bool :=
  jointRelabelRead origin firstLabel
    (fun i => firstLabel +
      survivorRelabel preCoins preRounds firstLabel
        basePending i) coins

theorem measurable_jointSurvivorRead
    (preCoins : Nat × Nat → Bool) (preRounds firstLabel basePending : Nat)
    (origin : Nat → Nat × Nat) :
    Measurable (jointSurvivorRead preCoins preRounds
      firstLabel basePending origin) :=
  measurable_jointRelabelRead origin firstLabel _

theorem jointSurvivorRead_prefix_local
    (preCoins : Nat × Nat → Bool) (preRounds firstLabel basePending : Nat)
    (origin : Nat → Nat × Nat) (rounds : Nat)
    (coins : Nat × Nat → Bool) :
    coinPrefix rounds
      (jointSurvivorRead preCoins preRounds firstLabel
        basePending origin (coinPrefix rounds coins)) =
      coinPrefix rounds
        (jointSurvivorRead preCoins preRounds firstLabel
          basePending origin coins) :=
  jointRelabelRead_prefix_local origin firstLabel _ rounds coins

theorem fairCoinStreamLaw_jointSurvivorRead
    (preCoins : Nat × Nat → Bool) (preRounds firstLabel basePending
      processed : Nat) (origin : Nat → Nat × Nat)
    (hhistory : OriginHistory firstLabel processed origin) :
    fairCoinStreamLaw.map
      (jointSurvivorRead preCoins preRounds firstLabel
        basePending origin) = fairCoinStreamLaw := by
  exact fairCoinStreamLaw_jointRelabelRead firstLabel processed origin
    hhistory _ (fun i j hij =>
      (survivorRelabel_injective preCoins preRounds firstLabel
        basePending) (Nat.add_left_cancel hij))

theorem jointSurvivorRead_active
    (preCoins : Nat × Nat → Bool) (preRounds firstLabel basePending : Nat)
    (origin : Nat → Nat × Nat) (coins : Nat × Nat → Bool)
    (rounds : Nat)
    (i : Fin (pendingAfter preCoins preRounds firstLabel basePending)) :
    jointSurvivorRead preCoins preRounds firstLabel basePending
      origin coins (rounds, firstLabel + i.val) =
    originalSurvivorCoinRestriction preCoins preRounds firstLabel
      basePending (jointFreshRead coins) (rounds, i) := by
  have hnot : ¬ firstLabel + i.val < firstLabel := by omega
  simp [jointSurvivorRead, jointRelabelRead,
    mergeCoinsAtLabel, hnot, survivorRelabel_active,
    originalSurvivorCoinRestriction]

/-- The actual second-loop stopping round equals first exit on the fair
joint-source read, including the surviving-copy renumbering. -/
theorem firstExitRoundSplit_originalSurvivors_eq_jointRead
    {n : Nat} (s : TTCState n) (threshold : Real)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat)
    (origin : Nat → Nat × Nat) (coins : Nat × Nat → Bool)
    (hfresh : s.LabelsFresh) :
    let pending := pendingAfter preCoins preRounds s.nextLabel basePending
    let old := fun pair : Nat × Nat => jointOldRead coins
      ((origin pair.2).1, (pair.1, (origin pair.2).2))
    let active := originalSurvivorCoinRestriction preCoins preRounds
      s.nextLabel basePending (jointFreshRead coins)
    firstExitRoundSplit s pending threshold old
      (pendingCoinExtension s.nextLabel pending active) =
    ttcPseudocode.secondLoopExitRound s pending threshold
      (jointSurvivorRead preCoins preRounds s.nextLabel
        basePending origin coins) := by
  let pending := pendingAfter preCoins preRounds s.nextLabel basePending
  let old := fun pair : Nat × Nat => jointOldRead coins
    ((origin pair.2).1, (pair.1, (origin pair.2).2))
  let active := originalSurvivorCoinRestriction preCoins preRounds
    s.nextLabel basePending (jointFreshRead coins)
  let fresh : Nat × Nat → Bool := fun pair =>
    jointFreshRead coins
      (pair.1, s.nextLabel +
        survivorRelabel preCoins preRounds s.nextLabel
          basePending (pair.2 - s.nextLabel))
  have hread : jointSurvivorRead preCoins preRounds
      s.nextLabel basePending origin coins =
      mergeCoinsAtLabel s.nextLabel old fresh := rfl
  have hcoin (r i : Nat) (hi : i < pending) :
      pendingCoinExtension s.nextLabel pending active
        (r, s.nextLabel + i) =
      fresh (r, s.nextLabel + i) := by
    let k : Fin pending := ⟨i, hi⟩
    rw [pendingCoinExtension_at s.nextLabel pending r i hi]
    change active (r, k) = fresh (r, s.nextLabel + i)
    have hactive := jointSurvivorRead_active preCoins preRounds
      s.nextLabel basePending origin coins r k
    rw [hread] at hactive
    have hnot : ¬ s.nextLabel + i < s.nextLabel := by omega
    simpa [mergeCoinsAtLabel, hnot, fresh, active, k] using hactive.symm
  calc
    firstExitRoundSplit s pending threshold old
        (pendingCoinExtension s.nextLabel pending active) =
      firstExitRoundSplit s pending threshold old fresh :=
        firstExitRoundSplit_fresh_coins_congr s pending threshold old
          _ _ hcoin
    _ = ttcPseudocode.secondLoopExitRound s pending threshold
        (jointSurvivorRead preCoins preRounds s.nextLabel
          basePending origin coins) := by
      rw [hread]
      exact (firstExitRound_mergeCoinsAtLabel s pending threshold old fresh
        hfresh).symm

theorem thinningResultSplitFinite_originalSurvivors_eq_jointRead
    {n : Nat} (s : TTCState n) (threshold : Real)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat)
    (origin : Nat → Nat × Nat) (coins : Nat × Nat → Bool)
    (hfresh : s.LabelsFresh) :
    let pending := pendingAfter preCoins preRounds s.nextLabel basePending
    let old := fun pair : Nat × Nat => jointOldRead coins
      ((origin pair.2).1, (pair.1, (origin pair.2).2))
    let active := originalSurvivorCoinRestriction preCoins preRounds
      s.nextLabel basePending (jointFreshRead coins)
    thinningResultSplitFinite s pending threshold old active =
    ttcPseudocode.secondLoopResult s pending threshold
      (jointSurvivorRead preCoins preRounds s.nextLabel
        basePending origin coins) := by
  let pending := pendingAfter preCoins preRounds s.nextLabel basePending
  let old := fun pair : Nat × Nat => jointOldRead coins
    ((origin pair.2).1, (pair.1, (origin pair.2).2))
  let active := originalSurvivorCoinRestriction preCoins preRounds
    s.nextLabel basePending (jointFreshRead coins)
  let fresh : Nat × Nat → Bool := fun pair =>
    jointFreshRead coins
      (pair.1, s.nextLabel +
        survivorRelabel preCoins preRounds s.nextLabel
          basePending (pair.2 - s.nextLabel))
  have hread : jointSurvivorRead preCoins preRounds
      s.nextLabel basePending origin coins =
      mergeCoinsAtLabel s.nextLabel old fresh := rfl
  have hcoin (r i : Nat) (hi : i < pending) :
      pendingCoinExtension s.nextLabel pending active
        (r, s.nextLabel + i) =
      fresh (r, s.nextLabel + i) := by
    let k : Fin pending := ⟨i, hi⟩
    rw [pendingCoinExtension_at s.nextLabel pending r i hi]
    change active (r, k) = fresh (r, s.nextLabel + i)
    have hactive := jointSurvivorRead_active preCoins preRounds
      s.nextLabel basePending origin coins r k
    rw [hread] at hactive
    have hnot : ¬ s.nextLabel + i < s.nextLabel := by omega
    simpa [mergeCoinsAtLabel, hnot, fresh, active, k] using hactive.symm
  calc
    thinningResultSplitFinite s pending threshold old active =
      thinningResultSplit s pending threshold old
        (pendingCoinExtension s.nextLabel pending active) := rfl
    _ = thinningResultSplit s pending threshold old fresh :=
      thinningResultSplit_fresh_coins_congr s pending threshold old
        _ _ hcoin
    _ = ttcPseudocode.secondLoopResult s pending threshold
        (jointSurvivorRead preCoins preRounds s.nextLabel
          basePending origin coins) := by
      rw [hread]
      exact (thinningResult_mergeCoinsAtLabel s pending threshold old fresh
        hfresh).symm

theorem thinningResultSplitFinite_originalSurvivors_atObserved
    {n : Nat} (s : TTCState n) (threshold : Real)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat)
    (origin : Nat → Nat × Nat) (coins : Nat × Nat → Bool)
    (hfresh : s.LabelsFresh) :
    let pending := pendingAfter preCoins preRounds s.nextLabel basePending
    let old := fun pair : Nat × Nat => jointOldRead coins
      ((origin pair.2).1, (pair.1, (origin pair.2).2))
    let active := originalSurvivorCoinRestriction preCoins preRounds
      s.nextLabel basePending (jointFreshRead coins)
    let read := jointSurvivorRead preCoins preRounds s.nextLabel
      basePending origin
    let stop := ttcPseudocode.secondLoopExitRound s pending threshold (read coins)
    thinningResultSplitFinite s pending threshold old active =
      thinningResultAtObserved s pending read
        (stop, coinPrefix stop coins) := by
  let pending := pendingAfter preCoins preRounds s.nextLabel basePending
  let read := jointSurvivorRead preCoins preRounds s.nextLabel
    basePending origin
  calc
    thinningResultSplitFinite s pending threshold
        (fun pair => jointOldRead coins
          ((origin pair.2).1, (pair.1, (origin pair.2).2)))
        (originalSurvivorCoinRestriction preCoins preRounds s.nextLabel
          basePending (jointFreshRead coins)) =
      ttcPseudocode.secondLoopResult s pending threshold (read coins) :=
        thinningResultSplitFinite_originalSurvivors_eq_jointRead s
          threshold preCoins preRounds basePending origin coins hfresh
    _ = thinningResultAtObserved s pending read
        (ttcPseudocode.secondLoopExitRound s pending threshold (read coins),
          coinPrefix (ttcPseudocode.secondLoopExitRound s pending threshold (read coins))
            coins) :=
      thinningResult_eq_atObserved s pending threshold read
        (fun r coins => jointSurvivorRead_prefix_local
          preCoins preRounds s.nextLabel basePending origin r coins)
        coins

/-- For the program's survivor-filtered second loop, the stopped observed
coin prefix is independent of both complete unused source families. -/
theorem jointSurvivorRead_stoppedPrefix_jointTail_law
    {n : Nat} (s : TTCState n) (threshold : Real)
    (hthreshold : 0 ≤ threshold)
    (preCoins : Nat × Nat → Bool) (preRounds basePending processed : Nat)
    (origin : Nat → Nat × Nat)
    (hhistory : OriginHistory s.nextLabel processed origin) :
    let pending := pendingAfter preCoins preRounds s.nextLabel basePending
    let read := jointSurvivorRead preCoins preRounds
      s.nextLabel basePending origin
    let stop := fun coins => ttcPseudocode.secondLoopExitRound s pending threshold (read coins)
    fairCoinStreamLaw.map
      (fun coins =>
        (coinPrefix (stop coins) coins,
          (jointOldRead (shiftCoins (stop coins) coins),
            jointFreshRead (shiftCoins (stop coins) coins)))) =
    (fairCoinStreamLaw.map
      (fun coins => coinPrefix (stop coins) coins)).prod
      ((Measure.infinitePi
        (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
        fairCoinStreamLaw) := by
  exact joint_localRead_stoppedPrefix_jointTail_law s
    (pendingAfter preCoins preRounds s.nextLabel basePending)
    threshold hthreshold
    (jointSurvivorRead preCoins preRounds s.nextLabel
      basePending origin)
    (measurable_jointSurvivorRead preCoins preRounds
      s.nextLabel basePending origin)
    (fairCoinStreamLaw_jointSurvivorRead preCoins preRounds
      s.nextLabel basePending processed origin hhistory)
    (fun r coins => jointSurvivorRead_prefix_local
      preCoins preRounds s.nextLabel basePending origin r coins)

theorem jointSurvivorRead_stoppedRoundPrefix_jointTail_law
    {n : Nat} (s : TTCState n) (threshold : Real)
    (hthreshold : 0 ≤ threshold)
    (preCoins : Nat × Nat → Bool) (preRounds basePending processed : Nat)
    (origin : Nat → Nat × Nat)
    (hhistory : OriginHistory s.nextLabel processed origin) :
    let pending := pendingAfter preCoins preRounds s.nextLabel basePending
    let read := jointSurvivorRead preCoins preRounds
      s.nextLabel basePending origin
    let stop := fun coins => ttcPseudocode.secondLoopExitRound s pending threshold (read coins)
    fairCoinStreamLaw.map
      (fun coins =>
        ((stop coins, coinPrefix (stop coins) coins),
          (jointOldRead (shiftCoins (stop coins) coins),
            jointFreshRead (shiftCoins (stop coins) coins)))) =
    (fairCoinStreamLaw.map
      (fun coins => (stop coins, coinPrefix (stop coins) coins))).prod
      ((Measure.infinitePi
        (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
        fairCoinStreamLaw) := by
  exact joint_localRead_stoppedRoundPrefix_jointTail_law s
    (pendingAfter preCoins preRounds s.nextLabel basePending)
    threshold hthreshold
    (jointSurvivorRead preCoins preRounds s.nextLabel
      basePending origin)
    (measurable_jointSurvivorRead preCoins preRounds
      s.nextLabel basePending origin)
    (fairCoinStreamLaw_jointSurvivorRead preCoins preRounds
      s.nextLabel basePending processed origin hhistory)
    (fun r coins => jointSurvivorRead_prefix_local
      preCoins preRounds s.nextLabel basePending origin r coins)

theorem jointSurvivorRead_stoppedReadPrefix_jointTail_law
    {n : Nat} (s : TTCState n) (threshold : Real)
    (hthreshold : 0 ≤ threshold)
    (preCoins : Nat × Nat → Bool) (preRounds basePending processed : Nat)
    (origin : Nat → Nat × Nat)
    (hhistory : OriginHistory s.nextLabel processed origin) :
    let pending := pendingAfter preCoins preRounds s.nextLabel basePending
    let read := jointSurvivorRead preCoins preRounds
      s.nextLabel basePending origin
    let stop := fun coins => ttcPseudocode.secondLoopExitRound s pending threshold (read coins)
    fairCoinStreamLaw.map
      (fun coins =>
        ((stop coins, coinPrefix (stop coins) (read coins)),
          (jointOldRead (shiftCoins (stop coins) coins),
            jointFreshRead (shiftCoins (stop coins) coins)))) =
    (fairCoinStreamLaw.map
      (fun coins => (stop coins,
        coinPrefix (stop coins) (read coins)))).prod
      ((Measure.infinitePi
        (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
        fairCoinStreamLaw) := by
  exact joint_localRead_stoppedReadPrefix_jointTail_law s
    (pendingAfter preCoins preRounds s.nextLabel basePending)
    threshold hthreshold
    (jointSurvivorRead preCoins preRounds s.nextLabel
      basePending origin)
    (measurable_jointSurvivorRead preCoins preRounds
      s.nextLabel basePending origin)
    (fairCoinStreamLaw_jointSurvivorRead preCoins preRounds
      s.nextLabel basePending processed origin hhistory)
    (fun r coins => jointSurvivorRead_prefix_local
      preCoins preRounds s.nextLabel basePending origin r coins)

/-- Replacing the new component's row in the old stopped global tail by
the fresh stopped tail yields a full fair global source, independent of the
observed stopped prefix. -/
theorem jointSurvivorRead_stoppedPrefix_combinedTail_law
    {n : Nat} (s : TTCState n) (threshold : Real)
    (hthreshold : 0 ≤ threshold)
    (preCoins : Nat × Nat → Bool) (preRounds basePending processed
      component : Nat)
    (origin : Nat → Nat × Nat)
    (hhistory : OriginHistory s.nextLabel processed origin) :
    let pending := pendingAfter preCoins preRounds s.nextLabel basePending
    let read := jointSurvivorRead preCoins preRounds
      s.nextLabel basePending origin
    let stop := fun coins => ttcPseudocode.secondLoopExitRound s pending threshold (read coins)
    fairCoinStreamLaw.map
      (fun coins =>
        (coinPrefix (stop coins) coins,
          fun tag : Nat × (Nat × Nat) =>
            if tag.1 = component then
              jointFreshRead (shiftCoins (stop coins) coins)
                (tag.2.1, tag.2.2)
            else
              jointOldRead (shiftCoins (stop coins) coins)
                (tag.1, (tag.2.1, tag.2.2)))) =
    (fairCoinStreamLaw.map
      (fun coins => coinPrefix (stop coins) coins)).prod
      (Measure.infinitePi
        (fun _ : Nat × (Nat × Nat) => fairCoinLaw)) := by
  let pending := pendingAfter preCoins preRounds s.nextLabel basePending
  let read := jointSurvivorRead preCoins preRounds
    s.nextLabel basePending origin
  let stop := fun coins => ttcPseudocode.secondLoopExitRound s pending threshold (read coins)
  let observed : (Nat × Nat → Bool) → Nat × Nat → Bool :=
    fun coins => coinPrefix (stop coins) coins
  let pairTail : (Nat × Nat → Bool) →
      (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool) :=
    fun coins =>
      (jointOldRead (shiftCoins (stop coins) coins),
        jointFreshRead (shiftCoins (stop coins) coins))
  let combine : ((Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool)) →
      Nat × (Nat × Nat) → Bool := fun z tag =>
    if tag.1 = component then z.2 (tag.2.1, tag.2.2)
    else z.1 (tag.1, (tag.2.1, tag.2.2))
  have hcombine : Measurable combine := by
    apply Measurable.of_eval
    intro tag
    by_cases htag : tag.1 = component
    · simpa only [combine, htag, ite_true, Function.comp_def] using
        (measurable_pi_apply (tag.2.1, tag.2.2)).comp measurable_snd
    · simpa only [combine, htag, ite_false, Function.comp_def] using
        (measurable_pi_apply
          (tag.1, (tag.2.1, tag.2.2))).comp measurable_fst
  have hsplit : Measurable (fun coins : Nat × Nat → Bool =>
      (observed coins, pairTail coins)) := by
    have hstop : Measurable stop :=
      (measurable_firstExitRound s pending threshold).comp
        (measurable_jointSurvivorRead preCoins preRounds
          s.nextLabel basePending origin)
    have hobserved : Measurable observed := by
      have hprefixJoint : Measurable
          (fun z : Nat × (Nat × Nat → Bool) => coinPrefix z.1 z.2) := by
        apply measurable_from_prod_countable_right
        intro rounds
        exact measurable_coinPrefix rounds
      exact hprefixJoint.comp (hstop.prodMk measurable_id)
    have htail : Measurable (fun coins : Nat × Nat → Bool =>
        shiftCoins (stop coins) coins) :=
      (measurable_stoppedCoinPair stop hstop).snd
    exact hobserved.prodMk (measurable_jointRead.comp htail)
  let reindex : ((Nat × Nat → Bool) ×
      ((Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool))) →
      (Nat × Nat → Bool) × (Nat × (Nat × Nat) → Bool) :=
    Prod.map id combine
  have hreindex : Measurable reindex :=
    measurable_fst.prodMk (hcombine.comp measurable_snd)
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  letI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
    fun _ => fairCoinLaw_isProbabilityMeasure
  letI : IsProbabilityMeasure
      (Measure.infinitePi
        (fun _ : Nat × (Nat × Nat) => fairCoinLaw)) := by
    infer_instance
  calc
    fairCoinStreamLaw.map
        (fun coins => (observed coins, combine (pairTail coins))) =
      (fairCoinStreamLaw.map (fun coins =>
        (observed coins, pairTail coins))).map reindex := by
        rw [Measure.map_map hreindex hsplit]
        rfl
    _ = ((fairCoinStreamLaw.map observed).prod
        ((Measure.infinitePi
          (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
          fairCoinStreamLaw)).map reindex := by
        rw [jointSurvivorRead_stoppedPrefix_jointTail_law s
          threshold hthreshold preCoins preRounds basePending processed
          origin hhistory]
    _ = ((fairCoinStreamLaw.map observed).map id).prod
        (((Measure.infinitePi
          (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
          fairCoinStreamLaw).map combine) := by
        exact (Measure.map_prod_map _ _ measurable_id hcombine).symm
    _ = _ := by
      rw [Measure.map_id]
      have hcombined :
          ((Measure.infinitePi
            (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
            fairCoinStreamLaw).map combine =
          Measure.infinitePi
            (fun _ : Nat × (Nat × Nat) => fairCoinLaw) := by
        simpa [combine] using
          combinedTail_fixedShift_law component 0 0
      exact congrArg (fun μ => (fairCoinStreamLaw.map observed).prod μ)
        hcombined

end ttc
