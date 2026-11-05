import Kr25Ssmxt.Analysis.ManuscriptGlobalSourcePrefix

/-! The encoded stopping law, expressed directly on the independent pair
of old global and newly drawn fair sources. -/

namespace Kr25Ssmxt

open MeasureTheory

noncomputable def manuscriptSurvivorPairRead
    (preCoins : Nat × Nat → Bool) (preRounds firstLabel basePending : Nat)
    (origin : Nat → Nat × Nat)
    (z : (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool)) :
    Nat × Nat → Bool :=
  mergeCoinsAtLabel firstLabel
    (fun pair => z.1 ((origin pair.2).1,
      (pair.1, (origin pair.2).2)))
    (fun pair => z.2 (pair.1, firstLabel +
      manuscriptSurvivorRelabel preCoins preRounds firstLabel
        basePending (pair.2 - firstLabel)))

theorem manuscriptSurvivorPairRead_jointRead
    (preCoins : Nat × Nat → Bool) (preRounds firstLabel basePending : Nat)
    (origin : Nat → Nat × Nat) (coins : Nat × Nat → Bool) :
    manuscriptSurvivorPairRead preCoins preRounds firstLabel basePending
      origin (manuscriptJointOldRead coins,
        manuscriptJointFreshRead coins) =
    manuscriptJointSurvivorRead preCoins preRounds firstLabel
      basePending origin coins := rfl

theorem measurable_manuscriptSurvivorPairRead
    (preCoins : Nat × Nat → Bool) (preRounds firstLabel basePending : Nat)
    (origin : Nat → Nat × Nat) :
    Measurable (manuscriptSurvivorPairRead preCoins preRounds firstLabel
      basePending origin) := by
  apply measurable_pi_lambda
  intro pair
  by_cases hlabel : pair.2 < firstLabel
  · simpa [manuscriptSurvivorPairRead, mergeCoinsAtLabel, hlabel,
      Function.comp_def] using
      (measurable_pi_apply
        ((origin pair.2).1, (pair.1, (origin pair.2).2))).comp
          measurable_fst
  · simpa [manuscriptSurvivorPairRead, mergeCoinsAtLabel, hlabel,
      Function.comp_def] using
      (measurable_pi_apply
        (pair.1, firstLabel +
          manuscriptSurvivorRelabel preCoins preRounds firstLabel
            basePending (pair.2 - firstLabel))).comp measurable_snd

theorem manuscriptSurvivorPairTail_jointRead
    (rounds : Nat) (coins : Nat × Nat → Bool) :
    (manuscriptGlobalSourceShift rounds (manuscriptJointOldRead coins),
      shiftCoins rounds (manuscriptJointFreshRead coins)) =
    (manuscriptJointOldRead (shiftCoins rounds coins),
      manuscriptJointFreshRead (shiftCoins rounds coins)) := by
  exact Prod.ext
    (by funext tag; rfl)
    (manuscriptJointFreshRead_shift coins rounds).symm

noncomputable def manuscriptSurvivorPairStop
    {n : Nat} (s : TTCState n) (threshold : Real)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat)
    (origin : Nat → Nat × Nat)
    (z : (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool)) : Nat :=
  firstExitRound s
    (pendingAfter preCoins preRounds s.nextLabel basePending) threshold
    (manuscriptSurvivorPairRead preCoins preRounds s.nextLabel
      basePending origin z)

noncomputable def manuscriptSurvivorPairObservation
    {n : Nat} (s : TTCState n) (threshold : Real)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat)
    (origin : Nat → Nat × Nat)
    (z : (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool)) :
    Nat × (Nat × Nat → Bool) :=
  let stop := manuscriptSurvivorPairStop s threshold preCoins preRounds
    basePending origin z
  (stop, coinPrefix stop
    (manuscriptSurvivorPairRead preCoins preRounds s.nextLabel
      basePending origin z))

noncomputable def manuscriptSurvivorPairRemaining
    {n : Nat} (s : TTCState n) (threshold : Real)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat)
    (origin : Nat → Nat × Nat)
    (z : (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool)) :
    (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool) :=
  let stop := manuscriptSurvivorPairStop s threshold preCoins preRounds
    basePending origin z
  (manuscriptGlobalSourceShift stop z.1, shiftCoins stop z.2)

theorem measurable_manuscriptSurvivorPairStop
    {n : Nat} (s : TTCState n) (threshold : Real)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat)
    (origin : Nat → Nat × Nat) :
    Measurable (manuscriptSurvivorPairStop s threshold preCoins preRounds
      basePending origin) :=
  (measurable_firstExitRound s
    (pendingAfter preCoins preRounds s.nextLabel basePending)
    threshold).comp
      (measurable_manuscriptSurvivorPairRead preCoins preRounds
        s.nextLabel basePending origin)

theorem measurable_manuscriptSurvivorPairObservation
    {n : Nat} (s : TTCState n) (threshold : Real)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat)
    (origin : Nat → Nat × Nat) :
    Measurable (manuscriptSurvivorPairObservation s threshold preCoins
      preRounds basePending origin) := by
  have hstop := measurable_manuscriptSurvivorPairStop s threshold
    preCoins preRounds basePending origin
  have hread := measurable_manuscriptSurvivorPairRead preCoins preRounds
    s.nextLabel basePending origin
  have hprefixJoint : Measurable
      (fun z : Nat × (Nat × Nat → Bool) => coinPrefix z.1 z.2) := by
    apply measurable_from_prod_countable_right
    intro rounds
    exact measurable_coinPrefix rounds
  exact hstop.prodMk (hprefixJoint.comp (hstop.prodMk hread))

theorem measurable_manuscriptSurvivorPairRemaining
    {n : Nat} (s : TTCState n) (threshold : Real)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat)
    (origin : Nat → Nat × Nat) :
    Measurable (manuscriptSurvivorPairRemaining s threshold preCoins
      preRounds basePending origin) := by
  have hstop := measurable_manuscriptSurvivorPairStop s threshold
    preCoins preRounds basePending origin
  have holdJoint : Measurable
      (fun z : Nat × (Nat × (Nat × Nat) → Bool) =>
        manuscriptGlobalSourceShift z.1 z.2) := by
    apply measurable_from_prod_countable_right
    intro rounds
    exact measurable_manuscriptGlobalSourceShift rounds
  have hfreshJoint : Measurable
      (fun z : Nat × (Nat × Nat → Bool) => shiftCoins z.1 z.2) := by
    apply measurable_from_prod_countable_right
    intro rounds
    exact measurable_shiftCoins rounds
  exact (holdJoint.comp (hstop.prodMk measurable_fst)).prodMk
    (hfreshJoint.comp (hstop.prodMk measurable_snd))

/-- The second-loop stopped observation and its complete remaining old/new
source pair have an exact product law on the actual independent source pair. -/
theorem manuscriptSurvivorPair_stoppedReadPrefix_tail_law
    {n : Nat} (s : TTCState n) (threshold : Real)
    (hthreshold : 0 ≤ threshold)
    (preCoins : Nat × Nat → Bool) (preRounds basePending processed : Nat)
    (origin : Nat → Nat × Nat)
    (hhistory : ManuscriptOriginHistory s.nextLabel processed origin) :
    let pending := pendingAfter preCoins preRounds s.nextLabel basePending
    let read := manuscriptSurvivorPairRead preCoins preRounds s.nextLabel
      basePending origin
    let stop := fun z => firstExitRound s pending threshold (read z)
    ((Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
      fairCoinStreamLaw).map
      (fun z =>
        ((stop z, coinPrefix (stop z) (read z)),
          (manuscriptGlobalSourceShift (stop z) z.1,
            shiftCoins (stop z) z.2))) =
    (((Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
      fairCoinStreamLaw).map
      (fun z => (stop z, coinPrefix (stop z) (read z)))).prod
      ((Measure.infinitePi
        (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
        fairCoinStreamLaw) := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  let μ := sourceLaw.prod fairCoinStreamLaw
  let pending := pendingAfter preCoins preRounds s.nextLabel basePending
  let read := manuscriptSurvivorPairRead preCoins preRounds s.nextLabel
    basePending origin
  let stop := fun z => firstExitRound s pending threshold (read z)
  let obs : (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool) →
      Nat × (Nat × Nat → Bool) :=
    fun z => (stop z, coinPrefix (stop z) (read z))
  let tail : (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool) →
      (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool) :=
    fun z => (manuscriptGlobalSourceShift (stop z) z.1,
      shiftCoins (stop z) z.2)
  let joint : (Nat × Nat → Bool) →
      (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool) :=
    fun coins => (manuscriptJointOldRead coins,
      manuscriptJointFreshRead coins)
  have hjoint : Measurable joint := measurable_manuscriptJointRead
  have hread : Measurable read :=
    measurable_manuscriptSurvivorPairRead preCoins preRounds s.nextLabel
      basePending origin
  have hstop : Measurable stop :=
    (measurable_firstExitRound s pending threshold).comp hread
  have hprefixJoint : Measurable
      (fun z : Nat × (Nat × Nat → Bool) => coinPrefix z.1 z.2) := by
    apply measurable_from_prod_countable_right
    intro rounds
    exact measurable_coinPrefix rounds
  have hobs : Measurable obs :=
    hstop.prodMk (hprefixJoint.comp (hstop.prodMk hread))
  have holdJoint : Measurable
      (fun z : Nat × (Nat × (Nat × Nat) → Bool) =>
        manuscriptGlobalSourceShift z.1 z.2) := by
    apply measurable_from_prod_countable_right
    intro rounds
    exact measurable_manuscriptGlobalSourceShift rounds
  have hfreshJoint : Measurable
      (fun z : Nat × (Nat × Nat → Bool) =>
        shiftCoins z.1 z.2) := by
    apply measurable_from_prod_countable_right
    intro rounds
    exact measurable_shiftCoins rounds
  have htail : Measurable tail :=
    (holdJoint.comp (hstop.prodMk measurable_fst)).prodMk
      (hfreshJoint.comp (hstop.prodMk measurable_snd))
  have houtput : Measurable (fun z => (obs z, tail z)) :=
    hobs.prodMk htail
  have hsourcePair : fairCoinStreamLaw.map joint = μ :=
    fairCoinStreamLaw_jointRead
  calc
    μ.map (fun z => (obs z, tail z)) =
      (fairCoinStreamLaw.map joint).map
        (fun z => (obs z, tail z)) := by rw [hsourcePair]
    _ = fairCoinStreamLaw.map
        (fun coins => (obs (joint coins), tail (joint coins))) := by
        rw [Measure.map_map houtput hjoint]
        rfl
    _ = fairCoinStreamLaw.map
        (fun coins =>
          ((firstExitRound s pending threshold
                (manuscriptJointSurvivorRead preCoins preRounds
                  s.nextLabel basePending origin coins),
              coinPrefix
                (firstExitRound s pending threshold
                  (manuscriptJointSurvivorRead preCoins preRounds
                    s.nextLabel basePending origin coins))
                (manuscriptJointSurvivorRead preCoins preRounds
                  s.nextLabel basePending origin coins)),
            (manuscriptJointOldRead
              (shiftCoins (stop (joint coins)) coins),
              manuscriptJointFreshRead
                (shiftCoins (stop (joint coins)) coins)))) := by
        congr 1
    _ = (fairCoinStreamLaw.map (fun coins => obs (joint coins))).prod μ := by
        simpa only [μ, sourceLaw, obs, stop, read, joint,
          manuscriptSurvivorPairRead_jointRead] using
          (manuscriptJointSurvivorRead_stoppedReadPrefix_jointTail_law
            s threshold hthreshold preCoins preRounds basePending
            processed origin hhistory)
    _ = (μ.map obs).prod μ := by
        rw [← hsourcePair, Measure.map_map hobs hjoint]
        rfl

end Kr25Ssmxt
