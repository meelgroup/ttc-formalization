import Kr25Ssmxt.Analysis.MathlibCompat
import Kr25Ssmxt.Analysis.ManuscriptOutputSourcePrefix
import Kr25Ssmxt.Analysis.ManuscriptSurvivorPairTail
import Kr25Ssmxt.Analysis.ManuscriptTwoStageSourceProduct

/-! Retain every old and new source coordinate below the adaptive second-loop
stopping round, including coordinates the loop did not read. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem manuscriptJointOldRead_fullPrefix
    (coins : Nat × Nat → Bool) (rounds : Nat) :
    manuscriptGlobalSourcePrefix rounds (manuscriptJointOldRead coins) =
      manuscriptJointOldRead (coinPrefix rounds coins) := by
  funext tag
  by_cases h : tag.2.1 < rounds <;>
    simp [manuscriptGlobalSourcePrefix, manuscriptJointOldRead,
      manuscriptJointSourceIndex, coinPrefix, h]

theorem manuscriptJointFreshRead_fullPrefix
    (coins : Nat × Nat → Bool) (rounds : Nat) :
    coinPrefix rounds (manuscriptJointFreshRead coins) =
      manuscriptJointFreshRead (coinPrefix rounds coins) := by
  funext pair
  by_cases h : pair.1 < rounds <;>
    simp [manuscriptJointFreshRead, manuscriptJointSourceIndex,
      coinPrefix, h]

theorem manuscriptGlobalSourcePrefix_add_eq_of_pieces
    (a b : Nat × (Nat × Nat) → Bool) (rounds extra : Nat)
    (hfirst : manuscriptGlobalSourcePrefix rounds a =
      manuscriptGlobalSourcePrefix rounds b)
    (hsecond : manuscriptGlobalSourcePrefix extra
        (manuscriptGlobalSourceShift rounds a) =
      manuscriptGlobalSourcePrefix extra
        (manuscriptGlobalSourceShift rounds b)) :
    manuscriptGlobalSourcePrefix (rounds + extra) a =
      manuscriptGlobalSourcePrefix (rounds + extra) b := by
  funext tag
  by_cases hround : tag.2.1 < rounds
  · have hpoint := congrFun hfirst tag
    have htotal : tag.2.1 < rounds + extra := by omega
    simpa [manuscriptGlobalSourcePrefix, hround, htotal] using hpoint
  · by_cases htotal : tag.2.1 < rounds + extra
    · have hlt : tag.2.1 - rounds < extra := by omega
      have hpoint := congrFun hsecond
        (tag.1, (tag.2.1 - rounds, tag.2.2))
      have hadd : tag.2.1 - rounds + rounds = tag.2.1 := by omega
      simpa [manuscriptGlobalSourcePrefix,
        manuscriptGlobalSourceShift, htotal, hlt, hadd] using hpoint
    · simp [manuscriptGlobalSourcePrefix, htotal]

theorem manuscriptSurvivorPairRead_prefix_eq_of_fullPrefixes
    (preCoins : Nat × Nat → Bool) (preRounds firstLabel basePending : Nat)
    (origin : Nat → Nat × Nat)
    (a b : (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool))
    (rounds : Nat)
    (hold : manuscriptGlobalSourcePrefix rounds a.1 =
      manuscriptGlobalSourcePrefix rounds b.1)
    (hfresh : coinPrefix rounds a.2 = coinPrefix rounds b.2) :
    coinPrefix rounds
      (manuscriptSurvivorPairRead preCoins preRounds firstLabel
        basePending origin a) =
    coinPrefix rounds
      (manuscriptSurvivorPairRead preCoins preRounds firstLabel
        basePending origin b) := by
  funext pair
  by_cases hround : pair.1 < rounds
  · by_cases hlabel : pair.2 < firstLabel
    · have hpoint := congrFun hold
        ((origin pair.2).1, (pair.1, (origin pair.2).2))
      simpa [manuscriptGlobalSourcePrefix, hround, coinPrefix,
        manuscriptSurvivorPairRead, mergeCoinsAtLabel, hlabel]
        using hpoint
    · have hpoint := congrFun hfresh
        (pair.1, firstLabel +
          manuscriptSurvivorRelabel preCoins preRounds firstLabel
            basePending (pair.2 - firstLabel))
      simpa [coinPrefix, hround, manuscriptSurvivorPairRead,
        mergeCoinsAtLabel, hlabel] using hpoint
  · simp [coinPrefix, hround]

theorem originalSurvivorExtension_prefix_eq_of_futurePrefix
    (preCoins : Nat × Nat → Bool) (preRounds firstLabel basePending
      rounds : Nat) (a b : Nat × Nat → Bool)
    (hfuture : coinPrefix rounds a = coinPrefix rounds b) :
    coinPrefix rounds
      (pendingCoinExtension firstLabel
        (pendingAfter preCoins preRounds firstLabel basePending)
        (originalSurvivorCoinRestriction preCoins preRounds
          firstLabel basePending a)) =
    coinPrefix rounds
      (pendingCoinExtension firstLabel
        (pendingAfter preCoins preRounds firstLabel basePending)
        (originalSurvivorCoinRestriction preCoins preRounds
          firstLabel basePending b)) := by
  funext pair
  by_cases hround : pair.1 < rounds
  · by_cases hlabel : firstLabel ≤ pair.2 ∧
        pair.2 < firstLabel +
          pendingAfter preCoins preRounds firstLabel basePending
    · have hpoint := congrFun hfuture
        (pair.1, firstLabel +
          (pendingSurvivorFin preCoins preRounds firstLabel
            basePending ⟨pair.2 - firstLabel, by omega⟩).val)
      simpa [coinPrefix, hround, pendingCoinExtension, hlabel,
        originalSurvivorCoinRestriction] using hpoint
    · simp [coinPrefix, hround, pendingCoinExtension, hlabel]
  · simp [coinPrefix, hround]

theorem thinningResult_eq_of_stop_and_prefix_eq
    {n : Nat} (s : TTCState n) (pending : Nat) (threshold : Real)
    (coins coins' : Nat × Nat → Bool)
    (hstop : ttcPseudocode.secondLoopExitRound s pending threshold coins =
      ttcPseudocode.secondLoopExitRound s pending threshold coins')
    (hprefix : coinPrefix
        (ttcPseudocode.secondLoopExitRound s pending threshold coins) coins =
      coinPrefix (ttcPseudocode.secondLoopExitRound s pending threshold coins) coins') :
    ttcPseudocode.secondLoopResult s pending threshold coins =
      ttcPseudocode.secondLoopResult s pending threshold coins' := by
  let rounds := ttcPseudocode.secondLoopExitRound s pending threshold coins
  have hsamples : samplesAfter coins rounds s.X =
      samplesAfter coins' rounds s.X := by
    calc
      samplesAfter coins rounds s.X =
        samplesAfter (coinPrefix rounds coins) rounds s.X :=
          (samplesAfter_coinPrefix s rounds rounds
            (le_refl rounds) coins).symm
      _ = samplesAfter (coinPrefix rounds coins') rounds s.X := by
        rw [hprefix]
      _ = samplesAfter coins' rounds s.X :=
        samplesAfter_coinPrefix s rounds rounds
          (le_refl rounds) coins'
  have hpending : pendingAfter coins rounds s.nextLabel pending =
      pendingAfter coins' rounds s.nextLabel pending := by
    calc
      pendingAfter coins rounds s.nextLabel pending =
        pendingAfter (coinPrefix rounds coins) rounds s.nextLabel pending :=
          (pendingAfter_coinPrefix rounds rounds s.nextLabel pending
            (le_refl rounds) coins).symm
      _ = pendingAfter (coinPrefix rounds coins') rounds
          s.nextLabel pending := by rw [hprefix]
      _ = pendingAfter coins' rounds s.nextLabel pending :=
        pendingAfter_coinPrefix rounds rounds s.nextLabel pending
          (le_refl rounds) coins'
  simp only [ttcPseudocode.secondLoopResult]
  rw [← hstop]
  rw [hsamples, hpending]

theorem thinningResultSplitFinite_pairRead
    {n : Nat} (s : TTCState n) (threshold : Real)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat)
    (origin : Nat → Nat × Nat)
    (z : (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool))
    (hfresh : s.LabelsFresh) :
    let pending := pendingAfter preCoins preRounds s.nextLabel basePending
    let old := fun pair : Nat × Nat => z.1
      ((origin pair.2).1, (pair.1, (origin pair.2).2))
    let active := originalSurvivorCoinRestriction preCoins preRounds
      s.nextLabel basePending z.2
    thinningResultSplitFinite s pending threshold old active =
      ttcPseudocode.secondLoopResult s pending threshold
        (manuscriptSurvivorPairRead preCoins preRounds s.nextLabel
          basePending origin z) := by
  let pending := pendingAfter preCoins preRounds s.nextLabel basePending
  let old := fun pair : Nat × Nat => z.1
    ((origin pair.2).1, (pair.1, (origin pair.2).2))
  let active := originalSurvivorCoinRestriction preCoins preRounds
    s.nextLabel basePending z.2
  let fresh : Nat × Nat → Bool := fun pair =>
    z.2 (pair.1, s.nextLabel +
      manuscriptSurvivorRelabel preCoins preRounds s.nextLabel
        basePending (pair.2 - s.nextLabel))
  have hread : manuscriptSurvivorPairRead preCoins preRounds
      s.nextLabel basePending origin z =
      mergeCoinsAtLabel s.nextLabel old fresh := rfl
  have hcoin (r i : Nat) (hi : i < pending) :
      pendingCoinExtension s.nextLabel pending active
        (r, s.nextLabel + i) =
      fresh (r, s.nextLabel + i) := by
    let k : Fin pending := ⟨i, hi⟩
    rw [pendingCoinExtension_at s.nextLabel pending r i hi]
    change active (r, k) = fresh (r, s.nextLabel + i)
    have hnot : ¬ s.nextLabel + i < s.nextLabel := by omega
    have hrel := manuscriptSurvivorRelabel_active preCoins preRounds
      s.nextLabel basePending k
    simpa [active, fresh, originalSurvivorCoinRestriction, k,
      Nat.add_sub_cancel_left] using
      congrArg (fun j => z.2 (r, s.nextLabel + j)) hrel.symm
  calc
    thinningResultSplitFinite s pending threshold old active =
      thinningResultSplit s pending threshold old
        (pendingCoinExtension s.nextLabel pending active) := rfl
    _ = thinningResultSplit s pending threshold old fresh :=
      thinningResultSplit_fresh_coins_congr s pending threshold old
        _ _ hcoin
    _ = ttcPseudocode.secondLoopResult s pending threshold
        (manuscriptSurvivorPairRead preCoins preRounds s.nextLabel
          basePending origin z) := by
      rw [hread]
      exact (thinningResult_mergeCoinsAtLabel s pending threshold old fresh
        hfresh).symm

theorem firstExitRoundSplit_pairRead
    {n : Nat} (s : TTCState n) (threshold : Real)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat)
    (origin : Nat → Nat × Nat)
    (z : (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool))
    (hfresh : s.LabelsFresh) :
    let pending := pendingAfter preCoins preRounds s.nextLabel basePending
    let old := fun pair : Nat × Nat => z.1
      ((origin pair.2).1, (pair.1, (origin pair.2).2))
    let active := originalSurvivorCoinRestriction preCoins preRounds
      s.nextLabel basePending z.2
    firstExitRoundSplit s pending threshold old
        (pendingCoinExtension s.nextLabel pending active) =
      manuscriptSurvivorPairStop s threshold preCoins preRounds
        basePending origin z := by
  let pending := pendingAfter preCoins preRounds s.nextLabel basePending
  let old := fun pair : Nat × Nat => z.1
    ((origin pair.2).1, (pair.1, (origin pair.2).2))
  let active := originalSurvivorCoinRestriction preCoins preRounds
    s.nextLabel basePending z.2
  let fresh : Nat × Nat → Bool := fun pair =>
    z.2 (pair.1, s.nextLabel +
      manuscriptSurvivorRelabel preCoins preRounds s.nextLabel
        basePending (pair.2 - s.nextLabel))
  have hread : manuscriptSurvivorPairRead preCoins preRounds
      s.nextLabel basePending origin z =
      mergeCoinsAtLabel s.nextLabel old fresh := rfl
  have hcoin (r i : Nat) (hi : i < pending) :
      pendingCoinExtension s.nextLabel pending active
        (r, s.nextLabel + i) =
      fresh (r, s.nextLabel + i) := by
    let k : Fin pending := ⟨i, hi⟩
    rw [pendingCoinExtension_at s.nextLabel pending r i hi]
    change active (r, k) = fresh (r, s.nextLabel + i)
    have hrel := manuscriptSurvivorRelabel_active preCoins preRounds
      s.nextLabel basePending k
    simpa [active, fresh, originalSurvivorCoinRestriction, k,
      Nat.add_sub_cancel_left] using
      congrArg (fun j => z.2 (r, s.nextLabel + j)) hrel.symm
  calc
    firstExitRoundSplit s pending threshold old
        (pendingCoinExtension s.nextLabel pending active) =
      firstExitRoundSplit s pending threshold old fresh :=
        firstExitRoundSplit_fresh_coins_congr s pending threshold old
          _ _ hcoin
    _ = ttcPseudocode.secondLoopExitRound s pending threshold
        (manuscriptSurvivorPairRead preCoins preRounds s.nextLabel
          basePending origin z) := by
      rw [hread]
      exact (firstExitRound_mergeCoinsAtLabel s pending threshold old fresh
        hfresh).symm

noncomputable def manuscriptSurvivorPairFullObservation
    {n : Nat} (s : TTCState n) (threshold : Real)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat)
    (origin : Nat → Nat × Nat)
    (z : (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool)) :
    Nat × ((Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool)) :=
  let stop := manuscriptSurvivorPairStop s threshold preCoins preRounds
    basePending origin z
  (stop, (manuscriptGlobalSourcePrefix stop z.1,
    coinPrefix stop z.2))

theorem thinningResultSplitFinite_eq_of_fullObservation_eq
    {n : Nat} (s : TTCState n) (threshold : Real)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat)
    (origin : Nat → Nat × Nat)
    (a b : (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool))
    (hfresh : s.LabelsFresh)
    (hobs : manuscriptSurvivorPairFullObservation s threshold preCoins
        preRounds basePending origin a =
      manuscriptSurvivorPairFullObservation s threshold preCoins
        preRounds basePending origin b) :
    let pending := pendingAfter preCoins preRounds s.nextLabel basePending
    let old := fun z : (Nat × (Nat × Nat) → Bool) ×
        (Nat × Nat → Bool) => fun pair : Nat × Nat => z.1
      ((origin pair.2).1, (pair.1, (origin pair.2).2))
    let active := fun z => originalSurvivorCoinRestriction preCoins
      preRounds s.nextLabel basePending z.2
    thinningResultSplitFinite s pending threshold (old a) (active a) =
      thinningResultSplitFinite s pending threshold (old b) (active b) := by
  let pending := pendingAfter preCoins preRounds s.nextLabel basePending
  let read := manuscriptSurvivorPairRead preCoins preRounds s.nextLabel
    basePending origin
  let stop := manuscriptSurvivorPairStop s threshold preCoins preRounds
    basePending origin
  have hstop : stop a = stop b :=
    congrArg Prod.fst hobs
  have hsource :
      (manuscriptGlobalSourcePrefix (stop a) a.1,
        coinPrefix (stop a) a.2) =
      (manuscriptGlobalSourcePrefix (stop a) b.1,
        coinPrefix (stop a) b.2) := by
    have h := congrArg Prod.snd hobs
    change (manuscriptGlobalSourcePrefix (stop a) a.1,
        coinPrefix (stop a) a.2) =
      (manuscriptGlobalSourcePrefix (stop b) b.1,
        coinPrefix (stop b) b.2) at h
    rwa [← hstop] at h
  have hread : coinPrefix (stop a) (read a) =
      coinPrefix (stop a) (read b) :=
    manuscriptSurvivorPairRead_prefix_eq_of_fullPrefixes preCoins
      preRounds s.nextLabel basePending origin a b (stop a)
      (congrArg Prod.fst hsource) (congrArg Prod.snd hsource)
  have hresult : ttcPseudocode.secondLoopResult s pending threshold (read a) =
      ttcPseudocode.secondLoopResult s pending threshold (read b) :=
    thinningResult_eq_of_stop_and_prefix_eq s pending threshold
      (read a) (read b) hstop hread
  calc
    thinningResultSplitFinite s pending threshold
        (fun pair => a.1 ((origin pair.2).1,
          (pair.1, (origin pair.2).2)))
        (originalSurvivorCoinRestriction preCoins preRounds
          s.nextLabel basePending a.2) =
      ttcPseudocode.secondLoopResult s pending threshold (read a) :=
        thinningResultSplitFinite_pairRead s threshold preCoins
          preRounds basePending origin a hfresh
    _ = ttcPseudocode.secondLoopResult s pending threshold (read b) := hresult
    _ = thinningResultSplitFinite s pending threshold
        (fun pair => b.1 ((origin pair.2).1,
          (pair.1, (origin pair.2).2)))
        (originalSurvivorCoinRestriction preCoins preRounds
          s.nextLabel basePending b.2) :=
        (thinningResultSplitFinite_pairRead s threshold preCoins
          preRounds basePending origin b hfresh).symm

theorem measurable_manuscriptSurvivorPairFullObservation
    {n : Nat} (s : TTCState n) (threshold : Real)
    (preCoins : Nat × Nat → Bool) (preRounds basePending : Nat)
    (origin : Nat → Nat × Nat) :
    Measurable (manuscriptSurvivorPairFullObservation s threshold
      preCoins preRounds basePending origin) := by
  have hstop := measurable_manuscriptSurvivorPairStop s threshold
    preCoins preRounds basePending origin
  have hold : Measurable
      (fun z : Nat × (Nat × (Nat × Nat) → Bool) =>
        manuscriptGlobalSourcePrefix z.1 z.2) := by
    apply measurable_from_prod_countable_right
    intro rounds
    exact measurable_manuscriptGlobalSourcePrefix rounds
  have hfresh : Measurable
      (fun z : Nat × (Nat × Nat → Bool) => coinPrefix z.1 z.2) := by
    apply measurable_from_prod_countable_right
    intro rounds
    exact measurable_coinPrefix rounds
  exact hstop.prodMk
    ((hold.comp (hstop.prodMk measurable_fst)).prodMk
      (hfresh.comp (hstop.prodMk measurable_snd)))

/-- The complete old/new source prefixes at the adaptive second-loop stop
are independent of the complete shifted old/new source tails. -/
theorem manuscriptSurvivorPair_fullPrefix_tail_product
    {n : Nat} (s : TTCState n) (threshold : Real)
    (hthreshold : 0 ≤ threshold)
    (preCoins : Nat × Nat → Bool) (preRounds basePending processed : Nat)
    (origin : Nat → Nat × Nat)
    (hhistory : ManuscriptOriginHistory s.nextLabel processed origin) :
    let μ := (Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod fairCoinStreamLaw
    let obs := manuscriptSurvivorPairFullObservation s threshold preCoins
      preRounds basePending origin
    let tail := manuscriptSurvivorPairRemaining s threshold preCoins
      preRounds basePending origin
    μ.map (fun z => (obs z, tail z)) = (μ.map obs).prod μ := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  let μ := sourceLaw.prod fairCoinStreamLaw
  let joint : (Nat × Nat → Bool) →
      (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool) :=
    fun coins => (manuscriptJointOldRead coins,
      manuscriptJointFreshRead coins)
  let read := manuscriptJointSurvivorRead preCoins preRounds s.nextLabel
    basePending origin
  let pending := pendingAfter preCoins preRounds s.nextLabel basePending
  let stop : (Nat × Nat → Bool) → Nat :=
    fun coins => ttcPseudocode.secondLoopExitRound s pending threshold (read coins)
  let rawObs : (Nat × Nat → Bool) → Nat × (Nat × Nat → Bool) :=
    fun coins => (stop coins, coinPrefix (stop coins) coins)
  let project : (Nat × (Nat × Nat → Bool)) →
      Nat × ((Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool)) :=
    fun o => (o.1, (manuscriptJointOldRead o.2,
      manuscriptJointFreshRead o.2))
  let obs := manuscriptSurvivorPairFullObservation s threshold preCoins
    preRounds basePending origin
  let tail := manuscriptSurvivorPairRemaining s threshold preCoins
    preRounds basePending origin
  let rawTail : (Nat × Nat → Bool) →
      (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool) :=
    fun coins =>
      (manuscriptJointOldRead (shiftCoins (stop coins) coins),
        manuscriptJointFreshRead (shiftCoins (stop coins) coins))
  have hjoint : Measurable joint := measurable_manuscriptJointRead
  have hobs : Measurable obs :=
    measurable_manuscriptSurvivorPairFullObservation s threshold preCoins
      preRounds basePending origin
  have htail : Measurable tail :=
    measurable_manuscriptSurvivorPairRemaining s threshold preCoins
      preRounds basePending origin
  have hproject : Measurable project :=
    measurable_fst.prodMk
      (measurable_manuscriptJointRead.comp measurable_snd)
  have hsourcePair : fairCoinStreamLaw.map joint = μ :=
    fairCoinStreamLaw_jointRead
  have hobsjoint (coins : Nat × Nat → Bool) :
      obs (joint coins) = project (rawObs coins) := by
    simp only [obs, manuscriptSurvivorPairFullObservation,
      manuscriptSurvivorPairStop, manuscriptSurvivorPairRead_jointRead,
      joint, rawObs, project, stop, read, pending]
    rw [manuscriptJointOldRead_fullPrefix,
      manuscriptJointFreshRead_fullPrefix]
  have htailjoint (coins : Nat × Nat → Bool) :
      tail (joint coins) = rawTail coins := by
    simp only [tail, manuscriptSurvivorPairRemaining,
      manuscriptSurvivorPairStop, manuscriptSurvivorPairRead_jointRead,
      joint, rawTail, stop, read, pending]
    exact manuscriptSurvivorPairTail_jointRead (stop coins) coins
  have hrawObs : Measurable rawObs := by
    have hstop : Measurable stop :=
      (measurable_firstExitRound s pending threshold).comp
        (measurable_manuscriptJointSurvivorRead preCoins preRounds
          s.nextLabel basePending origin)
    have hprefixJoint : Measurable
        (fun z : Nat × (Nat × Nat → Bool) => coinPrefix z.1 z.2) := by
      apply measurable_from_prod_countable_right
      intro rounds
      exact measurable_coinPrefix rounds
    exact hstop.prodMk (hprefixJoint.comp
      (hstop.prodMk measurable_id))
  have hrawTail : Measurable rawTail := by
    have heq : rawTail = tail ∘ joint := by
      funext coins
      exact (htailjoint coins).symm
    rw [heq]
    exact htail.comp hjoint
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  letI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
    fun _ => fairCoinLaw_isProbabilityMeasure
  letI : IsProbabilityMeasure sourceLaw := by
    dsimp [sourceLaw]
    infer_instance
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  letI : IsProbabilityMeasure (fairCoinStreamLaw.map rawObs) :=
    Measure.isProbabilityMeasure_map hrawObs.aemeasurable
  have hsingle : fairCoinStreamLaw.map (fun coins =>
        (rawObs coins, rawTail coins)) =
      (fairCoinStreamLaw.map rawObs).prod μ := by
    exact manuscriptJointSurvivorRead_stoppedRoundPrefix_jointTail_law
      s threshold hthreshold preCoins preRounds basePending processed
        origin hhistory
  have hprojectMap : Measurable
      (fun z : (Nat × (Nat × Nat → Bool)) ×
          ((Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool)) =>
        (project z.1, z.2)) :=
    (hproject.comp measurable_fst).prodMk measurable_snd
  have hobsmap : (fairCoinStreamLaw.map rawObs).map project =
      μ.map obs := by
    calc
      _ = fairCoinStreamLaw.map (project ∘ rawObs) :=
        Measure.map_map hproject hrawObs
      _ = fairCoinStreamLaw.map (obs ∘ joint) := by
        exact congrArg (fun f => fairCoinStreamLaw.map f)
          (funext fun coins => (hobsjoint coins).symm)
      _ = μ.map obs := by
        rw [← hsourcePair, Measure.map_map hobs hjoint]
  calc
    μ.map (fun z => (obs z, tail z)) =
        fairCoinStreamLaw.map (fun coins =>
          (obs (joint coins), tail (joint coins))) := by
      rw [← hsourcePair, Measure.map_map (hobs.prodMk htail) hjoint]
      rfl
    _ = fairCoinStreamLaw.map (fun coins =>
          (project (rawObs coins), rawTail coins)) := by
      exact congrArg (fun f => fairCoinStreamLaw.map f)
        (funext fun coins => Prod.ext (hobsjoint coins)
          (htailjoint coins))
    _ = (fairCoinStreamLaw.map (fun coins =>
          (rawObs coins, rawTail coins))).map
            (fun z => (project z.1, z.2)) := by
      rw [Measure.map_map hprojectMap (hrawObs.prodMk hrawTail)]
      rfl
    _ = ((fairCoinStreamLaw.map rawObs).prod μ).map
          (fun z => (project z.1, z.2)) := by rw [hsingle]
    _ = ((fairCoinStreamLaw.map rawObs).map project).prod μ := by
      change ((fairCoinStreamLaw.map rawObs).prod μ).map
          (Prod.map project id) = _
      simpa only [Measure.map_id] using
        (Measure.map_prod_map (fairCoinStreamLaw.map rawObs) μ
          hproject measurable_id).symm
    _ = (μ.map obs).prod μ := by
      rw [hobsmap]

/-- The first loop's fixed old-source prefix and both complete source prefixes
at the second loop's adaptive stop are jointly independent of the remaining
old/new source pair. -/
theorem manuscriptFirstAndSecondFullPrefix_tail_product
    {n : Nat} (s : TTCState n) (threshold : Real)
    (hthreshold : 0 ≤ threshold)
    (preCoins : Nat × Nat → Bool)
    (rounds preRounds basePending processed : Nat)
    (origin : Nat → Nat × Nat)
    (hhistory : ManuscriptOriginHistory s.nextLabel processed origin) :
    let sourceLaw := Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw)
    let μ := sourceLaw.prod fairCoinStreamLaw
    let obs := manuscriptSurvivorPairFullObservation s threshold preCoins
      preRounds basePending origin
    let tail := manuscriptSurvivorPairRemaining s threshold preCoins
      preRounds basePending origin
    μ.map (fun z =>
      ((manuscriptGlobalSourcePrefix rounds z.1,
          obs (manuscriptGlobalSourceShift rounds z.1, z.2)),
        tail (manuscriptGlobalSourceShift rounds z.1, z.2))) =
      ((sourceLaw.map (manuscriptGlobalSourcePrefix rounds)).prod
        (μ.map obs)).prod μ := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  let μ := sourceLaw.prod fairCoinStreamLaw
  let pre := fun z : (Nat × (Nat × Nat) → Bool) ×
      (Nat × Nat → Bool) => manuscriptGlobalSourcePrefix rounds z.1
  let post := fun z : (Nat × (Nat × Nat) → Bool) ×
      (Nat × Nat → Bool) =>
    (manuscriptGlobalSourceShift rounds z.1, z.2)
  let obs := manuscriptSurvivorPairFullObservation s threshold preCoins
    preRounds basePending origin
  let tail := manuscriptSurvivorPairRemaining s threshold preCoins
    preRounds basePending origin
  have hpre : Measurable pre :=
    (measurable_manuscriptGlobalSourcePrefix rounds).comp measurable_fst
  have hpost : Measurable post :=
    ((measurable_manuscriptGlobalSourceShift rounds).comp
      measurable_fst).prodMk measurable_snd
  have hobs : Measurable obs :=
    measurable_manuscriptSurvivorPairFullObservation s threshold preCoins
      preRounds basePending origin
  have htail : Measurable tail :=
    measurable_manuscriptSurvivorPairRemaining s threshold preCoins
      preRounds basePending origin
  letI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
    fun _ => fairCoinLaw_isProbabilityMeasure
  letI : IsProbabilityMeasure sourceLaw := by
    dsimp [sourceLaw]
    infer_instance
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  letI : IsProbabilityMeasure
      (sourceLaw.map (manuscriptGlobalSourcePrefix rounds)) :=
    Measure.isProbabilityMeasure_map
      (measurable_manuscriptGlobalSourcePrefix rounds).aemeasurable
  letI : IsProbabilityMeasure (μ.map obs) :=
    Measure.isProbabilityMeasure_map hobs.aemeasurable
  have hfirst : μ.map (fun z => (pre z, post z)) =
      (sourceLaw.map (manuscriptGlobalSourcePrefix rounds)).prod μ :=
    manuscriptGlobalSource_prefix_with_fresh_law rounds
  have hsecond : μ.map (fun y => (obs y, tail y)) =
      (μ.map obs).prod μ :=
    manuscriptSurvivorPair_fullPrefix_tail_product s threshold
      hthreshold preCoins preRounds basePending processed origin hhistory
  exact measure_twoStage_source_product μ
    (sourceLaw.map (manuscriptGlobalSourcePrefix rounds)) μ
    (μ.map obs) μ pre post obs tail hpre hpost hobs htail
    hfirst hsecond

end Kr25Ssmxt
