import Kr25Ssmxt.Analysis.MathlibCompat
import Kr25Ssmxt.Analysis.ManuscriptAdaptiveSourceBind

/-! The fair tail after the actual thinning stop is independent of all coins
observed up to that stop, not merely of the stopping round. -/

namespace Kr25Ssmxt

open MeasureTheory Function

noncomputable def stoppedCoinPrefix {n : Nat} (s : TTCState n) (pending : Nat)
    (threshold : Real) (coins : Nat × Nat → Bool) : Nat × Nat → Bool :=
  coinPrefix (firstExitRound s pending threshold coins) coins

theorem measurable_stoppedCoinPrefix {n : Nat} (s : TTCState n)
    (pending : Nat) (threshold : Real) :
    Measurable (stoppedCoinPrefix s pending threshold) := by
  have hprefix : Measurable
      (fun z : Nat × (Nat × Nat → Bool) => coinPrefix z.1 z.2) := by
    apply measurable_from_prod_countable_right
    intro rounds
    exact measurable_coinPrefix rounds
  exact hprefix.comp
    ((measurable_firstExitRound s pending threshold).prodMk measurable_id)

theorem firstExitRound_stoppedPrefix_shift_law {n : Nat}
    (s : TTCState n) (pending : Nat) (threshold : Real)
    (hthreshold : 0 ≤ threshold) :
    fairCoinStreamLaw.map
      (fun coins =>
        (stoppedCoinPrefix s pending threshold coins,
          shiftCoins (firstExitRound s pending threshold coins) coins)) =
    (fairCoinStreamLaw.map (stoppedCoinPrefix s pending threshold)).prod
      fairCoinStreamLaw := by
  classical
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  let stop := firstExitRound s pending threshold
  let observed := stoppedCoinPrefix s pending threshold
  let output : (Nat × Nat → Bool) →
      (Nat × Nat → Bool) × (Nat × Nat → Bool) :=
    fun coins => (observed coins, shiftCoins (stop coins) coins)
  have houtput : Measurable output :=
    (measurable_stoppedCoinPrefix s pending threshold).prodMk
      ((measurable_stoppedCoinPair stop
        (measurable_firstExitRound s pending threshold)).snd)
  letI : IsProbabilityMeasure (fairCoinStreamLaw.map output) :=
    Measure.isProbabilityMeasure_map houtput.aemeasurable
  apply Measure.ext_prod
  intro A B hA hB
  let fiber (r : Nat) : Set (Nat × Nat → Bool) :=
    {coins | stop coins = r}
  let F (r : Nat) : Set (Nat × Nat → Bool) :=
    fiber r ∩ (coinPrefix r) ⁻¹' A
  let E (r : Nat) : Set (Nat × Nat → Bool) :=
    F r ∩ (shiftCoins r) ⁻¹' B
  have hfiber (r : Nat) : MeasurableSet (fiber r) :=
    (measurableSet_singleton r).preimage
      (measurable_firstExitRound s pending threshold)
  have hF (r : Nat) : MeasurableSet (F r) :=
    (hfiber r).inter (hA.preimage (measurable_coinPrefix r))
  have hE (r : Nat) : MeasurableSet (E r) :=
    (hF r).inter (hB.preimage
      (Measurable.of_eval (fun index =>
        measurable_pi_apply (index.1 + r, index.2))))
  have hdisjF : Pairwise (Disjoint on F) := by
    intro r q hrq
    apply Set.disjoint_left.mpr
    intro coins hr hq
    have her : stop coins = r := hr.1
    have heq : stop coins = q := hq.1
    exact hrq (her.symm.trans heq)
  have hdisjE : Pairwise (Disjoint on E) := by
    intro r q hrq
    exact (hdisjF hrq).mono (Set.inter_subset_left) (Set.inter_subset_left)
  have hF_union : (⋃ r, F r) = observed ⁻¹' A := by
    ext coins
    simp only [Set.mem_iUnion, Set.mem_preimage, F, fiber,
      Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨r, hr, hApre⟩
      simpa [observed, stoppedCoinPrefix, stop, hr] using hApre
    · intro hApre
      exact ⟨stop coins, rfl, hApre⟩
  have hE_union : (⋃ r, E r) = output ⁻¹' (A ×ˢ B) := by
    ext coins
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_prod,
      E, F, fiber, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨r, ⟨hr, ha⟩, hb⟩
      simpa [output, observed, stoppedCoinPrefix, stop, hr] using
        (show coinPrefix r coins ∈ A ∧ shiftCoins r coins ∈ B from ⟨ha, hb⟩)
    · rintro ⟨ha, hb⟩
      exact ⟨stop coins, ⟨rfl, ha⟩, hb⟩
  have hterm (r : Nat) :
      fairCoinStreamLaw (E r) =
        fairCoinStreamLaw (F r) * fairCoinStreamLaw B := by
    let G : Set (Nat × Nat → Bool) :=
      firstExitPrefixEvent s pending threshold r ∩
        (coinPrefix r) ⁻¹' A
    have hG : MeasurableSet G :=
      (measurableSet_firstExitPrefixEvent s pending threshold r).inter
        (hA.preimage (measurable_coinPrefix r))
    have hprefixG : (coinPrefix r) ⁻¹' G = G := by
      ext coins
      simp only [Set.mem_preimage, G, Set.mem_inter_iff]
      have hEvent : coinPrefix r coins ∈
          firstExitPrefixEvent s pending threshold r ↔
          coins ∈ firstExitPrefixEvent s pending threshold r :=
        Set.ext_iff.mp
          (firstExitPrefixEvent_preimage s pending threshold r) coins
      have hprefixId : coinPrefix r (coinPrefix r coins) =
          coinPrefix r coins := by
        funext index
        simp [coinPrefix]
      simpa only [hprefixId] using and_congr hEvent Iff.rfl
    have hae := firstExitRound_eq_prefix_event_ae s pending threshold
      hthreshold r
    have hF_eq : fairCoinStreamLaw (F r) = fairCoinStreamLaw G := by
      apply measure_congr
      filter_upwards [hae] with coins hc
      exact propext (and_congr hc Iff.rfl)
    have hE_eq : fairCoinStreamLaw (E r) =
        fairCoinStreamLaw (G ∩ (shiftCoins r) ⁻¹' B) := by
      apply measure_congr
      filter_upwards [hae] with coins hc
      exact propext (and_congr (and_congr hc Iff.rfl) Iff.rfl)
    rw [hE_eq, ← hprefixG]
    rw [fairCoinStreamLaw_prefix_shift_indep r G B hG hB]
    rw [hprefixG, ← hF_eq]
  have hF_measure : fairCoinStreamLaw (observed ⁻¹' A) =
      ∑' r, fairCoinStreamLaw (F r) := by
    rw [← hF_union]
    exact measure_iUnion hdisjF hF
  have hE_measure : fairCoinStreamLaw (output ⁻¹' (A ×ˢ B)) =
      ∑' r, fairCoinStreamLaw (E r) := by
    rw [← hE_union]
    exact measure_iUnion hdisjE hE
  rw [Measure.map_apply houtput (hA.prod hB), hE_measure]
  rw [Measure.prod_prod,
    Measure.map_apply (measurable_stoppedCoinPrefix s pending threshold)
      hA, hF_measure]
  simp_rw [hterm]
  simp only [mul_comm (fairCoinStreamLaw (F _)) (fairCoinStreamLaw B)]
  rw [ENNReal.tsum_mul_left, mul_comm]

/-- The entire future component/original-label source is independent of the
coins observed before the first-exit stopping round. -/
theorem firstExitRound_stoppedPrefix_globalFuture_law {n : Nat}
    (s : TTCState n) (pending : Nat) (threshold : Real)
    (hthreshold : 0 ≤ threshold) :
    fairCoinStreamLaw.map
      (fun coins =>
        (stoppedCoinPrefix s pending threshold coins,
          manuscriptGlobalCoinRead
            (shiftCoins (firstExitRound s pending threshold coins) coins))) =
    (fairCoinStreamLaw.map
      (stoppedCoinPrefix s pending threshold)).prod
      (Measure.infinitePi
        (fun _ : Nat × (Nat × Nat) => fairCoinLaw)) := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  let observed := stoppedCoinPrefix s pending threshold
  let stop := firstExitRound s pending threshold
  let reindex : ((Nat × Nat → Bool) × (Nat × Nat → Bool)) →
      (Nat × Nat → Bool) × (Nat × (Nat × Nat) → Bool) :=
    Prod.map id manuscriptGlobalCoinRead
  have hreindex : Measurable reindex :=
    measurable_fst.prodMk
      (measurable_manuscriptGlobalCoinRead.comp measurable_snd)
  have hsplit : Measurable
      (fun coins => (observed coins, shiftCoins (stop coins) coins)) :=
    (measurable_stoppedCoinPrefix s pending threshold).prodMk
      ((measurable_stoppedCoinPair stop
        (measurable_firstExitRound s pending threshold)).snd)
  calc
    fairCoinStreamLaw.map
        (fun coins =>
          (observed coins,
            manuscriptGlobalCoinRead (shiftCoins (stop coins) coins))) =
      (fairCoinStreamLaw.map
        (fun coins => (observed coins, shiftCoins (stop coins) coins))).map
          reindex := by
            rw [Measure.map_map hreindex hsplit]
            rfl
    _ = ((fairCoinStreamLaw.map observed).prod fairCoinStreamLaw).map
          reindex := by
            rw [firstExitRound_stoppedPrefix_shift_law s pending threshold
              hthreshold]
    _ = ((fairCoinStreamLaw.map observed).map id).prod
          (fairCoinStreamLaw.map manuscriptGlobalCoinRead) := by
            exact (Measure.map_prod_map _ fairCoinStreamLaw measurable_id
              measurable_manuscriptGlobalCoinRead).symm
    _ = _ := by
      rw [Measure.map_id, fairCoinStreamLaw_globalCoinRead]

/-- The stopped history may choose the origin map and allocated-label count.
The old-copy future coins still supply a fresh fair block to any measurable
randomized continuation. -/
theorem firstExitRound_stoppedPrefix_originFuture_bind
    {n : Nat} (s : TTCState n) (pending : Nat) (threshold : Real)
    (hthreshold : 0 ≤ threshold)
    {β : Type*} [MeasurableSpace β]
    (nextLabel processed : (Nat × Nat → Bool) → Nat)
    (origin : (Nat × Nat → Bool) → Nat → Nat × Nat)
    (hhistory : ∀ᵐ pre ∂fairCoinStreamLaw.map
      (stoppedCoinPrefix s pending threshold),
      ManuscriptOriginHistory (nextLabel pre) (processed pre)
        (origin pre))
    (K : (pre : Nat × Nat → Bool) →
      (Nat × Fin (nextLabel pre) → Bool) → Measure β)
    (hK : ∀ pre, Measurable (K pre))
    (hjoint : Measurable
      (fun z : (Nat × Nat → Bool) × (Nat × (Nat × Nat) → Bool) =>
        K z.1 (fun pair => z.2
          (manuscriptOriginCoinIndex (nextLabel z.1) (origin z.1) pair)))) :
    fairCoinStreamLaw.bind (fun coins =>
      let pre := stoppedCoinPrefix s pending threshold coins
      K pre (fun pair =>
        manuscriptGlobalCoinRead
          (shiftCoins (firstExitRound s pending threshold coins) coins)
          (manuscriptOriginCoinIndex (nextLabel pre)
            (origin pre) pair))) =
    (fairCoinStreamLaw.map
      (stoppedCoinPrefix s pending threshold)).bind (fun pre =>
        (Measure.infinitePi
          (fun _ : Nat × Fin (nextLabel pre) => fairCoinLaw)).bind
          (K pre)) := by
  let observed := stoppedCoinPrefix s pending threshold
  let stop := firstExitRound s pending threshold
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  let preLaw := fairCoinStreamLaw.map observed
  let split : (Nat × Nat → Bool) →
      (Nat × Nat → Bool) × (Nat × (Nat × Nat) → Bool) :=
    fun coins => (observed coins,
      manuscriptGlobalCoinRead (shiftCoins (stop coins) coins))
  have hsplit : Measurable split :=
    (measurable_stoppedCoinPrefix s pending threshold).prodMk
      (measurable_manuscriptGlobalCoinRead.comp
        ((measurable_stoppedCoinPair stop
          (measurable_firstExitRound s pending threshold)).snd))
  let joint : ((Nat × Nat → Bool) × (Nat × (Nat × Nat) → Bool)) →
      Measure β := fun z => K z.1 (fun pair => z.2
        (manuscriptOriginCoinIndex (nextLabel z.1) (origin z.1) pair))
  have hjoint' : Measurable joint := hjoint
  have hpreSource : Measurable (fun pre : Nat × Nat → Bool =>
      sourceLaw.map (Prod.mk pre)) := by
    letI : IsProbabilityMeasure sourceLaw := by
      dsimp [sourceLaw]
      letI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
        fun _ => fairCoinLaw_isProbabilityMeasure
      infer_instance
    exact Measurable.map_prodMk_left
  calc
    fairCoinStreamLaw.bind (fun coins =>
        K (observed coins) (fun pair =>
          manuscriptGlobalCoinRead (shiftCoins (stop coins) coins)
            (manuscriptOriginCoinIndex (nextLabel (observed coins))
              (origin (observed coins)) pair))) =
      (fairCoinStreamLaw.map split).bind joint := by
        exact (bind_mapped_measure fairCoinStreamLaw split hsplit joint
          hjoint').symm
    _ = (preLaw.prod sourceLaw).bind joint := by
      rw [firstExitRound_stoppedPrefix_globalFuture_law s pending
        threshold hthreshold]
    _ = preLaw.bind (fun pre =>
        sourceLaw.bind fun source => joint (pre, source)) := by
      haveI : IsProbabilityMeasure sourceLaw := by
        dsimp [sourceLaw]
        haveI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
          fun _ => fairCoinLaw_isProbabilityMeasure
        infer_instance
      rw [Measure.prod_eq_bind_map]
      rw [Measure.bind_bind hpreSource.aemeasurable
        hjoint'.aemeasurable]
      congr 1
      funext pre
      exact bind_mapped_measure sourceLaw (Prod.mk pre)
        measurable_prodMk_left joint hjoint'
    _ = _ := manuscript_origin_futureCoins_adaptive_bind preLaw
      nextLabel processed origin hhistory K hK

/-- The merged old/new thinning loop has the same stopped-prefix independence
law as a single fair stream. -/
theorem firstExitRoundSplit_stoppedPrefix_shift_law {n : Nat}
    (s : TTCState n) (pending : Nat) (threshold : Real)
    (hthreshold : 0 ≤ threshold) (hfresh : s.LabelsFresh) :
    (fairCoinStreamLaw.prod fairCoinStreamLaw).map
      (fun pair =>
        let merged := mergeCoinsAtLabel s.nextLabel pair.1 pair.2
        let rounds := firstExitRoundSplit s pending threshold pair.1 pair.2
        (coinPrefix rounds merged, shiftCoins rounds merged)) =
    ((fairCoinStreamLaw.prod fairCoinStreamLaw).map
      (fun pair =>
        coinPrefix (firstExitRoundSplit s pending threshold pair.1 pair.2)
          (mergeCoinsAtLabel s.nextLabel pair.1 pair.2))).prod
      fairCoinStreamLaw := by
  let merge : ((Nat × Nat → Bool) × (Nat × Nat → Bool)) →
      Nat × Nat → Bool := fun pair =>
    mergeCoinsAtLabel s.nextLabel pair.1 pair.2
  let H : (Nat × Nat → Bool) →
      (Nat × Nat → Bool) × (Nat × Nat → Bool) :=
    fun coins =>
      (stoppedCoinPrefix s pending threshold coins,
        shiftCoins (firstExitRound s pending threshold coins) coins)
  have hmerge : Measurable merge :=
    measurable_mergeCoinsAtLabel_pair s.nextLabel
  have hH : Measurable H :=
    (measurable_stoppedCoinPrefix s pending threshold).prodMk
      ((measurable_stoppedCoinPair
        (firstExitRound s pending threshold)
        (measurable_firstExitRound s pending threshold)).snd)
  have hpath (pair : (Nat × Nat → Bool) × (Nat × Nat → Bool)) :
      firstExitRoundSplit s pending threshold pair.1 pair.2 =
        firstExitRound s pending threshold (merge pair) :=
    (firstExitRound_mergeCoinsAtLabel s pending threshold pair.1 pair.2
      hfresh).symm
  have hleft : (fairCoinStreamLaw.prod fairCoinStreamLaw).map
        (fun pair =>
          let merged := merge pair
          let rounds := firstExitRoundSplit s pending threshold pair.1 pair.2
          (coinPrefix rounds merged, shiftCoins rounds merged)) =
      fairCoinStreamLaw.map H := by
    calc
      _ = (fairCoinStreamLaw.prod fairCoinStreamLaw).map (H ∘ merge) := by
        congr 1
        funext pair
        simp only [Function.comp_apply, H, stoppedCoinPrefix, hpath pair]
      _ = ((fairCoinStreamLaw.prod fairCoinStreamLaw).map merge).map H := by
        rw [Measure.map_map hH hmerge]
      _ = _ := by rw [fairCoinStreamLaw_mergeLabels s.nextLabel]
  have hright : (fairCoinStreamLaw.prod fairCoinStreamLaw).map
        (fun pair =>
          coinPrefix (firstExitRoundSplit s pending threshold pair.1 pair.2)
            (merge pair)) =
      fairCoinStreamLaw.map
        (stoppedCoinPrefix s pending threshold) := by
    calc
      _ = (fairCoinStreamLaw.prod fairCoinStreamLaw).map
          ((stoppedCoinPrefix s pending threshold) ∘ merge) := by
            congr 1
            funext pair
            simp only [Function.comp_apply, stoppedCoinPrefix, hpath pair]
      _ = ((fairCoinStreamLaw.prod fairCoinStreamLaw).map merge).map
          (stoppedCoinPrefix s pending threshold) := by
            rw [Measure.map_map
              (measurable_stoppedCoinPrefix s pending threshold) hmerge]
      _ = _ := by rw [fairCoinStreamLaw_mergeLabels s.nextLabel]
  rw [hleft, hright]
  exact firstExitRound_stoppedPrefix_shift_law s pending threshold
    hthreshold

/-- The merged old/new thinning loop has the same stopped-prefix independence
law as a single fair stream, after reindexing its tail by source tags. -/
theorem firstExitRoundSplit_stoppedPrefix_globalFuture_law {n : Nat}
    (s : TTCState n) (pending : Nat) (threshold : Real)
    (hthreshold : 0 ≤ threshold) (hfresh : s.LabelsFresh) :
    (fairCoinStreamLaw.prod fairCoinStreamLaw).map
      (fun pair =>
        let merged := mergeCoinsAtLabel s.nextLabel pair.1 pair.2
        let rounds := firstExitRoundSplit s pending threshold pair.1 pair.2
        (coinPrefix rounds merged,
          manuscriptGlobalCoinRead (shiftCoins rounds merged))) =
    ((fairCoinStreamLaw.prod fairCoinStreamLaw).map
      (fun pair =>
        coinPrefix (firstExitRoundSplit s pending threshold pair.1 pair.2)
          (mergeCoinsAtLabel s.nextLabel pair.1 pair.2))).prod
      (Measure.infinitePi
        (fun _ : Nat × (Nat × Nat) => fairCoinLaw)) := by
  let merge : ((Nat × Nat → Bool) × (Nat × Nat → Bool)) →
      Nat × Nat → Bool := fun pair =>
    mergeCoinsAtLabel s.nextLabel pair.1 pair.2
  let H : (Nat × Nat → Bool) →
      (Nat × Nat → Bool) × (Nat × (Nat × Nat) → Bool) :=
    fun coins =>
      (stoppedCoinPrefix s pending threshold coins,
        manuscriptGlobalCoinRead
          (shiftCoins (firstExitRound s pending threshold coins) coins))
  have hmerge : Measurable merge :=
    measurable_mergeCoinsAtLabel_pair s.nextLabel
  have hH : Measurable H :=
    (measurable_stoppedCoinPrefix s pending threshold).prodMk
      (measurable_manuscriptGlobalCoinRead.comp
        ((measurable_stoppedCoinPair
          (firstExitRound s pending threshold)
          (measurable_firstExitRound s pending threshold)).snd))
  have hpath (pair : (Nat × Nat → Bool) × (Nat × Nat → Bool)) :
      firstExitRoundSplit s pending threshold pair.1 pair.2 =
        firstExitRound s pending threshold (merge pair) :=
    (firstExitRound_mergeCoinsAtLabel s pending threshold pair.1 pair.2
      hfresh).symm
  have hleft : (fairCoinStreamLaw.prod fairCoinStreamLaw).map
        (fun pair =>
          let merged := merge pair
          let rounds := firstExitRoundSplit s pending threshold pair.1 pair.2
          (coinPrefix rounds merged,
            manuscriptGlobalCoinRead (shiftCoins rounds merged))) =
      fairCoinStreamLaw.map H := by
    calc
      _ = (fairCoinStreamLaw.prod fairCoinStreamLaw).map (H ∘ merge) := by
        congr 1
        funext pair
        simp only [Function.comp_apply, H, stoppedCoinPrefix, hpath pair]
      _ = ((fairCoinStreamLaw.prod fairCoinStreamLaw).map merge).map H := by
        rw [Measure.map_map hH hmerge]
      _ = _ := by rw [fairCoinStreamLaw_mergeLabels s.nextLabel]
  have hright : (fairCoinStreamLaw.prod fairCoinStreamLaw).map
        (fun pair =>
          coinPrefix (firstExitRoundSplit s pending threshold pair.1 pair.2)
            (merge pair)) =
      fairCoinStreamLaw.map
        (stoppedCoinPrefix s pending threshold) := by
    calc
      _ = (fairCoinStreamLaw.prod fairCoinStreamLaw).map
          ((stoppedCoinPrefix s pending threshold) ∘ merge) := by
            congr 1
            funext pair
            simp only [Function.comp_apply, stoppedCoinPrefix, hpath pair]
      _ = ((fairCoinStreamLaw.prod fairCoinStreamLaw).map merge).map
          (stoppedCoinPrefix s pending threshold) := by
            rw [Measure.map_map
              (measurable_stoppedCoinPrefix s pending threshold) hmerge]
      _ = _ := by rw [fairCoinStreamLaw_mergeLabels s.nextLabel]
  rw [hleft, hright]
  exact firstExitRound_stoppedPrefix_globalFuture_law s pending threshold
    hthreshold

/-- The actual merged old/new thinning stop supplies a fresh allocated-label
coin block to every measurable continuation chosen from its stopped history. -/
theorem firstExitRoundSplit_stoppedPrefix_originFuture_bind
    {n : Nat} (s : TTCState n) (pending : Nat) (threshold : Real)
    (hthreshold : 0 ≤ threshold) (hfresh : s.LabelsFresh)
    {β : Type*} [MeasurableSpace β]
    (nextLabel processed : (Nat × Nat → Bool) → Nat)
    (origin : (Nat × Nat → Bool) → Nat → Nat × Nat)
    (hhistory : ∀ᵐ pre ∂(fairCoinStreamLaw.prod fairCoinStreamLaw).map
      (fun pair =>
        coinPrefix (firstExitRoundSplit s pending threshold pair.1 pair.2)
          (mergeCoinsAtLabel s.nextLabel pair.1 pair.2)),
      ManuscriptOriginHistory (nextLabel pre) (processed pre)
        (origin pre))
    (K : (pre : Nat × Nat → Bool) →
      (Nat × Fin (nextLabel pre) → Bool) → Measure β)
    (hK : ∀ pre, Measurable (K pre))
    (hjoint : Measurable
      (fun z : (Nat × Nat → Bool) × (Nat × (Nat × Nat) → Bool) =>
        K z.1 (fun index => z.2
          (manuscriptOriginCoinIndex (nextLabel z.1)
            (origin z.1) index)))) :
    (fairCoinStreamLaw.prod fairCoinStreamLaw).bind (fun pair =>
      let merged := mergeCoinsAtLabel s.nextLabel pair.1 pair.2
      let rounds := firstExitRoundSplit s pending threshold pair.1 pair.2
      let pre := coinPrefix rounds merged
      K pre (fun index =>
        manuscriptGlobalCoinRead (shiftCoins rounds merged)
          (manuscriptOriginCoinIndex (nextLabel pre)
            (origin pre) index))) =
    ((fairCoinStreamLaw.prod fairCoinStreamLaw).map
      (fun pair =>
        coinPrefix (firstExitRoundSplit s pending threshold pair.1 pair.2)
          (mergeCoinsAtLabel s.nextLabel pair.1 pair.2))).bind (fun pre =>
        (Measure.infinitePi
          (fun _ : Nat × Fin (nextLabel pre) => fairCoinLaw)).bind
          (K pre)) := by
  let μ := fairCoinStreamLaw.prod fairCoinStreamLaw
  let merge : ((Nat × Nat → Bool) × (Nat × Nat → Bool)) →
      Nat × Nat → Bool := fun pair =>
    mergeCoinsAtLabel s.nextLabel pair.1 pair.2
  let stop : ((Nat × Nat → Bool) × (Nat × Nat → Bool)) → Nat :=
    fun pair => firstExitRoundSplit s pending threshold pair.1 pair.2
  let observed : ((Nat × Nat → Bool) × (Nat × Nat → Bool)) →
      Nat × Nat → Bool := fun pair => coinPrefix (stop pair) (merge pair)
  let source : ((Nat × Nat → Bool) × (Nat × Nat → Bool)) →
      Nat × (Nat × Nat) → Bool := fun pair =>
    manuscriptGlobalCoinRead (shiftCoins (stop pair) (merge pair))
  have hmerge : Measurable merge :=
    measurable_mergeCoinsAtLabel_pair s.nextLabel
  have hpath (pair : (Nat × Nat → Bool) × (Nat × Nat → Bool)) :
      stop pair = firstExitRound s pending threshold (merge pair) :=
    (firstExitRound_mergeCoinsAtLabel s pending threshold pair.1 pair.2
      hfresh).symm
  have hH : Measurable
      (fun coins =>
        (stoppedCoinPrefix s pending threshold coins,
          manuscriptGlobalCoinRead
            (shiftCoins (firstExitRound s pending threshold coins) coins))) :=
    (measurable_stoppedCoinPrefix s pending threshold).prodMk
      (measurable_manuscriptGlobalCoinRead.comp
        ((measurable_stoppedCoinPair
          (firstExitRound s pending threshold)
          (measurable_firstExitRound s pending threshold)).snd))
  have hsplit : Measurable (fun pair => (observed pair, source pair)) := by
    have heq : (fun pair => (observed pair, source pair)) =
        (fun coins =>
          (stoppedCoinPrefix s pending threshold coins,
            manuscriptGlobalCoinRead
              (shiftCoins (firstExitRound s pending threshold coins)
                coins))) ∘ merge := by
      funext pair
      simp only [Function.comp_apply, observed, source,
        stoppedCoinPrefix, hpath pair]
    rw [heq]
    exact hH.comp hmerge
  exact manuscript_independentSource_adaptive_bind μ observed source
    hsplit (firstExitRoundSplit_stoppedPrefix_globalFuture_law
      s pending threshold hthreshold hfresh)
    nextLabel processed origin hhistory K hK hjoint

end Kr25Ssmxt
