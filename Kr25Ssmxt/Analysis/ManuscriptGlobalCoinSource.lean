import Kr25Ssmxt.Analysis.MathlibCompat
import Kr25Ssmxt.Analysis.ManuscriptStoppedCoinTail
import Kr25Ssmxt.Analysis.ManuscriptOriginHistory
import Mathlib.Data.Nat.Pairing

/-! Pair the component number and original Poisson-copy label into one
global IID fair-coin stream. The first coordinate remains absolute time. -/

namespace Kr25Ssmxt

open MeasureTheory

def manuscriptGlobalCoinIndex (tag : Nat × (Nat × Nat)) : Nat × Nat :=
  (tag.2.1, Nat.pair tag.1 tag.2.2)

theorem manuscriptGlobalCoinIndex_injective :
    Function.Injective manuscriptGlobalCoinIndex := by
  intro a b hab
  change (a.2.1, Nat.pair a.1 a.2.2) =
    (b.2.1, Nat.pair b.1 b.2.2) at hab
  simp only [Prod.mk.injEq, Nat.pair_eq_pair] at hab
  obtain ⟨hround, hcomponent, hlabel⟩ := hab
  exact Prod.ext hcomponent (Prod.ext hround hlabel)

def manuscriptGlobalCoinRead (coins : Nat × Nat → Bool) :
    Nat × (Nat × Nat) → Bool :=
  fun tag => coins (manuscriptGlobalCoinIndex tag)

theorem measurable_manuscriptGlobalCoinRead :
    Measurable manuscriptGlobalCoinRead :=
  Measurable.of_eval (fun tag =>
    measurable_pi_apply (manuscriptGlobalCoinIndex tag))

/-- Independent component/original-label streams can be read from one
absolute-time fair array without changing their joint product law. -/
theorem fairCoinStreamLaw_globalCoinRead :
    fairCoinStreamLaw.map manuscriptGlobalCoinRead =
    Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw) := by
  letI : ∀ _ : Nat × Nat, IsProbabilityMeasure fairCoinLaw :=
    fun _ => fairCoinLaw_isProbabilityMeasure
  exact @Measure.map_infinitePi_infinitePi_of_inj
    (Nat × Nat) (Nat × (Nat × Nat)) (fun _ => Bool)
    (fun _ => inferInstance) (fun _ => fairCoinLaw)
    (fun _ => fairCoinLaw_isProbabilityMeasure)
    manuscriptGlobalCoinIndex manuscriptGlobalCoinIndex_injective

/-- The same component source product is available after any fixed
absolute-time shift of the global stream. -/
theorem fairCoinStreamLaw_globalCoinRead_shift (level : Nat) :
    fairCoinStreamLaw.map
      (fun coins => manuscriptGlobalCoinRead (shiftCoins level coins)) =
    Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw) := by
  have hmap : Measurable manuscriptGlobalCoinRead :=
    measurable_manuscriptGlobalCoinRead
  calc
    fairCoinStreamLaw.map
        (fun coins => manuscriptGlobalCoinRead (shiftCoins level coins)) =
      (fairCoinStreamLaw.map (shiftCoins level)).map
        manuscriptGlobalCoinRead := by
          simpa only [Function.comp_def] using
            (Measure.map_map hmap
              (Measurable.of_eval (fun index =>
                measurable_pi_apply (index.1 + level, index.2)))).symm
    _ = fairCoinStreamLaw.map manuscriptGlobalCoinRead := by
      rw [fairCoinStreamLaw_shift level]
    _ = _ := fairCoinStreamLaw_globalCoinRead

/-- The complete family of future component/original-label coins is
independent of all global coin rounds observed before a fixed level. -/
theorem fairCoinStreamLaw_prefix_globalFuture (level : Nat) :
    fairCoinStreamLaw.map
      (fun coins =>
        (coinPrefix level coins,
          manuscriptGlobalCoinRead (shiftCoins level coins))) =
    (fairCoinStreamLaw.map (coinPrefix level)).prod
      (Measure.infinitePi
        (fun _ : Nat × (Nat × Nat) => fairCoinLaw)) := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  let split : (Nat × Nat → Bool) →
      (Nat × Nat → Bool) × (Nat × Nat → Bool) :=
    fun coins => (coinPrefix level coins, shiftCoins level coins)
  have hsplit : Measurable split :=
    (measurable_coinPrefix level).prodMk
      (Measurable.of_eval (fun index =>
        measurable_pi_apply (index.1 + level, index.2)))
  let reindex : ((Nat × Nat → Bool) × (Nat × Nat → Bool)) →
      (Nat × Nat → Bool) × (Nat × (Nat × Nat) → Bool) :=
    Prod.map id manuscriptGlobalCoinRead
  have hreindex : Measurable reindex :=
    measurable_fst.prodMk
      (measurable_manuscriptGlobalCoinRead.comp measurable_snd)
  calc
    fairCoinStreamLaw.map
        (fun coins =>
          (coinPrefix level coins,
            manuscriptGlobalCoinRead (shiftCoins level coins))) =
      (fairCoinStreamLaw.map split).map reindex := by
        rw [Measure.map_map hreindex hsplit]
        rfl
    _ = ((fairCoinStreamLaw.map (coinPrefix level)).prod
        fairCoinStreamLaw).map reindex := by
          rw [fairCoinStreamLaw_prefix_shift level]
    _ = ((fairCoinStreamLaw.map (coinPrefix level)).map id).prod
        (fairCoinStreamLaw.map manuscriptGlobalCoinRead) := by
          exact (Measure.map_prod_map
            (fairCoinStreamLaw.map (coinPrefix level)) fairCoinStreamLaw
            measurable_id measurable_manuscriptGlobalCoinRead).symm
    _ = _ := by
      rw [Measure.map_id, fairCoinStreamLaw_globalCoinRead]

/-- After the manuscript's first-exit round, the entire family of future
component/original-label fair coins is independent of that round count. -/
theorem firstExitRound_globalFuture_law {n : Nat}
    (s : TTCState n) (pending : Nat) (threshold : Real)
    (hthreshold : 0 ≤ threshold) :
    fairCoinStreamLaw.map
      (fun coins =>
        let rounds := firstExitRound s pending threshold coins
        (rounds, manuscriptGlobalCoinRead (shiftCoins rounds coins))) =
    (fairCoinStreamLaw.map (firstExitRound s pending threshold)).prod
      (Measure.infinitePi
        (fun _ : Nat × (Nat × Nat) => fairCoinLaw)) := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  let stopped : (Nat × Nat → Bool) →
      Nat × (Nat × Nat → Bool) := fun coins =>
    let rounds := firstExitRound s pending threshold coins
    (rounds, shiftCoins rounds coins)
  have hstopped : Measurable stopped :=
    measurable_stoppedCoinPair _
      (measurable_firstExitRound s pending threshold)
  let reindex : (Nat × (Nat × Nat → Bool)) →
      Nat × (Nat × (Nat × Nat) → Bool) :=
    Prod.map id manuscriptGlobalCoinRead
  have hreindex : Measurable reindex :=
    measurable_fst.prodMk
      (measurable_manuscriptGlobalCoinRead.comp measurable_snd)
  calc
    fairCoinStreamLaw.map
        (fun coins =>
          let rounds := firstExitRound s pending threshold coins
          (rounds, manuscriptGlobalCoinRead (shiftCoins rounds coins))) =
      (fairCoinStreamLaw.map stopped).map reindex := by
        rw [Measure.map_map hreindex hstopped]
        rfl
    _ = ((fairCoinStreamLaw.map
        (firstExitRound s pending threshold)).prod
          fairCoinStreamLaw).map reindex := by
            rw [firstExitRound_shift_law s pending threshold hthreshold]
    _ = ((fairCoinStreamLaw.map
        (firstExitRound s pending threshold)).map id).prod
          (fairCoinStreamLaw.map manuscriptGlobalCoinRead) := by
            exact (Measure.map_prod_map
              (fairCoinStreamLaw.map
                (firstExitRound s pending threshold)) fairCoinStreamLaw
              measurable_id measurable_manuscriptGlobalCoinRead).symm
    _ = _ := by
      rw [Measure.map_id, fairCoinStreamLaw_globalCoinRead]

theorem firstExitRoundSplit_merged_globalFuture_law {n : Nat}
    (s : TTCState n) (pending : Nat) (threshold : Real)
    (hthreshold : 0 ≤ threshold) (hfresh : s.LabelsFresh) :
    (fairCoinStreamLaw.prod fairCoinStreamLaw).map
      (fun pair =>
        let rounds := firstExitRoundSplit s pending threshold pair.1 pair.2
        (rounds, manuscriptGlobalCoinRead
          (shiftCoins rounds
            (mergeCoinsAtLabel s.nextLabel pair.1 pair.2)))) =
    ((fairCoinStreamLaw.prod fairCoinStreamLaw).map
      (fun pair => firstExitRoundSplit s pending threshold pair.1 pair.2)).prod
      (Measure.infinitePi
        (fun _ : Nat × (Nat × Nat) => fairCoinLaw)) := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  let stopped : ((Nat × Nat → Bool) × (Nat × Nat → Bool)) →
      Nat × (Nat × Nat → Bool) := fun pair =>
    let rounds := firstExitRoundSplit s pending threshold pair.1 pair.2
    (rounds, shiftCoins rounds
      (mergeCoinsAtLabel s.nextLabel pair.1 pair.2))
  have hstopped : Measurable stopped := by
    let merge : ((Nat × Nat → Bool) × (Nat × Nat → Bool)) →
        Nat × Nat → Bool := fun pair =>
      mergeCoinsAtLabel s.nextLabel pair.1 pair.2
    have hmerge := measurable_mergeCoinsAtLabel_pair s.nextLabel
    have hpath : stopped =
        (fun coins =>
          (firstExitRound s pending threshold coins,
            shiftCoins (firstExitRound s pending threshold coins) coins)) ∘
          merge := by
      funext pair
      simp [stopped, merge, Function.comp_def,
        firstExitRound_mergeCoinsAtLabel s pending threshold pair.1
          pair.2 hfresh]
    rw [hpath]
    exact (measurable_stoppedCoinPair _
      (measurable_firstExitRound s pending threshold)).comp hmerge
  let reindex : (Nat × (Nat × Nat → Bool)) →
      Nat × (Nat × (Nat × Nat) → Bool) :=
    Prod.map id manuscriptGlobalCoinRead
  have hreindex : Measurable reindex :=
    measurable_fst.prodMk
      (measurable_manuscriptGlobalCoinRead.comp measurable_snd)
  calc
    (fairCoinStreamLaw.prod fairCoinStreamLaw).map
        (fun pair =>
          let rounds := firstExitRoundSplit s pending threshold pair.1 pair.2
          (rounds, manuscriptGlobalCoinRead
            (shiftCoins rounds
              (mergeCoinsAtLabel s.nextLabel pair.1 pair.2)))) =
      ((fairCoinStreamLaw.prod fairCoinStreamLaw).map stopped).map reindex := by
        rw [Measure.map_map hreindex hstopped]
        rfl
    _ = (((fairCoinStreamLaw.prod fairCoinStreamLaw).map
        (fun pair => firstExitRoundSplit s pending threshold pair.1
          pair.2)).prod fairCoinStreamLaw).map reindex := by
            rw [firstExitRoundSplit_merged_shift_law s pending threshold
              hthreshold hfresh]
    _ = (((fairCoinStreamLaw.prod fairCoinStreamLaw).map
        (fun pair => firstExitRoundSplit s pending threshold pair.1
          pair.2)).map id).prod
          (fairCoinStreamLaw.map manuscriptGlobalCoinRead) := by
            exact (Measure.map_prod_map _ fairCoinStreamLaw
              measurable_id measurable_manuscriptGlobalCoinRead).symm
    _ = _ := by
      rw [Measure.map_id, fairCoinStreamLaw_globalCoinRead]

/-- Conditional on any fixed past prefix and injective origin assignment,
future coins on the allocated executable labels have the fair product law. -/
theorem fairCoinStreamLaw_prefix_originFuture
    (level nextLabel processed : Nat) (origin : Nat → Nat × Nat)
    (hhistory : ManuscriptOriginHistory nextLabel processed origin) :
    fairCoinStreamLaw.map
      (fun coins =>
        (coinPrefix level coins,
          fun pair : Nat × Fin nextLabel =>
            manuscriptGlobalCoinRead (shiftCoins level coins)
              (manuscriptOriginCoinIndex nextLabel origin pair))) =
    (fairCoinStreamLaw.map (coinPrefix level)).prod
      (Measure.infinitePi
        (fun _ : Nat × Fin nextLabel => fairCoinLaw)) := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ : Nat × (Nat × Nat) => fairCoinLaw)
  have hsourceProb : IsProbabilityMeasure sourceLaw := by
    letI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
      fun _ => fairCoinLaw_isProbabilityMeasure
    infer_instance
  letI : IsProbabilityMeasure sourceLaw := hsourceProb
  let oldRead : (Nat × (Nat × Nat) → Bool) →
      Nat × Fin nextLabel → Bool :=
    fun source pair => source (manuscriptOriginCoinIndex nextLabel origin pair)
  have holdRead : Measurable oldRead :=
    Measurable.of_eval (fun pair =>
      measurable_pi_apply (manuscriptOriginCoinIndex nextLabel origin pair))
  let split : (Nat × Nat → Bool) →
      (Nat × Nat → Bool) × (Nat × (Nat × Nat) → Bool) :=
    fun coins =>
      (coinPrefix level coins,
        manuscriptGlobalCoinRead (shiftCoins level coins))
  have hsplit : Measurable split :=
    (measurable_coinPrefix level).prodMk
      (measurable_manuscriptGlobalCoinRead.comp
        (Measurable.of_eval (fun index =>
          measurable_pi_apply (index.1 + level, index.2))))
  let reindex : ((Nat × Nat → Bool) × (Nat × (Nat × Nat) → Bool)) →
      (Nat × Nat → Bool) × (Nat × Fin nextLabel → Bool) :=
    Prod.map id oldRead
  have hreindex : Measurable reindex :=
    measurable_fst.prodMk (holdRead.comp measurable_snd)
  calc
    fairCoinStreamLaw.map
        (fun coins =>
          (coinPrefix level coins,
            fun pair : Nat × Fin nextLabel =>
              manuscriptGlobalCoinRead (shiftCoins level coins)
                (manuscriptOriginCoinIndex nextLabel origin pair))) =
      (fairCoinStreamLaw.map split).map reindex := by
        rw [Measure.map_map hreindex hsplit]
        rfl
    _ = ((fairCoinStreamLaw.map (coinPrefix level)).prod
        sourceLaw).map reindex := by
          rw [fairCoinStreamLaw_prefix_globalFuture level]
    _ = ((fairCoinStreamLaw.map (coinPrefix level)).map id).prod
        (sourceLaw.map oldRead) := by
          exact (Measure.map_prod_map _ sourceLaw measurable_id
            holdRead).symm
    _ = _ := by
      rw [Measure.map_id]
      exact congrArg ((fairCoinStreamLaw.map (coinPrefix level)).prod)
        (manuscript_origin_coins_on_allocated_labels nextLabel processed
          origin hhistory)

theorem firstExitRound_originFuture_law {n : Nat}
    (s : TTCState n) (pending : Nat) (threshold : Real)
    (hthreshold : 0 ≤ threshold)
    (nextLabel processed : Nat) (origin : Nat → Nat × Nat)
    (hhistory : ManuscriptOriginHistory nextLabel processed origin) :
    fairCoinStreamLaw.map
      (fun coins =>
        let rounds := firstExitRound s pending threshold coins
        (rounds, fun pair : Nat × Fin nextLabel =>
          manuscriptGlobalCoinRead (shiftCoins rounds coins)
            (manuscriptOriginCoinIndex nextLabel origin pair))) =
    (fairCoinStreamLaw.map
      (firstExitRound s pending threshold)).prod
      (Measure.infinitePi
        (fun _ : Nat × Fin nextLabel => fairCoinLaw)) := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ : Nat × (Nat × Nat) => fairCoinLaw)
  have hsourceProb : IsProbabilityMeasure sourceLaw := by
    letI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
      fun _ => fairCoinLaw_isProbabilityMeasure
    infer_instance
  letI : IsProbabilityMeasure sourceLaw := hsourceProb
  let oldRead : (Nat × (Nat × Nat) → Bool) →
      Nat × Fin nextLabel → Bool :=
    fun source pair => source (manuscriptOriginCoinIndex nextLabel origin pair)
  have holdRead : Measurable oldRead :=
    Measurable.of_eval (fun pair =>
      measurable_pi_apply (manuscriptOriginCoinIndex nextLabel origin pair))
  let stopped : (Nat × Nat → Bool) →
      Nat × (Nat × (Nat × Nat) → Bool) := fun coins =>
    let rounds := firstExitRound s pending threshold coins
    (rounds, manuscriptGlobalCoinRead (shiftCoins rounds coins))
  have hstopped : Measurable stopped := by
    let base : (Nat × Nat → Bool) → Nat × (Nat × Nat → Bool) :=
      fun coins =>
        let rounds := firstExitRound s pending threshold coins
        (rounds, shiftCoins rounds coins)
    have hbase : Measurable base :=
      measurable_stoppedCoinPair _
        (measurable_firstExitRound s pending threshold)
    exact (measurable_fst.prodMk
      (measurable_manuscriptGlobalCoinRead.comp measurable_snd)).comp hbase
  let reindex : (Nat × (Nat × (Nat × Nat) → Bool)) →
      Nat × (Nat × Fin nextLabel → Bool) := Prod.map id oldRead
  have hreindex : Measurable reindex :=
    measurable_fst.prodMk (holdRead.comp measurable_snd)
  calc
    fairCoinStreamLaw.map
        (fun coins =>
          let rounds := firstExitRound s pending threshold coins
          (rounds, fun pair : Nat × Fin nextLabel =>
            manuscriptGlobalCoinRead (shiftCoins rounds coins)
              (manuscriptOriginCoinIndex nextLabel origin pair))) =
      (fairCoinStreamLaw.map stopped).map reindex := by
        rw [Measure.map_map hreindex hstopped]
        rfl
    _ = ((fairCoinStreamLaw.map
        (firstExitRound s pending threshold)).prod sourceLaw).map reindex := by
          rw [firstExitRound_globalFuture_law s pending threshold hthreshold]
    _ = ((fairCoinStreamLaw.map
        (firstExitRound s pending threshold)).map id).prod
          (sourceLaw.map oldRead) := by
            exact (Measure.map_prod_map _ sourceLaw measurable_id
              holdRead).symm
    _ = _ := by
      rw [Measure.map_id]
      exact congrArg
        ((fairCoinStreamLaw.map
          (firstExitRound s pending threshold)).prod)
        (manuscript_origin_coins_on_allocated_labels nextLabel processed
          origin hhistory)

/-- An adaptive prefix may choose the current origin assignment and number
of allocated labels. An independent future component-source array still
projects to fresh fair coins on exactly those executable labels. -/
theorem manuscript_origin_futureCoins_adaptive
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (preLaw : Measure α)
    (nextLabel processed : α → Nat)
    (origin : α → Nat → Nat × Nat)
    (hhistory : ∀ a,
      ManuscriptOriginHistory (nextLabel a) (processed a) (origin a))
    (g : (a : α) → (Nat × Fin (nextLabel a) → Bool) → β)
    (hg : ∀ a, Measurable (g a)) :
    let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
      Measure.infinitePi (fun _ : Nat × (Nat × Nat) => fairCoinLaw)
    preLaw.bind (fun a => sourceLaw.map fun source =>
      g a (fun pair => source
        (manuscriptOriginCoinIndex (nextLabel a) (origin a) pair))) =
    preLaw.bind (fun a =>
      (Measure.infinitePi
        (fun _ : Nat × Fin (nextLabel a) => fairCoinLaw)).map (g a)) := by
  dsimp only
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro a
  let oldRead : (Nat × (Nat × Nat) → Bool) →
      Nat × Fin (nextLabel a) → Bool :=
    fun source pair => source
      (manuscriptOriginCoinIndex (nextLabel a) (origin a) pair)
  have holdRead : Measurable oldRead :=
    Measurable.of_eval (fun pair =>
      measurable_pi_apply
        (manuscriptOriginCoinIndex (nextLabel a) (origin a) pair))
  change (Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).map
      (g a ∘ oldRead) = _
  rw [← Measure.map_map (hg a) holdRead]
  rw [manuscript_origin_coins_on_allocated_labels
    (nextLabel a) (processed a) (origin a) (hhistory a)]

theorem manuscript_origin_futureCoins_adaptive_ae
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (preLaw : Measure α)
    (nextLabel processed : α → Nat)
    (origin : α → Nat → Nat × Nat)
    (hhistory : ∀ᵐ a ∂preLaw,
      ManuscriptOriginHistory (nextLabel a) (processed a) (origin a))
    (g : (a : α) → (Nat × Fin (nextLabel a) → Bool) → β)
    (hg : ∀ a, Measurable (g a)) :
    let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
      Measure.infinitePi (fun _ : Nat × (Nat × Nat) => fairCoinLaw)
    preLaw.bind (fun a => sourceLaw.map fun source =>
      g a (fun pair => source
        (manuscriptOriginCoinIndex (nextLabel a) (origin a) pair))) =
    preLaw.bind (fun a =>
      (Measure.infinitePi
        (fun _ : Nat × Fin (nextLabel a) => fairCoinLaw)).map (g a)) := by
  dsimp only
  apply Measure.bind_congr_right
  filter_upwards [hhistory] with a ha
  let oldRead : (Nat × (Nat × Nat) → Bool) →
      Nat × Fin (nextLabel a) → Bool :=
    fun source pair => source
      (manuscriptOriginCoinIndex (nextLabel a) (origin a) pair)
  have holdRead : Measurable oldRead :=
    Measurable.of_eval (fun pair =>
      measurable_pi_apply
        (manuscriptOriginCoinIndex (nextLabel a) (origin a) pair))
  change (Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).map
      (g a ∘ oldRead) = _
  rw [← Measure.map_map (hg a) holdRead]
  rw [manuscript_origin_coins_on_allocated_labels
    (nextLabel a) (processed a) (origin a) ha]

/-- A measurable continuation may choose the origin map from the observed
global prefix. Its old-copy future coins still have the independent fair
product law on the adaptively allocated executable labels. -/
theorem fairCoinStreamLaw_prefix_originFuture_adaptive
    {β : Type*} [MeasurableSpace β]
    (level : Nat)
    (nextLabel processed : (Nat × Nat → Bool) → Nat)
    (origin : (Nat × Nat → Bool) → Nat → Nat × Nat)
    (hhistory : ∀ᵐ pre ∂fairCoinStreamLaw.map (coinPrefix level),
      ManuscriptOriginHistory (nextLabel pre) (processed pre)
        (origin pre))
    (g : (pre : Nat × Nat → Bool) →
      (Nat × Fin (nextLabel pre) → Bool) → β)
    (hg : ∀ pre, Measurable (g pre))
    (hjoint : Measurable
      (fun z : (Nat × Nat → Bool) × (Nat × (Nat × Nat) → Bool) =>
        g z.1 (fun pair => z.2
          (manuscriptOriginCoinIndex (nextLabel z.1) (origin z.1) pair)))) :
    fairCoinStreamLaw.map
      (fun coins =>
        let pre := coinPrefix level coins
        g pre (fun pair =>
          manuscriptGlobalCoinRead (shiftCoins level coins)
            (manuscriptOriginCoinIndex (nextLabel pre)
              (origin pre) pair))) =
    (fairCoinStreamLaw.map (coinPrefix level)).bind (fun pre =>
      (Measure.infinitePi
        (fun _ : Nat × Fin (nextLabel pre) => fairCoinLaw)).map
        (g pre)) := by
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  let preLaw : Measure (Nat × Nat → Bool) :=
    fairCoinStreamLaw.map (coinPrefix level)
  letI : IsProbabilityMeasure preLaw :=
    Measure.isProbabilityMeasure_map
      (measurable_coinPrefix level).aemeasurable
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ : Nat × (Nat × Nat) => fairCoinLaw)
  have hsourceProb : IsProbabilityMeasure sourceLaw := by
    letI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
      fun _ => fairCoinLaw_isProbabilityMeasure
    infer_instance
  letI : IsProbabilityMeasure sourceLaw := hsourceProb
  let split : (Nat × Nat → Bool) →
      (Nat × Nat → Bool) × (Nat × (Nat × Nat) → Bool) :=
    fun coins => (coinPrefix level coins,
      manuscriptGlobalCoinRead (shiftCoins level coins))
  have hsplit : Measurable split :=
    (measurable_coinPrefix level).prodMk
      (measurable_manuscriptGlobalCoinRead.comp
        (Measurable.of_eval (fun index =>
          measurable_pi_apply (index.1 + level, index.2))))
  let f : (Nat × Nat → Bool) × (Nat × (Nat × Nat) → Bool) → β :=
    fun z => g z.1 (fun pair => z.2
      (manuscriptOriginCoinIndex (nextLabel z.1) (origin z.1) pair))
  have hf : Measurable f := hjoint
  have hproduct : (preLaw.prod sourceLaw).map f =
      preLaw.bind (fun pre =>
        sourceLaw.map fun source => f (pre, source)) := by
    rw [Measure.prod_eq_bind_map]
    rw [map_bind_measure preLaw
      (fun pre => sourceLaw.map (Prod.mk pre)) f
      Measurable.map_prodMk_left.aemeasurable hf]
    congr 1
    funext pre
    rw [Measure.map_map hf measurable_prodMk_left]
    rfl
  calc
    fairCoinStreamLaw.map
        (fun coins =>
          let pre := coinPrefix level coins
          g pre (fun pair =>
            manuscriptGlobalCoinRead (shiftCoins level coins)
              (manuscriptOriginCoinIndex (nextLabel pre)
                (origin pre) pair))) =
      (fairCoinStreamLaw.map split).map f := by
        rw [Measure.map_map hf hsplit]
        rfl
    _ = (preLaw.prod sourceLaw).map f := by
      rw [fairCoinStreamLaw_prefix_globalFuture level]
    _ = preLaw.bind (fun pre =>
        sourceLaw.map fun source => f (pre, source)) := hproduct
    _ = _ := by
      exact manuscript_origin_futureCoins_adaptive_ae preLaw nextLabel
        processed origin hhistory g hg

end Kr25Ssmxt
