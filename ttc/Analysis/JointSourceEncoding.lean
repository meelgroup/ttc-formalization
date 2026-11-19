import ttc.Analysis.GenericStoppedPrefix
import ttc.Analysis.StoppedRoundPrefix

/-! One fair array encodes both source families, with time unchanged. -/

namespace ttc

open MeasureTheory

def jointSourceIndex (tag : Fin 2 × (Nat × (Nat × Nat))) :
    Nat × Nat :=
  (tag.2.2.1, Nat.pair tag.1.val (Nat.pair tag.2.1 tag.2.2.2))

theorem jointSourceIndex_injective :
    Function.Injective jointSourceIndex := by
  intro a b hab
  change (a.2.2.1, Nat.pair a.1.val (Nat.pair a.2.1 a.2.2.2)) =
    (b.2.2.1, Nat.pair b.1.val (Nat.pair b.2.1 b.2.2.2)) at hab
  simp only [Prod.mk.injEq, Nat.pair_eq_pair] at hab
  exact Prod.ext (Fin.ext hab.2.1)
    (Prod.ext hab.2.2.1 (Prod.ext hab.1 hab.2.2.2))

def jointOldRead (coins : Nat × Nat → Bool) :
    Nat × (Nat × Nat) → Bool :=
  fun tag => coins (jointSourceIndex (0, tag))

def jointFreshRead (coins : Nat × Nat → Bool) :
    Nat × Nat → Bool :=
  fun pair => coins (jointSourceIndex (1, (0, pair)))

theorem measurable_jointRead :
    Measurable (fun coins : Nat × Nat → Bool =>
      (jointOldRead coins, jointFreshRead coins)) := by
  exact (Measurable.of_eval (fun tag =>
    measurable_pi_apply (jointSourceIndex (0, tag)))).prodMk
    (Measurable.of_eval (fun pair =>
      measurable_pi_apply (jointSourceIndex (1, (0, pair)))))

theorem jointOldRead_shift (coins : Nat × Nat → Bool)
    (rounds : Nat) :
    jointOldRead (shiftCoins rounds coins) =
      (fun tag => jointOldRead coins
        (tag.1, (tag.2.1 + rounds, tag.2.2))) := by
  funext tag
  rfl

theorem jointFreshRead_shift (coins : Nat × Nat → Bool)
    (rounds : Nat) :
    jointFreshRead (shiftCoins rounds coins) =
      shiftCoins rounds (jointFreshRead coins) := by
  funext pair
  rfl

theorem jointOldRead_prefix (coins : Nat × Nat → Bool)
    (rounds : Nat) (tag : Nat × (Nat × Nat))
    (hbefore : tag.2.1 < rounds) :
    jointOldRead (coinPrefix rounds coins) tag =
      jointOldRead coins tag := by
  simp [jointOldRead, jointSourceIndex,
    coinPrefix, hbefore]

theorem jointFreshRead_prefix (coins : Nat × Nat → Bool)
    (rounds : Nat) (pair : Nat × Nat) (hbefore : pair.1 < rounds) :
    jointFreshRead (coinPrefix rounds coins) pair =
      jointFreshRead coins pair := by
  simp [jointFreshRead, jointSourceIndex,
    coinPrefix, hbefore]

def jointMergedRead (origin : Nat → Nat × Nat)
    (firstLabel : Nat) (coins : Nat × Nat → Bool) :
    Nat × Nat → Bool :=
  mergeCoinsAtLabel firstLabel
    (fun pair => jointOldRead coins
      ((origin pair.2).1, (pair.1, (origin pair.2).2)))
    (jointFreshRead coins)

theorem measurable_jointMergedRead
    (origin : Nat → Nat × Nat) (firstLabel : Nat) :
    Measurable (jointMergedRead origin firstLabel) := by
  apply Measurable.of_eval
  intro pair
  by_cases hlabel : pair.2 < firstLabel
  · simpa [jointMergedRead, mergeCoinsAtLabel,
      hlabel, jointOldRead] using
      (measurable_pi_apply
        (jointSourceIndex
          (0, ((origin pair.2).1, (pair.1, (origin pair.2).2)))))
  · simpa [jointMergedRead, mergeCoinsAtLabel,
      hlabel, jointFreshRead] using
      (measurable_pi_apply
        (jointSourceIndex (1, (0, pair))))

theorem jointMergedRead_prefix_local
    (origin : Nat → Nat × Nat) (firstLabel rounds : Nat)
    (coins : Nat × Nat → Bool) :
    coinPrefix rounds
      (jointMergedRead origin firstLabel
        (coinPrefix rounds coins)) =
      coinPrefix rounds (jointMergedRead origin firstLabel coins) := by
  funext pair
  by_cases hround : pair.1 < rounds
  · by_cases hlabel : pair.2 < firstLabel
    · simp [coinPrefix, hround, jointMergedRead,
        mergeCoinsAtLabel, hlabel,
        jointOldRead_prefix coins rounds
          ((origin pair.2).1, (pair.1, (origin pair.2).2)) hround]
    · simp [coinPrefix, hround, jointMergedRead,
        mergeCoinsAtLabel, hlabel,
        jointFreshRead_prefix coins rounds pair hround]
  · simp [coinPrefix, hround]

theorem jointMergedRead_firstExitEvent_prefix
    {n : Nat} (s : TTCState n) (pending : Nat) (threshold : Real)
    (origin : Nat → Nat × Nat) (firstLabel rounds : Nat) :
    (coinPrefix rounds) ⁻¹'
      ((jointMergedRead origin firstLabel) ⁻¹'
        firstExitPrefixEvent s pending threshold rounds) =
      (jointMergedRead origin firstLabel) ⁻¹'
        firstExitPrefixEvent s pending threshold rounds := by
  exact firstExitPrefixEvent_preimage_of_prefix_local_read s pending
    threshold (jointMergedRead origin firstLabel)
    (fun r coins => jointMergedRead_prefix_local origin
      firstLabel r coins) rounds

/-- The merged old-label/new-label stream is fair when the allocated old
labels have distinct origin tags. -/
theorem fairCoinStreamLaw_jointMergedRead
    (firstLabel processed : Nat) (origin : Nat → Nat × Nat)
    (hhistory : OriginHistory firstLabel processed origin) :
    fairCoinStreamLaw.map
      (jointMergedRead origin firstLabel) =
    fairCoinStreamLaw := by
  let index : Nat × Nat → Nat × Nat := fun pair =>
    if pair.2 < firstLabel then
      jointSourceIndex
        (0, ((origin pair.2).1, (pair.1, (origin pair.2).2)))
    else jointSourceIndex (1, (0, pair))
  have hinj : Function.Injective index := by
    intro a b hab
    by_cases ha : a.2 < firstLabel <;>
      by_cases hb : b.2 < firstLabel
    · have htags :
          ((0 : Fin 2), ((origin a.2).1, (a.1, (origin a.2).2))) =
          ((0 : Fin 2), ((origin b.2).1, (b.1, (origin b.2).2))) := by
        apply jointSourceIndex_injective
        simpa [index, ha, hb] using hab
      have hround : a.1 = b.1 := by
        exact congrArg (fun tag : Fin 2 × (Nat × (Nat × Nat)) =>
          tag.2.2.1) htags
      have horigin : origin a.2 = origin b.2 := by
        exact Prod.ext
          (congrArg (fun tag : Fin 2 × (Nat × (Nat × Nat)) =>
            tag.2.1) htags)
          (congrArg (fun tag : Fin 2 × (Nat × (Nat × Nat)) =>
            tag.2.2.2) htags)
      exact Prod.ext hround (hhistory.2 a.2 b.2 ha hb horigin)
    · have htags := jointSourceIndex_injective
        (show jointSourceIndex
            (0, ((origin a.2).1, (a.1, (origin a.2).2))) =
          jointSourceIndex (1, (0, b)) by
          simpa [index, ha, hb] using hab)
      have : (0 : Fin 2) = 1 := congrArg Prod.fst htags
      exact False.elim (by norm_num at this)
    · have htags := jointSourceIndex_injective
        (show jointSourceIndex (1, (0, a)) =
          jointSourceIndex
            (0, ((origin b.2).1, (b.1, (origin b.2).2))) by
          simpa [index, ha, hb] using hab)
      have : (1 : Fin 2) = 0 := congrArg Prod.fst htags
      exact False.elim (by norm_num at this)
    · have htags : ((1 : Fin 2), (0, a)) = ((1 : Fin 2), (0, b)) :=
        jointSourceIndex_injective
          (by simpa [index, ha, hb] using hab)
      exact congrArg (fun tag : Fin 2 × (Nat × (Nat × Nat)) =>
        tag.2.2) htags
  have hmap : jointMergedRead origin firstLabel =
      (fun coins pair => coins (index pair)) := by
    funext coins pair
    by_cases hlabel : pair.2 < firstLabel <;>
      simp [jointMergedRead, mergeCoinsAtLabel,
        jointOldRead, jointFreshRead, index, hlabel]
  rw [hmap]
  letI : ∀ _ : Nat × Nat, IsProbabilityMeasure fairCoinLaw :=
    fun _ => fairCoinLaw_isProbabilityMeasure
  exact @Measure.map_infinitePi_infinitePi_of_inj
    (Nat × Nat) (Nat × Nat) (fun _ => Bool)
    (fun _ => inferInstance) (fun _ => fairCoinLaw)
    (fun _ => fairCoinLaw_isProbabilityMeasure) index hinj

/-- The actual first-exit rule, when it reads old labels through their
origin tags and fresh labels from the second channel, leaves the entire
joint source tail independent of the stopped joint-source prefix. -/
theorem jointMergedRead_stoppedPrefix_shift_law
    {n : Nat} (s : TTCState n) (pending : Nat) (threshold : Real)
    (hthreshold : 0 ≤ threshold)
    (processed : Nat) (origin : Nat → Nat × Nat)
    (hhistory : OriginHistory s.nextLabel processed origin) :
    let read := jointMergedRead origin s.nextLabel
    let stop := fun coins => ttcPseudocode.secondLoopExitRound s pending threshold (read coins)
    fairCoinStreamLaw.map
      (fun coins =>
        (coinPrefix (stop coins) coins, shiftCoins (stop coins) coins)) =
    (fairCoinStreamLaw.map
      (fun coins => coinPrefix (stop coins) coins)).prod
      fairCoinStreamLaw := by
  let read := jointMergedRead origin s.nextLabel
  let stop := fun coins => ttcPseudocode.secondLoopExitRound s pending threshold (read coins)
  let event := fun r => read ⁻¹' firstExitPrefixEvent s pending threshold r
  have hread : Measurable read :=
    measurable_jointMergedRead origin s.nextLabel
  have hstop : Measurable stop :=
    (measurable_firstExitRound s pending threshold).comp hread
  have hevent (r : Nat) : MeasurableSet (event r) :=
    (measurableSet_firstExitPrefixEvent s pending threshold r).preimage
      hread
  have hprefix (r : Nat) :
      (coinPrefix r) ⁻¹' event r = event r :=
    jointMergedRead_firstExitEvent_prefix s pending threshold
      origin s.nextLabel r
  have hae (r : Nat) : ∀ᵐ coins ∂fairCoinStreamLaw,
      (stop coins = r ↔ coins ∈ event r) := by
    have hbase := firstExitRound_eq_prefix_event_ae s pending threshold
      hthreshold r
    rw [← fairCoinStreamLaw_jointMergedRead s.nextLabel processed
      origin hhistory] at hbase
    exact ae_of_ae_map hread.aemeasurable hbase
  exact fairCoinStreamLaw_generic_stoppedPrefix_shift_law
    stop hstop event hevent hprefix hae

theorem fairCoinStreamLaw_jointRead :
    fairCoinStreamLaw.map
      (fun coins =>
        (jointOldRead coins, jointFreshRead coins)) =
    (Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
      fairCoinStreamLaw := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  let global : Measure (Fin 2 × (Nat × (Nat × Nat)) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  let read : (Nat × Nat → Bool) →
      Fin 2 × (Nat × (Nat × Nat)) → Bool :=
    fun coins tag => coins (jointSourceIndex tag)
  have hread : Measurable read :=
    Measurable.of_eval (fun tag =>
      measurable_pi_apply (jointSourceIndex tag))
  have hindexed : fairCoinStreamLaw.map read = global := by
    letI : ∀ _ : Nat × Nat, IsProbabilityMeasure fairCoinLaw :=
      fun _ => fairCoinLaw_isProbabilityMeasure
    exact @Measure.map_infinitePi_infinitePi_of_inj
      (Nat × Nat) (Fin 2 × (Nat × (Nat × Nat)))
      (fun _ => Bool) (fun _ => inferInstance)
      (fun _ => fairCoinLaw) (fun _ => fairCoinLaw_isProbabilityMeasure)
      jointSourceIndex jointSourceIndex_injective
  letI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
    fun _ => fairCoinLaw_isProbabilityMeasure
  letI : IsProbabilityMeasure sourceLaw := by
    dsimp [sourceLaw]
    infer_instance
  have hsource : sourceLaw.map
      (fun src => fun pair : Nat × Nat => src (0, pair)) =
      fairCoinStreamLaw := by
    exact @Measure.map_infinitePi_infinitePi_of_inj
      (Nat × (Nat × Nat)) (Nat × Nat) (fun _ => Bool)
      (fun _ => inferInstance) (fun _ => fairCoinLaw)
      (fun _ => fairCoinLaw_isProbabilityMeasure)
      (fun pair => (0, pair))
      (by intro a b hab; exact congrArg Prod.snd hab)
  have hcurry : global.map
      (MeasurableEquiv.curry (Fin 2) (Nat × (Nat × Nat)) Bool) =
      Measure.infinitePi (fun _ : Fin 2 => sourceLaw) := by
    exact Measure.infinitePi_map_curry
      (hμ := fun _ _ => fairCoinLaw_isProbabilityMeasure)
      (fun _ : Fin 2 => fun _ : Nat × (Nat × Nat) => fairCoinLaw)
  have htwo :
      (Measure.infinitePi (fun _ : Fin 2 => sourceLaw)).map
        MeasurableEquiv.finTwoArrow =
      sourceLaw.prod sourceLaw := by
    rw [Measure.infinitePi_eq_pi]
    exact (measurePreserving_finTwoArrow sourceLaw).map_eq
  have hbase : global.map (fun coins =>
      ((fun tag => coins (0, tag)),
        (fun tag => coins (1, tag)))) =
      sourceLaw.prod sourceLaw := by
    calc
      _ = (global.map
          (MeasurableEquiv.curry (Fin 2)
            (Nat × (Nat × Nat)) Bool)).map
              MeasurableEquiv.finTwoArrow := by
              rw [Measure.map_map
                MeasurableEquiv.finTwoArrow.measurable
                (MeasurableEquiv.curry (Fin 2)
                  (Nat × (Nat × Nat)) Bool).measurable]
              congr 1
      _ = _ := by rw [hcurry, htwo]
  let restrict : (Nat × (Nat × Nat) → Bool) →
      Nat × Nat → Bool := fun src pair => src (0, pair)
  have hrestrict : Measurable restrict :=
    Measurable.of_eval (fun pair => measurable_pi_apply (0, pair))
  have hbaseMap : Measurable
      (fun coins : Fin 2 × (Nat × (Nat × Nat)) → Bool =>
        ((fun tag => coins (0, tag)),
          (fun tag => coins (1, tag)))) := by fun_prop
  have hprodMap : Measurable
      (Prod.map (id : (Nat × (Nat × Nat) → Bool) →
        (Nat × (Nat × Nat) → Bool)) restrict) :=
    measurable_fst.prodMk (hrestrict.comp measurable_snd)
  have hpair : global.map (fun coins =>
      ((fun tag => coins (0, tag)),
        (fun pair => coins (1, (0, pair))))) =
      sourceLaw.prod fairCoinStreamLaw := by
    calc
      _ = (global.map (fun coins =>
          ((fun tag => coins (0, tag)),
            (fun tag => coins (1, tag))))).map
            (Prod.map id restrict) := by
              rw [Measure.map_map hprodMap hbaseMap]
              rfl
      _ = (sourceLaw.prod sourceLaw).map (Prod.map id restrict) := by
        rw [hbase]
      _ = (sourceLaw.map id).prod (sourceLaw.map restrict) := by
        exact (Measure.map_prod_map sourceLaw sourceLaw measurable_id
          hrestrict).symm
      _ = _ := by rw [Measure.map_id, hsource]
  let split : (Fin 2 × (Nat × (Nat × Nat)) → Bool) →
      (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool) :=
    fun coins => ((fun tag => coins (0, tag)),
      (fun pair => coins (1, (0, pair))))
  have hsplit : Measurable split := by fun_prop
  calc
    fairCoinStreamLaw.map
        (fun coins =>
          (jointOldRead coins, jointFreshRead coins)) =
      (fairCoinStreamLaw.map read).map split := by
        rw [Measure.map_map hsplit hread]
        rfl
    _ = global.map split := by rw [hindexed]
    _ = _ := hpair

/-- After the encoded first-exit stop, both complete unused source families
are independent of the observed joint-source prefix. -/
theorem jointMergedRead_stoppedPrefix_jointTail_law
    {n : Nat} (s : TTCState n) (pending : Nat) (threshold : Real)
    (hthreshold : 0 ≤ threshold)
    (processed : Nat) (origin : Nat → Nat × Nat)
    (hhistory : OriginHistory s.nextLabel processed origin) :
    let stop := fun coins => ttcPseudocode.secondLoopExitRound s pending threshold
      (jointMergedRead origin s.nextLabel coins)
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
  let stop := fun coins => ttcPseudocode.secondLoopExitRound s pending threshold
    (jointMergedRead origin s.nextLabel coins)
  let observed : (Nat × Nat → Bool) → Nat × Nat → Bool :=
    fun coins => coinPrefix (stop coins) coins
  let split : (Nat × Nat → Bool) →
      (Nat × Nat → Bool) × (Nat × Nat → Bool) :=
    fun coins => (observed coins, shiftCoins (stop coins) coins)
  let reindex : ((Nat × Nat → Bool) × (Nat × Nat → Bool)) →
      (Nat × Nat → Bool) ×
        ((Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool)) :=
    Prod.map id (fun coins =>
      (jointOldRead coins, jointFreshRead coins))
  have hstop : Measurable stop :=
    (measurable_firstExitRound s pending threshold).comp
      (measurable_jointMergedRead origin s.nextLabel)
  have hobserved : Measurable observed := by
    have hprefixJoint : Measurable
        (fun z : Nat × (Nat × Nat → Bool) => coinPrefix z.1 z.2) := by
      apply measurable_from_prod_countable_right
      intro rounds
      exact measurable_coinPrefix rounds
    exact hprefixJoint.comp (hstop.prodMk measurable_id)
  have hsplit : Measurable split :=
    hobserved.prodMk ((measurable_stoppedCoinPair stop hstop).snd)
  have hreindex : Measurable reindex :=
    measurable_fst.prodMk
      (measurable_jointRead.comp measurable_snd)
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
        (fun coins =>
          (observed coins,
            (jointOldRead (shiftCoins (stop coins) coins),
              jointFreshRead (shiftCoins (stop coins) coins)))) =
      (fairCoinStreamLaw.map split).map reindex := by
        rw [Measure.map_map hreindex hsplit]
        rfl
    _ = ((fairCoinStreamLaw.map observed).prod fairCoinStreamLaw).map
          reindex := by
        rw [jointMergedRead_stoppedPrefix_shift_law s pending
          threshold hthreshold processed origin hhistory]
    _ = ((fairCoinStreamLaw.map observed).map id).prod
          (fairCoinStreamLaw.map (fun coins =>
            (jointOldRead coins,
              jointFreshRead coins))) := by
        exact (Measure.map_prod_map _ fairCoinStreamLaw measurable_id
          measurable_jointRead).symm
    _ = _ := by
      rw [Measure.map_id, fairCoinStreamLaw_jointRead]

def jointRelabelRead (origin : Nat → Nat × Nat)
    (firstLabel : Nat) (labelMap : Nat → Nat)
    (coins : Nat × Nat → Bool) : Nat × Nat → Bool :=
  mergeCoinsAtLabel firstLabel
    (fun pair => jointOldRead coins
      ((origin pair.2).1, (pair.1, (origin pair.2).2)))
    (fun pair => jointFreshRead coins
      (pair.1, labelMap (pair.2 - firstLabel)))

theorem measurable_jointRelabelRead
    (origin : Nat → Nat × Nat) (firstLabel : Nat)
    (labelMap : Nat → Nat) :
    Measurable (jointRelabelRead origin firstLabel labelMap) := by
  apply Measurable.of_eval
  intro pair
  by_cases hlabel : pair.2 < firstLabel
  · simpa [jointRelabelRead, mergeCoinsAtLabel,
      hlabel, jointOldRead] using
      (measurable_pi_apply
        (jointSourceIndex
          (0, ((origin pair.2).1, (pair.1, (origin pair.2).2)))))
  · simpa [jointRelabelRead, mergeCoinsAtLabel,
      hlabel, jointFreshRead] using
      (measurable_pi_apply
        (jointSourceIndex
          (1, (0, (pair.1, labelMap (pair.2 - firstLabel))))))

theorem jointRelabelRead_prefix_local
    (origin : Nat → Nat × Nat) (firstLabel : Nat)
    (labelMap : Nat → Nat) (rounds : Nat)
    (coins : Nat × Nat → Bool) :
    coinPrefix rounds
      (jointRelabelRead origin firstLabel labelMap
        (coinPrefix rounds coins)) =
      coinPrefix rounds
        (jointRelabelRead origin firstLabel labelMap coins) := by
  funext pair
  by_cases hround : pair.1 < rounds
  · by_cases hlabel : pair.2 < firstLabel
    · simp [coinPrefix, hround, jointRelabelRead,
        mergeCoinsAtLabel, hlabel,
        jointOldRead_prefix coins rounds
          ((origin pair.2).1, (pair.1, (origin pair.2).2)) hround]
    · simp [coinPrefix, hround, jointRelabelRead,
        mergeCoinsAtLabel, hlabel,
        jointFreshRead_prefix coins rounds
          (pair.1, labelMap (pair.2 - firstLabel)) hround]
  · simp [coinPrefix, hround]

theorem fairCoinStreamLaw_jointRelabelRead
    (firstLabel processed : Nat) (origin : Nat → Nat × Nat)
    (hhistory : OriginHistory firstLabel processed origin)
    (labelMap : Nat → Nat) (hlabelMap : Function.Injective labelMap) :
    fairCoinStreamLaw.map
      (jointRelabelRead origin firstLabel labelMap) =
    fairCoinStreamLaw := by
  let index : Nat × Nat → Nat × Nat := fun pair =>
    if pair.2 < firstLabel then
      jointSourceIndex
        (0, ((origin pair.2).1, (pair.1, (origin pair.2).2)))
    else jointSourceIndex
      (1, (0, (pair.1, labelMap (pair.2 - firstLabel))))
  have hinj : Function.Injective index := by
    intro a b hab
    by_cases ha : a.2 < firstLabel <;> by_cases hb : b.2 < firstLabel
    · have htags :
          ((0 : Fin 2), ((origin a.2).1, (a.1, (origin a.2).2))) =
          ((0 : Fin 2), ((origin b.2).1, (b.1, (origin b.2).2))) :=
        jointSourceIndex_injective
          (by simpa [index, ha, hb] using hab)
      have hround : a.1 = b.1 :=
        congrArg (fun tag : Fin 2 × (Nat × (Nat × Nat)) =>
          tag.2.2.1) htags
      have horigin : origin a.2 = origin b.2 :=
        Prod.ext
          (congrArg (fun tag : Fin 2 × (Nat × (Nat × Nat)) =>
            tag.2.1) htags)
          (congrArg (fun tag : Fin 2 × (Nat × (Nat × Nat)) =>
            tag.2.2.2) htags)
      exact Prod.ext hround (hhistory.2 a.2 b.2 ha hb horigin)
    · have htags := jointSourceIndex_injective
        (show jointSourceIndex
            (0, ((origin a.2).1, (a.1, (origin a.2).2))) =
          jointSourceIndex
            (1, (0, (b.1, labelMap (b.2 - firstLabel)))) by
          simpa [index, ha, hb] using hab)
      have : (0 : Fin 2) = 1 := congrArg Prod.fst htags
      exact False.elim (by norm_num at this)
    · have htags := jointSourceIndex_injective
        (show jointSourceIndex
            (1, (0, (a.1, labelMap (a.2 - firstLabel)))) =
          jointSourceIndex
            (0, ((origin b.2).1, (b.1, (origin b.2).2))) by
          simpa [index, ha, hb] using hab)
      have : (1 : Fin 2) = 0 := congrArg Prod.fst htags
      exact False.elim (by norm_num at this)
    · have htags :
          ((1 : Fin 2), (0, (a.1, labelMap (a.2 - firstLabel)))) =
          ((1 : Fin 2), (0, (b.1, labelMap (b.2 - firstLabel)))) :=
        jointSourceIndex_injective
          (by simpa [index, ha, hb] using hab)
      have hround : a.1 = b.1 :=
        congrArg (fun tag : Fin 2 × (Nat × (Nat × Nat)) =>
          tag.2.2.1) htags
      have hlabel : a.2 - firstLabel = b.2 - firstLabel :=
        hlabelMap (congrArg
          (fun tag : Fin 2 × (Nat × (Nat × Nat)) => tag.2.2.2)
          htags)
      exact Prod.ext hround (by omega)
  have hmap : jointRelabelRead origin firstLabel labelMap =
      (fun coins pair => coins (index pair)) := by
    funext coins pair
    by_cases hlabel : pair.2 < firstLabel <;>
      simp [jointRelabelRead, mergeCoinsAtLabel,
        jointOldRead, jointFreshRead, index, hlabel]
  rw [hmap]
  letI : ∀ _ : Nat × Nat, IsProbabilityMeasure fairCoinLaw :=
    fun _ => fairCoinLaw_isProbabilityMeasure
  exact @Measure.map_infinitePi_infinitePi_of_inj
    (Nat × Nat) (Nat × Nat) (fun _ => Bool)
    (fun _ => inferInstance) (fun _ => fairCoinLaw)
    (fun _ => fairCoinLaw_isProbabilityMeasure) index hinj

theorem joint_localRead_stoppedPrefix_jointTail_law
    {n : Nat} (s : TTCState n) (pending : Nat) (threshold : Real)
    (hthreshold : 0 ≤ threshold)
    (read : (Nat × Nat → Bool) → Nat × Nat → Bool)
    (hread : Measurable read)
    (hfair : fairCoinStreamLaw.map read = fairCoinStreamLaw)
    (hlocal : ∀ r coins,
      coinPrefix r (read (coinPrefix r coins)) =
        coinPrefix r (read coins)) :
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
  let stop := fun coins => ttcPseudocode.secondLoopExitRound s pending threshold (read coins)
  let observed : (Nat × Nat → Bool) → Nat × Nat → Bool :=
    fun coins => coinPrefix (stop coins) coins
  let split : (Nat × Nat → Bool) →
      (Nat × Nat → Bool) × (Nat × Nat → Bool) :=
    fun coins => (observed coins, shiftCoins (stop coins) coins)
  let reindex : ((Nat × Nat → Bool) × (Nat × Nat → Bool)) →
      (Nat × Nat → Bool) ×
        ((Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool)) :=
    Prod.map id (fun coins =>
      (jointOldRead coins, jointFreshRead coins))
  have hstop : Measurable stop :=
    (measurable_firstExitRound s pending threshold).comp hread
  have hobserved : Measurable observed := by
    have hprefixJoint : Measurable
        (fun z : Nat × (Nat × Nat → Bool) => coinPrefix z.1 z.2) := by
      apply measurable_from_prod_countable_right
      intro rounds
      exact measurable_coinPrefix rounds
    exact hprefixJoint.comp (hstop.prodMk measurable_id)
  have hsplit : Measurable split :=
    hobserved.prodMk ((measurable_stoppedCoinPair stop hstop).snd)
  have hreindex : Measurable reindex :=
    measurable_fst.prodMk
      (measurable_jointRead.comp measurable_snd)
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  calc
    fairCoinStreamLaw.map
        (fun coins =>
          (observed coins,
            (jointOldRead (shiftCoins (stop coins) coins),
              jointFreshRead (shiftCoins (stop coins) coins)))) =
      (fairCoinStreamLaw.map split).map reindex := by
        rw [Measure.map_map hreindex hsplit]
        rfl
    _ = ((fairCoinStreamLaw.map observed).prod fairCoinStreamLaw).map
          reindex := by
        rw [fairCoinStreamLaw_firstExit_localRead_stoppedPrefix_shift_law
          s pending threshold hthreshold read hread hfair hlocal]
    _ = ((fairCoinStreamLaw.map observed).map id).prod
          (fairCoinStreamLaw.map (fun coins =>
            (jointOldRead coins,
              jointFreshRead coins))) := by
        exact (Measure.map_prod_map _ fairCoinStreamLaw measurable_id
          measurable_jointRead).symm
    _ = _ := by
      rw [Measure.map_id, fairCoinStreamLaw_jointRead]

theorem joint_localRead_stoppedRoundPrefix_jointTail_law
    {n : Nat} (s : TTCState n) (pending : Nat) (threshold : Real)
    (hthreshold : 0 ≤ threshold)
    (read : (Nat × Nat → Bool) → Nat × Nat → Bool)
    (hread : Measurable read)
    (hfair : fairCoinStreamLaw.map read = fairCoinStreamLaw)
    (hlocal : ∀ r coins,
      coinPrefix r (read (coinPrefix r coins)) =
        coinPrefix r (read coins)) :
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
  let stop := fun coins => ttcPseudocode.secondLoopExitRound s pending threshold (read coins)
  let observed : (Nat × Nat → Bool) →
      Nat × (Nat × Nat → Bool) :=
    fun coins => (stop coins, coinPrefix (stop coins) coins)
  let split : (Nat × Nat → Bool) →
      (Nat × (Nat × Nat → Bool)) × (Nat × Nat → Bool) :=
    fun coins => (observed coins, shiftCoins (stop coins) coins)
  let reindex : ((Nat × (Nat × Nat → Bool)) × (Nat × Nat → Bool)) →
      (Nat × (Nat × Nat → Bool)) ×
        ((Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool)) :=
    Prod.map id (fun coins =>
      (jointOldRead coins, jointFreshRead coins))
  have hstop : Measurable stop :=
    (measurable_firstExitRound s pending threshold).comp hread
  have hobserved : Measurable observed := by
    have hprefixJoint : Measurable
        (fun z : Nat × (Nat × Nat → Bool) => coinPrefix z.1 z.2) := by
      apply measurable_from_prod_countable_right
      intro rounds
      exact measurable_coinPrefix rounds
    exact hstop.prodMk
      (hprefixJoint.comp (hstop.prodMk measurable_id))
  have hsplit : Measurable split :=
    hobserved.prodMk ((measurable_stoppedCoinPair stop hstop).snd)
  have hreindex : Measurable reindex :=
    measurable_fst.prodMk
      (measurable_jointRead.comp measurable_snd)
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  calc
    fairCoinStreamLaw.map
        (fun coins =>
          (observed coins,
            (jointOldRead (shiftCoins (stop coins) coins),
              jointFreshRead (shiftCoins (stop coins) coins)))) =
      (fairCoinStreamLaw.map split).map reindex := by
        rw [Measure.map_map hreindex hsplit]
        rfl
    _ = ((fairCoinStreamLaw.map observed).prod fairCoinStreamLaw).map
          reindex := by
        rw [fairCoinStreamLaw_firstExit_localRead_stoppedRoundPrefix_shift_law
          s pending threshold hthreshold read hread hfair hlocal]
    _ = ((fairCoinStreamLaw.map observed).map id).prod
          (fairCoinStreamLaw.map (fun coins =>
            (jointOldRead coins,
              jointFreshRead coins))) := by
        exact (Measure.map_prod_map _ fairCoinStreamLaw measurable_id
          measurable_jointRead).symm
    _ = _ := by
      rw [Measure.map_id, fairCoinStreamLaw_jointRead]

/-- The observed prefix may be projected from the encoded source to the
actual fair stream read by the loop, while the complete old/new tails stay
independent. -/
theorem joint_localRead_stoppedReadPrefix_jointTail_law
    {n : Nat} (s : TTCState n) (pending : Nat) (threshold : Real)
    (hthreshold : 0 ≤ threshold)
    (read : (Nat × Nat → Bool) → Nat × Nat → Bool)
    (hread : Measurable read)
    (hfair : fairCoinStreamLaw.map read = fairCoinStreamLaw)
    (hlocal : ∀ r coins,
      coinPrefix r (read (coinPrefix r coins)) =
        coinPrefix r (read coins)) :
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
  let stop := fun coins => ttcPseudocode.secondLoopExitRound s pending threshold (read coins)
  let rawObs : (Nat × Nat → Bool) → Nat × (Nat × Nat → Bool) :=
    fun coins => (stop coins, coinPrefix (stop coins) coins)
  let actualObs : (Nat × Nat → Bool) → Nat × (Nat × Nat → Bool) :=
    fun coins => (stop coins, coinPrefix (stop coins) (read coins))
  let project : (Nat × (Nat × Nat → Bool)) →
      Nat × (Nat × Nat → Bool) :=
    fun z => (z.1, coinPrefix z.1 (read z.2))
  have hproject : Measurable project := by
    have hprefixJoint : Measurable
        (fun z : Nat × (Nat × Nat → Bool) => coinPrefix z.1 z.2) := by
      apply measurable_from_prod_countable_right
      intro r
      exact measurable_coinPrefix r
    exact measurable_fst.prodMk
      (hprefixJoint.comp
        (measurable_fst.prodMk (hread.comp measurable_snd)))
  have hobs : project ∘ rawObs = actualObs := by
    funext coins
    apply Prod.ext
    · rfl
    · exact hlocal (stop coins) coins
  let tail : (Nat × Nat → Bool) →
      (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool) :=
    fun coins =>
      (jointOldRead (shiftCoins (stop coins) coins),
        jointFreshRead (shiftCoins (stop coins) coins))
  have hstop : Measurable stop :=
    (measurable_firstExitRound s pending threshold).comp hread
  have hrawObs : Measurable rawObs := by
    have hprefixJoint : Measurable
        (fun z : Nat × (Nat × Nat → Bool) => coinPrefix z.1 z.2) := by
      apply measurable_from_prod_countable_right
      intro r
      exact measurable_coinPrefix r
    exact hstop.prodMk
      (hprefixJoint.comp (hstop.prodMk measurable_id))
  have htail : Measurable tail :=
    measurable_jointRead.comp
      ((measurable_stoppedCoinPair stop hstop).snd)
  have hrawSplit : Measurable (fun coins => (rawObs coins, tail coins)) :=
    hrawObs.prodMk htail
  let reindex : ((Nat × (Nat × Nat → Bool)) ×
      ((Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool))) →
      (Nat × (Nat × Nat → Bool)) ×
        ((Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool)) :=
    Prod.map project id
  have hreindex : Measurable reindex :=
    (hproject.comp measurable_fst).prodMk measurable_snd
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  letI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
    fun _ => fairCoinLaw_isProbabilityMeasure
  letI : IsProbabilityMeasure
      (Measure.infinitePi
        (fun _ : Nat × (Nat × Nat) => fairCoinLaw)) := by
    infer_instance
  calc
    fairCoinStreamLaw.map (fun coins => (actualObs coins, tail coins)) =
      (fairCoinStreamLaw.map
        (fun coins => (rawObs coins, tail coins))).map reindex := by
        rw [Measure.map_map hreindex hrawSplit]
        congr 1
        funext coins
        exact Prod.ext (congrFun hobs coins).symm rfl
    _ = ((fairCoinStreamLaw.map rawObs).prod
        ((Measure.infinitePi
          (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
          fairCoinStreamLaw)).map reindex := by
        rw [joint_localRead_stoppedRoundPrefix_jointTail_law
          s pending threshold hthreshold read hread hfair hlocal]
    _ = ((fairCoinStreamLaw.map rawObs).map project).prod
        (((Measure.infinitePi
          (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
          fairCoinStreamLaw).map id) := by
        exact (Measure.map_prod_map _ _ hproject measurable_id).symm
    _ = (fairCoinStreamLaw.map actualObs).prod
        ((Measure.infinitePi
          (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
          fairCoinStreamLaw) := by
        rw [Measure.map_id]
        rw [Measure.map_map hproject hrawObs, hobs]

end ttc
