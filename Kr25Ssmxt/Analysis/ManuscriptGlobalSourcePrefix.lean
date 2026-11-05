import Kr25Ssmxt.Analysis.ManuscriptStoppedSurvivorIndex

/-! A fixed number of first-loop rounds separates the old global source
into its observed prefix and an independent global fair tail. -/

namespace Kr25Ssmxt

open MeasureTheory

def manuscriptGlobalSourcePrefix (rounds : Nat)
    (source : Nat × (Nat × Nat) → Bool) :
    Nat × (Nat × Nat) → Bool :=
  fun tag => if tag.2.1 < rounds then source tag else false

def manuscriptGlobalSourceShift (rounds : Nat)
    (source : Nat × (Nat × Nat) → Bool) :
    Nat × (Nat × Nat) → Bool :=
  fun tag => source (tag.1, (tag.2.1 + rounds, tag.2.2))

theorem manuscriptGlobalSourcePrefix_read (rounds : Nat)
    (coins : Nat × Nat → Bool) :
    manuscriptGlobalSourcePrefix rounds (manuscriptGlobalCoinRead coins) =
      manuscriptGlobalCoinRead (coinPrefix rounds coins) := by
  funext tag
  by_cases h : tag.2.1 < rounds <;>
    simp [manuscriptGlobalSourcePrefix, manuscriptGlobalCoinRead,
      manuscriptGlobalCoinIndex, coinPrefix, h]

theorem manuscriptGlobalSourceShift_read (rounds : Nat)
    (coins : Nat × Nat → Bool) :
    manuscriptGlobalSourceShift rounds (manuscriptGlobalCoinRead coins) =
      manuscriptGlobalCoinRead (shiftCoins rounds coins) := by
  funext tag
  rfl

theorem measurable_manuscriptGlobalSourcePrefix (rounds : Nat) :
    Measurable (manuscriptGlobalSourcePrefix rounds) := by
  apply Measurable.of_eval
  intro tag
  by_cases h : tag.2.1 < rounds
  · simpa [manuscriptGlobalSourcePrefix, h] using
      (measurable_pi_apply tag)
  · simp [manuscriptGlobalSourcePrefix, h]

theorem measurable_manuscriptGlobalSourceShift (rounds : Nat) :
    Measurable (manuscriptGlobalSourceShift rounds) := by
  exact Measurable.of_eval (fun tag =>
    measurable_pi_apply
      (tag.1, (tag.2.1 + rounds, tag.2.2)))

theorem manuscriptGlobalSource_prefix_shift_law (rounds : Nat) :
    (Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).map
        (fun source =>
          (manuscriptGlobalSourcePrefix rounds source,
            manuscriptGlobalSourceShift rounds source)) =
    ((Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).map
        (manuscriptGlobalSourcePrefix rounds)).prod
      (Measure.infinitePi
        (fun _ : Nat × (Nat × Nat) => fairCoinLaw)) := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  let pairRead : ((Nat × Nat → Bool) × (Nat × Nat → Bool)) →
      (Nat × (Nat × Nat) → Bool) × (Nat × (Nat × Nat) → Bool) :=
    Prod.map manuscriptGlobalCoinRead manuscriptGlobalCoinRead
  have hpairRead : Measurable pairRead :=
    (measurable_manuscriptGlobalCoinRead.comp measurable_fst).prodMk
      (measurable_manuscriptGlobalCoinRead.comp measurable_snd)
  have hsource : sourceLaw =
      fairCoinStreamLaw.map manuscriptGlobalCoinRead :=
    fairCoinStreamLaw_globalCoinRead.symm
  have hsplit : Measurable
      (fun coins : Nat × Nat → Bool =>
        (coinPrefix rounds coins, shiftCoins rounds coins)) :=
    (measurable_coinPrefix rounds).prodMk
      (measurable_shiftCoins rounds)
  have hglobalSplit : Measurable
      (fun source : Nat × (Nat × Nat) → Bool =>
        (manuscriptGlobalSourcePrefix rounds source,
          manuscriptGlobalSourceShift rounds source)) :=
    (measurable_manuscriptGlobalSourcePrefix rounds).prodMk
      (measurable_manuscriptGlobalSourceShift rounds)
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  calc
    sourceLaw.map (fun source =>
        (manuscriptGlobalSourcePrefix rounds source,
          manuscriptGlobalSourceShift rounds source)) =
      (fairCoinStreamLaw.map manuscriptGlobalCoinRead).map
        (fun source =>
          (manuscriptGlobalSourcePrefix rounds source,
            manuscriptGlobalSourceShift rounds source)) := by rw [← hsource]
    _ = fairCoinStreamLaw.map (fun coins =>
        (manuscriptGlobalCoinRead (coinPrefix rounds coins),
          manuscriptGlobalCoinRead (shiftCoins rounds coins))) := by
        rw [Measure.map_map hglobalSplit measurable_manuscriptGlobalCoinRead]
        congr 1
    _ = (fairCoinStreamLaw.map (fun coins =>
        (coinPrefix rounds coins, shiftCoins rounds coins))).map
          pairRead := by
        rw [Measure.map_map hpairRead hsplit]
        rfl
    _ = ((fairCoinStreamLaw.map (coinPrefix rounds)).prod
        fairCoinStreamLaw).map pairRead := by
        rw [fairCoinStreamLaw_prefix_shift rounds]
    _ = ((fairCoinStreamLaw.map (coinPrefix rounds)).map
        manuscriptGlobalCoinRead).prod
          (fairCoinStreamLaw.map manuscriptGlobalCoinRead) := by
        exact (Measure.map_prod_map _ fairCoinStreamLaw
          measurable_manuscriptGlobalCoinRead
          measurable_manuscriptGlobalCoinRead).symm
    _ = (sourceLaw.map (manuscriptGlobalSourcePrefix rounds)).prod
          sourceLaw := by
        rw [← hsource]
        have hprefixMap : sourceLaw.map
            (manuscriptGlobalSourcePrefix rounds) =
            (fairCoinStreamLaw.map (coinPrefix rounds)).map
              manuscriptGlobalCoinRead := by
          rw [hsource, Measure.map_map
            (measurable_manuscriptGlobalSourcePrefix rounds)
            measurable_manuscriptGlobalCoinRead]
          rw [Measure.map_map measurable_manuscriptGlobalCoinRead
            (measurable_coinPrefix rounds)]
          congr 1
        rw [hprefixMap]

theorem manuscriptGlobalSource_prefix_with_fresh_law (rounds : Nat) :
    ((Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
      fairCoinStreamLaw).map
      (fun z =>
        (manuscriptGlobalSourcePrefix rounds z.1,
          (manuscriptGlobalSourceShift rounds z.1, z.2))) =
    ((Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).map
      (manuscriptGlobalSourcePrefix rounds)).prod
      ((Measure.infinitePi
        (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
        fairCoinStreamLaw) := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  let splitOld : (Nat × (Nat × Nat) → Bool) →
      (Nat × (Nat × Nat) → Bool) × (Nat × (Nat × Nat) → Bool) :=
    fun source =>
      (manuscriptGlobalSourcePrefix rounds source,
        manuscriptGlobalSourceShift rounds source)
  have hsplitOld : Measurable splitOld :=
    (measurable_manuscriptGlobalSourcePrefix rounds).prodMk
      (measurable_manuscriptGlobalSourceShift rounds)
  let assoc : (((Nat × (Nat × Nat) → Bool) ×
      (Nat × (Nat × Nat) → Bool)) × (Nat × Nat → Bool)) ≃ᵐ
      ((Nat × (Nat × Nat) → Bool) ×
        ((Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool))) :=
    MeasurableEquiv.prodAssoc
  have hpairMap : Measurable
      (fun z : (Nat × (Nat × Nat) → Bool) × (Nat × Nat → Bool) =>
        (splitOld z.1, z.2)) :=
    (hsplitOld.comp measurable_fst).prodMk measurable_snd
  letI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
    fun _ => fairCoinLaw_isProbabilityMeasure
  letI : IsProbabilityMeasure sourceLaw := by
    dsimp [sourceLaw]
    infer_instance
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  calc
    (sourceLaw.prod fairCoinStreamLaw).map
        (fun z =>
          (manuscriptGlobalSourcePrefix rounds z.1,
            (manuscriptGlobalSourceShift rounds z.1, z.2))) =
      ((sourceLaw.prod fairCoinStreamLaw).map
        (fun z => (splitOld z.1, z.2))).map assoc := by
          rw [Measure.map_map assoc.measurable hpairMap]
          rfl
    _ = ((sourceLaw.map splitOld).prod
        (fairCoinStreamLaw.map id)).map assoc := by
          rw [Measure.map_prod_map sourceLaw fairCoinStreamLaw
            hsplitOld measurable_id]
          rfl
    _ = (((sourceLaw.map
        (manuscriptGlobalSourcePrefix rounds)).prod sourceLaw).prod
          fairCoinStreamLaw).map assoc := by
          rw [Measure.map_id]
          rw [manuscriptGlobalSource_prefix_shift_law rounds]
    _ = (sourceLaw.map (manuscriptGlobalSourcePrefix rounds)).prod
        (sourceLaw.prod fairCoinStreamLaw) := by
          exact Measure.prodAssoc_prod

end Kr25Ssmxt
