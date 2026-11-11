import Kr25Ssmxt.Analysis.StoppedSurvivorIndex

/-! A fixed number of first-loop rounds separates the old global source
into its observed prefix and an independent global fair tail. -/

namespace Kr25Ssmxt

open MeasureTheory

def globalSourcePrefix (rounds : Nat)
    (source : Nat × (Nat × Nat) → Bool) :
    Nat × (Nat × Nat) → Bool :=
  fun tag => if tag.2.1 < rounds then source tag else false

def globalSourceShift (rounds : Nat)
    (source : Nat × (Nat × Nat) → Bool) :
    Nat × (Nat × Nat) → Bool :=
  fun tag => source (tag.1, (tag.2.1 + rounds, tag.2.2))

theorem globalSourcePrefix_read (rounds : Nat)
    (coins : Nat × Nat → Bool) :
    globalSourcePrefix rounds (globalCoinRead coins) =
      globalCoinRead (coinPrefix rounds coins) := by
  funext tag
  by_cases h : tag.2.1 < rounds <;>
    simp [globalSourcePrefix, globalCoinRead,
      globalCoinIndex, coinPrefix, h]

theorem globalSourceShift_read (rounds : Nat)
    (coins : Nat × Nat → Bool) :
    globalSourceShift rounds (globalCoinRead coins) =
      globalCoinRead (shiftCoins rounds coins) := by
  funext tag
  rfl

theorem measurable_globalSourcePrefix (rounds : Nat) :
    Measurable (globalSourcePrefix rounds) := by
  apply Measurable.of_eval
  intro tag
  by_cases h : tag.2.1 < rounds
  · simpa [globalSourcePrefix, h] using
      (measurable_pi_apply tag)
  · simp [globalSourcePrefix, h]

theorem measurable_globalSourceShift (rounds : Nat) :
    Measurable (globalSourceShift rounds) := by
  exact Measurable.of_eval (fun tag =>
    measurable_pi_apply
      (tag.1, (tag.2.1 + rounds, tag.2.2)))

theorem globalSource_prefix_shift_law (rounds : Nat) :
    (Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).map
        (fun source =>
          (globalSourcePrefix rounds source,
            globalSourceShift rounds source)) =
    ((Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).map
        (globalSourcePrefix rounds)).prod
      (Measure.infinitePi
        (fun _ : Nat × (Nat × Nat) => fairCoinLaw)) := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  let pairRead : ((Nat × Nat → Bool) × (Nat × Nat → Bool)) →
      (Nat × (Nat × Nat) → Bool) × (Nat × (Nat × Nat) → Bool) :=
    Prod.map globalCoinRead globalCoinRead
  have hpairRead : Measurable pairRead :=
    (measurable_globalCoinRead.comp measurable_fst).prodMk
      (measurable_globalCoinRead.comp measurable_snd)
  have hsource : sourceLaw =
      fairCoinStreamLaw.map globalCoinRead :=
    fairCoinStreamLaw_globalCoinRead.symm
  have hsplit : Measurable
      (fun coins : Nat × Nat → Bool =>
        (coinPrefix rounds coins, shiftCoins rounds coins)) :=
    (measurable_coinPrefix rounds).prodMk
      (measurable_shiftCoins rounds)
  have hglobalSplit : Measurable
      (fun source : Nat × (Nat × Nat) → Bool =>
        (globalSourcePrefix rounds source,
          globalSourceShift rounds source)) :=
    (measurable_globalSourcePrefix rounds).prodMk
      (measurable_globalSourceShift rounds)
  letI : IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  calc
    sourceLaw.map (fun source =>
        (globalSourcePrefix rounds source,
          globalSourceShift rounds source)) =
      (fairCoinStreamLaw.map globalCoinRead).map
        (fun source =>
          (globalSourcePrefix rounds source,
            globalSourceShift rounds source)) := by rw [← hsource]
    _ = fairCoinStreamLaw.map (fun coins =>
        (globalCoinRead (coinPrefix rounds coins),
          globalCoinRead (shiftCoins rounds coins))) := by
        rw [Measure.map_map hglobalSplit measurable_globalCoinRead]
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
        globalCoinRead).prod
          (fairCoinStreamLaw.map globalCoinRead) := by
        exact (Measure.map_prod_map _ fairCoinStreamLaw
          measurable_globalCoinRead
          measurable_globalCoinRead).symm
    _ = (sourceLaw.map (globalSourcePrefix rounds)).prod
          sourceLaw := by
        rw [← hsource]
        have hprefixMap : sourceLaw.map
            (globalSourcePrefix rounds) =
            (fairCoinStreamLaw.map (coinPrefix rounds)).map
              globalCoinRead := by
          rw [hsource, Measure.map_map
            (measurable_globalSourcePrefix rounds)
            measurable_globalCoinRead]
          rw [Measure.map_map measurable_globalCoinRead
            (measurable_coinPrefix rounds)]
          congr 1
        rw [hprefixMap]

theorem globalSource_prefix_with_fresh_law (rounds : Nat) :
    ((Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
      fairCoinStreamLaw).map
      (fun z =>
        (globalSourcePrefix rounds z.1,
          (globalSourceShift rounds z.1, z.2))) =
    ((Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).map
      (globalSourcePrefix rounds)).prod
      ((Measure.infinitePi
        (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).prod
        fairCoinStreamLaw) := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  let splitOld : (Nat × (Nat × Nat) → Bool) →
      (Nat × (Nat × Nat) → Bool) × (Nat × (Nat × Nat) → Bool) :=
    fun source =>
      (globalSourcePrefix rounds source,
        globalSourceShift rounds source)
  have hsplitOld : Measurable splitOld :=
    (measurable_globalSourcePrefix rounds).prodMk
      (measurable_globalSourceShift rounds)
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
          (globalSourcePrefix rounds z.1,
            (globalSourceShift rounds z.1, z.2))) =
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
        (globalSourcePrefix rounds)).prod sourceLaw).prod
          fairCoinStreamLaw).map assoc := by
          rw [Measure.map_id]
          rw [globalSource_prefix_shift_law rounds]
    _ = (sourceLaw.map (globalSourcePrefix rounds)).prod
        (sourceLaw.prod fairCoinStreamLaw) := by
          exact Measure.prodAssoc_prod

end Kr25Ssmxt
