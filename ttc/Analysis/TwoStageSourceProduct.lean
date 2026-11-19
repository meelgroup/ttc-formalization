import ttc.Analysis.MathlibCompat
import ttc.Analysis.SurvivorPairTail

/-! Compose a deterministic observed-prefix split with a later stopped
observation/tail split. -/

namespace ttc

open MeasureTheory

theorem measure_twoStage_source_product
    {α β γ δ ε : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] [MeasurableSpace ε]
    (μ : Measure α) (preLaw : Measure β) (middleLaw : Measure γ)
    (obsLaw : Measure δ) (tailLaw : Measure ε)
    [SFinite preLaw] [SFinite middleLaw] [SFinite obsLaw]
    [SFinite tailLaw]
    (pre : α → β) (post : α → γ)
    (obs : γ → δ) (tail : γ → ε)
    (hpre : Measurable pre) (hpost : Measurable post)
    (hobs : Measurable obs) (htail : Measurable tail)
    (hfirst : μ.map (fun x => (pre x, post x)) =
      preLaw.prod middleLaw)
    (hsecond : middleLaw.map (fun y => (obs y, tail y)) =
      obsLaw.prod tailLaw) :
    μ.map (fun x => ((pre x, obs (post x)), tail (post x))) =
      (preLaw.prod obsLaw).prod tailLaw := by
  let split : α → β × γ := fun x => (pre x, post x)
  let next : γ → δ × ε := fun y => (obs y, tail y)
  let step : β × γ → β × (δ × ε) := Prod.map id next
  have hsplit : Measurable split := hpre.prodMk hpost
  have hnext : Measurable next := hobs.prodMk htail
  have hstep : Measurable step :=
    measurable_fst.prodMk (hnext.comp measurable_snd)
  have hforward : μ.map
      (fun x => (pre x, (obs (post x), tail (post x)))) =
      preLaw.prod (obsLaw.prod tailLaw) := by
    calc
      μ.map (fun x => (pre x, (obs (post x), tail (post x)))) =
        (μ.map split).map step := by
          rw [Measure.map_map hstep hsplit]
          rfl
      _ = (preLaw.prod middleLaw).map step := by rw [hfirst]
      _ = (preLaw.map id).prod (middleLaw.map next) := by
        exact (Measure.map_prod_map preLaw middleLaw measurable_id
          hnext).symm
      _ = preLaw.prod (obsLaw.prod tailLaw) := by
        rw [Measure.map_id, hsecond]
  let assoc : ((β × δ) × ε) ≃ᵐ (β × (δ × ε)) :=
    MeasurableEquiv.prodAssoc
  have hinner : Measurable (fun x : α =>
      (pre x, (obs (post x), tail (post x)))) :=
    hpre.prodMk ((hobs.comp hpost).prodMk (htail.comp hpost))
  calc
    μ.map (fun x => ((pre x, obs (post x)), tail (post x))) =
      (μ.map (fun x =>
        (pre x, (obs (post x), tail (post x))))).map assoc.symm := by
          rw [Measure.map_map assoc.symm.measurable hinner]
          rfl
    _ = (preLaw.prod (obsLaw.prod tailLaw)).map assoc.symm := by
      rw [hforward]
    _ = (preLaw.prod obsLaw).prod tailLaw := by
      rw [← Measure.prodAssoc_prod]
      rw [Measure.map_map assoc.symm.measurable assoc.measurable]
      simp

/-- Before the new-component point tape is sampled, the deterministic
rate-thinning prefix and the adaptive count-thinning observation are jointly
independent of the full remaining old/new source pair. -/
theorem firstAndSecondPrefix_tail_product
    {n : Nat} (s : TTCState n) (threshold : Real)
    (hthreshold : 0 ≤ threshold)
    (preCoins : Nat × Nat → Bool)
    (rounds preRounds basePending processed : Nat)
    (origin : Nat → Nat × Nat)
    (hhistory : OriginHistory s.nextLabel processed origin) :
    let sourceLaw := Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw)
    let μ := sourceLaw.prod fairCoinStreamLaw
    let obs := survivorPairObservation s threshold preCoins
      preRounds basePending origin
    let tail := survivorPairRemaining s threshold preCoins
      preRounds basePending origin
    μ.map (fun z =>
      ((globalSourcePrefix rounds z.1,
          obs (globalSourceShift rounds z.1, z.2)),
        tail (globalSourceShift rounds z.1, z.2))) =
      ((sourceLaw.map (globalSourcePrefix rounds)).prod
        (μ.map obs)).prod μ := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  let μ := sourceLaw.prod fairCoinStreamLaw
  let pre := fun z : (Nat × (Nat × Nat) → Bool) ×
      (Nat × Nat → Bool) => globalSourcePrefix rounds z.1
  let post := fun z : (Nat × (Nat × Nat) → Bool) ×
      (Nat × Nat → Bool) =>
    (globalSourceShift rounds z.1, z.2)
  let obs := survivorPairObservation s threshold preCoins
    preRounds basePending origin
  let tail := survivorPairRemaining s threshold preCoins
    preRounds basePending origin
  have hpre : Measurable pre :=
    (measurable_globalSourcePrefix rounds).comp
      measurable_fst
  have hpost : Measurable post :=
    ((measurable_globalSourceShift rounds).comp
      measurable_fst).prodMk measurable_snd
  have hobs : Measurable obs :=
    measurable_survivorPairObservation s threshold preCoins
      preRounds basePending origin
  have htail : Measurable tail :=
    measurable_survivorPairRemaining s threshold preCoins
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
      (sourceLaw.map (globalSourcePrefix rounds)) :=
    Measure.isProbabilityMeasure_map
      (measurable_globalSourcePrefix rounds).aemeasurable
  letI : IsProbabilityMeasure (μ.map obs) :=
    Measure.isProbabilityMeasure_map hobs.aemeasurable
  have hfirst : μ.map (fun z => (pre z, post z)) =
      (sourceLaw.map (globalSourcePrefix rounds)).prod μ :=
    globalSource_prefix_with_fresh_law rounds
  have hsecond : μ.map (fun y => (obs y, tail y)) =
      (μ.map obs).prod μ :=
    survivorPair_stoppedReadPrefix_tail_law s threshold
      hthreshold preCoins preRounds basePending processed origin hhistory
  exact measure_twoStage_source_product μ
    (sourceLaw.map (globalSourcePrefix rounds)) μ
    (μ.map obs) μ pre post obs tail hpre hpost hobs htail
    hfirst hsecond

end ttc
