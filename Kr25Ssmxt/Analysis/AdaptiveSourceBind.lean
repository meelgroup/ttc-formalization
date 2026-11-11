import Kr25Ssmxt.Analysis.MathlibCompat
import Kr25Ssmxt.Analysis.OldCoinKernel

/-! The allocated-label source law can be used inside a measure-valued
adaptive continuation, including all later random choices of a component. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem origin_futureCoins_adaptive_bind
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (preLaw : Measure α)
    (nextLabel processed : α → Nat)
    (origin : α → Nat → Nat × Nat)
    (hhistory : ∀ᵐ a ∂preLaw,
      OriginHistory (nextLabel a) (processed a) (origin a))
    (K : (a : α) → (Nat × Fin (nextLabel a) → Bool) → Measure β)
    (hK : ∀ a, Measurable (K a)) :
    let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
      Measure.infinitePi (fun _ => fairCoinLaw)
    preLaw.bind (fun a => sourceLaw.bind fun source =>
      K a (fun pair => source
        (originCoinIndex (nextLabel a) (origin a) pair))) =
    preLaw.bind (fun a =>
      (Measure.infinitePi
        (fun _ : Nat × Fin (nextLabel a) => fairCoinLaw)).bind (K a)) := by
  dsimp only
  apply Measure.bind_congr_right
  filter_upwards [hhistory] with a ha
  let read : (Nat × (Nat × Nat) → Bool) →
      Nat × Fin (nextLabel a) → Bool :=
    fun source pair => source
      (originCoinIndex (nextLabel a) (origin a) pair)
  have hread : Measurable read :=
    Measurable.of_eval (fun pair =>
      measurable_pi_apply
        (originCoinIndex (nextLabel a) (origin a) pair))
  have hmap : (Measure.infinitePi
        (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).map read =
      Measure.infinitePi
        (fun _ : Nat × Fin (nextLabel a) => fairCoinLaw) :=
    origin_coins_on_allocated_labels
      (nextLabel a) (processed a) (origin a) ha
  change (Measure.infinitePi
      (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).bind
        (fun source => K a (read source)) = _
  rw [← bind_mapped_measure _ read hread (K a) (hK a), hmap]

/-- Any observed history and independent component source can be used to
drive an adaptive continuation with a finite fair block on allocated labels.
This is the measure-level form needed for fold induction. -/
theorem independentSource_adaptive_bind
    {ω α β : Type*} [MeasurableSpace ω] [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure ω)
    (observed : ω → α)
    (source : ω → Nat × (Nat × Nat) → Bool)
    (hsplit : Measurable (fun x => (observed x, source x)))
    (hproduct : μ.map (fun x => (observed x, source x)) =
      (μ.map observed).prod
        (Measure.infinitePi
          (fun _ : Nat × (Nat × Nat) => fairCoinLaw)))
    (nextLabel processed : α → Nat)
    (origin : α → Nat → Nat × Nat)
    (hhistory : ∀ᵐ a ∂μ.map observed,
      OriginHistory (nextLabel a) (processed a) (origin a))
    (K : (a : α) → (Nat × Fin (nextLabel a) → Bool) → Measure β)
    (hK : ∀ a, Measurable (K a))
    (hjoint : Measurable
      (fun z : α × (Nat × (Nat × Nat) → Bool) =>
        K z.1 (fun pair => z.2
          (originCoinIndex (nextLabel z.1)
            (origin z.1) pair)))) :
    μ.bind (fun x =>
      K (observed x) (fun pair =>
        source x (originCoinIndex (nextLabel (observed x))
          (origin (observed x)) pair))) =
    (μ.map observed).bind (fun a =>
      (Measure.infinitePi
        (fun _ : Nat × Fin (nextLabel a) => fairCoinLaw)).bind (K a)) := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  let preLaw := μ.map observed
  let split : ω → α × (Nat × (Nat × Nat) → Bool) :=
    fun x => (observed x, source x)
  let joint : α × (Nat × (Nat × Nat) → Bool) → Measure β :=
    fun z => K z.1 (fun pair => z.2
      (originCoinIndex (nextLabel z.1) (origin z.1) pair))
  have hpreSource : Measurable (fun a : α =>
      sourceLaw.map (Prod.mk a)) := by
    letI : IsProbabilityMeasure sourceLaw := by
      dsimp [sourceLaw]
      letI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
        fun _ => fairCoinLaw_isProbabilityMeasure
      infer_instance
    exact Measurable.map_prodMk_left
  calc
    μ.bind (fun x => joint (split x)) =
      (μ.map split).bind joint :=
        (bind_mapped_measure μ split hsplit joint hjoint).symm
    _ = (preLaw.prod sourceLaw).bind joint := by rw [hproduct]
    _ = preLaw.bind (fun a =>
        sourceLaw.bind fun src => joint (a, src)) := by
      haveI : IsProbabilityMeasure sourceLaw := by
        dsimp [sourceLaw]
        haveI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
          fun _ => fairCoinLaw_isProbabilityMeasure
        infer_instance
      rw [Measure.prod_eq_bind_map]
      rw [Measure.bind_bind hpreSource.aemeasurable hjoint.aemeasurable]
      congr 1
      funext a
      exact bind_mapped_measure sourceLaw (Prod.mk a)
        measurable_prodMk_left joint hjoint
    _ = _ := origin_futureCoins_adaptive_bind preLaw
      nextLabel processed origin hhistory K hK

/-- A measure-valued continuation may read the allocated old-copy coins from
the persistent global stream after an adaptively determined prefix. -/
theorem fairCoinStreamLaw_prefix_originFuture_adaptive_bind
    {β : Type*} [MeasurableSpace β]
    (level : Nat)
    (nextLabel processed : (Nat × Nat → Bool) → Nat)
    (origin : (Nat × Nat → Bool) → Nat → Nat × Nat)
    (hhistory : ∀ᵐ pre ∂fairCoinStreamLaw.map (coinPrefix level),
      OriginHistory (nextLabel pre) (processed pre)
        (origin pre))
    (K : (pre : Nat × Nat → Bool) →
      (Nat × Fin (nextLabel pre) → Bool) → Measure β)
    (hK : ∀ pre, Measurable (K pre))
    (hjoint : Measurable
      (fun z : (Nat × Nat → Bool) × (Nat × (Nat × Nat) → Bool) =>
        K z.1 (fun pair => z.2
          (originCoinIndex (nextLabel z.1) (origin z.1) pair)))) :
    fairCoinStreamLaw.bind
      (fun coins =>
        let pre := coinPrefix level coins
        K pre (fun pair =>
          globalCoinRead (shiftCoins level coins)
            (originCoinIndex (nextLabel pre)
              (origin pre) pair))) =
    (fairCoinStreamLaw.map (coinPrefix level)).bind (fun pre =>
      (Measure.infinitePi
        (fun _ : Nat × Fin (nextLabel pre) => fairCoinLaw)).bind (K pre)) := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  letI : IsProbabilityMeasure sourceLaw := by
    dsimp [sourceLaw]
    letI : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
      fun _ => fairCoinLaw_isProbabilityMeasure
    infer_instance
  let f : (Nat × Nat → Bool) × (Nat × (Nat × Nat) → Bool) → Measure β :=
    fun z => K z.1 (fun pair => z.2
      (originCoinIndex (nextLabel z.1) (origin z.1) pair))
  have hf : Measurable f := hjoint
  have hsourceFamily : Measurable
      (fun pre => sourceLaw.map (fun source => f (pre, source))) := by
    have hleft : Measurable
        (fun pre : Nat × Nat → Bool => sourceLaw.map (Prod.mk pre)) :=
      Measurable.map_prodMk_left
    have hright := (Measure.measurable_map f hf).comp hleft
    convert hright using 1
    funext pre
    change sourceLaw.map (fun source => f (pre, source)) =
      (sourceLaw.map (Prod.mk pre)).map f
    rw [Measure.map_map hf measurable_prodMk_left]
    rfl
  have hfamily : AEMeasurable
      (fun pre =>
        (Measure.infinitePi
          (fun _ : Nat × Fin (nextLabel pre) => fairCoinLaw)).map (K pre))
      (fairCoinStreamLaw.map (coinPrefix level)) := by
    apply AEMeasurable.congr hsourceFamily.aemeasurable
    filter_upwards [hhistory] with pre ha
    let read : (Nat × (Nat × Nat) → Bool) →
        Nat × Fin (nextLabel pre) → Bool :=
      fun source pair => source
        (originCoinIndex (nextLabel pre) (origin pre) pair)
    have hread : Measurable read :=
      Measurable.of_eval (fun pair =>
        measurable_pi_apply
          (originCoinIndex (nextLabel pre) (origin pre) pair))
    have hmap := origin_coins_on_allocated_labels
      (nextLabel pre) (processed pre) (origin pre) ha
    change sourceLaw.map (K pre ∘ read) =
      (Measure.infinitePi
        (fun _ : Nat × Fin (nextLabel pre) => fairCoinLaw)).map (K pre)
    rw [← Measure.map_map (hK pre) hread]
    exact congrArg (fun μ => μ.map (K pre)) hmap
  have hmap := fairCoinStreamLaw_prefix_originFuture_adaptive level
    nextLabel processed origin hhistory K hK hjoint
  have hjoin := congrArg Measure.join hmap
  change fairCoinStreamLaw.bind
      (fun coins =>
        let pre := coinPrefix level coins
        K pre (fun pair =>
          globalCoinRead (shiftCoins level coins)
            (originCoinIndex (nextLabel pre)
              (origin pre) pair))) =
    Measure.join ((fairCoinStreamLaw.map (coinPrefix level)).bind
      (fun pre =>
        (Measure.infinitePi
          (fun _ : Nat × Fin (nextLabel pre) => fairCoinLaw)).map (K pre))) at hjoin
  rw [Measure.join_eq_bind, Measure.bind_bind hfamily
    measurable_id.aemeasurable] at hjoin
  refine hjoin.trans ?_
  congr 1
  funext pre
  exact bind_mapped_measure _ (K pre) (hK pre) id measurable_id

end Kr25Ssmxt
