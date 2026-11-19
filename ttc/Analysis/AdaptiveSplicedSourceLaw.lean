import ttc.Analysis.MathlibCompat
import ttc.Analysis.SplicedSourcePointLaw

/-! A new component's Poisson count, spliced fair coins, and point tape form
one independent Poisson source even when the splice round is selected by the
incoming history. -/

namespace ttc

open Classical MeasureTheory

noncomputable def splicedSourceLaw
    {n : Nat} (mean : NNReal)
    (pointLaw : Measure (LatticePoint n)) (preRounds : Nat) :
    Measure (PoissonTape n) :=
  (ProbabilityTheory.poissonMeasure mean).bind fun pending =>
    (fairCoinStreamLaw.prod fairCoinStreamLaw).bind fun pair =>
      (Measure.infinitePi (fun _ : Nat => pointLaw)).map fun tape =>
        (pending, spliceCoins pair.1 pair.2 preRounds, tape)

theorem splicedSourceLaw_eq_poissonTape
    {n : Nat} (mean : NNReal)
    (pointLaw : Measure (LatticePoint n))
    [IsProbabilityMeasure pointLaw] (preRounds : Nat) :
    splicedSourceLaw mean pointLaw preRounds =
      poissonTapeLaw mean pointLaw := by
  let tapeLaw : Measure (Nat → LatticePoint n) :=
    Measure.infinitePi (fun _ : Nat => pointLaw)
  letI : IsProbabilityMeasure tapeLaw := inferInstance
  let K (pending : Nat) (coins : Nat × Nat → Bool) :
      Measure (PoissonTape n) :=
    tapeLaw.map fun tape => (pending, coins, tape)
  have hK (pending : Nat) : Measurable (K pending) := by
    apply measurable_parametric_probability_map
      (fun _ : Nat × Nat → Bool => tapeLaw) measurable_const
      (fun _ => inferInstance)
      (fun z : (Nat × Nat → Bool) × (Nat → LatticePoint n) =>
        (pending, z.1, z.2))
    fun_prop
  have hinner (pending : Nat) :
      (fairCoinStreamLaw.prod fairCoinStreamLaw).bind
        (fun pair => K pending (spliceCoins pair.1 pair.2 preRounds)) =
      fairCoinStreamLaw.bind (K pending) := by
    let splice : ((Nat × Nat → Bool) × (Nat × Nat → Bool)) →
        Nat × Nat → Bool := fun pair =>
      spliceCoins pair.1 pair.2 preRounds
    calc
      (fairCoinStreamLaw.prod fairCoinStreamLaw).bind
          (fun pair => K pending (splice pair)) =
        ((fairCoinStreamLaw.prod fairCoinStreamLaw).map splice).bind
          (K pending) := by
            exact (bind_mapped_measure _ splice
              (measurable_spliceCoins_pair preRounds)
              (K pending) (hK pending)).symm
      _ = fairCoinStreamLaw.bind (K pending) := by
        rw [fairCoinStreamLaw_splice preRounds]
  unfold splicedSourceLaw poissonTapeLaw
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro pending
  exact hinner pending

theorem splicedSourceLaw_adaptive_product
    {n : Nat} {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (mean : NNReal)
    (pointLaw : Measure (LatticePoint n))
    [IsProbabilityMeasure pointLaw] (preRounds : α → Nat) :
    μ.bind (fun a => (splicedSourceLaw mean pointLaw
      (preRounds a)).map (Prod.mk a)) =
    μ.prod (poissonTapeLaw mean pointLaw) := by
  simp_rw [splicedSourceLaw_eq_poissonTape]
  haveI := poissonTapeLaw_isProbabilityMeasure mean pointLaw
  rw [Measure.prod_eq_bind_map]

theorem splicedSourceLaw_adaptive_conditional
    {n : Nat} {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (mean : α → NNReal)
    (pointLaw : Measure (LatticePoint n))
    [IsProbabilityMeasure pointLaw] (preRounds : α → Nat) :
    μ.bind (fun a => (splicedSourceLaw (mean a) pointLaw
      (preRounds a)).map (Prod.mk a)) =
    μ.bind (fun a => (poissonTapeLaw (mean a) pointLaw).map
      (Prod.mk a)) := by
  simp_rw [splicedSourceLaw_eq_poissonTape]

theorem splicedSourceLaw_fixedLevel_pointCounts
    {n : Nat} (mean : NNReal)
    (pointLaw : Measure (LatticePoint n))
    [IsProbabilityMeasure pointLaw]
    (S : Finset (LatticePoint n))
    (hsupport : pointLaw (S : Set (LatticePoint n))ᶜ = 0)
    (firstLabel level preRounds : Nat) :
    (splicedSourceLaw mean pointLaw preRounds).map
      (poissonTapePointCounts S firstLabel level) =
    Measure.pi (fun x : S => ProbabilityTheory.poissonMeasure
      (Real.toNNReal
        (pointLaw.real {(x : LatticePoint n)} *
          ((unitInterval.toNNReal (survivalProbability level) *
            mean : NNReal) : Real)))) := by
  rw [splicedSourceLaw_eq_poissonTape]
  exact poissonTapeLaw_fixedLevel_pointCounts mean pointLaw
    S hsupport firstLabel level

set_option maxHeartbeats 1000000 in
theorem splicedSourceLaw_adaptive_fixedLevel_product
    {n : Nat} {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (mean : NNReal)
    (pointLaw : Measure (LatticePoint n))
    [IsProbabilityMeasure pointLaw]
    (S : Finset (LatticePoint n))
    (hsupport : pointLaw (S : Set (LatticePoint n))ᶜ = 0)
    (firstLabel preRounds : α → Nat) (level : Nat) :
    μ.bind (fun a =>
      (splicedSourceLaw mean pointLaw (preRounds a)).map
        (fun source =>
          (a, poissonTapePointCounts S (firstLabel a)
            level source))) =
    μ.prod (Measure.pi (fun x : S => ProbabilityTheory.poissonMeasure
      (Real.toNNReal
        (pointLaw.real {(x : LatticePoint n)} *
          ((unitInterval.toNNReal (survivalProbability level) *
            mean : NNReal) : Real))))) := by
  let q : Measure (S → Nat) := Measure.pi
    (fun x : S => ProbabilityTheory.poissonMeasure
      (Real.toNNReal
        (pointLaw.real {(x : LatticePoint n)} *
          ((unitInterval.toNNReal (survivalProbability level) *
            mean : NNReal) : Real))))
  have hinner (a : α) :
      (splicedSourceLaw mean pointLaw (preRounds a)).map
        (fun source => (a, poissonTapePointCounts S
          (firstLabel a) level source)) =
      q.map (Prod.mk a) := by
    have hcount := measurable_poissonTapePointCounts S
      (firstLabel a) level
    rw [show (fun source : PoissonTape n =>
        (a, poissonTapePointCounts S (firstLabel a)
          level source)) =
        (Prod.mk a) ∘ poissonTapePointCounts S
          (firstLabel a) level from rfl]
    rw [← Measure.map_map measurable_prodMk_left hcount]
    rw [splicedSourceLaw_fixedLevel_pointCounts mean pointLaw
      S hsupport (firstLabel a) level (preRounds a)]
  haveI := poissonTapeLaw_isProbabilityMeasure mean pointLaw
  rw [Measure.prod_eq_bind_map]
  exact Measure.bind_congr_right
    (Filter.Eventually.of_forall hinner)

noncomputable def OriginSourceState.stepPoissonTape
    {n : Nat} (g : OriginSourceState n)
    (P : PolytopeData n) (firstLabel : Nat)
    (source : PoissonTape n) : OriginSourceState n where
  processed := g.processed + 1
  valid := validUpdate g.valid g.marks P g.processed
    firstLabel source.1
  marks := marksAppend g.marks g.processed source.2.2
  coins := fun c => if c = g.processed then source.2.1 else g.coins c

theorem OriginSourceState.step_eq_stepPoissonTape
    {n : Nat} (g : OriginSourceState n)
    (step : OriginSourceStep n) :
    g.step step = g.stepPoissonTape step.component step.firstLabel
      (step.basePending,
        spliceCoins step.preCoins step.futureCoins step.preRounds,
        step.tape) := by
  rfl

theorem OriginSourceState.stepPoissonTape_pointCounts
    {n : Nat} (g : OriginSourceState n)
    (P : PolytopeData n) (firstLabel level : Nat)
    (source : PoissonTape n)
    (S : Finset (LatticePoint n))
    (hbound : ValidBound g.valid g.processed) :
    (g.stepPoissonTape P firstLabel source).pointCounts level S =
      fun x : S =>
        (if x.1.toPoint ∈ P.carrier then 0 else
          g.pointCounts level S x) +
        poissonTapePointCounts S firstLabel level source x := by
  classical
  let step : OriginSourceStep n :=
    { component := P
      firstLabel := firstLabel
      basePending := source.1
      preRounds := 0
      preCoins := source.2.1
      futureCoins := source.2.1
      tape := source.2.2 }
  have hstep : g.step step = g.stepPoissonTape P firstLabel source := by
    have hcoins : coinsAppend g.coins g.processed
        source.2.1 source.2.1 0 =
        (fun c => if c = g.processed then source.2.1 else g.coins c) := by
      funext c pair
      by_cases hc : c = g.processed <;>
        simp [coinsAppend, spliceCoins, hc]
    simp [OriginSourceState.step,
      OriginSourceState.stepPoissonTape, step, hcoins]
  rw [← hstep]
  have h := g.step_pointCounts step level S hbound
  have hsplice : spliceCoins source.2.1 source.2.1 0 = source.2.1 := by
    funext pair
    simp [spliceCoins]
  simpa [step, hsplice] using h

set_option maxHeartbeats 1000000 in
theorem OriginSourceState.stepPoissonTape_fixedLevel_law
    {n : Nat} (g : OriginSourceState n)
    (P : PolytopeData n) (firstLabel level preRounds : Nat)
    (mean : NNReal) (pointLaw : Measure (LatticePoint n))
    [IsProbabilityMeasure pointLaw]
    (S : Finset (LatticePoint n))
    (hsupport : pointLaw (S : Set (LatticePoint n))ᶜ = 0)
    (hbound : ValidBound g.valid g.processed) :
    (splicedSourceLaw mean pointLaw preRounds).map
      (fun source =>
        (g.stepPoissonTape P firstLabel source).pointCounts level S) =
    (Measure.pi (fun x : S => ProbabilityTheory.poissonMeasure
      (Real.toNNReal
        (pointLaw.real {(x : LatticePoint n)} *
          ((unitInterval.toNNReal (survivalProbability level) *
            mean : NNReal) : Real))))).map
      (fun incoming : S → Nat => fun x : S =>
        (if x.1.toPoint ∈ P.carrier then 0 else
          g.pointCounts level S x) + incoming x) := by
  let update : (S → Nat) → (S → Nat) := fun incoming x =>
    (if x.1.toPoint ∈ P.carrier then 0 else
      g.pointCounts level S x) + incoming x
  have hupdate : Measurable update := Measurable.of_discrete
  have hcounts := measurable_poissonTapePointCounts S
    firstLabel level
  have hfun : (fun source : PoissonTape n =>
      (g.stepPoissonTape P firstLabel source).pointCounts level S) =
      update ∘ poissonTapePointCounts S firstLabel level := by
    funext source
    exact g.stepPoissonTape_pointCounts P firstLabel level source S hbound
  rw [hfun]
  rw [← Measure.map_map hupdate hcounts]
  exact congrArg (fun μ : Measure (S → Nat) => μ.map update)
    (splicedSourceLaw_fixedLevel_pointCounts mean pointLaw
      S hsupport firstLabel level preRounds)

end ttc
