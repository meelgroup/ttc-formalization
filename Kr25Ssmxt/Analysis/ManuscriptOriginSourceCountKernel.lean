import Kr25Ssmxt.Analysis.ManuscriptAdaptiveFixedLevelUpdate
import Kr25Ssmxt.Analysis.ManuscriptOriginRandomCoinKernel

/-! The randomized ghost component's source marginal in its original draw
order, before refreshing old source tails. -/

namespace Kr25Ssmxt

open Classical MeasureTheory

theorem measurable_manuscriptOriginSourceState_stepPoissonTape
    {n : Nat} (g : ManuscriptOriginSourceState n)
    (P : PolytopeData n) (firstLabel : Nat) :
    Measurable (fun source : ManuscriptPoissonTape n =>
      g.stepPoissonTape P firstLabel source) := by
  apply measurable_from_prod_countable_right
  intro pending
  have hinput : Measurable (fun z :
      (Nat × Nat → Bool) × (Nat → LatticePoint n) =>
      ((firstLabel, 0), ((g, z.2), (z.1, z.1)))) := by
    exact measurable_const.prodMk
      ((measurable_const.prodMk measurable_snd).prodMk
        (measurable_fst.prodMk measurable_fst))
  have hcomp :=
    (measurable_manuscriptOriginSourceStepCoinPair P pending).comp hinput
  have heq : (fun z : (Nat × Nat → Bool) ×
      (Nat → LatticePoint n) =>
      manuscriptOriginSourceStepCoinPair P pending
        ((firstLabel, 0), ((g, z.2), (z.1, z.1)))) =
      (fun z => g.stepPoissonTape P firstLabel (pending, z.1, z.2)) := by
    funext z
    let step : ManuscriptOriginSourceStep n :=
      { component := P
        firstLabel := firstLabel
        basePending := pending
        preRounds := 0
        preCoins := z.1
        futureCoins := z.1
        tape := z.2 }
    change g.step step = g.stepPoissonTape P firstLabel
      (pending, z.1, z.2)
    have h := g.step_eq_stepPoissonTape step
    have hsplice : spliceCoins z.1 z.1 0 = z.1 := by
      funext pair
      simp [spliceCoins]
    simpa [step, hsplice] using h
  rw [← heq]
  exact hcomp

set_option maxHeartbeats 1000000 in
theorem manuscriptOriginPoissonCoinTapeLaw_map_source
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (c : ManuscriptOriginConfiguration n) :
    (manuscriptOriginPoissonCoinTapeLaw hn P b eta threshold hroute
      intensity c).map
        (fun next : ManuscriptOriginConfiguration n => next.source) =
    (ProbabilityTheory.poissonMeasure intensity).bind fun pending =>
      (fairCoinStreamLaw.prod fairCoinStreamLaw).bind fun pair =>
        (Measure.infinitePi (fun _ : Nat =>
          normalizedHitAndRunPointLaw hn P b hroute.1 eta hroute.2.1
            hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2)).map
          (fun tape => c.source.stepPoissonTape P c.state.nextLabel
            (pending, spliceCoins pair.1 pair.2
              (c.level + manuscriptRateExit (c.state.removeComponent P)
                intensity threshold), tape)) := by
  have hsource := measurable_manuscriptOriginConfiguration_source (n := n)
  have hK₁ : Measurable (fun pending : Nat =>
      manuscriptOriginFairCoinTapeLaw hn P b eta threshold hroute
        intensity pending c) := Measurable.of_discrete
  unfold manuscriptOriginPoissonCoinTapeLaw
  rw [map_bind_measure (ProbabilityTheory.poissonMeasure intensity)
    (fun pending => manuscriptOriginFairCoinTapeLaw hn P b eta threshold
      hroute intensity pending c) (fun next => next.source)
    hK₁.aemeasurable hsource]
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro pending
  have hK₂ : Measurable (fun pair :
      (Nat × Nat → Bool) × (Nat × Nat → Bool) =>
      manuscriptOriginCoinPairTapeLaw hn P b eta threshold hroute
        intensity pending (c, pair)) :=
    (measurable_manuscriptOriginCoinPairTapeLaw hn P b eta threshold
      hthreshold hroute intensity pending).comp
      (measurable_const.prodMk measurable_id)
  unfold manuscriptOriginFairCoinTapeLaw
  change ((fairCoinStreamLaw.prod fairCoinStreamLaw).bind
    (fun pair => manuscriptOriginCoinPairTapeLaw hn P b eta threshold
      hroute intensity pending (c, pair))).map
        (fun next : ManuscriptOriginConfiguration n => next.source) = _
  rw [map_bind_measure (fairCoinStreamLaw.prod fairCoinStreamLaw)
    (fun pair => manuscriptOriginCoinPairTapeLaw hn P b eta threshold
      hroute intensity pending (c, pair)) (fun next => next.source)
    hK₂.aemeasurable hsource]
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro pair
  unfold manuscriptOriginCoinPairTapeLaw
  change ((Measure.infinitePi (fun _ : Nat =>
      normalizedHitAndRunPointLaw hn P b hroute.1 eta hroute.2.1
        hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2)).map
      (fun tape => c.advance P intensity threshold pending pair.1
        pair.2 tape)).map
        (fun next : ManuscriptOriginConfiguration n => next.source) = _
  rw [Measure.map_map hsource
    (c.measurable_advance_tape P intensity threshold pending pair.1
      pair.2)]
  congr 1

set_option maxHeartbeats 1000000 in
theorem manuscriptOriginPoissonCoinTapeLaw_source_eq_spliced
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (c : ManuscriptOriginConfiguration n) :
    (manuscriptOriginPoissonCoinTapeLaw hn P b eta threshold hroute
      intensity c).map
        (fun next : ManuscriptOriginConfiguration n => next.source) =
    (manuscriptSplicedSourceLaw intensity
      (normalizedHitAndRunPointLaw hn P b hroute.1 eta hroute.2.1
        hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2)
      (c.level + manuscriptRateExit (c.state.removeComponent P)
        intensity threshold)).map
      (c.source.stepPoissonTape P c.state.nextLabel) := by
  let pointLaw := normalizedHitAndRunPointLaw hn P b hroute.1 eta
    hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
  letI : IsProbabilityMeasure pointLaw :=
    (P.normalizedHitAndRun_latticePointLaw hn b hroute.1
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2).1
  let tapeLaw : Measure (Nat → LatticePoint n) :=
    Measure.infinitePi (fun _ : Nat => pointLaw)
  letI : IsProbabilityMeasure tapeLaw := inferInstance
  let preRounds := c.level + manuscriptRateExit
    (c.state.removeComponent P) intensity threshold
  let result := c.source.stepPoissonTape P c.state.nextLabel
  have hresult : Measurable result :=
    measurable_manuscriptOriginSourceState_stepPoissonTape c.source P
      c.state.nextLabel
  let K₂ (pending : Nat) (pair :
      (Nat × Nat → Bool) × (Nat × Nat → Bool)) :
      Measure (ManuscriptPoissonTape n) :=
    tapeLaw.map (fun tape =>
      (pending, spliceCoins pair.1 pair.2 preRounds, tape))
  have hK₂ (pending : Nat) : Measurable (K₂ pending) := by
    apply measurable_parametric_probability_map
      (fun _ : (Nat × Nat → Bool) × (Nat × Nat → Bool) => tapeLaw)
      measurable_const (fun _ => inferInstance)
      (fun z : ((Nat × Nat → Bool) × (Nat × Nat → Bool)) ×
        (Nat → LatticePoint n) =>
        (pending, spliceCoins z.1.1 z.1.2 preRounds, z.2))
    exact measurable_const.prodMk
      (((measurable_spliceCoins_pair preRounds).comp measurable_fst).prodMk
        measurable_snd)
  let K₁ (pending : Nat) : Measure (ManuscriptPoissonTape n) :=
    (fairCoinStreamLaw.prod fairCoinStreamLaw).bind (K₂ pending)
  have hK₁ : Measurable K₁ := Measurable.of_discrete
  rw [manuscriptOriginPoissonCoinTapeLaw_map_source hn P b eta threshold
    hthreshold hroute intensity c]
  change _ = ((ProbabilityTheory.poissonMeasure intensity).bind K₁).map
    result
  rw [map_bind_measure (ProbabilityTheory.poissonMeasure intensity)
    K₁ result hK₁.aemeasurable hresult]
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro pending
  change _ = ((fairCoinStreamLaw.prod fairCoinStreamLaw).bind
    (K₂ pending)).map result
  rw [map_bind_measure (fairCoinStreamLaw.prod fairCoinStreamLaw)
    (K₂ pending) result (hK₂ pending).aemeasurable hresult]
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro pair
  change _ = (tapeLaw.map (fun tape =>
    (pending, spliceCoins pair.1 pair.2 preRounds, tape))).map result
  rw [Measure.map_map hresult (by fun_prop : Measurable
    (fun tape : Nat → LatticePoint n =>
      (pending, spliceCoins pair.1 pair.2 preRounds, tape)))]
  rfl

theorem manuscriptOriginPoissonCoinTapeLaw_source_eq_poissonTape
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (c : ManuscriptOriginConfiguration n) :
    (manuscriptOriginPoissonCoinTapeLaw hn P b eta threshold hroute
      intensity c).map
        (fun next : ManuscriptOriginConfiguration n => next.source) =
    (manuscriptPoissonTapeLaw intensity
      (normalizedHitAndRunPointLaw hn P b hroute.1 eta hroute.2.1
        hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2)).map
      (c.source.stepPoissonTape P c.state.nextLabel) := by
  rw [manuscriptOriginPoissonCoinTapeLaw_source_eq_spliced hn P b eta
    threshold hthreshold hroute intensity c]
  letI : IsProbabilityMeasure
      (normalizedHitAndRunPointLaw hn P b hroute.1 eta hroute.2.1
        hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2) :=
    (P.normalizedHitAndRun_latticePointLaw hn b hroute.1
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2).1
  rw [manuscriptSplicedSourceLaw_eq_poissonTape]

set_option maxHeartbeats 1000000 in
theorem manuscriptOriginPoissonCoinTapeLaw_fixedLevel_sourceCounts
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (c : ManuscriptOriginConfiguration n)
    (S : Finset (LatticePoint n))
    (hsupport : (normalizedHitAndRunPointLaw hn P b hroute.1 eta
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2)
        (S : Set (LatticePoint n))ᶜ = 0)
    (level : Nat) :
    (manuscriptOriginPoissonCoinTapeLaw hn P b eta threshold hroute
      intensity c).map
        (fun next : ManuscriptOriginConfiguration n =>
          next.source.pointCounts level S) =
    (Measure.pi (fun x : S => ProbabilityTheory.poissonMeasure
      (Real.toNNReal
        ((normalizedHitAndRunPointLaw hn P b hroute.1 eta
          hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2).real
            {(x : LatticePoint n)} *
          ((unitInterval.toNNReal (survivalProbability level) *
            intensity : NNReal) : Real))))).map
      (fun incoming : S → Nat => fun x : S =>
        (if x.1.toPoint ∈ P.carrier then 0 else
          c.source.pointCounts level S x) + incoming x) := by
  let pointLaw := normalizedHitAndRunPointLaw hn P b hroute.1 eta
    hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
  letI : IsProbabilityMeasure pointLaw :=
    (P.normalizedHitAndRun_latticePointLaw hn b hroute.1
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2).1
  have hsource := measurable_manuscriptOriginConfiguration_source (n := n)
  have hcounts := measurable_manuscriptOriginSourceState_pointCounts level S
  rw [show (fun next : ManuscriptOriginConfiguration n =>
      next.source.pointCounts level S) =
      (fun g : ManuscriptOriginSourceState n =>
        g.pointCounts level S) ∘ (fun next => next.source) from rfl]
  rw [← Measure.map_map hcounts hsource]
  rw [manuscriptOriginPoissonCoinTapeLaw_source_eq_spliced hn P b eta
    threshold hthreshold hroute intensity c]
  rw [Measure.map_map hcounts
    (measurable_manuscriptOriginSourceState_stepPoissonTape c.source P
      c.state.nextLabel)]
  exact c.source.stepPoissonTape_fixedLevel_law P c.state.nextLabel
    level (c.level + manuscriptRateExit (c.state.removeComponent P)
      intensity threshold) intensity pointLaw S hsupport c.bound

end Kr25Ssmxt
