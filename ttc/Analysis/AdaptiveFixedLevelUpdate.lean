import ttc.Analysis.AdaptiveSplicedSourceLaw
import ttc.Analysis.OriginMeasurable

/-! A new independent component source gives the fixed-level delete-and-add
law after an arbitrary adaptive ghost history. -/

namespace ttc

open Classical MeasureTheory

theorem OriginConfiguration.advance_source_eq_stepPoissonTape
    {n : Nat} (c : OriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool)
    (tape : Nat → LatticePoint n) :
    (c.advance P intensity threshold basePending preCoins future tape).source =
      c.source.stepPoissonTape P c.state.nextLabel
        (basePending,
          spliceCoins preCoins future
            (c.level + ttcReference.firstLoopExit (c.state.removeComponent P)
              intensity threshold), tape) := by
  rw [c.advance_source P intensity threshold basePending preCoins future
    tape]
  exact c.source.step_eq_stepPoissonTape _

theorem OriginConfiguration.advance_source_fixedLevel_pointCounts
    {n : Nat} (c : OriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool)
    (tape : Nat → LatticePoint n)
    (S : Finset (LatticePoint n)) (level : Nat) :
    ((c.advance P intensity threshold basePending preCoins future tape).source).pointCounts
        level S =
      fun x : S =>
        (if x.1.toPoint ∈ P.carrier then 0 else
          c.source.pointCounts level S x) +
        poissonTapePointCounts S c.state.nextLabel level
          (basePending,
            spliceCoins preCoins future
              (c.level + ttcReference.firstLoopExit (c.state.removeComponent P)
                intensity threshold), tape) x := by
  rw [c.advance_source_eq_stepPoissonTape P intensity threshold
    basePending preCoins future tape]
  exact c.source.stepPoissonTape_pointCounts P c.state.nextLabel level
    _ S c.bound

set_option maxHeartbeats 1000000 in
theorem origin_adaptive_source_fixedLevel_update
    {n : Nat} (μ : Measure (OriginConfiguration n))
    (P : PolytopeData n) (mean : NNReal)
    (pointLaw : Measure (LatticePoint n))
    [IsProbabilityMeasure pointLaw]
    (S : Finset (LatticePoint n))
    (hsupport : pointLaw (S : Set (LatticePoint n))ᶜ = 0)
    (firstLabel preRounds : OriginConfiguration n → Nat)
    (level : Nat) :
    μ.bind (fun c =>
      (splicedSourceLaw mean pointLaw (preRounds c)).map
        (fun source =>
          (c.source.stepPoissonTape P (firstLabel c) source).pointCounts
            level S)) =
    (μ.map (fun c => c.source.pointCounts level S)).bind
      (fun old =>
        (Measure.pi (fun x : S => ProbabilityTheory.poissonMeasure
          (Real.toNNReal
            (pointLaw.real {(x : LatticePoint n)} *
              ((unitInterval.toNNReal (survivalProbability level) *
                mean : NNReal) : Real))))).map
          (fun incoming : S → Nat => fun x : S =>
            (if x.1.toPoint ∈ P.carrier then 0 else old x) +
              incoming x)) := by
  let q : Measure (S → Nat) := Measure.pi
    (fun x : S => ProbabilityTheory.poissonMeasure
      (Real.toNNReal
        (pointLaw.real {(x : LatticePoint n)} *
          ((unitInterval.toNNReal (survivalProbability level) *
            mean : NNReal) : Real))))
  let oldCounts : OriginConfiguration n → (S → Nat) :=
    fun c => c.source.pointCounts level S
  let next : (S → Nat) → Measure (S → Nat) := fun old =>
    q.map (fun incoming : S → Nat => fun x : S =>
      (if x.1.toPoint ∈ P.carrier then 0 else old x) + incoming x)
  have hold : Measurable oldCounts :=
    (measurable_originSourceState_pointCounts level S).comp
      measurable_originConfiguration_source
  have hnext : Measurable next := measurable_of_countable _
  calc
    μ.bind (fun c =>
        (splicedSourceLaw mean pointLaw (preRounds c)).map
          (fun source =>
            (c.source.stepPoissonTape P (firstLabel c) source).pointCounts
              level S)) =
      μ.bind (fun c => next (oldCounts c)) := by
        apply Measure.bind_congr_right
        apply Filter.Eventually.of_forall
        intro c
        exact c.source.stepPoissonTape_fixedLevel_law P (firstLabel c)
          level (preRounds c) mean pointLaw S hsupport c.bound
    _ = (μ.map oldCounts).bind next := by
      exact (bind_mapped_measure μ oldCounts hold next hnext).symm

end ttc
