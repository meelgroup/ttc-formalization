import Kr25Ssmxt.Analysis.ManuscriptAdaptiveSplicedSourceLaw
import Kr25Ssmxt.Analysis.ManuscriptOriginMeasurable

/-! A new independent component source gives the fixed-level delete-and-add
law after an arbitrary adaptive ghost history. -/

namespace Kr25Ssmxt

open Classical MeasureTheory

theorem ManuscriptOriginConfiguration.advance_source_eq_stepPoissonTape
    {n : Nat} (c : ManuscriptOriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool)
    (tape : Nat → LatticePoint n) :
    (c.advance P intensity threshold basePending preCoins future tape).source =
      c.source.stepPoissonTape P c.state.nextLabel
        (basePending,
          spliceCoins preCoins future
            (c.level + ttcPseudocode.firstLoopExit (c.state.removeComponent P)
              intensity threshold), tape) := by
  rw [c.advance_source P intensity threshold basePending preCoins future
    tape]
  exact c.source.step_eq_stepPoissonTape _

theorem ManuscriptOriginConfiguration.advance_source_fixedLevel_pointCounts
    {n : Nat} (c : ManuscriptOriginConfiguration n)
    (P : PolytopeData n) (intensity : NNReal) (threshold : Real)
    (basePending : Nat) (preCoins future : Nat × Nat → Bool)
    (tape : Nat → LatticePoint n)
    (S : Finset (LatticePoint n)) (level : Nat) :
    ((c.advance P intensity threshold basePending preCoins future tape).source).pointCounts
        level S =
      fun x : S =>
        (if x.1.toPoint ∈ P.carrier then 0 else
          c.source.pointCounts level S x) +
        manuscriptPoissonTapePointCounts S c.state.nextLabel level
          (basePending,
            spliceCoins preCoins future
              (c.level + ttcPseudocode.firstLoopExit (c.state.removeComponent P)
                intensity threshold), tape) x := by
  rw [c.advance_source_eq_stepPoissonTape P intensity threshold
    basePending preCoins future tape]
  exact c.source.stepPoissonTape_pointCounts P c.state.nextLabel level
    _ S c.bound

set_option maxHeartbeats 1000000 in
theorem manuscriptOrigin_adaptive_source_fixedLevel_update
    {n : Nat} (μ : Measure (ManuscriptOriginConfiguration n))
    (P : PolytopeData n) (mean : NNReal)
    (pointLaw : Measure (LatticePoint n))
    [IsProbabilityMeasure pointLaw]
    (S : Finset (LatticePoint n))
    (hsupport : pointLaw (S : Set (LatticePoint n))ᶜ = 0)
    (firstLabel preRounds : ManuscriptOriginConfiguration n → Nat)
    (level : Nat) :
    μ.bind (fun c =>
      (manuscriptSplicedSourceLaw mean pointLaw (preRounds c)).map
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
  let oldCounts : ManuscriptOriginConfiguration n → (S → Nat) :=
    fun c => c.source.pointCounts level S
  let next : (S → Nat) → Measure (S → Nat) := fun old =>
    q.map (fun incoming : S → Nat => fun x : S =>
      (if x.1.toPoint ∈ P.carrier then 0 else old x) + incoming x)
  have hold : Measurable oldCounts :=
    (measurable_manuscriptOriginSourceState_pointCounts level S).comp
      measurable_manuscriptOriginConfiguration_source
  have hnext : Measurable next := measurable_of_countable _
  calc
    μ.bind (fun c =>
        (manuscriptSplicedSourceLaw mean pointLaw (preRounds c)).map
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

end Kr25Ssmxt
