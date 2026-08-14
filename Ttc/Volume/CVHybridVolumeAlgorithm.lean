/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVGuardedVolumeAlgorithm
import Ttc.Volume.MonteCarlo

/-!
# Unconditional hybrid volume algorithm

For inputs satisfying the radius-four tail guard this uses the concrete adaptive CV law.
For all remaining inputs it uses the existing hit-and-miss Monte Carlo oracle.  The fallback
is correct but no polynomial runtime claim is made for it.
-/

namespace Ttc.CVAdaptive

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.GaussianCooling

variable {n : Nat}

abbrev HybridRunCoin (n : Nat) (a : VolumeInput n) :=
  GuardedRunCoin n a ⊕ (Nat -> Space n)

noncomputable def hybridRunLaw (a : VolumeInput n) : Measure (HybridRunCoin n a) := by
  classical
  exact if ConcreteRunwiseTailGuard a then
    Measure.map Sum.inl (guardedRunLaw a)
  else Measure.map Sum.inr (Ttc.MonteCarlo.coins n)

instance isProbabilityMeasure_hybridRunLaw (a : VolumeInput n) :
    IsProbabilityMeasure (hybridRunLaw a) := by
  classical
  unfold hybridRunLaw
  split_ifs
  · exact Measure.isProbabilityMeasure_map measurable_inl.aemeasurable
  · exact Measure.isProbabilityMeasure_map measurable_inr.aemeasurable

noncomputable def hybridEstimator (a : VolumeInput n) : HybridRunCoin n a -> Real :=
  Sum.elim (guardedEstimator a) (Ttc.MonteCarlo.est a.1 a.2.1 a.2.2)

theorem measurable_hybridEstimator (a : VolumeInput n) : Measurable (hybridEstimator a) := by
  exact (measurable_guardedEstimator a).sumElim
    (Ttc.MonteCarlo.measurable_est a.1 a.2.1 a.2.2)

theorem hybridRunLaw_eq_cv (a : VolumeInput n) (hguard : ConcreteRunwiseTailGuard a) :
    hybridRunLaw a = Measure.map Sum.inl (guardedRunLaw a) := by
  classical
  simp [hybridRunLaw, hguard]

theorem hybridRunLaw_eq_monteCarlo (a : VolumeInput n)
    (hguard : ¬ ConcreteRunwiseTailGuard a) :
    hybridRunLaw a = Measure.map Sum.inr (Ttc.MonteCarlo.coins n) := by
  classical
  simp [hybridRunLaw, hguard]

@[simp] theorem hybridEstimator_inl (a : VolumeInput n) (omega : GuardedRunCoin n a) :
    hybridEstimator a (Sum.inl omega) = guardedEstimator a omega := rfl

@[simp] theorem hybridEstimator_inr (a : VolumeInput n) (omega : Nat -> Space n) :
    hybridEstimator a (Sum.inr omega) = Ttc.MonteCarlo.est a.1 a.2.1 a.2.2 omega := rfl

/-- Local CV correctness under the explicit tail guard. -/
theorem guardedRunLaw_correct_of_tail
    (hn : 21 <= n) {K : Set (Space n)} {eps p : Real}
    (heps : 0 < eps) (hp : 0 < p) (hp1 : p < 1)
    (hKc : Convex Real K) (hKcl : IsClosed K) (hKb : Bornology.IsBounded K)
    (hvol : 0 < volume K) (hclosedBall : closedBall (0 : Space n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (hguard : ConcreteRunwiseTailGuard (n := n) (K, eps, p)) :
    1 - p <= (guardedRunLaw (K, eps, p)).real
      {omega | guardedEstimator (K, eps, p) omega ∈ Ttc.relErr eps (volume K).toReal} := by
  let a : VolumeInput n := (K, eps, p)
  have hrawProb : IsProbabilityMeasure (guardedRawRunLaw a) :=
    isProbabilityMeasure_guardedRawRunLaw hn a heps hKc hKcl hclosedBall hfin
  have hlaw : guardedRunLaw a = guardedRawRunLaw a := guardedRunLaw_eq_raw a hrawProb
  have hest : guardedEstimator a = guardedRawEstimator a :=
    guardedEstimator_eq_raw a hKcl.measurableSet
  have hgeom := closure_concrete_geometry (n := n) (by omega) hKc
    (ball_subset_closedBall.trans hclosedBall) hfin
  have hKR : K ⊆ closedBall 0 (Ttc.CV.cvRadius K * Real.sqrt n) := by
    simpa [hKcl.closure_eq] using hgeom.2.2.2.2.2.2.2
  have hacc : 0 < guardedAccuracy a := by
    unfold guardedAccuracy
    positivity
  have hacc1 : guardedAccuracy a <= 1 := min_le_right _ _
  have hmain := concrete_adaptive_runwise_volume_accuracy hn hKc hKcl hKb hvol
    hclosedBall hfin (Ttc.CV.cvRadius_pos K) hacc hacc1 hp hp1 hKR hguard
  have hmain' : 1 - p <= (guardedRawRunLaw a).real
      {omega | guardedRawEstimator a omega ∈
        Ttc.relErr (guardedAccuracy a) (volume K).toReal} := by
    convert hmain using 1 <;>
      simp only [a, guardedAccuracy, guardedEta, guardedC, guardedS0, guardedJ,
        guardedM, guardedK, guardedR, guardedMix, guardedSteps, guardedPhaseLaw,
        guardedRawRunLaw, guardedScore, guardedRawEstimator] <;> rfl
  letI : IsProbabilityMeasure (guardedRawRunLaw a) := hrawProb
  have hmono : (guardedRawRunLaw a).real
      {omega | guardedRawEstimator a omega ∈
        Ttc.relErr (guardedAccuracy a) (volume K).toReal} <=
      (guardedRawRunLaw a).real
      {omega | guardedRawEstimator a omega ∈ Ttc.relErr eps (volume K).toReal} := by
    apply measureReal_mono
    · intro omega homega
      exact Ttc.CV.relErr_mono (min_le_left _ _) (volume K).toReal_nonneg homega
    · exact measure_ne_top _ _
  rw [hlaw, hest]
  exact hmain'.trans hmono

/-- Local correctness of the hybrid law on every admissible closed input. -/
theorem hybridRunLaw_correct
    (hn : 21 <= n) {K : Set (Space n)} {eps p : Real}
    (heps : 0 < eps) (hp : 0 < p) (hp1 : p < 1)
    (hKc : Convex Real K) (hKcl : IsClosed K) (hKb : Bornology.IsBounded K)
    (hvol : 0 < volume K) (hclosedBall : closedBall (0 : Space n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) :
    1 - p <= (hybridRunLaw (K, eps, p)).real
      {omega | hybridEstimator (K, eps, p) omega ∈ Ttc.relErr eps (volume K).toReal} := by
  let a : VolumeInput n := (K, eps, p)
  have hS : MeasurableSet
      {omega : HybridRunCoin n a |
        hybridEstimator a omega ∈ Ttc.relErr eps (volume K).toReal} :=
    (measurable_hybridEstimator a) measurableSet_Icc
  classical
  by_cases hguard : ConcreteRunwiseTailGuard a
  · have hcv := guardedRunLaw_correct_of_tail hn heps hp hp1 hKc hKcl hKb hvol
      hclosedBall hfin hguard
    rw [hybridRunLaw_eq_cv a hguard]
    rw [map_measureReal_apply measurable_inl hS]
    convert hcv using 1 <;> rfl
  · have hmc := Ttc.MonteCarlo.correct K eps p heps hp hp1 hKc
      (ball_subset_closedBall.trans hclosedBall) hfin
    rw [hybridRunLaw_eq_monteCarlo a hguard]
    rw [map_measureReal_apply measurable_inr hS]
    convert hmc using 1 <;> rfl

/-! ## Unconditional public algorithm -/

/-- Unconditional correctness: CV on the good tail regime, Monte Carlo otherwise. -/
noncomputable def hybridConcreteVolumeAlgorithm (n : Nat) (hn : 21 <= n) :
    Ttc.VolumeAlgorithm n :=
  Ttc.VolumeAlgorithm.ofClosedInputLaws n (by omega)
    (HybridRunCoin n) hybridRunLaw hybridEstimator measurable_hybridEstimator
    (fun K eps p heps hp hp1 hKc hKcl hKb hvol hclosedBall hfin =>
      hybridRunLaw_correct hn heps hp hp1 hKc hKcl hKb hvol hclosedBall hfin)

/-- On guarded admissible inputs the hybrid law and estimator are exactly the CV branch. -/
theorem hybrid_reduces_to_cv_on_guard
    (hn : 21 <= n) (K : Set (Space n)) (eps p : Real)
    (heps : 0 < eps) (hKc : Convex Real K) (hKcl : IsClosed K)
    (hclosedBall : closedBall (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hguard : ConcreteRunwiseTailGuard (n := n) (K, eps, p)) :
    hybridRunLaw (K, eps, p) =
        Measure.map Sum.inl (guardedRawRunLaw (K, eps, p)) ∧
      (∀ omega, hybridEstimator (K, eps, p) (Sum.inl omega) =
        guardedRawEstimator (K, eps, p) omega) := by
  let a : VolumeInput n := (K, eps, p)
  have hprob := isProbabilityMeasure_guardedRawRunLaw hn a heps hKc hKcl hclosedBall hfin
  constructor
  · rw [hybridRunLaw_eq_cv a hguard, guardedRunLaw_eq_raw a hprob]
  · intro omega
    rw [hybridEstimator_inl, guardedEstimator_eq_raw a hKcl.measurableSet]

/-! ### Axiom audit -/

#print axioms hybridRunLaw_correct
#print axioms hybridConcreteVolumeAlgorithm
#print axioms hybrid_reduces_to_cv_on_guard

end Ttc.CVAdaptive
