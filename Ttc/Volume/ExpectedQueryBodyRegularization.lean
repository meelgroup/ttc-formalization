/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.ExpectedQueryOracle
import Ttc.Volume.CVBodyRegularization

/-!
# Closed-body regularization for expected-query volume algorithms

This is the costed analogue of `VolumeAlgorithm.ofClosedInputLaws`.  Both the estimator and
the actual query-count random variable read the same input coordinate for `closure K`.
Consequently the expected-cost theorem is about precisely the execution law used for
accuracy, rather than an unrelated accounting function.

As with the uncosted closure adapter, this is a measure-theoretic correctness construction.
It does not turn a membership oracle for an arbitrary nonclosed set into an executable
membership oracle for its closure.  Operational callers should supply a closed body (as the
TTC rounding construction is intended to do), or separately prove boundary avoidance.
-/

namespace Ttc.ExpectedQueryVolumeAlgorithm

open MeasureTheory Metric Set
open scoped ENNReal

/-- Package input-indexed costed laws whose correctness theorem is available for closed,
bounded convex bodies.  On a public input `K`, the common estimator/cost coordinate is the
one indexed by `closure K`; the expected bound is evaluated at that same coordinate. -/
noncomputable def ofClosedInputCostedLaws
    (n : Nat) (hn : 1 ≤ n)
    (X : (Set (Space n) × Real × Real) → Type)
    [mX : ∀ a, MeasurableSpace (X a)]
    (nu : ∀ a, Measure (X a)) [hnu : ∀ a, IsProbabilityMeasure (nu a)]
    (localEst : ∀ a, X a → Real) (localCost : ∀ a, X a → ENNReal)
    (hlocalEst : ∀ a, Measurable (localEst a))
    (hlocalCost : ∀ a, Measurable (localCost a))
    (bound : (Set (Space n) × Real × Real) → ENNReal)
    (hbound : ∀ a, (∫⁻ x, localCost a x ∂(nu a)) ≤ bound a)
    (hcorrect : ∀ (K : Set (Space n)) (eps p : Real),
      0 < eps → 0 < p → p < 1 →
      Convex Real K → IsClosed K → Bornology.IsBounded K → 0 < volume K →
      closedBall (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      1 - p ≤ (nu (K, eps, p)).real
        {omega | localEst (K, eps, p) omega ∈ relErr eps (volume K).toReal}) :
    ExpectedQueryVolumeAlgorithm n where
  toVolumeAlgorithm := VolumeAlgorithm.ofClosedInputLaws n hn X nu localEst hlocalEst hcorrect
  queryCost K eps p omega :=
    localCost (closure K, eps, p) (omega (closure K, eps, p))
  queryCost_meas K eps p :=
    (hlocalCost (closure K, eps, p)).comp
      (measurable_pi_apply (closure K, eps, p))
  expectedBound K eps p := bound (closure K, eps, p)
  expectedQueryCost_le K eps p := by
    let a : Set (Space n) × Real × Real := (closure K, eps, p)
    have hmp := measurePreserving_inputCoord nu a
    change (∫⁻ omega : InputCoinSpace n X,
      localCost a (omega a) ∂(Measure.infinitePi nu)) ≤ bound a
    rw [show (∫⁻ omega : InputCoinSpace n X,
        localCost a (omega a) ∂(Measure.infinitePi nu)) =
        ∫⁻ x, localCost a x ∂(nu a) by
      exact hmp.lintegral_comp (hlocalCost a)]
    exact hbound a

/-- The closure-cost bound is inherited from the exact input-indexed execution law. -/
theorem expectedQueryBound_ofClosedInputCostedLaws
    (n : Nat) (hn : 1 ≤ n)
    (X : (Set (Space n) × Real × Real) → Type)
    [mX : ∀ a, MeasurableSpace (X a)]
    (nu : ∀ a, Measure (X a)) [hnu : ∀ a, IsProbabilityMeasure (nu a)]
    (localEst : ∀ a, X a → Real) (localCost : ∀ a, X a → ENNReal)
    (hlocalEst : ∀ a, Measurable (localEst a))
    (hlocalCost : ∀ a, Measurable (localCost a))
    (bound : (Set (Space n) × Real × Real) → ENNReal)
    (hbound : ∀ a, (∫⁻ x, localCost a x ∂(nu a)) ≤ bound a)
    (hcorrect : ∀ (K : Set (Space n)) (eps p : Real),
      0 < eps → 0 < p → p < 1 →
      Convex Real K → IsClosed K → Bornology.IsBounded K → 0 < volume K →
      closedBall (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      1 - p ≤ (nu (K, eps, p)).real
        {omega | localEst (K, eps, p) omega ∈ relErr eps (volume K).toReal})
    (K : Set (Space n)) (eps p : Real) :
    (∫⁻ omega,
        (ofClosedInputCostedLaws n hn X nu localEst localCost hlocalEst hlocalCost
          bound hbound hcorrect).queryCost K eps p omega
      ∂(ofClosedInputCostedLaws n hn X nu localEst localCost hlocalEst hlocalCost
          bound hbound hcorrect).μ) ≤
      bound (closure K, eps, p) :=
  (ofClosedInputCostedLaws n hn X nu localEst localCost hlocalEst hlocalCost
    bound hbound hcorrect).expectedQueryCost_le K eps p

end Ttc.ExpectedQueryVolumeAlgorithm

#print axioms Ttc.ExpectedQueryVolumeAlgorithm.ofClosedInputCostedLaws
#print axioms Ttc.ExpectedQueryVolumeAlgorithm.expectedQueryBound_ofClosedInputCostedLaws
