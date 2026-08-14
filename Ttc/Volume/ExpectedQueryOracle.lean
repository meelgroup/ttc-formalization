/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.InputLawAlgorithm

/-!
# Volume algorithms with an honest expected membership-query cost

Unlike the older deterministic `CVTheorem11Implementation.queryCost` field, the cost here
is a measurable random variable on the *same coin space as the estimator*.  Its expectation
therefore refers to the actual execution law.  The input-law constructor is designed for
the traced `(query count, output state)` measures in `Ttc.Exec`.
-/

namespace Ttc

open MeasureTheory
open scoped ENNReal

/-- A semantic volume oracle together with a measurable actual-query random variable and
an input-dependent expected-query certificate. -/
structure ExpectedQueryVolumeAlgorithm (n : Nat) extends VolumeAlgorithm n where
  queryCost : Set (Space n) → Real → Real → Ω → ENNReal
  queryCost_meas : ∀ K eps p, Measurable (queryCost K eps p)
  expectedBound : Set (Space n) → Real → Real → ENNReal
  expectedQueryCost_le : ∀ K eps p,
    (∫⁻ omega, queryCost K eps p omega ∂μ) ≤ expectedBound K eps p

namespace ExpectedQueryVolumeAlgorithm

variable {n : Nat}

/-- Accuracy is inherited verbatim from the underlying volume algorithm. -/
theorem accuracy (V : ExpectedQueryVolumeAlgorithm n)
    (K : Set (Space n)) (eps p : Real) (heps : 0 < eps) (hp : 0 < p)
    (hp1 : p < 1) (hKc : Convex Real K) (hball : Metric.ball (0 : Space n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) :
    1 - p ≤ (V.μ {omega | V.est K eps p omega ∈
      relErr eps (volume K).toReal}).toReal :=
  V.toVolumeAlgorithm.correct K eps p heps hp hp1 hKc hball hfin

/-- Package input-indexed *costed* execution laws into one oracle.  The universal product
stores one operational trace for every possible input and the estimator and query counter
read the same coordinate. -/
noncomputable def ofInputCostedLaws
    (n : Nat) (X : (Set (Space n) × Real × Real) → Type)
    [mX : ∀ a, MeasurableSpace (X a)]
    (nu : ∀ a, Measure (X a)) [hnu : ∀ a, IsProbabilityMeasure (nu a)]
    (localEst : ∀ a, X a → Real) (localCost : ∀ a, X a → ENNReal)
    (hlocalEst : ∀ a, Measurable (localEst a))
    (hlocalCost : ∀ a, Measurable (localCost a))
    (bound : (Set (Space n) × Real × Real) → ENNReal)
    (hbound : ∀ a, (∫⁻ x, localCost a x ∂(nu a)) ≤ bound a)
    (hcorrect : ∀ (K : Set (Space n)) (eps p : Real),
      0 < eps → 0 < p → p < 1 → Convex Real K → Metric.ball (0 : Space n) 1 ⊆ K →
      volume K ≠ ⊤ →
      1 - p ≤ (nu (K, eps, p)).real
        {omega | localEst (K, eps, p) omega ∈ relErr eps (volume K).toReal}) :
    ExpectedQueryVolumeAlgorithm n where
  toVolumeAlgorithm := VolumeAlgorithm.ofInputLaws n X nu localEst hlocalEst hcorrect
  queryCost K eps p omega := localCost (K, eps, p) (omega (K, eps, p))
  queryCost_meas K eps p :=
    (hlocalCost (K, eps, p)).comp (measurable_pi_apply (K, eps, p))
  expectedBound K eps p := bound (K, eps, p)
  expectedQueryCost_le K eps p := by
    let a : Set (Space n) × Real × Real := (K, eps, p)
    have hmp := measurePreserving_inputCoord nu a
    change (∫⁻ omega : InputCoinSpace n X,
      localCost a (omega a) ∂(Measure.infinitePi nu)) ≤ bound a
    rw [show (∫⁻ omega : InputCoinSpace n X,
        localCost a (omega a) ∂(Measure.infinitePi nu)) =
        ∫⁻ x, localCost a x ∂(nu a) by
      exact hmp.lintegral_comp (hlocalCost a)]
    exact hbound a

/-- The expected cost statement is genuinely about the same coins read by `est`. -/
theorem expectedQueryBound_holds (V : ExpectedQueryVolumeAlgorithm n)
    (K : Set (Space n)) (eps p : Real) :
    (∫⁻ omega, V.queryCost K eps p omega ∂V.μ) ≤ V.expectedBound K eps p :=
  V.expectedQueryCost_le K eps p

end ExpectedQueryVolumeAlgorithm

#print axioms ExpectedQueryVolumeAlgorithm.accuracy
#print axioms ExpectedQueryVolumeAlgorithm.ofInputCostedLaws
#print axioms ExpectedQueryVolumeAlgorithm.expectedQueryBound_holds

end Ttc
