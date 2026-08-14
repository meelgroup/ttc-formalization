/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.Oracle
import Mathlib.Probability.ProductMeasure

/-!
# Turning input-indexed probability laws into one volume algorithm

A `VolumeAlgorithm` has one coin space and one coin law, fixed before `(K, eps, p)` is
known.  An operational probabilistic construction is more naturally stated with a different
sample type and probability law for every input.  `Measure.infinitePi` removes that mismatch:
take the dependent product over all inputs, and read the coordinate belonging to the current
input.  This works for an arbitrary (even uncountable) input type and for dependent coordinate
types.
-/

namespace Ttc

open MeasureTheory

/-- The dependent universal coin space, with one coordinate for every volume-oracle input. -/
abbrev InputCoinSpace (n : ℕ) (X : (Set (Space n) × ℝ × ℝ) → Type) :=
  ∀ a, X a

/-- The coordinate projection is measure preserving for the universal input product. -/
theorem measurePreserving_inputCoord
    {n : ℕ} {X : (Set (Space n) × ℝ × ℝ) → Type}
    [∀ a, MeasurableSpace (X a)]
    (nu : ∀ a, Measure (X a)) [∀ a, IsProbabilityMeasure (nu a)]
    (a : Set (Space n) × ℝ × ℝ) :
    MeasurePreserving (fun omega : InputCoinSpace n X => omega a)
      (Measure.infinitePi nu) (nu a) :=
  measurePreserving_eval_infinitePi nu a

/-- Package input-specific probability laws and estimators as one `VolumeAlgorithm`.

The estimator on `(K, eps, p)` reads only that coordinate of the universal product.  Thus
its failure probability is exactly the failure probability under the supplied local law,
not merely bounded by a union or coupling estimate. -/
noncomputable def VolumeAlgorithm.ofInputLaws
    (n : ℕ) (X : (Set (Space n) × ℝ × ℝ) → Type)
    [mX : ∀ a, MeasurableSpace (X a)]
    (nu : ∀ a, Measure (X a)) [hnu : ∀ a, IsProbabilityMeasure (nu a)]
    (localEst : ∀ a, X a → ℝ)
    (hlocalMeas : ∀ a, Measurable (localEst a))
    (hlocalCorrect : ∀ (K : Set (Space n)) (eps p : ℝ),
      0 < eps → 0 < p → p < 1 → Convex ℝ K → Metric.ball (0 : Space n) 1 ⊆ K →
      volume K ≠ ⊤ →
      1 - p ≤ (nu (K, eps, p)).real
        {omega | localEst (K, eps, p) omega ∈ relErr eps (volume K).toReal}) :
    VolumeAlgorithm n where
  Ω := InputCoinSpace n X
  mΩ := inferInstance
  μ := Measure.infinitePi nu
  isProb := by infer_instance
  est K eps p omega := localEst (K, eps, p) (omega (K, eps, p))
  est_meas K eps p := (hlocalMeas (K, eps, p)).comp (measurable_pi_apply (K, eps, p))
  correct K eps p heps hp hp1 hKc hball hfin := by
    let a : Set (Space n) × ℝ × ℝ := (K, eps, p)
    let S : Set (X a) :=
      {omega | localEst a omega ∈ relErr eps (volume K).toReal}
    have hS : MeasurableSet S := (hlocalMeas a) measurableSet_Icc
    have hmp := measurePreserving_inputCoord nu a
    have hEq : (Measure.infinitePi nu).real
        {omega : InputCoinSpace n X |
          localEst a (omega a) ∈ relErr eps (volume K).toReal} = (nu a).real S := by
      exact hmp.measureReal_preimage hS.nullMeasurableSet
    change 1 - p ≤ (Measure.infinitePi nu).real
      {omega : InputCoinSpace n X |
        localEst a (omega a) ∈ relErr eps (volume K).toReal}
    rw [hEq]
    exact hlocalCorrect K eps p heps hp hp1 hKc hball hfin

#print axioms measurePreserving_inputCoord
#print axioms VolumeAlgorithm.ofInputLaws

end Ttc
