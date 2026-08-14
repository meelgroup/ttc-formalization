import Ttc.Exec.CVIndependentStreamGeneralizedCertificate
import Ttc.Exec.CVSourcePolynomialCutoffCapstone

/-!
# Source-sharp certificate for independent costed CV streams

The corrected CV estimator is evaluated on `k` independent complete scalar paths.  This
file connects that operational representation directly to the source-shaped global
cutoff.  In particular, there is no per-phase Markov cutoff and hence no division by
`correctedNu`: the expected one-run cost is exactly bounded by

`k * sum_i phaseBound i`.

The remaining source-rate obligation is the displayed deterministic comparison of that
sum with `sourceOneRunQueryBudget`.
-/

namespace Ttc.CVSourceSharpIndependentCertificate

open MeasureTheory ProbabilityTheory Set
open Ttc.CVIndependentStreamDependence
open Ttc.CVIndependentStreamGeneralizedCertificate
open Ttc.CVSourcePolynomialCutoffCapstone
open Ttc.GenericCostedPhaseCertificate
open scoped ENNReal Classical BigOperators

variable {E : Type} [MeasurableSpace E]

/-- A fixed-input source certificate for `k` independent costed scalar executions.

All accuracy and cost statements concern the same product law.  The runtime premise is
an expected-cost bound, so the single global cutoff in
`source_polynomial_cutoff_capstone` is the only timeout used. -/
theorem sourceOneRunCertificate_of_independentCostedStreams
    {k m : Nat}
    (P : Nat → Kernel E E) [∀ i, IsMarkovKernel (P i)]
    (Q : Nat → Kernel E (ENNReal × E)) [∀ i, IsMarkovKernel (Q i)]
    (mu0 : Measure E) [IsProbabilityMeasure mu0]
    (phaseBound : Nat → ENNReal)
    (hforget : ∀ i x, Measure.map Prod.snd (Q i x) = P i x)
    (hphase : ∀ i, i < m →
      (∫⁻ x, Ttc.SequentialCost.stepMean Q i x ∂stateMarginal Q mu0 i) ≤
        phaseBound i)
    (est : (Fin k → Nat → E) → Real) (hest : Measurable est)
    {runtimeConstant : Real} {n : Nat} {R eps lo hi : Real}
    (hsum : (k : ENNReal) * ∑ i ∈ Finset.range m, phaseBound i ≤
      sourceOneRunQueryBudget runtimeConstant n R eps)
    (haccuracy : 4 / 5 ≤
      (independentPathLaw k P mu0).real
        {omega | est omega ∈ Icc lo hi}) :
    SourceOneRunCertificate
      (independentCostedLaw k Q mu0)
      (independentQueryCost m)
      (independentValue est)
      runtimeConstant n R eps lo hi := by
  refine
    { probability := inferInstance
      cost_measurable := measurable_independentQueryCost m
      value_measurable := measurable_independentValue hest
      expected_queries := ?_
      accuracy := ?_ }
  · exact (lintegral_independentQueryCost_le_phaseBounds
      k m Q mu0 phaseBound hphase).trans hsum
  · let G : Set (Fin k → Nat → E) := {omega | est omega ∈ Icc lo hi}
    have hG : MeasurableSet G := measurableSet_Icc.preimage hest
    have hmap := map_independentStatePaths_independentCostedLaw
      k P Q mu0 hforget
    have heq : (independentCostedLaw k Q mu0).real
        (independentStatePaths ⁻¹' G) =
        (independentPathLaw k P mu0).real G := by
      change ((independentCostedLaw k Q mu0)
        (independentStatePaths ⁻¹' G)).toReal = _
      rw [← Measure.map_apply measurable_independentStatePaths hG, hmap]
      rfl
    change 4 / 5 ≤ (independentCostedLaw k Q mu0).real
      (independentStatePaths ⁻¹' G)
    rw [heq]
    exact haccuracy

variable {n : Nat}

/-- Input-indexed source certificates for the independent-stream operational law. -/
theorem sourcePublicOneRunCertificates_of_independentCostedStreams
    (runtimeConstant : Real) (radialR : Set (Ttc.Space n) → Real)
    (k m : Ttc.CVAdaptive.VolumeInput n → Nat)
    (P : ∀ a, Nat → Kernel E E) [∀ a i, IsMarkovKernel (P a i)]
    (Q : ∀ a, Nat → Kernel E (ENNReal × E))
    [∀ a i, IsMarkovKernel (Q a i)]
    (mu0 : ∀ a, Measure E) [∀ a, IsProbabilityMeasure (mu0 a)]
    (phaseBound : ∀ a, Nat → ENNReal)
    (est : ∀ a, (Fin (k a) → Nat → E) → Real)
    (hforget : ∀ a i x, Measure.map Prod.snd (Q a i x) = P a i x)
    (hphase : ∀ a i, i < m a →
      (∫⁻ x, Ttc.SequentialCost.stepMean (Q a) i x
        ∂stateMarginal (Q a) (mu0 a) i) ≤ phaseBound a i)
    (hsum : ∀ a,
      (k a : ENNReal) * ∑ i ∈ Finset.range (m a), phaseBound a i ≤
        sourceOneRunQueryBudget runtimeConstant n (radialR a.1) a.2.1)
    (hest : ∀ a, Measurable (est a))
    (haccuracy : ∀ (K : Set (Ttc.Space n)) (eps p : Real),
      0 < eps → 0 < p → p < 1 → Convex Real K →
      Metric.ball (0 : Ttc.Space n) 1 ⊆ K → volume K ≠ ⊤ →
      4 / 5 ≤
        (independentPathLaw (k (K, eps, p)) (P (K, eps, p))
          (mu0 (K, eps, p))).real
          {omega | est (K, eps, p) omega ∈
            Icc ((1 - eps) * (volume K).toReal)
              ((1 + eps) * (volume K).toReal)}) :
    SourcePublicOneRunCertificates n runtimeConstant radialR
      (fun a ↦ IndependentCostedPath (k a) E)
      (fun a ↦ independentCostedLaw (k a) (Q a) (mu0 a))
      (fun a ↦ independentQueryCost (m a))
      (fun a ↦ independentValue (est a)) := by
  refine
    { probability := fun _ ↦ inferInstance
      cost_measurable := fun a ↦ measurable_independentQueryCost (m a)
      value_measurable := fun a ↦ measurable_independentValue (hest a)
      expected_queries := fun a ↦
        (lintegral_independentQueryCost_le_phaseBounds
          (k a) (m a) (Q a) (mu0 a) (phaseBound a) (hphase a)).trans (hsum a)
      accuracy := ?_ }
  intro K eps p heps hp hp1 hKc hball hfin
  let a : Ttc.CVAdaptive.VolumeInput n := (K, eps, p)
  let cert := sourceOneRunCertificate_of_independentCostedStreams
    (P a) (Q a) (mu0 a) (phaseBound a) (hforget a) (hphase a)
    (est a) (hest a) (hsum a)
    (haccuracy K eps p heps hp hp1 hKc hball hfin)
  exact cert.accuracy

/-- The source-shaped public expected-query volume oracle obtained from independent
costed scalar paths and one global cutoff. -/
noncomputable def expectedQueryVolumeAlgorithmOfIndependentCostedStreams
    (runtimeConstant : Real) (radialR : Set (Ttc.Space n) → Real)
    (k m : Ttc.CVAdaptive.VolumeInput n → Nat)
    (P : ∀ a, Nat → Kernel E E) [∀ a i, IsMarkovKernel (P a i)]
    (Q : ∀ a, Nat → Kernel E (ENNReal × E))
    [∀ a i, IsMarkovKernel (Q a i)]
    (mu0 : ∀ a, Measure E) [∀ a, IsProbabilityMeasure (mu0 a)]
    (phaseBound : ∀ a, Nat → ENNReal)
    (est : ∀ a, (Fin (k a) → Nat → E) → Real)
    (hforget : ∀ a i x, Measure.map Prod.snd (Q a i x) = P a i x)
    (hphase : ∀ a i, i < m a →
      (∫⁻ x, Ttc.SequentialCost.stepMean (Q a) i x
        ∂stateMarginal (Q a) (mu0 a) i) ≤ phaseBound a i)
    (hsum : ∀ a,
      (k a : ENNReal) * ∑ i ∈ Finset.range (m a), phaseBound a i ≤
        sourceOneRunQueryBudget runtimeConstant n (radialR a.1) a.2.1)
    (hest : ∀ a, Measurable (est a))
    (haccuracy : ∀ (K : Set (Ttc.Space n)) (eps p : Real),
      0 < eps → 0 < p → p < 1 → Convex Real K →
      Metric.ball (0 : Ttc.Space n) 1 ⊆ K → volume K ≠ ⊤ →
      4 / 5 ≤
        (independentPathLaw (k (K, eps, p)) (P (K, eps, p))
          (mu0 (K, eps, p))).real
          {omega | est (K, eps, p) omega ∈
            Icc ((1 - eps) * (volume K).toReal)
              ((1 + eps) * (volume K).toReal)}) :
    Ttc.ExpectedQueryVolumeAlgorithm n :=
  expectedQueryVolumeAlgorithmOfSourceOneRunCertificates n runtimeConstant radialR
    (fun a ↦ IndependentCostedPath (k a) E)
    (fun a ↦ independentCostedLaw (k a) (Q a) (mu0 a))
    (fun a ↦ independentQueryCost (m a))
    (fun a ↦ independentValue (est a))
    (sourcePublicOneRunCertificates_of_independentCostedStreams
      runtimeConstant radialR k m P Q mu0 phaseBound est hforget hphase hsum hest
      haccuracy)

#print axioms sourceOneRunCertificate_of_independentCostedStreams
#print axioms sourcePublicOneRunCertificates_of_independentCostedStreams
#print axioms expectedQueryVolumeAlgorithmOfIndependentCostedStreams

end Ttc.CVSourceSharpIndependentCertificate
