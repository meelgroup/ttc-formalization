import Ttc.Exec.CVIndependentStreamAccuracy
import Ttc.Exec.GenericCostedPhaseCertificate
import Ttc.Exec.CVGeneralPolynomialCutoffCapstone

/-!
# Public one-run certificates from independent costed scalar streams

The operational CV estimator uses `k` independent *complete* scalar executions.  This
file equips that representation with honest query accounting: the one-run law is the
finite product of scalar costed execution laws and its cost is the sum of their recorded
costs.  Forgetting the costs is exactly `independentPathLaw`, the law consumed by
`CVIndependentStreamAccuracy`.

No runtime estimate is manufactured here.  The constructor leaves the actual scalar
per-phase expected-query estimate as a premise, then charges it exactly `k` times.
-/

namespace Ttc.CVIndependentStreamGeneralizedCertificate

open MeasureTheory ProbabilityTheory Set
open Ttc.GenericCostedPhaseCertificate
open Ttc.CVIndependentStreamDependence
open Ttc.CVGeneralPolynomialCutoffCapstone
open scoped ENNReal Classical BigOperators

variable {E : Type} [MeasurableSpace E]

abbrev ScalarCostedPath (E : Type*) := Nat → ENNReal × E
abbrev IndependentCostedPath (k : Nat) (E : Type*) := Fin k → ScalarCostedPath E

/-- Product of `k` independently restarted complete scalar costed executions. -/
noncomputable def independentCostedLaw
    (k : Nat) (Q : Nat → Kernel E (ENNReal × E)) [∀ i, IsMarkovKernel (Q i)]
    (mu0 : Measure E) : Measure (IndependentCostedPath k E) :=
  Measure.pi (fun _ : Fin k ↦ oneRunLaw Q mu0)

instance independentCostedLaw.isProbabilityMeasure
    (k : Nat) (Q : Nat → Kernel E (ENNReal × E)) [∀ i, IsMarkovKernel (Q i)]
    (mu0 : Measure E) [IsProbabilityMeasure mu0] :
    IsProbabilityMeasure (independentCostedLaw k Q mu0) := by
  letI : ∀ _l : Fin k, IsProbabilityMeasure (oneRunLaw Q mu0) := fun _l ↦ by
    unfold oneRunLaw
    infer_instance
  unfold independentCostedLaw
  infer_instance

/-- Total membership-query count across all independent streams. -/
noncomputable def independentQueryCost {k : Nat} (m : Nat)
    (omega : IndependentCostedPath k E) :
    ENNReal :=
  ∑ l : Fin k, queryCost m (omega l)

/-- Erase the cost coordinate from every scalar stream. -/
def independentStatePaths {k : Nat}
    (omega : IndependentCostedPath k E) : Fin k → Nat → E :=
  fun l ↦ statePath (omega l)

/-- Evaluate an estimator on the cost-erased independent paths. -/
def independentValue {k : Nat} (est : (Fin k → Nat → E) → Real)
    (omega : IndependentCostedPath k E) : Real :=
  est (independentStatePaths omega)

theorem measurable_independentQueryCost {k : Nat} (m : Nat) :
    Measurable (independentQueryCost (k := k) (E := E) m) := by
  unfold independentQueryCost
  apply Finset.measurable_fun_sum
  intro l _hl
  exact (measurable_queryCost m).comp (measurable_pi_apply l)

theorem measurable_independentStatePaths {k : Nat} :
    Measurable (independentStatePaths : IndependentCostedPath k E → Fin k → Nat → E) := by
  unfold independentStatePaths
  apply measurable_pi_lambda
  intro l
  exact (Ttc.SequentialCostedPathLumping.measurable_pathMap measurable_snd).comp
    (measurable_pi_apply l)

theorem measurable_independentValue {k : Nat}
    {est : (Fin k → Nat → E) → Real}
    (hest : Measurable est) : Measurable (independentValue est) :=
  hest.comp measurable_independentStatePaths

/-- Cost erasure commutes with the finite product: the resulting law is exactly the
independent complete-path law used by the corrected estimator proof. -/
theorem map_independentStatePaths_independentCostedLaw
    (k : Nat)
    (P : Nat → Kernel E E) [∀ i, IsMarkovKernel (P i)]
    (Q : Nat → Kernel E (ENNReal × E)) [∀ i, IsMarkovKernel (Q i)]
    (mu0 : Measure E) [IsProbabilityMeasure mu0]
    (hforget : ∀ i x, Measure.map Prod.snd (Q i x) = P i x) :
    Measure.map independentStatePaths (independentCostedLaw k Q mu0) =
      independentPathLaw k P mu0 := by
  letI : IsProbabilityMeasure (oneRunLaw Q mu0) := by
    unfold oneRunLaw
    infer_instance
  letI : ∀ _l : Fin k, SigmaFinite
      (Measure.map (Ttc.SequentialCostedPathLumping.pathMap Prod.snd)
        (oneRunLaw Q mu0)) := fun _l ↦ by infer_instance
  unfold independentCostedLaw independentPathLaw
  unfold Ttc.CVIndependentStreamMoments.independentStreamLaw
  change Measure.map (fun omega l ↦ statePath (omega l))
      (Measure.pi fun _l : Fin k ↦ oneRunLaw Q mu0) =
    Measure.pi (fun _l : Fin k ↦ Arlib.Probability.inhomogeneousPathMeasure P mu0)
  unfold statePath
  rw [Measure.pi_map_pi (fun _l ↦
    (Ttc.SequentialCostedPathLumping.measurable_pathMap measurable_snd).aemeasurable)]
  congr 1
  funext l
  exact Ttc.SequentialCostedPathLumping.map_statePath_execution Q P mu0 hforget

/-- Exact product-cost accounting reduced to the scalar full-run mean. -/
theorem lintegral_independentQueryCost_le
    (k m : Nat)
    (Q : Nat → Kernel E (ENNReal × E)) [∀ i, IsMarkovKernel (Q i)]
    (mu0 : Measure E) [IsProbabilityMeasure mu0] {B : ENNReal}
    (hscalar : (∫⁻ omega, queryCost m omega ∂oneRunLaw Q mu0) ≤ B) :
    (∫⁻ omega, independentQueryCost m omega ∂independentCostedLaw k Q mu0) ≤
      (k : ENNReal) * B := by
  letI : IsProbabilityMeasure (oneRunLaw Q mu0) := by
    unfold oneRunLaw
    infer_instance
  change (∫⁻ omega, ∑ l : Fin k, queryCost m (omega l)
      ∂independentCostedLaw k Q mu0) ≤ _
  rw [lintegral_finset_sum]
  · calc
      ∑ l : Fin k, ∫⁻ omega, queryCost m (omega l)
          ∂independentCostedLaw k Q mu0 ≤ ∑ _l : Fin k, B := by
            apply Finset.sum_le_sum
            intro l _hl
            let hmp := Ttc.CVIndependentStreamMoments.measurePreserving_streamCoord
              (k := k) (oneRunLaw Q mu0) l
            have hmapEval : Measure.map (fun omega : IndependentCostedPath k E ↦ omega l)
                (independentCostedLaw k Q mu0) = oneRunLaw Q mu0 := by
              unfold independentCostedLaw
              simpa only [Ttc.CVIndependentStreamMoments.independentStreamLaw] using
                hmp.map_eq
            calc
              ∫⁻ omega, queryCost m (omega l) ∂independentCostedLaw k Q mu0 =
                  ∫⁻ omega, queryCost m omega ∂oneRunLaw Q mu0 := by
                    rw [← lintegral_map (measurable_queryCost m) (measurable_pi_apply l)]
                    rw [hmapEval]
              _ ≤ B := hscalar
      _ = (k : ENNReal) * B := by simp [Finset.sum_const, nsmul_eq_mul]
  · intro l _hl
    exact (measurable_queryCost m).comp (measurable_pi_apply l)

/-- The exact expected cost from scalar per-phase bounds.  This is the only cost seam
needed by the public constructor below. -/
theorem lintegral_independentQueryCost_le_phaseBounds
    (k m : Nat)
    (Q : Nat → Kernel E (ENNReal × E)) [∀ i, IsMarkovKernel (Q i)]
    (mu0 : Measure E) [IsProbabilityMeasure mu0]
    (phaseBound : Nat → ENNReal)
    (hphase : ∀ i, i < m →
      (∫⁻ x, Ttc.SequentialCost.stepMean Q i x ∂stateMarginal Q mu0 i) ≤
        phaseBound i) :
    (∫⁻ omega, independentQueryCost m omega ∂independentCostedLaw k Q mu0) ≤
      (k : ENNReal) * ∑ i ∈ Finset.range m, phaseBound i := by
  exact lintegral_independentQueryCost_le k m Q mu0
    (expected_queryCost_le Q mu0 m phaseBound hphase)

variable {n : Nat}

/-- Public generalized certificate constructor for an honest product of scalar costed
paths.  `haccuracy` is in exactly the law/estimator shape produced by
`corrected_independentStreams_accuracy_four_fifths`; the remaining runtime premise is the
sum of scalar phase-query means, multiplied by the number of independent streams.
-/
theorem generalizedPublicOneRunCertificates_of_independentCostedStreams
    (oneEnvelope : Ttc.CVAdaptive.VolumeInput n → Real)
    (k m : Ttc.CVAdaptive.VolumeInput n → Nat)
    (P : ∀ a, Nat → Kernel E E) [hP : ∀ a i, IsMarkovKernel (P a i)]
    (Q : ∀ a, Nat → Kernel E (ENNReal × E))
    [hQ : ∀ a i, IsMarkovKernel (Q a i)]
    (mu0 : ∀ a, Measure E) [hmu0 : ∀ a, IsProbabilityMeasure (mu0 a)]
    (phaseBound : ∀ a, Nat → ENNReal)
    (est : ∀ a, (Fin (k a) → Nat → E) → Real)
    (hforget : ∀ a i x, Measure.map Prod.snd (Q a i x) = P a i x)
    (hphase : ∀ a i, i < m a →
      (∫⁻ x, Ttc.SequentialCost.stepMean (Q a) i x
        ∂stateMarginal (Q a) (mu0 a) i) ≤ phaseBound a i)
    (henvelope : ∀ a,
      ((k a : Nat) : ENNReal) * ∑ i ∈ Finset.range (m a), phaseBound a i ≤
        ENNReal.ofReal (oneEnvelope a))
    (hest : ∀ a, Measurable (est a))
    (haccuracy : ∀ (K : Set (Ttc.Space n)) (eps p : Real),
      0 < eps → 0 < p → p < 1 → Convex Real K →
      Metric.ball (0 : Ttc.Space n) 1 ⊆ K → volume K ≠ ⊤ →
      4 / 5 ≤ (independentPathLaw (k (K, eps, p)) (P (K, eps, p))
        (mu0 (K, eps, p))).real
        {omega | est (K, eps, p) omega ∈
          Icc ((1 - eps) * (volume K).toReal)
            ((1 + eps) * (volume K).toReal)}) :
    GeneralizedPublicOneRunCertificates n oneEnvelope
      (fun a ↦ IndependentCostedPath (k a) E)
      (fun a ↦ independentCostedLaw (k a) (Q a) (mu0 a))
      (fun a ↦ independentQueryCost (m a))
      (fun a ↦ independentValue (est a)) := by
  refine
    { probability := fun _a ↦ inferInstance
      cost_measurable := fun a ↦ measurable_independentQueryCost (m a)
      value_measurable := fun a ↦ measurable_independentValue (hest a)
      expected_queries := fun a ↦
        (lintegral_independentQueryCost_le_phaseBounds (k a) (m a) (Q a) (mu0 a)
          (phaseBound a) (hphase a)).trans (henvelope a)
      accuracy := ?_ }
  intro K eps p heps hp hp1 hKc hball hfin
  let a : Ttc.CVAdaptive.VolumeInput n := (K, eps, p)
  let G : Set (Fin (k a) → Nat → E) :=
    {omega | est a omega ∈
      Icc ((1 - eps) * (volume K).toReal) ((1 + eps) * (volume K).toReal)}
  have hG : MeasurableSet G := measurableSet_Icc.preimage (hest a)
  have hmap := map_independentStatePaths_independentCostedLaw
    (k a) (P a) (Q a) (mu0 a) (hforget a)
  have heq : (independentCostedLaw (k a) (Q a) (mu0 a)).real
      (independentStatePaths ⁻¹' G) =
      (independentPathLaw (k a) (P a) (mu0 a)).real G := by
    change ((independentCostedLaw (k a) (Q a) (mu0 a))
      (independentStatePaths ⁻¹' G)).toReal = _
    rw [← Measure.map_apply measurable_independentStatePaths hG, hmap]
    rfl
  change 4 / 5 ≤ (independentCostedLaw (k a) (Q a) (mu0 a)).real
    (independentStatePaths ⁻¹' G)
  rw [heq]
  exact haccuracy K eps p heps hp hp1 hKc hball hfin

#print axioms map_independentStatePaths_independentCostedLaw
#print axioms lintegral_independentQueryCost_le_phaseBounds
#print axioms generalizedPublicOneRunCertificates_of_independentCostedStreams

end Ttc.CVIndependentStreamGeneralizedCertificate
