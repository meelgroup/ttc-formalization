import Ttc.Exec.CVGaussianAdaptiveBlockOperational
import Ttc.Exec.CVGaussianWarmFallbackCostedPhaseKernel

/-! Zero-cost costed refinement of an active schedule with an exact reference tail. -/

namespace Ttc.CVGaussianCappedCostedSchedule

open MeasureTheory ProbabilityTheory
open Arlib Arlib.Probability Arlib.MarkovChains
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.SequentialCost
open Ttc.CVIndependentStreamDependence
open Ttc.CVIndependentStreamGeneralizedCertificate
open Ttc.CVGeneralPolynomialCutoffCapstone
open Ttc.GenericCostedPhaseCertificate
open scoped ENNReal Classical

variable {Score Seed : Type} [MeasurableSpace Score] [MeasurableSpace Seed]

/-- Record real costs on active phases and attach cost zero to exact tail resampling. -/
noncomputable def costedActiveReferenceTailSchedule
    (m : Nat) (R : Nat → Kernel Seed (ENNReal × (Score × Seed)))
    (tail : Nat → Measure (Score × Seed)) :
    Nat → Kernel Seed (ENNReal × (Score × Seed)) := fun i ↦
  if i + 1 < m then R i
  else Kernel.const Seed
    (Measure.map (fun z : Score × Seed ↦ ((0 : ENNReal), z)) (tail (i + 1)))

instance costedActiveReferenceTailSchedule.isMarkovKernel
    (m : Nat) (R : Nat → Kernel Seed (ENNReal × (Score × Seed)))
    [∀ i, IsMarkovKernel (R i)]
    (tail : Nat → Measure (Score × Seed))
    [∀ i, IsProbabilityMeasure (tail i)] (i : Nat) :
    IsMarkovKernel (costedActiveReferenceTailSchedule m R tail i) := by
  unfold costedActiveReferenceTailSchedule
  split
  · infer_instance
  · letI : IsProbabilityMeasure
        (Measure.map (fun z : Score × Seed ↦ ((0 : ENNReal), z)) (tail (i + 1))) :=
      Measure.isProbabilityMeasure_map (by fun_prop :
        Measurable (fun z : Score × Seed ↦ ((0 : ENNReal), z))).aemeasurable
    exact Kernel.const.instIsMarkovKernel

theorem map_snd_costedActiveReferenceTailSchedule
    (m : Nat) (Q : Nat → Kernel Seed (Score × Seed))
    (R : Nat → Kernel Seed (ENNReal × (Score × Seed)))
    (tail : Nat → Measure (Score × Seed))
    [∀ i, IsProbabilityMeasure (tail i)]
    (hforget : ∀ i x, Measure.map Prod.snd (R i x) = Q i x)
    (i : Nat) (x : Seed) :
    Measure.map Prod.snd (costedActiveReferenceTailSchedule m R tail i x) =
      activeReferenceTailSchedule m Q tail i x := by
  unfold costedActiveReferenceTailSchedule activeReferenceTailSchedule
  by_cases hi : i + 1 < m
  · simp only [if_pos hi]
    exact hforget i x
  · simp only [if_neg hi, Kernel.const_apply]
    rw [Measure.map_map measurable_snd (by fun_prop :
      Measurable (fun z : Score × Seed ↦ ((0 : ENNReal), z)))]
    rw [show Prod.snd ∘ (fun z : Score × Seed ↦ ((0 : ENNReal), z)) = id by
      funext z
      rfl, Measure.map_id]

/-- Cost erasure after lifting from seed kernels to score/seed state kernels. -/
theorem map_snd_costedStateActiveReferenceTailSchedule
    (m : Nat) (Q : Nat → Kernel Seed (Score × Seed))
    (R : Nat → Kernel Seed (ENNReal × (Score × Seed)))
    (tail : Nat → Measure (Score × Seed))
    [∀ i, IsProbabilityMeasure (tail i)]
    (hforget : ∀ i x, Measure.map Prod.snd (R i x) = Q i x)
    (i : Nat) (z : Score × Seed) :
    Measure.map Prod.snd
        (costedStateScheduleFromSeed
          (costedActiveReferenceTailSchedule m R tail) i z) =
      stateScheduleFromSeed (activeReferenceTailSchedule m Q tail) i z := by
  apply map_snd_costedStateScheduleFromSeed
  intro j x
  exact map_snd_costedActiveReferenceTailSchedule m Q R tail hforget j x

/-- An inactive tail transition has identically zero conditional cost. -/
theorem stepMean_costedStateActiveReferenceTailSchedule_inactive
    (m : Nat) (R : Nat → Kernel Seed (ENNReal × (Score × Seed)))
    (tail : Nat → Measure (Score × Seed))
    [∀ i, IsProbabilityMeasure (tail i)]
    (i : Nat) (hi : ¬ i + 1 < m) (z : Score × Seed) :
    stepMean
      (costedStateScheduleFromSeed (costedActiveReferenceTailSchedule m R tail)) i z = 0 := by
  unfold stepMean costedStateScheduleFromSeed costedStateKernelFromSeed
  rw [Kernel.comap_apply]
  unfold costedActiveReferenceTailSchedule
  rw [if_neg hi, Kernel.const_apply]
  rw [lintegral_map]
  · simp
  · fun_prop
  · exact (by fun_prop : Measurable
      (fun z : Score × Seed ↦ ((0 : ENNReal), z)))

theorem lintegral_stepMean_costedStateActiveReferenceTailSchedule_inactive
    (m : Nat) (R : Nat → Kernel Seed (ENNReal × (Score × Seed)))
    (tail : Nat → Measure (Score × Seed))
    [∀ i, IsProbabilityMeasure (tail i)]
    (mu : Measure (Score × Seed)) (i : Nat) (hi : ¬ i + 1 < m) :
    (∫⁻ z, stepMean
      (costedStateScheduleFromSeed (costedActiveReferenceTailSchedule m R tail)) i z
      ∂mu) = 0 := by
  simp_rw [stepMean_costedStateActiveReferenceTailSchedule_inactive m R tail i hi]
  exact lintegral_zero

variable {n : Nat}

/-- Public one-run certificate constructor for the capped exact-tail cost refinement.
The remaining `haccuracy` premise is precisely the estimator-identification theorem; all
cost erasure and inactive-tail accounting are closed here. -/
theorem generalizedPublicOneRunCertificates_activeReferenceTail
    (oneEnvelope : Ttc.CVAdaptive.VolumeInput n → Real)
    (k m : Ttc.CVAdaptive.VolumeInput n → Nat)
    (Q : ∀ a : Ttc.CVAdaptive.VolumeInput n,
      Nat → Kernel Seed (Score × Seed))
    [∀ a i, IsMarkovKernel (Q a i)]
    (R : ∀ a : Ttc.CVAdaptive.VolumeInput n,
      Nat → Kernel Seed (ENNReal × (Score × Seed)))
    [∀ a i, IsMarkovKernel (R a i)]
    (tail : ∀ a : Ttc.CVAdaptive.VolumeInput n,
      Nat → Measure (Score × Seed))
    [∀ a i, IsProbabilityMeasure (tail a i)]
    (mu0 : ∀ a : Ttc.CVAdaptive.VolumeInput n, Measure (Score × Seed))
    [∀ a, IsProbabilityMeasure (mu0 a)]
    (phaseBound : ∀ a : Ttc.CVAdaptive.VolumeInput n, Nat → ENNReal)
    (est : ∀ a : Ttc.CVAdaptive.VolumeInput n,
      (Fin (k a) → Nat → Score × Seed) → Real)
    (hforget : ∀ a i x, Measure.map Prod.snd (R a i x) = Q a i x)
    (hphase : ∀ a i, i < m a →
      (∫⁻ x, stepMean
        (costedStateScheduleFromSeed
          (costedActiveReferenceTailSchedule (m a) (R a) (tail a))) i x
        ∂stateMarginal
          (costedStateScheduleFromSeed
            (costedActiveReferenceTailSchedule (m a) (R a) (tail a)))
          (mu0 a) i) ≤ phaseBound a i)
    (henvelope : ∀ a,
      ((k a : Nat) : ENNReal) * ∑ i ∈ Finset.range (m a), phaseBound a i ≤
        ENNReal.ofReal (oneEnvelope a))
    (hest : ∀ a, Measurable (est a))
    (haccuracy : ∀ (K : Set (Ttc.Space n)) (eps p : Real),
      0 < eps → 0 < p → p < 1 → Convex Real K →
      Metric.ball (0 : Ttc.Space n) 1 ⊆ K → volume K ≠ ⊤ →
      4 / 5 ≤
        (independentPathLaw (k (K, eps, p))
          (stateScheduleFromSeed
            (activeReferenceTailSchedule (m (K, eps, p))
              (Q (K, eps, p)) (tail (K, eps, p))))
          (mu0 (K, eps, p))).real
          {omega | est (K, eps, p) omega ∈
            Set.Icc ((1 - eps) * (volume K).toReal)
              ((1 + eps) * (volume K).toReal)}) :
    GeneralizedPublicOneRunCertificates n oneEnvelope
      (fun a ↦ IndependentCostedPath (k a) (Score × Seed))
      (fun a ↦ independentCostedLaw (k a)
        (costedStateScheduleFromSeed
          (costedActiveReferenceTailSchedule (m a) (R a) (tail a))) (mu0 a))
      (fun a ↦ independentQueryCost (m a))
      (fun a ↦ independentValue (est a)) := by
  apply generalizedPublicOneRunCertificates_of_independentCostedStreams
    oneEnvelope k m
    (fun a ↦ stateScheduleFromSeed
      (activeReferenceTailSchedule (m a) (Q a) (tail a)))
    (fun a ↦ costedStateScheduleFromSeed
      (costedActiveReferenceTailSchedule (m a) (R a) (tail a)))
    mu0 phaseBound est
  · intro a i z
    exact map_snd_costedStateActiveReferenceTailSchedule
      (m a) (Q a) (R a) (tail a) (hforget a) i z
  · exact hphase
  · exact henvelope
  · exact hest
  · exact haccuracy

/-- The capped exact-tail certificate yields the public expected-query oracle through
the existing single global cutoff and median amplification. -/
noncomputable def expectedQueryVolumeAlgorithm_activeReferenceTail
    (oneEnvelope : Ttc.CVAdaptive.VolumeInput n → Real)
    (k m : Ttc.CVAdaptive.VolumeInput n → Nat)
    (R : ∀ a : Ttc.CVAdaptive.VolumeInput n,
      Nat → Kernel Seed (ENNReal × (Score × Seed)))
    [∀ a i, IsMarkovKernel (R a i)]
    (tail : ∀ a : Ttc.CVAdaptive.VolumeInput n,
      Nat → Measure (Score × Seed))
    [∀ a i, IsProbabilityMeasure (tail a i)]
    (mu0 : ∀ a : Ttc.CVAdaptive.VolumeInput n, Measure (Score × Seed))
    [∀ a, IsProbabilityMeasure (mu0 a)]
    (est : ∀ a : Ttc.CVAdaptive.VolumeInput n,
      (Fin (k a) → Nat → Score × Seed) → Real)
    (hcert : GeneralizedPublicOneRunCertificates n oneEnvelope
      (fun a ↦ IndependentCostedPath (k a) (Score × Seed))
      (fun a ↦ independentCostedLaw (k a)
        (costedStateScheduleFromSeed
          (costedActiveReferenceTailSchedule (m a) (R a) (tail a))) (mu0 a))
      (fun a ↦ independentQueryCost (m a))
      (fun a ↦ independentValue (est a))) : Ttc.ExpectedQueryVolumeAlgorithm n :=
  expectedQueryVolumeAlgorithmOfGeneralizedCertificates n oneEnvelope
    (fun a ↦ IndependentCostedPath (k a) (Score × Seed))
    (fun a ↦ independentCostedLaw (k a)
      (costedStateScheduleFromSeed
        (costedActiveReferenceTailSchedule (m a) (R a) (tail a))) (mu0 a))
    (fun a ↦ independentQueryCost (m a))
    (fun a ↦ independentValue (est a)) hcert

#print axioms map_snd_costedStateActiveReferenceTailSchedule
#print axioms stepMean_costedStateActiveReferenceTailSchedule_inactive
#print axioms generalizedPublicOneRunCertificates_activeReferenceTail
#print axioms expectedQueryVolumeAlgorithm_activeReferenceTail

end Ttc.CVGaussianCappedCostedSchedule
