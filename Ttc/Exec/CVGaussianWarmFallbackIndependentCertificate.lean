import Ttc.Exec.CVGaussianWarmFallbackAnalytic
import Ttc.Exec.CVGaussianWarmFallbackCostedPhaseKernel
import Ttc.Exec.CVIndependentStreamAccuracy

/-!
# Independent-stream accuracy for the literal Gaussian warm-fallback schedule

This file closes the empirical-moment seam in the costed warm-fallback assembly.  A
scalar phase score with relative second moment at most `9` gives the corrected
`1 + 8 / k` moment bound after taking the average of `k` genuinely independent complete
Gaussian warm-fallback paths.

The remaining `IndependentStreamOperational` argument is deliberately visible.  Its
Gaussian construction is supplied by `seedProjectedOperational_of_warmFallback`; the
current analytic accepted-sublaw theorem covers active indices `i + 1 < m`, whereas the
operational structure asks for every `i : Nat`.  Thus extending/capping the phase family
outside the active range is the exact remaining indexing seam, not a moment hypothesis.
-/

namespace Ttc.CVGaussianWarmFallbackIndependentCertificate

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVCorrected
open Ttc.CVGaussianWarmFallbackOperational
open Ttc.CVGaussianWarmFallbackCostedPhaseKernel
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVIndependentStreamMoments
open Ttc.CVIndependentStreamDependence
open Ttc.CVIndependentStreamAccuracy
open Ttc.CVIndependentStreamGeneralizedCertificate
open Ttc.CVGeneralPolynomialCutoffCapstone
open Ttc.GenericCostedPhaseCertificate
open scoped ENNReal Classical BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- Corrected one-run accuracy for the literal Gaussian warm-fallback phase family.

Unlike the generic independent-stream theorem, this statement does not assume an
empirical relative-second-moment inequality: it derives that inequality from the scalar
score bound `hscalarSq`.  It also derives measurability and square-integrability of the
empirical average. -/
theorem corrected_gaussianWarmFallback_independent_accuracy_four_fifths_of_scalarMoment
    {k m : Nat} (hk0 : 0 < k)
    {K : Set (State n)} (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)]
    (mu0 : Measure (ScoreSeed n)) [IsProbabilityMeasure mu0]
    (g : Nat → (Nat → ScoreSeed n) → Real)
    (Wbar W : Nat → (Fin k → Nat → ScoreSeed n) → Real)
    {eta : Real} (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hk : CorrectedSampleBudget m k eta)
    (hg : ∀ j, Measurable (g j))
    (hgL2 : ∀ j, MemLp (g j) 2
      (inhomogeneousPathMeasure
        (stateScheduleFromSeed
          (warmFallbackSchedule K hK delta sigmaSq shrink hdelta hshrink
            retrySteps retries fallback)) mu0))
    (hscalarSq : ∀ j,
      (∫ x, (g j x) ^ 2
        ∂inhomogeneousPathMeasure
          (stateScheduleFromSeed
            (warmFallbackSchedule K hK delta sigmaSq shrink hdelta hshrink
              retrySteps retries fallback)) mu0) ≤
        9 *
          (∫ x, g j x
            ∂inhomogeneousPathMeasure
              (stateScheduleFromSeed
                (warmFallbackSchedule K hK delta sigmaSq shrink hdelta hshrink
                  retrySteps retries fallback)) mu0) ^ 2)
    (hV0 : ∀ j omega, 0 ≤ streamAverage (k := k) (g j) omega)
    (hEpos : ∀ j, 0 < ∫ omega, streamAverage (k := k) (g j) omega
      ∂independentPathLaw k
        (stateScheduleFromSeed
          (warmFallbackSchedule K hK delta sigmaSq shrink hdelta hshrink
            retrySteps retries fallback)) mu0)
    (hVcap : ∀ j omega, streamAverage (k := k) (g j) omega ≤
      2 * correctedAlpha m eta *
        ∫ z, streamAverage (k := k) (g j) z
          ∂independentPathLaw k
            (stateScheduleFromSeed
              (warmFallbackSchedule K hK delta sigmaSq shrink hdelta hshrink
                retrySteps retries fallback)) mu0)
    (hV2cap : ∀ j omega, (streamAverage (k := k) (g j) omega) ^ 2 ≤
      2 * correctedAlpha m eta ^ 2 *
        ∫ z, (streamAverage (k := k) (g j) z) ^ 2
          ∂independentPathLaw k
            (stateScheduleFromSeed
              (warmFallbackSchedule K hK delta sigmaSq shrink hdelta hshrink
                retrySteps retries fallback)) mu0)
    (hWbarm : ∀ j, Measurable (Wbar j))
    (hWm : ∀ j, Measurable (W j))
    (hW0 : ∀ j omega, 0 ≤ Wbar j omega)
    (hWint : ∀ j, Integrable (Wbar j)
      (independentPathLaw k
        (stateScheduleFromSeed
          (warmFallbackSchedule K hK delta sigmaSq shrink hdelta hshrink
            retrySteps retries fallback)) mu0))
    (hWEpos : ∀ j, 0 < ∫ omega, Wbar j omega
      ∂independentPathLaw k
        (stateScheduleFromSeed
          (warmFallbackSchedule K hK delta sigmaSq shrink hdelta hshrink
            retrySteps retries fallback)) mu0)
    (hVdef : ∀ j omega, streamAverage (k := k) (g j) omega =
      min (Wbar j omega)
        (correctedAlpha m eta *
          ∫ z, Wbar j z
            ∂independentPathLaw k
              (stateScheduleFromSeed
                (warmFallbackSchedule K hK delta sigmaSq shrink hdelta hshrink
                  retrySteps retries fallback)) mu0))
    {Eexact : Set (Fin k → Nat → ScoreSeed n)} (hEexact : MeasurableSet Eexact)
    (hExactFail : (independentPathLaw k
      (stateScheduleFromSeed
        (warmFallbackSchedule K hK delta sigmaSq shrink hdelta hshrink
          retrySteps retries fallback)) mu0).real Eexactᶜ ≤ 1 / 20)
    (hExact : ∀ omega ∈ Eexact,
      phaseProduct Wbar m omega = phaseProduct W m omega)
    (hop : IndependentStreamOperational k
      (stateScheduleFromSeed
        (warmFallbackSchedule K hK delta sigmaSq shrink hdelta hshrink
          retrySteps retries fallback))
      (warmFallbackSchedule K hK delta sigmaSq shrink hdelta hshrink
        retrySteps retries fallback)
      Prod.snd mu0 (fun j ↦ streamAverage (k := k) (g j)) m eta)
    (initialNormalizer volumeTarget : Real) (hinit : 0 ≤ initialNormalizer)
    (htarget : initialNormalizer *
      prefixMean
        (independentPathLaw k
          (stateScheduleFromSeed
            (warmFallbackSchedule K hK delta sigmaSq shrink hdelta hshrink
              retrySteps retries fallback)) mu0)
        (fun j ↦ streamAverage (k := k) (g j)) m = volumeTarget) :
    4 / 5 ≤ (independentPathLaw k
      (stateScheduleFromSeed
        (warmFallbackSchedule K hK delta sigmaSq shrink hdelta hshrink
          retrySteps retries fallback)) mu0).real
      {omega | initialNormalizer * phaseProduct W m omega ∈
        Ttc.relErr eta volumeTarget} := by
  let P := stateScheduleFromSeed
    (warmFallbackSchedule K hK delta sigmaSq shrink hdelta hshrink
      retrySteps retries fallback)
  let scalarLaw := inhomogeneousPathMeasure P mu0
  let V : Nat → (Fin k → Nat → ScoreSeed n) → Real :=
    fun j ↦ streamAverage (k := k) (g j)
  have hVm : ∀ j, Measurable (V j) := fun j ↦ measurable_streamAverage (hg j)
  have hV2 : ∀ j, Integrable (fun omega ↦ (V j omega) ^ 2)
      (independentPathLaw k P mu0) := by
    intro j
    exact integrable_streamAverage_sq (k := k) scalarLaw (hgL2 j)
  have hphaseMoment : ∀ j,
      (∫ omega, (V j omega) ^ 2 ∂independentPathLaw k P mu0) ≤
        (1 + 8 / (k : Real)) *
          (∫ omega, V j omega ∂independentPathLaw k P mu0) ^ 2 := by
    intro j
    have hmean :
        ∫ omega, V j omega ∂independentPathLaw k P mu0 =
          ∫ x, g j x ∂scalarLaw := by
      exact integral_streamAverage hk0 scalarLaw (hg j)
        ((hgL2 j).integrable (by norm_num))
    have hsq : ∫ x, (g j x) ^ 2 ∂scalarLaw ≤
        9 * (∫ x, g j x ∂scalarLaw) ^ 2 := by
      simpa only [scalarLaw, P] using hscalarSq j
    calc
      ∫ omega, (V j omega) ^ 2 ∂independentPathLaw k P mu0 ≤
          (1 + 8 / (k : Real)) * (∫ x, g j x ∂scalarLaw) ^ 2 := by
            exact integral_streamAverage_sq_le_nine hk0 scalarLaw (hg j) (hgL2 j)
              rfl hsq
      _ = (1 + 8 / (k : Real)) *
          (∫ omega, V j omega ∂independentPathLaw k P mu0) ^ 2 := by rw [hmean]
  exact corrected_independentStreams_accuracy_four_fifths V Wbar W
    heta heta1 hk hVm hV0 hEpos hVcap hV2 hV2cap hWbarm hWm hW0 hWint hWEpos
    hVdef hphaseMoment hEexact hExactFail hExact hop initialNormalizer volumeTarget
    hinit htarget

#print axioms corrected_gaussianWarmFallback_independent_accuracy_four_fifths_of_scalarMoment

/-- Literal public one-run certificate for the costed Gaussian warm-fallback schedule.

The accuracy premise has the exact cost-erased `independentPathLaw` produced by the
preceding theorem.  Runtime is reduced to the scalar incoming-marginal phase bounds; the
costed kernel itself and the factor `k` are fully discharged here. -/
theorem generalizedPublicOneRunCertificates_gaussianWarmFallback
    (oneEnvelope : Ttc.CVAdaptive.VolumeInput n → Real)
    (k m : Ttc.CVAdaptive.VolumeInput n → Nat)
    (hK : ∀ a : Ttc.CVAdaptive.VolumeInput n, MeasurableSet a.1)
    (delta sigmaSq shrink : Ttc.CVAdaptive.VolumeInput n → Nat → Real)
    (hdelta : ∀ a i, 0 < delta a i)
    (hshrink : ∀ a i, shrink a i ≠ 0)
    (retrySteps : Ttc.CVAdaptive.VolumeInput n → Nat → Nat → Nat)
    (retries : Ttc.CVAdaptive.VolumeInput n → Nat → Nat)
    (fallback : ∀ a : Ttc.CVAdaptive.VolumeInput n,
      Nat → Measure (ScoreSeed n))
    [hfallback : ∀ a i, IsProbabilityMeasure (fallback a i)]
    (mu0 : ∀ a : Ttc.CVAdaptive.VolumeInput n, Measure (ScoreSeed n))
    [hmu0 : ∀ a, IsProbabilityMeasure (mu0 a)]
    (phaseBound : ∀ a : Ttc.CVAdaptive.VolumeInput n, Nat → ENNReal)
    (est : ∀ a : Ttc.CVAdaptive.VolumeInput n,
      (Fin (k a) → Nat → ScoreSeed n) → Real)
    (hphase : ∀ a i, i < m a →
      (∫⁻ x, Ttc.SequentialCost.stepMean
        (costedStateScheduleFromSeed
          (warmFallbackCostedSchedule a.1 (hK a) (delta a) (sigmaSq a) (shrink a)
            (hdelta a) (hshrink a) (retrySteps a) (retries a) (fallback a))) i x
        ∂stateMarginal
          (costedStateScheduleFromSeed
            (warmFallbackCostedSchedule a.1 (hK a) (delta a) (sigmaSq a) (shrink a)
              (hdelta a) (hshrink a) (retrySteps a) (retries a) (fallback a)))
          (mu0 a) i) ≤ phaseBound a i)
    (henvelope : ∀ a,
      ((k a : Nat) : ENNReal) * ∑ i ∈ Finset.range (m a), phaseBound a i ≤
        ENNReal.ofReal (oneEnvelope a))
    (hest : ∀ a, Measurable (est a))
    (haccuracy : ∀ (K : Set (Ttc.Space n)) (eps p : Real),
      0 < eps → 0 < p → p < 1 → Convex Real K →
      ball (0 : Ttc.Space n) 1 ⊆ K → volume K ≠ ⊤ →
      4 / 5 ≤
        (independentPathLaw (k (K, eps, p))
          (stateScheduleFromSeed
            (warmFallbackSchedule K (hK (K, eps, p))
              (delta (K, eps, p)) (sigmaSq (K, eps, p)) (shrink (K, eps, p))
              (hdelta (K, eps, p)) (hshrink (K, eps, p))
              (retrySteps (K, eps, p)) (retries (K, eps, p))
              (fallback (K, eps, p))))
          (mu0 (K, eps, p))).real
          {omega | est (K, eps, p) omega ∈
            Icc ((1 - eps) * (volume K).toReal)
              ((1 + eps) * (volume K).toReal)}) :
    GeneralizedPublicOneRunCertificates n oneEnvelope
      (fun a ↦ IndependentCostedPath (k a) (ScoreSeed n))
      (fun a ↦ independentCostedLaw (k a)
        (costedStateScheduleFromSeed
          (warmFallbackCostedSchedule a.1 (hK a) (delta a) (sigmaSq a) (shrink a)
            (hdelta a) (hshrink a) (retrySteps a) (retries a) (fallback a)))
        (mu0 a))
      (fun a ↦ independentQueryCost (m a))
      (fun a ↦ independentValue (est a)) := by
  apply generalizedPublicOneRunCertificates_of_independentCostedStreams
    oneEnvelope k m
    (fun a ↦ stateScheduleFromSeed
      (warmFallbackSchedule a.1 (hK a) (delta a) (sigmaSq a) (shrink a)
        (hdelta a) (hshrink a) (retrySteps a) (retries a) (fallback a)))
    (fun a ↦ costedStateScheduleFromSeed
      (warmFallbackCostedSchedule a.1 (hK a) (delta a) (sigmaSq a) (shrink a)
        (hdelta a) (hshrink a) (retrySteps a) (retries a) (fallback a)))
    mu0 phaseBound est
  · intro a i x
    exact map_snd_costedStateWarmFallbackSchedule a.1 (hK a) (delta a) (sigmaSq a)
      (shrink a) (hdelta a) (hshrink a) (retrySteps a) (retries a) (fallback a) i x
  · exact hphase
  · exact henvelope
  · exact hest
  · exact haccuracy

/-- The preceding literal certificate yields the semantic expected-query volume oracle
through the repository's single global cutoff and median amplification. -/
noncomputable def expectedQueryVolumeAlgorithm_gaussianWarmFallback
    (oneEnvelope : Ttc.CVAdaptive.VolumeInput n → Real)
    (k m : Ttc.CVAdaptive.VolumeInput n → Nat)
    (hK : ∀ a : Ttc.CVAdaptive.VolumeInput n, MeasurableSet a.1)
    (delta sigmaSq shrink : Ttc.CVAdaptive.VolumeInput n → Nat → Real)
    (hdelta : ∀ a i, 0 < delta a i)
    (hshrink : ∀ a i, shrink a i ≠ 0)
    (retrySteps : Ttc.CVAdaptive.VolumeInput n → Nat → Nat → Nat)
    (retries : Ttc.CVAdaptive.VolumeInput n → Nat → Nat)
    (fallback : ∀ a : Ttc.CVAdaptive.VolumeInput n,
      Nat → Measure (ScoreSeed n))
    [hfallback : ∀ a i, IsProbabilityMeasure (fallback a i)]
    (mu0 : ∀ a : Ttc.CVAdaptive.VolumeInput n, Measure (ScoreSeed n))
    [hmu0 : ∀ a, IsProbabilityMeasure (mu0 a)]
    (phaseBound : ∀ a : Ttc.CVAdaptive.VolumeInput n, Nat → ENNReal)
    (est : ∀ a : Ttc.CVAdaptive.VolumeInput n,
      (Fin (k a) → Nat → ScoreSeed n) → Real)
    (hcert : GeneralizedPublicOneRunCertificates n oneEnvelope
      (fun a ↦ IndependentCostedPath (k a) (ScoreSeed n))
      (fun a ↦ independentCostedLaw (k a)
        (costedStateScheduleFromSeed
          (warmFallbackCostedSchedule a.1 (hK a) (delta a) (sigmaSq a) (shrink a)
            (hdelta a) (hshrink a) (retrySteps a) (retries a) (fallback a)))
        (mu0 a))
      (fun a ↦ independentQueryCost (m a))
      (fun a ↦ independentValue (est a))) : Ttc.ExpectedQueryVolumeAlgorithm n :=
  expectedQueryVolumeAlgorithmOfGeneralizedCertificates n oneEnvelope
    (fun a ↦ IndependentCostedPath (k a) (ScoreSeed n))
    (fun a ↦ independentCostedLaw (k a)
      (costedStateScheduleFromSeed
        (warmFallbackCostedSchedule a.1 (hK a) (delta a) (sigmaSq a) (shrink a)
          (hdelta a) (hshrink a) (retrySteps a) (retries a) (fallback a)))
      (mu0 a))
    (fun a ↦ independentQueryCost (m a))
    (fun a ↦ independentValue (est a)) hcert

#print axioms generalizedPublicOneRunCertificates_gaussianWarmFallback
#print axioms expectedQueryVolumeAlgorithm_gaussianWarmFallback

end Ttc.CVGaussianWarmFallbackIndependentCertificate
