import Ttc.Exec.CVGaussianGuardedExpectedVolume

/-!
# Polynomial expected-query envelope for the guarded Gaussian oracle

This file is deliberately only a runtime capstone.  It specializes the generic guarded
expected-bound theorem to the literal capped Gaussian constructor and to the conservative
corrected continuing-retry envelope.  Estimator accuracy remains a premise of the
constructor and is not reproved here.

The bound is the generalized corrected envelope, whose exact expansion contains
`eps ^ (-10)`.  Thus this theorem makes no claim about the sharper source exponent.
-/

namespace Ttc.CVGaussianGuardedPolynomialRuntime

open MeasureTheory ProbabilityTheory Metric Set
open Ttc.CVAdaptive
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVGaussianGuardedExpectedVolume
open Ttc.CVGuardedGeneralizedPublic
open Ttc.CVGeneralPolynomialCutoffCapstone
open Ttc.CVGaussianCappedCostedSchedule
open Ttc.CVConcreteAugmentedRetryCutoffBudget
open scoped ENNReal Classical

variable {n : Nat}

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n
abbrev VolumeInput (n : Nat) := Ttc.CVAdaptive.VolumeInput n

/-- The explicit corrected one-run envelope, evaluated using the body's enclosing radius. -/
noncomputable def gaussianCorrectedOneRunEnvelope
    (n : Nat) (a : VolumeInput n) : Real :=
  concreteGeneralizedPublicOneEnvelope n a

theorem gaussianCorrectedOneRunEnvelope_nonneg
    {a : VolumeInput n} (heps : 0 < a.2.1) :
    0 ≤ gaussianCorrectedOneRunEnvelope n a := by
  exact generalizedRetryOneRunEnvelope_nonneg heps

/-- The literal guarded capped-Gaussian oracle has an explicit conservative polynomial
expected-query envelope.  Confidence amplification contributes the factor
`8 * log (1 / p) + 2`; the one-run part is `generalizedRetryOneRunEnvelope` and hence has
the machine-checked `eps ^ (-10)` expansion.

The large argument list is intentional: it is exactly the data of
`guardedExpectedQueryVolumeAlgorithm_gaussianCapped`.  In particular, `hexpected` can be
discharged by `gaussianClosedRaw_expected_le_of_operational`; only `haccuracy` concerns
the estimator rather than runtime accounting. -/
theorem guardedGaussianCapped_expectedBound_le_correctedPolynomial
    (hn : 1 ≤ n)
    (k m : VolumeInput n → Nat)
    (delta sigmaSq shrink : VolumeInput n → Nat → Real)
    (hdelta : ∀ a i, 0 < delta a i) (hshrink : ∀ a i, shrink a i ≠ 0)
    (steps : VolumeInput n → Nat → Nat → Nat)
    (retries : VolumeInput n → Nat → Nat)
    (fallback tail : ∀ a : VolumeInput n, Nat → Measure (ScoreSeed n))
    [∀ a i, IsProbabilityMeasure (fallback a i)]
    [∀ a i, IsProbabilityMeasure (tail a i)]
    (mu0 : ∀ a : VolumeInput n, Measure (ScoreSeed n))
    [∀ a, IsProbabilityMeasure (mu0 a)]
    (est : ∀ a, ClosedAdmissible a →
      (Fin (k a) → Nat → ScoreSeed n) → Real)
    (hest : ∀ a h, Measurable (est a h))
    (hexpected : ∀ a h,
      (∫⁻ omega, gaussianClosedRawCost k m a h omega
        ∂gaussianClosedRawLaw k m delta sigmaSq shrink hdelta hshrink steps
          retries fallback tail mu0 a h) ≤
        ENNReal.ofReal (gaussianCorrectedOneRunEnvelope n a))
    (haccuracy : ∀ a (h : ClosedAdmissible a),
      4 / 5 ≤
        (gaussianClosedRawLaw k m delta sigmaSq shrink hdelta hshrink steps
          retries fallback tail mu0 a h).real
          {omega | gaussianClosedRawValue k est a h omega ∈
            Icc ((1 - a.2.1) * (volume a.1).toReal)
              ((1 + a.2.1) * (volume a.1).toReal)})
    (K : Set (Ttc.Space n)) (eps p : Real)
    (heps : 0 < eps) (hp : 0 < p) (hp1 : p < 1) :
    (guardedExpectedQueryVolumeAlgorithm_gaussianCapped hn
      (gaussianCorrectedOneRunEnvelope n) k m delta sigmaSq shrink hdelta hshrink
      steps retries fallback tail mu0 est hest hexpected haccuracy).expectedBound K eps p ≤
      ENNReal.ofReal
        (generalizedAmplifiedEnvelope
          (gaussianCorrectedOneRunEnvelope n (regularizedInput (K, eps, p))) p) := by
  apply guardedExpectedBound_le_amplified
  · exact gaussianCorrectedOneRunEnvelope_nonneg heps
  · exact hp
  · exact hp1

/-- Exact expansion of the one-run part of the displayed Gaussian runtime bound. -/
theorem gaussianCorrectedOneRunEnvelope_eq_eps_ten
    {a : VolumeInput n} (heps : 0 < a.2.1) :
    gaussianCorrectedOneRunEnvelope n a =
      (generalizedCoordinateCalls n (Ttc.CV.cvRadius a.1) a.2.1 : Real) *
        (8 *
          (explicitRetryPhaseMeanEnvelope continuingReferenceWarm
              (generalizedUniformSteps n (Ttc.CV.cvRadius a.1) a.2.1)
              (generalizedPhaseCount n (Ttc.CV.cvRadius a.1) a.2.1) a.2.1 + 1) *
          (100000 ^ 5 *
            ((generalizedPhaseCount n (Ttc.CV.cvRadius a.1) a.2.1 : Real) + 1) ^ 5) /
          a.2.1 ^ 10) := by
  exact generalizedRetryOneRunEnvelope_eq_eps_ten heps

#print axioms gaussianCorrectedOneRunEnvelope_nonneg
#print axioms guardedGaussianCapped_expectedBound_le_correctedPolynomial
#print axioms gaussianCorrectedOneRunEnvelope_eq_eps_ten

end Ttc.CVGaussianGuardedPolynomialRuntime
