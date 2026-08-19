import Ttc.Exec.CVShapedExpectedImplementation
import Ttc.Exec.CVSourceDimensionGuard

/-!
# Reference-TV certificate families at an arbitrary input-indexed effective runtime

`Ttc.CVRadialLogEnvelope.expectedQueryVolumeAlgorithmOfRadialLogSourceReferenceTVCertificates`
already builds the outer iid law, the cutoff, the median, the confidence amplification and
the measurability side conditions from nothing but per-input one-run certificates.  Its
only rigidity is that the per-input *effective* runtime constant is hard-wired to
`radialLogEffectiveRuntime runtimeConstant (radialN K) = runtimeConstant * sourceLogFactor (radialN K) ^ 2`.

That hard-wiring is the reason the uniformly slow canonical schedule cannot use it: the
slow schedule's one-run budget exceeds Cousins–Vempala's Theorem 1.1 envelope by an
explicit schedule overhead which is *not* a squared radial logarithm, so no choice of
`radialN` expresses it (see
`Ttc.CVSlowCanonicalRuntimeComparison.slowCanonicalRetainedScalar_le_publicShape`).

This file makes the effective runtime an arbitrary function of the input.  Everything
downstream then follows: the resulting expected-query algorithm meets the shape
`cvConfidenceShape * OV` for any overhead envelope `OV` dominating the effective
constant, and `Ttc.CVShaped.ttc_volume_estimate_of_cvShapedExpectedImplementation`
transports that to TTC.

## Main results

* `EffectiveSourcePublicReferenceTVCertificates` — the seven per-input obligations, with
  the expected-cost one stated at `sourceOneRunQueryBudget (effective a) …`.
* `expectedQueryVolumeAlgorithmOfEffectiveSourceReferenceTVCertificates` — the oracle.
* `cvShapedExpectedImplementationOfEffectiveFamily` — the shape-generic implementation,
  at `shape = cvConfidenceShape * OV` and `runtimeConstant = 400 * (rc + 1)`.
* `EffectiveSourcePublicReferenceTVCertificates.ofRadialLog` — the existing radial-log
  certificate family is the instance at
  `effective a := radialLogEffectiveRuntime runtimeConstant (radialN a.1)`, so this file
  strictly generalises rather than forking.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Ttc.CVEffectiveSourceReference

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.GaussianCooling Arlib.Probability
open Ttc.CVShaped
open Ttc.CVCostedRuntimeCutoff
open Ttc.CVCostedAdjustableOuterMedian
open Ttc.CVExceptionalReferenceGlobalTimeout
open Ttc.CVSourcePolynomialCutoffCapstone
open Ttc.CVSourceReferenceTVCapstone
open Ttc.CVSourceTheorem11Arithmetic
open Ttc.CVRadialLogEnvelope
open scoped ENNReal BigOperators Classical

/-- Per-input reference-TV one-run certificates, with the expected-cost budget taken at an
arbitrary input-indexed effective runtime constant `effective`.

This is `Ttc.CVRadialLogEnvelope.RadialLogSourcePublicReferenceTVCertificates` with
`radialLogEffectiveRuntime runtimeConstant (radialN a.1)` replaced by `effective a`; every
other field is unchanged, including the `1/40` path-TV budget and the `4/5` accuracy
floor. -/
structure EffectiveSourcePublicReferenceTVCertificates
    (n : Nat) (effective : Ttc.CVAdaptive.VolumeInput n → Real)
    (radialR : Set (Ttc.Space n) → Real)
    (Omega : Ttc.CVAdaptive.VolumeInput n → Type)
    [∀ a, MeasurableSpace (Omega a)]
    (actual reference : ∀ a, Measure (Omega a))
    (cost : ∀ a, Omega a → ENNReal)
    (value : ∀ a, Omega a → Real) : Prop where
  actual_probability : ∀ a, IsProbabilityMeasure (actual a)
  reference_probability : ∀ a, IsProbabilityMeasure (reference a)
  cost_measurable : ∀ a, Measurable (cost a)
  value_measurable : ∀ a, Measurable (value a)
  path_tv : ∀ a, TVLe (actual a) (reference a) (ENNReal.ofReal (1 / 40 : Real))
  reference_expected_queries : ∀ a,
    (∫⁻ omega, cost a omega ∂reference a) ≤
      sourceOneRunQueryBudget (effective a) n (radialR a.1) a.2.1
  accuracy : ∀ (K : Set (Ttc.Space n)) (eps p : Real),
    0 < eps → 0 < p → p < 1 → Convex Real K →
    Metric.ball (0 : Ttc.Space n) 1 ⊆ K → volume K ≠ ⊤ →
    4 / 5 ≤ (actual (K, eps, p)).real
      {omega | value (K, eps, p) omega ∈
        Icc ((1 - eps) * (volume K).toReal) ((1 + eps) * (volume K).toReal)}

/-- The existing radial-log family is the instance at the radial-log effective runtime. -/
theorem EffectiveSourcePublicReferenceTVCertificates.ofRadialLog
    {n : Nat} {runtimeConstant : Real}
    {radialR radialN : Set (Ttc.Space n) → Real}
    {Omega : Ttc.CVAdaptive.VolumeInput n → Type}
    [∀ a, MeasurableSpace (Omega a)]
    {actual reference : ∀ a, Measure (Omega a)}
    {cost : ∀ a, Omega a → ENNReal} {value : ∀ a, Omega a → Real}
    (hcert : RadialLogSourcePublicReferenceTVCertificates n runtimeConstant
      radialR radialN Omega actual reference cost value) :
    EffectiveSourcePublicReferenceTVCertificates n
      (fun a ↦ radialLogEffectiveRuntime runtimeConstant (radialN a.1))
      radialR Omega actual reference cost value where
  actual_probability := hcert.actual_probability
  reference_probability := hcert.reference_probability
  cost_measurable := hcert.cost_measurable
  value_measurable := hcert.value_measurable
  path_tv := hcert.path_tv
  reference_expected_queries a := by
    rw [sourceOneRunQueryBudget_effective_eq_radialLog]
    exact hcert.reference_expected_queries a
  accuracy := hcert.accuracy

/-- The public expected-query bound of the constructed oracle, at the input's own
effective runtime constant. -/
noncomputable def effectiveSourceReferencePublicExpectedBound
    {n : Nat} (effective : Ttc.CVAdaptive.VolumeInput n → Real)
    (radialR : Set (Ttc.Space n) → Real)
    (K : Set (Ttc.Space n)) (eps p : Real) : ENNReal :=
  sourceReferencePublicExpectedBound (effective (K, eps, p)) n radialR K eps p

/-- **The oracle.**  Same construction as the radial-log one, with the effective runtime
constant supplied per input rather than computed from a radial normaliser. -/
noncomputable def expectedQueryVolumeAlgorithmOfEffectiveSourceReferenceTVCertificates
    (n : Nat) (effective : Ttc.CVAdaptive.VolumeInput n → Real)
    (radialR : Set (Ttc.Space n) → Real)
    (Omega : Ttc.CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ a, MeasurableSpace (Omega a)]
    (actual reference : ∀ a, Measure (Omega a))
    (cost : ∀ a, Omega a → ENNReal)
    (value : ∀ a, Omega a → Real)
    (hcert : EffectiveSourcePublicReferenceTVCertificates n effective
      radialR Omega actual reference cost value) :
    Ttc.ExpectedQueryVolumeAlgorithm n := by
  let X : Ttc.CVAdaptive.VolumeInput n → Type := fun a =>
    SourceReferenceOuterCoin (outerCutoffReps a.2.2) (Omega a)
  letI : ∀ a, MeasurableSpace (X a) := fun _ => inferInstance
  let nu : ∀ a, Measure (X a) := fun a =>
    sourceOuterLaw (actual a) (outerCutoffReps a.2.2)
  let localEst : ∀ a, X a → Real := fun a =>
    sourceReferenceOuterEstimator (effective a) n (radialR a.1) a.2.1 0
      (cost a) (value a)
  let localCost : ∀ a, X a → ENNReal := fun a =>
    sourceReferenceOuterQueryCost (effective a) n (radialR a.1) a.2.1 (cost a)
  let bound : Ttc.CVAdaptive.VolumeInput n → ENNReal := fun a =>
    effectiveSourceReferencePublicExpectedBound effective radialR a.1 a.2.1 a.2.2
  letI : ∀ a, IsProbabilityMeasure (actual a) := hcert.actual_probability
  letI : ∀ a, IsProbabilityMeasure (reference a) := hcert.reference_probability
  letI : ∀ a, IsProbabilityMeasure (nu a) := by
    intro a
    dsimp only [nu, X, sourceOuterLaw]
    infer_instance
  apply Ttc.ExpectedQueryVolumeAlgorithm.ofInputCostedLaws n X nu localEst localCost
    (bound := bound)
  · intro a
    dsimp only [localEst, X]
    apply measurable_medianSel
    intro i
    exact (measurable_cutoffValue (hcert.cost_measurable a)
      (hcert.value_measurable a)).comp (measurable_pi_apply i)
  · intro a
    dsimp only [localCost, X]
    exact measurable_sourceReferenceOuterQueryCost (hcert.cost_measurable a)
  · intro a
    dsimp only [localCost, nu, X, bound, effectiveSourceReferencePublicExpectedBound]
    exact sourceReferenceOuter_expectedQueryCost_le (actual a)
  · intro K eps p heps hp hp1 hKc hball hfin
    let a : Ttc.CVAdaptive.VolumeInput n := (K, eps, p)
    let cert : SourceReferenceTVOneRunCertificate
        (actual a) (reference a) (cost a) (value a)
        (effective a) n (radialR K) eps
        ((1 - eps) * (volume K).toReal) ((1 + eps) * (volume K).toReal) :=
      { actual_probability := hcert.actual_probability a
        reference_probability := hcert.reference_probability a
        cost_measurable := hcert.cost_measurable a
        value_measurable := hcert.value_measurable a
        path_tv := hcert.path_tv a
        reference_expected_queries := hcert.reference_expected_queries a
        accuracy := hcert.accuracy K eps p heps hp hp1 hKc hball hfin }
    dsimp only [nu, localEst, X]
    exact sourceReference_median_cutoff_accuracy
      (actual a) (reference a) (cost a) (value a) cert hp

/-- The public bound, against the Theorem 1.1 shape scaled by the input's own effective
runtime constant.  This is the shape-free half of the arithmetic; the caller supplies the
overhead envelope. -/
theorem effectiveSourceReferencePublicExpectedBound_le
    {n : Nat} {effective : Ttc.CVAdaptive.VolumeInput n → Real}
    (radialR : Set (Ttc.Space n) → Real) (K : Set (Ttc.Space n))
    {eps p R2 : Real}
    (heff : 0 ≤ effective (K, eps, p))
    (hn : 1 ≤ n) (hR2 : 0 ≤ R2) (hradius : (radialR K) ^ 2 ≤ R2)
    (heps : 0 < eps) (heps1 : eps < 1) (hp : 0 < p) (hp1 : p < 1) :
    effectiveSourceReferencePublicExpectedBound effective radialR K eps p ≤
      ENNReal.ofReal
        ((400 * (effective (K, eps, p) + 1)) * cvConfidenceShape n R2 eps p) := by
  have hbase : effectiveSourceReferencePublicExpectedBound effective radialR K eps p ≤
      2 * ENNReal.ofReal
        (sourceAmplifiedQueryEnvelope (effective (K, eps, p)) n (radialR K) eps p) := by
    unfold effectiveSourceReferencePublicExpectedBound
    rw [Ttc.CVSourceReferenceTheorem11Arithmetic.sourceReferencePublicExpectedBound_eq_two_mul]
    gcongr
    exact sourcePublicExpectedBound_le_polynomial heff radialR K hp hp1
  refine hbase.trans ?_
  have hstep : sourceAmplifiedQueryEnvelope (effective (K, eps, p)) n (radialR K) eps p ≤
      (200 * (effective (K, eps, p) + 1)) * cvConfidenceShape n R2 eps p :=
    Ttc.CVSourceTheorem11Arithmetic.sourceAmplifiedQueryEnvelope_le_confidence
      (R2 := R2) heff hp hp1
  calc
    (2 : ENNReal) * ENNReal.ofReal
        (sourceAmplifiedQueryEnvelope (effective (K, eps, p)) n (radialR K) eps p)
        ≤ 2 * ENNReal.ofReal
          ((200 * (effective (K, eps, p) + 1)) *
            cvConfidenceShape n R2 eps p) := by
          gcongr
    _ = ENNReal.ofReal
          ((400 * (effective (K, eps, p) + 1)) *
            cvConfidenceShape n R2 eps p) := by
          rw [show ((2 : ENNReal)) = ENNReal.ofReal (2 : Real) by
                simp [ENNReal.ofReal_ofNat],
            ← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          ring

/-- **The shape-generic implementation.**

`OV` is the per-input overhead envelope the construction pays over Cousins–Vempala's own
Theorem 1.1 shape.  The radial-log interface is the case `OV = sourceLogFactor (max 1 R2)^2`;
the uniformly slow canonical schedule supplies a larger one.  The resulting shape is the
honest product, with no constant pretending to absorb the overhead. -/
noncomputable def cvShapedExpectedImplementationOfEffectiveFamily
    (Adm : AdmissiblePredicate)
    (hAdm : ∀ (n : Nat) (K : Set (Ttc.Space n)) (R2 : Real),
      Adm n K R2 → CVAdmissible K R2)
    (runtimeConstant : Real) (hconstant : 0 ≤ runtimeConstant)
    (OV : (n : Nat) → Real → Real → Real → Real)
    (hOV : ∀ (n : Nat) (R2 eps p : Real), 1 ≤ OV n R2 eps p)
    (effective : ∀ n, Ttc.CVAdaptive.VolumeInput n → Real)
    (heff0 : ∀ n a, 0 ≤ effective n a)
    (heff : ∀ (n : Nat) (K : Set (Ttc.Space n)) (eps p R2 : Real),
      Adm n K R2 → effective n (K, eps, p) ≤ runtimeConstant * OV n R2 eps p)
    (radialR : ∀ n, Set (Ttc.Space n) → Real)
    (hrad : ∀ n (K : Set (Ttc.Space n)) R2,
      Adm n K R2 → (radialR n K) ^ 2 ≤ R2)
    (Omega : ∀ n, Ttc.CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ n a, MeasurableSpace (Omega n a)]
    (actual reference : ∀ n a, Measure (Omega n a))
    (cost : ∀ n a, Omega n a → ENNReal)
    (value : ∀ n a, Omega n a → Real)
    (hcert : ∀ n, EffectiveSourcePublicReferenceTVCertificates n (effective n)
      (radialR n) (Omega n) (actual n) (reference n) (cost n) (value n)) :
    CVShapedExpectedImplementation Adm
      (fun n R2 eps p ↦ cvConfidenceShape n R2 eps p * OV n R2 eps p) where
  algorithm n :=
    expectedQueryVolumeAlgorithmOfEffectiveSourceReferenceTVCertificates n
      (effective n) (radialR n) (Omega n) (actual n) (reference n) (cost n)
      (value n) (hcert n)
  runtimeConstant := 400 * (runtimeConstant + 1)
  runtimeConstant_nonneg := by positivity
  expectedBound_le n K eps p R2 hn heps heps1 hp hp1 hK := by
    have hR20 : 0 ≤ R2 := by
      have hm0 : 0 ≤ cvSecondMoment K := by
        unfold cvSecondMoment
        exact integral_nonneg (fun _ ↦ sq_nonneg _)
      exact hm0.trans (hAdm n K R2 hK).2.2.2.2
    have hshape0 : 0 ≤ cvConfidenceShape n R2 eps p :=
      cvConfidenceShape_nonneg n R2 eps p
    change effectiveSourceReferencePublicExpectedBound (effective n) (radialR n) K eps p ≤ _
    refine (effectiveSourceReferencePublicExpectedBound_le (radialR n) K
      (heff0 n (K, eps, p)) hn hR20 (hrad n K R2 hK) heps heps1 hp hp1).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have hOV1 : (1 : Real) ≤ OV n R2 eps p := hOV n R2 eps p
    have hOV0 : (0 : Real) ≤ OV n R2 eps p := le_trans (by norm_num) hOV1
    have hkey : effective n (K, eps, p) + 1 ≤ (runtimeConstant + 1) * OV n R2 eps p := by
      have h1 := heff n K eps p R2 hK
      nlinarith [hconstant, hOV1, hOV0]
    calc
      (400 * (effective n (K, eps, p) + 1)) * cvConfidenceShape n R2 eps p
          ≤ (400 * ((runtimeConstant + 1) * OV n R2 eps p)) *
            cvConfidenceShape n R2 eps p := by
            gcongr
      _ = (400 * (runtimeConstant + 1)) *
            (cvConfidenceShape n R2 eps p * OV n R2 eps p) := by ring

/-- **The dimension-guarded implementation.**

`cvShapedExpectedImplementationOfEffectiveFamily` needs certificates at *every* dimension,
but the slow canonical construction is only valid for `21 ≤ n`, and no total choice of law
repairs that: on a degenerate branch the law is a point mass, at which the certificate's
`4/5` accuracy field is not provable — while `CVValidInput` is satisfiable at every `n`,
`n = 0` included (there `Ttc.Space 0` is a point, so the unit ball is everything).

The repair is the one the repository already uses for the un-shaped interface
(`Ttc.CVSourceDimensionGuardTwentyOne.sourceExpectedAlgorithmWithExactBelowTwentyOne`):
below the valid range, route to the semantic exact-volume oracle, whose declared query cost
is identically `0` and therefore under any envelope.  The low-dimensional branch is honest
about what it is — an exact-volume witness, not an operational algorithm — and it is the
reason the TTC capstone carries `21 ≤ n`. -/
noncomputable def cvShapedExpectedImplementationOfEffectiveFamilyTwentyOne
    (Adm : AdmissiblePredicate)
    (hAdm : ∀ (n : Nat) (K : Set (Ttc.Space n)) (R2 : Real),
      Adm n K R2 → CVAdmissible K R2)
    (runtimeConstant : Real) (hconstant : 0 ≤ runtimeConstant)
    (OV : (n : Nat) → Real → Real → Real → Real)
    (hOV : ∀ (n : Nat) (R2 eps p : Real), 1 ≤ OV n R2 eps p)
    (effective : ∀ n, Ttc.CVAdaptive.VolumeInput n → Real)
    (heff0 : ∀ n a, 0 ≤ effective n a)
    (heff : ∀ (n : Nat) (K : Set (Ttc.Space n)) (eps p R2 : Real),
      Adm n K R2 → effective n (K, eps, p) ≤ runtimeConstant * OV n R2 eps p)
    (radialR : ∀ n, Set (Ttc.Space n) → Real)
    (hrad : ∀ n (K : Set (Ttc.Space n)) R2, Adm n K R2 → (radialR n K) ^ 2 ≤ R2)
    (Omega : ∀ n, Ttc.CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ n a, MeasurableSpace (Omega n a)]
    (actual reference : ∀ n a, Measure (Omega n a))
    (cost : ∀ n a, Omega n a → ENNReal)
    (value : ∀ n a, Omega n a → Real)
    (hcert : ∀ n, 21 ≤ n → EffectiveSourcePublicReferenceTVCertificates n (effective n)
      (radialR n) (Omega n) (actual n) (reference n) (cost n) (value n)) :
    CVShapedExpectedImplementation Adm
      (fun n R2 eps p ↦ cvConfidenceShape n R2 eps p * OV n R2 eps p) where
  algorithm n :=
    if h : 21 ≤ n then
      expectedQueryVolumeAlgorithmOfEffectiveSourceReferenceTVCertificates n
        (effective n) (radialR n) (Omega n) (actual n) (reference n) (cost n)
        (value n) (hcert n h)
    else Ttc.ExpectedQueryVolumeAlgorithm.exactExpected n
  runtimeConstant := 400 * (runtimeConstant + 1)
  runtimeConstant_nonneg := by positivity
  expectedBound_le n K eps p R2 hn heps heps1 hp hp1 hK := by
    by_cases h21 : 21 ≤ n
    · have hR20 : 0 ≤ R2 := by
        have hm0 : 0 ≤ cvSecondMoment K := by
          unfold cvSecondMoment
          exact integral_nonneg (fun _ ↦ sq_nonneg _)
        exact hm0.trans (hAdm n K R2 hK).2.2.2.2
      have hshape0 : 0 ≤ cvConfidenceShape n R2 eps p :=
        cvConfidenceShape_nonneg n R2 eps p
      simp only [dif_pos h21]
      change effectiveSourceReferencePublicExpectedBound (effective n) (radialR n) K eps p ≤ _
      refine (effectiveSourceReferencePublicExpectedBound_le (radialR n) K
        (heff0 n (K, eps, p)) hn hR20 (hrad n K R2 hK) heps heps1 hp hp1).trans ?_
      apply ENNReal.ofReal_le_ofReal
      have hOV1 : (1 : Real) ≤ OV n R2 eps p := hOV n R2 eps p
      have hOV0 : (0 : Real) ≤ OV n R2 eps p := le_trans (by norm_num) hOV1
      have hkey : effective n (K, eps, p) + 1 ≤ (runtimeConstant + 1) * OV n R2 eps p := by
        have h1 := heff n K eps p R2 hK
        nlinarith [hconstant, hOV1, hOV0]
      calc
        (400 * (effective n (K, eps, p) + 1)) * cvConfidenceShape n R2 eps p
            ≤ (400 * ((runtimeConstant + 1) * OV n R2 eps p)) *
              cvConfidenceShape n R2 eps p := by gcongr
        _ = (400 * (runtimeConstant + 1)) *
              (cvConfidenceShape n R2 eps p * OV n R2 eps p) := by ring
    · simp [dif_neg h21,
        Ttc.ExpectedQueryVolumeAlgorithm.exactExpected_expectedBound]

#print axioms cvShapedExpectedImplementationOfEffectiveFamilyTwentyOne
#print axioms EffectiveSourcePublicReferenceTVCertificates.ofRadialLog
#print axioms expectedQueryVolumeAlgorithmOfEffectiveSourceReferenceTVCertificates
#print axioms effectiveSourceReferencePublicExpectedBound_le
#print axioms cvShapedExpectedImplementationOfEffectiveFamily

end Ttc.CVEffectiveSourceReference
