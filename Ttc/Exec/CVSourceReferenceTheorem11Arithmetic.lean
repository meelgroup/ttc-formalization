import Ttc.Exec.CVSourceReferenceTVCapstone
import Ttc.Exec.CVSourceTheorem11Arithmetic
import Ttc.Exec.CVSourceDimensionGuard

/-!
# Reference-path source cutoff in the CV Theorem 1.1 shape

The cost-preserving reference construction uses a `40 * (B + 1)` one-run cutoff,
instead of the `20 * (B + 1)` cutoff used when the operational law itself has mean at
most `B`.  This file records that the sole effect on Theorem 1.1 is a factor two in the
universal runtime constant.
-/

namespace Ttc.CVSourceReferenceTheorem11Arithmetic

open MeasureTheory
open Ttc.CVSourcePolynomialCutoffCapstone
open Ttc.CVSourceReferenceTVCapstone
open Ttc.CVSourceTheorem11Arithmetic
open scoped ENNReal

/-- The reference-TV public cutoff budget is exactly twice the direct-mean budget. -/
theorem sourceReferencePublicExpectedBound_eq_two_mul
    (runtimeConstant : Real) (n : Nat)
    (radialR : Set (Ttc.Space n) → Real) (K : Set (Ttc.Space n))
    (eps p : Real) :
    sourceReferencePublicExpectedBound runtimeConstant n radialR K eps p =
      2 * sourcePublicExpectedBound runtimeConstant n radialR K eps p := by
  unfold sourceReferencePublicExpectedBound sourceReferenceCutoff
    sourcePublicExpectedBound sourceOuterCutoffBudget sourceOneRunCutoff
  ring

/-- The reference-TV oracle retains the source `eps^-2` complexity shape. -/
theorem sourceReferenceExpectedAlgorithm_expectedBound_le_cvComplexityShapeClipped
    {n : Nat} {runtimeConstant : Real}
    (hconstant : 0 ≤ runtimeConstant)
    (radialR : Set (Ttc.Space n) → Real)
    (Omega : Ttc.CVAdaptive.VolumeInput n → Type)
    [∀ a, MeasurableSpace (Omega a)]
    (actual reference : ∀ a, Measure (Omega a))
    (cost : ∀ a, Omega a → ENNReal)
    (value : ∀ a, Omega a → Real)
    (hcert : SourcePublicReferenceTVCertificates n runtimeConstant radialR
      Omega actual reference cost value)
    {K : Set (Ttc.Space n)} {R2 eps p : Real}
    (hn : 1 ≤ n) (heps : 0 < eps) (heps1 : eps < 1)
    (hp : 0 < p) (hp1 : p < 1) (hK : CVAdmissible K R2)
    (hrad : (radialR K) ^ 2 ≤ R2) :
    (expectedQueryVolumeAlgorithmOfSourceReferenceTVCertificates n runtimeConstant radialR
      Omega actual reference cost value hcert).expectedBound K eps p ≤
      ENNReal.ofReal
        ((400 * (runtimeConstant + 1)) *
          cvComplexityShapeClipped n R2 eps p) := by
  have hR20 : 0 ≤ R2 := by
    have hm0 : 0 ≤ cvSecondMoment K := by
      unfold cvSecondMoment
      exact integral_nonneg (fun _ ↦ sq_nonneg _)
    exact hm0.trans hK.2.2.2.2
  change sourceReferencePublicExpectedBound runtimeConstant n radialR K eps p ≤ _
  rw [sourceReferencePublicExpectedBound_eq_two_mul]
  calc
    2 * sourcePublicExpectedBound runtimeConstant n radialR K eps p ≤
        2 * ENNReal.ofReal
          (sourceAmplifiedQueryEnvelope runtimeConstant n (radialR K) eps p) := by
      gcongr
      exact sourcePublicExpectedBound_le_polynomial hconstant radialR K hp hp1
    _ ≤ 2 * ENNReal.ofReal
        ((200 * (runtimeConstant + 1)) *
          cvComplexityShapeClipped n R2 eps p) := by
      gcongr
      exact sourceAmplifiedQueryEnvelope_le_cvComplexityShapeClipped
        hconstant hn hR20 hrad heps heps1 hp hp1
    _ = ENNReal.ofReal
        ((400 * (runtimeConstant + 1)) *
          cvComplexityShapeClipped n R2 eps p) := by
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 2)]
      congr 1
      ring

/-- Reference-TV certificates in every dimension yield the literal honest expected-query
form of CV Theorem 1.1. -/
noncomputable def cvTheorem11ExpectedImplementationOfReferenceTVFamily
    (runtimeConstant : Real) (hconstant : 0 ≤ runtimeConstant)
    (radialR : ∀ n, Set (Ttc.Space n) → Real)
    (Omega : ∀ n, Ttc.CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ n a, MeasurableSpace (Omega n a)]
    (actual reference : ∀ n a, Measure (Omega n a))
    (cost : ∀ n a, Omega n a → ENNReal)
    (value : ∀ n a, Omega n a → Real)
    (hcert : ∀ n, SourcePublicReferenceTVCertificates n runtimeConstant (radialR n)
      (Omega n) (actual n) (reference n) (cost n) (value n))
    (hrad : ∀ n (K : Set (Ttc.Space n)) R2,
      CVAdmissible K R2 → (radialR n K) ^ 2 ≤ R2) :
    CVTheorem11ExpectedImplementation where
  algorithm n := expectedQueryVolumeAlgorithmOfSourceReferenceTVCertificates n
    runtimeConstant (radialR n) (Omega n) (actual n) (reference n) (cost n) (value n)
      (hcert n)
  runtimeConstant := 400 * (runtimeConstant + 1)
  runtimeConstant_nonneg := by positivity
  expectedBound_le n K eps p R2 hn heps heps1 hp hp1 hK := by
    exact sourceReferenceExpectedAlgorithm_expectedBound_le_cvComplexityShapeClipped
      hconstant (radialR n) (Omega n) (actual n) (reference n) (cost n) (value n)
      (hcert n) hn heps heps1 hp hp1 hK (hrad n K R2 hK)

/-- Use reference-TV source executions only in the Gaussian range `n ≥ 2`, and the
zero-cost exact semantic witness in dimensions zero and one. -/
noncomputable def referenceExpectedAlgorithmWithExactLowDimensions
    (runtimeConstant : Real)
    (radialR : ∀ n, Set (Ttc.Space n) → Real)
    (Omega : ∀ n, Ttc.CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ n a, MeasurableSpace (Omega n a)]
    (actual reference : ∀ n a, Measure (Omega n a))
    (cost : ∀ n a, Omega n a → ENNReal)
    (value : ∀ n a, Omega n a → Real)
    (hcert : ∀ n, 2 ≤ n → SourcePublicReferenceTVCertificates n runtimeConstant
      (radialR n) (Omega n) (actual n) (reference n) (cost n) (value n))
    (n : Nat) : Ttc.ExpectedQueryVolumeAlgorithm n :=
  if hn : 2 ≤ n then
    expectedQueryVolumeAlgorithmOfSourceReferenceTVCertificates n runtimeConstant
      (radialR n) (Omega n) (actual n) (reference n) (cost n) (value n) (hcert n hn)
  else
    Ttc.ExpectedQueryVolumeAlgorithm.exactExpected n

/-- Literal expected-query CV Theorem 1.1 from reference-TV certificates needed only in
the substantive range `n ≥ 2`.  The universal runtime constant is twice the direct-mean
source cutoff constant, and the dependence on accuracy remains `eps^-2`. -/
noncomputable def cvTheorem11ExpectedImplementationOfReferenceTVFamilyDimTwo
    (runtimeConstant : Real) (hconstant : 0 ≤ runtimeConstant)
    (radialR : ∀ n, Set (Ttc.Space n) → Real)
    (Omega : ∀ n, Ttc.CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ n a, MeasurableSpace (Omega n a)]
    (actual reference : ∀ n a, Measure (Omega n a))
    (cost : ∀ n a, Omega n a → ENNReal)
    (value : ∀ n a, Omega n a → Real)
    (hcert : ∀ n, 2 ≤ n → SourcePublicReferenceTVCertificates n runtimeConstant
      (radialR n) (Omega n) (actual n) (reference n) (cost n) (value n))
    (hrad : ∀ n, 2 ≤ n → ∀ (K : Set (Ttc.Space n)) R2,
      CVAdmissible K R2 → (radialR n K) ^ 2 ≤ R2) :
    CVTheorem11ExpectedImplementation where
  algorithm n := referenceExpectedAlgorithmWithExactLowDimensions runtimeConstant
    radialR Omega actual reference cost value hcert n
  runtimeConstant := 400 * (runtimeConstant + 1)
  runtimeConstant_nonneg := by positivity
  expectedBound_le n K eps p R2 hn heps heps1 hp hp1 hK := by
    by_cases hn2 : 2 ≤ n
    · rw [referenceExpectedAlgorithmWithExactLowDimensions, dif_pos hn2]
      exact sourceReferenceExpectedAlgorithm_expectedBound_le_cvComplexityShapeClipped
        hconstant (radialR n) (Omega n) (actual n) (reference n) (cost n) (value n)
        (hcert n hn2) hn heps heps1 hp hp1 hK (hrad n hn2 K R2 hK)
    · rw [referenceExpectedAlgorithmWithExactLowDimensions, dif_neg hn2]
      simp

#print axioms sourceReferencePublicExpectedBound_eq_two_mul
#print axioms sourceReferenceExpectedAlgorithm_expectedBound_le_cvComplexityShapeClipped
#print axioms cvTheorem11ExpectedImplementationOfReferenceTVFamily
#print axioms cvTheorem11ExpectedImplementationOfReferenceTVFamilyDimTwo

end Ttc.CVSourceReferenceTheorem11Arithmetic
