import Ttc.Exec.CVSourcePolynomialCutoffCapstone
import Ttc.Volume.CVTheorem11

/-!
# From the source cutoff envelope to the public Theorem 1.1 shape

This file performs the final deterministic comparison.  The harmless clipped logarithms
make the comparison valid on the entire pointwise input regime.  The global cutoff's
additive unit is absorbed by the main complexity term, which is at least one when
`1 <= n` and `0 < eps < 1`.
-/

namespace Ttc.CVSourceTheorem11Arithmetic

open MeasureTheory
open Ttc.CVSourcePolynomialCutoffCapstone

/-- The source one-run shape is monotone in the supplied squared radial scale. -/
theorem sourceOneRunQueryEnvelope_le_of_sq_le
    {runtimeConstant R R2 eps : Real} {n : Nat}
    (hconstant : 0 ≤ runtimeConstant) (hR : R ^ 2 ≤ R2)
    (heps : 0 < eps) :
    sourceOneRunQueryEnvelope runtimeConstant n R eps ≤
      runtimeConstant *
        (max (R2 * (n : Real) ^ 2) ((n : Real) ^ 3) / eps ^ 2 *
          sourceLogFactor n ^ 2 * sourceLogFactor (1 / eps) ^ 2 *
            sourceLogFactor ((n : Real) / eps) ^ 2) := by
  unfold sourceOneRunQueryEnvelope
  gcongr

/-- The non-confidence part of the clipped CV complexity is at least one. -/
theorem one_le_cvBaseClipped
    {n : Nat} {R2 eps : Real} (hn : 1 ≤ n) (hR2 : 0 ≤ R2)
    (heps : 0 < eps) (heps1 : eps < 1) :
    1 ≤
      (max (R2 * (n : Real) ^ 2) ((n : Real) ^ 3) / eps ^ 2) *
        max 1 (Real.log n) ^ 2 * max 1 (Real.log (1 / eps)) ^ 2 *
          max 1 (Real.log ((n : Real) / eps)) ^ 2 := by
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  have hn3 : (1 : Real) ≤ (n : Real) ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 1) hnR 3]
  have heps2 : 0 < eps ^ 2 := sq_pos_of_pos heps
  have heps2le : eps ^ 2 ≤ 1 := by nlinarith
  have hratio : 1 ≤ (n : Real) ^ 3 / eps ^ 2 := by
    rw [le_div_iff₀ heps2]
    simpa using heps2le.trans hn3
  have hmax : 1 ≤ max (R2 * (n : Real) ^ 2) ((n : Real) ^ 3) / eps ^ 2 := by
    rw [le_div_iff₀ heps2]
    have hnum : (n : Real) ^ 3 ≤
        max (R2 * (n : Real) ^ 2) ((n : Real) ^ 3) := le_max_right _ _
    nlinarith
  have hlogn : 1 ≤ max 1 (Real.log n) ^ 2 := by
    nlinarith [le_max_left (1 : Real) (Real.log n)]
  have hloge : 1 ≤ max 1 (Real.log (1 / eps)) ^ 2 := by
    nlinarith [le_max_left (1 : Real) (Real.log (1 / eps))]
  have hlogne : 1 ≤ max 1 (Real.log ((n : Real) / eps)) ^ 2 := by
    nlinarith [le_max_left (1 : Real) (Real.log ((n : Real) / eps))]
  have hmax0 : 0 ≤ max (R2 * (n : Real) ^ 2) ((n : Real) ^ 3) / eps ^ 2 :=
    le_trans (by norm_num) hmax
  have hlogn0 : 0 ≤ max 1 (Real.log n) ^ 2 := le_trans (by norm_num) hlogn
  have hloge0 : 0 ≤ max 1 (Real.log (1 / eps)) ^ 2 := le_trans (by norm_num) hloge
  calc
    1 ≤ max (R2 * (n : Real) ^ 2) ((n : Real) ^ 3) / eps ^ 2 := hmax
    _ ≤ (max (R2 * (n : Real) ^ 2) ((n : Real) ^ 3) / eps ^ 2) *
        max 1 (Real.log n) ^ 2 := le_mul_of_one_le_right hmax0 hlogn
    _ ≤ ((max (R2 * (n : Real) ^ 2) ((n : Real) ^ 3) / eps ^ 2) *
        max 1 (Real.log n) ^ 2) * max 1 (Real.log (1 / eps)) ^ 2 :=
      le_mul_of_one_le_right (mul_nonneg hmax0 hlogn0) hloge
    _ ≤ (((max (R2 * (n : Real) ^ 2) ((n : Real) ^ 3) / eps ^ 2) *
        max 1 (Real.log n) ^ 2) * max 1 (Real.log (1 / eps)) ^ 2) *
          max 1 (Real.log ((n : Real) / eps)) ^ 2 :=
      le_mul_of_one_le_right (mul_nonneg (mul_nonneg hmax0 hlogn0) hloge0) hlogne

/-- The amplified source envelope fits the clipped public Theorem 1.1 shape with one
universal numerical loss. -/
theorem sourceAmplifiedQueryEnvelope_le_cvComplexityShapeClipped
    {runtimeConstant R R2 eps p : Real} {n : Nat}
    (hconstant : 0 ≤ runtimeConstant) (hn : 1 ≤ n) (hR2 : 0 ≤ R2)
    (hR : R ^ 2 ≤ R2) (heps : 0 < eps) (heps1 : eps < 1)
    (hp : 0 < p) (hp1 : p < 1) :
    sourceAmplifiedQueryEnvelope runtimeConstant n R eps p ≤
      (200 * (runtimeConstant + 1)) *
        cvComplexityShapeClipped n R2 eps p := by
  let B : Real :=
    (max (R2 * (n : Real) ^ 2) ((n : Real) ^ 3) / eps ^ 2) *
      max 1 (Real.log n) ^ 2 * max 1 (Real.log (1 / eps)) ^ 2 *
        max 1 (Real.log ((n : Real) / eps)) ^ 2
  let L : Real := max 1 (Real.log (1 / p))
  have hB1 : 1 ≤ B := by
    exact one_le_cvBaseClipped hn hR2 heps heps1
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB1
  have hL1 : 1 ≤ L := le_max_left _ _
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL1
  have hlogp : 0 ≤ Real.log (1 / p) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hp]
    simpa using hp1.le
  have hfactor : 8 * Real.log (1 / p) + 2 ≤ 10 * L := by
    have hlogle : Real.log (1 / p) ≤ L := le_max_right _ _
    linarith [hL1]
  have hone : runtimeConstant * B + 1 ≤ (runtimeConstant + 1) * B := by
    nlinarith
  have hrun : sourceOneRunQueryEnvelope runtimeConstant n R eps ≤
      runtimeConstant * B := by
    simpa only [B, sourceLogFactor] using
      sourceOneRunQueryEnvelope_le_of_sq_le hconstant hR heps
  have hsource0 : 0 ≤ sourceOneRunQueryEnvelope runtimeConstant n R eps :=
    sourceOneRunQueryEnvelope_nonneg hconstant n R eps
  calc
    sourceAmplifiedQueryEnvelope runtimeConstant n R eps p =
        (8 * Real.log (1 / p) + 2) *
          (20 * (sourceOneRunQueryEnvelope runtimeConstant n R eps + 1)) := rfl
    _ ≤ (10 * L) *
        (20 * (sourceOneRunQueryEnvelope runtimeConstant n R eps + 1)) := by
      exact mul_le_mul_of_nonneg_right hfactor (by positivity)
    _ ≤ (10 * L) * (20 * (runtimeConstant * B + 1)) := by
      exact mul_le_mul_of_nonneg_left (by gcongr) (by positivity)
    _ ≤ (10 * L) * (20 * ((runtimeConstant + 1) * B)) := by
      exact mul_le_mul_of_nonneg_left (by gcongr) (by positivity)
    _ = (200 * (runtimeConstant + 1)) * (B * L) := by ring
    _ = (200 * (runtimeConstant + 1)) *
        cvComplexityShapeClipped n R2 eps p := by
      unfold cvComplexityShapeClipped
      dsimp only [B, L]

/-- The public oracle built from source one-run certificates satisfies the corrected
Theorem 1.1 expected-query contract whenever its radial parameter is bounded by the
admissible second-moment parameter. -/
theorem sourceExpectedAlgorithm_expectedBound_le_cvComplexityShapeClipped
    {n : Nat} {runtimeConstant : Real}
    (hconstant : 0 ≤ runtimeConstant)
    (radialR : Set (Ttc.Space n) → Real)
    (Omega : Ttc.CVAdaptive.VolumeInput n → Type)
    [∀ a, MeasurableSpace (Omega a)]
    (oneLaw : ∀ a, Measure (Omega a))
    (cost : ∀ a, Omega a → ENNReal)
    (value : ∀ a, Omega a → Real)
    (hcert : SourcePublicOneRunCertificates n runtimeConstant radialR
      Omega oneLaw cost value)
    {K : Set (Ttc.Space n)} {R2 eps p : Real}
    (hn : 1 ≤ n) (heps : 0 < eps) (heps1 : eps < 1)
    (hp : 0 < p) (hp1 : p < 1) (hK : CVAdmissible K R2)
    (hrad : (radialR K) ^ 2 ≤ R2) :
    (expectedQueryVolumeAlgorithmOfSourceOneRunCertificates n runtimeConstant radialR
      Omega oneLaw cost value hcert).expectedBound K eps p ≤
      ENNReal.ofReal
        ((200 * (runtimeConstant + 1)) *
          cvComplexityShapeClipped n R2 eps p) := by
  have hR20 : 0 ≤ R2 := by
    have hm0 : 0 ≤ cvSecondMoment K := by
      unfold cvSecondMoment
      exact integral_nonneg (fun _ ↦ sq_nonneg _)
    exact hm0.trans hK.2.2.2.2
  change sourcePublicExpectedBound runtimeConstant n radialR K eps p ≤ _
  calc
    _ ≤ ENNReal.ofReal
        (sourceAmplifiedQueryEnvelope runtimeConstant n (radialR K) eps p) :=
      sourcePublicExpectedBound_le_polynomial hconstant radialR K hp hp1
    _ ≤ ENNReal.ofReal
        ((200 * (runtimeConstant + 1)) *
          cvComplexityShapeClipped n R2 eps p) := by
      exact ENNReal.ofReal_le_ofReal
        (sourceAmplifiedQueryEnvelope_le_cvComplexityShapeClipped
          hconstant hn hR20 hrad heps heps1 hp hp1)

/-- A dimension-indexed family of source-sharp common-law certificates yields a literal
inhabitant of the honest expected-query form of CV Theorem 1.1.  All cutoff, confidence,
and asymptotic-shape arithmetic is discharged here. -/
noncomputable def cvTheorem11ExpectedImplementationOfSourceFamily
    (runtimeConstant : Real) (hconstant : 0 ≤ runtimeConstant)
    (radialR : ∀ n, Set (Ttc.Space n) → Real)
    (Omega : ∀ n, Ttc.CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ n a, MeasurableSpace (Omega n a)]
    (oneLaw : ∀ n a, Measure (Omega n a))
    (cost : ∀ n a, Omega n a → ENNReal)
    (value : ∀ n a, Omega n a → Real)
    (hcert : ∀ n, SourcePublicOneRunCertificates n runtimeConstant (radialR n)
      (Omega n) (oneLaw n) (cost n) (value n))
    (hrad : ∀ n (K : Set (Ttc.Space n)) R2,
      CVAdmissible K R2 → (radialR n K) ^ 2 ≤ R2) :
    CVTheorem11ExpectedImplementation where
  algorithm n := expectedQueryVolumeAlgorithmOfSourceOneRunCertificates n
    runtimeConstant (radialR n) (Omega n) (oneLaw n) (cost n) (value n) (hcert n)
  runtimeConstant := 200 * (runtimeConstant + 1)
  runtimeConstant_nonneg := by positivity
  expectedBound_le n K eps p R2 hn heps heps1 hp hp1 hK := by
    exact sourceExpectedAlgorithm_expectedBound_le_cvComplexityShapeClipped
      hconstant (radialR n) (Omega n) (oneLaw n) (cost n) (value n) (hcert n)
      hn heps heps1 hp hp1 hK (hrad n K R2 hK)

#print axioms sourceOneRunQueryEnvelope_le_of_sq_le
#print axioms one_le_cvBaseClipped
#print axioms sourceAmplifiedQueryEnvelope_le_cvComplexityShapeClipped
#print axioms sourceExpectedAlgorithm_expectedBound_le_cvComplexityShapeClipped
#print axioms cvTheorem11ExpectedImplementationOfSourceFamily

end Ttc.CVSourceTheorem11Arithmetic
