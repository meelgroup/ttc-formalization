import Ttc.Exec.CVSourceDimensionGuard

/-! Public dimension dispatch for operational certificates valid from dimension 21. -/

set_option autoImplicit false

namespace Ttc

open MeasureTheory
open scoped ENNReal

namespace CVSourceDimensionGuardTwentyOne

open Ttc.CVSourcePolynomialCutoffCapstone
open Ttc.CVSourceTheorem11Arithmetic

/-- Use the genuine source certificate in the speedy-conductance range and the
pre-existing exact semantic expected-query witness in the finitely many lower
dimensions. -/
noncomputable def sourceExpectedAlgorithmWithExactBelowTwentyOne
    (runtimeConstant : Real)
    (radialR : ∀ n, Set (Ttc.Space n) → Real)
    (Omega : ∀ n, Ttc.CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ n a, MeasurableSpace (Omega n a)]
    (oneLaw : ∀ n a, Measure (Omega n a))
    (cost : ∀ n a, Omega n a → ENNReal)
    (value : ∀ n a, Omega n a → Real)
    (hcert : ∀ n, 21 ≤ n → SourcePublicOneRunCertificates n runtimeConstant
      (radialR n) (Omega n) (oneLaw n) (cost n) (value n))
    (n : Nat) : ExpectedQueryVolumeAlgorithm n :=
  if hn : 21 ≤ n then
    expectedQueryVolumeAlgorithmOfSourceOneRunCertificates n runtimeConstant
      (radialR n) (Omega n) (oneLaw n) (cost n) (value n) (hcert n hn)
  else
    ExpectedQueryVolumeAlgorithm.exactExpected n

/-- A source-law family only required in its analytically valid range gives an
unconditional expected-query Theorem 1.1 interface.  The lower-dimensional branch
has recorded query cost zero. -/
noncomputable def cvTheorem11ExpectedImplementationOfSourceFamilyTwentyOne
    (runtimeConstant : Real) (hconstant : 0 ≤ runtimeConstant)
    (radialR : ∀ n, Set (Ttc.Space n) → Real)
    (Omega : ∀ n, Ttc.CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ n a, MeasurableSpace (Omega n a)]
    (oneLaw : ∀ n a, Measure (Omega n a))
    (cost : ∀ n a, Omega n a → ENNReal)
    (value : ∀ n a, Omega n a → Real)
    (hcert : ∀ n, 21 ≤ n → SourcePublicOneRunCertificates n runtimeConstant
      (radialR n) (Omega n) (oneLaw n) (cost n) (value n))
    (hrad : ∀ n, 21 ≤ n → ∀ (K : Set (Ttc.Space n)) R2,
      CVAdmissible K R2 → (radialR n K) ^ 2 ≤ R2) :
    CVTheorem11ExpectedImplementation where
  algorithm n := sourceExpectedAlgorithmWithExactBelowTwentyOne runtimeConstant
    radialR Omega oneLaw cost value hcert n
  runtimeConstant := 200 * (runtimeConstant + 1)
  runtimeConstant_nonneg := by positivity
  expectedBound_le n K eps p R2 hn heps heps1 hp hp1 hK := by
    by_cases hn21 : 21 ≤ n
    · rw [sourceExpectedAlgorithmWithExactBelowTwentyOne, dif_pos hn21]
      exact sourceExpectedAlgorithm_expectedBound_le_cvComplexityShapeClipped
        hconstant (radialR n) (Omega n) (oneLaw n) (cost n) (value n)
          (hcert n hn21) hn heps heps1 hp hp1 hK (hrad n hn21 K R2 hK)
    · rw [sourceExpectedAlgorithmWithExactBelowTwentyOne, dif_neg hn21]
      simp

#print axioms sourceExpectedAlgorithmWithExactBelowTwentyOne
#print axioms cvTheorem11ExpectedImplementationOfSourceFamilyTwentyOne

end CVSourceDimensionGuardTwentyOne

end Ttc
