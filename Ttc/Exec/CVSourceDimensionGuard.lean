import Ttc.Exec.CVSourceTheorem11Arithmetic
import Ttc.Volume.Bridge

/-!
# Closing the low-dimensional branch of the source CV certificate

The concrete Gaussian cooling estimates are naturally stated for `2 ≤ n`, whereas
the public Cousins--Vempala contract quantifies over every dimension and only assumes
`1 ≤ n` at use sites.  This file isolates that bookkeeping issue.

`exactExpected` is the expected-cost lift of the pre-existing semantic exact-volume
witness `VolumeAlgorithm.exact`; its query counter and expected bound are both zero.
It is deliberately used only below dimension two.  Thus the dispatcher lets a genuine
source-law implementation handle every substantive (`n ≥ 2`) branch without asking it
to prove a false dimension guard.

As with `VolumeAlgorithm.exact`, the low-dimensional branch is a semantic interface
witness, not executable membership-oracle code for recovering interval endpoints.
-/

namespace Ttc

open MeasureTheory
open scoped ENNReal

namespace ExpectedQueryVolumeAlgorithm

/-- Expected-query lift of the exact semantic volume witness, with zero recorded
membership queries. -/
noncomputable def exactExpected (n : Nat) : ExpectedQueryVolumeAlgorithm n where
  toVolumeAlgorithm := VolumeAlgorithm.exact n
  queryCost _ _ _ _ := 0
  queryCost_meas := fun _ _ _ ↦ measurable_const
  expectedBound _ _ _ := 0
  expectedQueryCost_le := by simp

@[simp] theorem exactExpected_expectedBound (n : Nat)
    (K : Set (Space n)) (eps p : Real) :
    (exactExpected n).expectedBound K eps p = 0 := rfl

@[simp] theorem exactExpected_queryCost (n : Nat)
    (K : Set (Space n)) (eps p : Real) (omega : (exactExpected n).Ω) :
    (exactExpected n).queryCost K eps p omega = 0 := rfl

@[simp] theorem exactExpected_expectedQueryCost (n : Nat)
    (K : Set (Space n)) (eps p : Real) :
    (∫⁻ omega, (exactExpected n).queryCost K eps p omega
      ∂(exactExpected n).μ) = 0 := by
  simp

end ExpectedQueryVolumeAlgorithm

namespace CVSourceDimensionGuard

open Ttc.CVSourcePolynomialCutoffCapstone
open Ttc.CVSourceTheorem11Arithmetic

/-- Use the source implementation in dimensions at least two and the zero-cost exact
semantic witness in dimensions zero and one. -/
noncomputable def sourceExpectedAlgorithmWithExactLowDimensions
    (runtimeConstant : Real)
    (radialR : ∀ n, Set (Ttc.Space n) → Real)
    (Omega : ∀ n, Ttc.CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ n a, MeasurableSpace (Omega n a)]
    (oneLaw : ∀ n a, Measure (Omega n a))
    (cost : ∀ n a, Omega n a → ENNReal)
    (value : ∀ n a, Omega n a → Real)
    (hcert : ∀ n, 2 ≤ n → SourcePublicOneRunCertificates n runtimeConstant
      (radialR n) (Omega n) (oneLaw n) (cost n) (value n))
    (n : Nat) : ExpectedQueryVolumeAlgorithm n :=
  if hn : 2 ≤ n then
    expectedQueryVolumeAlgorithmOfSourceOneRunCertificates n runtimeConstant
      (radialR n) (Omega n) (oneLaw n) (cost n) (value n) (hcert n hn)
  else
    ExpectedQueryVolumeAlgorithm.exactExpected n

/-- A source-law family needed only in its valid range `n ≥ 2` gives a literal
`CVTheorem11ExpectedImplementation`.  For the only positive excluded dimension,
`n = 1`, the expected query bound is exactly zero. -/
noncomputable def cvTheorem11ExpectedImplementationOfSourceFamilyDimTwo
    (runtimeConstant : Real) (hconstant : 0 ≤ runtimeConstant)
    (radialR : ∀ n, Set (Ttc.Space n) → Real)
    (Omega : ∀ n, Ttc.CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ n a, MeasurableSpace (Omega n a)]
    (oneLaw : ∀ n a, Measure (Omega n a))
    (cost : ∀ n a, Omega n a → ENNReal)
    (value : ∀ n a, Omega n a → Real)
    (hcert : ∀ n, 2 ≤ n → SourcePublicOneRunCertificates n runtimeConstant
      (radialR n) (Omega n) (oneLaw n) (cost n) (value n))
    (hrad : ∀ n, 2 ≤ n → ∀ (K : Set (Ttc.Space n)) R2,
      CVAdmissible K R2 → (radialR n K) ^ 2 ≤ R2) :
    CVTheorem11ExpectedImplementation where
  algorithm n := sourceExpectedAlgorithmWithExactLowDimensions runtimeConstant
    radialR Omega oneLaw cost value hcert n
  runtimeConstant := 200 * (runtimeConstant + 1)
  runtimeConstant_nonneg := by positivity
  expectedBound_le n K eps p R2 hn heps heps1 hp hp1 hK := by
    by_cases hn2 : 2 ≤ n
    · rw [sourceExpectedAlgorithmWithExactLowDimensions, dif_pos hn2]
      exact sourceExpectedAlgorithm_expectedBound_le_cvComplexityShapeClipped
        hconstant (radialR n) (Omega n) (oneLaw n) (cost n) (value n)
          (hcert n hn2) hn heps heps1 hp hp1 hK (hrad n hn2 K R2 hK)
    · rw [sourceExpectedAlgorithmWithExactLowDimensions, dif_neg hn2]
      simp

#print axioms ExpectedQueryVolumeAlgorithm.exactExpected
#print axioms cvTheorem11ExpectedImplementationOfSourceFamilyDimTwo

end CVSourceDimensionGuard

end Ttc
