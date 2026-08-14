import Ttc.Exec.CVHotRefreshHonestRuntime

/-! Public expected-query interface for the honestly capped radial-log CV runtime. -/

set_option autoImplicit false

namespace Ttc.CVCappedRadialLogInterface

open MeasureTheory Set
open Ttc.CVHotRefreshHonestRuntime
open Ttc.CVRadialLogEnvelope
open scoped ENNReal

/-- Expected-query CV implementation with the operationally honest capped radial-log
shape. -/
structure CVCappedRadialLogExpectedImplementation where
  algorithm : (n : Nat) → Ttc.ExpectedQueryVolumeAlgorithm n
  runtimeConstant : Real
  runtimeConstant_nonneg : 0 ≤ runtimeConstant
  expectedBound_le : ∀ (n : Nat) (K : Set (Ttc.Space n)) (eps p R2 : Real),
    1 ≤ n → 0 < eps → eps < 1 → 0 < p → p < 1 → CVAdmissible K R2 →
    (algorithm n).expectedBound K eps p ≤ ENNReal.ofReal
      (runtimeConstant * cvCappedRadialLogComplexityShapeClipped n R2 eps p)

/-- A constructor for algorithms proved directly against the corrected public shape. -/
noncomputable def CVCappedRadialLogExpectedImplementation.ofExpectedBound
    (algorithm : (n : Nat) → Ttc.ExpectedQueryVolumeAlgorithm n)
    (runtimeConstant : Real) (hconstant : 0 ≤ runtimeConstant)
    (hbound : ∀ (n : Nat) (K : Set (Ttc.Space n)) (eps p R2 : Real),
      1 ≤ n → 0 < eps → eps < 1 → 0 < p → p < 1 → CVAdmissible K R2 →
      (algorithm n).expectedBound K eps p ≤ ENNReal.ofReal
        (runtimeConstant * cvCappedRadialLogComplexityShapeClipped n R2 eps p)) :
    CVCappedRadialLogExpectedImplementation where
  algorithm := algorithm
  runtimeConstant := runtimeConstant
  runtimeConstant_nonneg := hconstant
  expectedBound_le := hbound

/-- Any implementation satisfying the earlier, stronger radial-log bound also satisfies
the honestly capped interface. -/
noncomputable def CVCappedRadialLogExpectedImplementation.ofRadial
    (I : CVRadialLogExpectedImplementation) :
    CVCappedRadialLogExpectedImplementation where
  algorithm := I.algorithm
  runtimeConstant := I.runtimeConstant
  runtimeConstant_nonneg := I.runtimeConstant_nonneg
  expectedBound_le n K eps p R2 hn heps heps1 hp hp1 hK := by
    have hR20 : 0 ≤ R2 := by
      have hm0 : 0 ≤ cvSecondMoment K := by
        unfold cvSecondMoment
        exact integral_nonneg (fun _ ↦ sq_nonneg _)
      exact hm0.trans hK.2.2.2.2
    exact (I.expectedBound_le n K eps p R2 hn heps heps1 hp hp1 hK).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (cvRadialLogComplexityShapeClipped_le_capped n hR20)
        I.runtimeConstant_nonneg))

/-- Reference-TV constructor for any family satisfying the existing stronger stopped
radial budget. -/
noncomputable def cvCappedRadialLogExpectedImplementationOfReferenceTVFamily
    (runtimeConstant : Real) (hconstant : 0 ≤ runtimeConstant)
    (radialR radialN : ∀ n, Set (Ttc.Space n) → Real)
    (Omega : ∀ n, Ttc.CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ n a, MeasurableSpace (Omega n a)]
    (actual reference : ∀ n a, Measure (Omega n a))
    (cost : ∀ n a, Omega n a → ENNReal)
    (value : ∀ n a, Omega n a → Real)
    (hcert : ∀ n, RadialLogSourcePublicReferenceTVCertificates n runtimeConstant
      (radialR n) (radialN n) (Omega n) (actual n) (reference n)
        (cost n) (value n))
    (hrad : ∀ n (K : Set (Ttc.Space n)) R2,
      CVAdmissible K R2 → (radialR n K) ^ 2 ≤ R2)
    (hNpos : ∀ n (K : Set (Ttc.Space n)), 0 < radialN n K)
    (hNle : ∀ n (K : Set (Ttc.Space n)) R2,
      CVAdmissible K R2 → radialN n K ≤ max 1 R2) :
    CVCappedRadialLogExpectedImplementation :=
  CVCappedRadialLogExpectedImplementation.ofRadial
    (cvRadialLogExpectedImplementationOfReferenceTVFamily runtimeConstant hconstant
      radialR radialN Omega actual reference cost value hcert hrad hNpos hNle)

#print axioms CVCappedRadialLogExpectedImplementation.ofExpectedBound
#print axioms CVCappedRadialLogExpectedImplementation.ofRadial
#print axioms cvCappedRadialLogExpectedImplementationOfReferenceTVFamily

end Ttc.CVCappedRadialLogInterface
