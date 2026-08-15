import Ttc.Exec.CVRecursiveActualWarmRuntimeEnvelope
import Ttc.Exec.CVCappedRadialLogExpectedImplementation

/-!
# Public radial-log shape for recursive actual warmth

This is the conservative closed public shape justified by the current operational
accounting.  Relative to the capped radial-log interface it reserves one further
`n log n` cold-prefix factor and the logarithm of a public sampler-call cap required by
the run-global truncation radius.  All factors are clipped below by one.
-/

set_option autoImplicit false

namespace Ttc.CVRecursiveActualWarmPublicShape

open MeasureTheory Set
open Ttc.CVHotRefreshHonestRuntime
open Ttc.CVRadialLogEnvelope
open Ttc.CVSourcePolynomialCutoffCapstone
open Ttc.CVGlobalLogarithmicRadius
open Ttc.CVCappedRadialLogInterface
open scoped ENNReal

/-- A closed call-count parameter usable by the global logarithmic radius. -/
noncomputable def recursiveActualWarmPublicCallCap
    (n : Nat) (R2 eps p : Real) : Real :=
  1 + cvCappedRadialLogComplexityShapeClipped n R2 eps p

/-- Extra factor reserved for the phase-affine recursive warm logarithm and the
run-global truncation radius. -/
noncomputable def recursiveActualWarmPublicOverhead
    (n : Nat) (R2 eps p : Real) : Real :=
  max 1 (n : Real) * sourceLogFactor n *
    sourceLogFactor (20 * recursiveActualWarmPublicCallCap n R2 eps p)

/-- Strongest currently closed source-parameter-only shape for the literal recursive
actual-warm route.  It remains polynomial and differs from the previous capped shape
only by explicit clipped logarithmic/polynomial factors. -/
noncomputable def cvRecursiveActualWarmComplexityShapeClipped
    (n : Nat) (R2 eps p : Real) : Real :=
  cvCappedRadialLogComplexityShapeClipped n R2 eps p *
    recursiveActualWarmPublicOverhead n R2 eps p

theorem one_le_recursiveActualWarmPublicCallCap
    (n : Nat) {R2 eps p : Real} (hR2 : 0 ≤ R2) :
    1 ≤ recursiveActualWarmPublicCallCap n R2 eps p := by
  unfold recursiveActualWarmPublicCallCap
  exact le_add_of_nonneg_right
    (cvCappedRadialLogComplexityShapeClipped_nonneg n hR2)

theorem one_le_recursiveActualWarmPublicOverhead
    (n : Nat) (R2 eps p : Real) :
    1 ≤ recursiveActualWarmPublicOverhead n R2 eps p := by
  have hn : 1 ≤ max 1 (n : Real) := le_max_left _ _
  have hLn : 1 ≤ sourceLogFactor n := le_max_left _ _
  have hLA : 1 ≤ sourceLogFactor
      (20 * recursiveActualWarmPublicCallCap n R2 eps p) := le_max_left _ _
  unfold recursiveActualWarmPublicOverhead
  nlinarith [mul_le_mul hn hLn (by norm_num : (0 : Real) ≤ 1)
    (by positivity : 0 ≤ max 1 (n : Real)),
    mul_le_mul (mul_le_mul hn hLn (by norm_num : (0 : Real) ≤ 1)
      (by positivity : 0 ≤ max 1 (n : Real))) hLA
      (by norm_num : (0 : Real) ≤ 1) (by positivity)]

theorem cvRecursiveActualWarmComplexityShapeClipped_nonneg
    (n : Nat) {R2 eps p : Real} (hR2 : 0 ≤ R2) :
    0 ≤ cvRecursiveActualWarmComplexityShapeClipped n R2 eps p := by
  unfold cvRecursiveActualWarmComplexityShapeClipped
  exact mul_nonneg
    (cvCappedRadialLogComplexityShapeClipped_nonneg n hR2)
    (zero_le_one.trans (one_le_recursiveActualWarmPublicOverhead n R2 eps p))

theorem cvCappedRadialLogComplexityShapeClipped_le_recursive
    (n : Nat) {R2 eps p : Real} (hR2 : 0 ≤ R2) :
    cvCappedRadialLogComplexityShapeClipped n R2 eps p ≤
      cvRecursiveActualWarmComplexityShapeClipped n R2 eps p := by
  unfold cvRecursiveActualWarmComplexityShapeClipped
  exact le_mul_of_one_le_right
    (cvCappedRadialLogComplexityShapeClipped_nonneg n hR2)
    (one_le_recursiveActualWarmPublicOverhead n R2 eps p)

/-- The closed public call cap supplies the hypotheses of the global-radius tail
theorem without a free call-count positivity premise. -/
theorem recursiveActualWarm_globalRadius_tailFits
    {n : Nat} (hn : 1 ≤ n) {R2 eps p : Real} (hR2 : 0 ≤ R2) :
    Arlib.GaussianCooling.AdjustableRadiusTailFits n
      (recursiveActualWarmPublicCallCap n R2 eps p) (1 / 20)
      (globalLogarithmicRadiusQ n
        (recursiveActualWarmPublicCallCap n R2 eps p)) :=
  globalLogarithmicRadiusQ_tailFits hn
    (one_le_recursiveActualWarmPublicCallCap n hR2)

/-- Public expected-query implementation against the conservative recursive-warm
shape. -/
structure CVRecursiveActualWarmExpectedImplementation where
  algorithm : (n : Nat) → Ttc.ExpectedQueryVolumeAlgorithm n
  runtimeConstant : Real
  runtimeConstant_nonneg : 0 ≤ runtimeConstant
  expectedBound_le : ∀ (n : Nat) (K : Set (Ttc.Space n)) (eps p R2 : Real),
    1 ≤ n → 0 < eps → eps < 1 → 0 < p → p < 1 → CVAdmissible K R2 →
    (algorithm n).expectedBound K eps p ≤ ENNReal.ofReal
      (runtimeConstant * cvRecursiveActualWarmComplexityShapeClipped n R2 eps p)

/-- Any implementation satisfying the capped radial-log bound automatically satisfies
the more conservative recursive-warm public interface. -/
noncomputable def CVRecursiveActualWarmExpectedImplementation.ofCapped
    (I : CVCappedRadialLogExpectedImplementation) :
    CVRecursiveActualWarmExpectedImplementation where
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
        (cvCappedRadialLogComplexityShapeClipped_le_recursive n hR20)
        I.runtimeConstant_nonneg))

#print axioms recursiveActualWarm_globalRadius_tailFits
#print axioms CVRecursiveActualWarmExpectedImplementation.ofCapped

end Ttc.CVRecursiveActualWarmPublicShape
