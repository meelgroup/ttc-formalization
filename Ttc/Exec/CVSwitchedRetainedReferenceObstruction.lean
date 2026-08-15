import Ttc.Exec.CVHybridRadiusQSwitchWarm
import Ttc.Exec.CVConcreteAugmentedRetryCutoffBudget

/-!
# The retained accepted-seed cost obstruction

The switched operational construction has two natural retained seed laws.  Resetting
to the current stationary law gives the polynomial `M = 1` reference-cost theorem,
but is not the outgoing seed law of the operational kernel.  Retaining the accepted
seed gives the local phase-TV comparison, but its available reference-cost theorem is
linear in the exact cross-warm factor.

This file records, without asymptotic notation, why the latter substitution cannot
establish a polynomial source bound during a full-body variance step of ratio `3/2`:
the certified multiplier is at least `2 * (6/5)^n`.  Thus an unconditional final
certificate needs either an operational stationary reset, a direct expected-cost
estimate which is not linear in warmness, or a schedule whose full-body rate remains
`O(1/n)`.
-/

set_option autoImplicit false

namespace Ttc.CVSwitchedRetainedReferenceObstruction

open Ttc.CVGaussianAdaptiveAcceptedWarm
open Ttc.CVConcreteAugmentedRetryCutoffBudget
open scoped ENNReal BigOperators

/-- The exact warm multiplier at a variance ratio of `3/2` is geometrically large.
The rational base `6/5` is used to keep the lower bound elementary. -/
theorem geometric_le_acceleratedSeedWarmFactor_three_halves (n : Nat) :
    ENNReal.ofReal (2 * (6 / 5 : Real) ^ n) ≤
      acceleratedSeedWarmFactor n (3 / 2 : Real) := by
  have hsqrt0 : 0 ≤ Real.sqrt (3 / 2 : Real) := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt (3 / 2 : Real)) ^ 2 = 3 / 2 := by
    rw [Real.sq_sqrt]
    norm_num
  have hsqrt : (6 / 5 : Real) ≤ Real.sqrt (3 / 2 : Real) := by
    nlinarith
  unfold acceleratedSeedWarmFactor
  apply ENNReal.ofReal_le_ofReal
  gcongr

/-- The generic retry reference envelope is exactly linear in its warmness input. -/
theorem retryReferenceMeanEnvelope_eq_mul
    (M : Real) (steps : Nat → Nat) (L : Nat) :
    retryReferenceMeanEnvelope M steps L =
      M * retryReferenceMeanEnvelope 1 steps L := by
  unfold retryReferenceMeanEnvelope
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Even one one-step retry at the accepted-seed warm factor has a certified reference
mean envelope at least `20 * (6/5)^n`.  This is the concrete obstruction to absorbing
the accepted-seed retained reference into a dimension-polynomial runtime bound. -/
theorem geometric_le_one_retry_referenceMeanEnvelope (n : Nat) :
    20 * (6 / 5 : Real) ^ n ≤
      retryReferenceMeanEnvelope
        (acceleratedSeedWarmFactor n (3 / 2 : Real)).toReal (fun _ ↦ 1) 1 := by
  have htop : acceleratedSeedWarmFactor n (3 / 2 : Real) ≠ ⊤ := by
    unfold acceleratedSeedWarmFactor
    exact ENNReal.ofReal_ne_top
  have hgeom := geometric_le_acceleratedSeedWarmFactor_three_halves n
  rw [← ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top htop,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * (6 / 5 : Real) ^ n)] at hgeom
  simp only [retryReferenceMeanEnvelope, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.cast_one, zero_add]
  nlinarith

#print axioms geometric_le_acceleratedSeedWarmFactor_three_halves
#print axioms retryReferenceMeanEnvelope_eq_mul
#print axioms geometric_le_one_retry_referenceMeanEnvelope

end Ttc.CVSwitchedRetainedReferenceObstruction
