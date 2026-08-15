import Ttc.Exec.CVGlobalLogarithmicRadius
import Ttc.Exec.CVAdaptiveRadiusQPrimitives

/-! Terminal equality for the run-global logarithmic truncation radius. -/

set_option autoImplicit false

namespace Ttc.CVGlobalRadiusTerminalBody

open Metric Set
open Ttc.CVGlobalLogarithmicRadius Ttc.CVAdaptiveRadiusQPrimitives
open Ttc.CVHybridSchedule

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- Positivity of the hybrid phase rate is automatic from the source parameters;
it need not remain a premise of the final operational certificate. -/
theorem hybridPhaseRate_nonneg
    {n : Nat} (hn : 1 ≤ n) {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    (i : Nat) : 0 ≤ phaseRate n N s0 i := by
  rw [phaseRate]
  split
  · have hnR : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
    positivity
  · exact (Arlib.GaussianCooling.Chunked.adaptiveChunkRate_pos hN
      (coldEnd_pos hn hs0) _).le

/-- Any phase satisfying the old radius-four interior condition automatically
satisfies the selected global-radius condition. -/
theorem one_le_globalLogarithmicRadius_mul_sqrt_of_four
    {n : Nat} (hn : 1 ≤ n) {A s : Real} (hA : 1 ≤ A)
    (hfour : 1 ≤ 4 * Real.sqrt s * Real.sqrt n) :
    1 ≤ globalLogarithmicRadiusQ n A * Real.sqrt s * Real.sqrt n := by
  exact hfour.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (four_le_globalLogarithmicRadiusQ hn hA) (Real.sqrt_nonneg s))
    (Real.sqrt_nonneg n))

/-- The original radius-four terminal certificate remains sufficient for the larger
run-global logarithmic radius. -/
theorem radiusQBody_globalLogarithmic_eq_of_outer_radius
    {n : Nat} (hn : 1 ≤ n) {A R s : Real} (hA : 1 ≤ A)
    {K : Set (State n)} (houter : K ⊆ closedBall 0 R)
    (hR : R ≤ 4 * Real.sqrt s * Real.sqrt n) :
    radiusQBody (globalLogarithmicRadiusQ n A) K s = K := by
  apply radiusQBody_eq_of_outer_radius houter
  exact hR.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (four_le_globalLogarithmicRadiusQ hn hA) (Real.sqrt_nonneg s))
    (Real.sqrt_nonneg n))

#print axioms radiusQBody_globalLogarithmic_eq_of_outer_radius
#print axioms one_le_globalLogarithmicRadius_mul_sqrt_of_four
#print axioms hybridPhaseRate_nonneg

end Ttc.CVGlobalRadiusTerminalBody
