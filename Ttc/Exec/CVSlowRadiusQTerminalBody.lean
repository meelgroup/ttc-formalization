import Ttc.Exec.CVSlowFullBodySourceSchedule
import Ttc.Exec.CVAdaptiveRadiusQPrimitives

/-! Terminal full-body equality for the uniformly slow selected-radius schedule. -/

set_option autoImplicit false

namespace Ttc.CVSlowRadiusQTerminalBody

open Metric Set
open Ttc.CVSlowFullBodySourceSchedule Ttc.CVAdaptiveRadiusQPrimitives

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- If the target variance dominates the squared outer radius, the terminal slow
phase's selected-radius body is exactly `K`. -/
theorem slowRadiusQBody_terminal_eq
    {n : Nat} (hn : 1 ≤ n) {q N s0 R : Real} (hq : 4 ≤ q)
    (hN : 0 < N) (hs0 : 0 < s0) (hsN : s0 ≤ N)
    (hR0 : 0 ≤ R) (hR2 : R ^ 2 ≤ N)
    {K : Set (State n)} (houter : K ⊆ closedBall 0 R) :
    radiusQBody q K
      (slowSourceSigmaSq n s0 (slowSourcePhases n N s0)) = K := by
  apply radiusQBody_eq_of_outer_radius houter
  have htarget := target_le_slowSourceSigmaSq_terminal hn hN hs0 hsN
  have hRsqrtN : R ≤ Real.sqrt N :=
    (Real.le_sqrt hR0 hN.le).2 hR2
  have hsqrtTarget : Real.sqrt N ≤
      Real.sqrt (slowSourceSigmaSq n s0 (slowSourcePhases n N s0)) :=
    Real.sqrt_le_sqrt htarget
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  have hsqrtNdim : (1 : Real) ≤ Real.sqrt n := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  calc
    R ≤ Real.sqrt N := hRsqrtN
    _ ≤ Real.sqrt (slowSourceSigmaSq n s0 (slowSourcePhases n N s0)) := hsqrtTarget
    _ = 1 * Real.sqrt (slowSourceSigmaSq n s0 (slowSourcePhases n N s0)) * 1 := by ring
    _ ≤ q * Real.sqrt (slowSourceSigmaSq n s0 (slowSourcePhases n N s0)) *
        Real.sqrt n := by gcongr <;> linarith

#print axioms slowRadiusQBody_terminal_eq

end Ttc.CVSlowRadiusQTerminalBody
