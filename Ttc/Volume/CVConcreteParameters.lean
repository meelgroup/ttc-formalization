/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.AdaptiveTerminalWarmLaw

/-!
# Computed parameters for the concrete adaptive CV sampler

The mixing theorem asks for a natural deadline above an explicit real expression.  Taking
the nonnegative ceiling plus one makes that premise definitional data rather than a caller
hypothesis.
-/

namespace Ttc.CVAdaptive

open Arlib.GaussianCooling.Chunked

/-- The exact real deadline appearing in the radius-four adaptive phase theorem. -/
noncomputable def adaptiveTerminalDeadline (n : Nat) (N s0 epsMix : Real) (i : Nat) : Real :=
  4 * 640 ^ 2 * adaptiveTerminalSigma N s0 i ^ 2 * (n : Real) *
      (Real.log (adaptiveRestartWarmConst n i) + 2 * Real.log (1 / epsMix)) /
        (adaptiveTerminalDelta (n := n) N s0 i * Real.log 2) ^ 2 + 1

/-- A concrete integral number of lazy speedy steps for every phase. -/
noncomputable def adaptiveTerminalSteps (n : Nat) (N s0 epsMix : Real)
    (m : Nat) : Fin (m + 1) -> Nat :=
  fun i => ⌈adaptiveTerminalDeadline n N s0 epsMix i⌉₊ + 1

theorem adaptiveTerminalDeadline_le_steps (n : Nat) (N s0 epsMix : Real)
    (m : Nat) (i : Fin (m + 1)) :
    adaptiveTerminalDeadline n N s0 epsMix i ≤
      (adaptiveTerminalSteps n N s0 epsMix m i : Real) := by
  have hceil := Nat.le_ceil (adaptiveTerminalDeadline n N s0 epsMix i)
  rw [adaptiveTerminalSteps]
  push_cast
  linarith

/-- The computed deadline discharges the warm-coordinate premise verbatim. -/
theorem adaptiveTerminalSteps_spec (n : Nat) (N s0 epsMix : Real)
    (m : Nat) :
    ∀ i : Fin (m + 1),
      ¬ 4 * (n : Real) * adaptiveSigmaSq N s0 i ≤ 1 ->
      4 * 640 ^ 2 * adaptiveTerminalSigma N s0 i ^ 2 * (n : Real) *
          (Real.log (adaptiveRestartWarmConst n i) + 2 * Real.log (1 / epsMix)) /
            (adaptiveTerminalDelta (n := n) N s0 i * Real.log 2) ^ 2 + 1
        ≤ (adaptiveTerminalSteps n N s0 epsMix m i : Real) := by
  intro i _
  exact adaptiveTerminalDeadline_le_steps n N s0 epsMix m i

end Ttc.CVAdaptive

#print axioms Ttc.CVAdaptive.adaptiveTerminalDeadline_le_steps
#print axioms Ttc.CVAdaptive.adaptiveTerminalSteps_spec
