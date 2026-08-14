import Ttc.Exec.CVCostedAdjustablePublicEstimator

set_option autoImplicit false

/-!
# Cost audit for the independently restarted CV estimator

The independently packed CV implementation is an honest operational membership-query
law, and its exact-law coupling/accuracy plumbing is complete.  Its presently proved
query envelope is not the source-sharp polynomial envelope, however: every warm
coordinate is restarted from the fixed cold-ball law.  The certified warmness of that
restart at phase `i` is exactly `2^(1+n*i)`, and the charged warm-coordinate envelope
multiplies by this constant rather than by its logarithm.

The lemmas below make that obstruction literal.  They do not claim a lower bound on the
true running time of every possible implementation.  They show that the existing
`terminalPhaseQueryBound` cannot be promoted to the CV Theorem 1.1 polynomial budget by
arithmetic simplification: on every warm phase with at least one declared mixing step it
already contains the exponential restart factor.
-/

namespace Ttc.CVIndependentRestartCostAudit

open Arlib.GaussianCooling.Chunked
open Ttc.CostedAdaptiveTerminalPhaseAssembly
open scoped ENNReal

/-- The independently restarted warmness certificate is literally exponential in the
dimension times the flattened phase index. -/
theorem adaptiveRestartWarmConst_eq_pow (n i : Nat) :
    adaptiveRestartWarmConst n i = (2 : Real) ^ (1 + n * i) := rfl

/-- The same identity in the query-count codomain. -/
theorem ofReal_adaptiveRestartWarmConst_eq_pow (n i : Nat) :
    ENNReal.ofReal (adaptiveRestartWarmConst n i) =
      (2 : ENNReal) ^ (1 + n * i) := by
  rw [adaptiveRestartWarmConst]
  rw [ENNReal.ofReal_pow (by norm_num : (0 : Real) ≤ 2)]
  norm_num

/-- On a warm coordinate, the existing terminal query envelope exposes the restart
warmness as a multiplicative factor, not only through `log M` in the mixing deadline. -/
theorem terminalPhaseQueryBound_warm
    {n m : Nat} {q N s0 eps : Real}
    (M : Fin (m + 1) → ENNReal) (i : Fin (m + 1))
    (hi : ¬ 4 * (n : Real) *
      Arlib.GaussianCooling.Chunked.adaptiveSigmaSq N s0 i ≤ 1) :
    terminalPhaseQueryBound (n := n) (m := m) q N s0 eps M i =
      160 * ((Ttc.CVAdaptive.adaptiveTerminalStepsQ (n := n) (m := m)
        q N s0 eps i : ENNReal) *
        M i) := by
  unfold terminalPhaseQueryBound
  rw [if_neg hi]

/-- Consequently one nontrivial independently restarted warm coordinate is charged at
least `160 * 2^(1+n*i)` by the current operational theorem. -/
theorem exponential_restart_factor_le_terminalPhaseQueryBound
    {n m : Nat} {q N s0 eps : Real} (i : Fin (m + 1))
    (hi : ¬ 4 * (n : Real) *
      Arlib.GaussianCooling.Chunked.adaptiveSigmaSq N s0 i ≤ 1)
    (hstep : 1 ≤ Ttc.CVAdaptive.adaptiveTerminalStepsQ
      (n := n) (m := m) q N s0 eps i) :
    160 * (2 : ENNReal) ^ (1 + n * (i : Nat)) ≤
      terminalPhaseQueryBound (n := n) (m := m) q N s0 eps
        (fun j => ENNReal.ofReal (adaptiveRestartWarmConst n j)) i := by
  rw [terminalPhaseQueryBound_warm _ i hi,
    ofReal_adaptiveRestartWarmConst_eq_pow]
  have hstepE : (1 : ENNReal) ≤
      (Ttc.CVAdaptive.adaptiveTerminalStepsQ
        (n := n) (m := m) q N s0 eps i : ENNReal) := by
    exact_mod_cast hstep
  calc
    160 * (2 : ENNReal) ^ (1 + n * (i : Nat)) =
        160 * (1 * (2 : ENNReal) ^ (1 + n * (i : Nat))) := by simp
    _ ≤ 160 *
        ((Ttc.CVAdaptive.adaptiveTerminalStepsQ
          (n := n) (m := m) q N s0 eps i : ENNReal) *
          (2 : ENNReal) ^ (1 + n * (i : Nat))) := by gcongr

#print axioms adaptiveRestartWarmConst_eq_pow
#print axioms ofReal_adaptiveRestartWarmConst_eq_pow
#print axioms terminalPhaseQueryBound_warm
#print axioms exponential_restart_factor_le_terminalPhaseQueryBound

end Ttc.CVIndependentRestartCostAudit
