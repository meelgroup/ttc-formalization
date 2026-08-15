import Ttc.Volume.CVHybridSchedule
import Ttc.Exec.CVSwitchedSmallRateUniversalWarm
import Ttc.Exec.CVConcreteAugmentedRetryCutoffBudget

/-!
# A uniformly slow source cooling schedule

This is the operationally honest fallback after the cost-preserving product reset is
ruled out.  The variance ratio remains `1 + 1/n` even after the truncation body has
become the full body.  Consequently the accepted-seed cross-warm factor is constant
(`O(e)`) rather than exponential in the dimension.

The price is an all-geometric phase count

`O(n log (N / s0))`,

which must be carried as an additional runtime factor instead of claiming the faster
accelerated source schedule.
-/

set_option autoImplicit false

namespace Ttc.CVSlowFullBodySourceSchedule

open Arlib.GaussianCooling
open Ttc.CVHybridSchedule
open Ttc.CVGaussianAdaptiveAcceptedWarm
open Ttc.CVSwitchedSmallRateUniversalWarm
open Ttc.CVConcreteAugmentedRetryCutoffBudget

/-- Number of `1+1/n` variance steps needed to grow from `s0` to `N`. -/
noncomputable def slowSourcePhases (n : Nat) (N s0 : Real) : Nat :=
  coldPhases n (s0 / N)

/-- The uniform-rate variance schedule. -/
noncomputable def slowSourceSigmaSq (n : Nat) (s0 : Real) (i : Nat) : Real :=
  geomSchedule s0 (1 / (n : Real)) i

theorem slowSourceSigmaSq_pos
    {n : Nat} (hn : 1 ≤ n) {s0 : Real} (hs0 : 0 < s0) (i : Nat) :
    0 < slowSourceSigmaSq n s0 i := by
  unfold slowSourceSigmaSq
  exact geomSchedule_pos hs0 (by positivity) i

/-- Every successor uses exactly the safe fixed rate. -/
theorem slowSourceSigmaSq_succ
    (n : Nat) (s0 : Real) (i : Nat) :
    slowSourceSigmaSq n s0 (i + 1) =
      slowSourceSigmaSq n s0 i * (1 + 1 / (n : Real)) := by
  unfold slowSourceSigmaSq
  rw [geomSchedule_succ]

/-- The declared terminal phase reaches the requested target variance. -/
theorem target_le_slowSourceSigmaSq_terminal
    {n : Nat} (hn : 1 ≤ n) {N s0 : Real}
    (hN : 0 < N) (hs0 : 0 < s0) (hsN : s0 ≤ N) :
    N ≤ slowSourceSigmaSq n s0 (slowSourcePhases n N s0) := by
  have hratio0 : 0 < s0 / N := div_pos hs0 hN
  have hratio1 : s0 / N ≤ 1 := (div_le_one hN).2 hsN
  have hreach := one_le_coldEnd hn hratio0 hratio1
  unfold coldEnd at hreach
  unfold slowSourcePhases slowSourceSigmaSq
  unfold geomSchedule at hreach ⊢
  have hmul := mul_le_mul_of_nonneg_left hreach hN.le
  calc
    N = N * 1 := by ring
    _ ≤ N * ((s0 / N) * (1 + 1 / (n : Real)) ^ coldPhases n (s0 / N)) := hmul
    _ = s0 * (1 + 1 / (n : Real)) ^ coldPhases n (s0 / N) := by
      field_simp

/-- It overshoots by less than one safe cooling factor. -/
theorem slowSourceSigmaSq_terminal_lt
    {n : Nat} (hn : 1 ≤ n) {N s0 : Real}
    (hN : 0 < N) (hs0 : 0 < s0) (hsN : s0 ≤ N) :
    slowSourceSigmaSq n s0 (slowSourcePhases n N s0) <
      N * (1 + 1 / (n : Real)) := by
  have hratio0 : 0 < s0 / N := div_pos hs0 hN
  have hratio1 : s0 / N ≤ 1 := (div_le_one hN).2 hsN
  have hover := coldEnd_lt_one_add_inv hn hratio0 hratio1
  unfold coldEnd at hover
  unfold slowSourcePhases slowSourceSigmaSq
  unfold geomSchedule at hover ⊢
  have hmul := mul_lt_mul_of_pos_left hover hN
  calc
    s0 * (1 + 1 / (n : Real)) ^ coldPhases n (s0 / N) =
        N * ((s0 / N) * (1 + 1 / (n : Real)) ^ coldPhases n (s0 / N)) := by
      field_simp
    _ < N * (1 + 1 / (n : Real)) := hmul

/-- Exact phase-count bound for the slow fallback. -/
theorem slowSourcePhases_cast_lt
    {n : Nat} (hn : 1 ≤ n) {N s0 : Real}
    (hN : 0 < N) (hs0 : 0 < s0) :
    (slowSourcePhases n N s0 : Real) <
      2 * (n : Real) * max 0 (Real.log (N / s0)) + 1 := by
  have h := coldPhases_cast_lt_add_one hn (s0 / N)
  unfold slowSourcePhases
  convert h using 1
  congr 3
  field_simp

/-- The accepted full-body seed transition on the slow schedule has a universal warm
factor.  This is the analytic fact that fails for the accelerated `3/2` transition. -/
theorem slowFullBodyWarmFactor_le_two_exp {n : Nat} (hn : 1 ≤ n) :
    acceleratedSeedWarmFactor n (1 + 1 / (n : Real)) ≤
      ENNReal.ofReal (2 * Real.exp 1) := by
  apply acceleratedSeedWarmFactor_one_add_le_two_exp hn
  · positivity
  · exact le_rfl

/-- Consequently the generic retained accepted-seed reference-cost envelope is bounded
by the same envelope with the dimension-independent multiplier `2e`. -/
theorem retryReferenceMeanEnvelope_slowWarm_le_two_exp
    {n : Nat} (hn : 1 ≤ n) (steps : Nat → Nat) (L : Nat) :
    retryReferenceMeanEnvelope
        (acceleratedSeedWarmFactor n (1 + 1 / (n : Real))).toReal steps L ≤
      retryReferenceMeanEnvelope (2 * Real.exp 1) steps L := by
  have htop : ENNReal.ofReal (2 * Real.exp 1) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hM := ENNReal.toReal_le_toReal
    (by
      unfold acceleratedSeedWarmFactor
      exact ENNReal.ofReal_ne_top)
    htop |>.2 (slowFullBodyWarmFactor_le_two_exp hn)
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.exp 1)] at hM
  unfold retryReferenceMeanEnvelope
  apply Finset.sum_le_sum
  intro i hi
  gcongr

#print axioms slowSourceSigmaSq_pos
#print axioms slowSourceSigmaSq_succ
#print axioms target_le_slowSourceSigmaSq_terminal
#print axioms slowSourceSigmaSq_terminal_lt
#print axioms slowSourcePhases_cast_lt
#print axioms slowFullBodyWarmFactor_le_two_exp
#print axioms retryReferenceMeanEnvelope_slowWarm_le_two_exp

end Ttc.CVSlowFullBodySourceSchedule
