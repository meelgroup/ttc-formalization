/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.AdaptiveTerminalWarmLaw
import Ttc.Volume.RunwiseSamplerAmplification
import Ttc.Volume.CVSamplerErrorBudget

/-!
# Explicit one-run sampler-error parameters

The runwise coupling theorem tensorizes only across the `(m+1)*k` elementary samples in
one estimator run.  We spend `1/20` on mixing and leave `1/20` for the unavoidable
radius-four truncation tail.
-/

namespace Ttc.CVAdaptive

open Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open Ttc.CV.Adaptive
open scoped ENNReal

noncomputable def runwiseSamplerCalls (m k : Nat) : Real :=
  (((m + 1) * k : Nat) : Real)

/-- With `A=(m+1)k` calls, `64*epsMix=1/(20A)`. -/
noncomputable def runwiseChosenMixError (m k : Nat) : Real :=
  1 / (1280 * runwiseSamplerCalls m k)

theorem runwiseSamplerCalls_pos (m : Nat) {k : Nat} (hk : 0 < k) :
    0 < runwiseSamplerCalls m k := by
  unfold runwiseSamplerCalls
  positivity

theorem runwiseChosenMixError_pos (m : Nat) {k : Nat} (hk : 0 < k) :
    0 < runwiseChosenMixError m k := by
  unfold runwiseChosenMixError
  positivity [runwiseSamplerCalls_pos m hk]

theorem runwiseChosenMixError_le_one_div_32 (m : Nat) {k : Nat} (hk : 0 < k) :
    runwiseChosenMixError m k <= 1 / 32 := by
  have hA : 1 <= runwiseSamplerCalls m k := by
    unfold runwiseSamplerCalls
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity : (m + 1) * k ≠ 0)
  have hApos : 0 < runwiseSamplerCalls m k := runwiseSamplerCalls_pos m hk
  unfold runwiseChosenMixError
  rw [div_le_div_iff₀ (by positivity : (0 : Real) < 1280 * runwiseSamplerCalls m k)
    (by norm_num : (0 : Real) < 32)]
  nlinarith

theorem runwiseChosenMixError_exact_budget (m : Nat) {k : Nat} (hk : 0 < k) :
    runwiseSamplerCalls m k * (64 * runwiseChosenMixError m k) = 1 / 20 := by
  have hA : 0 < runwiseSamplerCalls m k := runwiseSamplerCalls_pos m hk
  unfold runwiseChosenMixError
  field_simp
  ring

/-- Exact feasibility condition for the fixed radius-four theorem: its one-run accumulated
tail must fit in the reserved `1/20`.  No repetition count or requested failure probability
appears here. -/
def RunwiseRadiusFourTailFits (n m k : Nat) : Prop :=
  runwiseSamplerCalls m k * radiusFourTail n <= 1 / 20

/-- The chosen mixing tolerance and the explicit tail premise discharge the exact real-valued
budget consumed by `RunwiseSamplerAmplification`. -/
theorem runwise_sampler_real_budget (n m : Nat) {k : Nat} (hk : 0 < k)
    (htail : RunwiseRadiusFourTailFits n m k) :
    runwiseSamplerCalls m k *
        (64 * runwiseChosenMixError m k + radiusFourTail n) <= 1 / 10 := by
  have hmix := runwiseChosenMixError_exact_budget m hk
  unfold RunwiseRadiusFourTailFits at htail
  nlinarith

/-- The same statement in the exact `ENNReal.toReal` shape of the concrete warm-law TV
constant and `median_success_of_runwise_sampler_tv`. -/
theorem runwise_sampler_toReal_budget (n m : Nat) {k : Nat} (hk : 0 < k)
    (htail : RunwiseRadiusFourTailFits n m k) :
    ((((m + 1) * k : Nat) : Real) *
      (64 * ENNReal.ofReal (runwiseChosenMixError m k) +
        ENNReal.ofReal ((4 * Real.exp (-(15 : Real) / 2)) ^ n)).toReal) <= 1 / 10 := by
  have heps : 0 <= runwiseChosenMixError m k := (runwiseChosenMixError_pos m hk).le
  have htail0 : 0 <= (4 * Real.exp (-(15 : Real) / 2)) ^ n := by positivity
  have htoReal :
      (64 * ENNReal.ofReal (runwiseChosenMixError m k) +
        ENNReal.ofReal ((4 * Real.exp (-(15 : Real) / 2)) ^ n)).toReal =
      64 * runwiseChosenMixError m k + radiusFourTail n := by
    rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul]
    simp [ENNReal.toReal_ofReal, heps, htail0, radiusFourTail]
  rw [htoReal]
  exact runwise_sampler_real_budget n m hk htail

/-- Full one-run sampler parameter package: positivity, the warm-law `1/32` range, and the
runwise tensor budget. -/
theorem runwise_sampler_parameter_bundle (n m : Nat) {k : Nat} (hk : 0 < k)
    (htail : RunwiseRadiusFourTailFits n m k) :
    0 < runwiseChosenMixError m k ∧
      runwiseChosenMixError m k <= 1 / 32 ∧
      ((((m + 1) * k : Nat) : Real) *
        (64 * ENNReal.ofReal (runwiseChosenMixError m k) +
          ENNReal.ofReal ((4 * Real.exp (-(15 : Real) / 2)) ^ n)).toReal) <= 1 / 10 := by
  exact ⟨runwiseChosenMixError_pos m hk, runwiseChosenMixError_le_one_div_32 m hk,
    runwise_sampler_toReal_budget n m hk htail⟩

/-! ## Concrete mixing deadline -/

noncomputable def runwiseMixingDeadline (n : Nat) (N s0 : Real) (m k : Nat)
    (i : Fin (m + 1)) : Real :=
  4 * 640 ^ 2 * adaptiveTerminalSigma N s0 i ^ 2 * (n : Real) *
      (Real.log (adaptiveRestartWarmConst n i) +
        2 * Real.log (1 / runwiseChosenMixError m k)) /
        (adaptiveTerminalDelta (n := n) N s0 i * Real.log 2) ^ 2 + 1

noncomputable def runwiseMixingSteps (n : Nat) (N s0 : Real) (m k : Nat) :
    Fin (m + 1) -> Nat :=
  fun i => ⌈runwiseMixingDeadline n N s0 m k i⌉₊ + 1

/-- The selected natural step count directly supplies `AdaptiveTerminalWarmLaw.hsteps`. -/
theorem runwiseMixingSteps_spec (n : Nat) (N s0 : Real) (m k : Nat)
    (i : Fin (m + 1)) :
    4 * 640 ^ 2 * adaptiveTerminalSigma N s0 i ^ 2 * (n : Real) *
          (Real.log (adaptiveRestartWarmConst n i) +
            2 * Real.log (1 / runwiseChosenMixError m k)) /
            (adaptiveTerminalDelta (n := n) N s0 i * Real.log 2) ^ 2 + 1
      <= (runwiseMixingSteps n N s0 m k i : Real) := by
  change runwiseMixingDeadline n N s0 m k i <=
    (runwiseMixingSteps n N s0 m k i : Real)
  have hceil := Nat.le_ceil (runwiseMixingDeadline n N s0 m k i)
  rw [runwiseMixingSteps]
  push_cast
  linarith

/-- The ceiling adds less than two steps above the displayed real deadline. -/
theorem runwiseMixingSteps_cast_lt (n : Nat) (N s0 : Real) (m : Nat)
    {k : Nat} (hk : 0 < k) (i : Fin (m + 1)) :
    (runwiseMixingSteps n N s0 m k i : Real) <
      runwiseMixingDeadline n N s0 m k i + 2 := by
  have heps0 : 0 < runwiseChosenMixError m k := runwiseChosenMixError_pos m hk
  have heps32 : runwiseChosenMixError m k <= 1 / 32 :=
    runwiseChosenMixError_le_one_div_32 m hk
  have hinv : 1 <= 1 / runwiseChosenMixError m k := by
    rw [le_div_iff₀ heps0]
    linarith
  have hlogeps : 0 <= Real.log (1 / runwiseChosenMixError m k) :=
    Real.log_nonneg hinv
  have hlogM : 0 <= Real.log (adaptiveRestartWarmConst n i) := by
    rw [log_adaptiveRestartWarmConst]
    positivity
  have hdeadline : 0 <= runwiseMixingDeadline n N s0 m k i := by
    unfold runwiseMixingDeadline
    have hlogs : 0 <= Real.log (adaptiveRestartWarmConst n i) +
        2 * Real.log (1 / runwiseChosenMixError m k) := by positivity
    have hnum : 0 <= 4 * 640 ^ 2 * adaptiveTerminalSigma N s0 i ^ 2 * (n : Real) *
        (Real.log (adaptiveRestartWarmConst n i) +
          2 * Real.log (1 / runwiseChosenMixError m k)) := by positivity
    exact add_nonneg (div_nonneg hnum (sq_nonneg _)) (by norm_num)
  have hceil := Nat.ceil_lt_add_one hdeadline
  rw [runwiseMixingSteps]
  push_cast
  linarith

/-! ### Axiom audit -/

#print axioms runwise_sampler_toReal_budget
#print axioms runwise_sampler_parameter_bundle
#print axioms runwiseMixingSteps_spec
#print axioms runwiseMixingSteps_cast_lt

end Ttc.CVAdaptive
