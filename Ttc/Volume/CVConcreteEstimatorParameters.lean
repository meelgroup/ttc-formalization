/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVConcreteOracleAccuracy
import Ttc.Volume.RunwiseSamplerAmplification

/-!
# Explicit sample and repetition counts for the concrete CV oracle

The terminal estimator spends half of `varBudget eps` on the preterminal phases and reserves
the other half for the last phase.  A single ceiling then discharges all three lower bounds
on the sample count.
-/

namespace Ttc.CVAdaptive

open Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open Ttc.CV.Adaptive

noncomputable def concreteEstimatorKappa (eps : Real) : Real :=
  varBudget eps / 2

noncomputable def concreteEstimatorSampleThreshold (J : Nat) (eps : Real) : Real :=
  max 42 (max
    (14 * (J : Real) / varBudget eps)
    (2 * (Real.exp (1 / 2) - 1) / varBudget eps))

noncomputable def concreteEstimatorSamples (J : Nat) (eps : Real) : Nat :=
  ⌈concreteEstimatorSampleThreshold J eps⌉₊ + 1

/-- Repetitions for the runwise-coupled theorem, whose one-run success is `7/10`. -/
noncomputable def concreteRunwiseReps (p : Real) : Nat :=
  ⌈Real.log (1 / p) / (2 * (7 / 10 - 1 / 2) ^ 2)⌉₊ + 1

/-- Repetitions for the current packed theorem, whose exact one-run success is `4/5`. -/
noncomputable def concretePackedReps (eps p : Real) : Nat := reps eps p

theorem concreteEstimatorKappa_pos {eps : Real} (heps : 0 < eps) :
    0 < concreteEstimatorKappa eps := by
  unfold concreteEstimatorKappa
  positivity [varBudget_pos heps]

theorem concreteEstimatorSamples_pos (J : Nat) (eps : Real) :
    0 < concreteEstimatorSamples J eps := by
  simp [concreteEstimatorSamples]

theorem concreteEstimatorSampleThreshold_le_cast_samples (J : Nat) (eps : Real) :
    concreteEstimatorSampleThreshold J eps <= (concreteEstimatorSamples J eps : Real) := by
  have hceil := Nat.le_ceil (concreteEstimatorSampleThreshold J eps)
  rw [concreteEstimatorSamples]
  push_cast
  linarith

theorem concreteEstimatorSamples_ge_42 (J : Nat) (eps : Real) :
    42 <= (concreteEstimatorSamples J eps : Real) := by
  exact (le_max_left 42 _).trans
    (concreteEstimatorSampleThreshold_le_cast_samples J eps)

theorem concreteEstimatorSamples_phase_budget (J : Nat) {eps : Real} (heps : 0 < eps) :
    7 * (J : Real) <=
      (concreteEstimatorSamples J eps : Real) * concreteEstimatorKappa eps := by
  have hV : 0 < varBudget eps := varBudget_pos heps
  have hk := concreteEstimatorSampleThreshold_le_cast_samples J eps
  have hterm : 14 * (J : Real) / varBudget eps <=
      (concreteEstimatorSamples J eps : Real) :=
    (le_max_left (14 * (J : Real) / varBudget eps)
      (2 * (Real.exp (1 / 2) - 1) / varBudget eps)).trans
      ((le_max_right 42 _).trans hk)
  rw [div_le_iff₀ hV] at hterm
  unfold concreteEstimatorKappa
  nlinarith

theorem concreteEstimator_terminal_allowance (J : Nat) {eps : Real} (heps : 0 < eps) :
    (Real.exp (1 / 2) - 1) / (concreteEstimatorSamples J eps : Real) <=
      varBudget eps / 2 := by
  have hV : 0 < varBudget eps := varBudget_pos heps
  have hkNat : 0 < concreteEstimatorSamples J eps := concreteEstimatorSamples_pos J eps
  have hkR : (0 : Real) < concreteEstimatorSamples J eps := by exact_mod_cast hkNat
  have hk := concreteEstimatorSampleThreshold_le_cast_samples J eps
  have hterm : 2 * (Real.exp (1 / 2) - 1) / varBudget eps <=
      (concreteEstimatorSamples J eps : Real) :=
    (le_max_right (14 * (J : Real) / varBudget eps)
      (2 * (Real.exp (1 / 2) - 1) / varBudget eps)).trans
      ((le_max_right 42 _).trans hk)
  rw [div_le_iff₀ hV] at hterm
  rw [div_le_iff₀ hkR]
  nlinarith

/-- The concrete choices discharge the terminal estimator's exponential budget. -/
theorem concreteEstimator_exp_budget (J : Nat) {eps : Real} (heps : 0 < eps) :
    Real.exp (concreteEstimatorKappa eps +
        (Real.exp (1 / 2) - 1) / (concreteEstimatorSamples J eps : Real)) - 1 <=
      eps ^ 2 / 5 := by
  have hallow := concreteEstimator_terminal_allowance J heps
  have harg : concreteEstimatorKappa eps +
      (Real.exp (1 / 2) - 1) / (concreteEstimatorSamples J eps : Real) <=
      varBudget eps := by
    unfold concreteEstimatorKappa
    linarith
  calc
    Real.exp (concreteEstimatorKappa eps +
        (Real.exp (1 / 2) - 1) / (concreteEstimatorSamples J eps : Real)) - 1 <=
      Real.exp (varBudget eps) - 1 := by gcongr
    _ <= eps ^ 2 / 5 := varBudget_spec eps heps

/-- One theorem packages the four estimator binders used by `CVConcreteOracleAccuracy`. -/
theorem concreteEstimator_parameter_bundle (J : Nat) {eps : Real} (heps : 0 < eps) :
    0 < concreteEstimatorSamples J eps ∧
    0 <= concreteEstimatorKappa eps ∧
    42 <= (concreteEstimatorSamples J eps : Real) ∧
    7 * (J : Real) <=
      (concreteEstimatorSamples J eps : Real) * concreteEstimatorKappa eps ∧
    Real.exp (concreteEstimatorKappa eps +
        (Real.exp (1 / 2) - 1) / (concreteEstimatorSamples J eps : Real)) - 1 <=
      eps ^ 2 / 5 := by
  exact ⟨concreteEstimatorSamples_pos J eps, (concreteEstimatorKappa_pos heps).le,
    concreteEstimatorSamples_ge_42 J eps,
    concreteEstimatorSamples_phase_budget J heps,
    concreteEstimator_exp_budget J heps⟩

/-- Direct specialization to the chunk index appearing in
`packed_median_accuracy_concrete_adaptive`. -/
theorem concreteTerminalEstimator_parameter_bundle
    (n : Nat) (C eta : Real) {eps : Real} (heps : 0 < eps) :
    let J := adaptiveTerminalChunk (C ^ 2 * n) (polynomialEndpointSigmaSq n eta)
    0 < concreteEstimatorSamples J eps ∧
    0 <= concreteEstimatorKappa eps ∧
    42 <= (concreteEstimatorSamples J eps : Real) ∧
    7 * (J : Real) <=
      (concreteEstimatorSamples J eps : Real) * concreteEstimatorKappa eps ∧
    Real.exp (concreteEstimatorKappa eps +
        (Real.exp (1 / 2) - 1) / (concreteEstimatorSamples J eps : Real)) - 1 <=
      eps ^ 2 / 5 := by
  dsimp only
  exact concreteEstimator_parameter_bundle _ heps

/-- The ceiling costs less than two above the explicit real threshold. -/
theorem concreteEstimatorSamples_cast_lt (J : Nat) {eps : Real} (heps : 0 < eps) :
    (concreteEstimatorSamples J eps : Real) <
      concreteEstimatorSampleThreshold J eps + 2 := by
  have hV : 0 < varBudget eps := varBudget_pos heps
  have hA : 0 < Real.exp (1 / 2) - 1 := by
    have := Real.add_one_lt_exp (x := (1 / 2 : Real)) (by norm_num)
    linarith
  have hthreshold : 0 <= concreteEstimatorSampleThreshold J eps := by
    unfold concreteEstimatorSampleThreshold
    positivity
  have hceil := Nat.ceil_lt_add_one hthreshold
  rw [concreteEstimatorSamples]
  push_cast
  linarith

theorem concreteRunwiseReps_pos (p : Real) : 0 < concreteRunwiseReps p := by
  simp [concreteRunwiseReps]

theorem concreteRunwiseReps_spec (p : Real) :
    Real.log (1 / p) / (2 * (7 / 10 - 1 / 2) ^ 2) <=
      (concreteRunwiseReps p : Real) := by
  have hceil := Nat.le_ceil
    (Real.log (1 / p) / (2 * (7 / 10 - 1 / 2) ^ 2))
  rw [concreteRunwiseReps]
  push_cast
  linarith

theorem concretePackedReps_bundle {eps p : Real} (hp : 0 < p) (hp1 : p < 1) :
    0 < concretePackedReps eps p ∧
      Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2) <=
        (concretePackedReps eps p : Real) := by
  exact ⟨reps_pos eps p hp hp1, reps_spec eps p hp hp1⟩

theorem concreteRunwiseReps_cast_lt {p : Real} (hp : 0 < p) (hp1 : p < 1) :
    (concreteRunwiseReps p : Real) <
      Real.log (1 / p) / (2 * (7 / 10 - 1 / 2) ^ 2) + 2 := by
  have hinv : 1 < 1 / p := by
    rw [lt_div_iff₀ hp]
    simpa using hp1
  have hlog : 0 <= Real.log (1 / p) := (Real.log_pos hinv).le
  have hden : (0 : Real) < 2 * (7 / 10 - 1 / 2) ^ 2 := by norm_num
  have harg : 0 <= Real.log (1 / p) / (2 * (7 / 10 - 1 / 2) ^ 2) :=
    div_nonneg hlog hden.le
  have hceil := Nat.ceil_lt_add_one harg
  rw [concreteRunwiseReps]
  push_cast
  linarith

/-! ### Axiom audit -/

#print axioms concreteEstimator_parameter_bundle
#print axioms concreteTerminalEstimator_parameter_bundle
#print axioms concreteEstimatorSamples_cast_lt
#print axioms concreteRunwiseReps_spec
#print axioms concreteRunwiseReps_cast_lt
#print axioms concretePackedReps_bundle

end Ttc.CVAdaptive
