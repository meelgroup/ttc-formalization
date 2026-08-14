/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Volume.CVOperationalRuntime
import Arlib.MarkovChains.Continuous.ColdTruncationRelativeFour

/-!
# A total sampler-error budget for the adaptive CV schedule

The per-sample TV error is `64 * epsMix + (4 * exp (-15/2))^n`.  This file chooses
`epsMix` so that the mixing term uses half of a requested global budget, then gives the exact
source-regime condition under which the fixed truncation tail uses the other half.
-/

namespace Ttc.CVAdaptive

open Arlib.GaussianCooling.Chunked
open Ttc.CV.Adaptive

/-- The dimension-only radius-four relative truncation error. -/
noncomputable def radiusFourTail (n : ℕ) : ℝ :=
  (4 * Real.exp (-(15 : ℝ) / 2)) ^ n

/-- Coarse upper bound for the number of speedy draws across all runs and all adaptive
phases.  The terminal output contributes the `+3` rather than the preterminal `+2`. -/
noncomputable def adaptiveSamplerCallEnvelope
    (N s₀ runs drawsPerPhase : ℝ) : ℝ :=
  runs * (5 * N / s₀ + 3) * drawsPerPhase

/-- The per-chain mixing tolerance which allocates half of `rhoBudget` to accumulated mixing
error after the factor `64`. -/
noncomputable def adaptiveChosenMixError
    (N s₀ runs drawsPerPhase rhoBudget : ℝ) : ℝ :=
  rhoBudget / (128 * adaptiveSamplerCallEnvelope N s₀ runs drawsPerPhase)

/-- The radius-four mixing deadline after substituting the globally budgeted mixing error. -/
noncomputable def adaptiveBudgetedMixingEnvelope
    (n : ℕ) (N s₀ runs drawsPerPhase rhoBudget : ℝ) : ℝ :=
  adaptiveRadiusFourMixingEnvelope n N s₀
    (adaptiveChosenMixError N s₀ runs drawsPerPhase rhoBudget)

/-- Including the terminal output, the adaptive phase count is below `5N/s₀+3`. -/
theorem adaptiveTerminalPhaseCount_lt {N s₀ : ℝ} (hN : 0 < N) (hs₀ : 0 < s₀) :
    ((adaptiveChunkOffset N s₀ (adaptiveTerminalChunk N s₀) + 1 : ℕ) : ℝ) <
      5 * N / s₀ + 3 := by
  have h := adaptiveTerminalOffset_lt_five_mul_div_add_two hN hs₀
  push_cast
  linarith

/-- The source tail is already stronger than `2^{-n}`. -/
theorem radiusFourTail_le_two_pow_neg (n : ℕ) :
    radiusFourTail n ≤ (1 / 2 : ℝ) ^ n := by
  have hexp : (8 : ℝ) ≤ Real.exp (15 / 2) := by
    have h := Real.add_one_le_exp (15 / 2 : ℝ)
    linarith
  have hpos : 0 < Real.exp (15 / 2 : ℝ) := Real.exp_pos _
  have hinv : Real.exp (-(15 : ℝ) / 2) ≤ 1 / 8 := by
    have hrecip : (Real.exp (15 / 2 : ℝ))⁻¹ ≤ (8 : ℝ)⁻¹ :=
      (inv_le_inv₀ hpos (by norm_num : (0 : ℝ) < 8)).2 hexp
    calc
      Real.exp (-(15 : ℝ) / 2) = (Real.exp (15 / 2 : ℝ))⁻¹ := by
        rw [← Real.exp_neg]
        congr 1
        ring
      _ ≤ (8 : ℝ)⁻¹ := hrecip
      _ = 1 / 8 := by norm_num
  have hbase : 4 * Real.exp (-(15 : ℝ) / 2) ≤ 1 / 2 := by nlinarith
  have hbase0 : 0 ≤ 4 * Real.exp (-(15 : ℝ) / 2) := by positivity
  unfold radiusFourTail
  exact pow_le_pow_left₀ hbase0 hbase n

/-- Positivity and the probability-range upper bound for the chosen mixing tolerance. -/
theorem adaptiveChosenMixError_mem_Ioc {N s₀ rhoBudget : ℝ} {runs drawsPerPhase : ℕ}
    (hN : 0 < N) (hs₀ : 0 < s₀) (hruns : 1 ≤ runs) (hdraws : 1 ≤ drawsPerPhase)
    (hrho0 : 0 < rhoBudget) (hrho1 : rhoBudget ≤ 1) :
    adaptiveChosenMixError N s₀ runs drawsPerPhase rhoBudget ∈ Set.Ioc 0 1 := by
  have hB : 0 < 5 * N / s₀ + 3 := by positivity
  have hr : (1 : ℝ) ≤ runs := by exact_mod_cast hruns
  have hd : (1 : ℝ) ≤ drawsPerPhase := by exact_mod_cast hdraws
  have hA : 0 < adaptiveSamplerCallEnvelope N s₀ runs drawsPerPhase := by
    unfold adaptiveSamplerCallEnvelope
    positivity
  constructor
  · unfold adaptiveChosenMixError
    positivity
  · rw [adaptiveChosenMixError, div_le_one (by positivity : 0 <
        128 * adaptiveSamplerCallEnvelope N s₀ runs drawsPerPhase)]
    have hratio : 0 < N / s₀ := div_pos hN hs₀
    have hfive : 0 < 5 * N / s₀ := by positivity
    have hB1 : (1 : ℝ) ≤ 5 * N / s₀ + 3 := by linarith
    have hrB : (1 : ℝ) ≤ (runs : ℝ) * (5 * N / s₀ + 3) := by
      nlinarith [mul_le_mul hr hB1 (by norm_num : (0 : ℝ) ≤ 1)
        (by positivity : (0 : ℝ) ≤ (runs : ℝ))]
    have hAge : 1 ≤ adaptiveSamplerCallEnvelope N s₀ runs drawsPerPhase := by
      unfold adaptiveSamplerCallEnvelope
      nlinarith [mul_le_mul hrB hd (by norm_num : (0 : ℝ) ≤ 1)
        (by positivity : (0 : ℝ) ≤ (runs : ℝ) * (5 * N / s₀ + 3))]
    nlinarith

/-- Exact logarithm appearing in the polynomial deadline after choosing `epsMix`. -/
theorem log_inv_adaptiveChosenMixError {N s₀ runs drawsPerPhase rhoBudget : ℝ}
    (hA : 0 < adaptiveSamplerCallEnvelope N s₀ runs drawsPerPhase)
    (hrho : 0 < rhoBudget) :
    Real.log (1 / adaptiveChosenMixError N s₀ runs drawsPerPhase rhoBudget) =
      Real.log (128 * adaptiveSamplerCallEnvelope N s₀ runs drawsPerPhase / rhoBudget) := by
  congr 1
  unfold adaptiveChosenMixError
  field_simp

/-- **Exact global sampler budget.**  The chosen mixing tolerance contributes at most
`rhoBudget/2`.  The displayed tail-regime hypothesis says that the fixed truncation error,
even after the same union bound, contributes at most the other half. -/
theorem adaptive_total_sampler_error_le_budget {n : ℕ} {N s₀ rhoBudget : ℝ}
    {runs drawsPerPhase : ℕ} (hN : 0 < N) (hs₀ : 0 < s₀)
    (hruns : 1 ≤ runs) (hdraws : 1 ≤ drawsPerPhase) (hrho0 : 0 < rhoBudget)
    (htail : 2 * adaptiveSamplerCallEnvelope N s₀ runs drawsPerPhase * radiusFourTail n ≤
      rhoBudget) :
    (runs : ℝ) *
        (adaptiveChunkOffset N s₀ (adaptiveTerminalChunk N s₀) + 1 : ℕ) *
        (drawsPerPhase : ℝ) *
        (64 * adaptiveChosenMixError N s₀ runs drawsPerPhase rhoBudget + radiusFourTail n)
      ≤ rhoBudget := by
  let A := adaptiveSamplerCallEnvelope N s₀ runs drawsPerPhase
  let C := (runs : ℝ) *
    (adaptiveChunkOffset N s₀ (adaptiveTerminalChunk N s₀) + 1 : ℕ) *
    (drawsPerPhase : ℝ)
  have hr0 : (0 : ℝ) ≤ runs := by positivity
  have hd0 : (0 : ℝ) ≤ drawsPerPhase := by positivity
  have hB : 0 < 5 * N / s₀ + 3 := by positivity
  have hA : 0 < A := by
    dsimp [A, adaptiveSamplerCallEnvelope]
    positivity
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hCA : C ≤ A := by
    dsimp [C, A, adaptiveSamplerCallEnvelope]
    have hphase := (adaptiveTerminalPhaseCount_lt hN hs₀).le
    gcongr
  have heq : 64 * adaptiveChosenMixError N s₀ runs drawsPerPhase rhoBudget =
      rhoBudget / (2 * A) := by
    dsimp [A]
    unfold adaptiveChosenMixError
    field_simp
    ring
  have hmix : C * (64 * adaptiveChosenMixError N s₀ runs drawsPerPhase rhoBudget) ≤
      rhoBudget / 2 := by
    rw [heq]
    calc
      C * (rhoBudget / (2 * A)) ≤ A * (rhoBudget / (2 * A)) := by
        gcongr
      _ = rhoBudget / 2 := by field_simp
  have htail' : C * radiusFourTail n ≤ rhoBudget / 2 := by
    have htail0 : 0 ≤ radiusFourTail n := by unfold radiusFourTail; positivity
    have hCA' := mul_le_mul_of_nonneg_right hCA htail0
    change 2 * A * radiusFourTail n ≤ rhoBudget at htail
    nlinarith
  dsimp [C] at hmix htail' ⊢
  ring_nf at hmix htail' ⊢
  linarith

/-- Simpler sufficient source regime: it is enough for the budget to dominate the call
envelope times `2^(1-n)`. -/
theorem adaptive_total_sampler_error_le_budget_of_dyadic {n : ℕ} {N s₀ rhoBudget : ℝ}
    {runs drawsPerPhase : ℕ} (hN : 0 < N) (hs₀ : 0 < s₀)
    (hruns : 1 ≤ runs) (hdraws : 1 ≤ drawsPerPhase) (hrho0 : 0 < rhoBudget)
    (hsource : 2 * adaptiveSamplerCallEnvelope N s₀ runs drawsPerPhase * (1 / 2 : ℝ) ^ n ≤
      rhoBudget) :
    (runs : ℝ) *
        (adaptiveChunkOffset N s₀ (adaptiveTerminalChunk N s₀) + 1 : ℕ) *
        (drawsPerPhase : ℝ) *
        (64 * adaptiveChosenMixError N s₀ runs drawsPerPhase rhoBudget + radiusFourTail n)
      ≤ rhoBudget := by
  apply adaptive_total_sampler_error_le_budget hN hs₀ hruns hdraws hrho0
  have hcall0 : 0 ≤ adaptiveSamplerCallEnvelope N s₀ runs drawsPerPhase := by
    unfold adaptiveSamplerCallEnvelope
    positivity
  exact (mul_le_mul_of_nonneg_left (radiusFourTail_le_two_pow_neg n)
    (mul_nonneg (by norm_num) hcall0)).trans hsource

/-- The globally chosen tolerance can be substituted directly into the polynomial
radius-four mixing deadline at every preterminal adaptive phase. -/
theorem adaptive_budgeted_radiusFour_deadline_le {n : ℕ} (hn : 21 ≤ n)
    {N s₀ rhoBudget : ℝ} {runs drawsPerPhase : ℕ}
    (hN : 0 < N) (hs₀ : 0 < s₀) (hruns : 1 ≤ runs) (hdraws : 1 ≤ drawsPerPhase)
    (hrho0 : 0 < rhoBudget) (hrho1 : rhoBudget ≤ 1)
    {i : ℕ} (hi : i < adaptiveChunkOffset N s₀ (adaptiveTerminalChunk N s₀)) :
    let u := adaptiveSigmaSq N s₀ i
    let σ := Real.sqrt u
    let M := adaptiveRestartWarmConst n i
    let δ := min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))
    4 * 640 ^ 2 * σ ^ 2 * (n : ℝ) *
          (Real.log M + 2 * Real.log
            (1 / adaptiveChosenMixError N s₀ runs drawsPerPhase rhoBudget)) /
          (δ * Real.log 2) ^ 2 + 1
      ≤ adaptiveBudgetedMixingEnvelope n N s₀ runs drawsPerPhase rhoBudget := by
  have heps := adaptiveChosenMixError_mem_Ioc hN hs₀ hruns hdraws hrho0 hrho1
  exact adaptive_radiusFour_deadline_le_envelope hn hN hs₀ heps.1 heps.2 hi

end Ttc.CVAdaptive

#print axioms Ttc.CVAdaptive.radiusFourTail_le_two_pow_neg
#print axioms Ttc.CVAdaptive.adaptive_total_sampler_error_le_budget
#print axioms Ttc.CVAdaptive.adaptive_total_sampler_error_le_budget_of_dyadic
#print axioms Ttc.CVAdaptive.adaptive_budgeted_radiusFour_deadline_le
