/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVRunwiseSamplerParameters
import Ttc.Volume.CVConcreteEstimatorParameters
import Arlib.MarkovChains.Continuous.SamplerStepCount

/-!
# Concrete feasibility of the radius-four runwise tail

In the source endpoint branch the adaptive schedule has fewer than
`80*C^2*n^2+3` phases (including the terminal phase), and the concrete estimator uses fewer
than `4800*(16*C^2*n^2+3)/eps^2` samples per phase.  The radius-four tail is at most
`2^(-8*n)`.  Consequently the displayed, entirely explicit polynomial-versus-exponential
inequality is sufficient for the runwise truncation budget.

There can be no unconditional statement for arbitrary `C`: both the phase count and sample
count grow polynomially in `C`, whereas the dimension-only truncation tail is fixed.
-/

namespace Ttc.CVAdaptive

open Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open Ttc.CV.Adaptive

/-- A sharper elementary bound on the radius-four tail: `4*exp(-15/2) <= 1/256`.
The only analytic input is the ninth Taylor partial sum for `exp(15/2)`. -/
theorem radiusFourTail_le_two_pow_neg_eight (n : Nat) :
    radiusFourTail n <= (1 / 256 : Real) ^ n := by
  have hexp : (1024 : Real) <= Real.exp (15 / 2) := by
    have hsum := Real.sum_le_exp_of_nonneg (x := (15 / 2 : Real)) (by norm_num) 9
    norm_num [Finset.sum_range_succ] at hsum ⊢
    linarith
  have hpos : 0 < Real.exp (15 / 2 : Real) := Real.exp_pos _
  have hinv : Real.exp (-(15 : Real) / 2) <= 1 / 1024 := by
    have hrecip : (Real.exp (15 / 2 : Real))⁻¹ <= (1024 : Real)⁻¹ :=
      (inv_le_inv₀ hpos (by norm_num : (0 : Real) < 1024)).2 hexp
    calc
      Real.exp (-(15 : Real) / 2) = (Real.exp (15 / 2 : Real))⁻¹ := by
        rw [← Real.exp_neg]
        congr 1
        ring
      _ <= (1024 : Real)⁻¹ := hrecip
      _ = 1 / 1024 := by norm_num
  have hbase : 4 * Real.exp (-(15 : Real) / 2) <= 1 / 256 := by nlinarith
  have hbase0 : 0 <= 4 * Real.exp (-(15 : Real) / 2) := by positivity
  unfold radiusFourTail
  exact pow_le_pow_left₀ hbase0 hbase n

/-- The exact dimension-versus-call-count sufficient condition. -/
theorem runwiseRadiusFourTailFits_of_calls_mul_pow_le
    {n m k : Nat}
    (hcount : runwiseSamplerCalls m k * (1 / 256 : Real) ^ n <= 1 / 20) :
    RunwiseRadiusFourTailFits n m k := by
  unfold RunwiseRadiusFourTailFits
  have hcalls0 : 0 <= runwiseSamplerCalls m k := by
    unfold runwiseSamplerCalls
    positivity
  exact (mul_le_mul_of_nonneg_left (radiusFourTail_le_two_pow_neg_eight n) hcalls0).trans
    hcount

/-- In the source endpoint branch, the terminal chunk index is below
`16*C^2*n^2+2`. -/
theorem concrete_source_terminalChunk_lt
    {n : Nat} {C eps : Real} (hn : 1 <= n) (hC : 0 < C)
    (hsource : (1 / 2 : Real) ^ n <= eps / 4) :
    (adaptiveTerminalChunk (C ^ 2 * n)
        (polynomialEndpointSigmaSq n (eps / 4)) : Real) <
      16 * C ^ 2 * (n : Real) ^ 2 + 2 := by
  have hnR : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hN : 0 < C ^ 2 * (n : Real) := by positivity
  have hs : polynomialEndpointSigmaSq n (eps / 4) = 1 / (16 * (n : Real)) := by
    rw [polynomialEndpointSigmaSq, if_pos hsource]
    rfl
  have hspos : 0 < polynomialEndpointSigmaSq n (eps / 4) := by
    rw [hs]
    positivity
  have hJ := adaptiveTerminalChunk_lt_div_add_two hN hspos
  rw [hs]
  rw [hs] at hJ
  convert hJ using 1
  field_simp

/-- In the source endpoint branch, the complete phase count (including the terminal output)
is below `80*C^2*n^2+3`. -/
theorem concrete_source_phaseCount_lt
    {n : Nat} {C eps : Real} (hn : 1 <= n) (hC : 0 < C)
    (hsource : (1 / 2 : Real) ^ n <= eps / 4) :
    ((terminalPhaseCount n C (polynomialEndpointSigmaSq n (eps / 4)) + 1 : Nat) : Real) <
      80 * C ^ 2 * (n : Real) ^ 2 + 3 := by
  have hnR : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hN : 0 < C ^ 2 * (n : Real) := by positivity
  have hs : polynomialEndpointSigmaSq n (eps / 4) = 1 / (16 * (n : Real)) := by
    rw [polynomialEndpointSigmaSq, if_pos hsource]
    rfl
  have hspos : 0 < polynomialEndpointSigmaSq n (eps / 4) := by
    rw [hs]
    positivity
  have hm := adaptiveTerminalPhaseCount_lt hN hspos
  change ((terminalPhaseCount n C (polynomialEndpointSigmaSq n (eps / 4)) + 1 : Nat) : Real) < _
  rw [terminalPhaseCount, terminalChunk, terminalTarget, hs]
  rw [hs] at hm
  convert hm using 1 <;> field_simp <;> ring

/-- Source-regime upper bound for the concrete per-phase sample count. -/
theorem concrete_source_estimatorSamples_lt
    {n : Nat} {C eps : Real} (hn : 1 <= n) (hC : 0 < C)
    (heps : 0 < eps) (heps1 : eps <= 1)
    (hsource : (1 / 2 : Real) ^ n <= eps / 4) :
    let J := adaptiveTerminalChunk (C ^ 2 * n)
      (polynomialEndpointSigmaSq n (eps / 4))
    (concreteEstimatorSamples J (eps / 4) : Real) <
      4800 * (16 * C ^ 2 * (n : Real) ^ 2 + 3) / eps ^ 2 := by
  dsimp only
  let J := adaptiveTerminalChunk (C ^ 2 * n)
    (polynomialEndpointSigmaSq n (eps / 4))
  have hepsHalf0 : 0 < eps / 2 := by positivity
  have hepsHalf1 : eps / 2 <= 1 := by linarith
  have hV := (Arlib.MarkovChains.sq_div_forty_le_varBudget_le_one
    hepsHalf0 hepsHalf1).1
  have hVform : eps ^ 2 / 160 <= varBudget (eps / 4) := by
    convert hV using 1 <;> ring
  have hVpos : 0 < varBudget (eps / 4) := varBudget_pos (by positivity)
  have hepsSq0 : 0 < eps ^ 2 := sq_pos_of_pos heps
  have hJ0 : (0 : Real) <= J := by positivity
  have hJ1 : (1 : Real) <= (J : Real) + 1 := by linarith
  have hepsSq1 : eps ^ 2 <= 1 := by nlinarith [sq_nonneg (eps - 1)]
  have hexp : Real.exp (1 / 2 : Real) - 1 <= 2 := by
    have hmono : Real.exp (1 / 2 : Real) <= Real.exp 1 := Real.exp_le_exp.2 (by norm_num)
    linarith [Real.exp_one_lt_d9]
  have hA : 14 * (J : Real) / varBudget (eps / 4) <=
      2400 * ((J : Real) + 1) / eps ^ 2 := by
    rw [div_le_iff₀ hVpos]
    have hmul := mul_le_mul_of_nonneg_left hVform (by positivity : (0 : Real) <=
      2400 * ((J : Real) + 1) / eps ^ 2)
    rw [div_mul_eq_mul_div, div_le_iff₀ hepsSq0] at hmul
    nlinarith
  have hB : 2 * (Real.exp (1 / 2) - 1) / varBudget (eps / 4) <=
      2400 * ((J : Real) + 1) / eps ^ 2 := by
    rw [div_le_iff₀ hVpos]
    have hmul := mul_le_mul_of_nonneg_left hVform (by positivity : (0 : Real) <=
      2400 * ((J : Real) + 1) / eps ^ 2)
    rw [div_mul_eq_mul_div, div_le_iff₀ hepsSq0] at hmul
    nlinarith
  have h42 : (42 : Real) <= 2400 * ((J : Real) + 1) / eps ^ 2 := by
    rw [le_div_iff₀ hepsSq0]
    nlinarith
  have hthreshold : concreteEstimatorSampleThreshold J (eps / 4) <=
      2400 * ((J : Real) + 1) / eps ^ 2 := by
    unfold concreteEstimatorSampleThreshold
    exact max_le h42 (max_le hA hB)
  have hk := concreteEstimatorSamples_cast_lt J (by positivity : 0 < eps / 4)
  have hJ := concrete_source_terminalChunk_lt hn hC hsource
  dsimp only [J] at hJ hthreshold hk ⊢
  have htwo : (2 : Real) <= 2400 * ((J : Real) + 1) / eps ^ 2 := by
    rw [le_div_iff₀ hepsSq0]
    nlinarith
  have hk' : (concreteEstimatorSamples J (eps / 4) : Real) <
      4800 * ((J : Real) + 1) / eps ^ 2 := by
    calc
      _ < concreteEstimatorSampleThreshold J (eps / 4) + 2 := hk
      _ <= 2400 * ((J : Real) + 1) / eps ^ 2 +
          2400 * ((J : Real) + 1) / eps ^ 2 := add_le_add hthreshold htwo
      _ = 4800 * ((J : Real) + 1) / eps ^ 2 := by ring
  calc
    _ < 4800 * ((J : Real) + 1) / eps ^ 2 := hk'
    _ < 4800 * (16 * C ^ 2 * (n : Real) ^ 2 + 3) / eps ^ 2 := by
      have hJ' : (J : Real) + 1 < 16 * C ^ 2 * (n : Real) ^ 2 + 3 := by linarith
      gcongr

/-- Fully concrete discharge of `RunwiseRadiusFourTailFits`, with the unavoidable explicit
polynomial-versus-exponential side condition.  The endpoint and estimator accuracies are both
`eps/4`, as in the standard final relative-error composition. -/
theorem concrete_source_runwiseRadiusFourTailFits
    {n : Nat} {C eps : Real} (hn : 21 <= n) (hC : 0 < C)
    (heps : 0 < eps) (heps1 : eps <= 1)
    (hsource : (1 / 2 : Real) ^ n <= eps / 4)
    (henvelope :
      (80 * C ^ 2 * (n : Real) ^ 2 + 3) *
          (4800 * (16 * C ^ 2 * (n : Real) ^ 2 + 3) / eps ^ 2) *
          (1 / 256 : Real) ^ n <= 1 / 20) :
    let s0 := polynomialEndpointSigmaSq n (eps / 4)
    let J := adaptiveTerminalChunk (C ^ 2 * n) s0
    RunwiseRadiusFourTailFits n (terminalPhaseCount n C s0)
      (concreteEstimatorSamples J (eps / 4)) := by
  dsimp only
  apply runwiseRadiusFourTailFits_of_calls_mul_pow_le
  have hm := concrete_source_phaseCount_lt (show 1 <= n by omega) hC hsource
  push_cast at hm
  have hk := concrete_source_estimatorSamples_lt (show 1 <= n by omega) hC heps heps1 hsource
  have hpow : 0 <= (1 / 256 : Real) ^ n := by positivity
  unfold runwiseSamplerCalls
  push_cast
  calc
    ((terminalPhaseCount n C (polynomialEndpointSigmaSq n (eps / 4)) : Real) + 1) *
          (concreteEstimatorSamples
            (adaptiveTerminalChunk (C ^ 2 * n) (polynomialEndpointSigmaSq n (eps / 4)))
            (eps / 4) : Real) * (1 / 256 : Real) ^ n
        <= (80 * C ^ 2 * (n : Real) ^ 2 + 3) *
            (4800 * (16 * C ^ 2 * (n : Real) ^ 2 + 3) / eps ^ 2) *
            (1 / 256 : Real) ^ n := by
          apply mul_le_mul_of_nonneg_right _ hpow
          exact mul_le_mul hm.le hk.le (by positivity) (by positivity)
    _ <= 1 / 20 := henvelope

#print axioms radiusFourTail_le_two_pow_neg_eight
#print axioms concrete_source_terminalChunk_lt
#print axioms concrete_source_phaseCount_lt
#print axioms concrete_source_estimatorSamples_lt
#print axioms concrete_source_runwiseRadiusFourTailFits

end Ttc.CVAdaptive
