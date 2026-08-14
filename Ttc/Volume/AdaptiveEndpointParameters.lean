/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVAdaptiveTerminalOracleAccuracy

/-!
# Explicit endpoint and error parameters for the adaptive terminal oracle

We take the restart ball radius `rho = 1/2` and the Chernoff split `t = 1/2`.  For requested
cold-normalizer relative error `eta`, a deliberately conservative variance is

`s0 = eta / (32 * 2^n)`.

The exponential tail is then bounded without delicate logarithmic normalization, using only
`x <= exp x`: its exponential factor is at most `eta / (2 * 2^n)`, while the Gaussian
normalizer inflation is at most `2^n`.  This is stronger than the requested certificate by
a factor of two and simultaneously satisfies the cold-ball warm-start inequality.
-/

namespace Ttc.CVAdaptive

open MeasureTheory Metric Set
open Arlib.GaussianCooling

variable {n : Nat}

noncomputable def endpointRho : Real := 1 / 2

noncomputable def endpointChernoffT : Real := 1 / 2

noncomputable def endpointSigmaSq (n : Nat) (eta : Real) : Real :=
  eta / (32 * (2 : Real) ^ n)

theorem endpointRho_pos : 0 < endpointRho := by norm_num [endpointRho]

theorem endpointChernoffT_pos : 0 < endpointChernoffT := by
  norm_num [endpointChernoffT]

theorem endpointChernoffT_lt_one : endpointChernoffT < 1 := by
  norm_num [endpointChernoffT]

theorem endpointSigmaSq_pos {eta : Real} (heta : 0 < eta) :
    0 < endpointSigmaSq n eta := by
  unfold endpointSigmaSq
  positivity

theorem endpointRho_lt_shrink (hn : 2 <= n) :
    endpointRho < 1 - 1 / (2 * (n : Real)) := by
  have hnR : (1 : Real) <= n := by exact_mod_cast (show 1 <= n by omega)
  have hn2R : (2 : Real) <= n := by exact_mod_cast hn
  dsimp [endpointRho]
  have hnpos : (0 : Real) < n := lt_of_lt_of_le zero_lt_one hnR
  have hden : (0 : Real) < 2 * n := by positivity
  have hinv : 1 / (2 * (n : Real)) <= 1 / 4 := by
    rw [div_le_iff₀ hden]
    nlinarith
  linarith

/-- The same variance meets the cold-ball start condition for every `eta <= 1`. -/
theorem endpointSigmaSq_coldBall {eta : Real} (heta0 : 0 <= eta) (heta1 : eta <= 1) :
    4 * (n : Real) * endpointSigmaSq n eta <= endpointRho ^ 2 := by
  have hpow : (0 : Real) < (2 : Real) ^ n := by positivity
  have hnPow : (n : Real) <= (2 : Real) ^ n := Ttc.CV.Adaptive.natCast_le_two_pow n
  have hn0 : (0 : Real) <= n := by positivity
  have hneta : (n : Real) * eta <= (2 : Real) ^ n := by
    calc
      (n : Real) * eta <= (n : Real) * 1 := mul_le_mul_of_nonneg_left heta1 hn0
      _ = n := by ring
      _ <= (2 : Real) ^ n := hnPow
  unfold endpointSigmaSq endpointRho
  calc
    4 * (n : Real) * (eta / (32 * 2 ^ n)) =
        ((n : Real) * eta) / (8 * 2 ^ n) := by ring
    _ <= 1 / 8 := by
      rw [div_le_iff₀ (by positivity : (0 : Real) < 8 * 2 ^ n)]
      nlinarith
    _ <= (1 / 2 : Real) ^ 2 := by norm_num

/-- The complete geometric/numeric endpoint bundle in the dimension range used by the
radius-four walk. -/
theorem endpoint_parameter_bundle (hn : 21 <= n) {eta : Real}
    (heta : 0 < eta) (heta1 : eta <= 1) :
    0 < endpointSigmaSq n eta ∧
      0 < endpointRho ∧
      endpointRho < 1 - 1 / (2 * (n : Real)) ∧
      4 * (n : Real) * endpointSigmaSq n eta <= endpointRho ^ 2 ∧
      0 < endpointChernoffT ∧ endpointChernoffT < 1 := by
  exact ⟨endpointSigmaSq_pos heta, endpointRho_pos,
    endpointRho_lt_shrink (by omega), endpointSigmaSq_coldBall heta.le heta1,
    endpointChernoffT_pos, endpointChernoffT_lt_one⟩

/-- Elementary exponential estimate used by the explicit Chernoff certificate. -/
theorem exp_neg_le_inv_of_pos {x : Real} (hx : 0 < x) :
    Real.exp (-x) <= 1 / x := by
  have hxe : x <= Real.exp x := by
    linarith [Real.add_one_le_exp x]
  rw [Real.exp_neg, one_div]
  simpa [one_div] using one_div_le_one_div_of_le hx hxe

/-- The explicit `(rho,t,s0)` choice discharges the Gaussian Chernoff certificate. -/
theorem endpoint_chernoff_certificate {eta : Real} (heta : 0 < eta) :
    Real.exp (-(endpointChernoffT * endpointRho ^ 2) /
          (2 * endpointSigmaSq n eta)) *
        (2 * Real.pi * (endpointSigmaSq n eta / (1 - endpointChernoffT))) ^
          ((n : Real) / 2) <=
      eta * (2 * Real.pi * endpointSigmaSq n eta) ^ ((n : Real) / 2) := by
  let s := endpointSigmaSq n eta
  have hs : 0 < s := endpointSigmaSq_pos heta
  have hpown : (0 : Real) < (2 : Real) ^ n := by positivity
  let x : Real := 1 / (16 * s)
  have hx : 0 < x := by dsimp [x]; positivity
  have hxform : x = 2 * (2 : Real) ^ n / eta := by
    dsimp [x, s, endpointSigmaSq]
    field_simp
    <;> ring
  have hexp : Real.exp (-x) <= eta / (2 * (2 : Real) ^ n) := by
    calc
      Real.exp (-x) <= 1 / x := exp_neg_le_inv_of_pos hx
      _ = eta / (2 * (2 : Real) ^ n) := by rw [hxform]; field_simp
  have hn0 : (0 : Real) <= n := by positivity
  have hhalf : (n : Real) / 2 <= (n : Real) := by linarith
  have hrpow : (2 : Real) ^ ((n : Real) / 2) <= (2 : Real) ^ n := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hhalf
  have hbase :
      2 * Real.pi * (s / (1 - endpointChernoffT)) =
        2 * (2 * Real.pi * s) := by
    dsimp [endpointChernoffT]
    field_simp
    ring
  have htailRewrite :
      -(endpointChernoffT * endpointRho ^ 2) / (2 * s) = -x := by
    dsimp [endpointChernoffT, endpointRho, x]
    field_simp
    ring
  rw [show endpointSigmaSq n eta = s by rfl, htailRewrite, hbase,
    Real.mul_rpow (by norm_num : (0 : Real) <= 2)
      (by positivity : (0 : Real) <= 2 * Real.pi * s)]
  calc
    Real.exp (-x) *
        ((2 : Real) ^ ((n : Real) / 2) *
          (2 * Real.pi * s) ^ ((n : Real) / 2))
      <= (eta / (2 * 2 ^ n)) *
        ((2 : Real) ^ n * (2 * Real.pi * s) ^ ((n : Real) / 2)) := by
          gcongr
    _ = (eta / 2) * (2 * Real.pi * s) ^ ((n : Real) / 2) := by
          field_simp
    _ <= eta * (2 * Real.pi * s) ^ ((n : Real) / 2) := by
          gcongr
          linarith

/-- The concrete cold endpoint is within `eta` relative error of the known ambient
normalizer. -/
theorem G_indicator_mem_relErr_explicit_endpoint
    {K : Set (Ttc.Space n)} (hKm : MeasurableSet K)
    (hball : closedBall (0 : Ttc.Space n) endpointRho ⊆ K)
    {eta : Real} (heta : 0 < eta) :
    Arlib.GaussianCooling.G (indicator K (1 : Ttc.Space n -> Real))
        (endpointSigmaSq n eta) ∈
      Ttc.relErr eta
        ((2 * Real.pi * endpointSigmaSq n eta) ^ ((n : Real) / 2)) := by
  exact Ttc.CV.G_indicator_mem_relErr_ambient_of_chernoff hKm
    (endpointSigmaSq_pos heta) endpointRho_pos.le endpointChernoffT_pos
    endpointChernoffT_lt_one heta.le hball (endpoint_chernoff_certificate heta)

/-- Phase zero of any positive-length chain whose initial variance is the explicit `s0`
is the same Gaussian integral used by the endpoint theorem. -/
theorem chain_zero_eq_G_explicit_endpoint {eta : Real} {m : Nat} (hm : 0 < m)
    {sigmaSq : Nat -> Real} (hsigma0 : sigmaSq 0 = endpointSigmaSq n eta)
    (K : Set (Ttc.Space n)) (hKm : MeasurableSet K) :
    chain m sigmaSq K 0 =
      G (indicator K (1 : Ttc.Space n -> Real)) (endpointSigmaSq n eta) := by
  rw [chain_of_lt hm K, hsigma0, Ttc.CV.G_indicator_eq K hKm]

/-- All cold-normalizer premises of the terminal oracle, at the explicit endpoint.

The first conclusion supplies `hcoldLe`; the second is `hcold`. -/
theorem chain_zero_explicit_endpoint_package {eta : Real} {m : Nat} (hm : 0 < m)
    {sigmaSq : Nat -> Real} (hsigma0 : sigmaSq 0 = endpointSigmaSq n eta)
    {K : Set (Ttc.Space n)} (hKm : MeasurableSet K) (hfin : volume K ≠ ⊤)
    (hn : 1 <= n) (hball : closedBall (0 : Ttc.Space n) endpointRho ⊆ K)
    (heta : 0 < eta) (heta1 : eta <= 1) :
    chain m sigmaSq K 0 <=
        (2 * Real.pi * endpointSigmaSq n eta) ^ ((n : Real) / 2) ∧
      chain m sigmaSq K 0 ∈ Ttc.relErr eta
        ((2 * Real.pi * endpointSigmaSq n eta) ^ ((n : Real) / 2)) := by
  have hs : 0 < endpointSigmaSq n eta := endpointSigmaSq_pos (n := n) heta
  have hcold := endpointSigmaSq_coldBall (n := n) heta.le heta1
  have hIcc := Ttc.CV.G_indicator_mem_coldNormalizer_Icc hKm hfin hn hs
    endpointRho_pos hcold hball
  have hrel := G_indicator_mem_relErr_explicit_endpoint hKm hball heta
  rw [← chain_zero_eq_G_explicit_endpoint hm hsigma0 K hKm] at hIcc hrel
  exact ⟨hIcc.2, hrel⟩

/-! ## Error-budget bookkeeping -/

/-- Splitting the requested failure probability evenly between estimator failure and the
tensorized sampler coupling gives exactly the requested total failure. -/
theorem half_failure_split (p : Real) : 1 - p / 2 - p / 2 = 1 - p := by ring

/-- If both the estimator and cold-normalizer relative errors are at most `epsilon/4`, the
terminal oracle's reported relative error is at most `2*epsilon/3`, hence below `epsilon`,
for `epsilon <= 1`. -/
theorem terminal_relative_error_split {epsilon epsEst eta : Real}
    (hepsilon0 : 0 <= epsilon) (hepsilon1 : epsilon <= 1)
    (hest0 : 0 <= epsEst) (hest : epsEst <= epsilon / 4)
    (heta0 : 0 <= eta) (heta : eta <= epsilon / 4) :
    (epsEst + eta) / (1 - eta) <= epsilon := by
  have heta14 : eta <= 1 / 4 := heta.trans (by linarith)
  have hden : 0 < 1 - eta := by linarith
  rw [div_le_iff₀ hden]
  nlinarith

/-- The tensor budget expected by the oracle follows from the direct per-coordinate choice
`b.toReal <= p/(2*r*(m+1)*k)`. -/
theorem tensor_budget_half_failure {r m k : Nat} {b p : Real}
    (hp0 : 0 <= p)
    (hb : b <= p / (2 * ((r * (m + 1) * k : Nat) : Real))) :
    (((r * (m + 1) * k : Nat) : Real) * b) <= p / 2 := by
  by_cases hcount : r * (m + 1) * k = 0
  · rw [hcount]
    norm_num
    exact div_nonneg hp0 (by norm_num)
  · have hpos : (0 : Real) < (r * (m + 1) * k : Nat) := by
      exact_mod_cast Nat.pos_of_ne_zero hcount
    calc
      ((r * (m + 1) * k : Nat) : Real) * b <=
          ((r * (m + 1) * k : Nat) : Real) *
            (p / (2 * ((r * (m + 1) * k : Nat) : Real))) :=
        mul_le_mul_of_nonneg_left hb hpos.le
      _ = p / 2 := by field_simp

/-! ### Axiom audit -/

#print axioms endpointSigmaSq_coldBall
#print axioms endpoint_parameter_bundle
#print axioms endpoint_chernoff_certificate
#print axioms G_indicator_mem_relErr_explicit_endpoint
#print axioms chain_zero_explicit_endpoint_package
#print axioms terminal_relative_error_split
#print axioms tensor_budget_half_failure

end Ttc.CVAdaptive
