/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.AdaptiveEndpointParameters

/-!
# Polynomial cold endpoint parameters

The source regime assumes `2^{-n} <= eta`.  Its initial variance is `1/(4n)` and its
Chernoff split is `t=3/4`.  For the independently restarted walk used by this repository,
the geometrically scaled choice `rho=1/2`, `s0=1/(16n)` has exactly the same tail exponent
and also satisfies `4*n*s0=rho^2`.

For completeness we also package an all-accuracy piecewise choice: use the scaled polynomial
endpoint in the source regime, and the existing arbitrary-accuracy endpoint outside it.
-/

namespace Ttc.CVAdaptive

open MeasureTheory Metric Set
open Arlib.GaussianCooling

variable {n : Nat}

noncomputable def sourceEndpointSigmaSq (n : Nat) : Real := 1 / (4 * (n : Real))

noncomputable def operationalEndpointSigmaSq (n : Nat) : Real := 1 / (16 * (n : Real))

noncomputable def sourceEndpointRho : Real := 1

noncomputable def sourceEndpointChernoffT : Real := 3 / 4

/-- The real-number heart already used by `ColdWarmStart`: under `4*n*s <= rho^2`, the
`t=3/4` Chernoff certificate has relative error at most `2^{-n}`. -/
theorem cold_chernoff_certificate_dyadic (hn : 1 <= n) {s rho : Real}
    (hs : 0 < s) (hrho : 0 < rho) (hcold : 4 * (n : Real) * s <= rho ^ 2) :
    Real.exp (-(sourceEndpointChernoffT * rho ^ 2) / (2 * s)) *
        (2 * Real.pi * (s / (1 - sourceEndpointChernoffT))) ^ ((n : Real) / 2) <=
      (1 / 2 : Real) ^ n * (2 * Real.pi * s) ^ ((n : Real) / 2) := by
  have hexp32 : (4 : Real) <= Real.exp (3 / 2) := by
    have hsum := Real.sum_le_exp_of_nonneg (x := (3 / 2 : Real)) (by norm_num) 4
    norm_num [Finset.sum_range_succ] at hsum ⊢
    linarith
  have hbase :
      2 * Real.pi * (s / (1 - sourceEndpointChernoffT)) =
        4 * (2 * Real.pi * s) := by
    dsimp [sourceEndpointChernoffT]
    ring
  have hfour : (4 : Real) ^ ((n : Real) / 2) = 2 ^ n := by
    have h4 : (4 : Real) = (2 : Real) ^ (2 : Real) := by
      rw [show (2 : Real) = ((2 : Nat) : Real) by norm_num, Real.rpow_natCast]
      norm_num
    rw [h4, ← Real.rpow_mul (by norm_num),
      show (2 : Real) * ((n : Real) / 2) = (n : Real) by ring,
      Real.rpow_natCast]
  have hrpow :
      (2 * Real.pi * (s / (1 - sourceEndpointChernoffT))) ^ ((n : Real) / 2) =
        2 ^ n * (2 * Real.pi * s) ^ ((n : Real) / 2) := by
    rw [hbase, Real.mul_rpow (by norm_num) (by positivity), hfour]
  have hquot :
      (3 : Real) * (n : Real) / 2 <=
        (sourceEndpointChernoffT * rho ^ 2) / (2 * s) := by
    dsimp [sourceEndpointChernoffT]
    rw [le_div_iff₀ (by positivity : (0 : Real) < 2 * s)]
    nlinarith
  have hE1 :
      Real.exp (-(sourceEndpointChernoffT * rho ^ 2) / (2 * s)) <=
        Real.exp (-(3 * (n : Real) / 2)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hE2 : Real.exp (-(3 * (n : Real) / 2)) <= (1 / 4 : Real) ^ n := by
    have hpow : (4 : Real) ^ n <= Real.exp (3 / 2) ^ n :=
      pow_le_pow_left₀ (by norm_num) hexp32 n
    have hE : Real.exp (3 / 2) ^ n = Real.exp (3 * (n : Real) / 2) := by
      rw [← Real.exp_nat_mul]
      ring_nf
    rw [hE] at hpow
    rw [Real.exp_neg, one_div, inv_pow]
    exact (inv_le_inv₀ (Real.exp_pos (3 * (n : Real) / 2))
      (pow_pos (by norm_num : (0 : Real) < 4) n)).2 hpow
  have htail :
      Real.exp (-(sourceEndpointChernoffT * rho ^ 2) / (2 * s)) * 2 ^ n <=
        (1 / 2 : Real) ^ n := by
    calc
      Real.exp (-(sourceEndpointChernoffT * rho ^ 2) / (2 * s)) * 2 ^ n <=
          (1 / 4 : Real) ^ n * 2 ^ n := by
        gcongr
        exact hE1.trans hE2
      _ = (1 / 2 : Real) ^ n := by rw [← mul_pow]; norm_num
  have hnn : 0 <= (2 * Real.pi * s) ^ ((n : Real) / 2) :=
    Real.rpow_nonneg (by positivity) _
  calc
    Real.exp (-(sourceEndpointChernoffT * rho ^ 2) / (2 * s)) *
        (2 * Real.pi * (s / (1 - sourceEndpointChernoffT))) ^ ((n : Real) / 2) =
      (Real.exp (-(sourceEndpointChernoffT * rho ^ 2) / (2 * s)) * 2 ^ n) *
        (2 * Real.pi * s) ^ ((n : Real) / 2) := by rw [hrpow]; ring
    _ <= (1 / 2 : Real) ^ n *
        (2 * Real.pi * s) ^ ((n : Real) / 2) :=
      mul_le_mul_of_nonneg_right htail hnn

theorem sourceEndpointSigmaSq_pos (hn : 1 <= n) : 0 < sourceEndpointSigmaSq n := by
  unfold sourceEndpointSigmaSq
  have : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  positivity

theorem sourceEndpointSigmaSq_cold (hn : 1 <= n) :
    4 * (n : Real) * sourceEndpointSigmaSq n <= sourceEndpointRho ^ 2 := by
  have hnR : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  unfold sourceEndpointSigmaSq sourceEndpointRho
  field_simp
  exact le_rfl

/-- The endpoint exactly matching `vol3_journal.tex`: `s0=1/(4n)`, containment radius one. -/
theorem sourceEndpoint_chernoff_certificate (hn : 1 <= n) :
    Real.exp (-(sourceEndpointChernoffT * sourceEndpointRho ^ 2) /
          (2 * sourceEndpointSigmaSq n)) *
        (2 * Real.pi * (sourceEndpointSigmaSq n /
          (1 - sourceEndpointChernoffT))) ^ ((n : Real) / 2) <=
      (1 / 2 : Real) ^ n *
        (2 * Real.pi * sourceEndpointSigmaSq n) ^ ((n : Real) / 2) := by
  exact cold_chernoff_certificate_dyadic hn (sourceEndpointSigmaSq_pos hn)
    (by norm_num [sourceEndpointRho]) (sourceEndpointSigmaSq_cold hn)

theorem operationalEndpointSigmaSq_pos (hn : 1 <= n) :
    0 < operationalEndpointSigmaSq n := by
  unfold operationalEndpointSigmaSq
  have : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  positivity

theorem operationalEndpointSigmaSq_cold (hn : 1 <= n) :
    4 * (n : Real) * operationalEndpointSigmaSq n <= endpointRho ^ 2 := by
  have hnR : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  unfold operationalEndpointSigmaSq endpointRho
  field_simp
  norm_num

/-- Operationally compatible scaling: `s0=1/(16n)`, `rho=1/2`, with the same dyadic tail. -/
theorem operationalEndpoint_chernoff_certificate (hn : 1 <= n) :
    Real.exp (-(sourceEndpointChernoffT * endpointRho ^ 2) /
          (2 * operationalEndpointSigmaSq n)) *
        (2 * Real.pi * (operationalEndpointSigmaSq n /
          (1 - sourceEndpointChernoffT))) ^ ((n : Real) / 2) <=
      (1 / 2 : Real) ^ n *
        (2 * Real.pi * operationalEndpointSigmaSq n) ^ ((n : Real) / 2) := by
  exact cold_chernoff_certificate_dyadic hn (operationalEndpointSigmaSq_pos hn)
    endpointRho_pos (operationalEndpointSigmaSq_cold hn)

theorem G_indicator_mem_relErr_operational_endpoint
    {K : Set (Ttc.Space n)} (hKm : MeasurableSet K)
    (hball : closedBall (0 : Ttc.Space n) endpointRho ⊆ K)
    (hn : 1 <= n) {eta : Real} (hdyadic : (1 / 2 : Real) ^ n <= eta) :
    G (indicator K (1 : Ttc.Space n -> Real)) (operationalEndpointSigmaSq n) ∈
      Ttc.relErr eta
        ((2 * Real.pi * operationalEndpointSigmaSq n) ^ ((n : Real) / 2)) := by
  have hsmall := Ttc.CV.G_indicator_mem_relErr_ambient_of_chernoff hKm
    (operationalEndpointSigmaSq_pos hn) endpointRho_pos.le
    (by norm_num [sourceEndpointChernoffT]) (by norm_num [sourceEndpointChernoffT])
    (by positivity : 0 <= (1 / 2 : Real) ^ n) hball
    (operationalEndpoint_chernoff_certificate hn)
  have hbase : 0 <= 2 * Real.pi * operationalEndpointSigmaSq n := by
    positivity [operationalEndpointSigmaSq_pos hn]
  exact Ttc.CV.relErr_mono hdyadic
    (Real.rpow_nonneg hbase _) hsmall

/-! ## Piecewise all-accuracy choice -/

noncomputable def polynomialEndpointSigmaSq (n : Nat) (eta : Real) : Real :=
  if (1 / 2 : Real) ^ n <= eta then operationalEndpointSigmaSq n
  else endpointSigmaSq n eta

noncomputable def polynomialEndpointChernoffT (n : Nat) (eta : Real) : Real :=
  if (1 / 2 : Real) ^ n <= eta then sourceEndpointChernoffT
  else endpointChernoffT

theorem polynomialEndpointSigmaSq_pos (hn : 1 <= n) {eta : Real} (heta : 0 < eta) :
    0 < polynomialEndpointSigmaSq n eta := by
  by_cases h : (1 / 2 : Real) ^ n <= eta
  · rw [polynomialEndpointSigmaSq, if_pos h]
    exact operationalEndpointSigmaSq_pos hn
  · rw [polynomialEndpointSigmaSq, if_neg h]
    exact endpointSigmaSq_pos heta

theorem polynomialEndpointSigmaSq_coldBall (hn : 1 <= n) {eta : Real}
    (heta : 0 < eta) (heta1 : eta <= 1) :
    4 * (n : Real) * polynomialEndpointSigmaSq n eta <= endpointRho ^ 2 := by
  by_cases h : (1 / 2 : Real) ^ n <= eta
  · rw [polynomialEndpointSigmaSq, if_pos h]
    exact operationalEndpointSigmaSq_cold hn
  · rw [polynomialEndpointSigmaSq, if_neg h]
    exact endpointSigmaSq_coldBall (n := n) heta.le heta1

/-- The inverse variance governing the adaptive phase count is polynomial in `n` and
`1/eta`.  In the source branch it is exactly `16*n`; in the smaller-error branch the
dyadic test turns the old expression into the displayed quadratic bound. -/
theorem polynomialEndpointSigmaSq_inv_le_max (hn : 1 <= n) {eta : Real}
    (heta : 0 < eta) :
    (polynomialEndpointSigmaSq n eta)⁻¹ <=
      max (16 * (n : Real)) (32 / eta ^ 2) := by
  have hnR : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  by_cases h : (1 / 2 : Real) ^ n <= eta
  · rw [polynomialEndpointSigmaSq, if_pos h]
    have heq : (operationalEndpointSigmaSq n)⁻¹ = 16 * (n : Real) := by
      unfold operationalEndpointSigmaSq
      field_simp
    rw [heq]
    exact le_max_left _ _
  · rw [polynomialEndpointSigmaSq, if_neg h]
    have hp : (0 : Real) < (2 : Real) ^ n := by positivity
    have hsmall : eta < 1 / (2 : Real) ^ n := by
      simpa [div_pow] using lt_of_not_ge h
    have hpow : (2 : Real) ^ n < 1 / eta := by
      rw [lt_div_iff₀ heta]
      rw [lt_div_iff₀ hp] at hsmall
      nlinarith
    have heq : (endpointSigmaSq n eta)⁻¹ = 32 * (2 : Real) ^ n / eta := by
      unfold endpointSigmaSq
      field_simp
    rw [heq]
    apply le_max_of_le_right
    calc
      32 * (2 : Real) ^ n / eta <= 32 * (1 / eta) / eta := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow.le (by norm_num)) heta.le
      _ = 32 / eta ^ 2 := by field_simp

theorem polynomialEndpoint_chernoff_certificate (hn : 1 <= n) {eta : Real}
    (heta : 0 < eta) :
    Real.exp (-(polynomialEndpointChernoffT n eta * endpointRho ^ 2) /
          (2 * polynomialEndpointSigmaSq n eta)) *
        (2 * Real.pi * (polynomialEndpointSigmaSq n eta /
          (1 - polynomialEndpointChernoffT n eta))) ^ ((n : Real) / 2) <=
      eta * (2 * Real.pi * polynomialEndpointSigmaSq n eta) ^ ((n : Real) / 2) := by
  by_cases h : (1 / 2 : Real) ^ n <= eta
  · simp only [polynomialEndpointChernoffT, polynomialEndpointSigmaSq, if_pos h]
    have hbase : 0 <= 2 * Real.pi * operationalEndpointSigmaSq n := by
      positivity [operationalEndpointSigmaSq_pos hn]
    exact (operationalEndpoint_chernoff_certificate hn).trans
      (mul_le_mul_of_nonneg_right h
        (Real.rpow_nonneg hbase _))
  · simp only [polynomialEndpointChernoffT, polynomialEndpointSigmaSq, if_neg h]
    exact endpoint_chernoff_certificate heta

theorem G_indicator_mem_relErr_polynomial_endpoint
    {K : Set (Ttc.Space n)} (hKm : MeasurableSet K)
    (hball : closedBall (0 : Ttc.Space n) endpointRho ⊆ K)
    (hn : 1 <= n) {eta : Real} (heta : 0 < eta) :
    G (indicator K (1 : Ttc.Space n -> Real)) (polynomialEndpointSigmaSq n eta) ∈
      Ttc.relErr eta
        ((2 * Real.pi * polynomialEndpointSigmaSq n eta) ^ ((n : Real) / 2)) := by
  have ht0 : 0 < polynomialEndpointChernoffT n eta := by
    by_cases h : (1 / 2 : Real) ^ n <= eta
    · rw [polynomialEndpointChernoffT, if_pos h]
      norm_num [sourceEndpointChernoffT]
    · rw [polynomialEndpointChernoffT, if_neg h]
      norm_num [endpointChernoffT]
  have ht1 : polynomialEndpointChernoffT n eta < 1 := by
    by_cases h : (1 / 2 : Real) ^ n <= eta
    · rw [polynomialEndpointChernoffT, if_pos h]
      norm_num [sourceEndpointChernoffT]
    · rw [polynomialEndpointChernoffT, if_neg h]
      norm_num [endpointChernoffT]
  exact Ttc.CV.G_indicator_mem_relErr_ambient_of_chernoff hKm
    (polynomialEndpointSigmaSq_pos hn heta) endpointRho_pos.le ht0 ht1 heta.le hball
    (polynomialEndpoint_chernoff_certificate hn heta)

/-- Phase zero of a positive-length chain at the polynomial endpoint is the corresponding
restricted Gaussian integral. -/
theorem chain_zero_eq_G_polynomial_endpoint {eta : Real} {m : Nat} (hm : 0 < m)
    {sigmaSq : Nat -> Real} (hsigma0 : sigmaSq 0 = polynomialEndpointSigmaSq n eta)
    (K : Set (Ttc.Space n)) (hKm : MeasurableSet K) :
    chain m sigmaSq K 0 =
      G (indicator K (1 : Ttc.Space n -> Real)) (polynomialEndpointSigmaSq n eta) := by
  rw [chain_of_lt hm K, hsigma0, Ttc.CV.G_indicator_eq K hKm]

/-- The two cold-normalizer facts consumed by the concrete terminal estimator, now with the
all-accuracy endpoint whose reciprocal is polynomial in `n` and `1/eta`. -/
theorem chain_zero_polynomial_endpoint_package {eta : Real} {m : Nat} (hm : 0 < m)
    {sigmaSq : Nat -> Real} (hsigma0 : sigmaSq 0 = polynomialEndpointSigmaSq n eta)
    {K : Set (Ttc.Space n)} (hKm : MeasurableSet K) (hfin : volume K ≠ ⊤)
    (hn : 1 <= n) (hball : closedBall (0 : Ttc.Space n) endpointRho ⊆ K)
    (heta : 0 < eta) (heta1 : eta <= 1) :
    chain m sigmaSq K 0 <=
        (2 * Real.pi * polynomialEndpointSigmaSq n eta) ^ ((n : Real) / 2) ∧
      chain m sigmaSq K 0 ∈ Ttc.relErr eta
        ((2 * Real.pi * polynomialEndpointSigmaSq n eta) ^ ((n : Real) / 2)) := by
  have hs : 0 < polynomialEndpointSigmaSq n eta :=
    polynomialEndpointSigmaSq_pos hn heta
  have hcold := polynomialEndpointSigmaSq_coldBall hn heta heta1
  have hIcc := Ttc.CV.G_indicator_mem_coldNormalizer_Icc hKm hfin hn hs
    endpointRho_pos hcold hball
  have hrel := G_indicator_mem_relErr_polynomial_endpoint hKm hball hn heta
  rw [← chain_zero_eq_G_polynomial_endpoint hm hsigma0 K hKm] at hIcc hrel
  exact ⟨hIcc.2, hrel⟩

/-! ### Axiom audit -/

#print axioms sourceEndpoint_chernoff_certificate
#print axioms operationalEndpoint_chernoff_certificate
#print axioms G_indicator_mem_relErr_operational_endpoint
#print axioms polynomialEndpointSigmaSq_inv_le_max
#print axioms polynomialEndpoint_chernoff_certificate
#print axioms G_indicator_mem_relErr_polynomial_endpoint
#print axioms chain_zero_polynomial_endpoint_package

end Ttc.CVAdaptive
