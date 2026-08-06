/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Ttc.Constants.Arith
import Ttc.Model.Prelude

/-!
# `lem:numlattice`: the epoch analysis of the streaming sketch

`lem:numlattice` asserts that `TtcCore` outputs an estimate within `(1 ± ε/2)` of
`|Q ∩ 𝕃ⁿ| / 10^(ρ·n)` with probability at least `1 − δ`. Its proof (given in the
appendix) is a union bound over the *epochs* `j` — the successive halvings of the
sampling rate `p = 2^(−j)` — split into

* `Pr[⋃_{j ≥ j*} Noise(j)]`, the probability that `p` ever drops below the level
  where the sketch is still accurate, bounded by `δ/6` using the overflow
  estimate and a union bound over the `m` polytopes; and
* `∑_{j < j*} Pr[Err(j)]`, bounded by `δ/6` using a Chernoff estimate per epoch
  and summing a doubly-exponential series.

This file proves that entire deductive skeleton, plus the two interval
computations that justify the constants chosen in Algorithm 1. What remains
assumed is only the *Poisson–Chernoff estimate itself* (the paper's
`lem:chernoff`, cited to Soos et al.) and the distributional invariant, which is
`Ttc.poisson_splitting` in `Ttc/Poisson.lean`.

## What this verifies about the algorithm's constants

Algorithm 1 sets

* `ε' ← ε/12` (line 18), and
* `Thresh ← max(24·ln(24/δ)/((1−ε')ε'²), 15(ln(6/δ) + ln m))` (line 20).

`Ttc.sketch_interval` shows `ε' = ε/12` is exactly what makes the three-sided
`(1 ± ε')³` loss fit inside `(1 ± ε/2)`; `Ttc.err_sum_le_delta` and
`Ttc.noise_bound_le_delta` show the two branches of the `max` are exactly what
make each failure branch `δ/6`. Both constants are therefore confirmed correct
(indeed with slack: the total failure probability comes out at `δ/3`).
-/

namespace Ttc

open Finset Real

/-! ## The doubly-exponential series -/

/-- `t + 1 ≤ 2^t` over the reals. -/
theorem nat_succ_le_two_pow (t : ℕ) : (t : ℝ) + 1 ≤ 2 ^ t := by
  induction t with
  | zero => norm_num
  | succ k ih =>
      have h2 : (0:ℝ) < 2 ^ k := by positivity
      have hk : (1:ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      push_cast
      calc (k : ℝ) + 1 + 1 ≤ 2 ^ k + 2 ^ k := by linarith
        _ = 2 ^ (k + 1) := by ring

/-- Each term of the epoch series decays geometrically: for `a ≥ log 2`,
`exp (−a·2ᵗ) ≤ exp (−a)·2⁻ᵗ`. -/
theorem exp_two_pow_le {a : ℝ} (ha : Real.log 2 ≤ a) (t : ℕ) :
    Real.exp (-(a * 2 ^ t)) ≤ Real.exp (-a) * (1 / 2) ^ t := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hstep : a + t * Real.log 2 ≤ a * 2 ^ t := by
    have h1 : (t : ℝ) ≤ 2 ^ t - 1 := by linarith [nat_succ_le_two_pow t]
    have h2 : (t : ℝ) * Real.log 2 ≤ (2 ^ t - 1) * a := by
      calc (t : ℝ) * Real.log 2 ≤ (2 ^ t - 1) * Real.log 2 := by
            apply mul_le_mul_of_nonneg_right h1 (le_of_lt hlog2)
        _ ≤ (2 ^ t - 1) * a := by
            apply mul_le_mul_of_nonneg_left ha (by linarith)
    linarith
  have hlogpow : Real.log ((2:ℝ) ^ t) = (t:ℝ) * Real.log 2 := by
    rw [Real.log_pow]
  have hpow : Real.exp (-((t:ℝ) * Real.log 2)) = (1 / 2 : ℝ) ^ t := by
    rw [← hlogpow, Real.exp_neg, Real.exp_log (by positivity), one_div, inv_pow]
  have hrw : Real.exp (-a) * (1 / 2) ^ t = Real.exp (-(a + (t:ℝ) * Real.log 2)) := by
    rw [neg_add, Real.exp_add, hpow]
  rw [hrw]
  exact Real.exp_le_exp.2 (by linarith)

/-- **The epoch series bound.** For `a ≥ log 2`,
`∑_{t < T} 2·exp(−a·2ᵗ) ≤ 4·exp(−a)`.

This is the paper's step
`2e^{−cT/24} + 2e^{−cT/12} + … ≤ 4e^{−cT/24}`. -/
theorem epoch_series_le {a : ℝ} (ha : Real.log 2 ≤ a) (T : ℕ) :
    ∑ t ∈ range T, 2 * Real.exp (-(a * 2 ^ t)) ≤ 4 * Real.exp (-a) := by
  have hstep : ∑ t ∈ range T, 2 * Real.exp (-(a * 2 ^ t))
      ≤ ∑ t ∈ range T, 2 * (Real.exp (-a) * (1 / 2) ^ t) := by
    refine sum_le_sum fun t _ => ?_
    exact mul_le_mul_of_nonneg_left (exp_two_pow_le ha t) (by norm_num)
  refine le_trans hstep ?_
  have hfac : ∑ t ∈ range T, 2 * (Real.exp (-a) * (1 / 2) ^ t)
      = 2 * Real.exp (-a) * ∑ t ∈ range T, (1 / (2:ℝ)) ^ t := by
    rw [mul_sum]; exact sum_congr rfl fun t _ => by ring
  rw [hfac]
  have hgeom : ∑ t ∈ range T, (1 / (2:ℝ)) ^ t ≤ 2 := sum_geometric_two_le T
  nlinarith [Real.exp_pos (-a)]

/-! ## The two failure branches -/

/-- **The `Err` branch is `δ/6`.** If
`Thresh ≥ 24·log(24/δ)/((1−ε')ε'²)` — the first argument of Algorithm 1's `max` —
then the epoch series is at most `δ/6`. -/
theorem err_sum_le_delta {δ ε' Thresh : ℝ} (hδ0 : 0 < δ) (_hδ1 : δ ≤ 1)
    (hε'0 : 0 < ε') (hε'1 : ε' < 1)
    (hT : 24 * Real.log (24 / δ) / ((1 - ε') * ε' ^ 2) ≤ Thresh) :
    4 * Real.exp (-((1 - ε') * ε' ^ 2 * Thresh / 24)) ≤ δ / 6 := by
  have hc : (0:ℝ) < (1 - ε') * ε' ^ 2 := by positivity
  -- the exponent dominates `log (24/δ)`
  have hexp : Real.log (24 / δ) ≤ (1 - ε') * ε' ^ 2 * Thresh / 24 := by
    rw [div_le_iff₀ hc] at hT
    linarith [hT]
  have hle : Real.exp (-((1 - ε') * ε' ^ 2 * Thresh / 24)) ≤ δ / 24 := by
    calc Real.exp (-((1 - ε') * ε' ^ 2 * Thresh / 24))
        ≤ Real.exp (-Real.log (24 / δ)) := Real.exp_le_exp.2 (by linarith)
      _ = (24 / δ)⁻¹ := by rw [Real.exp_neg, Real.exp_log (by positivity)]
      _ = δ / 24 := by rw [inv_div]
  linarith

/-- **The `Noise` branch is `δ/6`.** If
`Thresh ≥ 6(log(6/δ) + log m)` — the second argument of Algorithm 1's `max` — then
the union bound over the `m` polytopes of the overflow estimate `exp(−Thresh/6)`
is at most `δ/6`. -/
theorem noise_bound_le_delta {δ m Thresh : ℝ} (hδ0 : 0 < δ) (hm : 1 ≤ m)
    (hT : 6 * (Real.log (6 / δ) + Real.log m) ≤ Thresh) :
    m * Real.exp (-(Thresh / 6)) ≤ δ / 6 := by
  have hmpos : (0:ℝ) < m := by linarith
  have hsplit : Real.log (6 / δ) + Real.log m = Real.log (6 * m / δ) := by
    rw [show (6:ℝ) * m / δ = (6 / δ) * m by ring,
      Real.log_mul (by positivity) (by linarith)]
  have hexp : Real.log (6 * m / δ) ≤ Thresh / 6 := by rw [← hsplit]; linarith
  calc m * Real.exp (-(Thresh / 6))
      ≤ m * Real.exp (-Real.log (6 * m / δ)) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (le_of_lt hmpos)
    _ = m * (6 * m / δ)⁻¹ := by rw [Real.exp_neg, Real.exp_log (by positivity)]
    _ = δ / 6 := by field_simp

/-- **The failure probability of `lem:numlattice`.** The two branches together are at most
`δ/3 ≤ δ`, so Algorithm 1's `Thresh` is chosen with a factor-3 margin. -/
theorem numlattice_failure_bound {δ errSum noiseSum : ℝ} (hδ0 : 0 < δ)
    (herr : errSum ≤ δ / 6) (hnoise : noiseSum ≤ δ / 6) :
    errSum + noiseSum ≤ δ := by linarith

/-! ## The two oracle failure events, `E_vol` and `E_samp`

`alg:ttc` line 18 sets `δ' ← δ/(4m)`; line 24 calls `Vol_ED(P(cᵢ), ε', δ')` and
line 43 calls `GenerateSamples(P(cᵢ), Nᵢ, ρ, ε', δ')`, each once per polytope. So
each family of `m` calls fails with total probability at most `δ/4`, and
`¬E_vol ∧ ¬E_samp` costs `δ/2` in all — which is exactly the room the `4` in `δ'`
buys over the `2` of the version without `eq:sampler`.

The two branches of the epoch estimate give `δ/6` each, so the budget closes at
`δ/6 + δ/6 + δ/4 + δ/4 = 5δ/6 ≤ δ`. That is what the lemmas here record.
-/

/-- **The `m` `Vol_ED` calls cost `δ/4`, and so do the `m` `GenerateSamples`
calls** — this is what `δ' = δ/(4m)` (`alg:ttc` line 18) is for. -/
theorem Params.vol_failure_eq (P : Params) : (P.m : ℝ) * P.deltaPrime = P.δ / 4 := by
  have hm : (1:ℝ) ≤ (P.m : ℝ) := by exact_mod_cast P.hm
  unfold Params.deltaPrime
  field_simp

/-- **Both oracle families together cost `δ/2`.** -/
theorem Params.oracle_failure_eq (P : Params) :
    (P.m : ℝ) * P.deltaPrime + (P.m : ℝ) * P.deltaPrime = P.δ / 2 := by
  rw [P.vol_failure_eq]; ring

/-- **The failure budget with both oracle families included.** The paper's two
branches give `δ/6` each, the `m` volume oracles `δ/4` and the `m` samplers a
further `δ/4`; the total is `5δ/6 ≤ δ`, so `lem:numlattice`'s conclusion survives
— with `δ/6` to spare. -/
theorem numlattice_failure_bound_with_vol {δ errSum noiseSum volSum sampSum : ℝ} (hδ0 : 0 < δ)
    (herr : errSum ≤ δ / 6) (hnoise : noiseSum ≤ δ / 6) (hvol : volSum ≤ δ / 4)
    (hsamp : sampSum ≤ δ / 4) :
    errSum + noiseSum + volSum + sampSum ≤ δ := by linarith

/-! ## The interval computation behind `ε' = ε/12` -/

/-- **Why `ε' = ε/12` works.** The invariant loses a factor `(1 ± ε')` three times
— once for the almost-uniformity of `GenerateSamples` (`eq:sampler`), once for
`Vol_ED` inside the Poisson rate `q_j`, and once in the concentration of `|X|` —
so the estimate `|X|/p` sits in `[(1−ε')³·L, (1+ε')³·L]`. With `ε' = ε/12` that is
inside `[(1−ε/2)L, (1+ε/2)L]`, which is `lem:numlattice`'s conclusion.

(`ε/3` would **not** do: `(1 + ε/12)³ ≥ 1 + ε/4` already, and `lem:lattice`'s
`(1±ε/8)` is still to come.) -/
theorem sketch_interval {ε L est : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hL : 0 ≤ L)
    (hlo : (1 - ε / 12) ^ 3 * L ≤ est) (hhi : est ≤ (1 + ε / 12) ^ 3 * L) :
    (1 - ε / 2) * L ≤ est ∧ est ≤ (1 + ε / 2) * L := by
  have h2 : ε ^ 2 ≤ ε := by nlinarith
  have h3 : ε ^ 3 ≤ ε := by nlinarith
  have h3nn : (0:ℝ) ≤ ε ^ 3 := by positivity
  constructor
  · refine le_trans ?_ hlo
    apply mul_le_mul_of_nonneg_right _ hL
    nlinarith
  · refine le_trans hhi ?_
    apply mul_le_mul_of_nonneg_right _ hL
    nlinarith

/-- The rate window of the invariant: if the per-point Poisson rate `q` lies in
`[(1−ε')²·2^(−j)/10^(ρn), (1+ε')²·2^(−j)/10^(ρn)]` — one `(1±ε')` from `Vol_ED`,
one from the almost-uniformity of `GenerateSamples` (`eq:sampler`) — and `|X|`
concentrates to within `(1 ± ε')` of `q·|Q ∩ 𝕃ⁿ|`, then `|X|/p` with `p = 2^(−j)`
lies in `[(1−ε')³L, (1+ε')³L]` for `L = |Q ∩ 𝕃ⁿ|/10^(ρn)`.

Note `q` is **per point**: an almost-uniform sampler gives each lattice point its
own rate inside this window, which is why the statement quantifies over a single
`q` and the caller sums. -/
theorem sketch_window {ε' N c p q card est : ℝ} (hε'0 : 0 < ε') (hε'1 : ε' < 1)
    (hp : 0 < p) (hc : 0 < c) (hN : 0 ≤ N)
    (hq_lo : (1 - ε') ^ 2 * (p / c) ≤ q) (hq_hi : q ≤ (1 + ε') ^ 2 * (p / c))
    (hcard_lo : (1 - ε') * (q * N) ≤ card) (hcard_hi : card ≤ (1 + ε') * (q * N))
    (hest : est = card / p) :
    (1 - ε') ^ 3 * (N / c) ≤ est ∧ est ≤ (1 + ε') ^ 3 * (N / c) := by
  have hqpos : 0 ≤ q := le_trans (by positivity) hq_lo
  subst hest
  constructor
  · rw [le_div_iff₀ hp]
    have h1 : (1 - ε') * ((1 - ε') ^ 2 * (p / c) * N) ≤ (1 - ε') * (q * N) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact mul_le_mul_of_nonneg_right hq_lo hN
    have h2 : (1 - ε') ^ 3 * (N / c) * p = (1 - ε') * ((1 - ε') ^ 2 * (p / c) * N) := by
      field_simp
    linarith
  · rw [div_le_iff₀ hp]
    have h1 : (1 + ε') * (q * N) ≤ (1 + ε') * ((1 + ε') ^ 2 * (p / c) * N) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact mul_le_mul_of_nonneg_right hq_hi hN
    have h2 : (1 + ε') ^ 3 * (N / c) * p = (1 + ε') * ((1 + ε') ^ 2 * (p / c) * N) := by
      field_simp
    linarith

end Ttc
