/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.AdaptiveChunkEndpoints
import Arlib.Convexity.GaussianCooling.AdaptiveRestartWarm

/-!
# Polynomial size bounds for the adaptive CV schedule

The first terminal chunk is defined by `Nat.find`.  These lemmas give it an explicit coarse
upper bound and hence bound the flattened number of phases.  They are intentionally stated in
division form, so substituting the standard cold start `s₀ = 1/(4n)` immediately gives a
polynomial in `n` and the terminal target `N`.
-/

namespace Ttc.CVAdaptive

open Arlib.GaussianCooling.Chunked
open Ttc.CV.Adaptive

/-- The first terminal chunk occurs no later than `ceil (N/s₀) + 1`. -/
theorem adaptiveTerminalChunk_le_ceil_add_one {N s₀ : ℝ} (hN : 0 < N) (hs₀ : 0 < s₀) :
    adaptiveTerminalChunk N s₀ ≤ ⌈N / s₀⌉₊ + 1 := by
  let q : ℕ := ⌈N / s₀⌉₊ + 1
  have hx0 : 0 ≤ N / s₀ := by positivity
  have hqgt : N / s₀ < (q : ℝ) := by
    dsimp [q]
    push_cast
    linarith [Nat.le_ceil (N / s₀)]
  have hNq : N < (q : ℝ) * s₀ := by
    rw [div_lt_iff₀ hs₀] at hqgt
    exact hqgt
  have hqpow : (q : ℝ) ≤ 2 ^ q := Ttc.CV.Adaptive.natCast_le_two_pow q
  have htarget : N ≤ adaptiveChunkStart N s₀ q := by
    calc
      N ≤ (q : ℝ) * s₀ := hNq.le
      _ ≤ 2 ^ q * s₀ := mul_le_mul_of_nonneg_right hqpow hs₀.le
      _ ≤ adaptiveChunkStart N s₀ q := pow_two_mul_le_adaptiveChunkStart hN hs₀ q
  have hex := exists_target_le_adaptiveChunkStart hN hs₀
  rw [adaptiveTerminalChunk, dif_pos hex]
  exact Nat.find_min' hex htarget

/-- Coarse real bound on the terminal chunk index. -/
theorem adaptiveTerminalChunk_lt_div_add_two {N s₀ : ℝ} (hN : 0 < N) (hs₀ : 0 < s₀) :
    (adaptiveTerminalChunk N s₀ : ℝ) < N / s₀ + 2 := by
  have hle := adaptiveTerminalChunk_le_ceil_add_one hN hs₀
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ N / s₀ by positivity)
  have hle' : (adaptiveTerminalChunk N s₀ : ℝ) ≤ (⌈N / s₀⌉₊ : ℝ) + 1 := by
    exact_mod_cast hle
  linarith

/-- The complete accelerated Gaussian block has fewer than `5N/s₀+2` phases. -/
theorem adaptiveTerminalOffset_lt_five_mul_div_add_two {N s₀ : ℝ}
    (hN : 0 < N) (hs₀ : 0 < s₀) :
    (adaptiveChunkOffset N s₀ (adaptiveTerminalChunk N s₀) : ℝ) <
      5 * N / s₀ + 2 := by
  have hphase := adaptiveTotalPhases_le hN hs₀ (adaptiveTerminalChunk N s₀)
  rw [adaptiveChunkOffset_eq_totalPhases]
  have hJ := adaptiveTerminalChunk_lt_div_add_two hN hs₀
  have harith : 4 * N / s₀ + (N / s₀ + 2) = 5 * N / s₀ + 2 := by ring
  calc
    (adaptiveTotalPhases N s₀ (adaptiveTerminalChunk N s₀) : ℝ) ≤
        4 * N / s₀ + adaptiveTerminalChunk N s₀ := hphase
    _ < 5 * N / s₀ + 2 := by linarith

/-- The logarithm of the independent-restart warmness constant is explicitly polynomial
throughout the terminal schedule. -/
theorem log_adaptiveRestartWarmConst_le_terminal_poly {n : ℕ} {N s₀ : ℝ}
    (hN : 0 < N) (hs₀ : 0 < s₀)
    {i : ℕ} (hi : i < adaptiveChunkOffset N s₀ (adaptiveTerminalChunk N s₀)) :
    Real.log (adaptiveRestartWarmConst n i) ≤
      (1 + (n : ℝ) * (5 * N / s₀ + 2)) * Real.log 2 := by
  rw [log_adaptiveRestartWarmConst]
  have hi' : (i : ℝ) < 5 * N / s₀ + 2 := by
    have hiCast : (i : ℝ) <
        (adaptiveChunkOffset N s₀ (adaptiveTerminalChunk N s₀) : ℝ) := by
      exact_mod_cast hi
    exact hiCast.trans (adaptiveTerminalOffset_lt_five_mul_div_add_two hN hs₀)
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  push_cast
  have : 1 + (n : ℝ) * i ≤ 1 + (n : ℝ) * (5 * N / s₀ + 2) := by
    simpa [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left hi'.le hn0) 1
  exact mul_le_mul_of_nonneg_right this hlog.le

#print axioms adaptiveTerminalChunk_le_ceil_add_one
#print axioms adaptiveTerminalOffset_lt_five_mul_div_add_two
#print axioms log_adaptiveRestartWarmConst_le_terminal_poly

end Ttc.CVAdaptive
