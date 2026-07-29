/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Analysis.Arith
import Ttc.Model.Prelude

/-!
# What the algorithm's constants are chosen to satisfy

`Ttc.Params` (`Model/Prelude`) defines the five quantities `TTC` (`alg:ttc`) and
`GetPrecision` (`alg:prec`) compute before the main loop. Each is a *choice*, and
each is chosen to make one specific inequality of the analysis true. This module
proves exactly those inequalities:

| Paper | Definition | Chosen so that | Proved here |
| --- | --- | --- | --- |
| `ε' ← ε/12` | `Params.epsPrime` | the two-sided `(1±ε')` losses fit inside `(1±ε/3)` | `epsPrime_window` |
| `κ` (`lem:nonconv`) | `Params.kappa` | `κ ≤ 2√(log(8r/η))` | `kappa_le` |
| `γ` (`alg:prec`, line 86) | `Params.gamma` | `κ/γ ≤ η/(32mn)` | `kappa_div_gamma_le` |
| ↳ what that buys | | `(1 + κ/γ)ⁿ ≤ 1 + η/(16m)` | `shell_factor_bound` |

If a constant in the paper changes, exactly one definition in `Model/Prelude`
changes and the corresponding theorem here either still compiles or does not.
-/

namespace Ttc

open Real

namespace Params

variable (P : Params)

/-! ## `η` is in range -/

theorem eta_pos : 0 < P.eta := by unfold eta; linarith [P.hε0]

theorem eta_le_one : P.eta ≤ 1 := by unfold eta; linarith [P.hε1]

/-! ## `κ` and `γ`: the ratio bound the shell argument consumes -/

theorem log_r_nonneg : 0 ≤ Real.log P.r := Real.log_nonneg P.hr

theorem log_eight_div_eta_nonneg : 0 ≤ Real.log (8 / P.eta) :=
  Real.log_nonneg (by rw [le_div_iff₀ P.eta_pos]; linarith [P.eta_le_one])

/-- `log(8r/η) = log(8/η) + log r`. -/
theorem log_split : Real.log (8 * P.r / P.eta) = Real.log (8 / P.eta) + Real.log P.r := by
  have hη := P.eta_pos
  rw [show (8 : ℝ) * P.r / P.eta = (8 / P.eta) * P.r by ring,
    Real.log_mul (by positivity) (by linarith [P.hr])]

theorem log_pos : 0 < Real.log (8 * P.r / P.eta) := by
  have h8 : Real.log 8 ≤ Real.log (8 / P.eta) := by
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ P.eta_pos]; nlinarith [P.eta_le_one]
  have : 0 < Real.log 8 := Real.log_pos (by norm_num)
  rw [P.log_split]; linarith [P.log_r_nonneg]

/-- **`κ ≤ 2√(log(8r/η))`.** The quantitative content of `√u + √v ≤ √(2(u+v))`. -/
theorem kappa_le : P.kappa ≤ 2 * Real.sqrt (Real.log (8 * P.r / P.eta)) := by
  rw [kappa, P.log_split]
  exact sqrt_two_mul_add_le P.log_eight_div_eta_nonneg P.log_r_nonneg

theorem kappa_nonneg : 0 ≤ P.kappa := by unfold kappa; positivity

theorem gamma_pos : 0 < P.gamma := by
  have hn : (1:ℝ) ≤ (P.n : ℝ) := by exact_mod_cast P.hn
  have hm : (1:ℝ) ≤ (P.m : ℝ) := by exact_mod_cast P.hm
  have := Real.sqrt_pos.2 P.log_pos
  have hc : 0 < 64 * (P.m : ℝ) * P.n / P.eta := div_pos (by nlinarith) P.eta_pos
  unfold gamma
  exact mul_pos hc this

/-- **The ratio bound `κ/γ ≤ η/(32mn)`.**

This is the hypothesis the shell argument of `lem:nonconv` consumes
(`Ttc.shell_bound` via `(1 + κ/γ)ⁿ ≤ 1 + η/(16m)`). It holds *exactly*, with no
slack, which is why `γ` must use the same logarithm argument as `κ`. -/
theorem kappa_div_gamma_le :
    P.kappa / P.gamma ≤ P.eta / (32 * P.m * P.n) := by
  have hn : (1:ℝ) ≤ (P.n : ℝ) := by exact_mod_cast P.hn
  have hm : (1:ℝ) ≤ (P.m : ℝ) := by exact_mod_cast P.hm
  have hsL : 0 < Real.sqrt (Real.log (8 * P.r / P.eta)) := Real.sqrt_pos.2 P.log_pos
  have hne : P.eta ≠ 0 := ne_of_gt P.eta_pos
  rw [div_le_iff₀ P.gamma_pos]
  refine le_trans P.kappa_le (le_of_eq ?_)
  unfold gamma
  field_simp
  ring


/-! ## The shell factor: what `κ/γ` buys -/

/-- **`(1 + κ/γ)ⁿ ≤ 1 + η/(16m)`.**

This is the paper's step "since `κ/γ ≤ η/(32mn)`, we have
`(1+κ/γ)ⁿ ≤ (1+η/(32mn))ⁿ ≤ 1+η/(16m)`", proved end to end from the definitions
of `κ` and `γ`. Feeding it to `Ttc.shell_bound` gives
`vol Q' ≤ (1 + η/16)·vol Q`. -/
theorem shell_factor_bound :
    (1 + P.kappa / P.gamma) ^ P.n ≤ 1 + P.eta / (16 * P.m) := by
  have hn : (1:ℝ) ≤ (P.n : ℝ) := by exact_mod_cast P.hn
  have hm : (1:ℝ) ≤ (P.m : ℝ) := by exact_mod_cast P.hm
  have hα0 : (0:ℝ) ≤ P.eta / (32 * P.m) := by
    have := P.eta_pos; positivity
  have hα1 : P.eta / (32 * P.m) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith [P.eta_le_one]
  -- `κ/γ ≤ (η/(32m))/n`
  have hstep : P.kappa / P.gamma ≤ (P.eta / (32 * P.m)) / (P.n : ℝ) := by
    refine le_trans P.kappa_div_gamma_le (le_of_eq ?_)
    field_simp
  have hbase : (0:ℝ) ≤ 1 + P.kappa / P.gamma := by
    have := P.kappa_nonneg; have := P.gamma_pos; positivity
  calc (1 + P.kappa / P.gamma) ^ P.n
      ≤ (1 + (P.eta / (32 * P.m)) / (P.n : ℝ)) ^ P.n :=
        pow_le_pow_left₀ hbase (by linarith) P.n
    _ ≤ 1 + 2 * (P.eta / (32 * P.m)) := one_add_div_pow_le P.hn hα0 hα1
    _ = 1 + P.eta / (16 * P.m) := by ring

/-! ## `ε'`: the sketch's interval -/

theorem epsPrime_pos : 0 < P.epsPrime := by unfold epsPrime; linarith [P.hε0]

theorem epsPrime_le_one : P.epsPrime ≤ 1 := by unfold epsPrime; linarith [P.hε1]

/-- **`ε' = ε/12` is exactly what makes the two-sided loss fit `ε/3`.** -/
theorem epsPrime_window :
    (1 - P.epsPrime) * (1 - P.ε / 8) ≥ 1 - P.ε / 3 ∧
      (1 + P.epsPrime) * (1 + P.ε / 8) ≤ 1 + P.ε / 3 := by
  have h0 := P.hε0
  have h1 := P.hε1
  unfold epsPrime
  refine ⟨by nlinarith [sq_nonneg P.ε], by nlinarith [sq_nonneg P.ε]⟩

end Params

end Ttc
