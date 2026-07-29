/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Internal.Repair
import Ttc.Internal.Recentred
import Ttc.Internal.Lattice
import Ttc.Internal.Sketch

/-!
# The parameters the algorithm computes, and what they are chosen to satisfy

`TTC` (`alg:ttc`) and `GetPrecision` (`alg:prec`) compute five quantities before
the main loop runs. Each is a *choice*, and each is chosen to make one specific
inequality of the analysis true. This module defines them as functions and proves
exactly those inequalities.

| Paper | Here | Chosen so that |
| --- | --- | --- |
| `ε' ← ε/12` (`alg:ttc`, line 18) | `Ttc.Params.epsPrime` | the two-sided `(1±ε')` losses fit inside `(1±ε/3)` |
| `Thresh ← max(…)` (`alg:ttc`, line 20) | `Ttc.Params.thresh` | each failure branch of `lem:numlattice` is `δ/6` |
| `κ` (`lem:nonconv`) | `Ttc.Params.kappa` | the rounding tail bound is `η/(4r)` per facet |
| `γ` (`alg:prec`, line 86) | `Ttc.Params.gamma` | `κ/γ ≤ η/(32mn)`, the shell bound's input |
| `ρ ← ⌈log₁₀(γ/γ̂)⌉` (`alg:prec`) | `Ttc.Params.precision` | the fine lattice `𝕃ⁿ` is fine enough |

This module covers **only the scalars computed before the main loop**. The
loop itself is in `Ttc.Algorithm`. This module is the audit surface for the
constants: If a constant in the
paper changes, exactly one definition here changes and the corresponding theorem
either still compiles or does not.

## Note on `γ`

`γ` must be stated with the **same** logarithm argument as `κ`. With
`κ = √(2 log(8/η)) + √(2 log r)` one has `κ ≤ 2√(log(8r/η))`, so
`γ = (64mn/η)·√(log(8r/η))` gives `κ/γ ≤ η/(32mn)` exactly
(`Ttc.Params.kappa_div_gamma_le`). Using `√(log(4r/η))` in `γ` while `κ` is
computed at `8/η` leaves a residual factor `√(log(8r/η)/log(4r/η))`, which is up
to `√1.5 ≈ 1.23` — the bound then fails. See the README, finding 2.
-/

namespace Ttc

open Real

/-- The parameters the algorithm computes from its inputs. `n` is the dimension,
`m` the number of cubes in the DNF, `r` the total facet count. -/
structure Params where
  /-- The requested multiplicative accuracy. -/
  ε : ℝ
  /-- The requested failure probability. -/
  δ : ℝ
  /-- The ambient dimension. -/
  n : ℕ
  /-- The number of polytopes in the decomposition. -/
  m : ℕ
  /-- The total number of facets, `r = ∑ᵢ facet(Pᵢ)`. -/
  r : ℝ
  /-- Accuracy is in `(0,1]`. -/
  hε0 : 0 < ε
  /-- Accuracy is in `(0,1]`. -/
  hε1 : ε ≤ 1
  /-- The dimension is positive. -/
  hn : 1 ≤ n
  /-- There is at least one cube. -/
  hm : 1 ≤ m
  /-- There is at least one facet. -/
  hr : 1 ≤ r

namespace Params

variable (P : Params)

/-- `η ← ε/8`: the accuracy at which `GetPrecision` is called (`alg:ttc`, line 17). -/
noncomputable def eta : ℝ := P.ε / 8

/-- `ε' ← ε/12` (`alg:ttc`, line 18). -/
noncomputable def epsPrime : ℝ := P.ε / 12

/-- `Thresh ← max(24 ln(24/δ) / ((1−ε')ε'²), 6(ln(6/δ) + ln m))` (`alg:ttc`, line 20). -/
noncomputable def thresh : ℝ :=
  max (24 * Real.log (24 / P.δ) / ((1 - P.epsPrime) * P.epsPrime ^ 2))
      (6 * (Real.log (6 / P.δ) + Real.log P.m))

/-- `κ = √(2 log(8/η)) + √(2 log r)`, the facet displacement of `lem:nonconv`.

The `8/η` (rather than `4/η`) is the `θ = η/2` internal parameter that makes the
final combination close; see the README, finding 1. -/
noncomputable def kappa : ℝ :=
  Real.sqrt (2 * Real.log (8 / P.eta)) + Real.sqrt (2 * Real.log P.r)

/-- `γ = (64 m n / η)·√(log(8r/η))`, the inscribed radius `GetPrecision` targets
(`alg:prec`, line 86).

The factor `m` is what allows the `Pᵢ` to have *different* inscribed-ball centres
— see `Ttc.Internal.Recentred`. The `8r/η` matches `κ`. -/
noncomputable def gamma : ℝ :=
  (64 * P.m * P.n / P.eta) * Real.sqrt (Real.log (8 * P.r / P.eta))

/-- `ρ ← ⌈log₁₀(γ/γ̂)⌉` (`alg:prec`), where `γ̂` is the largest inscribed radius
found by the LP. -/
noncomputable def precision (gammaHat : ℝ) : ℤ := ⌈Real.logb 10 (P.gamma / gammaHat)⌉

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
