/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.CostedBackend
import Ttc.Sampler.HitAndRunTheorem11
import Arlib.Probability.RejectionRounds

/-!
# `Exec/SamplerCost`: an *arithmetic-operation* price for the hit-and-run sampler

> ## ⚠ EVERYTHING PRICED HERE IS CONDITIONAL ON AN UNPROVED MIXING THEOREM ⚠
>
> Every cost statement in this file whose step count is
> `Ttc.hitAndRunTheorem11Steps` is meaningful only *given*
> `H : Ttc.HitAndRunTheorem11Input` — Lovász–Vempala Theorem 1.1.  That structure is
> **assumed, and inhabited nowhere in this development**; inhabiting it needs the
> weighted-isoperimetry/localisation argument, which in turn rests on `hLS`
> (Lovász–Simonovits 1993, Corollary 1.5), which nobody in this repository has proved.
> **Nothing in this file is a proof that `TTC` runs in `O(m·n⁴)` — let alone `O(m·n⁵)`.**
> It is a proof that *if* Theorem 1.1 holds at the shape this repository derives, *then*
> the arithmetic charge of one sample is at most an explicit number, and that number is
> `O(n⁴ · r · (R²/γ²) · log R)`.
>
> Additionally, the per-step arithmetic charge `n·r` below is a **cost-model
> definition**, not a theorem: no executable hit-and-run step exists in this repository
> and nothing measures one (`CLAUDE.md` §11, "semantic `def`s").  Its name says
> `Charge`, not `Cost of the real implementation`.

## What this file adds, and what already existed

`Ttc/Exec/PriceList.lean` + `Ttc/Exec/SamplePrice.lean` carried a complete uniform price
list for the **ball-walk** sampler (`Ttc.ttcSampPrice`), and `Ttc/Exec/Complexity.lean`
composed it.  `Exec/SamplePrice` was deleted on 2026-08-19 with the reference-oracle
apparatus, so `Ttc.ttcSampPrice` no longer exists; what survives of that machinery is the
transition-counting model, and the paragraph below still describes what it does and does not
charge for.  Two things that machinery does *not* have, and this file supplies:

* it counts **chain transitions only** — "per-step arithmetic is free"
  (`Exec/SamplePrice` module docstring, `Exec/PriceList` §"what a number does not mean").
  There is no cost model anywhere in the repository for one hit-and-run step, for the
  coordinate rounding, or for the membership test.  `Ttc.SamplerCost.stepOpCharge` is that
  model;
* `Ttc.ttcSampPrice` prices `Ttc.mixStepsBound`, which is **exponential in `n`**
  (`4ⁿ·((γ+D)/γ)^{4n}`).  The hit-and-run count `Ttc.hitAndRunTheorem11Steps` is
  polynomial, and it is what `sections/proof-appendix.tex`'s `cor:linf` cites.

## The chain this file formalises

`cor:linf` (`sections/proof-appendix.tex`) prices one accepted lattice sample as

1. a draw from the sampling oracle over `P'` at TV distance `ν = ε/(16·vol P')`;
2. realised by hit-and-run: `steps` transitions;
3. each transition `O(n·r)` operations (line/facet intersection), which also dominates
   the `O(n)` coordinate rounding and the `O(n·r)` membership test;
4. the rejection loop, `1/(1−ε/3) ≤ 3/2` draws in expectation.

Steps 2–3 are `Ttc.SamplerCost.samplePrice` and
`Ttc.SamplerCost.drawWork_le_samplePrice`; step 4 is
`Ttc.SamplerCost.expected_draws_le_three_halves`, kept **deliberately separate** from the
price (§"the rejection factor" below).

## Section 1 is a bug-oracle audit of the rewritten `cor:linf`

Every inequality of the new proof of `cor:linf` is checked below over its stated range
`0 < ε ≤ 1`.  **All of them hold.**  Two defects were found elsewhere in the argument, and
both are recorded as lemmas here:

* `Ttc.SamplerCost.paper_escape_constant_unsupported` — the choice `c = √(log(32/ε))` gives
  the budgeted escape mass `ε/16` only under `claim:linf`'s *printed* constant `2e^{−c²}`.
  The escape bound this repository actually proves at the same inflation
  `κ = c + √(2 log r)` is `e^{−c²/2}` (`Arlib.KV97.escape_prob_le_exp`), and at the paper's
  `c` that is `√(ε/32) > ε/16` for **every** `ε ≤ 1` (indeed every `ε < 8`).
  `Ttc.SamplerCost.corrected_escape_constant` gives the repair: `c = √(2·log(16/ε))` makes
  the proved bound *exactly* `ε/16`, and `Ttc.SamplerCost.kappa_le_of_corrected_c` shows
  `κ ≤ 2√(log(32r/ε))` still holds at that `c`, so the hypothesis on `γ` and every
  downstream step of `cor:linf` survive unchanged.
* `Ttc.SamplerCost.corlinf_upper_with_nu` — `claim:linf`'s printed upper bound
  `Pr[rnd p = x] ≤ 1/vol(P')` drops the TV term; the honest bound is `1/vol(P') + ν`.
  The corollary survives: `(1 + ε/16)/(1 − ε/8) ≤ 1 + ε/3` on the whole range.

## Section 2's headline: the derived exponent is **4**, not the paper's 5

`sections/analysis.tex`'s `thm:runtime` proof says the sampling step costs `O(n⁵)` per
sample, from `cor:linf`'s `O(n⁴ R²/γ² log R)` walk steps at `O(n·r)` each.  Deriving the
step count from **this repository's own** `Ttc.hitAndRunTheorem11Steps` instead gives one
factor of `n` less.  See `Ttc.SamplerCost.samplePrice_le_quartic` and the long note above
it.  (`thm:runtime`'s *statement* still reads `O(m n⁴)` while its proof concludes
`O(m n⁵)`; `O(m n⁴)` is the one this formalisation supports.)
-/

namespace Ttc.SamplerCost

open MeasureTheory

/-! ## Section 1 — bug oracle: the arithmetic of the rewritten `cor:linf`

Each lemma below is one printed step of the proof of `cor:linf`
(`sections/proof-appendix.tex`), over its stated range `0 < ε ≤ 1`.  Nothing here is used
by Section 2; these are referee lemmas. -/

section Corlinf

variable {ε : ℝ}

/-- **`(1−ε/8)²(1−ε/128) ≥ 1 − 33ε/128` — HOLDS on `0 ≤ ε ≤ 1`** (indeed on `0 ≤ ε ≤ 144`).

Expanding, the left side is `1 − 33ε/128 + 9ε²/512 − ε³/8192`, so the claim is
`ε²(9/512) ≥ ε³/8192`, i.e. `ε ≤ 144`. -/
theorem corlinf_lower_expand (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    1 - 33 * ε / 128 ≤ (1 - ε / 8) ^ 2 * (1 - ε / 128) := by
  nlinarith [sq_nonneg ε, mul_nonneg (mul_nonneg hε0 hε0) hε0]

/-- **`1 − 33ε/128 ≥ 1 − ε/3` — HOLDS**, since `33/128 = 0.2578… < 1/3`. -/
theorem corlinf_lower_relax (hε0 : 0 ≤ ε) : 1 - ε / 3 ≤ 1 - 33 * ε / 128 := by
  linarith

/-- **`1/(1−ε/8) ≤ 1 + ε/7` — HOLDS on `0 ≤ ε ≤ 1`, with equality at `ε = 1`.**

`1/(1−t) = 1 + t/(1−t)` and `1 − ε/8 ≥ 7/8`, so `t/(1−t) ≤ (ε/8)/(7/8) = ε/7`. -/
theorem corlinf_upper_seven (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    1 / (1 - ε / 8) ≤ 1 + ε / 7 := by
  have hd : (0 : ℝ) < 1 - ε / 8 := by linarith
  rw [div_le_iff₀ hd]
  nlinarith

/-- **`1 + ε/7 ≤ 1 + ε/3` — HOLDS.** -/
theorem corlinf_upper_relax (hε0 : 0 ≤ ε) : 1 + ε / 7 ≤ 1 + ε / 3 := by linarith

/-- **`(1+ε/3)/(1−ε/3) ≤ 1 + ε` — HOLDS on `0 ≤ ε ≤ 1`, with equality at `ε = 1`.**

Clearing the denominator, the claim is `0 ≤ (ε/3)(1 − ε)`. -/
theorem corlinf_condition_ratio (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (1 + ε / 3) / (1 - ε / 3) ≤ 1 + ε := by
  have hd : (0 : ℝ) < 1 - ε / 3 := by linarith
  rw [div_le_iff₀ hd]
  nlinarith

/-- **`1/(1−ε/3) ≤ 3/2` — HOLDS on `0 ≤ ε ≤ 1`**: the expected number of rejection
rounds `cor:linf` quotes. -/
theorem corlinf_rounds_le (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    1 / (1 - ε / 3) ≤ 3 / 2 := by
  have hd : (0 : ℝ) < 1 - ε / 3 := by linarith
  rw [div_le_iff₀ hd]
  linarith

/-- **`e^α ≤ 1 + 2α` on `0 ≤ α ≤ 1`** — the analytic core of `(1+α/x)^x ≤ 1+2α`.

By convexity of `exp` on `[0,1]`: `e^α ≤ (1−α)·1 + α·e ≤ 1 + α(e−1) ≤ 1 + 2α`. -/
theorem exp_le_one_add_two_mul {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    Real.exp α ≤ 1 + 2 * α := by
  have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (by linarith : (0 : ℝ) ≤ 1 - α) (by linarith : (0 : ℝ) ≤ α) (by ring)
  simp only [smul_eq_mul, Real.exp_zero, mul_one] at hconv
  rw [show (1 - α) * 0 + α = α from by ring] at hconv
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  nlinarith

/-- **`(1 + α/k)^k ≤ 1 + 2α` for `0 ≤ α ≤ 1` and `k ≥ 1` — HOLDS.**

This is `cor:linf`'s helper inequality, at the natural exponent that the corollary
actually uses (`k = n`).  Proof: `1 + α/k ≤ e^{α/k}`, so the power is at most `e^α`, and
`Ttc.SamplerCost.exp_le_one_add_two_mul` finishes.  (The paper states it for real `x ≥ 1`;
that form is also true, by the same two steps with `rpow`.) -/
theorem one_add_div_pow_le {α : ℝ} (k : ℕ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    (1 + α / k) ^ k ≤ 1 + 2 * α := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simpa using by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hbase : 1 + α / k ≤ Real.exp (α / k) := by
    have := Real.add_one_le_exp (α / k)
    linarith
  have hnn : (0 : ℝ) ≤ 1 + α / k := by positivity
  calc (1 + α / k) ^ k ≤ (Real.exp (α / k)) ^ k := by
        exact pow_le_pow_left₀ hnn hbase k
    _ = Real.exp (α / k * k) := by rw [← Real.exp_nat_mul]; ring_nf
    _ = Real.exp α := by rw [div_mul_cancel₀ _ (ne_of_gt hk0)]
    _ ≤ 1 + 2 * α := exp_le_one_add_two_mul hα0 hα1

/-- **`(1 + ε/(256n))ⁿ ≤ 1 + ε/128` — HOLDS on `0 ≤ ε ≤ 1`, any `n`**, the instance
`cor:linf` uses (`α = ε/256`). -/
theorem corlinf_inflation_pow (n : ℕ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (1 + ε / (256 * n)) ^ n ≤ 1 + ε / 128 := by
  have h : (1 + (ε / 256) / n) ^ n ≤ 1 + 2 * (ε / 256) :=
    one_add_div_pow_le n (by linarith) (by linarith)
  have he : ε / (256 * (n : ℝ)) = (ε / 256) / n := by ring
  rw [he]
  linarith

/-- **`√u + √v ≤ √(2(u+v))`** — the step `cor:linf` uses to bound `κ`. -/
theorem sqrt_add_sqrt_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Real.sqrt u + Real.sqrt v ≤ Real.sqrt (2 * (u + v)) := by
  have hnn : 0 ≤ Real.sqrt u + Real.sqrt v :=
    add_nonneg (Real.sqrt_nonneg u) (Real.sqrt_nonneg v)
  have key : (Real.sqrt u + Real.sqrt v) ^ 2 ≤ 2 * (u + v) := by
    have hsu := Real.sq_sqrt hu
    have hsv := Real.sq_sqrt hv
    nlinarith [sq_nonneg (Real.sqrt u - Real.sqrt v)]
  calc Real.sqrt u + Real.sqrt v
      = Real.sqrt ((Real.sqrt u + Real.sqrt v) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt (2 * (u + v)) := Real.sqrt_le_sqrt key

/-- `√(4L) = 2√L`. -/
theorem sqrt_four_mul (L : ℝ) : Real.sqrt (4 * L) = 2 * Real.sqrt L := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]

/-- **`κ = √(log(32/ε)) + √(2 log r) ≤ 2√(log(32r/ε))` — HOLDS** for `0 < ε ≤ 1`,
`1 ≤ r`.  This is the paper's own displayed bound on the facet displacement. -/
theorem corlinf_kappa_le {r : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hr : 1 ≤ r) :
    Real.sqrt (Real.log (32 / ε)) + Real.sqrt (2 * Real.log r)
      ≤ 2 * Real.sqrt (Real.log (32 * r / ε)) := by
  have hlr : 0 ≤ Real.log r := Real.log_nonneg hr
  have hle : (1 : ℝ) ≤ 32 / ε := by rw [le_div_iff₀ hε0]; linarith
  have hlε : 0 ≤ Real.log (32 / ε) := Real.log_nonneg hle
  have hsplit : Real.log (32 * r / ε) = Real.log (32 / ε) + Real.log r := by
    rw [show (32 : ℝ) * r / ε = 32 / ε * r by ring,
      Real.log_mul (by positivity) (by positivity)]
  refine le_trans (sqrt_add_sqrt_le hlε (by linarith)) ?_
  rw [← sqrt_four_mul]
  refine Real.sqrt_le_sqrt ?_
  rw [hsplit]; linarith

/-- **The repaired constant keeps `cor:linf`'s displayed `κ` bound.**  At
`c = √(2 log(16/ε))` — the value the escape bound this repository *proves* needs — the
facet displacement still satisfies `κ ≤ 2√(log(32r/ε))`, so the hypothesis on `γ` and
every downstream step of the corollary are unchanged. -/
theorem kappa_le_of_corrected_c {r : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hr : 1 ≤ r) :
    Real.sqrt (2 * Real.log (16 / ε)) + Real.sqrt (2 * Real.log r)
      ≤ 2 * Real.sqrt (Real.log (32 * r / ε)) := by
  have hlr : 0 ≤ Real.log r := Real.log_nonneg hr
  have hle16 : (1 : ℝ) ≤ 16 / ε := by rw [le_div_iff₀ hε0]; linarith
  have hl16 : 0 ≤ Real.log (16 / ε) := Real.log_nonneg hle16
  have hmono : Real.log (16 / ε) ≤ Real.log (32 / ε) :=
    Real.log_le_log (by positivity) (by gcongr; norm_num)
  have hsplit : Real.log (32 * r / ε) = Real.log (32 / ε) + Real.log r := by
    rw [show (32 : ℝ) * r / ε = 32 / ε * r by ring,
      Real.log_mul (by positivity) (by positivity)]
  refine le_trans (sqrt_add_sqrt_le (by linarith) (by linarith)) ?_
  rw [← sqrt_four_mul]
  refine Real.sqrt_le_sqrt ?_
  rw [hsplit]; linarith

/-- **`κ/γ ≤ ε/(256n)` — HOLDS**, given the corollary's hypothesis on `γ` and the
displayed bound `κ ≤ 2√L` (`L = log(32r/ε)`).  Written with `L` abstract so it serves the
paper's `c` and the repaired `c` alike. -/
theorem corlinf_kappa_div_gamma {n : ℕ} {γ κ L : ℝ} (hn : 1 ≤ n) (hL : 0 < L)
    (hε0 : 0 < ε) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 2 * Real.sqrt L)
    (hγ : 512 * (n : ℝ) / ε * Real.sqrt L ≤ γ) :
    κ / γ ≤ ε / (256 * n) := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hlow : 0 < 512 * (n : ℝ) / ε * Real.sqrt L := by positivity
  have hγ0 : 0 < γ := lt_of_lt_of_le hlow hγ
  rw [div_le_div_iff₀ hγ0 (by positivity)]
  have h2 : ε * (512 * (n : ℝ) / ε * Real.sqrt L) = 512 * (n : ℝ) * Real.sqrt L := by
    field_simp
  nlinarith [mul_le_mul_of_nonneg_left hγ (le_of_lt hε0)]

/-! ### The two defects

Both are in `claim:linf` (Theorem 2 of Kannan–Vempala), not in the new arithmetic of
`cor:linf`; but the new `cor:linf` inherits them. -/

/-- **DEFECT 1 — the paper's `c = √(log(32/ε))` does NOT deliver the budgeted escape mass
`ε/16` under the bound this repository proves.**

`Arlib.KV97.escape_prob_le_exp` bounds the escape probability at inflation
`κ = c + √(2 log r)` by `e^{−c²/2}`, *not* by `claim:linf`'s printed `2e^{−c²}`.  At the
paper's `c` that is `√(ε/32)`, and this lemma shows it **strictly exceeds** the `ε/16` the
proof of `cor:linf` needs — for every `0 < ε ≤ 1` (in fact every `0 < ε < 8`).

This is *unsupported*, not *false*: the repository's escape bound comes from Hoeffding for
generic `[−1,1]`-bounded noise, and the rounding law's own sub-Gaussian constant may well
rescue the printed `2e^{−c²}`.  This development simply cannot certify it.
`Ttc.SamplerCost.corrected_escape_constant` is the cheap repair. -/
theorem paper_escape_constant_unsupported (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ε / 16 < Real.exp (-(Real.sqrt (Real.log (32 / ε))) ^ 2 / 2) := by
  have hle : (1 : ℝ) ≤ 32 / ε := by rw [le_div_iff₀ hε0]; linarith
  have hlε : 0 ≤ Real.log (32 / ε) := Real.log_nonneg hle
  rw [Real.sq_sqrt hlε]
  set t := Real.exp (-Real.log (32 / ε) / 2) with ht
  have htpos : 0 < t := Real.exp_pos _
  have hsq : t ^ 2 = ε / 32 := by
    have h2 : t ^ 2 = Real.exp (-Real.log (32 / ε) / 2 + -Real.log (32 / ε) / 2) := by
      rw [Real.exp_add, ht]; ring
    rw [h2, show -Real.log (32 / ε) / 2 + -Real.log (32 / ε) / 2
      = -Real.log (32 / ε) by ring, Real.exp_neg,
      Real.exp_log (by positivity : (0 : ℝ) < 32 / ε)]
    field_simp
  refine lt_of_pow_lt_pow_left₀ 2 htpos.le ?_
  rw [hsq]
  nlinarith

/-- **THE REPAIR for defect 1.**  At `c = √(2 log(16/ε))` the escape bound this repository
proves is *exactly* the `ε/16` that `cor:linf` budgets.  Together with
`Ttc.SamplerCost.kappa_le_of_corrected_c` — which shows `κ ≤ 2√(log(32r/ε))` still holds —
the corollary's hypothesis on `γ`, its `κ/γ ≤ ε/(256n)`, and every later step go through
verbatim.  The cost of the repair is a factor `√2` in `c`, absorbed by slack. -/
theorem corrected_escape_constant (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    Real.exp (-(Real.sqrt (2 * Real.log (16 / ε))) ^ 2 / 2) = ε / 16 := by
  have hle : (1 : ℝ) ≤ 16 / ε := by rw [le_div_iff₀ hε0]; linarith
  have hl : 0 ≤ Real.log (16 / ε) := Real.log_nonneg hle
  rw [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 2 * Real.log (16 / ε)),
    show -(2 * Real.log (16 / ε)) / 2 = -Real.log (16 / ε) by ring, Real.exp_neg,
    Real.exp_log (by positivity : (0 : ℝ) < 16 / ε)]
  field_simp

/-- **DEFECT 2 — `claim:linf`'s printed upper bound drops the TV term.**

`Pr[rnd p = x] = ∫ tent_x dμ_p` with `0 ≤ tent_x ≤ 1`; the uniform law gives
`≤ 1/vol(P')`, and a `ν`-close law can add `ν`.  So the honest upper bound is
`1/vol(P') + ν = (1 + ε/16)/vol(P')`, not the printed `1/vol(P')`.

**`cor:linf` survives with room to spare**: this lemma is the repaired upper chain, and it
still lands inside the `1 + ε/3` the corollary needs (the requirement is only `ε ≤ 3.5`). -/
theorem corlinf_upper_with_nu (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (1 + ε / 16) / (1 - ε / 8) ≤ 1 + ε / 3 := by
  have hd : (0 : ℝ) < 1 - ε / 8 := by linarith
  rw [div_le_iff₀ hd]
  nlinarith

end Corlinf

/-! ## Section 2 — the per-sample arithmetic price

### The cost model (STEP 0(a): none of this existed)

Nothing in this repository charges arithmetic.  `Ttc.ttcSampPrice` and `Ttc.ttcVolPrice`
count *chain transitions* and *coins*, and both of their module docstrings say in so many
words that "per-step arithmetic is free".  `Ttc.SamplerCost.stepOpCharge` below is
therefore a **new modelling decision**, and it is a `def`, not a theorem: it asserts
nothing about any executable.

### The price (STEP 0(b))

`Ttc.SamplerCost.samplePrice n γ R M ε' rfac` is a function of exactly six things —

* `n`   the dimension;
* `γ`   a **lower** bound on the inradius of every inflated polytope `P'ᵢ`;
* `R`   an **upper** bound on the circumradius of every `P'ᵢ`;
* `M`   an **upper** bound on the warmness of every start;
* `ε'`  the sampler accuracy `Ttc.Params.epsPrime`, which fixes the TV tolerance
  `ε'/(4·vol P'ᵢ)` of `Ttc.kv97SamplerOfHitAndRun.law_tv`
  (the paper writes `ν = ε/(16·vol P')`; same shape, different constant);
* `rfac` the facet count `Ttc.Params.r`.

**`δ` does not enter.**  The failure probability appears only in TTC's sample *threshold*
`Ttc.ttcThresh`, i.e. in how many samples are drawn, never in the price of one.  That is
why `Ttc.backendCost_le_ttcComplexity` multiplies the two.

### The derived step count and exponent (STEP 0(c)) — see
`Ttc.SamplerCost.samplePrice_le_quartic`, whose docstring is the whole finding. -/

section Price

/-- **The arithmetic charge of one hit-and-run transition, as a MODELLING DEFINITION.**

`⌈n·rfac⌉₊`: intersecting the sampled line with the `rfac` facets of `P'` costs one inner
product each, `n` operations per inner product.  This mirrors `cor:linf`'s
"each step intersects a line with the `r` facets of `P'` at cost `O(n·r)`".

**This is not a theorem and its name does not claim one.**  No executable hit-and-run step
exists in this repository, so nothing measures this; it is the cost model, stated openly so
that a reader can reject it (`CLAUDE.md` §11). -/
noncomputable def stepOpCharge (n : ℕ) (rfac : ℝ) : ℕ := ⌈(n : ℝ) * rfac⌉₊

/-- **The arithmetic charge of one *draw*** — `steps` transitions, plus two more
`stepOpCharge` units that pay for `cor:linf`'s two post-processing costs: the `O(n)`
rounding of the `n` coordinates and the `O(n·rfac)` membership test `rnd p ∈ P`.  The paper
observes that the per-step cost dominates both; charging one extra unit for each makes that
absorption explicit rather than implicit. -/
noncomputable def drawOpCharge (steps n : ℕ) (rfac : ℝ) : ℕ :=
  (steps + 2) * stepOpCharge n rfac

/-- **The worst-case TV tolerance.**  `Ttc.kv97SamplerOfHitAndRun`'s `law_tv` runs at
`ε'/(4·vol P'ᵢ)`, which is *smallest* — hence most expensive — when `vol P'ᵢ` is largest.
`P'ᵢ ⊆ B̄(z, R)` gives `vol P'ᵢ ≤ (2R)ⁿ`, the paper's own bound. -/
noncomputable def worstTol (n : ℕ) (epsPrime R : ℝ) : ℝ :=
  epsPrime / (4 * (2 * R) ^ n)

/-- **The uniform transition count** — `Ttc.hitAndRunTheorem11Steps` at the worst geometry
and the worst tolerance.  Conditional on `H : Ttc.HitAndRunTheorem11Input` for its meaning;
as a number it is unconditional arithmetic. -/
noncomputable def stepsPrice (n : ℕ) (γ R M epsPrime : ℝ) : ℕ :=
  hitAndRunTheorem11Steps n γ R M (worstTol n epsPrime R)

/-- **THE UNIFORM PER-SAMPLE PRICE**, in arithmetic operations.  A plain arithmetic `def`:
its name promises no semantic identity, and `Ttc.SamplerCost.drawWork_le_samplePrice` is
what makes it a *price*. -/
noncomputable def samplePrice (n : ℕ) (γ R M epsPrime rfac : ℝ) : ℕ :=
  drawOpCharge (stepsPrice n γ R M epsPrime) n rfac

/-- **The work of one draw at cube `i`**, from that cube's own inradius `ri`,
circumradius `Ri`, warmness `Mi` and tolerance `ei`.  This is the operational field a
`Ttc.CostedBackend` wants. -/
noncomputable def drawWork (n : ℕ) (ri Ri Mi ei rfac : ℝ) : ℕ :=
  drawOpCharge (hitAndRunTheorem11Steps n ri Ri Mi ei) n rfac

/-! ### Monotonicity of the transition count -/

set_option maxRecDepth 8000 in
/-- **`Ttc.hitAndRunTheorem11Threshold` is monotone in the four directions the price
needs**: it grows with the circumradius and the warmness, and shrinks with the inradius and
the tolerance. -/
theorem hitAndRunTheorem11Threshold_le_of (n : ℕ) {ri Ri Mi ei γ R M e : ℝ}
    (hγ0 : 0 < γ) (hri : γ ≤ ri) (hRi0 : 0 ≤ Ri) (hRi : Ri ≤ R)
    (hMi1 : 1 ≤ Mi) (hMi : Mi ≤ M) (he0 : 0 < e) (hei : e ≤ ei) (hei1 : ei ≤ 1) :
    hitAndRunTheorem11Threshold n ri Ri Mi ei
      ≤ hitAndRunTheorem11Threshold n γ R M e := by
  have hri0 : 0 < ri := lt_of_lt_of_le hγ0 hri
  have hei0 : 0 < ei := lt_of_lt_of_le he0 hei
  have hargi : (1 : ℝ) ≤ 8 * Mi / ei ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have harg : 8 * Mi / ei ^ 2 ≤ 8 * M / e ^ 2 := by
    have hei2 : e ^ 2 ≤ ei ^ 2 := by nlinarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg e, sq_nonneg ei]
  have hlog0 : 0 ≤ Real.log (8 * Mi / ei ^ 2) := Real.log_nonneg hargi
  have hlog : Real.log (8 * Mi / ei ^ 2) ≤ Real.log (8 * M / e ^ 2) :=
    Real.log_le_log (by positivity) harg
  have hgeo : (2 : ℝ) ^ 56 * (n : ℝ) ^ 2 * Ri ^ 2 / ri ^ 2
      ≤ 2 ^ 56 * (n : ℝ) ^ 2 * R ^ 2 / γ ^ 2 := by
    gcongr
  have hgeo0 : (0 : ℝ) ≤ 2 ^ 56 * (n : ℝ) ^ 2 * Ri ^ 2 / ri ^ 2 :=
    div_nonneg (by positivity) (by positivity)
  unfold hitAndRunTheorem11Threshold
  exact mul_le_mul hgeo hlog hlog0 (hgeo0.trans hgeo)

/-- The integer deadline inherits the monotonicity. -/
theorem hitAndRunTheorem11Steps_le_of (n : ℕ) {ri Ri Mi ei γ R M e : ℝ}
    (hγ0 : 0 < γ) (hri : γ ≤ ri) (hRi0 : 0 ≤ Ri) (hRi : Ri ≤ R)
    (hMi1 : 1 ≤ Mi) (hMi : Mi ≤ M) (he0 : 0 < e) (hei : e ≤ ei) (hei1 : ei ≤ 1) :
    hitAndRunTheorem11Steps n ri Ri Mi ei ≤ hitAndRunTheorem11Steps n γ R M e :=
  Nat.add_le_add_right
    (Nat.floor_le_floor
      (hitAndRunTheorem11Threshold_le_of n hγ0 hri hRi0 hRi hMi1 hMi he0 hei hei1)) 1

/-! ### STEP 1: the price dominates the work, at every cube -/

/-- **`Ttc.SamplerCost.worstTol` really is the worst tolerance**: any cube whose inflated
polytope has volume at most `(2R)ⁿ` runs at a tolerance at least this one. -/
theorem worstTol_le (n : ℕ) {epsPrime R Vi : ℝ} (heps0 : 0 < epsPrime) (hVi0 : 0 < Vi)
    (hVi : Vi ≤ (2 * R) ^ n) :
    worstTol n epsPrime R ≤ epsPrime / (4 * Vi) := by
  unfold worstTol
  gcongr

/-- **STEP 1 — the pointwise bound `Ttc.CostedBackend` asks for.**

At every cube, the arithmetic charge of one draw is at most the uniform price, given the
five uniform-geometry hypotheses: the inradius is at least `γ`, the circumradius at most
`R`, the warmness at most `M`, the volume of `P'ᵢ` at most `(2R)ⁿ`, and the resulting
tolerance at most `1` (which `Ttc.kv97SamplerOfHitAndRun` needs anyway — it is that
construction's binder `heps1`, not something invented here).

Conditional on `H : Ttc.HitAndRunTheorem11Input` for its *meaning*; the inequality itself
is unconditional arithmetic. -/
theorem drawWork_le_samplePrice (n : ℕ) {ri Ri Mi Vi γ R M epsPrime rfac : ℝ}
    (hγ0 : 0 < γ) (hri : γ ≤ ri) (hRi0 : 0 ≤ Ri) (hRi : Ri ≤ R)
    (hMi1 : 1 ≤ Mi) (hMi : Mi ≤ M) (heps0 : 0 < epsPrime) (hR0 : 0 < R)
    (hVi0 : 0 < Vi) (hVi : Vi ≤ (2 * R) ^ n) (htol1 : epsPrime / (4 * Vi) ≤ 1) :
    drawWork n ri Ri Mi (epsPrime / (4 * Vi)) rfac ≤ samplePrice n γ R M epsPrime rfac := by
  have he0 : 0 < worstTol n epsPrime R := by
    unfold worstTol; positivity
  exact Nat.mul_le_mul_right _
    (Nat.add_le_add_right
      (hitAndRunTheorem11Steps_le_of n hγ0 hri hRi0 hRi hMi1 hMi he0
        (worstTol_le n heps0 hVi0 hVi) htol1) 2)

end Price

/-! ## STEP 2 — the rejection factor, kept honestly separate from the price

`Ttc.CostedBackend.samplePrice` is a **uniform, deterministic** natural: `sampleWork i ≤
samplePrice` for every cube, no measure in sight.  `cor:linf`'s `1/(1−ε/3) ≤ 3/2` is an
**expectation** over the rejection loop's randomness.  The two cannot be the same object,
and this file does not pretend they are:

* `Ttc.SamplerCost.samplePrice` prices **one draw**, deterministically;
* `Ttc.SamplerCost.expected_draws_le_three_halves` bounds the **expected number of draws**;
* `Ttc.SamplerCost.expected_loop_ops_le` multiplies them, and is a statement about a
  Bochner integral — not a uniform bound, and it is not a field of any backend.

Reconciliation, stated plainly: the `Ttc.CostedBackend` charge is the cost of the loop
*conditioned on one draw per sample*; the expected true cost is at most `3/2` times it. -/

section Rejection

open Arlib.Probability

variable {E : Type*} [MeasurableSpace E]

/-- **`E[rounds] ≤ 3/2`** from `cor:linf`'s acceptance bound `Pr[rnd p ∈ P] ≥ 1 − ε/3`.

The acceptance bound itself is *hypothesis*, not theorem: it is the sum over the `N`
lattice points of `cor:linf`'s own lower bound, which this file does not reprove.  What is
proved here is the loop arithmetic on top of it, via
`Arlib.Probability.integral_roundCountNat_le` (`E[rounds] = 1/Pr[accept]` exactly, from
`Arlib.Probability.lintegral_roundCount`).

For the acceptance constant this repository *does* prove — `9/(20e)`, from
`Arlib.KV97.acceptance_ge_nine_div_twenty_exp` — the unconditional bound is
`Arlib.Probability.integral_roundCountNat_le_twentyExpDivNine`, `E[rounds] ≤ 20e/9 < 6.041`.
That is a factor `≈ 4` worse than `3/2` and costs only a constant. -/
theorem expected_draws_le_three_halves (ν : Measure E) [IsProbabilityMeasure ν]
    {A : Set E} (hA : MeasurableSet A) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hacc : ENNReal.ofReal (1 - ε / 3) ≤ ν A) :
    ∫ ω, (roundCountNat A ω : ℝ) ∂(roundsMeasure ν) ≤ 3 / 2 :=
  le_trans (integral_roundCountNat_le ν hA (by linarith) (by linarith) hacc)
    (corlinf_rounds_le hε0 hε1)

/-- **The expected arithmetic charge of the whole rejection loop is at most
`(3/2)·samplePrice`.**

The integrand is `rounds · samplePrice`: the loop's total charge when every round is priced
at the uniform `Ttc.SamplerCost.samplePrice`.  The expectation then factorises, because the
price is a constant.

Two honesty notes.  (i) This is an *integral* inequality; it is **not** a
`Ttc.CostedBackend` field and must not be read as one.  (ii) The link to a *particular
cube's* work is not formalised here — `Ttc.SamplerCost.drawWork_le_samplePrice` is the
separate, deterministic, per-cube statement, and composing the two is prose, not a
theorem. -/
theorem expected_loop_ops_le (ν : Measure E) [IsProbabilityMeasure ν]
    {A : Set E} (hA : MeasurableSet A) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hacc : ENNReal.ofReal (1 - ε / 3) ≤ ν A)
    (n : ℕ) (γ R M epsPrime rfac : ℝ) :
    ∫ ω, (roundCountNat A ω : ℝ) * (samplePrice n γ R M epsPrime rfac : ℝ)
        ∂(roundsMeasure ν)
      ≤ 3 / 2 * (samplePrice n γ R M epsPrime rfac : ℝ) := by
  rw [integral_mul_const]
  have hpos : (0 : ℝ) ≤ (samplePrice n γ R M epsPrime rfac : ℝ) := Nat.cast_nonneg _
  nlinarith [expected_draws_le_three_halves ν hA hε0 hε1 hacc]

end Rejection

/-! ## STEP 3 — instantiating `Ttc.CostedBackend`, and the run-level charge -/

section Backend

variable {n : ℕ} {ι : Type*}

/-- **A cost-certified backend whose sampler is hit-and-run.**

The semantic half is *passed in* — `hvol`, `hsamp` are the caller's own certificates for
the caller's own `volumeSpec`/`sampleSpec`, and the volume price is the caller's too.  This
file's contribution is exactly the sampling half of the **operational** record:
`sampleWork` is `Ttc.SamplerCost.drawWork` at each cube's geometry, and `samplePrice` is
`Ttc.SamplerCost.samplePrice`.  `Ttc.CostedBackend`'s separation of the two halves is
preserved, not weakened: nothing here lets a correctness theorem discharge a price.

⚠ Conditional: `sampleWork` is meaningful as a *number of hit-and-run steps to accuracy*
only given `H : Ttc.HitAndRunTheorem11Input` (module docstring). -/
noncomputable def hitAndRunBackend (P : Params)
    {volumeSpec sampleSpec : Oracles n ι → Prop} (O : Oracles n ι)
    (hvol : volumeSpec O) (hsamp : sampleSpec O)
    (vWork : ι → ℕ) (vPrice : ℕ) (hvw : ∀ i, vWork i ≤ vPrice)
    (γ R M epsPrime rfac : ℝ) (ri Ri Mi Vi : ι → ℝ)
    (hγ0 : 0 < γ) (hR0 : 0 < R) (heps0 : 0 < epsPrime)
    (hri : ∀ i, γ ≤ ri i) (hRi0 : ∀ i, 0 ≤ Ri i) (hRi : ∀ i, Ri i ≤ R)
    (hMi1 : ∀ i, 1 ≤ Mi i) (hMi : ∀ i, Mi i ≤ M)
    (hVi0 : ∀ i, 0 < Vi i) (hVi : ∀ i, Vi i ≤ (2 * R) ^ n)
    (htol1 : ∀ i, epsPrime / (4 * Vi i) ≤ 1) :
    CostedBackend P volumeSpec sampleSpec where
  oracles := O
  volume_correct := hvol
  sample_correct := hsamp
  volumeWork := vWork
  sampleWork := fun i => drawWork n (ri i) (Ri i) (Mi i) (epsPrime / (4 * Vi i)) rfac
  volumePrice := vPrice
  samplePrice := _root_.Ttc.SamplerCost.samplePrice n γ R M epsPrime rfac
  volumeWork_le := hvw
  sampleWork_le := fun i =>
    drawWork_le_samplePrice n hγ0 (hri i) (hRi0 i) (hRi i) (hMi1 i) (hMi i) heps0 hR0
      (hVi0 i) (hVi i) (htol1 i)

@[simp] theorem hitAndRunBackend_samplePrice (P : Params)
    {volumeSpec sampleSpec : Oracles n ι → Prop} (O : Oracles n ι)
    (hvol : volumeSpec O) (hsamp : sampleSpec O)
    (vWork : ι → ℕ) (vPrice : ℕ) (hvw : ∀ i, vWork i ≤ vPrice)
    (γ R M epsPrime rfac : ℝ) (ri Ri Mi Vi : ι → ℝ)
    (hγ0 : 0 < γ) (hR0 : 0 < R) (heps0 : 0 < epsPrime)
    (hri : ∀ i, γ ≤ ri i) (hRi0 : ∀ i, 0 ≤ Ri i) (hRi : ∀ i, Ri i ≤ R)
    (hMi1 : ∀ i, 1 ≤ Mi i) (hMi : ∀ i, Mi i ≤ M)
    (hVi0 : ∀ i, 0 < Vi i) (hVi : ∀ i, Vi i ≤ (2 * R) ^ n)
    (htol1 : ∀ i, epsPrime / (4 * Vi i) ≤ 1) :
    (hitAndRunBackend P O hvol hsamp vWork vPrice hvw γ R M epsPrime rfac ri Ri Mi Vi
      hγ0 hR0 heps0 hri hRi0 hRi hMi1 hMi hVi0 hVi htol1).samplePrice
      = _root_.Ttc.SamplerCost.samplePrice n γ R M epsPrime rfac := rfl

/-- **STEP 3, composed — the run-level charge of the hit-and-run backend.**

`Ttc.backendCost_le_ttcComplexity` at `Ttc.SamplerCost.hitAndRunBackend`: TTC's whole
charged cost is at most `m · (C_vol + samplePrice · Thresh)` with `samplePrice` the
explicit arithmetic price of this file.  Every hypothesis of the general theorem is carried
verbatim; nothing new is assumed here.

⚠ Conditional on `H : Ttc.HitAndRunTheorem11Input` for its *meaning*, exactly as everything
else in this file. -/
theorem backendCost_le_ttcComplexity_hitAndRun {A : Type*} (atoms : A → LinAtom n)
    (φ : BForm A) (ε δ : ℝ) {volumeSpec sampleSpec : Oracles n (Cube A) → Prop}
    (O : Oracles n (Cube A)) (hvol : volumeSpec O) (hsamp : sampleSpec O)
    (vWork : Cube A → ℕ) (vPrice : ℕ) (hvw : ∀ i, vWork i ≤ vPrice)
    (γ R M epsPrime rfac : ℝ) (ri Ri Mi Vi : Cube A → ℝ)
    (hγ0 : 0 < γ) (hR0 : 0 < R) (heps0 : 0 < epsPrime)
    (hri : ∀ i, γ ≤ ri i) (hRi0 : ∀ i, 0 ≤ Ri i) (hRi : ∀ i, Ri i ≤ R)
    (hMi1 : ∀ i, 1 ≤ Mi i) (hMi : ∀ i, Mi i ≤ M)
    (hVi0 : ∀ i, 0 < Vi i) (hVi : ∀ i, Vi i ≤ (2 * R) ^ n)
    (htol1 : ∀ i, epsPrime / (4 * Vi i) ≤ 1)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hterm : Terminates (ttcBlock atoms φ ε δ) O (toDNFd (ttcInput atoms φ))) :
    (backendCost atoms φ ε δ volumeSpec sampleSpec
        (hitAndRunBackend (ttcBlock atoms φ ε δ) O hvol hsamp vWork vPrice hvw
          γ R M epsPrime rfac ri Ri Mi Vi hγ0 hR0 heps0 hri hRi0 hRi hMi1 hMi
          hVi0 hVi htol1) : ℝ)
      ≤ ttcComplexity atoms φ ε δ vPrice
          (_root_.Ttc.SamplerCost.samplePrice n γ R M epsPrime rfac) :=
  backendCost_le_ttcComplexity atoms φ ε δ volumeSpec sampleSpec hε0 hε1 hn hφ hpos
    hδ0 hδ1 _ hterm

end Backend

/-! ## STEP 4 — the asymptotics, with every suppressed factor an explicit hypothesis

**Read the hypothesis list before the exponent.**  The exponent is reachable only after
`rfac`, `R²/γ²` and `log(2R)` are suppressed, and those three are *visible on the right-hand
side* of `Ttc.SamplerCost.samplePrice_le_quartic` rather than hidden inside an `O(·)`. -/

section Asymptotic

set_option maxRecDepth 100000

/-- **The argument of the logarithm, bounded by a power of `2R`.**

`8M/ν² = 128·M·(2R)^{2n}/ε'²`, and each factor is at most a power of `2R`: `128 ≤ (2R)⁷`,
`M ≤ (2R)ⁿ` (the warmness hypothesis), `1/ε'² ≤ 4ⁿ ≤ (2R)^{2n}` (the regime `ε' ≥ 2⁻ⁿ`).
Total exponent `7 + 5n ≤ 12n`. -/
theorem logArg_le (n : ℕ) {M R epsPrime : ℝ} (hn : 1 ≤ n) (hR1 : 1 ≤ R)
    (hM1 : 1 ≤ M) (hMB : M ≤ (2 * R) ^ n) (heps0 : 0 < epsPrime)
    (hepsn : 1 / 2 ^ n ≤ epsPrime) :
    8 * M / worstTol n epsPrime R ^ 2 ≤ (2 * R) ^ (12 * n) := by
  have hB2 : (2 : ℝ) ≤ 2 * R := by linarith
  have hB1 : (1 : ℝ) ≤ 2 * R := by linarith
  have hB0 : (0 : ℝ) < 2 * R := by linarith
  have hX0 : (0 : ℝ) < (2 * R) ^ n := by positivity
  have heq : 8 * M / worstTol n epsPrime R ^ 2
      = 128 * M * ((2 * R) ^ n) ^ 2 * (1 / epsPrime) ^ 2 := by
    unfold worstTol
    field_simp
    ring
  rw [heq]
  have h2n : (2 : ℝ) ^ n ≤ (2 * R) ^ n := pow_le_pow_left₀ (by norm_num) hB2 n
  have hinv : 1 / epsPrime ≤ (2 * R) ^ n := by
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    rw [div_le_iff₀ h2] at hepsn
    have : 1 / epsPrime ≤ 2 ^ n := by
      rw [div_le_iff₀ heps0]; linarith
    linarith
  have hinv0 : (0 : ℝ) ≤ 1 / epsPrime := by positivity
  have h128 : (128 : ℝ) ≤ (2 * R) ^ 7 := by
    calc (128 : ℝ) = 2 ^ 7 := by norm_num
      _ ≤ (2 * R) ^ 7 := pow_le_pow_left₀ (by norm_num) hB2 7
  have hstep : 128 * M * ((2 * R) ^ n) ^ 2 * (1 / epsPrime) ^ 2
      ≤ (2 * R) ^ 7 * (2 * R) ^ n * ((2 * R) ^ n) ^ 2 * ((2 * R) ^ n) ^ 2 := by
    gcongr
  refine hstep.trans ?_
  have hpow : (2 * R) ^ 7 * (2 * R) ^ n * ((2 * R) ^ n) ^ 2 * ((2 * R) ^ n) ^ 2
      = (2 * R) ^ (7 + 5 * n) := by
    rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add]
    congr 1
    ring
  rw [hpow]
  exact pow_le_pow_right₀ hB1 (by omega)

/-- **`log(8M/ν²) ≤ 12·n·log(2R)`** — the expansion `cor:linf` performs by hand, at this
repository's own log argument `8M/ν²` rather than the paper's `1/ν`.

**This is where the paper's extra factor of `n` was double-counted.**  `log M` and
`2·log(1/ν)` are *added* inside one logarithm, and each is `O(n·log R)`; together they
contribute **one** factor of `n`, not two.  `cor:linf` instead quotes an `O(n³·R²/ρ²·
log(1/ν))` step bound — whose `n³` can only come from folding `log M` into the base of the
`n²` of Lovász–Vempala Theorem 1.1 — and then multiplies by `log(1/ν) = O(n log R)` again. -/
theorem log_logArg_le (n : ℕ) {M R epsPrime : ℝ} (hn : 1 ≤ n) (hR1 : 1 ≤ R)
    (hM1 : 1 ≤ M) (hMB : M ≤ (2 * R) ^ n) (heps0 : 0 < epsPrime)
    (hepsn : 1 / 2 ^ n ≤ epsPrime) :
    Real.log (8 * M / worstTol n epsPrime R ^ 2) ≤ 12 * (n : ℝ) * Real.log (2 * R) := by
  have hw0 : 0 < worstTol n epsPrime R := by unfold worstTol; positivity
  have hnum : (0 : ℝ) < 8 * M / worstTol n epsPrime R ^ 2 :=
    div_pos (by linarith) (pow_pos hw0 2)
  have h := Real.log_le_log hnum (logArg_le n hn hR1 hM1 hMB heps0 hepsn)
  rw [Real.log_pow] at h
  push_cast at h
  linarith

/-- **The uniform transition count is `O(n³ · (R²/γ²) · log R)`** — explicitly,
`12·2⁵⁶·n³·(R²/γ²)·log(2R) + 1`.

`cor:linf` claims `O(n⁴·(R²/γ²)·log R)`.  The difference is exactly the double-counted
factor of `n` explained at `Ttc.SamplerCost.log_logArg_le`. -/
theorem stepsPrice_le (n : ℕ) {γ R M epsPrime : ℝ} (hn : 1 ≤ n) (hR1 : 1 ≤ R)
    (hγ0 : 0 < γ) (hM1 : 1 ≤ M) (hMB : M ≤ (2 * R) ^ n) (heps0 : 0 < epsPrime)
    (heps1 : epsPrime ≤ 1) (hepsn : 1 / 2 ^ n ≤ epsPrime) :
    (stepsPrice n γ R M epsPrime : ℝ)
      ≤ 12 * 2 ^ 56 * ((n : ℝ) ^ 3 * (R ^ 2 / γ ^ 2) * Real.log (2 * R)) + 1 := by
  have hB1 : (1 : ℝ) ≤ 2 * R := by linarith
  have hXn : (1 : ℝ) ≤ (2 * R) ^ n := one_le_pow₀ hB1
  have hw0 : 0 < worstTol n epsPrime R := by unfold worstTol; positivity
  have ht1 : worstTol n epsPrime R ≤ 1 := by
    unfold worstTol
    rw [div_le_one (by positivity)]
    linarith
  have hlogarg : (1 : ℝ) ≤ 8 * M / worstTol n epsPrime R ^ 2 := by
    rw [le_div_iff₀ (pow_pos hw0 2)]
    nlinarith [hw0.le]
  have hlog0 : 0 ≤ Real.log (8 * M / worstTol n epsPrime R ^ 2) := Real.log_nonneg hlogarg
  have hgeo0 : (0 : ℝ) ≤ 2 ^ 56 * (n : ℝ) ^ 2 * (R ^ 2 / γ ^ 2) :=
    mul_nonneg (by positivity) (by positivity)
  have hthr0 : 0 ≤ hitAndRunTheorem11Threshold n γ R M (worstTol n epsPrime R) := by
    unfold hitAndRunTheorem11Threshold
    exact mul_nonneg (div_nonneg (by positivity) (by positivity)) hlog0
  have hthr : hitAndRunTheorem11Threshold n γ R M (worstTol n epsPrime R)
      ≤ 12 * 2 ^ 56 * ((n : ℝ) ^ 3 * (R ^ 2 / γ ^ 2) * Real.log (2 * R)) := by
    unfold hitAndRunTheorem11Threshold
    rw [mul_div_assoc]
    calc 2 ^ 56 * (n : ℝ) ^ 2 * (R ^ 2 / γ ^ 2)
            * Real.log (8 * M / worstTol n epsPrime R ^ 2)
        ≤ 2 ^ 56 * (n : ℝ) ^ 2 * (R ^ 2 / γ ^ 2) * (12 * (n : ℝ) * Real.log (2 * R)) :=
          mul_le_mul_of_nonneg_left (log_logArg_le n hn hR1 hM1 hMB heps0 hepsn) hgeo0
      _ = 12 * 2 ^ 56 * ((n : ℝ) ^ 3 * (R ^ 2 / γ ^ 2) * Real.log (2 * R)) := by ring
  unfold stepsPrice hitAndRunTheorem11Steps
  push_cast
  have hfl := Nat.floor_le hthr0
  linarith

/-- **THE HEADLINE OF THIS FILE — the derived exponent is `4`, not the paper's `5`.**

```
samplePrice n γ R M ε' rfac  ≤  2⁶² · n⁴ · rfac · (R²/γ²) · log(2R)
```

*Every* factor the `O(·)` of `thm:runtime` suppresses is on the right-hand side, and every
regime assumption is a named hypothesis:

* `hn : 1 ≤ n`, `hrfac : 1 ≤ rfac` — `rfac` is the facet count, **not** suppressed here;
* `hR1 : 1 ≤ R`, `hγ0 : 0 < γ`, `hγR : γ ≤ R` — `R²/γ²` is **not** suppressed here;
* `hM1 : 1 ≤ M`, `hMB : M ≤ (2R)ⁿ` — the warmness of the start.  Nothing in this
  repository constructs a warm start, so this is a genuine open hypothesis;
* `heps0`, `heps1`, `hepsn : 2⁻ⁿ ≤ ε'` — `cor:linf`'s own regime `ε ≥ 2⁻ⁿ`.

Suppressing `rfac`, `R²/γ²` and `log R` leaves **`O(n⁴)` arithmetic operations per
sample**, hence `O(m·n⁴)` for TTC — one factor of `n` below the `O(n⁵)`/`O(m n⁵)` the
rewritten proof of `thm:runtime` concludes, and equal to the `O(m n⁴)` that theorem's own
*statement* still prints.

**Where the difference comes from** (see `Ttc.SamplerCost.log_logArg_le`): Lovász–Vempala
Theorem 1.1, in the shape this repository derives, is `n²·(R²/r²)·log(8M/ν²)` — the
dimension enters the *base* quadratically, and `log M` and `log(1/ν)` sit **added together
inside one logarithm**, contributing one factor `n·log R` between them.  `cor:linf` instead
cites the walk as `O(n³·(R²/ρ²)·log(1/ν))` and then expands `log(1/ν) = O(n log R)`
separately, which charges the volume logarithm twice.

⚠ The bound is **conditional on `H : Ttc.HitAndRunTheorem11Input`** for its meaning (module
docstring).  `O(m·n⁴)` is an upper bound derived here; `O(m·n⁵)` is therefore also true, so
the paper's new claim is *loose*, not false. -/
theorem samplePrice_le_quartic (n : ℕ) {γ R M epsPrime rfac : ℝ} (hn : 1 ≤ n)
    (hrfac : 1 ≤ rfac) (hR1 : 1 ≤ R) (hγ0 : 0 < γ) (hγR : γ ≤ R)
    (hM1 : 1 ≤ M) (hMB : M ≤ (2 * R) ^ n) (heps0 : 0 < epsPrime) (heps1 : epsPrime ≤ 1)
    (hepsn : 1 / 2 ^ n ≤ epsPrime) :
    (samplePrice n γ R M epsPrime rfac : ℝ)
      ≤ 2 ^ 62 * (n : ℝ) ^ 4 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog2 : (0.69 : ℝ) ≤ Real.log (2 * R) := by
    have h := Real.log_two_gt_d9
    have h2 : Real.log 2 ≤ Real.log (2 * R) :=
      Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hlog0 : (0 : ℝ) ≤ Real.log (2 * R) := by linarith
  have hRg : (1 : ℝ) ≤ R ^ 2 / γ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hn3 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hn1
  have hS := stepsPrice_le n hn hR1 hγ0 hM1 hMB heps0 heps1 hepsn
  set T : ℝ := (n : ℝ) ^ 3 * (R ^ 2 / γ ^ 2) * Real.log (2 * R) with hT
  have hT069 : (0.69 : ℝ) ≤ T := by
    have h1 : (1 : ℝ) * 1 ≤ (n : ℝ) ^ 3 * (R ^ 2 / γ ^ 2) :=
      mul_le_mul hn3 hRg (by norm_num) (by linarith)
    have h2 := mul_le_mul_of_nonneg_right h1 hlog0
    rw [hT]
    linarith
  have h3 : (3 : ℝ) ≤ 12 * 2 ^ 56 * T := by
    have hmul : 12 * (2 : ℝ) ^ 56 * 0.69 ≤ 12 * 2 ^ 56 * T :=
      mul_le_mul_of_nonneg_left hT069 (by positivity)
    have hnum : (3 : ℝ) ≤ 12 * (2 : ℝ) ^ 56 * 0.69 := by norm_num
    linarith
  have hstep2 : (stepsPrice n γ R M epsPrime : ℝ) + 2 ≤ 24 * 2 ^ 56 * T := by linarith
  have hC : ((stepOpCharge n rfac : ℕ) : ℝ) ≤ 2 * (n : ℝ) * rfac := by
    unfold stepOpCharge
    have h1 : ((⌈(n : ℝ) * rfac⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) * rfac + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    nlinarith
  have hC0 : (0 : ℝ) ≤ ((stepOpCharge n rfac : ℕ) : ℝ) := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ 24 * 2 ^ 56 * T := by
    have : (0 : ℝ) ≤ T := by linarith
    positivity
  have hfinal : (samplePrice n γ R M epsPrime rfac : ℝ)
      ≤ 24 * 2 ^ 56 * T * (2 * (n : ℝ) * rfac) := by
    unfold samplePrice drawOpCharge
    push_cast
    exact mul_le_mul hstep2 hC hC0 hb0
  refine hfinal.trans ?_
  have hQ0 : (0 : ℝ) ≤ (n : ℝ) ^ 4 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity)) hlog0
  have hconst : (48 : ℝ) * 2 ^ 56 ≤ 2 ^ 62 := by norm_num
  calc 24 * 2 ^ 56 * T * (2 * (n : ℝ) * rfac)
      = 48 * 2 ^ 56 * ((n : ℝ) ^ 4 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)) := by
        rw [hT]; ring
    _ ≤ 2 ^ 62 * ((n : ℝ) ^ 4 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)) :=
        mul_le_mul_of_nonneg_right hconst hQ0
    _ = 2 ^ 62 * (n : ℝ) ^ 4 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R) := by ring

/-- **The `IsBigO` form — `O(n⁴)` per sample.**

`γ`, `R` and `rfac` are *fixed constants* of the statement and the warmness/accuracy
schedules `M`, `ε'` are functions of `n` constrained by named hypotheses; the implied
constant is `2⁶²·rfac·(R²/γ²)·log(2R)`, visible in the proof.  Nothing is hidden in the
`O(·)` that is not a hypothesis here. -/
theorem isBigO_samplePrice_quartic {γ R rfac : ℝ} {M epsPrime : ℕ → ℝ}
    (hrfac : 1 ≤ rfac) (hR1 : 1 ≤ R) (hγ0 : 0 < γ) (hγR : γ ≤ R)
    (hM1 : ∀ n, 1 ≤ M n) (hMB : ∀ n : ℕ, M n ≤ (2 * R) ^ n)
    (heps0 : ∀ n, 0 < epsPrime n) (heps1 : ∀ n, epsPrime n ≤ 1)
    (hepsn : ∀ n : ℕ, 1 / 2 ^ n ≤ epsPrime n) :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => (samplePrice n γ R (M n) (epsPrime n) rfac : ℝ))
      (fun n : ℕ => (n : ℝ) ^ 4) := by
  refine Asymptotics.IsBigO.of_bound
    (2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have h := samplePrice_le_quartic n hn hrfac hR1 hγ0 hγR (hM1 n) (hMB n)
    (heps0 n) (heps1 n) (hepsn n)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 4)]
  calc (samplePrice n γ R (M n) (epsPrime n) rfac : ℝ)
      ≤ 2 ^ 62 * (n : ℝ) ^ 4 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R) := h
    _ = 2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R) * (n : ℝ) ^ 4 := by ring

/-- **The paper's `O(n⁵)` per sample follows, and is therefore *loose*, not false.**

`O(n⁴) ⊆ O(n⁵)`.  This corollary exists so that the relationship between the two claims is
in the development rather than only in prose: what `thm:runtime`'s rewritten proof asserts
is implied by `Ttc.SamplerCost.isBigO_samplePrice_quartic`, which is strictly stronger. -/
theorem isBigO_samplePrice_quintic {γ R rfac : ℝ} {M epsPrime : ℕ → ℝ}
    (hrfac : 1 ≤ rfac) (hR1 : 1 ≤ R) (hγ0 : 0 < γ) (hγR : γ ≤ R)
    (hM1 : ∀ n, 1 ≤ M n) (hMB : ∀ n : ℕ, M n ≤ (2 * R) ^ n)
    (heps0 : ∀ n, 0 < epsPrime n) (heps1 : ∀ n, epsPrime n ≤ 1)
    (hepsn : ∀ n : ℕ, 1 / 2 ^ n ≤ epsPrime n) :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => (samplePrice n γ R (M n) (epsPrime n) rfac : ℝ))
      (fun n : ℕ => (n : ℝ) ^ 5) := by
  refine (isBigO_samplePrice_quartic hrfac hR1 hγ0 hγR hM1 hMB heps0 heps1 hepsn).trans ?_
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 4),
    Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 5)]
  nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ)) 4]

end Asymptotic

/-! ## Non-vacuity (`CLAUDE.md` §11)

A `∀`-statement over unsatisfiable hypotheses proves nothing.  The witness below shows the
hypothesis bundles of `Ttc.SamplerCost.drawWork_le_samplePrice` and
`Ttc.SamplerCost.samplePrice_le_quartic` are **simultaneously satisfiable**, and that the
price at the witness is a genuine positive natural, not `0`.

Not covered, and stated so: `Ttc.SamplerCost.hitAndRunBackend` additionally needs an
`Oracles n ι` together with the caller's own semantic certificates; inhabiting *those* is
the caller's obligation, since the specs are the caller's parameters.  And nothing here
inhabits `Ttc.HitAndRunTheorem11Input` — see the module docstring. -/

section Witness

/-- **The regime hypotheses of this file are satisfiable, at a price that is positive.**

`n = 1`, `γ = R = M = rfac = Vi = 1`, `ε' = 1/2` (so `1/2ⁿ ≤ ε'` is tight). -/
theorem exists_nondegenerate_price :
    ∃ (n : ℕ) (γ R M epsPrime rfac Vi : ℝ),
      1 ≤ n ∧ 1 ≤ rfac ∧ 1 ≤ R ∧ 0 < γ ∧ γ ≤ R ∧ 1 ≤ M ∧ M ≤ (2 * R) ^ n ∧
      0 < epsPrime ∧ epsPrime ≤ 1 ∧ 1 / 2 ^ n ≤ epsPrime ∧
      0 < Vi ∧ Vi ≤ (2 * R) ^ n ∧ epsPrime / (4 * Vi) ≤ 1 ∧
      0 < samplePrice n γ R M epsPrime rfac := by
  refine ⟨1, 1, 1, 1, 1 / 2, 1, 1, le_refl 1, le_refl 1, le_refl 1, one_pos, le_refl 1,
    le_refl 1, by norm_num, by norm_num, by norm_num, by norm_num, one_pos, by norm_num,
    by norm_num, ?_⟩
  have hc : stepOpCharge 1 1 = 1 := by
    unfold stepOpCharge; norm_num
  unfold samplePrice drawOpCharge
  rw [hc]
  omega

end Witness

end Ttc.SamplerCost

/-! ## Axiom profile

Target for every line: `[propext, Classical.choice, Quot.sound]`.

Note what `#print axioms` **cannot** see, and what the module docstring therefore says
instead: `Ttc.SamplerCost.stepOpCharge` is a modelling `def` (no executable is measured by
it), and every step count here is meaningful only given the *assumed*
`Ttc.HitAndRunTheorem11Input`. -/

-- Section 1: the `cor:linf` audit
#print axioms Ttc.SamplerCost.corlinf_lower_expand
#print axioms Ttc.SamplerCost.corlinf_lower_relax
#print axioms Ttc.SamplerCost.corlinf_upper_seven
#print axioms Ttc.SamplerCost.corlinf_upper_relax
#print axioms Ttc.SamplerCost.corlinf_condition_ratio
#print axioms Ttc.SamplerCost.corlinf_rounds_le
#print axioms Ttc.SamplerCost.exp_le_one_add_two_mul
#print axioms Ttc.SamplerCost.one_add_div_pow_le
#print axioms Ttc.SamplerCost.corlinf_inflation_pow
#print axioms Ttc.SamplerCost.corlinf_kappa_le
#print axioms Ttc.SamplerCost.kappa_le_of_corrected_c
#print axioms Ttc.SamplerCost.corlinf_kappa_div_gamma
#print axioms Ttc.SamplerCost.paper_escape_constant_unsupported
#print axioms Ttc.SamplerCost.corrected_escape_constant
#print axioms Ttc.SamplerCost.corlinf_upper_with_nu
#print axioms Ttc.SamplerCost.sqrt_add_sqrt_le
#print axioms Ttc.SamplerCost.sqrt_four_mul

-- Section 2: the price
#print axioms Ttc.SamplerCost.stepOpCharge
#print axioms Ttc.SamplerCost.samplePrice
#print axioms Ttc.SamplerCost.drawOpCharge
#print axioms Ttc.SamplerCost.worstTol
#print axioms Ttc.SamplerCost.stepsPrice
#print axioms Ttc.SamplerCost.drawWork
#print axioms Ttc.SamplerCost.hitAndRunTheorem11Threshold_le_of
#print axioms Ttc.SamplerCost.hitAndRunTheorem11Steps_le_of
#print axioms Ttc.SamplerCost.worstTol_le
#print axioms Ttc.SamplerCost.drawWork_le_samplePrice

-- STEP 2: the rejection factor
#print axioms Ttc.SamplerCost.expected_draws_le_three_halves
#print axioms Ttc.SamplerCost.expected_loop_ops_le

-- STEP 3: the backend and the run-level charge
#print axioms Ttc.SamplerCost.hitAndRunBackend
#print axioms Ttc.SamplerCost.hitAndRunBackend_samplePrice
#print axioms Ttc.SamplerCost.backendCost_le_ttcComplexity_hitAndRun

-- STEP 4: the asymptotics
#print axioms Ttc.SamplerCost.logArg_le
#print axioms Ttc.SamplerCost.log_logArg_le
#print axioms Ttc.SamplerCost.stepsPrice_le
#print axioms Ttc.SamplerCost.samplePrice_le_quartic
#print axioms Ttc.SamplerCost.isBigO_samplePrice_quartic
#print axioms Ttc.SamplerCost.isBigO_samplePrice_quintic

-- Non-vacuity
#print axioms Ttc.SamplerCost.exists_nondegenerate_price
