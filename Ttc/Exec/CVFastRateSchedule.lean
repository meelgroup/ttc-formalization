/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.CVSlowFullBodySourceSchedule
import Ttc.Volume.CVCorrectedRuntime
import Arlib.Convexity.GaussianCooling.PhaseSchedule

/-!
# A rate-generic Gaussian cooling schedule, and the `1/√n` specialisation

## What pins the cooling rate

The slow canonical route cools at the fixed rate `α = 1/n`
(`Ttc.CVSlowFullBodySourceSchedule.slowSourceSigmaSq`), and therefore needs
`Θ(n · log(N/s0))` phases.  The question this file answers is *what forces that rate*.

**It is not the per-phase variance analysis.**  The Cousins–Vempala per-phase budget is

  `Arlib.GaussianCooling.phaseVarBudget n α = (n+1)·α²/(1-α²)`

(`Arlib/Convexity/GaussianCooling/IndicatorVariance.lean:151`), which is `Θ(n α²)`, **not**
`Θ(n α)`.  The unconditional per-phase variance bound for the indicator of a convex body,
`Arlib.GaussianCooling.variance_le_exp_indicator`, assumes only `0 ≤ α < 1` — no `α ≤ 1/n`.
Consequently `α = 1/√n` gives a per-phase budget that is `Θ(1)`, not `Θ(1/n)`:
`phaseVarBudget_inv_sqrt` below computes it **exactly** as `(n+1)/(n-1)`, and
`phaseVarBudget_inv_sqrt_le_three` bounds it by `3` for every `n ≥ 2`.

What actually pins the rate is the *shape of the budget the consumer declares*:

* Under the one-sample-per-phase shape `1 + κ/m`, `Arlib.GaussianCooling.generalPhaseCount_ge_of_budget`
  (`Arlib/Convexity/GaussianCooling/GeneralRate.lean:263`) proves the matching **lower** bound
  `m ≥ (n+1)(log T)²/κ`, and `generalCoolRate_lt_fixedRate` (`:330`) proves the admissible rate
  is strictly *below* `1/n`.  In that shape the rate cannot be raised at all.
* Under the `k`-samples-per-phase shape the slow route actually declares —
  `Ttc.CVCorrectedRuntime.correctedRuntimeSamples m eps = ⌈10⁵(m+1)/eps²⌉₊ + 1`
  (`Ttc/Volume/CVCorrectedRuntime.lean:156`) — the constraint is `m · (per-phase budget) ≤ k · κ`,
  and `k ∝ m/eps²` is exactly the provisioning for a **constant** per-phase budget.  That is
  the regime `α = 1/√n` lives in, and `correctedRuntimeSamples_covers_constant_budget` below
  certifies that the *existing* stream formula meets that constraint with a factor-500 margin.
  What is **not** verified here is that every consumer of the slow chain's accuracy proof
  reduces to this constraint shape; only the arithmetic is proved.

## What is landed here

* `fastSourceSigmaSq` / `fastSourcePhases` — the rate-generic schedule and phase count.
* `fastSourcePhases_lt` — the counting bound `m < 2·L/α + 1` with `L = max 0 (log (N/s0))`,
  via `Arlib.GaussianCooling.half_le_log_one_add` (`log(1+α) ≥ α/2` on `[0,1]`).
* `target_le_fastSourceSigmaSq_terminal` — the schedule really reaches `N`.
* `fastSourcePhases_inv_sqrt_lt` — the specialisation: `m < 2·√n·L + 1`, i.e. `Θ(√n · log(N/s0))`.
* `slowSourcePhases_ge` — the matching lower bound for the slow route, `m ≥ n·L`, so the
  contrast `Θ(n L)` vs `Θ(√n L)` is machine-checked from two one-sided bounds.
* `variance_le_exp_indicator_inv_sqrt` — `variance_le_exp_indicator` applied at `α = 1/√n`,
  with the resulting budget `(n+1)/(n-1) ≤ 3`, i.e. `Var(W) ≤ (e³-1)·E(W)²`.
* `correctedSampleBudget_covers_inv_sqrt` / `correctedRuntimeSamples_covers_constant_budget` —
  the slow route's declared sample budget `100000(m+1) ≤ k·eps²` contains no `n` at all, and
  numerically absorbs the constant per-phase factor the `1/√n` rate produces.  This is the
  arithmetic only — the slow chain's accuracy proof is not re-derived at the new rate.

## Scope (`CLAUDE.md` §11)

Nothing here rewires the slow canonical chain: `slowSourceSigmaSq` and its consumers are
untouched.  This file establishes that the rate is *admissible* and what the phase count
becomes; migrating the chain onto it is a separate, larger job.  The honest cost statement is
`correctedRuntimeSamples_covers_constant_budget` together with the observation recorded in
`fastSourcePhases_inv_sqrt_lt`'s docstring: the phase count falls by `√n`, and the *required*
per-phase stream count rises by `√n`, so the total sample count `m·k` under exact provisioning
is rate-invariant.  The win is in every cost that multiplies `m` but not `m·k`.

## Semantic `def`s (`CLAUDE.md` §11)

`fastSourceSigmaSq` and `fastSourcePhases` are closed-form abbreviations and nothing more; they
assert no property.  Everything claimed of them is proved below.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
-- The dimension `n` is carried in the signatures of `fastSourceSigmaSq` / `fastSourcePhases`
-- for uniformity with the slow canonical route even though the bodies are rate-driven.
set_option linter.unusedVariables false

namespace Ttc.CVFastRateSchedule

open Arlib.GaussianCooling
open Ttc.CVHybridSchedule
open Ttc.CVSlowFullBodySourceSchedule

/-! ## The rate-generic schedule -/

/-- The rate-generic variance schedule `σᵢ² = s0·(1+α)ⁱ`.

A closed-form abbreviation and nothing more.  At `α = 1/n` it is definitionally the slow
canonical schedule (`fastSourceSigmaSq_fixed_rate`). -/
noncomputable def fastSourceSigmaSq (n : Nat) (alpha s0 : Real) (i : Nat) : Real :=
  Arlib.GaussianCooling.geomSchedule s0 alpha i

/-- The rate-generic phase count: the number of `(1+α)` steps needed to grow `s0` to `N`.

A closed-form abbreviation and nothing more.  At `α = 1/n` it agrees with
`Ttc.CVSlowFullBodySourceSchedule.slowSourcePhases` (`fastSourcePhases_fixed_rate`). -/
noncomputable def fastSourcePhases (n : Nat) (alpha N s0 : Real) : Nat :=
  ⌈max 0 (Real.log (N / s0)) / Real.log (1 + alpha)⌉₊

/-! ### Bridge to the slow canonical route

Both definitions specialise to the existing ones at `α = 1/n`, unconditionally. -/

/-- At the fixed rate the generic schedule *is* the slow canonical schedule. -/
theorem fastSourceSigmaSq_fixed_rate (n : Nat) (s0 : Real) (i : Nat) :
    fastSourceSigmaSq n (1 / (n : Real)) s0 i = slowSourceSigmaSq n s0 i := rfl

/-- At the fixed rate the generic phase count *is* the slow canonical phase count.

`slowSourcePhases n N s0 = coldPhases n (s0 / N)` and `log (1 / (s0 / N)) = log (N / s0)`, so
this holds with no hypotheses at all. -/
theorem fastSourcePhases_fixed_rate (n : Nat) (N s0 : Real) :
    fastSourcePhases n (1 / (n : Real)) N s0 = slowSourcePhases n N s0 := by
  unfold fastSourcePhases slowSourcePhases coldPhases
  rw [one_div_div]

/-! ## The counting bound

The key step is `Arlib.GaussianCooling.half_le_log_one_add`: `log (1 + α) ≥ α/2` on `[0,1]`. -/

/-- **The counting bound.**  For `0 < α ≤ 1`,

  `fastSourcePhases n α N s0 < 2·max 0 (log (N/s0)) / α + 1`.

Proof: `⌈x⌉₊ < x + 1` for `x ≥ 0`, and `x = L/log(1+α) ≤ L/(α/2) = 2L/α` since
`log(1+α) ≥ α/2`. -/
theorem fastSourcePhases_lt {alpha : Real} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (n : Nat) (N s0 : Real) :
    (fastSourcePhases n alpha N s0 : Real)
      < 2 * max 0 (Real.log (N / s0)) / alpha + 1 := by
  have hlogpos : 0 < Real.log (1 + alpha) :=
    Real.log_pos (by linarith)
  have hhalf : alpha / 2 ≤ Real.log (1 + alpha) :=
    Arlib.GaussianCooling.half_le_log_one_add halpha0.le halpha1
  have hL0 : (0 : Real) ≤ max 0 (Real.log (N / s0)) := le_max_left _ _
  have hratio : max 0 (Real.log (N / s0)) / Real.log (1 + alpha)
      ≤ 2 * max 0 (Real.log (N / s0)) / alpha := by
    rw [div_le_div_iff₀ hlogpos halpha0]
    nlinarith
  have hceil : (fastSourcePhases n alpha N s0 : Real)
      < max 0 (Real.log (N / s0)) / Real.log (1 + alpha) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  linarith

/-! ## The schedule reaches its target -/

/-- **The declared terminal phase reaches the requested target variance**, at any positive
rate.  The rate-generic analogue of
`Ttc.CVSlowFullBodySourceSchedule.target_le_slowSourceSigmaSq_terminal`. -/
theorem target_le_fastSourceSigmaSq_terminal
    {alpha : Real} (halpha0 : 0 < alpha) {n : Nat} {N s0 : Real}
    (hN : 0 < N) (hs0 : 0 < s0) (hsN : s0 ≤ N) :
    N ≤ fastSourceSigmaSq n alpha s0 (fastSourcePhases n alpha N s0) := by
  set m : Nat := fastSourcePhases n alpha N s0 with hm
  have hlogpos : 0 < Real.log (1 + alpha) := Real.log_pos (by linarith)
  have hceil : max 0 (Real.log (N / s0)) / Real.log (1 + alpha) ≤ (m : Real) :=
    Nat.le_ceil _
  rw [div_le_iff₀ hlogpos] at hceil
  have hlog : Real.log (N / s0) ≤ (m : Real) * Real.log (1 + alpha) :=
    le_trans (le_max_right _ _) hceil
  have hbase : (0 : Real) < 1 + alpha := by linarith
  have hpow : Real.log ((1 + alpha) ^ m) = (m : Real) * Real.log (1 + alpha) := by
    rw [Real.log_pow]
  have hquot : (0 : Real) < N / s0 := div_pos hN hs0
  have hpowpos : (0 : Real) < (1 + alpha) ^ m := pow_pos hbase m
  have hle : N / s0 ≤ (1 + alpha) ^ m := by
    have := Real.log_le_log_iff hquot hpowpos
    rw [hpow] at this
    exact this.1 hlog
  rw [div_le_iff₀ hs0] at hle
  unfold fastSourceSigmaSq Arlib.GaussianCooling.geomSchedule
  linarith [hle]

/-! ## The rate `α = 1/√n`

`n ≥ 2` throughout: at `n = 1` the rate is `1/√1 = 1`, which violates the `α < 1` hypothesis
of `Arlib.GaussianCooling.variance_le_exp_indicator`. -/

/-- `1 < √n` for `n ≥ 2`. -/
theorem one_lt_sqrt_nat {n : Nat} (hn : 2 ≤ n) : (1 : Real) < Real.sqrt (n : Real) := by
  have hn2 : (2 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hnn : (0 : Real) ≤ (n : Real) := by linarith
  have hsq : Real.sqrt (n : Real) ^ 2 = (n : Real) := Real.sq_sqrt hnn
  have hnonneg : (0 : Real) ≤ Real.sqrt (n : Real) := Real.sqrt_nonneg _
  nlinarith

/-- `0 < 1/√n` for `n ≥ 2`. -/
theorem inv_sqrt_pos {n : Nat} (hn : 2 ≤ n) : (0 : Real) < 1 / Real.sqrt (n : Real) := by
  have h := one_lt_sqrt_nat hn
  positivity

/-- `1/√n < 1` for `n ≥ 2` — the `α < 1` side condition of `variance_le_exp_indicator`. -/
theorem inv_sqrt_lt_one {n : Nat} (hn : 2 ≤ n) : (1 : Real) / Real.sqrt (n : Real) < 1 := by
  have h := one_lt_sqrt_nat hn
  rw [div_lt_one (by linarith)]
  exact h

/-- `(1/√n)² = 1/n`, the identity the whole `1/√n` analysis rests on. -/
theorem inv_sqrt_sq {n : Nat} (hn : 2 ≤ n) :
    ((1 : Real) / Real.sqrt (n : Real)) ^ 2 = 1 / (n : Real) := by
  have hn2 : (2 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hnn : (0 : Real) ≤ (n : Real) := by linarith
  rw [div_pow, one_pow, Real.sq_sqrt hnn]

/-! ### The per-phase variance budget at `α = 1/√n`

This is the Step 1 answer in one line: `phaseVarBudget n α = (n+1)α²/(1-α²)` is `Θ(nα²)`,
so at `α = 1/√n` the budget is `(n+1)/(n-1) = Θ(1)` — a *constant*, not `Θ(1/n)`.  Compare
`Arlib.GaussianCooling.phaseVarBudget_fixed_rate`: at `α = 1/n` the budget is `1/(n-1)`. -/

/-- **The budget at the `1/√n` cooling rate.**  `phaseVarBudget n (1/√n) = (n+1)/(n-1)` for
`n ≥ 2` — the exact analogue of `Arlib.GaussianCooling.phaseVarBudget_fixed_rate`'s
`phaseVarBudget n (1/n) = 1/(n-1)`. -/
theorem phaseVarBudget_inv_sqrt {n : Nat} (hn : 2 ≤ n) :
    phaseVarBudget n (1 / Real.sqrt (n : Real)) = ((n : Real) + 1) / ((n : Real) - 1) := by
  have hn2 : (2 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hn0 : (0 : Real) < (n : Real) := by linarith
  have hn1 : (0 : Real) < (n : Real) - 1 := by linarith
  rw [phaseVarBudget, inv_sqrt_sq hn]
  have hden : (1 : Real) - 1 / (n : Real) = ((n : Real) - 1) / (n : Real) := by
    field_simp
  rw [hden]
  field_simp

/-- **The budget is a constant.**  `phaseVarBudget n (1/√n) ≤ 3` for every `n ≥ 2`, with
equality at `n = 2`; it decreases to `1` as `n → ∞`.

This is the whole point: the variance analysis does **not** force `α ≤ 1/n`.  At `α = 1/√n`
the per-phase relative-variance factor is `e^{(n+1)/(n-1)} - 1 ≤ e³ - 1 < 20`, an absolute
constant. -/
theorem phaseVarBudget_inv_sqrt_le_three {n : Nat} (hn : 2 ≤ n) :
    phaseVarBudget n (1 / Real.sqrt (n : Real)) ≤ 3 := by
  have hn2 : (2 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hn1 : (0 : Real) < (n : Real) - 1 := by linarith
  rw [phaseVarBudget_inv_sqrt hn, div_le_iff₀ hn1]
  linarith

/-! ### The phase count at `α = 1/√n`: `Θ(√n · log (N/s0))` -/

/-- **The headline count.**  At the rate `α = 1/√n` the schedule needs

  `fastSourcePhases n (1/√n) N s0 < 2·√n·max 0 (log (N/s0)) + 1`

phases — `Θ(√n · log (N/s0))`, against the slow route's `Θ(n · log (N/s0))`
(`slowSourcePhases_ge` below is the matching lower bound for the slow route).

**Cost, stated honestly.**  The phase count falls by a factor `√n`, but the per-phase budget
rises from `1/(n-1)` to `(n+1)/(n-1)` — a factor of `n`.  The accuracy constraint the
consumer must meet is `m · (per-phase budget) ≤ k · κ`, so the *required* stream count `k`
rises by `√n` and the total sample count `m·k` under exact provisioning is rate-invariant.
What is genuinely saved is every cost that multiplies `m` but not `m·k`.  Separately,
`correctedRuntimeSamples_covers_constant_budget` shows the slow route's declared stream
formula `k = ⌈10⁵(m+1)/eps²⌉₊ + 1` already provisions for a constant budget, so it needs no
change at `α = 1/√n`. -/
theorem fastSourcePhases_inv_sqrt_lt {n : Nat} (hn : 2 ≤ n) (N s0 : Real) :
    (fastSourcePhases n (1 / Real.sqrt (n : Real)) N s0 : Real)
      < 2 * Real.sqrt (n : Real) * max 0 (Real.log (N / s0)) + 1 := by
  have hs : (1 : Real) < Real.sqrt (n : Real) := one_lt_sqrt_nat hn
  have h := fastSourcePhases_lt (alpha := 1 / Real.sqrt (n : Real))
    (inv_sqrt_pos hn) (inv_sqrt_lt_one hn).le n N s0
  refine h.trans_le ?_
  have hrw : 2 * max 0 (Real.log (N / s0)) / (1 / Real.sqrt (n : Real))
      = 2 * Real.sqrt (n : Real) * max 0 (Real.log (N / s0)) := by
    field_simp
  rw [hrw]

/-- **The matching lower bound for the slow route.**  The fixed rate `1/n` really does cost
`Ω(n · log (N/s0))` phases:

  `n · max 0 (log (N/s0)) ≤ slowSourcePhases n N s0`.

Proof: `log (1 + 1/n) ≤ 1/n`, so `L/log(1+1/n) ≥ nL`, and `⌈·⌉₊` only increases.

Together with `fastSourcePhases_inv_sqrt_lt` this pins the contrast: `Θ(n L)` for the slow
route against `Θ(√n L)` at `α = 1/√n`. -/
theorem slowSourcePhases_ge {n : Nat} (hn : 1 ≤ n) (N s0 : Real) :
    (n : Real) * max 0 (Real.log (N / s0)) ≤ (slowSourcePhases n N s0 : Real) := by
  have hn1 : (1 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hn0 : (0 : Real) < (n : Real) := by linarith
  have hinv0 : (0 : Real) < 1 / (n : Real) := by positivity
  have hlogpos : 0 < Real.log (1 + 1 / (n : Real)) := Real.log_pos (by linarith)
  have hlogle : Real.log (1 + 1 / (n : Real)) ≤ 1 / (n : Real) := by
    have := Real.log_le_sub_one_of_pos (x := 1 + 1 / (n : Real)) (by linarith)
    linarith
  have hL0 : (0 : Real) ≤ max 0 (Real.log (N / s0)) := le_max_left _ _
  have hceil : max 0 (Real.log (N / s0)) / Real.log (1 + 1 / (n : Real))
      ≤ (slowSourcePhases n N s0 : Real) := by
    rw [← fastSourcePhases_fixed_rate n N s0]
    exact Nat.le_ceil _
  refine le_trans ?_ hceil
  rw [le_div_iff₀ hlogpos]
  have hmul : (n : Real) * max 0 (Real.log (N / s0)) * Real.log (1 + 1 / (n : Real))
      ≤ (n : Real) * max 0 (Real.log (N / s0)) * (1 / (n : Real)) :=
    mul_le_mul_of_nonneg_left hlogle (mul_nonneg hn0.le hL0)
  have hcancel : (n : Real) * max 0 (Real.log (N / s0)) * (1 / (n : Real))
      = max 0 (Real.log (N / s0)) := by
    field_simp
  linarith

/-! ### `variance_le_exp_indicator` at `α = 1/√n`

The hypotheses of `Arlib.GaussianCooling.variance_le_exp_indicator` are exactly
`Convex ℝ K`, `MeasurableSet K`, `0 < volume K`, `0 < σ`, `0 ≤ α`, `α < 1`.  Nothing in them
mentions `1/n`, so the only thing to check at `α = 1/√n` is `1/√n < 1`, i.e. `n ≥ 2`. -/

/-- **The per-phase variance bound holds at `α = 1/√n`, with a constant budget.**

For a convex measurable body `K ⊆ ℝⁿ` of positive volume, `σ > 0` and `n ≥ 2`, the per-phase
ratio estimator between the consecutive gaussians `σ²/(1 + 1/√n)` and `σ²` satisfies

  `Var(W) ≤ (e³ - 1)·E(W)²`.

`e³ - 1 < 20` is an absolute constant: the `1/√n` cooling rate is admissible for the
variance analysis, at a per-phase relative variance that does not grow with the dimension.
No `ZLogconcaveHypothesis`, no localization, no roundness. -/
theorem variance_le_exp_indicator_inv_sqrt {n : Nat} (hn : 2 ≤ n)
    {K : Set (EuclSpace n)} (hK : Convex Real K) (hKm : MeasurableSet K)
    (hvol : 0 < MeasureTheory.volume K) {sigma : Real} (hsigma : 0 < sigma) :
    (∫ x, (gW (Set.indicator K (1 : EuclSpace n → Real)) (sigma ^ 2) x
          / gW (Set.indicator K (1 : EuclSpace n → Real))
              (sigma ^ 2 / (1 + 1 / Real.sqrt (n : Real))) x) ^ 2
        * (gW (Set.indicator K (1 : EuclSpace n → Real))
              (sigma ^ 2 / (1 + 1 / Real.sqrt (n : Real))) x
          / G (Set.indicator K (1 : EuclSpace n → Real))
              (sigma ^ 2 / (1 + 1 / Real.sqrt (n : Real)))))
        - (∫ x, (gW (Set.indicator K (1 : EuclSpace n → Real)) (sigma ^ 2) x
              / gW (Set.indicator K (1 : EuclSpace n → Real))
                  (sigma ^ 2 / (1 + 1 / Real.sqrt (n : Real))) x)
            * (gW (Set.indicator K (1 : EuclSpace n → Real))
                  (sigma ^ 2 / (1 + 1 / Real.sqrt (n : Real))) x
              / G (Set.indicator K (1 : EuclSpace n → Real))
                  (sigma ^ 2 / (1 + 1 / Real.sqrt (n : Real))))) ^ 2
      ≤ (Real.exp 3 - 1)
        * (∫ x, (gW (Set.indicator K (1 : EuclSpace n → Real)) (sigma ^ 2) x
              / gW (Set.indicator K (1 : EuclSpace n → Real))
                  (sigma ^ 2 / (1 + 1 / Real.sqrt (n : Real))) x)
            * (gW (Set.indicator K (1 : EuclSpace n → Real))
                  (sigma ^ 2 / (1 + 1 / Real.sqrt (n : Real))) x
              / G (Set.indicator K (1 : EuclSpace n → Real))
                  (sigma ^ 2 / (1 + 1 / Real.sqrt (n : Real))))) ^ 2 := by
  have hbase := variance_le_exp_indicator (n := n) hK hKm hvol hsigma
    (inv_sqrt_pos hn).le (inv_sqrt_lt_one hn)
  refine hbase.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
  have := Real.exp_le_exp.2 (phaseVarBudget_inv_sqrt_le_three hn)
  linarith

/-! ### The declared stream count already covers a constant budget

The slow route declares `k = Ttc.CVCorrectedRuntime.correctedRuntimeSamples m eps`
`= ⌈10⁵(m+1)/eps²⌉₊ + 1`, i.e. `k ∝ m/eps²`.  The accuracy constraint a `k`-sample-averaged
`m`-phase product estimator must meet is `m · (per-phase budget) ≤ k · κ` with
`κ = Arlib.GaussianCooling.varBudget eps`.  At `α = 1/√n` the per-phase relative-variance
factor is `e^{(n+1)/(n-1)} - 1 ≤ e³ - 1 < 20`, so the constraint reads `20·m ≤ k·κ`, and the
declared `k` meets it with a factor-500 margin. -/

/-- **The declared stream count absorbs a constant per-phase budget.**  For `0 < eps ≤ 1`,

  `20 · m ≤ correctedRuntimeSamples m eps · varBudget eps`,

with room to spare (the true margin is `10⁴/20 = 500`).  Since `e³ - 1 < 20` bounds the
per-phase relative-variance factor at `α = 1/√n` (`phaseVarBudget_inv_sqrt_le_three`), the
slow route's *existing* stream formula needs no change **to meet this constraint**.

**Honest scope.**  Whether every consumer of the slow chain's accuracy proof reduces to this
constraint shape is *not* verified here; see `correctedSampleBudget_covers_inv_sqrt`.

Proof: `varBudget eps = log(1 + eps²/5) ≥ eps²/10` by
`Arlib.GaussianCooling.half_le_log_one_add`, and
`correctedRuntimeSamples m eps ≥ 10⁵(m+1)/eps²`. -/
theorem correctedRuntimeSamples_covers_constant_budget
    (m : Nat) {eps : Real} (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    20 * (m : Real)
      ≤ (Ttc.CVCorrectedRuntime.correctedRuntimeSamples m eps : Real) * varBudget eps := by
  have heps2 : (0 : Real) < eps ^ 2 := by positivity
  have heps2le : eps ^ 2 ≤ 1 := by nlinarith
  -- `varBudget eps ≥ eps²/10`
  have hvb : eps ^ 2 / 10 ≤ varBudget eps := by
    have h := Arlib.GaussianCooling.half_le_log_one_add
      (α := eps ^ 2 / 5) (by positivity) (by linarith)
    rw [varBudget]
    linarith
  -- `k ≥ 10⁵(m+1)/eps²`
  have hk : 100000 * ((m : Real) + 1) / eps ^ 2
      ≤ (Ttc.CVCorrectedRuntime.correctedRuntimeSamples m eps : Real) := by
    rw [Ttc.CVCorrectedRuntime.correctedRuntimeSamples]
    push_cast
    linarith [Nat.le_ceil (100000 * ((m : Real) + 1) / eps ^ 2)]
  have hkpos : (0 : Real) ≤ 100000 * ((m : Real) + 1) / eps ^ 2 := by positivity
  have hstep : 100000 * ((m : Real) + 1) / eps ^ 2 * (eps ^ 2 / 10)
      ≤ (Ttc.CVCorrectedRuntime.correctedRuntimeSamples m eps : Real) * varBudget eps :=
    mul_le_mul hk hvb (by positivity) (le_trans hkpos hk)
  have hcancel : 100000 * ((m : Real) + 1) / eps ^ 2 * (eps ^ 2 / 10)
      = 10000 * ((m : Real) + 1) := by
    field_simp
    ring
  rw [hcancel] at hstep
  have hm0 : (0 : Real) ≤ (m : Real) := Nat.cast_nonneg m
  linarith

/-- `e³ - 1 < 20`.  (`e³ = 20.0855…`, so the margin is real but thin; `Real.exp_one_lt_d9`
cubed is enough.) -/
theorem exp_three_sub_one_lt_twenty : Real.exp 3 - 1 < 20 := by
  have hcube : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hlt := Real.exp_one_lt_d9
  have hpos : (0 : Real) < Real.exp 1 := Real.exp_pos 1
  have hsq : Real.exp 1 * Real.exp 1 < 2.7182818286 * 2.7182818286 := by nlinarith
  have hstep : Real.exp 1 * (Real.exp 1 * Real.exp 1)
      < Real.exp 1 * (2.7182818286 * 2.7182818286) :=
    mul_lt_mul_of_pos_left hsq hpos
  have hfin : Real.exp 1 * (2.7182818286 * 2.7182818286) < 21 := by nlinarith
  have hpow : Real.exp 1 ^ 3 = Real.exp 1 * (Real.exp 1 * Real.exp 1) := by ring
  rw [hcube, hpow]
  linarith

/-- **The slow route's declared sample budget already pays for the `1/√n` rate.**

`Ttc.CVCorrected.CorrectedSampleBudget m k eps` is `100000·(m+1) ≤ k·eps²`
(`Ttc/Volume/CVCorrectedParameters.lean:42`) — note it contains **no `n` at all**, i.e. it is
provisioned for a per-phase relative-variance factor that is an absolute constant.  This
theorem cashes that in: whenever the declared budget holds and `0 < eps ≤ 1`,

  `m · (e^{phaseVarBudget n (1/√n)} - 1) ≤ k · varBudget eps`  for every `n ≥ 2`,

which is exactly the `k`-sample accuracy constraint at the `1/√n` cooling rate.  At `α = 1/n`
the left side is `m·(e^{1/(n-1)} - 1) = Θ(m/n)`, so the declared budget is over-provisioned
there by a factor `n`; at `α = 1/√n` it is provisioned correctly.

**Honest scope.**  This is the standard `k`-sample-averaged accuracy shape (see
`Arlib/Convexity/GaussianCooling/GeneralRate.lean:74-87` and the Cousins–Vempala accounting it
cites).  It shows the declared budget *numerically* absorbs a constant per-phase factor; it
does **not** re-derive the slow chain's accuracy proof at the new rate, which would require
re-instantiating every phase-moment lemma and is out of scope. -/
theorem correctedSampleBudget_covers_inv_sqrt
    {n m k : Nat} (hn : 2 ≤ n) {eps : Real} (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hbudget : Ttc.CVCorrected.CorrectedSampleBudget m k eps) :
    (m : Real) * (Real.exp (phaseVarBudget n (1 / Real.sqrt (n : Real))) - 1)
      ≤ (k : Real) * varBudget eps := by
  have heps2 : (0 : Real) < eps ^ 2 := by positivity
  have heps2le : eps ^ 2 ≤ 1 := by nlinarith
  have hm0 : (0 : Real) ≤ (m : Real) := Nat.cast_nonneg m
  have hk0 : (0 : Real) ≤ (k : Real) := Nat.cast_nonneg k
  -- `varBudget eps ≥ eps²/10`
  have hvb : eps ^ 2 / 10 ≤ varBudget eps := by
    have h := Arlib.GaussianCooling.half_le_log_one_add
      (α := eps ^ 2 / 5) (by positivity) (by linarith)
    rw [varBudget]
    linarith
  -- `k·varBudget eps ≥ k·eps²/10 ≥ 10⁴(m+1) ≥ 10⁴·m`
  have hlow : 10000 * ((m : Real) + 1) ≤ (k : Real) * varBudget eps := by
    have hb : 100000 * ((m : Real) + 1) ≤ (k : Real) * eps ^ 2 := hbudget
    nlinarith [mul_le_mul_of_nonneg_left hvb hk0]
  -- `e^{phaseVarBudget n (1/√n)} - 1 ≤ e³ - 1 < 20`
  have hfac : Real.exp (phaseVarBudget n (1 / Real.sqrt (n : Real))) - 1 < 20 := by
    have := Real.exp_le_exp.2 (phaseVarBudget_inv_sqrt_le_three hn)
    linarith [exp_three_sub_one_lt_twenty]
  nlinarith [mul_le_mul_of_nonneg_left hfac.le hm0]

/-! ## Axiom audit (`CLAUDE.md` §4) -/

#print axioms fastSourceSigmaSq_fixed_rate
#print axioms fastSourcePhases_fixed_rate
#print axioms fastSourcePhases_lt
#print axioms target_le_fastSourceSigmaSq_terminal
#print axioms one_lt_sqrt_nat
#print axioms inv_sqrt_pos
#print axioms inv_sqrt_lt_one
#print axioms inv_sqrt_sq
#print axioms phaseVarBudget_inv_sqrt
#print axioms phaseVarBudget_inv_sqrt_le_three
#print axioms fastSourcePhases_inv_sqrt_lt
#print axioms slowSourcePhases_ge
#print axioms variance_le_exp_indicator_inv_sqrt
#print axioms correctedRuntimeSamples_covers_constant_budget
#print axioms exp_three_sub_one_lt_twenty
#print axioms correctedSampleBudget_covers_inv_sqrt

end Ttc.CVFastRateSchedule
