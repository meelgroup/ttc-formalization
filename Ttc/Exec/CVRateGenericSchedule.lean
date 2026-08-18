/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.CVFastRateSchedule

/-!
# The rate-generic cooling schedule layer, and the two levers it exposes

## Why this file exists

`Ttc.CVSlowFullBodySourceSchedule.slowSourceSigmaSq n s0 = geomSchedule s0 (1/n)`
(`Ttc/Exec/CVSlowFullBodySourceSchedule.lean:36`) pins the slow canonical route to the
cooling rate `α = 1/n`, hence to `Θ(n · log (N/s0))` phases.  `Ttc.CVFastRateSchedule`
established that the *variance* analysis does not force this: `phaseVarBudget n α` is
`Θ(n α²)`, so `α = 1/√n` gives a constant per-phase budget.

This file supplies the **schedule layer** at a general rate — the five lemmas that the
slow chain's schedule-consuming lemmas actually use (positivity, the successor identity,
`s0 ≤ σᵢ`, `σᵢ ≤ σᵢ₊₁`, `i ≤ j → σᵢ ≤ σⱼ`) — plus the two quantitative facts that make the
rate an *optimisation* rather than a free parameter:

* `rateSigmaSq_inv_gap` — the rate-generic form of `Ttc.CVSharpScoreTransport.slowSourceSigmaSq_inv_gap`
  (`Ttc/Exec/CVSharpScoreTransport.lean:116`).  The reciprocal gap is `α / (σᵢ(1+α))`,
  so the sharp score-transport exponent is `R²α / (2 σᵢ (1+α))`.
* `rateScoreExponent_mono_alpha` — that exponent is **increasing** in `α`, while
  `ratePhaseCountBound_antitone_alpha` records that the phase-count bound `2L/α` is
  **decreasing** in `α`.  Both levers, stated in one place.

## The obstruction this file also records

The audit of the slow chain found exactly one layer where the numeric value `1/n` is
load-bearing rather than merely a source of positivity/monotonicity: the **accepted-seed
warm factor**.

`Ttc.CVGaussianAdaptiveAcceptedWarm.acceleratedSeedWarmFactor n cc = ofReal (2 · √cc ^ n)`
(`Ttc/Exec/CVGaussianAdaptiveAcceptedWarm.lean:38`) is bounded by `2e` only through
`Ttc.CVSwitchedSmallRateUniversalWarm.acceleratedSeedWarmFactor_one_add_le_two_exp`
(`Ttc/Exec/CVSwitchedSmallRateUniversalWarm.lean:17`), whose hypothesis is literally
`hr : r ≤ 1 / (n : Real)`, and which
`Ttc.CVSlowFullBodySourceSchedule.slowFullBodyWarmFactor_le_two_exp`
(`Ttc/Exec/CVSlowFullBodySourceSchedule.lean:104`) discharges with `le_rfl` — i.e. the slow
route sits exactly on the boundary of that hypothesis.

`exp_rate_le_seedWarmFactor` below quantifies what happens off that boundary: the warm
factor is at least `2·exp(nα/4)`.  At `α = 1/n` that is `2·e^{1/4}`, harmless.  At
`α = 1/√n` it is `2·e^{√n/4}`, and `two_exp_lt_seedWarmFactor_inv_sqrt` proves the `2e`
bound genuinely **fails** for every `n ≥ 17`.  That is the concrete blocker for
re-instantiating the slow chain at `α = 1/√n`, and it is a re-proof, not a re-instantiation.

## Scope (`CLAUDE.md` §11)

Nothing here rewires the slow canonical chain.  `rateSigmaSq` is a closed-form abbreviation;
`rateSigmaSq_fixed_rate` shows the existing chain is literally its `α = 1/n` instance.

## Relation to `Ttc.CVFastRateSchedule`

`rateSigmaSq` and `Ttc.CVFastRateSchedule.fastSourceSigmaSq` are definitionally the same
function (`rateSigmaSq_eq_fastSourceSigmaSq`, by `rfl`).  The new content here is the lemma
family, which `CVFastRateSchedule` does not provide: it proved facts about the *phase count*
and the *variance budget*, not about the schedule's order structure or its score gap.

## Semantic `def`s (`CLAUDE.md` §11)

`rateSigmaSq` asserts no property; everything claimed of it is proved below.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
-- `n` is carried in `rateSigmaSq`'s signature for uniformity with the slow canonical route
-- even though the body is rate-driven and does not mention it.
set_option linter.unusedVariables false

namespace Ttc.CVRateGenericSchedule

open Arlib.GaussianCooling
open Ttc.CVSlowFullBodySourceSchedule

/-! ## The rate-generic schedule -/

/-- The rate-generic variance schedule `σᵢ² = s0 · (1 + α)ⁱ`.

A closed-form abbreviation and nothing more.  At `α = 1/n` it is *definitionally* the slow
canonical schedule (`rateSigmaSq_fixed_rate`). -/
noncomputable def rateSigmaSq (n : Nat) (alpha s0 : Real) (i : Nat) : Real :=
  Arlib.GaussianCooling.geomSchedule s0 alpha i

/-- **The existing slow chain is the `α = 1/n` instance**, as functions of the phase index,
with no hypotheses at all. -/
theorem rateSigmaSq_fixed_rate (n : Nat) (s0 : Real) :
    rateSigmaSq n (1 / (n : Real)) s0 = slowSourceSigmaSq n s0 := rfl

/-- No duplication with `Ttc.CVFastRateSchedule.fastSourceSigmaSq`: they are the same
function.  That file proves phase-count and variance-budget facts; this one proves the
schedule's order structure and its score gap. -/
theorem rateSigmaSq_eq_fastSourceSigmaSq (n : Nat) (alpha s0 : Real) :
    rateSigmaSq n alpha s0 = Ttc.CVFastRateSchedule.fastSourceSigmaSq n alpha s0 := rfl

/-! ## The five schedule lemmas the slow chain consumes

The audit found that every schedule-consuming lemma in the slow chain outside the
accepted-seed warm layer uses `slowSourceSigmaSq` only through these five facts.  Each holds
at *any* nonnegative (resp. positive) rate. -/

/-- Rate-generic form of `Ttc.CVSlowFullBodySourceSchedule.slowSourceSigmaSq_pos`. -/
theorem rateSigmaSq_pos (n : Nat) {alpha s0 : Real} (halpha : 0 ≤ alpha) (hs0 : 0 < s0)
    (i : Nat) :
    0 < rateSigmaSq n alpha s0 i := by
  unfold rateSigmaSq
  exact geomSchedule_pos hs0 (by linarith) i

/-- Rate-generic form of `Ttc.CVSlowFullBodySourceSchedule.slowSourceSigmaSq_succ`.
No hypotheses: the successor identity is the definition. -/
theorem rateSigmaSq_succ (n : Nat) (alpha s0 : Real) (i : Nat) :
    rateSigmaSq n alpha s0 (i + 1) = rateSigmaSq n alpha s0 i * (1 + alpha) := by
  unfold rateSigmaSq
  rw [geomSchedule_succ]

/-- Rate-generic form of `Ttc.CVSlowCanonicalShareBounds.slowSourceSigmaSq_mono_start`
(`Ttc/Exec/CVSlowCanonicalShareBounds.lean:49`). -/
theorem rateSigmaSq_mono_start (n : Nat) {alpha s0 : Real} (halpha : 0 ≤ alpha)
    (hs0 : 0 < s0) (i : Nat) :
    s0 ≤ rateSigmaSq n alpha s0 i := by
  unfold rateSigmaSq geomSchedule
  have hbase : (1 : Real) ≤ 1 + alpha := by linarith
  have hp : (1 : Real) ≤ (1 + alpha) ^ i := one_le_pow₀ hbase
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hs0.le

/-- Rate-generic form of `Ttc.CVSlowCanonicalShareBounds.slowSourceSigmaSq_mono_succ`
(`Ttc/Exec/CVSlowCanonicalShareBounds.lean:58`). -/
theorem rateSigmaSq_mono_succ (n : Nat) {alpha s0 : Real} (halpha : 0 ≤ alpha)
    (hs0 : 0 < s0) (i : Nat) :
    rateSigmaSq n alpha s0 i ≤ rateSigmaSq n alpha s0 (i + 1) := by
  rw [rateSigmaSq_succ]
  have hs := rateSigmaSq_pos n halpha hs0 i
  nlinarith

/-- Rate-generic form of `Ttc.CVSlowCanonicalDeadlineCost.slowSourceSigmaSq_le_terminal`
(`Ttc/Exec/CVSlowCanonicalDeadlineCost.lean:47`). -/
theorem rateSigmaSq_le_terminal (n : Nat) {alpha s0 : Real} (halpha : 0 < alpha)
    (hs0 : 0 < s0) {i j : Nat} (hij : i ≤ j) :
    rateSigmaSq n alpha s0 i ≤ rateSigmaSq n alpha s0 j := by
  unfold rateSigmaSq
  exact (geomSchedule_strictMono hs0 halpha).monotone hij

/-! ## The sharp score gap at a general rate

`Ttc.CVSharpScoreTransport.slowSourceSigmaSq_inv_gap`
(`Ttc/Exec/CVSharpScoreTransport.lean:116`) computes the reciprocal gap on the slow schedule
as `1 / (σᵢ (n+1))`.  That is the `α = 1/n` case of the following. -/

/-- **The rate-generic reciprocal gap.**

  `1/σᵢ − 1/σᵢ₊₁ = α / (σᵢ (1 + α))`.

Since the phase score bound is `exp(R²/2 · (1/σᵢ − 1/σᵢ₊₁))`, this says the sharp transport
exponent at rate `α` is `R² α / (2 σᵢ (1 + α))` — see `rateScoreExponent_eq`.  A *larger*
rate makes the transport bound *worse* (`rateScoreExponent_mono_alpha`). -/
theorem rateSigmaSq_inv_gap (n : Nat) {alpha s0 : Real} (halpha : 0 ≤ alpha)
    (hs0 : 0 < s0) (i : Nat) :
    1 / rateSigmaSq n alpha s0 i - 1 / rateSigmaSq n alpha s0 (i + 1)
      = alpha / (rateSigmaSq n alpha s0 i * (1 + alpha)) := by
  have hs : 0 < rateSigmaSq n alpha s0 i := rateSigmaSq_pos n halpha hs0 i
  have ha : (0 : Real) < 1 + alpha := by linarith
  rw [rateSigmaSq_succ]
  field_simp
  ring

/-- **Consistency with the sharp slow-schedule computation.**  At `α = 1/n` the rate-generic
exponent `R²α/(2σᵢ(1+α))` is exactly the `R²/(2σᵢ(n+1))` of
`Ttc.CVSharpScoreTransport.coolRatio_slowSource_le`
(`Ttc/Exec/CVSharpScoreTransport.lean:127`). -/
theorem rateScoreExponent_fixed_rate {n : Nat} (hn : 1 ≤ n) {s0 R : Real} (hs0 : 0 < s0)
    (i : Nat) :
    R ^ 2 * (1 / (n : Real))
        / (2 * rateSigmaSq n (1 / (n : Real)) s0 i * (1 + 1 / (n : Real)))
      = R ^ 2 / (2 * slowSourceSigmaSq n s0 i * ((n : Real) + 1)) := by
  have hn0 : (0 : Real) < (n : Real) := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hs : 0 < slowSourceSigmaSq n s0 i := slowSourceSigmaSq_pos hn hs0 i
  rw [rateSigmaSq_fixed_rate]
  field_simp

/-- **The score-transport exponent in gap form.**  `R²/2 · (1/σᵢ − 1/σᵢ₊₁) = R²α/(2σᵢ(1+α))`:
the shape in which `Ttc.CVSharpScoreTransport.coolRatio_le_of_norm_le` consumes the gap. -/
theorem rateScoreExponent_eq (n : Nat) {alpha s0 R : Real} (halpha : 0 ≤ alpha)
    (hs0 : 0 < s0) (i : Nat) :
    R ^ 2 / 2 * (1 / rateSigmaSq n alpha s0 i - 1 / rateSigmaSq n alpha s0 (i + 1))
      = R ^ 2 * alpha / (2 * rateSigmaSq n alpha s0 i * (1 + alpha)) := by
  have hs : 0 < rateSigmaSq n alpha s0 i := rateSigmaSq_pos n halpha hs0 i
  have ha : (0 : Real) < 1 + alpha := by linarith
  rw [rateSigmaSq_inv_gap n halpha hs0 i]
  field_simp

/-! ## Lever 3 against lever 1: the trade-off, stated

Raising the rate `α` cuts the phase count (`ratePhaseCountBound_antitone_alpha`) and
inflates the sharp score-transport exponent (`rateScoreExponent_mono_alpha`).  Nobody had
written both down in one place. -/

/-- **The sharp transport exponent is increasing in the rate.**

  `α ≤ α'  ⟹  R²α / (2s(1+α)) ≤ R²α' / (2s(1+α'))`.

Combined with `ratePhaseCountBound_antitone_alpha` this is the real optimisation: the
phase count falls like `1/α` while the per-phase score bound grows like `exp(Θ(α))`. -/
theorem rateScoreExponent_mono_alpha {R s alpha alpha' : Real} (hs : 0 < s)
    (halpha : 0 ≤ alpha) (h : alpha ≤ alpha') :
    R ^ 2 * alpha / (2 * s * (1 + alpha)) ≤ R ^ 2 * alpha' / (2 * s * (1 + alpha')) := by
  have ha : (0 : Real) < 1 + alpha := by linarith
  have ha' : (0 : Real) < 1 + alpha' := by linarith
  have hR : (0 : Real) ≤ R ^ 2 := sq_nonneg R
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg hR hs.le) (sub_nonneg.2 h)]

/-- **The phase-count bound is decreasing in the rate.**  The counting bound of
`Ttc.CVFastRateSchedule.fastSourcePhases_lt` is `2L/α + 1`, and `2L/α` is antitone in `α`
for `L ≥ 0`.  This is the other half of the trade-off. -/
theorem ratePhaseCountBound_antitone_alpha {L alpha alpha' : Real} (hL : 0 ≤ L)
    (halpha : 0 < alpha) (h : alpha ≤ alpha') :
    2 * L / alpha' ≤ 2 * L / alpha := by
  have ha' : (0 : Real) < alpha' := lt_of_lt_of_le halpha h
  exact div_le_div_of_nonneg_left (by linarith) halpha h

/-! ## The concrete obstruction: the accepted-seed warm factor

`Ttc.CVGaussianAdaptiveAcceptedWarm.acceleratedSeedWarmFactor n cc = ofReal (2 · √cc ^ n)`
(`Ttc/Exec/CVGaussianAdaptiveAcceptedWarm.lean:38`).  At `cc = 1 + α` this is
`2 · (1+α)^{n/2}`, which is `≤ 2e` only when `nα = O(1)`.  The two lemmas below quantify
that, and show the `2e` bound the slow chain depends on **fails** at `α = 1/√n`. -/

/-- `exp(nα/4) ≤ √(1+α) ^ n` for `0 ≤ α ≤ 1`.

Proof: `log(√(1+α)^n) = (n/2)·log(1+α) ≥ (n/2)·(α/2)` by
`Arlib.GaussianCooling.half_le_log_one_add`. -/
theorem exp_rate_le_sqrt_pow (n : Nat) {alpha : Real}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) :
    Real.exp ((n : Real) * alpha / 4) ≤ Real.sqrt (1 + alpha) ^ n := by
  have ha : (0 : Real) < 1 + alpha := by linarith
  have hspos : 0 < Real.sqrt (1 + alpha) := Real.sqrt_pos.2 ha
  have hpow : (0 : Real) < Real.sqrt (1 + alpha) ^ n := pow_pos hspos n
  have hlog : alpha / 2 ≤ Real.log (1 + alpha) :=
    Arlib.GaussianCooling.half_le_log_one_add halpha0 halpha1
  have hn0 : (0 : Real) ≤ (n : Real) := Nat.cast_nonneg n
  have hlp : Real.log (Real.sqrt (1 + alpha) ^ n)
      = (n : Real) * (Real.log (1 + alpha) / 2) := by
    rw [Real.log_pow, Real.log_sqrt ha.le]
  have hge : (n : Real) * alpha / 4 ≤ Real.log (Real.sqrt (1 + alpha) ^ n) := by
    rw [hlp]; nlinarith
  calc Real.exp ((n : Real) * alpha / 4)
      ≤ Real.exp (Real.log (Real.sqrt (1 + alpha) ^ n)) := Real.exp_le_exp.2 hge
    _ = Real.sqrt (1 + alpha) ^ n := Real.exp_log hpow

/-- **The accepted-seed warm factor grows like `exp(nα/4)`.**

  `ofReal (2·exp(nα/4)) ≤ acceleratedSeedWarmFactor n (1 + α)`  for `0 ≤ α ≤ 1`.

At the slow rate `α = 1/n` the left side is `2e^{1/4}`, consistent with the `2e` bound of
`Ttc.CVSwitchedSmallRateUniversalWarm.acceleratedSeedWarmFactor_one_add_le_two_exp`.  At
`α = 1/√n` it is `2e^{√n/4}` — exponential in `√n`. -/
theorem exp_rate_le_seedWarmFactor (n : Nat) {alpha : Real}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) :
    ENNReal.ofReal (2 * Real.exp ((n : Real) * alpha / 4))
      ≤ Ttc.CVGaussianAdaptiveAcceptedWarm.acceleratedSeedWarmFactor n (1 + alpha) := by
  unfold Ttc.CVGaussianAdaptiveAcceptedWarm.acceleratedSeedWarmFactor
  exact ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (exp_rate_le_sqrt_pow n halpha0 halpha1) (by norm_num))

/-- **The blocker, machine-checked.**  For every `n ≥ 17`,

  `ofReal (2 e) < acceleratedSeedWarmFactor n (1 + 1/√n)`.

So the universal `2e` accepted-seed warm factor — which
`Ttc.CVSlowFullBodySourceSchedule.slowFullBodyWarmFactor_le_two_exp`
(`Ttc/Exec/CVSlowFullBodySourceSchedule.lean:104`) obtains by discharging the hypothesis
`r ≤ 1/n` of `acceleratedSeedWarmFactor_one_add_le_two_exp` with `le_rfl`, i.e. exactly at
the boundary — is **false** at the `1/√n` cooling rate.  Re-instantiating the slow chain at
`α = 1/√n` therefore requires a genuinely new warm-factor argument for the accepted-seed
transition, not a re-instantiation of the existing one.

`17` is where *this proof's* half-log slack (`log(1+α) ≥ α/2`, hence `√n/4 > 1`) first bites.
The exact threshold is smaller: `2·(1+1/√n)^{n/2}` exceeds `2e` already from `n = 6`
(`(1+1/√6)^3 ≈ 2.793 > e`, while `(1+1/√5)^{5/2} ≈ 2.520 < e`).  `n ≥ 17` is what is
recorded here; nothing downstream needs the sharp threshold. -/
theorem two_exp_lt_seedWarmFactor_inv_sqrt {n : Nat} (hn : 17 ≤ n) :
    ENNReal.ofReal (2 * Real.exp 1)
      < Ttc.CVGaussianAdaptiveAcceptedWarm.acceleratedSeedWarmFactor n
          (1 + 1 / Real.sqrt (n : Real)) := by
  have hnR : (17 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hn0 : (0 : Real) ≤ (n : Real) := by linarith
  have hsq : Real.sqrt (n : Real) * Real.sqrt (n : Real) = (n : Real) :=
    Real.mul_self_sqrt hn0
  have hsnn : (0 : Real) ≤ Real.sqrt (n : Real) := Real.sqrt_nonneg _
  have h4 : (4 : Real) < Real.sqrt (n : Real) := by nlinarith
  have hspos : (0 : Real) < Real.sqrt (n : Real) := by linarith
  have halpha0 : (0 : Real) ≤ 1 / Real.sqrt (n : Real) := by positivity
  have halpha1 : 1 / Real.sqrt (n : Real) ≤ 1 := by
    rw [div_le_one hspos]; linarith
  have hbase := exp_rate_le_sqrt_pow n halpha0 halpha1
  have hexp : (n : Real) * (1 / Real.sqrt (n : Real)) / 4 = Real.sqrt (n : Real) / 4 := by
    field_simp
    nlinarith
  rw [hexp] at hbase
  have h1 : (1 : Real) < Real.sqrt (n : Real) / 4 := by linarith
  have hlt : Real.exp 1 < Real.sqrt (1 + 1 / Real.sqrt (n : Real)) ^ n :=
    lt_of_lt_of_le (Real.exp_lt_exp.2 h1) hbase
  unfold Ttc.CVGaussianAdaptiveAcceptedWarm.acceleratedSeedWarmFactor
  rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)]
  linarith

/-! ## The second obstruction: the `C = 2` per-phase moment constant

`Ttc.CVSlowGaussianPhaseMoment.slowSource_phaseScore_interior_sq_moment_le_two`
(`Ttc/Exec/CVSlowGaussianPhaseMoment.lean:31`) proves `∫W² ≤ 2·(∫W)²` on the slow schedule,
and that `2` propagates through the whole factor-seven moment chain
(`Ttc/Exec/CVSlowCanonicalPhaseMomentPackage.lean:127`, `:205`, `:275`, `:327`, all of which
instantiate the exact-law family as the literal `fun _ ↦ 2`).

The second-moment ratio the variance route delivers is `exp(phaseVarBudget n α)`.  At
`α = 1/n` that is `exp(1/(n-1))`, which is `≤ 2` for `n ≥ 3` — hence the `2`.  At
`α = 1/√n` the budget is `(n+1)/(n-1) > 1` (`Ttc.CVFastRateSchedule.phaseVarBudget_inv_sqrt`),
so `exp(budget) > e > 2` for **every** `n`: the constant `2` is not available at the fast
rate, in any dimension.  `two_lt_exp_phaseVarBudget_inv_sqrt` records exactly that.

Not machine-checked here, but worth stating: the *factor-seven* shape does survive, since
`(n+1)/(n-1) < log 7 ≈ 1.9459` for `n ≥ 4` (`(4+1)/(4-1) = 5/3 ≈ 1.667`), so a re-proof at
`α = 1/√n` would carry `C = exp((n+1)/(n-1)) < 7` rather than `C = 2`.  That is a re-proof of
`slowSource_phaseScore_interior_sq_moment_le_two` and of the `fun _ ↦ 2` instantiations, not
a re-instantiation. -/

/-- **The moment constant `2` is unavailable at `α = 1/√n`, in every dimension.**

  `2 < exp(phaseVarBudget n (1/√n))`  for all `n ≥ 2`.

Since the per-phase second-moment ratio the variance route delivers is `exp(phaseVarBudget)`,
this says the `C = 2` of `Ttc.CVSlowGaussianPhaseMoment.slowSource_phaseScore_interior_sq_moment_le_two`
cannot be recovered at the fast rate.  Proof: `phaseVarBudget n (1/√n) = (n+1)/(n-1) > 1`
and `e > 2`. -/
theorem two_lt_exp_phaseVarBudget_inv_sqrt {n : Nat} (hn : 2 ≤ n) :
    2 < Real.exp (phaseVarBudget n (1 / Real.sqrt (n : Real))) := by
  have hn2 : (2 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hn1 : (0 : Real) < (n : Real) - 1 := by linarith
  have hbudget : (1 : Real) ≤ phaseVarBudget n (1 / Real.sqrt (n : Real)) := by
    rw [Ttc.CVFastRateSchedule.phaseVarBudget_inv_sqrt hn, le_div_iff₀ hn1]
    linarith
  have he : (2 : Real) < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  exact lt_of_lt_of_le he (Real.exp_le_exp.2 hbudget)

/-! ## Axiom audit (`CLAUDE.md` §4) -/

#print axioms rateSigmaSq_fixed_rate
#print axioms rateSigmaSq_eq_fastSourceSigmaSq
#print axioms rateSigmaSq_pos
#print axioms rateSigmaSq_succ
#print axioms rateSigmaSq_mono_start
#print axioms rateSigmaSq_mono_succ
#print axioms rateSigmaSq_le_terminal
#print axioms rateSigmaSq_inv_gap
#print axioms rateScoreExponent_fixed_rate
#print axioms rateScoreExponent_eq
#print axioms rateScoreExponent_mono_alpha
#print axioms ratePhaseCountBound_antitone_alpha
#print axioms exp_rate_le_sqrt_pow
#print axioms exp_rate_le_seedWarmFactor
#print axioms two_exp_lt_seedWarmFactor_inv_sqrt
#print axioms two_lt_exp_phaseVarBudget_inv_sqrt

end Ttc.CVRateGenericSchedule
