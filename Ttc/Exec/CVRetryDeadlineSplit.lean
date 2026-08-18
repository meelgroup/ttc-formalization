import Ttc.Exec.CVSlowUniformShareBounds

/-!
# Is the `rho^4` in the proved per-phase cost an artefact, or is it structural?

The proved slow-run overhead is
`Ttc.CVSlowEffectiveOverhead.slowUniformRetainedRealEnvelope`
(`k * m * 10 * retryEnv * deadlineEnv * 2e`), i.e. per phase a product

* `retryEnv  ~ 16 * log_2 (1 / floor)` (the finite-retry cap), and
* `deadlineEnv` whose payload is `log (2e / floor) + 2 * log (32 / floor)`
  (the speedy mixing deadline),

both keyed to the *same* tail floor.  With `log (1 / floor) ~ rho^2` this is `rho^4`,
while the paper's displayed source envelope carries `rho^2` once.

This file answers the question "must the retry count be keyed to the same share the
mixing deadline is keyed to?" **in the affirmative**, and does so by a machine-checked
*lower* bound rather than by inspecting the existing upper bounds.

The reason the two are locked together is a single additive total-variation budget.
`Ttc.FiniteContinuingRetryEmbeddedSelective.tvLe_map_output_embeddedMarginal_selective`
concludes `TVLe ... (acceptedError + (eta + r ^ L))`: the unresolved survival mass
`r ^ L` after `L` retries is *added* to the mixing error `acceptedError` in one TV bound.
That single bound is `Ttc.CVGaussianScoreAwareParameters.scoreAwareMixError`, and
`scoreAwareMixError_mul_boundSq_le_slack` then multiplies the whole sum by the
second-moment transport multiplier `boundSq` before comparing it to `slack`.  So *any*
retry count admissible for that obligation must already satisfy
`(15/16) ^ L <= slack / boundSq`.

`mixErrorWithRetries` below is `scoreAwareMixError` with the retry count freed from the
share, which is exactly the decoupling the audit was asked to test.  The theorems show
that freeing it changes nothing: the moment obligation alone forces
`L >= log (boundSq / slack) / log (16/15)`, and the deadline payload independently
carries `2 * log (boundSq / slack)`, so their product is bounded *below* by a constant
times `log (boundSq / slack) ^ 2`.  The `rho^4` is therefore structural to this
sampler's accounting, not an artefact of a loose upper bound.

## Where a `rho^2` could still be recovered (out of scope here)

Independently of the TV budget, the *cost* side charges each of the `L` retries the full
`M * T`: `Ttc.FiniteContinuingRetryExpectedCost.lintegral_accumulatedCost_embeddedMarginal`
is an exact identity `sum_j (integral of candidateMean over runningCurrent_j)`, and
`..._le` (same file, line 147) then applies unnormalised warmness round by round,
discarding the survival mass `s_j`.  Operationally `sum_j s_j <= 16 + L * eta = O(1)`, so
the true expected retry cost is `O(T)`, not `O(L * T)`.  That factor is **not** recoverable
from first-moment warmness alone: given only `mu <= M * pi` and `mu univ = s`, the
inequality `integral f dmu <= s * M * integral f dpi` is false — take
`mu = M * (pi restricted to T)` with `pi T = s / M` and `f = indicator T`, so the left
side is `s` and the right side is `s^2`.  Recovering it needs an `L^2(pi)` bound on the
walk's query count (Cauchy-Schwarz gives `sqrt (M * s_j) * ||f||_2`, and `sum_j sqrt s_j`
converges), i.e. a second-moment analysis of the lazy speedy walk's membership-query
count that does not exist in this repository.  That is new sampler analysis and is
deliberately not attempted here.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Ttc.CVRetryDeadlineSplit

open Ttc.CVContinuingRetryParameters
open Ttc.CVGaussianScoreAwareParameters
open Ttc.CVSlowUniformShareBounds
open scoped ENNReal

/-! ## The mixing error with a retry count decoupled from the share

This is `Ttc.CVGaussianScoreAwareParameters.scoreAwareMixError` with `zeta`, `eta` and
the retry count `L` supplied independently, so that nothing forces `L` to be keyed to
the share. -/

/-- Operational phase TV error: mixing (`32 * zeta`), the significance threshold
(`eta`), and the unresolved retry tail (`continuingContraction ^ L`), added in one
budget exactly as `tvLe_map_output_embeddedMarginal_selective` produces them. -/
noncomputable def mixErrorWithRetries (zeta eta : ENNReal) (L : Nat) : ENNReal :=
  32 * zeta + (eta + continuingContraction ^ L)

theorem mixErrorWithRetries_scoreAware
    (m k : Nat) (eps : Real) (slack boundSq : Nat → Real) (i : Nat) :
    mixErrorWithRetries (scoreAwareZeta m k eps slack boundSq i)
        (scoreAwareEta m k eps slack boundSq i)
        (scoreAwareRetries m k eps slack boundSq i) =
      scoreAwareMixError m k eps slack boundSq i := rfl

/-- The retry tail is a summand of the single TV budget: it cannot be relaxed
independently of the other two terms. -/
theorem contraction_pow_le_mixErrorWithRetries (zeta eta : ENNReal) (L : Nat) :
    continuingContraction ^ L ≤ mixErrorWithRetries zeta eta L := by
  unfold mixErrorWithRetries
  exact le_trans (self_le_add_left _ _) (self_le_add_left _ _)

theorem mixErrorWithRetries_ne_top {zeta eta : ENNReal}
    (hzeta : zeta ≠ ⊤) (heta : eta ≠ ⊤) (L : Nat) :
    mixErrorWithRetries zeta eta L ≠ ⊤ := by
  unfold mixErrorWithRetries continuingContraction
  finiteness

theorem toReal_continuingContraction_pow (L : Nat) :
    (continuingContraction ^ L).toReal = (15 / 16 : Real) ^ L := by
  rw [continuingContraction, ← ENNReal.ofReal_pow (by norm_num),
    ENNReal.toReal_ofReal (by positivity)]

/-! ## Necessity: the moment obligation alone pins the retry count -/

/-- Any retry count admissible for the second-moment transport obligation
`mixError * boundSq <= slack` already drives the unresolved mass below `slack / boundSq`.
This is the crux: it holds for an arbitrary `zeta`, `eta` and `L`, so decoupling the
retry target from the share does not help. -/
theorem contraction_pow_le_slack_div_boundSq
    {zeta eta : ENNReal} (hzeta : zeta ≠ ⊤) (heta : eta ≠ ⊤) {L : Nat}
    {slack boundSq : Real} (hbound : 0 < boundSq)
    (hbudget : (mixErrorWithRetries zeta eta L).toReal * boundSq ≤ slack) :
    (15 / 16 : Real) ^ L ≤ slack / boundSq := by
  have htop := mixErrorWithRetries_ne_top hzeta heta L
  have hpowtop : continuingContraction ^ L ≠ ⊤ := by
    unfold continuingContraction; finiteness
  have hle : (15 / 16 : Real) ^ L ≤ (mixErrorWithRetries zeta eta L).toReal := by
    rw [← toReal_continuingContraction_pow L]
    exact (ENNReal.toReal_le_toReal hpowtop htop).2
      (contraction_pow_le_mixErrorWithRetries zeta eta L)
  rw [le_div_iff₀ hbound]
  exact le_trans (mul_le_mul_of_nonneg_right hle hbound.le) hbudget

/-- Logarithmic form of a geometric tail bound.  Stated with `Real.log` so that it is
unconditionally true (the left side is nonpositive when `1 <= x`). -/
theorem log_inv_div_log_le_of_pow_le {x : Real} {L : Nat}
    (hx : (15 / 16 : Real) ^ L ≤ x) :
    Real.log (1 / x) / Real.log (16 / 15) ≤ (L : Real) := by
  have hpow0 : (0 : Real) < (15 / 16 : Real) ^ L := by positivity
  have hlog : Real.log ((15 / 16 : Real) ^ L) ≤ Real.log x :=
    Real.log_le_log hpow0 hx
  rw [Real.log_pow] at hlog
  have hrewrite : (15 / 16 : Real) = (16 / 15 : Real)⁻¹ := by norm_num
  rw [hrewrite, Real.log_inv] at hlog
  have hpos : 0 < Real.log (16 / 15 : Real) := Real.log_pos (by norm_num)
  rw [one_div, Real.log_inv, div_le_iff₀ hpos]
  linarith

/-- **The crux, as a lower bound.**  Every retry count that discharges the phase moment
obligation is at least `log (boundSq / slack) / log (16/15)`.  Since `boundSq` is the
`exp (R^2 / (2 sigma))^2` score-transport multiplier, this is `Omega(rho^2)` — and it
holds for *any* choice of `zeta`, `eta`, `L`, so the retry target cannot be crudened to
`1/2` or `1/m` while keeping this obligation. -/
theorem log_ratio_div_log_le_retries
    {zeta eta : ENNReal} (hzeta : zeta ≠ ⊤) (heta : eta ≠ ⊤) {L : Nat}
    {slack boundSq : Real} (hbound : 0 < boundSq)
    (hbudget : (mixErrorWithRetries zeta eta L).toReal * boundSq ≤ slack) :
    Real.log (boundSq / slack) / Real.log (16 / 15) ≤ (L : Real) := by
  have hx := contraction_pow_le_slack_div_boundSq hzeta heta hbound hbudget
  have h := log_inv_div_log_le_of_pow_le hx
  rwa [one_div_div] at h

/-- The same lower bound for the retry count actually selected by the score-aware
parameters, obtained from the repository's own moment discharge
`scoreAwareMixError_mul_boundSq_le_slack`. -/
theorem log_ratio_div_log_le_scoreAwareRetries
    {m k : Nat} {eps : Real} {slack boundSq : Nat → Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hslack : ∀ i, 0 < slack i) (hbound : ∀ i, 0 < boundSq i) (i : Nat) :
    Real.log (boundSq i / slack i) / Real.log (16 / 15) ≤
      (scoreAwareRetries m k eps slack boundSq i : Real) := by
  have hbudget := scoreAwareMixError_mul_boundSq_le_slack
    (m := m) (k := k) heps heps1 hslack hbound i
  rw [← mixErrorWithRetries_scoreAware m k eps slack boundSq i] at hbudget
  exact log_ratio_div_log_le_retries
    (zeta := scoreAwareZeta m k eps slack boundSq i)
    (eta := scoreAwareEta m k eps slack boundSq i)
    (by unfold scoreAwareZeta; exact ENNReal.ofReal_ne_top)
    (by unfold scoreAwareEta; exact ENNReal.ofReal_ne_top)
    (hbound i) hbudget

/-! ## The deadline payload carries the same logarithm

The payload of `Ttc.CVGaussianAdaptiveMixing.adjustableSpeedyDeadline` at share `share`
is `log (2e / share) + 2 * log (32 / share)`; the score-aware share obeys
`share <= slack / (3 * boundSq)`, so the payload is at least `2 * log (boundSq / slack)`.
This is independent of the retry analysis above. -/

/-- Lower bound for the exact deadline payload in terms of the same ratio that lower
bounds the retry count. -/
theorem log_ratio_le_deadlinePayload
    {slack boundSq share : Real} (hbound : 0 < boundSq) (hslack : 0 < slack)
    (hshare0 : 0 < share) (hshare1 : share ≤ 1)
    (hshare : share ≤ slack / (3 * boundSq)) :
    2 * Real.log (boundSq / slack) ≤
      Real.log ((2 * Real.exp 1) / share) + 2 * Real.log (32 / share) := by
  have hratio0 : 0 < boundSq / slack := div_pos hbound hslack
  have hfirst : 0 ≤ Real.log ((2 * Real.exp 1) / share) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hshare0]
    have he : (1 : Real) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    nlinarith
  have hshare' : share * (3 * boundSq) ≤ slack := by
    rw [le_div_iff₀ (by positivity : (0 : Real) < 3 * boundSq)] at hshare
    exact hshare
  have hsecond : boundSq / slack ≤ 32 / share := by
    rw [div_le_div_iff₀ hslack hshare0]
    nlinarith
  have hlog : Real.log (boundSq / slack) ≤ Real.log (32 / share) :=
    Real.log_le_log hratio0 hsecond
  linarith

/-! ## The verdict: the squared logarithm is structural

Multiplying the two independent lower bounds gives a *lower* bound on the per-phase
`retries * steps` product formed by
`Ttc.CVConcreteAugmentedRetryCutoffBudget.retryReferenceMeanEnvelope`.  No choice of
`zeta`, `eta`, `L` compatible with the phase moment obligation can avoid it. -/

/-- **Structural `rho^4`.**  For any retry count `L` discharging the moment obligation
and any share the deadline is keyed to, the product of the retry count and the exact
deadline payload is at least `2 * log (boundSq / slack) ^ 2 / log (16/15)`.  With
`boundSq = 15 * exp (R^2 / (2 sigma))^2` this is `Omega(rho^4)`: the double count is
*not* an artefact of loose upper bounds. -/
theorem log_ratio_sq_le_retries_mul_payload
    {zeta eta : ENNReal} (hzeta : zeta ≠ ⊤) (heta : eta ≠ ⊤) {L : Nat}
    {slack boundSq share : Real} (hbound : 0 < boundSq) (hslack : 0 < slack)
    (hle : slack ≤ boundSq) (hshare0 : 0 < share) (hshare1 : share ≤ 1)
    (hshare : share ≤ slack / (3 * boundSq))
    (hbudget : (mixErrorWithRetries zeta eta L).toReal * boundSq ≤ slack) :
    2 * Real.log (boundSq / slack) ^ 2 / Real.log (16 / 15) ≤
      (L : Real) *
        (Real.log ((2 * Real.exp 1) / share) + 2 * Real.log (32 / share)) := by
  have hc : 0 < Real.log (16 / 15 : Real) := Real.log_pos (by norm_num)
  have hD0 : 0 ≤ Real.log (boundSq / slack) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hslack]
    linarith
  have hL := log_ratio_div_log_le_retries hzeta heta hbound hbudget
  have hP := log_ratio_le_deadlinePayload hbound hslack hshare0 hshare1 hshare
  calc
    2 * Real.log (boundSq / slack) ^ 2 / Real.log (16 / 15) =
        (Real.log (boundSq / slack) / Real.log (16 / 15)) *
          (2 * Real.log (boundSq / slack)) := by
          field_simp
    _ ≤ (L : Real) *
        (Real.log ((2 * Real.exp 1) / share) + 2 * Real.log (32 / share)) := by
          exact mul_le_mul hL hP (by linarith) (by positivity)

/-- The structural lower bound at the repository's own score-aware parameters.  The
right-hand factor is literally the payload bounded by
`Ttc.CVSlowUniformShareBounds.slowDeadlinePayload_le_uniform` and consumed by
`slowScoreAwareSteps_uniform_active_le`, and the left factor is literally
`Ttc.CVGaussianScoreAwareParameters.scoreAwareRetries`. -/
theorem log_ratio_sq_le_scoreAwareRetries_mul_payload
    {m k : Nat} {eps : Real} {slack boundSq : Nat → Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hslack : ∀ i, 0 < slack i) (hbound : ∀ i, 0 < boundSq i)
    (i : Nat) (hle : slack i ≤ boundSq i) :
    2 * Real.log (boundSq i / slack i) ^ 2 / Real.log (16 / 15) ≤
      (scoreAwareRetries m k eps slack boundSq i : Real) *
        (Real.log ((2 * Real.exp 1) / scoreAwareShare m k eps slack boundSq i) +
          2 * Real.log (32 / scoreAwareShare m k eps slack boundSq i)) := by
  have hbudget := scoreAwareMixError_mul_boundSq_le_slack
    (m := m) (k := k) heps heps1 hslack hbound i
  rw [← mixErrorWithRetries_scoreAware m k eps slack boundSq i] at hbudget
  exact log_ratio_sq_le_retries_mul_payload
    (zeta := scoreAwareZeta m k eps slack boundSq i)
    (eta := scoreAwareEta m k eps slack boundSq i)
    (by unfold scoreAwareZeta; exact ENNReal.ofReal_ne_top)
    (by unfold scoreAwareEta; exact ENNReal.ofReal_ne_top)
    (hbound i) (hslack i) hle
    (scoreAwareShare_pos heps hslack hbound i)
    (scoreAwareShare_lt_one heps heps1 i).le
    (min_le_right _ _) hbudget

#print axioms mixErrorWithRetries_scoreAware
#print axioms contraction_pow_le_mixErrorWithRetries
#print axioms toReal_continuingContraction_pow
#print axioms contraction_pow_le_slack_div_boundSq
#print axioms log_inv_div_log_le_of_pow_le
#print axioms log_ratio_div_log_le_retries
#print axioms log_ratio_div_log_le_scoreAwareRetries
#print axioms log_ratio_le_deadlinePayload
#print axioms log_ratio_sq_le_retries_mul_payload
#print axioms log_ratio_sq_le_scoreAwareRetries_mul_payload

end Ttc.CVRetryDeadlineSplit
