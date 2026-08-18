import Ttc.Exec.CVSlowActualSteps
import Ttc.Exec.CVRefreshWarmRoute

/-!
# The frontier's `hsteps` binder, at the refresh-routed warm envelope

This file is the refresh-based analogue of `Ttc.Exec.CVSlowActualSteps`.  Everything is
mirrored from that file with a single change: the warm payload
`Ttc.CVSlowActualSteps.slowActualWlog = log (2e) + m·log (A + F)` is replaced by the
refresh-routed payload at the uniform index `m`,

```
slowRefreshUniformWlog n m k q epsP R
  = Ttc.CVRefreshWarmRoute.slowRefreshWlog n q (slowSourceInitialVariance n) m
      (slowActualRetriesCap n m k epsP R) m
  = m·log A + log (m+1) + log (2e) + (1/(32 s0) + n·log (4 max 1 R))
```

where `A := (slowAcceptedCap L).toReal` is the retry-capped accepted ratio and
`F := (slowFallbackEnvelope …).toReal` the independent-refresh normalizer, whose logarithm
is exactly `1/(32 s0) + n·log (4 max 1 R)`
(`Ttc.CVRefreshWarmRoute.log_slowFallbackEnvelope_toReal`).  The two share payloads
`Ttc.CVSlowActualSteps.slowActualElog` / `…slowActualZlog` are reused unchanged.

## Does the refresh envelope dominate?

**Not unconditionally.**  At the uniform index `m` the comparison is *equivalent* to

```
(m+1) · A^m · F ≤ (A + F)^m
```

which fails at `m = 0` (it demands `F ≤ 1`) and at `m = 1` (it demands `2·A·F ≤ A + F`,
false for all `A, F ≥ 1` except `A = F = 1`).  This is the same phenomenon
`Ttc.CVRefreshWarmRoute.log_slowWarmBudget_toReal_le_min` records: the refresh route pays
`log F` up front, so it loses in the first phases and wins thereafter.  It wins by a margin
growing with `m` once `F` dominates `A`, which is the operative regime (`F` is exponential
in `n`, `A` linear in the retry cap `L`).

Consequently the **unconditional** deliverable is the pointwise minimum
`slowMinStepsEnvelope`, and the conditional dominance is recorded separately.

## Main results

* `slowRefreshStepsBound` / `slowRefreshStepsEnvelope` — the per-phase deadline value and
  its uniform real envelope, at the refresh-routed payload.
* `slowCanonicalSteps_refresh_le` — the frontier's `hsteps` at
  `T := ⌈slowRefreshStepsEnvelope …⌉₊ + 1`.
* `slowRefreshWlog_le_slowActualWlog_of_large_phase` — the machine-checked comparison,
  under the exact hypothesis above (plus the convenient sufficient form
  `…_of_refresh_dominant` and the envelope-level `slowRefreshStepsEnvelope_le_actual_…`).
* `slowMinStepsEnvelope` / `slowCanonicalSteps_min_le` — **what the capstone should use**:
  the `hsteps` binder at `min` of the two envelopes, unconditionally at least as good as
  the status quo.
* `cast_slowRefreshStepsCap_le` / `cast_slowMinStepsCap_le` — the `Tenv` the cost side
  consumes.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Ttc.CVSlowRefreshSteps

open MeasureTheory Metric Set
open Ttc.CVSpeedyDeadlineMono
open Ttc.CVAdaptiveRadiusQPrimitives
open Ttc.CVSlowFullBodySourceSchedule
open Ttc.CVSlowSourceReferenceCertificate
open Ttc.CVSlowRadiusQCanonicalOperational
open Ttc.CVSlowWarmBudgetBound
open Ttc.CVSlowActualDeadline
open Ttc.CVSlowCanonicalShareBounds
open Ttc.CVSlowCanonicalDeadlineCost
open Ttc.CVSlowCanonicalUniformParameters
open Ttc.CVSlowUniformShareBounds
open Ttc.CVGaussianScoreAwareParameters
open Ttc.CVRefreshWarmRoute
open Ttc.CVSlowActualSteps
open scoped ENNReal

variable {n : Nat}

local notation "State" => fun m => EuclideanSpace Real (Fin m)

/-! ## The bridge between the two uniform per-phase factors -/

/-- The product envelope's per-phase factor is literally the refresh route's accepted cap
plus the refresh normalizer. -/
theorem slowWarmFactorEnvelope_eq (n : Nat) (q s0 : Real) (m L : Nat) :
    slowWarmFactorEnvelope n q s0 m L =
      slowAcceptedCap L + slowFallbackEnvelope n q s0 m := rfl

theorem slowWarmFactorEnvelope_toReal (n : Nat) (q s0 : Real) (m L : Nat) :
    (slowWarmFactorEnvelope n q s0 m L).toReal =
      (slowAcceptedCap L).toReal + (slowFallbackEnvelope n q s0 m).toReal := by
  rw [slowWarmFactorEnvelope_eq,
    ENNReal.toReal_add (slowAcceptedCap_ne_top L) (slowFallbackEnvelope_ne_top n q s0 m)]

/-! ## The refresh-routed payload of the actual slow canonical schedule -/

/-- The refresh-routed warm payload of the canonical slow schedule, at the uniform
(phase-index-free) index `m`.  This is the drop-in replacement for
`Ttc.CVSlowActualSteps.slowActualWlog`: the accepted cap compounds, but the radial refresh
normalizer `1/(32 s0) + n log (4 max 1 R)` is paid **once**. -/
noncomputable def slowRefreshUniformWlog (n m k : Nat) (q epsP R : Real) : Real :=
  slowRefreshWlog n q (slowSourceInitialVariance n) m
    (slowActualRetriesCap n m k epsP R) m

theorem slowRefreshUniformWlog_nonneg
    (hn : 1 ≤ n) (m k : Nat) (q epsP R : Real) :
    0 ≤ slowRefreshUniformWlog n m k q epsP R := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have h1 : 0 ≤ (m : Real) *
      Real.log (slowAcceptedCap (slowActualRetriesCap n m k epsP R)).toReal :=
    mul_nonneg (Nat.cast_nonneg m)
      (Real.log_nonneg (one_le_slowAcceptedCap_toReal _))
  have h2 : 0 ≤ Real.log ((m : Real) + 1) := by
    refine Real.log_nonneg ?_
    have : (0 : Real) ≤ (m : Real) := Nat.cast_nonneg m
    linarith
  have h3 : 0 ≤ Real.log (2 * Real.exp 1) := by
    refine Real.log_nonneg ?_
    have he : (1 : Real) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    linarith
  have h4 : 0 ≤ 1 / (32 * slowSourceInitialVariance n) := by positivity
  have h5 : 0 ≤ (n : Real) *
      Real.log (4 * max 1 (slowRefreshRadius n q (slowSourceInitialVariance n) m)) := by
    refine mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg ?_)
    have : (1 : Real) ≤ max 1 (slowRefreshRadius n q (slowSourceInitialVariance n) m) :=
      le_max_left _ _
    linarith
  unfold slowRefreshUniformWlog slowRefreshWlog
  linarith

/-- **Deliverable 1.**  The per-phase deadline value the actual slow canonical schedule
selects, at the refresh-routed warm payload and the two unchanged share payloads
`slowActualElog` / `slowActualZlog`. -/
noncomputable def slowRefreshStepsBound
    (n m k : Nat) (q epsP R : Real) (i : Nat) : Real :=
  slowActualDeadlineExpression n
    (radiusQDelta n q (slowSourceSigmaSq n (slowSourceInitialVariance n) i))
    (slowSourceSigmaSq n (slowSourceInitialVariance n) i)
    (slowRefreshUniformWlog n m k q epsP R) (slowActualElog n m k epsP R)
    (slowActualZlog n m k epsP R)

/-- **Deliverable 2.**  One real envelope valid at every phase: the variance is taken at
the terminal phase `m` (largest) and the mixing radius at the initial variance (smallest,
and the expression divides by its square). -/
noncomputable def slowRefreshStepsEnvelope
    (n m k : Nat) (q epsP R : Real) : Real :=
  slowActualDeadlineExpression n
    (radiusQDelta n q (slowSourceInitialVariance n))
    (slowSourceSigmaSq n (slowSourceInitialVariance n) m)
    (slowRefreshUniformWlog n m k q epsP R) (slowActualElog n m k epsP R)
    (slowActualZlog n m k epsP R)

/-- The full logarithmic payload of the refresh-routed deadline expression is
nonnegative. -/
theorem slowRefreshPayload_nonneg
    (hn : 1 ≤ n) {m k : Nat} {q epsP R : Real} (hepsP : 0 < epsP) :
    0 ≤ (Real.log 2 + slowRefreshUniformWlog n m k q epsP R +
        slowActualElog n m k epsP R) + 2 * slowActualZlog n m k epsP R := by
  have h0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h1 := slowRefreshUniformWlog_nonneg hn m k q epsP R
  have h2 := slowActualElog_nonneg (n := n) hn (m := m) (k := k) (R := R) hepsP
  have h3 := slowActualZlog_nonneg (n := n) hn (m := m) (k := k) (R := R) hepsP
  linarith

/-- **Deliverable 2.**  The per-phase deadline value is below the uniform envelope at
every phase of the schedule. -/
theorem slowRefreshStepsBound_le_envelope
    (hn : 1 ≤ n) {m k : Nat} {q epsP R : Real} (hq : 0 < q) (hepsP : 0 < epsP)
    {i : Nat} (hi : i ≤ m) :
    slowRefreshStepsBound n m k q epsP R i ≤ slowRefreshStepsEnvelope n m k q epsP R := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have hsigle : slowSourceSigmaSq n (slowSourceInitialVariance n) i ≤
      slowSourceSigmaSq n (slowSourceInitialVariance n) m :=
    slowSourceSigmaSq_le_terminal hn hs0 hi
  have hd0 : 0 < radiusQDelta n q (slowSourceInitialVariance n) :=
    radiusQDelta_pos hn hq hs0
  have hdle : radiusQDelta n q (slowSourceInitialVariance n) ≤
      radiusQDelta n q (slowSourceSigmaSq n (slowSourceInitialVariance n) i) :=
    radiusQDelta_mono_variance n q (slowSourceSigmaSq_mono_start hn hs0 i)
  have hP := slowRefreshPayload_nonneg (n := n) hn (m := m) (k := k) (q := q) (R := R) hepsP
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsigi : 0 ≤ slowSourceSigmaSq n (slowSourceInitialVariance n) i :=
    (slowSourceSigmaSq_pos hn hs0 i).le
  unfold slowRefreshStepsBound slowRefreshStepsEnvelope slowActualDeadlineExpression
  gcongr
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hsigi.trans hsigle))
    (Nat.cast_nonneg n)) hP

/-- Padding the refresh payload from the running phase `i` to the uniform index `m`. -/
theorem slowRefreshDeadlineExpression_le_bound
    (hn : 1 ≤ n) {m k : Nat} {q epsP R : Real} {i : Nat} (hi : i ≤ m) :
    slowActualDeadlineExpression n
        (radiusQDelta n q (slowSourceSigmaSq n (slowSourceInitialVariance n) i))
        (slowSourceSigmaSq n (slowSourceInitialVariance n) i)
        (slowRefreshWlog n q (slowSourceInitialVariance n) m
          (slowActualRetriesCap n m k epsP R) i)
        (slowActualElog n m k epsP R) (slowActualZlog n m k epsP R) ≤
      slowRefreshStepsBound n m k q epsP R i := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have hsigi : 0 ≤ slowSourceSigmaSq n (slowSourceInitialVariance n) i :=
    (slowSourceSigmaSq_pos hn hs0 i).le
  have hW := slowRefreshWlog_mono n q (slowSourceInitialVariance n) m
    (slowActualRetriesCap n m k epsP R) hi
  unfold slowRefreshStepsBound slowRefreshUniformWlog slowActualDeadlineExpression
  have hcoef : (0 : Real) ≤ 4 * 640 ^ 2 *
      slowSourceSigmaSq n (slowSourceInitialVariance n) i * (n : Real) := by positivity
  gcongr

/-- **Deliverable 3.**  Every active phase of the *actual* slow canonical schedule obeys
one explicit natural deadline cap built from the **refresh-routed** warm envelope, namely
`⌈slowRefreshStepsEnvelope …⌉₊ + 1`. -/
theorem slowCanonicalSteps_refresh_le
    (hn : 1 ≤ n) (m k : Nat) {q epsP R : Real} (hq : 0 < q) (hepsP : 0 < epsP)
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    (hball : Metric.ball (0 : EuclideanSpace Real (Fin n)) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i < m) :
    slowCanonicalSteps slowReferenceWarm n q (slowSourceInitialVariance n) K
        (scoreAwareRetries (m + 1) k (epsP / 2)
          (slowUniformSlack n m K) (slowUniformBoundSq n R))
        (scoreAwareEta (m + 1) k (epsP / 2)
          (slowUniformSlack n m K) (slowUniformBoundSq n R))
        (scoreAwareZeta (m + 1) k (epsP / 2)
          (slowUniformSlack n m K) (slowUniformBoundSq n R))
        i 0 ≤
      ⌈slowRefreshStepsEnvelope n m k q epsP R⌉₊ + 1 := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have heps2 : (0 : Real) < epsP / 2 := by linarith
  have hshare0 : 0 < scoreAwareShare (m + 1) k (epsP / 2)
      (slowUniformSlack n m K) (slowUniformBoundSq n R) i :=
    scoreAwareShare_pos heps2 (slowUniformSlack_pos hn hball hfin)
      (fun j ↦ slowUniformBoundSq_pos j) i
  have hfloor0 : 0 < slowUniformShareFloor (m + 1) k (epsP / 2) R
      (slowSourceInitialVariance n) := slowUniformShareFloor_pos heps2
  have hfloor : slowUniformShareFloor (m + 1) k (epsP / 2) R
        (slowSourceInitialVariance n) ≤
      scoreAwareShare (m + 1) k (epsP / 2)
        (slowUniformSlack n m K) (slowUniformBoundSq n R) i :=
    slowUniformShareFloor_le_scoreAwareShare hn hK hball hfin i
  have hL : ∀ j, scoreAwareRetries (m + 1) k (epsP / 2)
      (slowUniformSlack n m K) (slowUniformBoundSq n R) j ≤
      slowActualRetriesCap n m k epsP R :=
    fun j ↦ scoreAwareRetries_slowUniform_le hn heps2 hK hball hfin j
  have heta : (scoreAwareEta (m + 1) k (epsP / 2)
      (slowUniformSlack n m K) (slowUniformBoundSq n R) i).toReal =
      scoreAwareShare (m + 1) k (epsP / 2)
        (slowUniformSlack n m K) (slowUniformBoundSq n R) i := by
    rw [scoreAwareEta, ENNReal.toReal_ofReal hshare0.le]
  have hzeta : (scoreAwareZeta (m + 1) k (epsP / 2)
      (slowUniformSlack n m K) (slowUniformBoundSq n R) i).toReal =
      scoreAwareShare (m + 1) k (epsP / 2)
        (slowUniformSlack n m K) (slowUniformBoundSq n R) i / 32 := by
    rw [scoreAwareZeta, ENNReal.toReal_ofReal (by positivity)]
  have heta0 : scoreAwareEta (m + 1) k (epsP / 2)
      (slowUniformSlack n m K) (slowUniformBoundSq n R) i ≠ 0 := by
    rw [scoreAwareEta, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hshare0
  have hetaTop : scoreAwareEta (m + 1) k (epsP / 2)
      (slowUniformSlack n m K) (slowUniformBoundSq n R) i ≠ ⊤ := by
    rw [scoreAwareEta]; exact ENNReal.ofReal_ne_top
  have hElog : Real.log (1 / (scoreAwareEta (m + 1) k (epsP / 2)
      (slowUniformSlack n m K) (slowUniformBoundSq n R) i).toReal) ≤
      slowActualElog n m k epsP R := by
    rw [heta]
    unfold slowActualElog
    exact Real.log_le_log (by positivity) (one_div_le_one_div_of_le hfloor0 hfloor)
  have hZlog : Real.log (1 / (scoreAwareZeta (m + 1) k (epsP / 2)
      (slowUniformSlack n m K) (slowUniformBoundSq n R) i).toReal) ≤
      slowActualZlog n m k epsP R := by
    rw [hzeta, show 1 / (scoreAwareShare (m + 1) k (epsP / 2)
        (slowUniformSlack n m K) (slowUniformBoundSq n R) i / 32) =
        32 / scoreAwareShare (m + 1) k (epsP / 2)
          (slowUniformSlack n m K) (slowUniformBoundSq n R) i by field_simp]
    unfold slowActualZlog
    exact Real.log_le_log (by positivity)
      (div_le_div_of_nonneg_left (by norm_num) hfloor0 hfloor)
  refine slowCanonicalSteps_le_ceil_of_refresh_log hn hq hs0 hK hL hi.le heta0 hetaTop
    hElog hZlog ?_
  exact (slowRefreshDeadlineExpression_le_bound hn hi.le).trans
    (slowRefreshStepsBound_le_envelope hn hq hepsP hi.le)

/-! ## The cost side's real envelope -/

theorem slowRefreshStepsEnvelope_nonneg
    (hn : 1 ≤ n) {m k : Nat} {q epsP R : Real} (hepsP : 0 < epsP) :
    0 ≤ slowRefreshStepsEnvelope n m k q epsP R := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have hsigm : 0 ≤ slowSourceSigmaSq n (slowSourceInitialVariance n) m :=
    (slowSourceSigmaSq_pos hn hs0 m).le
  have hP := slowRefreshPayload_nonneg (n := n) hn (m := m) (k := k) (q := q) (R := R) hepsP
  unfold slowRefreshStepsEnvelope slowActualDeadlineExpression
  have hnum : 0 ≤ 4 * 640 ^ 2 * slowSourceSigmaSq n (slowSourceInitialVariance n) m *
      (n : Real) *
      ((Real.log 2 + slowRefreshUniformWlog n m k q epsP R +
          slowActualElog n m k epsP R) + 2 * slowActualZlog n m k epsP R) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hsigm) (Nat.cast_nonneg n)) hP
  have hden : 0 ≤ (radiusQDelta n q (slowSourceInitialVariance n) * Real.log 2) ^ 2 :=
    sq_nonneg _
  have := div_nonneg hnum hden
  linarith

/-- **Deliverable 4.**  The natural cap of `slowCanonicalSteps_refresh_le` is bounded, as a
real, by the envelope plus `2`; this is the `Tenv` the cost assembly consumes. -/
theorem cast_slowRefreshStepsCap_le
    (n m k : Nat) (q epsP R : Real)
    (hE : 0 ≤ slowRefreshStepsEnvelope n m k q epsP R) :
    ((⌈slowRefreshStepsEnvelope n m k q epsP R⌉₊ + 1 : Nat) : Real) ≤
      slowRefreshStepsEnvelope n m k q epsP R + 2 :=
  cast_ceil_add_one_le _ hE

/-! ## Comparing the two warm envelopes at the uniform index `m`

Write `A := (slowAcceptedCap L).toReal ≥ 1` for the retry-capped accepted ratio and
`F := (slowFallbackEnvelope …).toReal ≥ 1` for the independent-refresh normalizer.  At the
uniform index `m`,

* `slowRefreshUniformWlog = m·log A + log (m+1) + log (2e) + log F`,
* `slowActualWlog        = log (2e) + m·log (A + F)`,

so the refresh route dominates **exactly when** `(m+1)·A^m·F ≤ (A+F)^m`.

That condition is *not* a theorem.  At `m = 0` it demands `F ≤ 1`; at `m = 1` it demands
`2·A·F ≤ A + F`, which fails for every `A, F ≥ 1` except `A = F = 1` (and `A ≥ 32e`
whenever `L ≥ 1`).  So the refresh envelope is genuinely **worse** in the first phases —
it has already paid `log F` while the product envelope has not.  It becomes better as soon
as `F` is large relative to `A^{m/(m-1)}`, which is the operative regime here: `F` is
exponential in the dimension `n` (it contains `(4R)^n`) while `A` is linear in the retry
cap `L`.  The hypothesis below is stated in the exact form, so no strength is lost. -/
theorem slowRefreshWlog_le_slowActualWlog_of_large_phase
    (hn : 1 ≤ n) (m k : Nat) (q epsP R : Real)
    (hdom : ((m : Real) + 1) *
          (slowAcceptedCap (slowActualRetriesCap n m k epsP R)).toReal ^ m *
          (slowFallbackEnvelope n q (slowSourceInitialVariance n) m).toReal ≤
        ((slowAcceptedCap (slowActualRetriesCap n m k epsP R)).toReal +
          (slowFallbackEnvelope n q (slowSourceInitialVariance n) m).toReal) ^ m) :
    slowRefreshUniformWlog n m k q epsP R ≤
      Ttc.CVSlowActualSteps.slowActualWlog n m k q epsP R := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have hA1 : (1 : Real) ≤
      (slowAcceptedCap (slowActualRetriesCap n m k epsP R)).toReal :=
    one_le_slowAcceptedCap_toReal _
  have hF1 : (1 : Real) ≤
      (slowFallbackEnvelope n q (slowSourceInitialVariance n) m).toReal :=
    one_le_slowFallbackEnvelope_toReal n q hs0 m
  have hA0 : (0 : Real) <
      (slowAcceptedCap (slowActualRetriesCap n m k epsP R)).toReal :=
    lt_of_lt_of_le one_pos hA1
  have hF0 : (0 : Real) <
      (slowFallbackEnvelope n q (slowSourceInitialVariance n) m).toReal :=
    lt_of_lt_of_le one_pos hF1
  have hm1 : (0 : Real) < (m : Real) + 1 := by
    have : (0 : Real) ≤ (m : Real) := Nat.cast_nonneg m
    linarith
  have hApow : (0 : Real) <
      (slowAcceptedCap (slowActualRetriesCap n m k epsP R)).toReal ^ m :=
    pow_pos hA0 m
  have hpos : (0 : Real) < ((m : Real) + 1) *
      (slowAcceptedCap (slowActualRetriesCap n m k epsP R)).toReal ^ m *
      (slowFallbackEnvelope n q (slowSourceInitialVariance n) m).toReal := by positivity
  have hkey := Real.log_le_log hpos hdom
  rw [Real.log_mul (by positivity) hF0.ne', Real.log_mul hm1.ne' hApow.ne',
    Real.log_pow, Real.log_pow] at hkey
  unfold slowRefreshUniformWlog slowRefreshWlog Ttc.CVSlowActualSteps.slowActualWlog
  rw [slowWarmFactorEnvelope_toReal, ← log_slowFallbackEnvelope_toReal n q hs0 m]
  linarith

/-- A convenient sufficient condition for the dominance hypothesis, dropping the accepted
ratio from the right-hand side: the refresh route wins as soon as `(m+1)·A^m·F ≤ F^m`,
i.e. as soon as the refresh normalizer's `(m-1)`-st power beats `(m+1)·A^m`.  With
`F = e^{1/(32 s0)} (4 max 1 R)^n` exponential in the dimension and `A = 32 e L` linear in
the retry cap, this holds for every `m ≥ 2` once `n` is large. -/
theorem slowRefreshWlog_le_slowActualWlog_of_refresh_dominant
    (hn : 1 ≤ n) (m k : Nat) (q epsP R : Real)
    (hdom : ((m : Real) + 1) *
          (slowAcceptedCap (slowActualRetriesCap n m k epsP R)).toReal ^ m *
          (slowFallbackEnvelope n q (slowSourceInitialVariance n) m).toReal ≤
        (slowFallbackEnvelope n q (slowSourceInitialVariance n) m).toReal ^ m) :
    slowRefreshUniformWlog n m k q epsP R ≤
      Ttc.CVSlowActualSteps.slowActualWlog n m k q epsP R := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have hA1 : (1 : Real) ≤
      (slowAcceptedCap (slowActualRetriesCap n m k epsP R)).toReal :=
    one_le_slowAcceptedCap_toReal _
  have hF1 : (1 : Real) ≤
      (slowFallbackEnvelope n q (slowSourceInitialVariance n) m).toReal :=
    one_le_slowFallbackEnvelope_toReal n q hs0 m
  refine slowRefreshWlog_le_slowActualWlog_of_large_phase hn m k q epsP R (hdom.trans ?_)
  exact pow_le_pow_left₀ (by linarith) (by linarith) m

/-- The comparison transported to the deadline envelopes themselves. -/
theorem slowRefreshStepsEnvelope_le_actual_of_large_phase
    (hn : 1 ≤ n) (m k : Nat) {q epsP R : Real}
    (hdom : ((m : Real) + 1) *
          (slowAcceptedCap (slowActualRetriesCap n m k epsP R)).toReal ^ m *
          (slowFallbackEnvelope n q (slowSourceInitialVariance n) m).toReal ≤
        ((slowAcceptedCap (slowActualRetriesCap n m k epsP R)).toReal +
          (slowFallbackEnvelope n q (slowSourceInitialVariance n) m).toReal) ^ m) :
    slowRefreshStepsEnvelope n m k q epsP R ≤
      Ttc.CVSlowActualSteps.slowActualStepsEnvelope n m k q epsP R := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have hsigm : 0 ≤ slowSourceSigmaSq n (slowSourceInitialVariance n) m :=
    (slowSourceSigmaSq_pos hn hs0 m).le
  have hW := slowRefreshWlog_le_slowActualWlog_of_large_phase hn m k q epsP R hdom
  unfold slowRefreshStepsEnvelope Ttc.CVSlowActualSteps.slowActualStepsEnvelope
    slowActualDeadlineExpression
  have hcoef : (0 : Real) ≤ 4 * 640 ^ 2 *
      slowSourceSigmaSq n (slowSourceInitialVariance n) m * (n : Real) := by positivity
  gcongr

/-! ## The unconditional deliverable: the pointwise minimum of the two envelopes -/

/-- **The envelope the capstone should consume.**  Both routes are available at every
phase, so the deadline may take whichever is smaller.  This is unconditionally at least as
good as `Ttc.CVSlowActualSteps.slowActualStepsEnvelope`, and equals the refresh envelope in
the operative regime (`F` exponential in `n`). -/
noncomputable def slowMinStepsEnvelope (n m k : Nat) (q epsP R : Real) : Real :=
  min (Ttc.CVSlowActualSteps.slowActualStepsEnvelope n m k q epsP R)
    (slowRefreshStepsEnvelope n m k q epsP R)

theorem slowMinStepsEnvelope_le_actual (n m k : Nat) (q epsP R : Real) :
    slowMinStepsEnvelope n m k q epsP R ≤
      Ttc.CVSlowActualSteps.slowActualStepsEnvelope n m k q epsP R :=
  min_le_left _ _

theorem slowMinStepsEnvelope_le_refresh (n m k : Nat) (q epsP R : Real) :
    slowMinStepsEnvelope n m k q epsP R ≤ slowRefreshStepsEnvelope n m k q epsP R :=
  min_le_right _ _

/-- **Deliverable 5.**  The frontier's `hsteps` at the pointwise-better of the two
envelopes.  The conclusion is byte-identical to
`Ttc.CVSlowActualSteps.slowCanonicalSteps_actual_le`'s except for the envelope. -/
theorem slowCanonicalSteps_min_le
    (hn : 1 ≤ n) (m k : Nat) {q epsP R : Real} (hq : 0 < q) (hepsP : 0 < epsP)
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    (hball : Metric.ball (0 : EuclideanSpace Real (Fin n)) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i < m) :
    slowCanonicalSteps slowReferenceWarm n q (slowSourceInitialVariance n) K
        (scoreAwareRetries (m + 1) k (epsP / 2)
          (slowUniformSlack n m K) (slowUniformBoundSq n R))
        (scoreAwareEta (m + 1) k (epsP / 2)
          (slowUniformSlack n m K) (slowUniformBoundSq n R))
        (scoreAwareZeta (m + 1) k (epsP / 2)
          (slowUniformSlack n m K) (slowUniformBoundSq n R))
        i 0 ≤
      ⌈slowMinStepsEnvelope n m k q epsP R⌉₊ + 1 := by
  unfold slowMinStepsEnvelope
  rcases le_total (Ttc.CVSlowActualSteps.slowActualStepsEnvelope n m k q epsP R)
    (slowRefreshStepsEnvelope n m k q epsP R) with h | h
  · rw [min_eq_left h]
    exact slowCanonicalSteps_actual_le hn m k hq hepsP hK hball hfin hi
  · rw [min_eq_right h]
    exact slowCanonicalSteps_refresh_le hn m k hq hepsP hK hball hfin hi

theorem slowMinStepsEnvelope_nonneg
    (hn : 1 ≤ n) {m k : Nat} {q epsP R : Real} (hepsP : 0 < epsP) :
    0 ≤ slowMinStepsEnvelope n m k q epsP R :=
  le_min (slowActualStepsEnvelope_nonneg hn hepsP) (slowRefreshStepsEnvelope_nonneg hn hepsP)

/-- The `Tenv` the cost assembly consumes for the `min` route. -/
theorem cast_slowMinStepsCap_le
    (n m k : Nat) (q epsP R : Real)
    (hE : 0 ≤ slowMinStepsEnvelope n m k q epsP R) :
    ((⌈slowMinStepsEnvelope n m k q epsP R⌉₊ + 1 : Nat) : Real) ≤
      slowMinStepsEnvelope n m k q epsP R + 2 :=
  cast_ceil_add_one_le _ hE

#print axioms slowWarmFactorEnvelope_eq
#print axioms slowWarmFactorEnvelope_toReal
#print axioms slowRefreshUniformWlog_nonneg
#print axioms slowRefreshPayload_nonneg
#print axioms slowRefreshStepsBound_le_envelope
#print axioms slowRefreshDeadlineExpression_le_bound
#print axioms slowCanonicalSteps_refresh_le
#print axioms slowRefreshStepsEnvelope_nonneg
#print axioms cast_slowRefreshStepsCap_le
#print axioms slowRefreshWlog_le_slowActualWlog_of_large_phase
#print axioms slowRefreshWlog_le_slowActualWlog_of_refresh_dominant
#print axioms slowRefreshStepsEnvelope_le_actual_of_large_phase
#print axioms slowMinStepsEnvelope_le_actual
#print axioms slowMinStepsEnvelope_le_refresh
#print axioms slowCanonicalSteps_min_le
#print axioms slowMinStepsEnvelope_nonneg
#print axioms cast_slowMinStepsCap_le

end Ttc.CVSlowRefreshSteps
