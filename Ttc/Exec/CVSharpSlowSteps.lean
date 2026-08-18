import Ttc.Exec.CVSlowRefreshSteps
import Ttc.Exec.CVSharpUniformParameters

/-!
# The frontier's `hsteps` binder, at the **sharp** slack / transport pair

`Ttc.CVSharpFrontier.exists_slowOneRunCertificate_canonical_sharp` carries unprovided
`hsteps` and `hretries` binders.  `Ttc.CVSharpFrontier.canonical_hretries_sharp` discharges
the second at `L := Ttc.CVSharpUniformParameters.slowSharpRetriesCap (m+1) k (eps/2) R`;
this file discharges the first.

It is the sharp analogue of `Ttc.Exec.CVSlowActualSteps` / `Ttc.Exec.CVSlowRefreshSteps`:
the deadline bridge `Ttc.CVSlowActualDeadline.slowCanonicalSteps_le_ceil_of_log_le` is
*bound-independent* and is reused verbatim; only the three logarithmic payloads it consumes
are recomputed at the sharp floor

```
slowSharpFloor6 m k eps R = min (blockShare m k eps) (1 / (54 * exp (8 R^2)^2))
```

whose exponent is **dimension-free** — that is where the factor `n` is saved.

## The two warm routes, merged at the payload

`Ttc.Exec.CVSlowRefreshSteps` keeps the product route and the refresh route in two separate
envelopes and takes their `min` at the very end (`slowMinStepsEnvelope`).  Here the `min` is
taken one level earlier, at the warm payload itself:

```
slowSharpWlog = min slowSharpWlogProduct slowSharpWlogRefresh
```

The deadline expression `Ttc.CVSlowActualDeadline.slowActualDeadlineExpression` is monotone
in its `Wlog` slot with the two share slots fixed, so the resulting envelope is *pointwise
equal* to the minimum of the two envelopes one would obtain by mirroring the two template
files separately — the same value, with one envelope and one `hsteps` theorem instead of
three.  Both routes are available because they depend on the floor only through the retry
cap `L`, which is supplied here as the sharp one.

## Main results

* `slowSharpElog` / `slowSharpZlog` — the two share payloads at the sharp floor, with
  nonnegativity requiring **only** `0 < epsP` (no upper bound on `eps`: the sharp floor is
  at most `1/54` outright).
* `slowSharpRetriesCapAt` — the `L` the frontier's `hretries` binder wants, in the exact
  spelling of `Ttc.CVSharpFrontier.canonical_hretries_sharp`.
* `slowSharpStepsBound` / `slowSharpStepsEnvelope` — the per-phase deadline value and its
  uniform real envelope.
* `slowCanonicalSteps_sharp_le` — **the deliverable**: the frontier's `hsteps` at
  `T := ⌈slowSharpStepsEnvelope …⌉₊ + 1`.
* `cast_slowSharpStepsCap_le` — the real envelope of that natural cap, for the cost side.
* `slowSharpStepsEnvelope_le_actual` — the quantified payoff, under `2 ≤ n` and `1 ≤ R`
  (both are necessary: `Ttc.CVSharpUniformParameters.slowSharpFloor6_ge_slowUniformShareFloor`
  is false at `n = 1` and as `R → 0`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Ttc.CVSharpSlowSteps

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
open Ttc.CVGaussianScoreAwareParameters
open Ttc.CVRefreshWarmRoute
open Ttc.CVSlowActualSteps
open Ttc.CVSharpUniformParameters
open Ttc.CVSharpScoreTransport
open scoped ENNReal

variable {n : Nat}

local notation "State" => fun m => EuclideanSpace Real (Fin m)

/-! ## The sharp floor never exceeds `1/54`

This is the analogue of `Ttc.CVSlowActualSteps.slowUniformShareFloor_le_eighteenth`, and it
is **hypothesis-free**: the sharp exponent `8 R^2` is nonnegative for every real `R`, where
the loose one needed the positivity of the initial variance. -/

theorem slowSharpFloor6_le_fiftyFourth (m k : Nat) (eps R : Real) :
    slowSharpFloor6 m k eps R ≤ 1 / 54 := by
  refine (min_le_right _ _).trans ?_
  have hA : (0 : Real) ≤ 8 * R ^ 2 := by positivity
  have hexp : (1 : Real) ≤ Real.exp (8 * R ^ 2) := Real.one_le_exp hA
  have hsq : (1 : Real) ≤ Real.exp (8 * R ^ 2) ^ 2 := by nlinarith
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)

/-! ## The retry cap and the two share payloads -/

/-- The retry cap the frontier's literal sharp retry family obeys.  This is *exactly* the
`L` produced by `Ttc.CVSharpFrontier.canonical_hretries_sharp`. -/
noncomputable def slowSharpRetriesCapAt (n m k : Nat) (epsP R : Real) : Nat :=
  slowSharpRetriesCap (m + 1) k (epsP / 2) R

/-- The logarithmic envelope of `1 / eta i`, at the sharp share floor. -/
noncomputable def slowSharpElog (n m k : Nat) (epsP R : Real) : Real :=
  Real.log (1 / slowSharpFloor6 (m + 1) k (epsP / 2) R)

/-- The logarithmic envelope of `1 / zeta i`.  The extra factor `32` is the explicit
`share / 32` in `scoreAwareZeta`. -/
noncomputable def slowSharpZlog (n m k : Nat) (epsP R : Real) : Real :=
  Real.log (32 / slowSharpFloor6 (m + 1) k (epsP / 2) R)

theorem slowSharpElog_nonneg
    (n m k : Nat) {epsP R : Real} (hepsP : 0 < epsP) :
    0 ≤ slowSharpElog n m k epsP R := by
  have hf0 : 0 < slowSharpFloor6 (m + 1) k (epsP / 2) R :=
    slowSharpFloor6_pos (by linarith)
  have hf54 : slowSharpFloor6 (m + 1) k (epsP / 2) R ≤ 1 / 54 :=
    slowSharpFloor6_le_fiftyFourth (m + 1) k (epsP / 2) R
  refine Real.log_nonneg ?_
  rw [le_div_iff₀ hf0]
  linarith

theorem slowSharpZlog_nonneg
    (n m k : Nat) {epsP R : Real} (hepsP : 0 < epsP) :
    0 ≤ slowSharpZlog n m k epsP R := by
  have hf0 : 0 < slowSharpFloor6 (m + 1) k (epsP / 2) R :=
    slowSharpFloor6_pos (by linarith)
  have hf54 : slowSharpFloor6 (m + 1) k (epsP / 2) R ≤ 1 / 54 :=
    slowSharpFloor6_le_fiftyFourth (m + 1) k (epsP / 2) R
  refine Real.log_nonneg ?_
  rw [le_div_iff₀ hf0]
  linarith

/-! ## The warm payload, along both available routes

The two warm envelopes depend on the share floor **only** through the retry cap `L`, so
both are available at the sharp cap.  The product route
(`Ttc.CVSlowWarmBudgetBound.log_slowWarmBudget_toReal_le`) compounds the accepted ratio and
the refresh normalizer together, once per phase; the refresh route
(`Ttc.CVRefreshWarmRoute.log_slowWarmBudget_toReal_le_refresh_uniform`) compounds only the
accepted ratio and pays the refresh normalizer once.  Neither dominates the other (see the
module docstring of `Ttc.Exec.CVSlowRefreshSteps`), so the payload is their minimum. -/

/-- The product route's warm payload, padded to the terminal phase `m`, at the **sharp**
retry cap. -/
noncomputable def slowSharpWlogProduct (n m k : Nat) (q epsP R : Real) : Real :=
  Real.log (2 * Real.exp 1) +
    (m : Real) *
      Real.log ((slowWarmFactorEnvelope n q (slowSourceInitialVariance n) m
        (slowSharpRetriesCapAt n m k epsP R)).toReal)

/-- The refresh route's warm payload at the uniform index `m`, at the **sharp** retry
cap. -/
noncomputable def slowSharpWlogRefresh (n m k : Nat) (q epsP R : Real) : Real :=
  slowRefreshWlog n q (slowSourceInitialVariance n) m
    (slowSharpRetriesCapAt n m k epsP R) m

/-- **The warm payload.**  Both routes are available simultaneously, so the deadline may
consume whichever is smaller. -/
noncomputable def slowSharpWlog (n m k : Nat) (q epsP R : Real) : Real :=
  min (slowSharpWlogProduct n m k q epsP R) (slowSharpWlogRefresh n m k q epsP R)

theorem slowSharpWlogProduct_nonneg (n m k : Nat) (q epsP R : Real) :
    0 ≤ slowSharpWlogProduct n m k q epsP R := by
  unfold slowSharpWlogProduct
  have h1 : 0 ≤ Real.log (2 * Real.exp 1) := by
    refine Real.log_nonneg ?_
    have he : (1 : Real) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    linarith
  have h2 : 0 ≤ Real.log ((slowWarmFactorEnvelope n q (slowSourceInitialVariance n) m
      (slowSharpRetriesCapAt n m k epsP R)).toReal) :=
    Real.log_nonneg (one_le_slowWarmFactorEnvelope_toReal _ _ _ _ _)
  have := mul_nonneg (Nat.cast_nonneg (α := Real) m) h2
  linarith

theorem slowSharpWlogRefresh_nonneg
    (hn : 1 ≤ n) (m k : Nat) (q epsP R : Real) :
    0 ≤ slowSharpWlogRefresh n m k q epsP R := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have h1 : 0 ≤ (m : Real) *
      Real.log (slowAcceptedCap (slowSharpRetriesCapAt n m k epsP R)).toReal :=
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
  unfold slowSharpWlogRefresh slowRefreshWlog
  linarith

theorem slowSharpWlog_nonneg (hn : 1 ≤ n) (m k : Nat) (q epsP R : Real) :
    0 ≤ slowSharpWlog n m k q epsP R :=
  le_min (slowSharpWlogProduct_nonneg n m k q epsP R)
    (slowSharpWlogRefresh_nonneg hn m k q epsP R)

theorem slowSharpWlog_le_product (n m k : Nat) (q epsP R : Real) :
    slowSharpWlog n m k q epsP R ≤ slowSharpWlogProduct n m k q epsP R :=
  min_le_left _ _

theorem slowSharpWlog_le_refresh (n m k : Nat) (q epsP R : Real) :
    slowSharpWlog n m k q epsP R ≤ slowSharpWlogRefresh n m k q epsP R :=
  min_le_right _ _

/-! ## The sharp deadline value and its uniform envelope -/

/-- The per-phase deadline value the actual slow canonical schedule selects, at the three
sharp payloads. -/
noncomputable def slowSharpStepsBound
    (n m k : Nat) (q epsP R : Real) (i : Nat) : Real :=
  slowActualDeadlineExpression n
    (radiusQDelta n q (slowSourceSigmaSq n (slowSourceInitialVariance n) i))
    (slowSourceSigmaSq n (slowSourceInitialVariance n) i)
    (slowSharpWlog n m k q epsP R) (slowSharpElog n m k epsP R)
    (slowSharpZlog n m k epsP R)

/-- One real envelope valid at every phase: the variance is taken at the terminal phase `m`
(largest) and the mixing radius at the initial variance (smallest, and the expression
divides by its square). -/
noncomputable def slowSharpStepsEnvelope
    (n m k : Nat) (q epsP R : Real) : Real :=
  slowActualDeadlineExpression n
    (radiusQDelta n q (slowSourceInitialVariance n))
    (slowSourceSigmaSq n (slowSourceInitialVariance n) m)
    (slowSharpWlog n m k q epsP R) (slowSharpElog n m k epsP R)
    (slowSharpZlog n m k epsP R)

/-- The full logarithmic payload of the sharp deadline expression is nonnegative. -/
theorem slowSharpPayload_nonneg
    (hn : 1 ≤ n) {m k : Nat} {q epsP R : Real} (hepsP : 0 < epsP) :
    0 ≤ (Real.log 2 + slowSharpWlog n m k q epsP R + slowSharpElog n m k epsP R) +
      2 * slowSharpZlog n m k epsP R := by
  have h0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h1 := slowSharpWlog_nonneg hn m k q epsP R
  have h2 := slowSharpElog_nonneg n m k (R := R) hepsP
  have h3 := slowSharpZlog_nonneg n m k (R := R) hepsP
  linarith

/-- The per-phase deadline value is below the uniform envelope at every phase of the
schedule. -/
theorem slowSharpStepsBound_le_envelope
    (hn : 1 ≤ n) {m k : Nat} {q epsP R : Real} (hq : 0 < q) (hepsP : 0 < epsP)
    {i : Nat} (hi : i ≤ m) :
    slowSharpStepsBound n m k q epsP R i ≤ slowSharpStepsEnvelope n m k q epsP R := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have hsigle : slowSourceSigmaSq n (slowSourceInitialVariance n) i ≤
      slowSourceSigmaSq n (slowSourceInitialVariance n) m :=
    slowSourceSigmaSq_le_terminal hn hs0 hi
  have hd0 : 0 < radiusQDelta n q (slowSourceInitialVariance n) :=
    radiusQDelta_pos hn hq hs0
  have hdle : radiusQDelta n q (slowSourceInitialVariance n) ≤
      radiusQDelta n q (slowSourceSigmaSq n (slowSourceInitialVariance n) i) :=
    Ttc.CVSlowActualSteps.radiusQDelta_mono_variance n q
      (slowSourceSigmaSq_mono_start hn hs0 i)
  have hP := slowSharpPayload_nonneg (n := n) hn (m := m) (k := k) (q := q) (R := R) hepsP
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsigi : 0 ≤ slowSourceSigmaSq n (slowSourceInitialVariance n) i :=
    (slowSourceSigmaSq_pos hn hs0 i).le
  unfold slowSharpStepsBound slowSharpStepsEnvelope slowActualDeadlineExpression
  gcongr
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hsigi.trans hsigle))
    (Nat.cast_nonneg n)) hP

theorem slowSharpStepsEnvelope_nonneg
    (hn : 1 ≤ n) {m k : Nat} {q epsP R : Real} (hepsP : 0 < epsP) :
    0 ≤ slowSharpStepsEnvelope n m k q epsP R := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have hsigm : 0 ≤ slowSourceSigmaSq n (slowSourceInitialVariance n) m :=
    (slowSourceSigmaSq_pos hn hs0 m).le
  have hP := slowSharpPayload_nonneg (n := n) hn (m := m) (k := k) (q := q) (R := R) hepsP
  unfold slowSharpStepsEnvelope slowActualDeadlineExpression
  have hnum : 0 ≤ 4 * 640 ^ 2 * slowSourceSigmaSq n (slowSourceInitialVariance n) m *
      (n : Real) *
      ((Real.log 2 + slowSharpWlog n m k q epsP R + slowSharpElog n m k epsP R) +
        2 * slowSharpZlog n m k epsP R) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hsigm) (Nat.cast_nonneg n)) hP
  have hden : 0 ≤ (radiusQDelta n q (slowSourceInitialVariance n) * Real.log 2) ^ 2 :=
    sq_nonneg _
  have := div_nonneg hnum hden
  linarith

/-- The natural cap of `slowCanonicalSteps_sharp_le` is bounded, as a real, by the envelope
plus `2`; this is the `Tenv` the cost assembly consumes. -/
theorem cast_slowSharpStepsCap_le
    (n m k : Nat) (q epsP R : Real)
    (hE : 0 ≤ slowSharpStepsEnvelope n m k q epsP R) :
    ((⌈slowSharpStepsEnvelope n m k q epsP R⌉₊ + 1 : Nat) : Real) ≤
      slowSharpStepsEnvelope n m k q epsP R + 2 :=
  cast_ceil_add_one_le _ hE

/-! ## The deliverable: the frontier's `hsteps` binder at the sharp pair -/

/-- **The deliverable.**  Every active phase of the *actual* slow canonical schedule at the
**sharp** slack / transport pair — the one whose warmness argument is the compounding
`slowWarmBudget`, and whose shares are the literal score-aware families
`Ttc.CVSharpFrontier.exists_slowOneRunCertificate_canonical_sharp` forces — obeys one
explicit natural deadline cap, namely `⌈slowSharpStepsEnvelope …⌉₊ + 1`.

The conclusion is byte-identical to
`Ttc.CVSlowActualSteps.slowCanonicalSteps_actual_le`'s except for the three substitutions
`slowUniformSlack n m K ↦ slowSharpSlack n m K`,
`slowUniformBoundSq n R ↦ slowSharpBoundSq n R` and the envelope. -/
theorem slowCanonicalSteps_sharp_le
    (hn : 1 ≤ n) (m k : Nat) {q epsP R : Real} (hq : 0 < q) (hepsP : 0 < epsP)
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    (hball : Metric.ball (0 : EuclideanSpace Real (Fin n)) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i < m) :
    slowCanonicalSteps slowReferenceWarm n q (slowSourceInitialVariance n) K
        (scoreAwareRetries (m + 1) k (epsP / 2)
          (slowSharpSlack n m K) (slowSharpBoundSq n R))
        (scoreAwareEta (m + 1) k (epsP / 2)
          (slowSharpSlack n m K) (slowSharpBoundSq n R))
        (scoreAwareZeta (m + 1) k (epsP / 2)
          (slowSharpSlack n m K) (slowSharpBoundSq n R))
        i 0 ≤
      ⌈slowSharpStepsEnvelope n m k q epsP R⌉₊ + 1 := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have heps2 : (0 : Real) < epsP / 2 := by linarith
  -- the actual phase share, and the sharp floor below it
  have hshare0 : 0 < scoreAwareShare (m + 1) k (epsP / 2)
      (slowSharpSlack n m K) (slowSharpBoundSq n R) i :=
    scoreAwareShare_pos heps2 (slowSharpSlack_pos hn hball hfin)
      (fun j ↦ slowSharpBoundSq_pos (n := n) (R := R) j) i
  have hfloor0 : 0 < slowSharpFloor6 (m + 1) k (epsP / 2) R :=
    slowSharpFloor6_pos heps2
  have hfloor : slowSharpFloor6 (m + 1) k (epsP / 2) R ≤
      scoreAwareShare (m + 1) k (epsP / 2)
        (slowSharpSlack n m K) (slowSharpBoundSq n R) i :=
    slowSharpFloor6_le_scoreAwareShare (chainLength := m) hn hK hball hfin i
  -- the compounding warm budget is finite and at least one
  have hW := slowWarmBudget_ne_top (q := q) hn hs0 hK
    (scoreAwareRetries (m + 1) k (epsP / 2)
      (slowSharpSlack n m K) (slowSharpBoundSq n R)) i
  have hW1 := one_le_slowWarmBudget
    (scoreAwareRetries (m + 1) k (epsP / 2)
      (slowSharpSlack n m K) (slowSharpBoundSq n R))
    n q (slowSourceInitialVariance n) K i
  have hW0 : 0 < (slowWarmBudget slowReferenceWarm n q (slowSourceInitialVariance n) K
      (scoreAwareRetries (m + 1) k (epsP / 2)
        (slowSharpSlack n m K) (slowSharpBoundSq n R)) i).toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one hW1)) hW
  -- the sharp retry cap
  have hL : ∀ j, scoreAwareRetries (m + 1) k (epsP / 2)
      (slowSharpSlack n m K) (slowSharpBoundSq n R) j ≤
      slowSharpRetriesCapAt n m k epsP R :=
    fun j ↦ scoreAwareRetries_slowSharp_le (chainLength := m) hn heps2 hK hball hfin j
  -- the warm-budget logarithm, along both routes
  have hWprod : Real.log (slowWarmBudget slowReferenceWarm n q
      (slowSourceInitialVariance n) K
      (scoreAwareRetries (m + 1) k (epsP / 2)
        (slowSharpSlack n m K) (slowSharpBoundSq n R)) i).toReal ≤
      slowSharpWlogProduct n m k q epsP R := by
    refine (log_slowWarmBudget_toReal_le hn hq.le hs0 hK hL hi.le).trans ?_
    unfold slowSharpWlogProduct
    have hlogE : 0 ≤ Real.log ((slowWarmFactorEnvelope n q (slowSourceInitialVariance n) m
        (slowSharpRetriesCapAt n m k epsP R)).toReal) :=
      Real.log_nonneg (one_le_slowWarmFactorEnvelope_toReal _ _ _ _ _)
    have him : (i : Real) ≤ (m : Real) := by exact_mod_cast hi.le
    nlinarith
  have hWref : Real.log (slowWarmBudget slowReferenceWarm n q
      (slowSourceInitialVariance n) K
      (scoreAwareRetries (m + 1) k (epsP / 2)
        (slowSharpSlack n m K) (slowSharpBoundSq n R)) i).toReal ≤
      slowSharpWlogRefresh n m k q epsP R :=
    log_slowWarmBudget_toReal_le_refresh_uniform hn hq.le hs0 hK hL hi.le
  have hWlog : Real.log (slowWarmBudget slowReferenceWarm n q
      (slowSourceInitialVariance n) K
      (scoreAwareRetries (m + 1) k (epsP / 2)
        (slowSharpSlack n m K) (slowSharpBoundSq n R)) i).toReal ≤
      slowSharpWlog n m k q epsP R := le_min hWprod hWref
  -- the two share logarithms
  have heta : (scoreAwareEta (m + 1) k (epsP / 2)
      (slowSharpSlack n m K) (slowSharpBoundSq n R) i).toReal =
      scoreAwareShare (m + 1) k (epsP / 2)
        (slowSharpSlack n m K) (slowSharpBoundSq n R) i := by
    rw [scoreAwareEta, ENNReal.toReal_ofReal hshare0.le]
  have hzeta : (scoreAwareZeta (m + 1) k (epsP / 2)
      (slowSharpSlack n m K) (slowSharpBoundSq n R) i).toReal =
      scoreAwareShare (m + 1) k (epsP / 2)
        (slowSharpSlack n m K) (slowSharpBoundSq n R) i / 32 := by
    rw [scoreAwareZeta, ENNReal.toReal_ofReal (by positivity)]
  have heta0 : scoreAwareEta (m + 1) k (epsP / 2)
      (slowSharpSlack n m K) (slowSharpBoundSq n R) i ≠ 0 := by
    rw [scoreAwareEta, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hshare0
  have hetaTop : scoreAwareEta (m + 1) k (epsP / 2)
      (slowSharpSlack n m K) (slowSharpBoundSq n R) i ≠ ⊤ := by
    rw [scoreAwareEta]; exact ENNReal.ofReal_ne_top
  have hElog : Real.log (1 / (scoreAwareEta (m + 1) k (epsP / 2)
      (slowSharpSlack n m K) (slowSharpBoundSq n R) i).toReal) ≤
      slowSharpElog n m k epsP R := by
    rw [heta]
    unfold slowSharpElog
    exact Real.log_le_log (by positivity) (one_div_le_one_div_of_le hfloor0 hfloor)
  have hZlog : Real.log (1 / (scoreAwareZeta (m + 1) k (epsP / 2)
      (slowSharpSlack n m K) (slowSharpBoundSq n R) i).toReal) ≤
      slowSharpZlog n m k epsP R := by
    rw [hzeta, show 1 / (scoreAwareShare (m + 1) k (epsP / 2)
        (slowSharpSlack n m K) (slowSharpBoundSq n R) i / 32) =
        32 / scoreAwareShare (m + 1) k (epsP / 2)
          (slowSharpSlack n m K) (slowSharpBoundSq n R) i by field_simp]
    unfold slowSharpZlog
    exact Real.log_le_log (by positivity)
      (div_le_div_of_nonneg_left (by norm_num) hfloor0 hfloor)
  exact slowCanonicalSteps_le_ceil_of_log_le hn hq hs0 hW hW0 heta0 hetaTop hWlog hElog
    hZlog (slowSharpStepsBound_le_envelope hn hq hepsP hi.le)

/-! ## The quantified payoff: the sharp envelope dominates the loose one

Both hypotheses `2 ≤ n` and `1 ≤ R` are inherited from
`Ttc.CVSharpUniformParameters.slowSharpFloor6_ge_slowUniformShareFloor`, and both are
**necessary** there: at `n = 1` the two exponents agree and the `18 → 54` that the `/6`
mixing slack costs makes the floor comparison false, and it is false as `R → 0` at every
`n`.  Downstream `ball 0 1 ⊆ K ⊆ closedBall 0 R` forces `1 ≤ R` anyway.  So the dominance
is **not** unconditional, and is not asserted to be. -/

/-- The product route's per-phase factor is monotone in the retry cap. -/
theorem slowWarmFactorEnvelope_mono_retries
    (n : Nat) (q s0 : Real) (m : Nat) {L L' : Nat} (hL : L ≤ L') :
    slowWarmFactorEnvelope n q s0 m L ≤ slowWarmFactorEnvelope n q s0 m L' := by
  have hcast : ((L : ENNReal)) * (16 * ENNReal.ofReal (2 * Real.exp 1)) ≤
      ((L' : ENNReal)) * (16 * ENNReal.ofReal (2 * Real.exp 1)) :=
    mul_le_mul_right' (Nat.cast_le.2 hL) _
  unfold slowWarmFactorEnvelope
  exact add_le_add (max_le_max le_rfl hcast) le_rfl

theorem log_slowWarmFactorEnvelope_mono_retries
    (n : Nat) (q s0 : Real) (m : Nat) {L L' : Nat} (hL : L ≤ L') :
    Real.log ((slowWarmFactorEnvelope n q s0 m L).toReal) ≤
      Real.log ((slowWarmFactorEnvelope n q s0 m L').toReal) := by
  have hone : (1 : Real) ≤ (slowWarmFactorEnvelope n q s0 m L).toReal :=
    one_le_slowWarmFactorEnvelope_toReal n q s0 m L
  have hmono : (slowWarmFactorEnvelope n q s0 m L).toReal ≤
      (slowWarmFactorEnvelope n q s0 m L').toReal :=
    ENNReal.toReal_mono (slowWarmFactorEnvelope_ne_top n q s0 m L')
      (slowWarmFactorEnvelope_mono_retries n q s0 m hL)
  exact Real.log_le_log (by linarith) hmono

/-- The sharp retry cap is below the loose one — the quantified runtime payoff, transported
to the exact spelling this file uses. -/
theorem slowSharpRetriesCapAt_le_slowActualRetriesCap
    {n : Nat} (hn : 2 ≤ n) (m k : Nat) {epsP R : Real}
    (hepsP : 0 < epsP) (hR : 1 ≤ R) :
    slowSharpRetriesCapAt n m k epsP R ≤
      Ttc.CVSlowActualSteps.slowActualRetriesCap n m k epsP R :=
  slowSharpRetriesCap_le_slowUniformRetriesCap (n := n) hn (by linarith) hR

/-- The sharp warm payload is below the loose one: the payloads differ only through the
retry cap, and the sharp cap is smaller. -/
theorem slowSharpWlog_le_slowActualWlog
    {n : Nat} (hn : 2 ≤ n) (m k : Nat) (q : Real) {epsP R : Real}
    (hepsP : 0 < epsP) (hR : 1 ≤ R) :
    slowSharpWlog n m k q epsP R ≤
      Ttc.CVSlowActualSteps.slowActualWlog n m k q epsP R := by
  refine (slowSharpWlog_le_product n m k q epsP R).trans ?_
  unfold slowSharpWlogProduct Ttc.CVSlowActualSteps.slowActualWlog
  have hlog := log_slowWarmFactorEnvelope_mono_retries n q (slowSourceInitialVariance n) m
    (slowSharpRetriesCapAt_le_slowActualRetriesCap hn m k hepsP hR)
  have hm : (0 : Real) ≤ (m : Real) := Nat.cast_nonneg m
  nlinarith

theorem slowSharpElog_le_slowActualElog
    {n : Nat} (hn : 2 ≤ n) (m k : Nat) {epsP R : Real}
    (hepsP : 0 < epsP) (hR : 1 ≤ R) :
    slowSharpElog n m k epsP R ≤ Ttc.CVSlowActualSteps.slowActualElog n m k epsP R := by
  have hU0 : 0 < Ttc.CVSlowUniformShareBounds.slowUniformShareFloor (m + 1) k (epsP / 2) R
      (slowSourceInitialVariance n) :=
    Ttc.CVSlowUniformShareBounds.slowUniformShareFloor_pos (by linarith)
  have hf0 : 0 < slowSharpFloor6 (m + 1) k (epsP / 2) R :=
    slowSharpFloor6_pos (by linarith)
  have hcmp := slowSharpFloor6_ge_slowUniformShareFloor (n := n) hn (m + 1) k (epsP / 2) hR
  unfold slowSharpElog Ttc.CVSlowActualSteps.slowActualElog
  exact Real.log_le_log (one_div_pos.2 hf0) (one_div_le_one_div_of_le hU0 hcmp)

theorem slowSharpZlog_le_slowActualZlog
    {n : Nat} (hn : 2 ≤ n) (m k : Nat) {epsP R : Real}
    (hepsP : 0 < epsP) (hR : 1 ≤ R) :
    slowSharpZlog n m k epsP R ≤ Ttc.CVSlowActualSteps.slowActualZlog n m k epsP R := by
  have hU0 : 0 < Ttc.CVSlowUniformShareBounds.slowUniformShareFloor (m + 1) k (epsP / 2) R
      (slowSourceInitialVariance n) :=
    Ttc.CVSlowUniformShareBounds.slowUniformShareFloor_pos (by linarith)
  have hf0 : 0 < slowSharpFloor6 (m + 1) k (epsP / 2) R :=
    slowSharpFloor6_pos (by linarith)
  have hcmp := slowSharpFloor6_ge_slowUniformShareFloor (n := n) hn (m + 1) k (epsP / 2) hR
  unfold slowSharpZlog Ttc.CVSlowActualSteps.slowActualZlog
  exact Real.log_le_log (div_pos (by norm_num) hf0)
    (div_le_div_of_nonneg_left (by norm_num) hU0 hcmp)

/-- **The payoff, machine-checked.**  The sharp deadline envelope is below the loose
actual-deadline envelope of `Ttc.Exec.CVSlowActualSteps`, under exactly the two hypotheses
that the sharp floor comparison itself requires. -/
theorem slowSharpStepsEnvelope_le_actual
    {n : Nat} (hn : 2 ≤ n) (m k : Nat) {q epsP R : Real}
    (hepsP : 0 < epsP) (hR : 1 ≤ R) :
    slowSharpStepsEnvelope n m k q epsP R ≤
      Ttc.CVSlowActualSteps.slowActualStepsEnvelope n m k q epsP R := by
  have hn1 : 1 ≤ n := by omega
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn1
  have hsigm : 0 ≤ slowSourceSigmaSq n (slowSourceInitialVariance n) m :=
    (slowSourceSigmaSq_pos hn1 hs0 m).le
  have hW := slowSharpWlog_le_slowActualWlog hn m k q hepsP hR
  have hE := slowSharpElog_le_slowActualElog hn m k hepsP hR
  have hZ := slowSharpZlog_le_slowActualZlog hn m k hepsP hR
  unfold slowSharpStepsEnvelope Ttc.CVSlowActualSteps.slowActualStepsEnvelope
    slowActualDeadlineExpression
  have hcoef : (0 : Real) ≤ 4 * 640 ^ 2 *
      slowSourceSigmaSq n (slowSourceInitialVariance n) m * (n : Real) := by positivity
  gcongr

/-- The same comparison against the `min` route of `Ttc.Exec.CVSlowRefreshSteps`: the sharp
envelope's warm payload is *already* the minimum of the two routes, at a smaller retry cap,
so it is below the refresh envelope too. -/
theorem slowSharpStepsEnvelope_le_refresh
    {n : Nat} (hn : 2 ≤ n) (m k : Nat) {q epsP R : Real}
    (hepsP : 0 < epsP) (hR : 1 ≤ R) :
    slowSharpStepsEnvelope n m k q epsP R ≤
      Ttc.CVSlowRefreshSteps.slowRefreshStepsEnvelope n m k q epsP R := by
  have hn1 : 1 ≤ n := by omega
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn1
  have hsigm : 0 ≤ slowSourceSigmaSq n (slowSourceInitialVariance n) m :=
    (slowSourceSigmaSq_pos hn1 hs0 m).le
  have hcap := slowSharpRetriesCapAt_le_slowActualRetriesCap hn m k hepsP hR
  have hA : Real.log (slowAcceptedCap (slowSharpRetriesCapAt n m k epsP R)).toReal ≤
      Real.log (slowAcceptedCap
        (Ttc.CVSlowActualSteps.slowActualRetriesCap n m k epsP R)).toReal := by
    have hone : (1 : Real) ≤
        (slowAcceptedCap (slowSharpRetriesCapAt n m k epsP R)).toReal :=
      one_le_slowAcceptedCap_toReal _
    refine Real.log_le_log (by linarith) (ENNReal.toReal_mono (slowAcceptedCap_ne_top _) ?_)
    unfold slowAcceptedCap
    exact max_le_max le_rfl (mul_le_mul_right' (Nat.cast_le.2 hcap) _)
  have hW : slowSharpWlog n m k q epsP R ≤
      Ttc.CVSlowRefreshSteps.slowRefreshUniformWlog n m k q epsP R := by
    refine (slowSharpWlog_le_refresh n m k q epsP R).trans ?_
    unfold slowSharpWlogRefresh Ttc.CVSlowRefreshSteps.slowRefreshUniformWlog
      slowRefreshWlog
    have hm : (0 : Real) ≤ (m : Real) := Nat.cast_nonneg m
    nlinarith
  have hE := slowSharpElog_le_slowActualElog hn m k hepsP hR
  have hZ := slowSharpZlog_le_slowActualZlog hn m k hepsP hR
  unfold slowSharpStepsEnvelope Ttc.CVSlowRefreshSteps.slowRefreshStepsEnvelope
    slowActualDeadlineExpression
  have hcoef : (0 : Real) ≤ 4 * 640 ^ 2 *
      slowSourceSigmaSq n (slowSourceInitialVariance n) m * (n : Real) := by positivity
  gcongr

/-- Hence the sharp envelope is below `Ttc.CVSlowRefreshSteps.slowMinStepsEnvelope`, the
best envelope the loose route offers. -/
theorem slowSharpStepsEnvelope_le_min
    {n : Nat} (hn : 2 ≤ n) (m k : Nat) {q epsP R : Real}
    (hepsP : 0 < epsP) (hR : 1 ≤ R) :
    slowSharpStepsEnvelope n m k q epsP R ≤
      Ttc.CVSlowRefreshSteps.slowMinStepsEnvelope n m k q epsP R :=
  le_min (slowSharpStepsEnvelope_le_actual hn m k hepsP hR)
    (slowSharpStepsEnvelope_le_refresh hn m k hepsP hR)

#print axioms slowSharpFloor6_le_fiftyFourth
#print axioms slowSharpRetriesCapAt
#print axioms slowSharpElog
#print axioms slowSharpZlog
#print axioms slowSharpElog_nonneg
#print axioms slowSharpZlog_nonneg
#print axioms slowSharpWlogProduct
#print axioms slowSharpWlogRefresh
#print axioms slowSharpWlog
#print axioms slowSharpWlogProduct_nonneg
#print axioms slowSharpWlogRefresh_nonneg
#print axioms slowSharpWlog_nonneg
#print axioms slowSharpWlog_le_product
#print axioms slowSharpWlog_le_refresh
#print axioms slowSharpStepsBound
#print axioms slowSharpStepsEnvelope
#print axioms slowSharpPayload_nonneg
#print axioms slowSharpStepsBound_le_envelope
#print axioms slowSharpStepsEnvelope_nonneg
#print axioms cast_slowSharpStepsCap_le
#print axioms slowCanonicalSteps_sharp_le
#print axioms slowWarmFactorEnvelope_mono_retries
#print axioms log_slowWarmFactorEnvelope_mono_retries
#print axioms slowSharpRetriesCapAt_le_slowActualRetriesCap
#print axioms slowSharpWlog_le_slowActualWlog
#print axioms slowSharpElog_le_slowActualElog
#print axioms slowSharpZlog_le_slowActualZlog
#print axioms slowSharpStepsEnvelope_le_actual
#print axioms slowSharpStepsEnvelope_le_refresh
#print axioms slowSharpStepsEnvelope_le_min

end Ttc.CVSharpSlowSteps
