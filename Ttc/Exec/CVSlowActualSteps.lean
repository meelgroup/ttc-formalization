import Ttc.Exec.CVSlowActualDeadline
import Ttc.Exec.CVSlowUniformShareBounds

/-!
# The frontier's `hsteps` binder, at the actual slow canonical schedule

`Ttc.CVSlowOneRunValid.exists_slowOneRunCertificate_canonical` carries an unprovided
`hsteps` binder: a uniform natural cap `T` on

```
slowCanonicalSteps slowReferenceWarm n q s0 K
  (scoreAwareRetries (m+1) k (eps/2) slack boundSq)
  (scoreAwareEta    (m+1) k (eps/2) slack boundSq)
  (scoreAwareZeta   (m+1) k (eps/2) slack boundSq) i 0
```

for every active phase `i < m`, where the warmness argument is the **compounding
actual-path** budget `slowWarmBudget`, not the fixed reference warm.  This file produces
that cap outright, together with the real envelope the cost side consumes as `Tenv`.

Three proved ingredients are combined:

* `Ttc.CVSlowWarmBudgetBound.log_slowWarmBudget_toReal_le` — the compounding budget's
  logarithm grows by at most one additive term per phase;
* `Ttc.CVSlowActualDeadline.slowCanonicalSteps_le_ceil_of_log_le` — the deadline bridge,
  consuming logarithmic bounds on the warm budget and on the two (different!) shares
  `eta` and `zeta`;
* `Ttc.CVSlowUniformShareBounds.slowUniformShareFloor_le_scoreAwareShare` and
  `…scoreAwareRetries_slowUniform_le` — one global floor below every phase share, and the
  induced retry cap.

The phase index is eliminated **uniformly**, not by a `Finset.sup`: the variance `σᵢ` is
bounded above by the terminal `σ_m` and the mixing radius `radiusQDelta n q σᵢ` below by
its value at the initial variance `s0` (it is monotone in the variance, and the deadline
expression divides by its square, so the smallest radius gives the largest deadline).

## Main results

* `slowActualStepsBound` / `slowActualStepsEnvelope` — the per-phase deadline value and
  its uniform real envelope.
* `slowCanonicalSteps_actual_le` — **the deliverable**: the frontier's `hsteps` at
  `T := ⌈slowActualStepsEnvelope …⌉₊ + 1`.
* `cast_slowActualStepsCap_le` — the real envelope of that natural cap, for the cost side.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Ttc.CVSlowActualSteps

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
open scoped ENNReal

variable {n : Nat}

local notation "State" => fun m => EuclideanSpace Real (Fin m)

/-! ## Two elementary monotonicity facts -/

/-- The uniform share floor never exceeds `1/18`: its exponential branch is at most
`1/18` because the exponent `R² / (2 s0)` is nonnegative.  This is what makes the two
logarithmic payloads nonnegative without any upper bound on `eps`. -/
theorem slowUniformShareFloor_le_eighteenth
    {m k : Nat} {eps R s0 : Real} (hs0 : 0 < s0) :
    slowUniformShareFloor m k eps R s0 ≤ 1 / 18 := by
  refine (min_le_right _ _).trans ?_
  have hA : (0 : Real) ≤ R ^ 2 / (2 * s0) := by positivity
  have hexp : (1 : Real) ≤ Real.exp (R ^ 2 / (2 * s0)) := Real.one_le_exp hA
  have hsq : (1 : Real) ≤ Real.exp (R ^ 2 / (2 * s0)) ^ 2 := by nlinarith
  apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)

/-- The mixing radius is monotone in the variance: both branches of the `min` are. -/
theorem radiusQDelta_mono_variance
    (n : Nat) (q : Real) {s s' : Real} (hss : s ≤ s') :
    radiusQDelta n q s ≤ radiusQDelta n q s' := by
  unfold radiusQDelta
  refine min_le_min ?_ le_rfl
  have hden : (0 : Real) ≤ max 8 (2 * q) * Real.sqrt n := by
    have h8 : (0 : Real) ≤ max 8 (2 * q) := le_trans (by norm_num) (le_max_left _ _)
    positivity
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hss) (inv_nonneg.2 hden)

/-! ## The three logarithmic payloads of the actual schedule -/

/-- The retry cap the frontier's literal retry family obeys: it is the uniform cap at the
share-family parameters `(m+1, k, epsP/2)`. -/
noncomputable def slowActualRetriesCap (n m k : Nat) (epsP R : Real) : Nat :=
  slowUniformRetriesCap (m + 1) k (epsP / 2) R (slowSourceInitialVariance n)

/-- The compounding warm budget's logarithmic envelope, padded to the terminal phase so
that it is valid simultaneously at every `i ≤ m`. -/
noncomputable def slowActualWlog (n m k : Nat) (q epsP R : Real) : Real :=
  Real.log (2 * Real.exp 1) +
    (m : Real) *
      Real.log ((slowWarmFactorEnvelope n q (slowSourceInitialVariance n) m
        (slowActualRetriesCap n m k epsP R)).toReal)

/-- The logarithmic envelope of `1 / eta i`, at the uniform share floor. -/
noncomputable def slowActualElog (n m k : Nat) (epsP R : Real) : Real :=
  Real.log (1 / slowUniformShareFloor (m + 1) k (epsP / 2) R (slowSourceInitialVariance n))

/-- The logarithmic envelope of `1 / zeta i`.  The extra factor `32` is the explicit
`share / 32` in `scoreAwareZeta`. -/
noncomputable def slowActualZlog (n m k : Nat) (epsP R : Real) : Real :=
  Real.log (32 / slowUniformShareFloor (m + 1) k (epsP / 2) R (slowSourceInitialVariance n))

/-- **Deliverable 1.**  The per-phase deadline value the actual slow canonical schedule
selects, at the three envelopes above. -/
noncomputable def slowActualStepsBound
    (n : Nat) (m k : Nat) (q epsP R : Real) (i : Nat) : Real :=
  slowActualDeadlineExpression n
    (radiusQDelta n q (slowSourceSigmaSq n (slowSourceInitialVariance n) i))
    (slowSourceSigmaSq n (slowSourceInitialVariance n) i)
    (slowActualWlog n m k q epsP R) (slowActualElog n m k epsP R)
    (slowActualZlog n m k epsP R)

/-- **Deliverable 2.**  One real envelope valid at every phase: the variance is taken at
the terminal phase `m` (largest) and the mixing radius at the initial variance (smallest,
and the expression divides by its square). -/
noncomputable def slowActualStepsEnvelope
    (n m k : Nat) (q epsP R : Real) : Real :=
  slowActualDeadlineExpression n
    (radiusQDelta n q (slowSourceInitialVariance n))
    (slowSourceSigmaSq n (slowSourceInitialVariance n) m)
    (slowActualWlog n m k q epsP R) (slowActualElog n m k epsP R)
    (slowActualZlog n m k epsP R)

/-! ## Nonnegativity of the payloads -/

theorem slowActualWlog_nonneg (n m k : Nat) (q epsP R : Real) :
    0 ≤ slowActualWlog n m k q epsP R := by
  unfold slowActualWlog
  have h1 : 0 ≤ Real.log (2 * Real.exp 1) := by
    refine Real.log_nonneg ?_
    have he : (1 : Real) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    linarith
  have h2 : 0 ≤ Real.log ((slowWarmFactorEnvelope n q (slowSourceInitialVariance n) m
      (slowActualRetriesCap n m k epsP R)).toReal) :=
    Real.log_nonneg (one_le_slowWarmFactorEnvelope_toReal _ _ _ _ _)
  have := mul_nonneg (Nat.cast_nonneg (α := Real) m) h2
  linarith

theorem slowActualElog_nonneg
    (hn : 1 ≤ n) {m k : Nat} {epsP R : Real} (hepsP : 0 < epsP) :
    0 ≤ slowActualElog n m k epsP R := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have hf0 : 0 < slowUniformShareFloor (m + 1) k (epsP / 2) R
      (slowSourceInitialVariance n) := slowUniformShareFloor_pos (by linarith)
  have hf18 : slowUniformShareFloor (m + 1) k (epsP / 2) R
      (slowSourceInitialVariance n) ≤ 1 / 18 :=
    slowUniformShareFloor_le_eighteenth hs0
  refine Real.log_nonneg ?_
  rw [le_div_iff₀ hf0]
  linarith

theorem slowActualZlog_nonneg
    (hn : 1 ≤ n) {m k : Nat} {epsP R : Real} (hepsP : 0 < epsP) :
    0 ≤ slowActualZlog n m k epsP R := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have hf0 : 0 < slowUniformShareFloor (m + 1) k (epsP / 2) R
      (slowSourceInitialVariance n) := slowUniformShareFloor_pos (by linarith)
  have hf18 : slowUniformShareFloor (m + 1) k (epsP / 2) R
      (slowSourceInitialVariance n) ≤ 1 / 18 :=
    slowUniformShareFloor_le_eighteenth hs0
  refine Real.log_nonneg ?_
  rw [le_div_iff₀ hf0]
  linarith

/-- The full logarithmic payload of the deadline expression is nonnegative. -/
theorem slowActualPayload_nonneg
    (hn : 1 ≤ n) {m k : Nat} {q epsP R : Real} (hepsP : 0 < epsP) :
    0 ≤ (Real.log 2 + slowActualWlog n m k q epsP R + slowActualElog n m k epsP R) +
      2 * slowActualZlog n m k epsP R := by
  have h0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h1 := slowActualWlog_nonneg n m k q epsP R
  have h2 := slowActualElog_nonneg (n := n) hn (m := m) (k := k) (R := R) hepsP
  have h3 := slowActualZlog_nonneg (n := n) hn (m := m) (k := k) (R := R) hepsP
  linarith

/-! ## The uniform envelope dominates every phase -/

/-- **Deliverable 2.**  The per-phase deadline value is below the uniform envelope at
every phase of the schedule. -/
theorem slowActualStepsBound_le_envelope
    (hn : 1 ≤ n) {m k : Nat} {q epsP R : Real} (hq : 0 < q) (hepsP : 0 < epsP)
    {i : Nat} (hi : i ≤ m) :
    slowActualStepsBound n m k q epsP R i ≤ slowActualStepsEnvelope n m k q epsP R := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have hsigle : slowSourceSigmaSq n (slowSourceInitialVariance n) i ≤
      slowSourceSigmaSq n (slowSourceInitialVariance n) m :=
    slowSourceSigmaSq_le_terminal hn hs0 hi
  have hd0 : 0 < radiusQDelta n q (slowSourceInitialVariance n) :=
    radiusQDelta_pos hn hq hs0
  have hdle : radiusQDelta n q (slowSourceInitialVariance n) ≤
      radiusQDelta n q (slowSourceSigmaSq n (slowSourceInitialVariance n) i) :=
    radiusQDelta_mono_variance n q (slowSourceSigmaSq_mono_start hn hs0 i)
  have hP := slowActualPayload_nonneg (n := n) hn (m := m) (k := k) (q := q) (R := R) hepsP
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsigi : 0 ≤ slowSourceSigmaSq n (slowSourceInitialVariance n) i :=
    (slowSourceSigmaSq_pos hn hs0 i).le
  unfold slowActualStepsBound slowActualStepsEnvelope slowActualDeadlineExpression
  gcongr
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hsigi.trans hsigle))
    (Nat.cast_nonneg n)) hP

/-! ## The deliverable: the frontier's `hsteps` binder -/

/-- **Deliverable 3.**  Every active phase of the *actual* slow canonical schedule — the
one whose warmness argument is the compounding `slowWarmBudget`, and whose shares are the
literal score-aware families the frontier forces — obeys one explicit natural deadline
cap, namely `⌈slowActualStepsEnvelope …⌉₊ + 1`. -/
theorem slowCanonicalSteps_actual_le
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
      ⌈slowActualStepsEnvelope n m k q epsP R⌉₊ + 1 := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have heps2 : (0 : Real) < epsP / 2 := by linarith
  -- the actual phase share, and the floor below it
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
  -- the compounding warm budget is finite and at least one
  have hW := slowWarmBudget_ne_top (q := q) hn hs0 hK
    (scoreAwareRetries (m + 1) k (epsP / 2)
      (slowUniformSlack n m K) (slowUniformBoundSq n R)) i
  have hW1 := one_le_slowWarmBudget
    (scoreAwareRetries (m + 1) k (epsP / 2)
      (slowUniformSlack n m K) (slowUniformBoundSq n R))
    n q (slowSourceInitialVariance n) K i
  have hW0 : 0 < (slowWarmBudget slowReferenceWarm n q (slowSourceInitialVariance n) K
      (scoreAwareRetries (m + 1) k (epsP / 2)
        (slowUniformSlack n m K) (slowUniformBoundSq n R)) i).toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one hW1)) hW
  -- the retry cap
  have hL : ∀ j, scoreAwareRetries (m + 1) k (epsP / 2)
      (slowUniformSlack n m K) (slowUniformBoundSq n R) j ≤
      slowActualRetriesCap n m k epsP R :=
    fun j ↦ scoreAwareRetries_slowUniform_le hn heps2 hK hball hfin j
  -- the warm-budget logarithm, padded from phase `i` to phase `m`
  have hWlog : Real.log (slowWarmBudget slowReferenceWarm n q
      (slowSourceInitialVariance n) K
      (scoreAwareRetries (m + 1) k (epsP / 2)
        (slowUniformSlack n m K) (slowUniformBoundSq n R)) i).toReal ≤
      slowActualWlog n m k q epsP R := by
    refine (log_slowWarmBudget_toReal_le hn hq.le hs0 hK hL hi.le).trans ?_
    unfold slowActualWlog
    have hlogE : 0 ≤ Real.log ((slowWarmFactorEnvelope n q (slowSourceInitialVariance n) m
        (slowActualRetriesCap n m k epsP R)).toReal) :=
      Real.log_nonneg (one_le_slowWarmFactorEnvelope_toReal _ _ _ _ _)
    have him : (i : Real) ≤ (m : Real) := by exact_mod_cast hi.le
    nlinarith
  -- the two share logarithms
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
  exact slowCanonicalSteps_le_ceil_of_log_le hn hq hs0 hW hW0 heta0 hetaTop hWlog hElog
    hZlog (slowActualStepsBound_le_envelope hn hq hepsP hi.le)

/-! ## The cost side's real envelope -/

theorem slowActualStepsEnvelope_nonneg
    (hn : 1 ≤ n) {m k : Nat} {q epsP R : Real} (hepsP : 0 < epsP) :
    0 ≤ slowActualStepsEnvelope n m k q epsP R := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have hsigm : 0 ≤ slowSourceSigmaSq n (slowSourceInitialVariance n) m :=
    (slowSourceSigmaSq_pos hn hs0 m).le
  have hP := slowActualPayload_nonneg (n := n) hn (m := m) (k := k) (q := q) (R := R) hepsP
  unfold slowActualStepsEnvelope slowActualDeadlineExpression
  have hnum : 0 ≤ 4 * 640 ^ 2 * slowSourceSigmaSq n (slowSourceInitialVariance n) m *
      (n : Real) *
      ((Real.log 2 + slowActualWlog n m k q epsP R + slowActualElog n m k epsP R) +
        2 * slowActualZlog n m k epsP R) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hsigm) (Nat.cast_nonneg n)) hP
  have hden : 0 ≤ (radiusQDelta n q (slowSourceInitialVariance n) * Real.log 2) ^ 2 :=
    sq_nonneg _
  have := div_nonneg hnum hden
  linarith

/-- **Deliverable 4.**  The natural cap of `slowCanonicalSteps_actual_le` is bounded, as a
real, by the envelope plus `2`; this is the `Tenv` the cost assembly consumes. -/
theorem cast_slowActualStepsCap_le
    (n m k : Nat) (q epsP R : Real)
    (hE : 0 ≤ slowActualStepsEnvelope n m k q epsP R) :
    ((⌈slowActualStepsEnvelope n m k q epsP R⌉₊ + 1 : Nat) : Real) ≤
      slowActualStepsEnvelope n m k q epsP R + 2 :=
  cast_ceil_add_one_le _ hE

#print axioms slowUniformShareFloor_le_eighteenth
#print axioms radiusQDelta_mono_variance
#print axioms slowActualWlog_nonneg
#print axioms slowActualElog_nonneg
#print axioms slowActualZlog_nonneg
#print axioms slowActualPayload_nonneg
#print axioms slowActualStepsBound_le_envelope
#print axioms slowCanonicalSteps_actual_le
#print axioms slowActualStepsEnvelope_nonneg
#print axioms cast_slowActualStepsCap_le

end Ttc.CVSlowActualSteps
