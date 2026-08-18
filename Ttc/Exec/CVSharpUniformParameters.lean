import Ttc.Exec.CVSharpScoreTransport

/-!
# Score-aware shares, retry caps and deadline caps at the **sharp** slack/boundSq pair

`Ttc.CVSlowUniformShareBounds` builds the whole share/retry/deadline stack at the *loose*
pair selected by `Ttc.CVSlowCanonicalUniformParameters`:

* `slack = fun j ↦ phaseMomentSlackSeven _ σ K slowUniformC j / 2`;
* `boundSq = phaseScoreTransportBoundSqSeven R σ = exp (R^2/(2 σ_i))^2 * 15`.

`Ttc.CVSharpScoreTransport` sharpens the *bound* to
`phaseScoreTransportBoundSqSharp n R σ i = exp (R^2/(2 σ_i (n+1)))^2 * 15`, removing a full
factor `n` from the exponent, and `Ttc.CVSharpFactorSeven` shows that the price of the
sharp bound is that the **mixing-slack binder must be taken at `… / 6` instead of `… / 2`**
(forced: at the terminal index the sharp bound coincides with the loose one, and the crux
`sharpPhaseSup_sq_mul_le_three_mul` pays a factor `3`).

This file is the sharp analogue of `Ttc.CVSlowUniformShareBounds` at that `/6` pair.
Writing `r := chain (i+1) / chain i ≥ 1` and `x := R^2/(2 σ_i (n+1))`, the score-aware
share's exponential branch is

`slack / (3 boundSq) = ((7 - 2) r^2 / 6) / (3 * 15 * exp x ^ 2) = r^2 / (54 * exp x ^ 2)`,

and `σ_i ≥ s0 = 1/(16 n)` gives `2 σ_i (n+1) ≥ (n+1)/(8n) ≥ 1/8`, hence `x ≤ 8 R^2` with
**no `n`**.  So the right floor here is

`slowSharpFloor6 m k eps R = min (blockShare m k eps) (1 / (54 * exp (8 R^2)^2))`

— the `/6` slack costs exactly the `18 → 54` relative to
`Ttc.CVSharpScoreTransport.slowSharpShareFloor` (which is the `/2` statement) and relative
to `Ttc.CVSlowUniformShareBounds.slowUniformShareFloor`'s constant `18`.

The payoff is `slowSharpFloor6_ge_slowUniformShareFloor` and
`slowSharpRetriesCap_le_slowUniformRetriesCap`: the loose floor is
`1/(18 * exp (8 n R^2)^2) = 1/(18 * e^{16 n R^2})` and the sharp one is
`1/(54 * e^{16 R^2})`, so for `2 ≤ n` and `1 ≤ R` the removed factor `n` in the exponent
dominates the `18 → 54` and the sharp floor is genuinely larger — hence the sharp retry cap
is genuinely smaller.  Both hypotheses are needed and both are honest: at `n = 1` the two
exponents agree and `54 > 18` makes the comparison **false**, and for `R → 0` it is false at
every `n`.  Downstream `ball 0 1 ⊆ K ⊆ closedBall 0 R` forces `1 ≤ R` anyway.

Nothing here weakens or replaces the loose layer: `Ttc.CVSlowUniformShareBounds` is
untouched and remains available.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Ttc.CVSharpUniformParameters

open MeasureTheory Metric Set
open Arlib.GaussianCooling
open Ttc.CVAdaptive
open Ttc.CVSlowFullBodySourceSchedule Ttc.CVSlowSourceReferenceCertificate
open Ttc.CVGaussianFactorSevenAssembly
open Ttc.CVGaussianBlockRetryParameters Ttc.CVGaussianScoreAwareParameters
open Ttc.CVMinimalScoreAwareWarmLogArithmetic
open Ttc.CVSlowCanonicalShareBounds
open Ttc.CVSlowCanonicalUniformParameters
open Ttc.CVAdaptiveRadiusQPrimitives Ttc.CVGlobalLogarithmicRadius
open Ttc.CVSlowGlobalRadiusTailBudget Ttc.CVSlowSourceCostEnvelope
open Ttc.CVGaussianAdaptiveMixing Ttc.CVGaussianScoreAwareSharpScheduleBound
open Ttc.CVConcreteAugmentedRetryCutoffBudget
open Ttc.CVSlowCanonicalDeadlineCost
open Ttc.CVSlowCanonicalRuntimeComparison
open Ttc.CVSharpScoreTransport
open scoped ENNReal

variable {n : Nat}

/-! ## Step 1 — the sharp slack -/

/-- The **sixth** factor-seven phase moment slack at `C = slowUniformC = 2`.  This is the
binder shape `Ttc.CVSharpFactorSeven` forces once the score transport bound is sharpened;
compare `Ttc.CVSlowCanonicalUniformParameters.slowUniformSlack`, which is the same thing
divided by `2`. -/
noncomputable def slowSharpSlack (n m : Nat)
    (K : Set (EuclideanSpace Real (Fin n))) : Nat → Real :=
  fun j ↦ phaseMomentSlackSeven m
    (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
    Ttc.CVSlowCanonicalUniformParameters.slowUniformC j / 6

theorem slowSharpSlack_pos {n m : Nat} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace Real (Fin n))}
    (hball : ball (0 : EuclideanSpace Real (Fin n)) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (i : Nat) :
    0 < slowSharpSlack n m K i := by
  unfold slowSharpSlack
  refine div_pos ?_ (by norm_num)
  exact phaseMomentSlackSeven_pos
    (slowSourceSigmaSq_pos hn (slowSourceInitialVariance_pos hn))
    hball hfin slowUniformC_lt_seven i

/-! ## Step 2 — the sharp share floor at the `/6` slack -/

/-- One lower share valid simultaneously at every slow phase, at the **sharp** slack/boundSq
pair.  The exponential branch is `1/(54 * exp (8 R^2)^2)`: the constant `54` is the `/6`
slack's price over the `18` of the `/2` statements, and the exponent `8 R^2` is
dimension-free where the loose one is `8 n R^2`. -/
noncomputable def slowSharpFloor6 (m k : Nat) (eps R : Real) : Real :=
  min (blockShare m k eps) (1 / (54 * Real.exp (8 * R ^ 2) ^ 2))

theorem slowSharpFloor6_pos {m k : Nat} {eps R : Real} (heps : 0 < eps) :
    0 < slowSharpFloor6 m k eps R := by
  unfold slowSharpFloor6
  exact lt_min (blockShare_pos heps) (by positivity)

theorem slowSharpFloor6_lt_one {m k : Nat} {eps R : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    slowSharpFloor6 m k eps R < 1 :=
  (min_le_left _ _).trans_lt (blockShare_lt_one heps heps1)

theorem slowSharpFloor6_nonneg (m k : Nat) (eps R : Real) :
    0 ≤ slowSharpFloor6 m k eps R := by
  unfold slowSharpFloor6 blockShare Ttc.CVCorrected.correctedNu
  refine le_min ?_ (by positivity)
  positivity

/-! ## Step 3 — the crux: the sharp floor is under the sharp share -/

/-- **The crux.**  At the sharp slack/boundSq pair — mixing slack
`phaseMomentSlackSeven … / 6`, transport bound `slowSharpBoundSq n R` — the score-aware
share of every slow phase is bounded below by the single dimension-free floor
`min (blockShare m k eps) (1 / (54 * exp (8 R^2)^2))`.

The arithmetic: `slack i = (7 - 2) r^2 / 6 = (5/6) r^2` with `r ≥ 1`, and
`3 * boundSq i = 45 * exp x ^ 2` with `x = R^2/(2 σ_i (n+1)) ≤ 8 R^2`, so the second branch
of `scoreAwareShare` is `r^2 / (54 exp x ^ 2) ≥ 1 / (54 exp (8 R^2)^2)`. -/
theorem slowSharpFloor6_le_scoreAwareShare
    {n : Nat} (hn : 1 ≤ n) {m k chainLength : Nat} {eps R : Real}
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    (hball : ball (0 : EuclideanSpace Real (Fin n)) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (i : Nat) :
    slowSharpFloor6 m k eps R ≤
      scoreAwareShare m k eps (slowSharpSlack n chainLength K)
        (Ttc.CVSharpScoreTransport.slowSharpBoundSq n R) i := by
  have hn1 : (1 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  set s0 := slowSourceInitialVariance n with hs0def
  set sched := slowSourceSigmaSq n s0 with hscheddef
  set r := chain chainLength sched K (i + 1) / chain chainLength sched K i with hrdef
  set x := R ^ 2 / (2 * sched i * ((n : Real) + 1)) with hxdef
  have hsched : 0 < sched i := slowSourceSigmaSq_pos hn hs0 i
  have hratio : 1 ≤ r := by
    rw [hrdef, hscheddef]
    exact one_le_chain_ratio_of_sigmaSq_le_succ hK hfin hball
      (slowSourceSigmaSq_pos hn hs0) (slowSourceSigmaSq_mono_succ hn hs0 i)
  -- the sharp exponent is at most `8 R^2`, with no `n`
  have hexponent : x ≤ 8 * R ^ 2 := by
    have hlow : (1 : Real) / 8 ≤ 2 * sched i * ((n : Real) + 1) := by
      have hstart : s0 ≤ sched i := slowSourceSigmaSq_mono_start hn hs0 i
      have hs0eq : s0 = 1 / (16 * (n : Real)) := rfl
      have hn0 : (0 : Real) < (n : Real) := by linarith
      have h1 : 2 * s0 * ((n : Real) + 1) ≤ 2 * sched i * ((n : Real) + 1) := by
        nlinarith
      refine le_trans ?_ h1
      rw [hs0eq, div_le_iff₀ (by norm_num : (0 : Real) < 8)]
      rw [show 2 * (1 / (16 * (n : Real))) * ((n : Real) + 1) * 8
          = ((n : Real) + 1) / (n : Real) by field_simp; ring]
      rw [le_div_iff₀ hn0]
      linarith
    rw [hxdef, div_le_iff₀ (by linarith : (0 : Real) < 2 * sched i * ((n : Real) + 1))]
    nlinarith [sq_nonneg R]
  unfold slowSharpFloor6 scoreAwareShare
  refine le_min (min_le_left _ _) ((min_le_right _ _).trans ?_)
  unfold slowSharpSlack Ttc.CVSharpScoreTransport.slowSharpBoundSq
    Ttc.CVSharpScoreTransport.phaseScoreTransportBoundSqSharp
    Ttc.CVSlowCanonicalUniformParameters.slowUniformC phaseMomentSlackSeven
  change 1 / (54 * Real.exp (8 * R ^ 2) ^ 2) ≤
    ((7 - 2) * r ^ 2 / 6) / (3 * (Real.exp x ^ 2 * (1 + 2 * 7)))
  have he : Real.exp x ≤ Real.exp (8 * R ^ 2) := Real.exp_le_exp.2 hexponent
  have he2 : Real.exp x ^ 2 ≤ Real.exp (8 * R ^ 2) ^ 2 :=
    pow_le_pow_left₀ (Real.exp_pos x).le he 2
  have hr2 : 1 ≤ r ^ 2 := by nlinarith
  rw [show (7 - 2 : Real) * r ^ 2 / 6 = 5 * r ^ 2 / 6 by ring,
    show 3 * (Real.exp x ^ 2 * (1 + 2 * 7)) = 45 * Real.exp x ^ 2 by ring]
  rw [div_le_div_iff₀ (by positivity : (0 : Real) < 54 * Real.exp (8 * R ^ 2) ^ 2)
    (by positivity : (0 : Real) < 45 * Real.exp x ^ 2)]
  nlinarith [Real.exp_pos (8 * R ^ 2), Real.exp_pos x]

/-! ## Step 4 — the sharp retry cap -/

/-- Uniform logarithmic retry cap induced by the sharp share floor. -/
noncomputable def slowSharpRetriesCap (m k : Nat) (eps R : Real) : Nat :=
  16 * explicitDyadicTailIndex (slowSharpFloor6 m k eps R)

/-- Every literal retry count at the sharp pair is bounded by the single sharp retry cap. -/
theorem scoreAwareRetries_slowSharp_le
    {n : Nat} (hn : 1 ≤ n) {m k chainLength : Nat} {eps R : Real} (heps : 0 < eps)
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    (hball : ball (0 : EuclideanSpace Real (Fin n)) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (i : Nat) :
    scoreAwareRetries m k eps (slowSharpSlack n chainLength K)
        (Ttc.CVSharpScoreTransport.slowSharpBoundSq n R) i ≤
      slowSharpRetriesCap m k eps R := by
  have hfloor0 := slowSharpFloor6_pos (m := m) (k := k) (R := R) heps
  have hshare0 := scoreAwareShare_pos (m := m) (k := k) heps
    (slowSharpSlack_pos (m := chainLength) hn hball hfin)
    (fun j ↦ Ttc.CVSharpScoreTransport.slowSharpBoundSq_pos (n := n) (R := R) j) i
  have hfloor := slowSharpFloor6_le_scoreAwareShare
    (m := m) (k := k) (chainLength := chainLength) (eps := eps) (R := R)
    hn hK hball hfin i
  have hinv :
      1 / scoreAwareShare m k eps (slowSharpSlack n chainLength K)
          (Ttc.CVSharpScoreTransport.slowSharpBoundSq n R) i ≤
        1 / slowSharpFloor6 m k eps R :=
    one_div_le_one_div_of_le hfloor0 hfloor
  have hlog := (Real.logb_le_logb (by norm_num : (1 : Real) < 2)
    (by positivity) (by positivity)).2 hinv
  unfold scoreAwareRetries slowSharpRetriesCap explicitDyadicTailIndex
  exact Nat.mul_le_mul_left 16 (Nat.ceil_mono hlog)

/-! ## Step 5 — the sharp deadline cap -/

/-- The logarithmic payload obtained by replacing every phase share by the sharp
global lower bound. -/
noncomputable def slowSharpDeadlinePayload (m k : Nat) (eps R : Real) : Real :=
  Real.log ((2 * Real.exp 1) / slowSharpFloor6 m k eps R) +
    2 * Real.log (32 / slowSharpFloor6 m k eps R)

/-- One literal natural deadline cap for every active phase, at the sharp pair. -/
noncomputable def slowSharpDeadlineCap
    (n m k : Nat) (eps R N : Real) : Nat :=
  ⌈4 * 640 ^ 2 * slowCanonicalGeometryEnvelope n m k eps N *
      slowSharpDeadlinePayload m k eps R / Real.log 2 ^ 2 + 1⌉₊ + 1

/-- Replacing the actual score-aware share by the sharp floor enlarges the exact
mixing logarithm. -/
theorem slowDeadlinePayload_le_sharp
    {m k : Nat} {eps R share : Real}
    (hf0 : 0 < slowSharpFloor6 m k eps R)
    (hfs : slowSharpFloor6 m k eps R ≤ share) :
    Real.log ((2 * Real.exp 1) / share) + 2 * Real.log (32 / share) ≤
      slowSharpDeadlinePayload m k eps R := by
  have hs0 : 0 < share := hf0.trans_le hfs
  have hfirst : (2 * Real.exp 1) / share ≤
      (2 * Real.exp 1) / slowSharpFloor6 m k eps R :=
    div_le_div_of_nonneg_left (by positivity) hf0 hfs
  have hsecond : 32 / share ≤ 32 / slowSharpFloor6 m k eps R :=
    div_le_div_of_nonneg_left (by norm_num) hf0 hfs
  unfold slowSharpDeadlinePayload
  gcongr

theorem slowSharpDeadlinePayload_nonneg
    {m k : Nat} {eps R : Real}
    (hf0 : 0 < slowSharpFloor6 m k eps R)
    (hf1 : slowSharpFloor6 m k eps R < 1) :
    0 ≤ slowSharpDeadlinePayload m k eps R := by
  have hfirst : 1 ≤ (2 * Real.exp 1) / slowSharpFloor6 m k eps R := by
    rw [le_div_iff₀ hf0]
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    nlinarith
  have hsecond : 1 ≤ 32 / slowSharpFloor6 m k eps R := by
    rw [le_div_iff₀ hf0]
    nlinarith
  unfold slowSharpDeadlinePayload
  exact add_nonneg (Real.log_nonneg hfirst)
    (mul_nonneg (by norm_num) (Real.log_nonneg hsecond))

/-- Every active slow source phase has the advertised explicit deadline, at the
sharp slack/boundSq pair. -/
theorem slowScoreAwareSteps_sharp_active_le
    {n : Nat} (hn : 1 ≤ n) {m k chainLength : Nat} {N eps R s0 : Real}
    (hN : 0 < N) (hs0 : 0 < s0) (hsN : s0 ≤ N)
    (hs0eq : s0 = slowSourceInitialVariance n)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    (hball : Metric.ball 0 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hm : m = slowSourcePhases n N s0)
    {i : Nat} (hi : i + 1 < m) :
    slowScoreAwareSteps n m k (slowGlobalRadiusQ n m k eps) eps
        (slowSharpSlack n chainLength K)
        (Ttc.CVSharpScoreTransport.slowSharpBoundSq n R) i 0 ≤
      slowSharpDeadlineCap n m k eps R N := by
  subst hs0eq
  let share := scoreAwareShare m k eps (slowSharpSlack n chainLength K)
    (Ttc.CVSharpScoreTransport.slowSharpBoundSq n R) i
  let floor := slowSharpFloor6 m k eps R
  let A := slowRadiusTailCalls m k eps
  let sigma := slowSourceSigmaSq n (slowSourceInitialVariance n) i
  have hf0 : 0 < floor := slowSharpFloor6_pos (m := m) (k := k) (R := R) heps
  have hf1 : floor < 1 := slowSharpFloor6_lt_one heps heps1
  have hs0' : 0 < share := scoreAwareShare_pos (m := m) (k := k) heps
    (slowSharpSlack_pos (m := chainLength) hn hball hfin)
    (fun j ↦ Ttc.CVSharpScoreTransport.slowSharpBoundSq_pos (n := n) (R := R) j) i
  have hfs : floor ≤ share := slowSharpFloor6_le_scoreAwareShare
    (m := m) (k := k) (chainLength := chainLength) (eps := eps) (R := R)
    hn hK hball hfin i
  have hs1 : share < 1 := scoreAwareShare_lt_one heps heps1 i
  have hA : 1 ≤ A := one_le_slowRadiusTailCalls m k eps
  have hsigma0 : 0 < sigma := slowSourceSigmaSq_pos hn hs0 i
  have hsigmaN : sigma ≤ 2 * N := by
    dsimp only [sigma]
    apply slowSourceSigmaSq_active_le_two_target hn hN hs0 hsN
    simpa only [hm] using hi
  have hcoef : sigma * (n : Real) /
      radiusQDelta n (slowGlobalRadiusQ n m k eps) sigma ^ 2 ≤
      slowCanonicalGeometryEnvelope n m k eps N := by
    have hraw := sigmaSq_mul_n_div_globalDelta_sq_hot_le
      (N := 2 * N) hn hA hsigma0 hsigmaN
    change sigma * (n : Real) / globalLogarithmicDelta n A sigma ^ 2 ≤
      slowCanonicalGeometryEnvelope n m k eps N
    convert hraw using 1
    dsimp only [A, slowCanonicalGeometryEnvelope]
    ring
  have hpayload :
      Real.log ((2 * Real.exp 1) / share) + 2 * Real.log (32 / share) ≤
        slowSharpDeadlinePayload m k eps R :=
    slowDeadlinePayload_le_sharp hf0 hfs
  have hpayload0 : 0 ≤
      Real.log ((2 * Real.exp 1) / share) + 2 * Real.log (32 / share) := by
    have hfirst : 1 ≤ (2 * Real.exp 1) / share := by
      rw [le_div_iff₀ hs0']
      have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      nlinarith
    have hsecond : 1 ≤ 32 / share := by
      rw [le_div_iff₀ hs0']
      nlinarith
    exact add_nonneg (Real.log_nonneg hfirst)
      (mul_nonneg (by norm_num) (Real.log_nonneg hsecond))
  have hgeom0 : 0 ≤ slowCanonicalGeometryEnvelope n m k eps N :=
    (mul_nonneg (by
      have hlog : 0 ≤ Real.log (20 * A) := Real.log_nonneg (by nlinarith)
      positivity) (by positivity))
  apply adjustableSpeedyDeadline_le_ceil_of_expression_le
  unfold adjustableSpeedyDeadlineExpression
  have heta : (scoreAwareEta m k eps (slowSharpSlack n chainLength K)
      (Ttc.CVSharpScoreTransport.slowSharpBoundSq n R) i).toReal = share := by
    simp [scoreAwareEta, share, hs0'.le]
  have hzeta : (scoreAwareZeta m k eps (slowSharpSlack n chainLength K)
      (Ttc.CVSharpScoreTransport.slowSharpBoundSq n R) i).toReal =
        share / 32 := by
    rw [scoreAwareZeta, ENNReal.toReal_ofReal]
    exact div_nonneg hs0'.le (by norm_num)
  have hwarm : slowReferenceWarm.toReal = 2 * Real.exp 1 := by
    rw [slowReferenceWarm, ENNReal.toReal_ofReal]
    positivity
  rw [ENNReal.toReal_div, hwarm, heta, hzeta]
  rw [show 1 / (share / 32) = 32 / share by field_simp]
  change 4 * 640 ^ 2 * sigma * (n : Real) *
      (Real.log ((2 * Real.exp 1) / share) + 2 * Real.log (32 / share)) /
        (radiusQDelta n (slowGlobalRadiusQ n m k eps) sigma * Real.log 2) ^ 2 + 1 ≤ _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdelta := radiusQDelta_pos hn
    (lt_of_lt_of_le (by norm_num) (four_le_slowGlobalRadiusQ hn m k eps)) hsigma0
  have hden : 0 < radiusQDelta n (slowGlobalRadiusQ n m k eps) sigma ^ 2 *
      Real.log 2 ^ 2 := mul_pos (sq_pos_of_pos hdelta) (sq_pos_of_pos hlog2)
  rw [show (radiusQDelta n (slowGlobalRadiusQ n m k eps) sigma * Real.log 2) ^ 2 =
      radiusQDelta n (slowGlobalRadiusQ n m k eps) sigma ^ 2 * Real.log 2 ^ 2 by ring]
  calc
    4 * 640 ^ 2 * sigma * (n : Real) *
          (Real.log ((2 * Real.exp 1) / share) + 2 * Real.log (32 / share)) /
          (radiusQDelta n (slowGlobalRadiusQ n m k eps) sigma ^ 2 * Real.log 2 ^ 2) + 1 =
        4 * 640 ^ 2 *
          (sigma * (n : Real) / radiusQDelta n
            (slowGlobalRadiusQ n m k eps) sigma ^ 2) *
          (Real.log ((2 * Real.exp 1) / share) + 2 * Real.log (32 / share)) /
          Real.log 2 ^ 2 + 1 := by field_simp
    _ ≤ 4 * 640 ^ 2 * slowCanonicalGeometryEnvelope n m k eps N *
          slowSharpDeadlinePayload m k eps R / Real.log 2 ^ 2 + 1 := by
      gcongr

/-! ## Step 6 — real envelopes for the two literal natural caps -/

/-- Real upper envelope for the literal natural sharp retry cap. -/
noncomputable def slowSharpRetryRealEnvelope (m k : Nat) (eps R : Real) : Real :=
  16 * (Real.logb 2 (1 / slowSharpFloor6 m k eps R) + 1)

/-- Real upper envelope for the literal natural sharp mixing deadline. -/
noncomputable def slowSharpDeadlineRealEnvelope
    (n m k : Nat) (eps R N : Real) : Real :=
  4 * 640 ^ 2 * slowCanonicalGeometryEnvelope n m k eps N *
      slowSharpDeadlinePayload m k eps R / Real.log 2 ^ 2 + 3

theorem slowSharpRetriesCap_cast_le_realEnvelope
    {m k : Nat} {eps R : Real} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (slowSharpRetriesCap m k eps R : Real) ≤
      slowSharpRetryRealEnvelope m k eps R := by
  have hf0 := slowSharpFloor6_pos (m := m) (k := k) (R := R) heps
  have hf1 := slowSharpFloor6_lt_one (m := m) (k := k) (R := R) heps heps1
  have hindex := Ttc.CVAdaptive.explicitDyadicTailIndex_lt_logb_add_one hf0 hf1
  unfold slowSharpRetriesCap slowSharpRetryRealEnvelope
  push_cast
  linarith

theorem slowSharpDeadlineCap_cast_le_realEnvelope
    {n m k : Nat} {eps R N : Real}
    (hgeom0 : 0 ≤ slowCanonicalGeometryEnvelope n m k eps N)
    (hpayload0 : 0 ≤ slowSharpDeadlinePayload m k eps R) :
    (slowSharpDeadlineCap n m k eps R N : Real) ≤
      slowSharpDeadlineRealEnvelope n m k eps R N := by
  let x := 4 * 640 ^ 2 * slowCanonicalGeometryEnvelope n m k eps N *
      slowSharpDeadlinePayload m k eps R / Real.log 2 ^ 2 + 1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx0 : 0 ≤ x := by
    dsimp only [x]
    positivity
  have hceil := (Nat.ceil_lt_add_one hx0).le
  unfold slowSharpDeadlineCap slowSharpDeadlineRealEnvelope
  dsimp only [x] at hceil
  push_cast
  linarith

/-! ## Step 7 — the improvement, machine-checked

The loose floor's exponential branch is `1/(18 * exp (8 n R^2)^2) = 1/(18 * e^{16 n R^2})`;
the sharp one is `1/(54 * e^{16 R^2})`.  The comparison reduces to `3 ≤ e^{16 (n-1) R^2}`,
which needs both `2 ≤ n` (at `n = 1` the exponents agree and `54 > 18` makes it **false**)
and a lower bound on `R` (it is false as `R → 0` at every `n`).  We take `1 ≤ R`, which is
what `ball 0 1 ⊆ K ⊆ closedBall 0 R` forces downstream anyway; then
`16 (n-1) R^2 ≥ 16` and `e^{16} ≫ 3` with room to spare. -/

/-- **The improvement at the floor.**  For `2 ≤ n` and `1 ≤ R` the sharp share floor is
*larger* than the loose one: removing the factor `n` from the exponent beats the `18 → 54`
that the `/6` mixing slack costs. -/
theorem slowSharpFloor6_ge_slowUniformShareFloor
    {n : Nat} (hn : 2 ≤ n) (m k : Nat) (eps : Real) {R : Real} (hR : 1 ≤ R) :
    Ttc.CVSlowUniformShareBounds.slowUniformShareFloor m k eps R
        (slowSourceInitialVariance n) ≤ slowSharpFloor6 m k eps R := by
  have hn2 : (2 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hn0 : (0 : Real) < (n : Real) := by linarith
  have hRsq : (1 : Real) ≤ R ^ 2 := by nlinarith
  have hval : R ^ 2 / (2 * slowSourceInitialVariance n) = 8 * (n : Real) * R ^ 2 := by
    have hs0 : slowSourceInitialVariance n = 1 / (16 * (n : Real)) := rfl
    rw [hs0]
    field_simp
    ring
  have hsplit : Real.exp (8 * (n : Real) * R ^ 2) =
      Real.exp (8 * R ^ 2) * Real.exp (8 * ((n : Real) - 1) * R ^ 2) := by
    rw [← Real.exp_add]
    ring_nf
  have hbig : (3 : Real) ≤ Real.exp (8 * ((n : Real) - 1) * R ^ 2) ^ 2 := by
    have h8 : (8 : Real) ≤ 8 * ((n : Real) - 1) * R ^ 2 := by nlinarith
    have hle := Real.add_one_le_exp (8 * ((n : Real) - 1) * R ^ 2)
    nlinarith [Real.exp_pos (8 * ((n : Real) - 1) * R ^ 2)]
  unfold Ttc.CVSlowUniformShareBounds.slowUniformShareFloor slowSharpFloor6
  refine le_min (min_le_left _ _) ((min_le_right _ _).trans ?_)
  rw [hval]
  refine one_div_le_one_div_of_le (by positivity) ?_
  rw [hsplit, mul_pow]
  nlinarith [Real.exp_pos (8 * R ^ 2), sq_nonneg (Real.exp (8 * R ^ 2)),
    Real.exp_pos (8 * ((n : Real) - 1) * R ^ 2)]

/-- **The improvement at the retry cap** — the quantified runtime payoff.  A larger share
floor means fewer dyadic retry shells, so the sharp retry cap is *below* the loose one. -/
theorem slowSharpRetriesCap_le_slowUniformRetriesCap
    {n : Nat} (hn : 2 ≤ n) {m k : Nat} {eps R : Real} (heps : 0 < eps) (hR : 1 ≤ R) :
    slowSharpRetriesCap m k eps R ≤
      Ttc.CVSlowUniformShareBounds.slowUniformRetriesCap m k eps R
        (slowSourceInitialVariance n) := by
  have hfloorU0 := Ttc.CVSlowUniformShareBounds.slowUniformShareFloor_pos
    (m := m) (k := k) (R := R) (s0 := slowSourceInitialVariance n) heps
  have hfloor60 := slowSharpFloor6_pos (m := m) (k := k) (R := R) heps
  have hcmp := slowSharpFloor6_ge_slowUniformShareFloor (n := n) hn m k eps hR
  have hinv :
      1 / slowSharpFloor6 m k eps R ≤
        1 / Ttc.CVSlowUniformShareBounds.slowUniformShareFloor m k eps R
          (slowSourceInitialVariance n) :=
    one_div_le_one_div_of_le hfloorU0 hcmp
  have hlog := (Real.logb_le_logb (by norm_num : (1 : Real) < 2)
    (by positivity) (by positivity)).2 hinv
  unfold slowSharpRetriesCap Ttc.CVSlowUniformShareBounds.slowUniformRetriesCap
    explicitDyadicTailIndex
  exact Nat.mul_le_mul_left 16 (Nat.ceil_mono hlog)

#print axioms slowSharpSlack
#print axioms slowSharpSlack_pos
#print axioms slowSharpFloor6
#print axioms slowSharpFloor6_pos
#print axioms slowSharpFloor6_lt_one
#print axioms slowSharpFloor6_nonneg
#print axioms slowSharpFloor6_le_scoreAwareShare
#print axioms slowSharpRetriesCap
#print axioms scoreAwareRetries_slowSharp_le
#print axioms slowSharpDeadlinePayload
#print axioms slowSharpDeadlineCap
#print axioms slowDeadlinePayload_le_sharp
#print axioms slowSharpDeadlinePayload_nonneg
#print axioms slowScoreAwareSteps_sharp_active_le
#print axioms slowSharpRetryRealEnvelope
#print axioms slowSharpDeadlineRealEnvelope
#print axioms slowSharpRetriesCap_cast_le_realEnvelope
#print axioms slowSharpDeadlineCap_cast_le_realEnvelope
#print axioms slowSharpFloor6_ge_slowUniformShareFloor
#print axioms slowSharpRetriesCap_le_slowUniformRetriesCap

end Ttc.CVSharpUniformParameters
