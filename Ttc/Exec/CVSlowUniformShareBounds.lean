import Ttc.Exec.CVSlowCanonicalUniformParameters
import Ttc.Exec.CVSlowCanonicalRuntimeComparison

/-!
# Score-aware shares at the *uniform* slack/boundSq pair

`Ttc.CVSlowCanonicalShareBounds` builds a share floor, a retry cap and (via
`Ttc.CVSlowCanonicalDeadlineCost`) a deadline cap for the **relative** phase pair
`relativePhaseSlack _ _ _ (fun _ ↦ 3)` / `relativePhaseBoundSq _ _ (fun _ ↦ 3)`.
The frontier theorem's `hslackDef`/`hboundDef` binders however force the **factor-seven**
pair produced by `Ttc.CVSlowCanonicalUniformParameters`, namely

* `slack = fun j ↦ phaseMomentSlackSeven _ σ K slowUniformC j / 2` with `slowUniformC = 2`;
* `boundSq = phaseScoreTransportBoundSqSeven R σ`.

Writing `r := chain (i+1) / chain i` and `x := R^2 / (2 σ i)`, the two shares are

* relative pair: `slack / (3 boundSq) = (2 r^2) / (3 * 11 * exp x ^ 2) = 2 r^2 / (33 exp x ^ 2)`;
* uniform pair:  `slack / (3 boundSq) = ((5/2) r^2) / (3 * 15 * exp x ^ 2) = r^2 / (18 exp x ^ 2)`.

Since `2/33 > 1/18`, the canonical floor `slowCanonicalShareFloor` is **not** below the
uniform share, so the canonical retry/deadline caps do not apply to the parameters the
frontier forces.  This file rebuilds the whole stack at the uniform pair with the exact
constant `1/18`; every proof is the canonical one with the constants changed.
-/

set_option autoImplicit false

namespace Ttc.CVSlowUniformShareBounds

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
open scoped ENNReal

variable {n : Nat}

/-! ## The uniform share floor -/

/-- One lower share valid simultaneously at every slow phase, at the **uniform**
slack/boundSq pair.  The exponential branch is `1/18`, not the canonical `2/33`. -/
noncomputable def slowUniformShareFloor
    (m k : Nat) (eps R s0 : Real) : Real :=
  min (blockShare m k eps)
    (1 / (18 * Real.exp (R ^ 2 / (2 * s0)) ^ 2))

theorem slowUniformShareFloor_pos
    {m k : Nat} {eps R s0 : Real} (heps : 0 < eps) :
    0 < slowUniformShareFloor m k eps R s0 := by
  unfold slowUniformShareFloor
  exact lt_min (blockShare_pos heps) (by positivity)

theorem slowUniformShareFloor_lt_one
    {m k : Nat} {eps R s0 : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    slowUniformShareFloor m k eps R s0 < 1 :=
  (min_le_left _ _).trans_lt (blockShare_lt_one heps heps1)

theorem slowUniformShareFloor_nonneg (m k : Nat) (eps R s0 : Real) :
    0 ≤ slowUniformShareFloor m k eps R s0 := by
  unfold slowUniformShareFloor blockShare Ttc.CVCorrected.correctedNu
  refine le_min ?_ (by positivity)
  positivity

/-! ## The floor is below the uniform score-aware share -/

/-- The global uniform floor is below the actual score-aware share at every phase, for the
factor-seven slack/boundSq pair selected by `Ttc.CVSlowCanonicalUniformParameters`. -/
theorem slowUniformShareFloor_le_scoreAwareShare
    (hn : 1 ≤ n) {m k chainLength : Nat} {eps R : Real}
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    (hball : ball (0 : EuclideanSpace Real (Fin n)) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (i : Nat) :
    slowUniformShareFloor m k eps R (slowSourceInitialVariance n) ≤
      scoreAwareShare m k eps
        (Ttc.CVSlowCanonicalUniformParameters.slowUniformSlack n chainLength K)
        (Ttc.CVSlowCanonicalUniformParameters.slowUniformBoundSq n R) i := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  let s0 := slowSourceInitialVariance n
  let sched := slowSourceSigmaSq n s0
  let r := chain chainLength sched K (i + 1) / chain chainLength sched K i
  let x := R ^ 2 / (2 * sched i)
  let A := R ^ 2 / (2 * s0)
  have hsched : ∀ j, 0 < sched j := slowSourceSigmaSq_pos hn hs0
  have hratio : 1 ≤ r := by
    dsimp only [r, sched]
    exact one_le_chain_ratio_of_sigmaSq_le_succ hK hfin hball
      (slowSourceSigmaSq_pos hn hs0)
      (slowSourceSigmaSq_mono_succ hn hs0 i)
  have hexponent : x ≤ A := by
    dsimp only [x, A, sched]
    exact div_le_div_of_nonneg_left (sq_nonneg R) (by positivity)
      (mul_le_mul_of_nonneg_left (slowSourceSigmaSq_mono_start hn hs0 i)
        (by norm_num))
  unfold slowUniformShareFloor scoreAwareShare
  apply le_min
  · exact min_le_left _ _
  · refine (min_le_right _ _).trans ?_
    unfold Ttc.CVSlowCanonicalUniformParameters.slowUniformSlack
      Ttc.CVSlowCanonicalUniformParameters.slowUniformBoundSq
    change 1 / (18 * Real.exp A ^ 2) ≤
      ((7 - 2) * r ^ 2 / 2) /
        (3 * (Real.exp x ^ 2 * (1 + 2 * 7)))
    have he : Real.exp x ≤ Real.exp A := Real.exp_le_exp.2 hexponent
    have he2 : Real.exp x ^ 2 ≤ Real.exp A ^ 2 :=
      pow_le_pow_left₀ (Real.exp_pos x).le he 2
    have hr2 : 1 ≤ r ^ 2 := by nlinarith
    rw [show (7 - 2 : Real) * r ^ 2 / 2 = 5 * r ^ 2 / 2 by ring,
      show 3 * (Real.exp x ^ 2 * (1 + 2 * 7)) = 45 * Real.exp x ^ 2 by ring]
    rw [div_le_div_iff₀ (by positivity : (0 : Real) < 18 * Real.exp A ^ 2)
      (by positivity : (0 : Real) < 45 * Real.exp x ^ 2)]
    nlinarith [Real.exp_pos A, Real.exp_pos x]

/-! ## The uniform retry cap -/

/-- Uniform logarithmic retry cap induced by the uniform share floor. -/
noncomputable def slowUniformRetriesCap
    (m k : Nat) (eps R s0 : Real) : Nat :=
  16 * explicitDyadicTailIndex (slowUniformShareFloor m k eps R s0)

/-- Every literal retry count at the uniform pair is bounded by the single retry cap. -/
theorem scoreAwareRetries_slowUniform_le
    (hn : 1 ≤ n) {m k chainLength : Nat} {eps R : Real} (heps : 0 < eps)
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    (hball : ball (0 : EuclideanSpace Real (Fin n)) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (i : Nat) :
    scoreAwareRetries m k eps
        (Ttc.CVSlowCanonicalUniformParameters.slowUniformSlack n chainLength K)
        (Ttc.CVSlowCanonicalUniformParameters.slowUniformBoundSq n R) i ≤
      slowUniformRetriesCap m k eps R (slowSourceInitialVariance n) := by
  have hfloor0 := slowUniformShareFloor_pos
    (m := m) (k := k) (R := R) (s0 := slowSourceInitialVariance n) heps
  have hshare0 := scoreAwareShare_pos (m := m) (k := k) heps
    (slowUniformSlack_pos (m := chainLength) hn hball hfin)
    (fun j ↦ slowUniformBoundSq_pos (n := n) (R := R) j) i
  have hfloor := slowUniformShareFloor_le_scoreAwareShare
    (m := m) (k := k) (chainLength := chainLength) (eps := eps) (R := R)
    hn hK hball hfin i
  have hinv :
      1 / scoreAwareShare m k eps
          (Ttc.CVSlowCanonicalUniformParameters.slowUniformSlack n chainLength K)
          (Ttc.CVSlowCanonicalUniformParameters.slowUniformBoundSq n R) i ≤
        1 / slowUniformShareFloor m k eps R (slowSourceInitialVariance n) :=
    one_div_le_one_div_of_le hfloor0 hfloor
  have hlog := (Real.logb_le_logb (by norm_num : (1 : Real) < 2)
    (by positivity) (by positivity)).2 hinv
  unfold scoreAwareRetries slowUniformRetriesCap explicitDyadicTailIndex
  exact Nat.mul_le_mul_left 16 (Nat.ceil_mono hlog)

/-! ## The uniform deadline cap -/

/-- The logarithmic payload obtained by replacing every phase share by the uniform
global lower bound. -/
noncomputable def slowUniformDeadlinePayload
    (m k : Nat) (eps R s0 : Real) : Real :=
  Real.log ((2 * Real.exp 1) / slowUniformShareFloor m k eps R s0) +
    2 * Real.log (32 / slowUniformShareFloor m k eps R s0)

/-- One literal natural deadline cap for every active phase, at the uniform pair. -/
noncomputable def slowUniformDeadlineCap
    (n m k : Nat) (eps R s0 N : Real) : Nat :=
  ⌈4 * 640 ^ 2 * slowCanonicalGeometryEnvelope n m k eps N *
      slowUniformDeadlinePayload m k eps R s0 / Real.log 2 ^ 2 + 1⌉₊ + 1

/-- Replacing the actual score-aware share by the uniform floor enlarges the exact
mixing logarithm. -/
theorem slowDeadlinePayload_le_uniform
    {m k : Nat} {eps R s0 share : Real}
    (hf0 : 0 < slowUniformShareFloor m k eps R s0)
    (hfs : slowUniformShareFloor m k eps R s0 ≤ share) :
    Real.log ((2 * Real.exp 1) / share) + 2 * Real.log (32 / share) ≤
      slowUniformDeadlinePayload m k eps R s0 := by
  have hs0 : 0 < share := hf0.trans_le hfs
  have hfirst : (2 * Real.exp 1) / share ≤
      (2 * Real.exp 1) / slowUniformShareFloor m k eps R s0 := by
    exact div_le_div_of_nonneg_left (by positivity) hf0 hfs
  have hsecond : 32 / share ≤
      32 / slowUniformShareFloor m k eps R s0 := by
    exact div_le_div_of_nonneg_left (by norm_num) hf0 hfs
  unfold slowUniformDeadlinePayload
  gcongr

theorem slowUniformDeadlinePayload_nonneg
    {m k : Nat} {eps R s0 : Real}
    (hf0 : 0 < slowUniformShareFloor m k eps R s0)
    (hf1 : slowUniformShareFloor m k eps R s0 < 1) :
    0 ≤ slowUniformDeadlinePayload m k eps R s0 := by
  have hfirst : 1 ≤ (2 * Real.exp 1) /
      slowUniformShareFloor m k eps R s0 := by
    rw [le_div_iff₀ hf0]
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    nlinarith
  have hsecond : 1 ≤ 32 / slowUniformShareFloor m k eps R s0 := by
    rw [le_div_iff₀ hf0]
    nlinarith
  unfold slowUniformDeadlinePayload
  exact add_nonneg (Real.log_nonneg hfirst)
    (mul_nonneg (by norm_num) (Real.log_nonneg hsecond))

/-- Every active slow source phase has the advertised explicit deadline, at the
uniform slack/boundSq pair. -/
theorem slowScoreAwareSteps_uniform_active_le
    (hn : 1 ≤ n) {m k chainLength : Nat} {N eps R s0 : Real}
    (hN : 0 < N) (hs0 : 0 < s0) (hsN : s0 ≤ N)
    (hs0eq : s0 = slowSourceInitialVariance n)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    (hball : Metric.ball 0 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hm : m = slowSourcePhases n N s0)
    {i : Nat} (hi : i + 1 < m) :
    slowScoreAwareSteps n m k (slowGlobalRadiusQ n m k eps) eps
        (Ttc.CVSlowCanonicalUniformParameters.slowUniformSlack n chainLength K)
        (Ttc.CVSlowCanonicalUniformParameters.slowUniformBoundSq n R) i 0 ≤
      slowUniformDeadlineCap n m k eps R s0 N := by
  subst hs0eq
  let share := scoreAwareShare m k eps
    (Ttc.CVSlowCanonicalUniformParameters.slowUniformSlack n chainLength K)
    (Ttc.CVSlowCanonicalUniformParameters.slowUniformBoundSq n R) i
  let floor := slowUniformShareFloor m k eps R (slowSourceInitialVariance n)
  let A := slowRadiusTailCalls m k eps
  let sigma := slowSourceSigmaSq n (slowSourceInitialVariance n) i
  have hf0 : 0 < floor := slowUniformShareFloor_pos
    (m := m) (k := k) (R := R) heps
  have hf1 : floor < 1 := slowUniformShareFloor_lt_one heps heps1
  have hs0' : 0 < share := scoreAwareShare_pos (m := m) (k := k) heps
    (slowUniformSlack_pos (m := chainLength) hn hball hfin)
    (fun j ↦ slowUniformBoundSq_pos (n := n) (R := R) j) i
  have hfs : floor ≤ share := slowUniformShareFloor_le_scoreAwareShare
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
    convert hraw using 1 <;> dsimp only [A, slowCanonicalGeometryEnvelope] <;> ring
  have hpayload :
      Real.log ((2 * Real.exp 1) / share) + 2 * Real.log (32 / share) ≤
        slowUniformDeadlinePayload m k eps R (slowSourceInitialVariance n) :=
    slowDeadlinePayload_le_uniform hf0 hfs
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
  have heta : (scoreAwareEta m k eps
      (Ttc.CVSlowCanonicalUniformParameters.slowUniformSlack n chainLength K)
      (Ttc.CVSlowCanonicalUniformParameters.slowUniformBoundSq n R) i).toReal = share := by
    simp [scoreAwareEta, share, hs0'.le]
  have hzeta : (scoreAwareZeta m k eps
      (Ttc.CVSlowCanonicalUniformParameters.slowUniformSlack n chainLength K)
      (Ttc.CVSlowCanonicalUniformParameters.slowUniformBoundSq n R) i).toReal =
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
          slowUniformDeadlinePayload m k eps R (slowSourceInitialVariance n) /
          Real.log 2 ^ 2 + 1 := by
      gcongr

/-! ## Real envelopes for the two literal natural caps -/

/-- Real upper envelope for the literal natural uniform retry cap. -/
noncomputable def slowUniformRetryRealEnvelope
    (m k : Nat) (eps R s0 : Real) : Real :=
  16 * (Real.logb 2 (1 / slowUniformShareFloor m k eps R s0) + 1)

/-- Real upper envelope for the literal natural uniform mixing deadline. -/
noncomputable def slowUniformDeadlineRealEnvelope
    (n m k : Nat) (eps R s0 N : Real) : Real :=
  4 * 640 ^ 2 * slowCanonicalGeometryEnvelope n m k eps N *
      slowUniformDeadlinePayload m k eps R s0 / Real.log 2 ^ 2 + 3

theorem slowUniformRetriesCap_cast_le_realEnvelope
    {m k : Nat} {eps R s0 : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (slowUniformRetriesCap m k eps R s0 : Real) ≤
      slowUniformRetryRealEnvelope m k eps R s0 := by
  have hf0 := slowUniformShareFloor_pos
    (m := m) (k := k) (R := R) (s0 := s0) heps
  have hf1 := slowUniformShareFloor_lt_one
    (m := m) (k := k) (R := R) (s0 := s0) heps heps1
  have hindex := Ttc.CVAdaptive.explicitDyadicTailIndex_lt_logb_add_one hf0 hf1
  unfold slowUniformRetriesCap slowUniformRetryRealEnvelope
  push_cast
  linarith

theorem slowUniformDeadlineCap_cast_le_realEnvelope
    {n m k : Nat} {eps R s0 N : Real}
    (hgeom0 : 0 ≤ slowCanonicalGeometryEnvelope n m k eps N)
    (hpayload0 : 0 ≤ slowUniformDeadlinePayload m k eps R s0) :
    (slowUniformDeadlineCap n m k eps R s0 N : Real) ≤
      slowUniformDeadlineRealEnvelope n m k eps R s0 N := by
  let x := 4 * 640 ^ 2 * slowCanonicalGeometryEnvelope n m k eps N *
      slowUniformDeadlinePayload m k eps R s0 / Real.log 2 ^ 2 + 1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx0 : 0 ≤ x := by
    dsimp only [x]
    positivity
  have hceil := (Nat.ceil_lt_add_one hx0).le
  unfold slowUniformDeadlineCap slowUniformDeadlineRealEnvelope
  dsimp only [x] at hceil
  push_cast
  linarith

#print axioms slowUniformShareFloor_pos
#print axioms slowUniformShareFloor_lt_one
#print axioms slowUniformShareFloor_nonneg
#print axioms slowUniformShareFloor_le_scoreAwareShare
#print axioms scoreAwareRetries_slowUniform_le
#print axioms slowDeadlinePayload_le_uniform
#print axioms slowUniformDeadlinePayload_nonneg
#print axioms slowScoreAwareSteps_uniform_active_le
#print axioms slowUniformRetriesCap_cast_le_realEnvelope
#print axioms slowUniformDeadlineCap_cast_le_realEnvelope

end Ttc.CVSlowUniformShareBounds
