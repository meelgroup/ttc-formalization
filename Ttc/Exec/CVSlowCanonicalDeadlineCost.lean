import Ttc.Exec.CVSlowCanonicalShareBounds
import Ttc.Exec.CVSlowSourceCostEnvelope
import Ttc.Exec.CVGlobalLogarithmicRadius

/-!
Uniform retry/deadline accounting for the canonical uniformly slow source schedule.

Only active phases are bounded: after the declared terminal phase the retained schedule
has zero cost.  The deliberately conservative variance bound `2*N` keeps the resulting
formula elementary and explicit.
-/

set_option autoImplicit false

namespace Ttc.CVSlowCanonicalDeadlineCost

open Finset MeasureTheory
open Arlib.GaussianCooling
open Ttc.CVAdaptiveRadiusQPrimitives Ttc.CVGlobalLogarithmicRadius
open Ttc.CVSlowFullBodySourceSchedule Ttc.CVSlowGlobalRadiusTailBudget
open Ttc.CVSlowSourceReferenceCertificate Ttc.CVSlowSourceCostEnvelope
open Ttc.CVGaussianScoreAwareParameters Ttc.CVGaussianAdaptiveMixing
open Ttc.CVGaussianScoreAwareSharpScheduleBound
open Ttc.CVConcreteAugmentedRetryCutoffBudget
open Ttc.CVSlowCanonicalShareBounds
open scoped ENNReal BigOperators

/-- The logarithmic payload obtained by replacing every phase share by its global
canonical lower bound. -/
noncomputable def slowCanonicalDeadlinePayload
    (m k : Nat) (eps R s0 : Real) : Real :=
  Real.log ((2 * Real.exp 1) / slowCanonicalShareFloor m k eps R s0) +
    2 * Real.log (32 / slowCanonicalShareFloor m k eps R s0)

/-- Uniform geometric coefficient for every active phase. -/
noncomputable def slowCanonicalGeometryEnvelope
    (n m k : Nat) (eps N : Real) : Real :=
  (64 + 16 * Real.log (20 * slowRadiusTailCalls m k eps) + 8 * N) *
    (n : Real) ^ 3

/-- One literal natural deadline cap for every active phase. -/
noncomputable def slowCanonicalDeadlineCap
    (n m k : Nat) (eps R s0 N : Real) : Nat :=
  ⌈4 * 640 ^ 2 * slowCanonicalGeometryEnvelope n m k eps N *
      slowCanonicalDeadlinePayload m k eps R s0 / Real.log 2 ^ 2 + 1⌉₊ + 1

theorem slowSourceSigmaSq_le_terminal
    {n : Nat} (hn : 1 ≤ n) {s0 : Real} (hs0 : 0 < s0)
    {i j : Nat} (hij : i ≤ j) :
    slowSourceSigmaSq n s0 i ≤ slowSourceSigmaSq n s0 j := by
  unfold slowSourceSigmaSq
  exact (geomSchedule_strictMono hs0 (by positivity : 0 < 1 / (n : Real))).monotone hij

theorem slowSourceSigmaSq_active_le_two_target
    {n : Nat} (hn : 1 ≤ n) {N s0 : Real}
    (hN : 0 < N) (hs0 : 0 < s0) (hsN : s0 ≤ N)
    {i : Nat} (hi : i + 1 < slowSourcePhases n N s0) :
    slowSourceSigmaSq n s0 i ≤ 2 * N := by
  have him : i ≤ slowSourcePhases n N s0 := by omega
  have hmono := slowSourceSigmaSq_le_terminal hn hs0 him
  have hterminal := slowSourceSigmaSq_terminal_lt hn hN hs0 hsN
  have hnreal : (1 : Real) ≤ n := by exact_mod_cast hn
  have hinv : 1 / (n : Real) ≤ 1 := (div_le_one (by positivity)).2 hnreal
  have hover : N * (1 + 1 / (n : Real)) ≤ 2 * N := by
    nlinarith
  exact hmono.trans (hterminal.le.trans hover)

/-- Replacing the actual score-aware share by the canonical floor enlarges the exact
mixing logarithm. -/
theorem slowDeadlinePayload_le_canonical
    {m k : Nat} {eps R s0 share : Real}
    (hf0 : 0 < slowCanonicalShareFloor m k eps R s0)
    (hfs : slowCanonicalShareFloor m k eps R s0 ≤ share) :
    Real.log ((2 * Real.exp 1) / share) + 2 * Real.log (32 / share) ≤
      slowCanonicalDeadlinePayload m k eps R s0 := by
  have hs0 : 0 < share := hf0.trans_le hfs
  have hfirst : (2 * Real.exp 1) / share ≤
      (2 * Real.exp 1) / slowCanonicalShareFloor m k eps R s0 := by
    exact div_le_div_of_nonneg_left (by positivity) hf0 hfs
  have hsecond : 32 / share ≤
      32 / slowCanonicalShareFloor m k eps R s0 := by
    exact div_le_div_of_nonneg_left (by norm_num) hf0 hfs
  unfold slowCanonicalDeadlinePayload
  gcongr

theorem slowCanonicalDeadlinePayload_nonneg
    {m k : Nat} {eps R s0 : Real}
    (hf0 : 0 < slowCanonicalShareFloor m k eps R s0)
    (hf1 : slowCanonicalShareFloor m k eps R s0 < 1) :
    0 ≤ slowCanonicalDeadlinePayload m k eps R s0 := by
  have hfirst : 1 ≤ (2 * Real.exp 1) /
      slowCanonicalShareFloor m k eps R s0 := by
    rw [le_div_iff₀ hf0]
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    nlinarith
  have hsecond : 1 ≤ 32 / slowCanonicalShareFloor m k eps R s0 := by
    rw [le_div_iff₀ hf0]
    nlinarith
  unfold slowCanonicalDeadlinePayload
  exact add_nonneg (Real.log_nonneg hfirst)
    (mul_nonneg (by norm_num) (Real.log_nonneg hsecond))

/-- Every active slow source phase has the advertised explicit deadline. -/
theorem slowScoreAwareSteps_canonical_active_le
    {n m k chainLength : Nat} (hn : 1 ≤ n) {N eps R s0 : Real}
    (hN : 0 < N) (hs0 : 0 < s0) (hsN : s0 ≤ N)
    (hs0eq : s0 = slowSourceInitialVariance n)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    (hball : Metric.ball 0 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hm : m = slowSourcePhases n N s0)
    {i : Nat} (hi : i + 1 < m) :
    slowScoreAwareSteps n m k (slowGlobalRadiusQ n m k eps) eps
        (slowCanonicalSlack chainLength n s0 K)
        (slowCanonicalBoundSq n R s0) i 0 ≤
      slowCanonicalDeadlineCap n m k eps R s0 N := by
  let share := scoreAwareShare m k eps
    (slowCanonicalSlack chainLength n s0 K)
    (slowCanonicalBoundSq n R s0) i
  let floor := slowCanonicalShareFloor m k eps R s0
  let A := slowRadiusTailCalls m k eps
  let sigma := slowSourceSigmaSq n (slowSourceInitialVariance n) i
  have hf0 : 0 < floor := slowCanonicalShareFloor_pos
    (m := m) (k := k) (R := R) heps hs0
  have hf1 : floor < 1 := slowCanonicalShareFloor_lt_one heps heps1
  have hs0' : 0 < share := scoreAwareShare_pos (m := m) (k := k) heps
    (slowCanonicalSlack_pos (chainLength := chainLength) hn hs0 hball hfin)
    (slowCanonicalBoundSq_pos (R := R) hn hs0) i
  have hfs : floor ≤ share := slowCanonicalShareFloor_le_scoreAwareShare
    (m := m) (k := k) (chainLength := chainLength) (eps := eps) (R := R)
    hn hs0 hK hball hfin i
  have hs1 : share < 1 := scoreAwareShare_lt_one heps heps1 i
  have hA : 1 ≤ A := one_le_slowRadiusTailCalls m k eps
  have hsigma0 : 0 < sigma := slowSourceSigmaSq_pos hn
    (by unfold slowSourceInitialVariance; positivity) i
  have hsigmaN : sigma ≤ 2 * N := by
    dsimp only [sigma]
    rw [← hs0eq]
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
        slowCanonicalDeadlinePayload m k eps R s0 :=
    slowDeadlinePayload_le_canonical hf0 hfs
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
      (slowCanonicalSlack chainLength n s0 K)
      (slowCanonicalBoundSq n R s0) i).toReal = share := by
    simp [scoreAwareEta, share, hs0'.le]
  have hzeta : (scoreAwareZeta m k eps
      (slowCanonicalSlack chainLength n s0 K)
      (slowCanonicalBoundSq n R s0) i).toReal = share / 32 := by
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
          slowCanonicalDeadlinePayload m k eps R s0 / Real.log 2 ^ 2 + 1 := by
      gcongr

/-- One active canonical phase is bounded by the common retry/deadline envelope; an
inactive phase is exactly zero. -/
theorem slowPhaseCostBound_canonical_le
    {n m k chainLength : Nat} (hn : 1 ≤ n) {N eps R s0 : Real}
    (hN : 0 < N) (hs0 : 0 < s0) (hsN : s0 ≤ N)
    (hs0eq : s0 = slowSourceInitialVariance n)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    (hball : Metric.ball 0 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hm : m = slowSourcePhases n N s0) (i : Nat) :
    slowPhaseCostBound n m k (slowGlobalRadiusQ n m k eps) eps
        (slowCanonicalSlack chainLength n s0 K)
        (slowCanonicalBoundSq n R s0) i ≤
      ENNReal.ofReal
        (10 * (slowCanonicalRetriesCap m k eps R s0 : Real) *
          (slowCanonicalDeadlineCap n m k eps R s0 N : Real) *
          (2 * Real.exp 1)) := by
  unfold slowPhaseCostBound
  split_ifs with hi
  · apply ENNReal.ofReal_le_ofReal
    have hsteps := slowScoreAwareSteps_canonical_active_le
      (k := k) (R := R) (chainLength := chainLength)
      hn hN hs0 hsN hs0eq heps heps1
      hK hball hfin hm hi
    have hretries := scoreAwareRetries_slowCanonical_le
      (m := m) (k := k) (chainLength := chainLength) (eps := eps) (R := R)
      hn heps hs0 hK hball hfin i
    have hmean := retryReferenceMeanEnvelope_le_uniform
      (M := 2 * Real.exp 1)
      (steps := fun _ ↦ slowScoreAwareSteps n m k
        (slowGlobalRadiusQ n m k eps) eps
        (slowCanonicalSlack chainLength n s0 K)
        (slowCanonicalBoundSq n R s0) i 0)
      (L := scoreAwareRetries m k eps
        (slowCanonicalSlack chainLength n s0 K)
        (slowCanonicalBoundSq n R s0) i)
      (T := slowCanonicalDeadlineCap n m k eps R s0 N)
      (by positivity) (fun _ _ ↦ hsteps)
    calc
      retryReferenceMeanEnvelope (2 * Real.exp 1)
          (slowScoreAwareSteps n m k (slowGlobalRadiusQ n m k eps) eps
            (slowCanonicalSlack chainLength n s0 K)
            (slowCanonicalBoundSq n R s0) i)
          (scoreAwareRetries m k eps
            (slowCanonicalSlack chainLength n s0 K)
            (slowCanonicalBoundSq n R s0) i) =
        retryReferenceMeanEnvelope (2 * Real.exp 1)
          (fun _ ↦ slowScoreAwareSteps n m k
            (slowGlobalRadiusQ n m k eps) eps
            (slowCanonicalSlack chainLength n s0 K)
            (slowCanonicalBoundSq n R s0) i 0)
          (scoreAwareRetries m k eps
            (slowCanonicalSlack chainLength n s0 K)
            (slowCanonicalBoundSq n R s0) i) := by rfl
      _ ≤ 10 * (scoreAwareRetries m k eps
            (slowCanonicalSlack chainLength n s0 K)
            (slowCanonicalBoundSq n R s0) i : Real) *
          (slowCanonicalDeadlineCap n m k eps R s0 N : Real) *
          (2 * Real.exp 1) := hmean
      _ ≤ 10 * (slowCanonicalRetriesCap m k eps R s0 : Real) *
          (slowCanonicalDeadlineCap n m k eps R s0 N : Real) *
          (2 * Real.exp 1) := by
        have hcast : (scoreAwareRetries m k eps
            (slowCanonicalSlack chainLength n s0 K)
            (slowCanonicalBoundSq n R s0) i : Real) ≤
            slowCanonicalRetriesCap m k eps R s0 := by exact_mod_cast hretries
        gcongr
  · exact bot_le

/-- Closed aggregate retained-reference query bound for the canonical slow schedule. -/
theorem aggregate_slowPhaseCostBound_canonical_le
    {n m k chainLength : Nat} (hn : 1 ≤ n) {N eps R s0 : Real}
    (hN : 0 < N) (hs0 : 0 < s0) (hsN : s0 ≤ N)
    (hs0eq : s0 = slowSourceInitialVariance n)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    (hball : Metric.ball 0 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hm : m = slowSourcePhases n N s0) :
    (k : ENNReal) *
        (∑ i ∈ range m,
          slowPhaseCostBound n m k (slowGlobalRadiusQ n m k eps) eps
            (slowCanonicalSlack chainLength n s0 K)
            (slowCanonicalBoundSq n R s0) i) ≤
      (k : ENNReal) * (m : ENNReal) * ENNReal.ofReal
        (10 * (slowCanonicalRetriesCap m k eps R s0 : Real) *
          (slowCanonicalDeadlineCap n m k eps R s0 N : Real) *
          (2 * Real.exp 1)) := by
  have hphase := slowPhaseCostBound_canonical_le
    (k := k) (R := R) (chainLength := chainLength)
    hn hN hs0 hsN hs0eq heps heps1
    hK hball hfin hm
  calc
    (k : ENNReal) *
        (∑ i ∈ range m,
          slowPhaseCostBound n m k (slowGlobalRadiusQ n m k eps) eps
            (slowCanonicalSlack chainLength n s0 K)
            (slowCanonicalBoundSq n R s0) i) ≤
      (k : ENNReal) * (∑ _i ∈ range m, ENNReal.ofReal
        (10 * (slowCanonicalRetriesCap m k eps R s0 : Real) *
          (slowCanonicalDeadlineCap n m k eps R s0 N : Real) *
          (2 * Real.exp 1))) := by
            gcongr with i hi
            exact hphase i
    _ = (k : ENNReal) * (m : ENNReal) * ENNReal.ofReal
        (10 * (slowCanonicalRetriesCap m k eps R s0 : Real) *
          (slowCanonicalDeadlineCap n m k eps R s0 N : Real) *
          (2 * Real.exp 1)) := by simp [nsmul_eq_mul, mul_assoc]

#print axioms slowSourceSigmaSq_active_le_two_target
#print axioms slowDeadlinePayload_le_canonical
#print axioms slowScoreAwareSteps_canonical_active_le
#print axioms slowPhaseCostBound_canonical_le
#print axioms aggregate_slowPhaseCostBound_canonical_le

end Ttc.CVSlowCanonicalDeadlineCost
