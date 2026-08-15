import Ttc.Exec.CVSlowSourceReferenceCertificate
import Ttc.Exec.CVGaussianSourceWeightedMoment
import Ttc.Exec.CVMinimalScoreAwareWarmLogArithmetic

/-!
Concrete score-aware shares for the uniformly slow schedule.

We use the fixed exact-moment comparison factor `C = 3`.  Monotonicity of the
geometric variance schedule makes every cooling-chain ratio at least one, while the
initial variance bounds every score-transport exponent.  This gives one explicit
positive share floor, hence one logarithmic retry bound for all phases.
-/

set_option autoImplicit false

namespace Ttc.CVSlowCanonicalShareBounds

open MeasureTheory Metric Set
open Arlib.GaussianCooling
open Ttc.CVAdaptive
open Ttc.CVSlowFullBodySourceSchedule Ttc.CVSlowSourceReferenceCertificate
open Ttc.CVGaussianSourceWeightedMoment
open Ttc.CVGaussianBlockRetryParameters Ttc.CVGaussianScoreAwareParameters
open Ttc.CVMinimalScoreAwareWarmLogArithmetic
open scoped ENNReal

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

noncomputable def slowCanonicalSlack
    (chainLength n : Nat) (s0 : Real) (K : Set (State n)) : Nat → Real :=
  relativePhaseSlack chainLength (slowSourceSigmaSq n s0) K (fun _ ↦ 3)

noncomputable def slowCanonicalBoundSq
    (n : Nat) (R s0 : Real) : Nat → Real :=
  relativePhaseBoundSq R (slowSourceSigmaSq n s0) (fun _ ↦ 3)

/-- One lower share valid simultaneously at every slow phase. -/
noncomputable def slowCanonicalShareFloor
    (m k : Nat) (eps R s0 : Real) : Real :=
  min (blockShare m k eps)
    (2 / (33 * Real.exp (R ^ 2 / (2 * s0)) ^ 2))

/-- Uniform logarithmic retry cap induced by the share floor. -/
noncomputable def slowCanonicalRetriesCap
    (m k : Nat) (eps R s0 : Real) : Nat :=
  16 * explicitDyadicTailIndex (slowCanonicalShareFloor m k eps R s0)

theorem slowSourceSigmaSq_mono_start
    {n : Nat} (hn : 1 ≤ n) {s0 : Real} (hs0 : 0 < s0) (i : Nat) :
    s0 ≤ slowSourceSigmaSq n s0 i := by
  unfold slowSourceSigmaSq geomSchedule
  have hbase : (1 : Real) ≤ 1 + 1 / (n : Real) := by
    exact le_add_of_nonneg_right (by positivity)
  have hp : (1 : Real) ≤ (1 + 1 / (n : Real)) ^ i := one_le_pow₀ hbase
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hs0.le

theorem slowSourceSigmaSq_mono_succ
    {n : Nat} (hn : 1 ≤ n) {s0 : Real} (hs0 : 0 < s0) (i : Nat) :
    slowSourceSigmaSq n s0 i ≤ slowSourceSigmaSq n s0 (i + 1) := by
  rw [slowSourceSigmaSq_succ]
  have hs := slowSourceSigmaSq_pos hn hs0 i
  have hinv : 0 ≤ 1 / (n : Real) := by positivity
  nlinarith

theorem slowCanonicalSlack_pos
    (hn : 1 ≤ n) {chainLength : Nat} {s0 : Real} (hs0 : 0 < s0)
    {K : Set (State n)} (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (i : Nat) :
    0 < slowCanonicalSlack chainLength n s0 K i := by
  unfold slowCanonicalSlack
  exact relativePhaseSlack_pos
    (slowSourceSigmaSq_pos hn hs0) hball hfin (by intro; norm_num) i

theorem slowCanonicalBoundSq_pos
    (hn : 1 ≤ n) {R s0 : Real} (hs0 : 0 < s0) (i : Nat) :
    0 < slowCanonicalBoundSq n R s0 i := by
  unfold slowCanonicalBoundSq
  exact relativePhaseBoundSq_pos (by intro; norm_num) i

/-- The global floor is below the actual score-aware share at every phase. -/
theorem slowCanonicalShareFloor_le_scoreAwareShare
    (hn : 1 ≤ n) {m k chainLength : Nat} {eps R s0 : Real}
    (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (i : Nat) :
    slowCanonicalShareFloor m k eps R s0 ≤
      scoreAwareShare m k eps
        (slowCanonicalSlack chainLength n s0 K)
        (slowCanonicalBoundSq n R s0) i := by
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
  unfold slowCanonicalShareFloor scoreAwareShare
  apply le_min
  · exact min_le_left _ _
  · refine (min_le_right _ _).trans ?_
    unfold slowCanonicalSlack slowCanonicalBoundSq
    change 2 / (33 * Real.exp A ^ 2) ≤
      ((3 - 1) * r ^ 2) /
        (3 * (Real.exp x ^ 2 * (1 + 2 * (2 * 3 - 1))))
    norm_num only
    have he : Real.exp x ≤ Real.exp A := Real.exp_le_exp.2 hexponent
    have he2 : Real.exp x ^ 2 ≤ Real.exp A ^ 2 :=
      pow_le_pow_left₀ (Real.exp_pos x).le he 2
    have hr2 : 1 ≤ r ^ 2 := by nlinarith
    rw [show 3 * (Real.exp x ^ 2 * 11) = 33 * Real.exp x ^ 2 by ring]
    rw [div_le_div_iff₀ (by positivity : 0 < 33 * Real.exp A ^ 2)
      (by positivity : 0 < 33 * Real.exp x ^ 2)]
    nlinarith

theorem slowCanonicalShareFloor_pos
    {m k : Nat} {eps R s0 : Real} (heps : 0 < eps) (hs0 : 0 < s0) :
    0 < slowCanonicalShareFloor m k eps R s0 := by
  unfold slowCanonicalShareFloor
  exact lt_min (blockShare_pos heps) (by positivity)

theorem slowCanonicalShareFloor_lt_one
    {m k : Nat} {eps R s0 : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    slowCanonicalShareFloor m k eps R s0 < 1 :=
  (min_le_left _ _).trans_lt (blockShare_lt_one heps heps1)

/-- Every literal retry count is bounded by the single retry cap. -/
theorem scoreAwareRetries_slowCanonical_le
    (hn : 1 ≤ n) {m k chainLength : Nat} {eps R s0 : Real}
    (heps : 0 < eps) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (i : Nat) :
    scoreAwareRetries m k eps
        (slowCanonicalSlack chainLength n s0 K)
        (slowCanonicalBoundSq n R s0) i ≤
      slowCanonicalRetriesCap m k eps R s0 := by
  have hfloor0 := slowCanonicalShareFloor_pos
    (m := m) (k := k) (R := R) heps hs0
  have hshare0 := scoreAwareShare_pos (m := m) (k := k) heps
    (slowCanonicalSlack_pos (chainLength := chainLength) hn hs0 hball hfin)
    (slowCanonicalBoundSq_pos (R := R) hn hs0) i
  have hfloor := slowCanonicalShareFloor_le_scoreAwareShare
    (m := m) (k := k) (chainLength := chainLength) (eps := eps) (R := R)
    hn hs0 hK hball hfin i
  have hinv :
      1 / scoreAwareShare m k eps
          (slowCanonicalSlack chainLength n s0 K)
          (slowCanonicalBoundSq n R s0) i ≤
        1 / slowCanonicalShareFloor m k eps R s0 :=
    one_div_le_one_div_of_le hfloor0 hfloor
  have hlog := (Real.logb_le_logb (by norm_num : (1 : Real) < 2)
    (by positivity) (by positivity)).2 hinv
  unfold scoreAwareRetries slowCanonicalRetriesCap explicitDyadicTailIndex
  exact Nat.mul_le_mul_left 16 (Nat.ceil_mono hlog)

#print axioms slowCanonicalShareFloor_le_scoreAwareShare
#print axioms scoreAwareRetries_slowCanonical_le

end Ttc.CVSlowCanonicalShareBounds
