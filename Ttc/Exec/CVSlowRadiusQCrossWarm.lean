import Ttc.Exec.CVSlowRadiusQReferenceCostSum
import Ttc.Exec.CVAdaptiveRadiusQCrossWarm

/-! Constant adjacent local-graph warmth for the globally slow schedule. -/

set_option autoImplicit false

namespace Ttc.CVSlowRadiusQCrossWarm

open MeasureTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVAdaptiveRadiusQPrimitives Ttc.CVAdaptiveRadiusQCrossWarm
open Ttc.CVAdaptiveRadiusQSmallRateWarm
open Ttc.CVSlowFullBodySourceSchedule Ttc.CVSlowRadiusQReferenceCostSum
open scoped ENNReal

variable {n m : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- The previous exact local graph seed is `2e`-warm for the next selected-radius
stationary target throughout the all-geometric schedule, including after the body has
already become all of `K`. -/
theorem isWarm_slowRadiusQ_localGraphSeed_succ_two_exp
    (hn : 1 ≤ n) {q : Real} (hq : 0 < q)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K)
    {s0 : Real} (hs0 : 0 < s0) {i : Nat} (hi : i + 1 < m)
    (hrad : 1 ≤ q * Real.sqrt (slowSourceSigmaSq n s0 i) * Real.sqrt n) :
    IsWarm (ENNReal.ofReal (2 * Real.exp 1))
      (Measure.map (fun x : State n ↦ (1 - 1 / (2 * (n : Real))) • x)
        (coolLaw m (slowSourceSigmaSq n s0)
          (radiusQBody q K (slowSourceSigmaSq n s0 i)) i))
      (ellGaussianProb
        (radiusQBody q K (slowSourceSigmaSq n s0 (i + 1)))
        (radiusQDelta n q (slowSourceSigmaSq n s0 (i + 1)))
        (slowSourceSigmaSq n s0 (i + 1))) := by
  have hraw := isWarm_standardScaledTruncated_ellGaussianProb_radiusQ_ratio
    (m := m) hn hq (slowSourceSigmaSq_pos hn hs0) hK hKc hball hi
    (show 1 ≤ 1 + 1 / (n : Real) by
      exact le_add_of_nonneg_right (by positivity))
    (by rw [slowSourceSigmaSq_succ]; ring)
    hrad
    (radiusQDelta_pos hn hq (slowSourceSigmaSq_pos hn hs0 (i + 1)))
    (radiusQDelta_le_n n q _)
  exact hraw.mono (adaptiveRadiusQWarmFactor_one_add_le_two_exp hn
    (by positivity) le_rfl)

/-- Source-start specialization with the radius premise discharged by `q ≥ 4`. -/
theorem isWarm_slowRadiusQ_sourceLocalGraphSeed_succ_two_exp
    (hn : 1 ≤ n) {q : Real} (hq : 4 ≤ q)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K)
    {i : Nat} (hi : i + 1 < m) :
    IsWarm (ENNReal.ofReal (2 * Real.exp 1))
      (Measure.map (fun x : State n ↦ (1 - 1 / (2 * (n : Real))) • x)
        (coolLaw m (slowSourceSigmaSq n (1 / (16 * (n : Real))))
          (radiusQBody q K
            (slowSourceSigmaSq n (1 / (16 * (n : Real))) i)) i))
      (ellGaussianProb
        (radiusQBody q K
          (slowSourceSigmaSq n (1 / (16 * (n : Real))) (i + 1)))
        (radiusQDelta n q
          (slowSourceSigmaSq n (1 / (16 * (n : Real))) (i + 1)))
        (slowSourceSigmaSq n (1 / (16 * (n : Real))) (i + 1))) := by
  exact isWarm_slowRadiusQ_localGraphSeed_succ_two_exp hn
    (lt_of_lt_of_le (by norm_num) hq) hK hKc hball (by positivity) hi
    (one_le_q_mul_sqrt_slowSourceSigmaSq hn hq i)

#print axioms isWarm_slowRadiusQ_localGraphSeed_succ_two_exp
#print axioms isWarm_slowRadiusQ_sourceLocalGraphSeed_succ_two_exp

end Ttc.CVSlowRadiusQCrossWarm
