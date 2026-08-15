import Ttc.Exec.CVRadiusQGenericReferenceCost
import Ttc.Exec.CVSlowFullBodySourceSchedule

/-! Summed retained-reference cost for the globally slow selected-radius schedule. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Ttc.CVSlowRadiusQReferenceCostSum

open MeasureTheory ProbabilityTheory Metric Set Finset
open Arlib Arlib.MarkovChains
open Ttc.CVAdaptiveRadiusQPrimitives
open Ttc.CVRadiusQGenericFallbackSchedule
open Ttc.CVRadiusQGenericReferenceCost
open Ttc.CVSlowFullBodySourceSchedule
open Ttc.CVConcreteAugmentedRetryCutoffBudget
open Ttc.CVHeterogeneousHistoryReference
open scoped ENNReal Classical BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- At the source start `1/(16n)`, every slow phase has radius at least one for every
`q ≥ 4`. -/
theorem one_le_q_mul_sqrt_slowSourceSigmaSq
    {n : Nat} (hn : 1 ≤ n) {q : Real} (hq : 4 ≤ q) (i : Nat) :
    1 ≤ q * Real.sqrt
      (slowSourceSigmaSq n (1 / (16 * (n : Real))) i) * Real.sqrt n := by
  have hn0 : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hs0 : 0 < (1 / (16 * (n : Real)) : Real) := by positivity
  have hgeom : (1 / (16 * (n : Real)) : Real) ≤
      slowSourceSigmaSq n (1 / (16 * (n : Real))) i := by
    unfold slowSourceSigmaSq Arlib.GaussianCooling.geomSchedule
    have hbase : (1 : Real) ≤ 1 + 1 / (n : Real) :=
      le_add_of_nonneg_right (by positivity)
    have hp : (1 : Real) ≤ (1 + 1 / (n : Real)) ^ i := one_le_pow₀ hbase
    nlinarith
  have hs := slowSourceSigmaSq_pos hn hs0 i
  have hscaled : 1 ≤ 16 *
      slowSourceSigmaSq n (1 / (16 * (n : Real))) i * (n : Real) := by
    have h := mul_le_mul_of_nonneg_right hgeom
      (show 0 ≤ 16 * (n : Real) by positivity)
    calc
      1 = (1 / (16 * (n : Real))) * (16 * (n : Real)) := by field_simp
      _ ≤ slowSourceSigmaSq n (1 / (16 * (n : Real))) i *
          (16 * (n : Real)) := h
      _ = 16 * slowSourceSigmaSq n (1 / (16 * (n : Real))) i * (n : Real) := by ring
  have hsqrtS := Real.sq_sqrt hs.le
  have hsqrtN := Real.sq_sqrt hn0.le
  have hsquare : (4 * Real.sqrt
      (slowSourceSigmaSq n (1 / (16 * (n : Real))) i) * Real.sqrt n) ^ 2 =
      16 * slowSourceSigmaSq n (1 / (16 * (n : Real))) i * (n : Real) := by
    rw [mul_pow, mul_pow, hsqrtS, hsqrtN]
    ring
  have hx0 : 0 ≤ 4 * Real.sqrt
      (slowSourceSigmaSq n (1 / (16 * (n : Real))) i) * Real.sqrt n := by
    positivity
  have hfour : 1 ≤ 4 * Real.sqrt
      (slowSourceSigmaSq n (1 / (16 * (n : Real))) i) * Real.sqrt n := by
    nlinarith [hsquare, sq_nonneg (4 * Real.sqrt
      (slowSourceSigmaSq n (1 / (16 * (n : Real))) i) * Real.sqrt n - 1)]
  exact hfour.trans (by gcongr)

/-- Exact finite sum of phase costs for a local graph reference whose phasewise
warmness is bounded by `2e`.  This is polynomial: the warm multiplier is a constant,
and all remaining growth is confined to the literal deadlines and retry counts. -/
theorem slowRadiusQ_referenceCost_sum_le
    (hn : 21 ≤ n) {q : Real} (hq : 4 ≤ q)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)]
    (rho : Nat → Measure (State n)) [∀ i, IsProbabilityMeasure (rho i)]
    (hwarm : ∀ i, IsWarm (ENNReal.ofReal (2 * Real.exp 1)) (rho i)
      (ellGaussianProb
        (radiusQBody q K (slowSourceSigmaSq n (1 / (16 * (n : Real))) i))
        (radiusQDelta n q (slowSourceSigmaSq n (1 / (16 * (n : Real))) i))
        (slowSourceSigmaSq n (1 / (16 * (n : Real))) i)))
    (m : Nat) :
    ∑ i ∈ range m, (∫⁻ x, heterogeneousStepMean
        (radiusQWarmFallbackCostedKernelOfSigma (by omega : 1 ≤ n)
          q (lt_of_lt_of_le (by norm_num) hq) K hK
          (slowSourceSigmaSq n (1 / (16 * (n : Real))))
          (slowSourceSigmaSq_pos (by omega) (by positivity))
          steps retries fallback i) x ∂rho i) ≤
      ∑ i ∈ range m, ENNReal.ofReal
        (retryReferenceMeanEnvelope (2 * Real.exp 1) (steps i) (retries i)) := by
  apply sum_le_sum
  intro i hi
  have hcost := radiusQGeneric_referenceCost_le_of_warm (by omega : 2 ≤ n)
    (lt_of_lt_of_le (by norm_num) hq) hK hKc hball
    (slowSourceSigmaSq n (1 / (16 * (n : Real))))
    (slowSourceSigmaSq_pos (by omega) (by positivity)) steps retries fallback
    (rho i) (M := ENNReal.ofReal (2 * Real.exp 1)) ENNReal.ofReal_ne_top i
    (one_le_q_mul_sqrt_slowSourceSigmaSq (by omega) hq i) (hwarm i)
  simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.exp 1)] using hcost

#print axioms one_le_q_mul_sqrt_slowSourceSigmaSq
#print axioms slowRadiusQ_referenceCost_sum_le

end Ttc.CVSlowRadiusQReferenceCostSum
