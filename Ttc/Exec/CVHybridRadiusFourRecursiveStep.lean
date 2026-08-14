import Ttc.Exec.CVHybridRadiusFourFallbackSchedule
import Ttc.Exec.CVColdAcceptedWarm
import Ttc.Exec.CVColdResetSeedWarm
import Ttc.Exec.CVIndependentRefreshSeedLaws
import Ttc.Exec.CVGaussianColdHotRecursiveStep
import Ttc.Exec.CVAdaptiveRadiusFourAcceptedWarm

/-!
# Recursive warmth data for the all-radius-four hybrid schedule

Unlike the earlier cold/full-body split, this schedule keeps the phase body truncated
at radius `4 * sqrt(s_i) * sqrt(n)` throughout cooling.  Thus the local speedy-walk
geometry has the fixed parameter `q = 4`; the outer body is recovered only at the
terminal variance, using `fixedRadiusFourBody_eq_of_outer_radius`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Ttc.CVHybridRadiusFourRecursiveStep

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVHybridSchedule
open Ttc.CVSourceTruncatedFixedCost
open Ttc.CVAdaptiveRadiusFourCrossWarm
open Ttc.CVHybridRadiusFourFallbackSchedule
open Ttc.CVGaussianColdHotRecursiveStep
open Ttc.CVColdResetSeedWarm
open Ttc.CVIndependentRefreshSeedLaws
open Ttc.FiniteContinuingRetryRandomFallback
open Ttc.CVAdaptiveRadiusFourAcceptedWarm
open Ttc.CVGaussianWarmFallbackPhaseKernel
open Ttc.CVSequentialPhaseSampler
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- The speedy stationary seed law for the radius-four body at hybrid phase `i`. -/
noncomputable def hybridRadiusFourSeedTarget
    (n : Nat) (N s0 : Real) (K : Set (State n)) (i : Nat) : Measure (State n) :=
  ellGaussianProb (hybridRadiusFourBody n N s0 K i)
    (hybridRadiusFourDelta n N s0 i) (sigmaSq n N s0 i)

/-- A directly sampleable fallback pair.  Its seed is a small Gaussian ball at the
*next* variance, so the generic finite-volume warmness theorem applies to the next
radius-four target. -/
noncomputable def hybridRadiusFourFallback
    (n : Nat) (N s0 scoreScale : Real) (i : Nat) : Measure (ScoreSeed n) :=
  coldScoreSeedFallback (n := n) scoreScale (sigmaSq n N s0 (i + 1)) hotRefreshRadius

theorem isProbabilityMeasure_hybridRadiusFourFallback
    (hn : 1 ≤ n) {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    (scoreScale : Real) (i : Nat) :
    IsProbabilityMeasure (hybridRadiusFourFallback n N s0 scoreScale i) := by
  unfold hybridRadiusFourFallback
  exact isProbabilityMeasure_coldScoreSeedFallback _ _ _
    (sigmaSq_pos hn hN hs0 _) hotRefreshRadius_pos

/-- Fully specialized operational schedule, with its fallback probability instances
constructed from the input positivity assumptions. -/
noncomputable def sourceHybridRadiusFourWarmFallbackSchedule
    (hn : 1 ≤ n) {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    (K : Set (State n)) (hK : MeasurableSet K)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat) (scoreScale : Real) :
    Nat → Kernel (State n) (ScoreSeed n) := by
  letI : ∀ j, IsProbabilityMeasure (hybridRadiusFourFallback n N s0 scoreScale j) :=
    fun j ↦ isProbabilityMeasure_hybridRadiusFourFallback hn hN hs0 scoreScale j
  exact hybridRadiusFourWarmFallbackKernel hn K hK N s0 hN hs0 steps retries
    (hybridRadiusFourFallback n N s0 scoreScale)

instance sourceHybridRadiusFourWarmFallbackSchedule.isMarkovKernel
    (hn : 1 ≤ n) {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    (K : Set (State n)) (hK : MeasurableSet K)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat) (scoreScale : Real) (i : Nat) :
    IsMarkovKernel (sourceHybridRadiusFourWarmFallbackSchedule hn hN hs0 K hK
      steps retries scoreScale i) := by
  letI : ∀ j, IsProbabilityMeasure (hybridRadiusFourFallback n N s0 scoreScale j) :=
    fun j ↦ isProbabilityMeasure_hybridRadiusFourFallback hn hN hs0 scoreScale j
  unfold sourceHybridRadiusFourWarmFallbackSchedule
  infer_instance

/-- Exact finite fallback coefficient for the next truncated phase. -/
noncomputable def hybridRadiusFourFallbackFactor
    (n : Nat) (N s0 : Real) (K : Set (State n)) (i : Nat) : ENNReal :=
  gaussianBallWarmFactor (hybridRadiusFourBody n N s0 K (i + 1))
    (sigmaSq n N s0 (i + 1)) hotRefreshRadius

/-- Accepted first-hit coefficient.  The `max 1` form is convenient for the recursive
warm-budget API. -/
noncomputable def hybridRadiusFourAcceptedFactor
    (n : Nat) (N s0 : Real) (retries : Nat → Nat) (i : Nat) : ENNReal :=
  max 1 ((retries i : ENNReal) *
    (16 * adaptiveRadiusFourWarmFactor n (1 + phaseRate n N s0 i)))

theorem one_le_hybridRadiusFourAcceptedFactor
    (n : Nat) (N s0 : Real) (retries : Nat → Nat) (i : Nat) :
    1 ≤ hybridRadiusFourAcceptedFactor n N s0 retries i :=
  le_max_left _ _

theorem hybridRadiusFourAcceptedFactor_ne_top
    (n : Nat) (N s0 : Real) (retries : Nat → Nat) (i : Nat) :
    hybridRadiusFourAcceptedFactor n N s0 retries i ≠ ⊤ := by
  unfold hybridRadiusFourAcceptedFactor adaptiveRadiusFourWarmFactor
  apply max_ne_top
  · simp
  · exact ENNReal.mul_ne_top (by simp)
      (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)

theorem hybridRadiusFourFallbackFactor_ne_top
    {N s0 : Real} (hn : 1 ≤ n) (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hfin : volume K ≠ ⊤) (i : Nat) :
    hybridRadiusFourFallbackFactor n N s0 K i ≠ ⊤ := by
  unfold hybridRadiusFourFallbackFactor hybridRadiusFourBody
  exact gaussianBallWarmFactor_ne_top (measurableSet_fixedRadiusFourBody hK _)
    (volume_inter_closedBall_ne_top K _) (sigmaSq_pos hn hN hs0 (i + 1))
    hotRefreshRadius_pos

/-- The fallback seed marginal is warm for the next radius-four speedy target. -/
theorem isWarm_seed_hybridRadiusFourFallback_next
    (hn : 1 ≤ n) {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (i : Nat)
    (hradNext : 1 ≤ 4 * Real.sqrt (sigmaSq n N s0 (i + 1)) * Real.sqrt n)
    (scoreScale : Real) :
    IsWarm (hybridRadiusFourFallbackFactor n N s0 K i)
      (Measure.map Prod.snd (hybridRadiusFourFallback n N s0 scoreScale i))
      (hybridRadiusFourSeedTarget n N s0 K (i + 1)) := by
  let Knext := hybridRadiusFourBody n N s0 K (i + 1)
  have hKm : MeasurableSet Knext := measurableSet_fixedRadiusFourBody hK _
  have hKc' : Convex Real Knext := convex_fixedRadiusFourBody hKc _
  have hKb : ball (0 : State n) 1 ⊆ Knext :=
    unitBall_subset_inter_closedBall hball hradNext
  have hKtop : volume Knext ≠ ⊤ := volume_inter_closedBall_ne_top K _
  have hs := sigmaSq_pos hn hN hs0 (i + 1)
  rw [hybridRadiusFourFallback, map_snd_coldScoreSeedFallback]
  simpa only [hybridRadiusFourFallbackFactor, hybridRadiusFourSeedTarget,
    hybridRadiusFourBody, hybridRadiusFourDelta, Knext] using
    (isWarm_hotRefresh_ellGaussianProb hn hKm hKc' hKb hKtop hs
      (fixedRadiusFourDelta_pos hn hs) (fixedRadiusFourDelta_le_n (n := n)))

/-- Exact one-step recursive warmth theorem for the all-radius-four hybrid kernel.
Both the accepted and independently sampled fallback pieces are discharged here. -/
theorem isWarm_seed_hybridRadiusFourWarmFallbackKernel_step
    (hn : 1 ≤ n) {m : Nat} {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat) (scoreScale : Real)
    {i : Nat} (hi : i + 1 < m)
    (hrate0 : 0 ≤ phaseRate n N s0 i)
    (hrateHalf : phaseRate n N s0 i ≤ 1 / 2)
    (hrad : 1 ≤ 4 * Real.sqrt (sigmaSq n N s0 i) * Real.sqrt n)
    (hradNext : 1 ≤ 4 * Real.sqrt (sigmaSq n N s0 (i + 1)) * Real.sqrt n)
    (hradTwo : 1 ≤ 2 * Real.sqrt (sigmaSq n N s0 (i + 1)) * Real.sqrt n)
    (rho : Measure (State n)) [IsProbabilityMeasure rho] {M : ENNReal}
    (hwarm : IsWarm M rho (hybridRadiusFourSeedTarget n N s0 K i)) :
    IsWarm
      (hybridRadiusFourAcceptedFactor n N s0 retries i * M +
        hybridRadiusFourFallbackFactor n N s0 K i)
      (Measure.map Prod.snd
        (sampleFromKernel
          (sourceHybridRadiusFourWarmFallbackSchedule hn hN hs0 K hK
            steps retries scoreScale i) rho))
      (hybridRadiusFourSeedTarget n N s0 K (i + 1)) := by
  letI : ∀ j, IsProbabilityMeasure (hybridRadiusFourFallback n N s0 scoreScale j) :=
    fun j ↦ isProbabilityMeasure_hybridRadiusFourFallback hn hN hs0 scoreScale j
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hc : c ≠ 0 := by
    have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
    have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    dsimp only [c]
    linarith
  have hacc := isWarm_seed_acceptedOutputSubmeasure_radiusFour_hybrid
    hn hN hs0 hK hKc hball hfin hi hrate0 hrateHalf hrad hradTwo hwarm
      (steps i) (retries i)
  have hfb := isWarm_seed_hybridRadiusFourFallback_next hn hN hs0 hK hKc hball
    hfin i hradNext scoreScale
  have hstep := isWarm_seed_sampleFrom_gaussianWarmFallbackPhaseKernel
    (measurableSet_fixedRadiusFourBody hK _)
    (hybridRadiusFourDelta n N s0 i) (sigmaSq n N s0 i) c
    (fixedRadiusFourDelta_pos hn (sigmaSq_pos hn hN hs0 i)) hc
    (steps i) (retries i) (hybridRadiusFourFallback n N s0 scoreScale i) rho
    (hybridRadiusFourSeedTarget n N s0 K (i + 1)) hacc hfb
  apply hstep.mono
  apply add_le_add _ le_rfl
  calc
    (retries i : ENNReal) *
          ((16 * adaptiveRadiusFourWarmFactor n (1 + phaseRate n N s0 i)) * M) =
        ((retries i : ENNReal) *
          (16 * adaptiveRadiusFourWarmFactor n (1 + phaseRate n N s0 i))) * M := by
            ac_rfl
    _ ≤ hybridRadiusFourAcceptedFactor n N s0 retries i * M := by
      apply mul_le_mul_right'
      exact le_max_right _ _

#print axioms isWarm_seed_hybridRadiusFourWarmFallbackKernel_step

#print axioms isWarm_seed_hybridRadiusFourFallback_next

end Ttc.CVHybridRadiusFourRecursiveStep
