import Ttc.Exec.CVHybridRadiusQFallbackSchedule
import Ttc.Exec.CVAdaptiveRadiusQCrossWarm
import Ttc.Exec.CVAdaptiveRadiusQAcceptedWarm
import Ttc.Exec.CVIndependentRefreshSeedLaws
import Ttc.Exec.CVGaussianColdHotRecursiveStep

/-! Recursive-warm data for the globally selected radius-`q` hybrid schedule. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Ttc.CVHybridRadiusQRecursiveStep

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVHybridSchedule Ttc.CVAdaptiveRadiusQPrimitives
open Ttc.CVAdaptiveRadiusQCrossWarm
open Ttc.CVAdaptiveRadiusQAcceptedWarm
open Ttc.CVHybridRadiusQFallbackSchedule
open Ttc.CVIndependentRefreshSeedLaws
open Ttc.FiniteContinuingRetryRandomFallback
open Ttc.CVGaussianWarmFallbackPhaseKernel
open Ttc.CVSequentialPhaseSampler
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

noncomputable def hybridRadiusQSeedTarget
    (n : Nat) (q N s0 : Real) (K : Set (State n)) (i : Nat) : Measure (State n) :=
  ellGaussianProb (radiusQBody q K (sigmaSq n N s0 i))
    (radiusQDelta n q (sigmaSq n N s0 i)) (sigmaSq n N s0 i)

noncomputable def hybridRadiusQFallback
    (n : Nat) (N s0 scoreScale : Real) (i : Nat) : Measure (ScoreSeed n) :=
  coldScoreSeedFallback (n := n) scoreScale (sigmaSq n N s0 (i + 1)) hotRefreshRadius

theorem isProbabilityMeasure_hybridRadiusQFallback
    (hn : 1 ≤ n) {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    (scoreScale : Real) (i : Nat) :
    IsProbabilityMeasure (hybridRadiusQFallback n N s0 scoreScale i) := by
  unfold hybridRadiusQFallback
  exact isProbabilityMeasure_coldScoreSeedFallback _ _ _
    (sigmaSq_pos hn hN hs0 _) hotRefreshRadius_pos

noncomputable def sourceHybridRadiusQWarmFallbackSchedule
    (hn : 1 ≤ n) (q : Real) (hq : 0 < q)
    {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    (K : Set (State n)) (hK : MeasurableSet K)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat) (scoreScale : Real) :
    Nat → Kernel (State n) (ScoreSeed n) := by
  letI : ∀ j, IsProbabilityMeasure (hybridRadiusQFallback n N s0 scoreScale j) :=
    fun j ↦ isProbabilityMeasure_hybridRadiusQFallback hn hN hs0 scoreScale j
  exact hybridRadiusQWarmFallbackKernel hn q hq K hK N s0 hN hs0 steps retries
    (hybridRadiusQFallback n N s0 scoreScale)

instance sourceHybridRadiusQWarmFallbackSchedule.isMarkovKernel
    (hn : 1 ≤ n) (q : Real) (hq : 0 < q)
    {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    (K : Set (State n)) (hK : MeasurableSet K)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat) (scoreScale : Real) (i : Nat) :
    IsMarkovKernel (sourceHybridRadiusQWarmFallbackSchedule hn q hq hN hs0 K hK
      steps retries scoreScale i) := by
  letI : ∀ j, IsProbabilityMeasure (hybridRadiusQFallback n N s0 scoreScale j) :=
    fun j ↦ isProbabilityMeasure_hybridRadiusQFallback hn hN hs0 scoreScale j
  unfold sourceHybridRadiusQWarmFallbackSchedule
  infer_instance

/-- Costed companion of the specialized selected-radius schedule. -/
noncomputable def sourceHybridRadiusQWarmFallbackCostedSchedule
    (hn : 1 ≤ n) (q : Real) (hq : 0 < q)
    {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    (K : Set (State n)) (hK : MeasurableSet K)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat) (scoreScale : Real) :
    Nat → Kernel (State n) (ENNReal × ScoreSeed n) := by
  letI : ∀ j, IsProbabilityMeasure (hybridRadiusQFallback n N s0 scoreScale j) :=
    fun j ↦ isProbabilityMeasure_hybridRadiusQFallback hn hN hs0 scoreScale j
  exact hybridRadiusQWarmFallbackCostedKernel hn q hq K hK N s0 hN hs0
    steps retries (hybridRadiusQFallback n N s0 scoreScale)

instance sourceHybridRadiusQWarmFallbackCostedSchedule.isMarkovKernel
    (hn : 1 ≤ n) (q : Real) (hq : 0 < q)
    {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    (K : Set (State n)) (hK : MeasurableSet K)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat) (scoreScale : Real) (i : Nat) :
    IsMarkovKernel (sourceHybridRadiusQWarmFallbackCostedSchedule hn q hq hN hs0 K hK
      steps retries scoreScale i) := by
  letI : ∀ j, IsProbabilityMeasure (hybridRadiusQFallback n N s0 scoreScale j) :=
    fun j ↦ isProbabilityMeasure_hybridRadiusQFallback hn hN hs0 scoreScale j
  unfold sourceHybridRadiusQWarmFallbackCostedSchedule
  infer_instance

theorem map_snd_sourceHybridRadiusQWarmFallbackCostedSchedule
    (hn : 1 ≤ n) (q : Real) (hq : 0 < q)
    {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    (K : Set (State n)) (hK : MeasurableSet K)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat) (scoreScale : Real)
    (i : Nat) (x : State n) :
    Measure.map Prod.snd
        (sourceHybridRadiusQWarmFallbackCostedSchedule hn q hq hN hs0 K hK
          steps retries scoreScale i x) =
      sourceHybridRadiusQWarmFallbackSchedule hn q hq hN hs0 K hK
        steps retries scoreScale i x := by
  letI : ∀ j, IsProbabilityMeasure (hybridRadiusQFallback n N s0 scoreScale j) :=
    fun j ↦ isProbabilityMeasure_hybridRadiusQFallback hn hN hs0 scoreScale j
  exact map_snd_hybridRadiusQWarmFallbackCostedKernel hn q hq K hK N s0 hN hs0
    steps retries (hybridRadiusQFallback n N s0 scoreScale) i x

noncomputable def hybridRadiusQFallbackFactor
    (n : Nat) (q N s0 : Real) (K : Set (State n)) (i : Nat) : ENNReal :=
  gaussianBallWarmFactor (radiusQBody q K (sigmaSq n N s0 (i + 1)))
    (sigmaSq n N s0 (i + 1)) hotRefreshRadius

noncomputable def hybridRadiusQAcceptedFactor
    (n : Nat) (N s0 : Real) (retries : Nat → Nat) (i : Nat) : ENNReal :=
  max 1 ((retries i : ENNReal) *
    (16 * adaptiveRadiusQWarmFactor n (1 + phaseRate n N s0 i)))

theorem one_le_hybridRadiusQAcceptedFactor
    (n : Nat) (N s0 : Real) (retries : Nat → Nat) (i : Nat) :
    1 ≤ hybridRadiusQAcceptedFactor n N s0 retries i := le_max_left _ _

theorem hybridRadiusQAcceptedFactor_ne_top
    (n : Nat) (N s0 : Real) (retries : Nat → Nat) (i : Nat) :
    hybridRadiusQAcceptedFactor n N s0 retries i ≠ ⊤ := by
  unfold hybridRadiusQAcceptedFactor adaptiveRadiusQWarmFactor
  apply max_ne_top
  · simp
  · exact ENNReal.mul_ne_top (by simp)
      (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)

theorem hybridRadiusQFallbackFactor_ne_top
    {q N s0 : Real} (hn : 1 ≤ n) (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hfin : volume K ≠ ⊤) (i : Nat) :
    hybridRadiusQFallbackFactor n q N s0 K i ≠ ⊤ := by
  unfold hybridRadiusQFallbackFactor radiusQBody
  exact gaussianBallWarmFactor_ne_top (hK.inter measurableSet_closedBall)
    (volume_inter_closedBall_ne_top K _) (sigmaSq_pos hn hN hs0 (i + 1))
    hotRefreshRadius_pos

theorem isWarm_seed_hybridRadiusQFallback_next
    (hn : 1 ≤ n) {q N s0 : Real} (hq : 0 < q) (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (i : Nat)
    (hradNext : 1 ≤ q * Real.sqrt (sigmaSq n N s0 (i + 1)) * Real.sqrt n)
    (scoreScale : Real) :
    IsWarm (hybridRadiusQFallbackFactor n q N s0 K i)
      (Measure.map Prod.snd (hybridRadiusQFallback n N s0 scoreScale i))
      (hybridRadiusQSeedTarget n q N s0 K (i + 1)) := by
  let Knext := radiusQBody q K (sigmaSq n N s0 (i + 1))
  have hKm : MeasurableSet Knext := measurableSet_radiusQBody hK
  have hKc' : Convex Real Knext := convex_radiusQBody hKc
  have hKb : ball (0 : State n) 1 ⊆ Knext :=
    unitBall_subset_inter_closedBall hball hradNext
  have hKtop : volume Knext ≠ ⊤ := by
    dsimp only [Knext, radiusQBody]
    exact volume_inter_closedBall_ne_top K _
  have hs := sigmaSq_pos hn hN hs0 (i + 1)
  rw [hybridRadiusQFallback, map_snd_coldScoreSeedFallback]
  simpa only [hybridRadiusQFallbackFactor, hybridRadiusQSeedTarget, Knext] using
    (isWarm_hotRefresh_ellGaussianProb hn hKm hKc' hKb hKtop hs
      (radiusQDelta_pos hn hq hs) (radiusQDelta_le_n n q _))

/-- Exact actual-seed recurrence step for the selected global radius. -/
theorem isWarm_seed_hybridRadiusQWarmFallbackKernel_step
    (hn : 1 ≤ n) {m : Nat} {q N s0 : Real} (hq : 0 < q)
    (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat) (scoreScale : Real)
    {i : Nat} (hi : i + 1 < m)
    (hrate0 : 0 ≤ phaseRate n N s0 i)
    (hrad : 1 ≤ q * Real.sqrt (sigmaSq n N s0 i) * Real.sqrt n)
    (hradNext : 1 ≤ q * Real.sqrt (sigmaSq n N s0 (i + 1)) * Real.sqrt n)
    (rho : Measure (State n)) [IsProbabilityMeasure rho] {M : ENNReal}
    (hwarm : IsWarm M rho (hybridRadiusQSeedTarget n q N s0 K i)) :
    IsWarm
      (hybridRadiusQAcceptedFactor n N s0 retries i * M +
        hybridRadiusQFallbackFactor n q N s0 K i)
      (Measure.map Prod.snd
        (sampleFromKernel
          (sourceHybridRadiusQWarmFallbackSchedule hn q hq hN hs0 K hK
            steps retries scoreScale i) rho))
      (hybridRadiusQSeedTarget n q N s0 K (i + 1)) := by
  letI : ∀ j, IsProbabilityMeasure (hybridRadiusQFallback n N s0 scoreScale j) :=
    fun j ↦ isProbabilityMeasure_hybridRadiusQFallback hn hN hs0 scoreScale j
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hc : c ≠ 0 := by
    have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
    have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    dsimp only [c]
    linarith
  have hacc := isWarm_seed_acceptedOutputSubmeasure_radiusQ_hybrid
    hn hq hN hs0 hK hKc hball hfin hi hrate0 hrad hwarm
      (steps i) (retries i)
  have hfb := isWarm_seed_hybridRadiusQFallback_next hn hq hN hs0 hK hKc hball
    hfin i hradNext scoreScale
  have hstep := isWarm_seed_sampleFrom_gaussianWarmFallbackPhaseKernel
    (measurableSet_radiusQBody hK)
    (radiusQDelta n q (sigmaSq n N s0 i)) (sigmaSq n N s0 i) c
    (radiusQDelta_pos hn hq (sigmaSq_pos hn hN hs0 i)) hc
    (steps i) (retries i) (hybridRadiusQFallback n N s0 scoreScale i) rho
    (hybridRadiusQSeedTarget n q N s0 K (i + 1)) hacc hfb
  apply hstep.mono
  apply add_le_add _ le_rfl
  calc
    (retries i : ENNReal) *
          ((16 * adaptiveRadiusQWarmFactor n (1 + phaseRate n N s0 i)) * M) =
        ((retries i : ENNReal) *
          (16 * adaptiveRadiusQWarmFactor n (1 + phaseRate n N s0 i))) * M := by
            ac_rfl
    _ ≤ hybridRadiusQAcceptedFactor n N s0 retries i * M := by
      apply mul_le_mul_right'
      exact le_max_right _ _

#print axioms isWarm_seed_hybridRadiusQWarmFallbackKernel_step

#print axioms isWarm_seed_hybridRadiusQFallback_next

end Ttc.CVHybridRadiusQRecursiveStep
