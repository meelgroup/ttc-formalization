import Ttc.Exec.CVSlowRadiusQReferencePhaseTV
import Ttc.Exec.CVSlowRadiusQCrossWarm
import Ttc.Exec.CVAdaptiveRadiusQAcceptedWarm
import Ttc.Exec.CVRecursiveWarmOperational
import Ttc.Exec.CVSlowRadiusQOperationalPair

/-! Recursive actual-path operation for the uniformly slow selected-radius schedule. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Ttc.CVSlowRadiusQRecursiveOperational

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVCorrected Ttc.CVSequentialPhaseSampler
open Ttc.CVSeedProjectedDependence Ttc.CVScoreSeedPhaseKernel
open Ttc.CVRecursiveWarmOperational Ttc.CVWarmBudgetRecurrence
open Ttc.CVGaussianWarmFallbackCappedOperational Ttc.CVIndependentStreamDependence
open Ttc.CVAdaptiveRadiusQPrimitives Ttc.CVAdaptiveRadiusQAcceptedWarm
open Ttc.CVSlowFullBodySourceSchedule Ttc.CVSlowRadiusQFallbackSchedule
open Ttc.CVSlowRadiusQReferencePhaseTV Ttc.CVSlowRadiusQCrossWarm
open Ttc.CVIndependentRefreshSeedLaws
open Ttc.FiniteContinuingRetryRandomFallback
open Ttc.CVGaussianWarmFallbackPhaseKernel
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

noncomputable def slowAcceptedFactor
    (retries : Nat → Nat) (i : Nat) : ENNReal :=
  max 1 ((retries i : ENNReal) * (16 * ENNReal.ofReal (2 * Real.exp 1)))

noncomputable def slowFallbackFactor
    (n : Nat) (q s0 : Real) (K : Set (State n)) (i : Nat) : ENNReal :=
  gaussianBallWarmFactor (radiusQBody q K (slowSourceSigmaSq n s0 (i + 1)))
    (slowSourceSigmaSq n s0 (i + 1)) hotRefreshRadius

/-- The executable slow kernel with its sampleable fallback instance installed. -/
noncomputable def slowWarmFallbackSchedule
    (hn : 1 ≤ n) (q : Real) (hq : 0 < q) {s0 : Real} (hs0 : 0 < s0)
    (K : Set (State n)) (hK : MeasurableSet K)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat) (scoreScale : Real) :
    Nat → Kernel (State n) (ScoreSeed n) := by
  letI : ∀ j, IsProbabilityMeasure (slowRadiusQFallback n s0 scoreScale j) :=
    fun j ↦ isProbabilityMeasure_slowRadiusQFallback hn hs0 scoreScale j
  exact radiusQWarmFallbackKernelOfSigma hn q hq K hK
    (slowSourceSigmaSq n s0) (slowSourceSigmaSq_pos hn hs0)
    steps retries (slowRadiusQFallback n s0 scoreScale)

noncomputable def slowWarmFallbackCostedSchedule
    (hn : 1 ≤ n) (q : Real) (hq : 0 < q) {s0 : Real} (hs0 : 0 < s0)
    (K : Set (State n)) (hK : MeasurableSet K)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat) (scoreScale : Real) :
    Nat → Kernel (State n) (ENNReal × ScoreSeed n) := by
  letI : ∀ j, IsProbabilityMeasure (slowRadiusQFallback n s0 scoreScale j) :=
    fun j ↦ isProbabilityMeasure_slowRadiusQFallback hn hs0 scoreScale j
  exact radiusQWarmFallbackCostedKernelOfSigma hn q hq K hK
    (slowSourceSigmaSq n s0) (slowSourceSigmaSq_pos hn hs0)
    steps retries (slowRadiusQFallback n s0 scoreScale)

instance slowWarmFallbackSchedule.isMarkovKernel
    (hn : 1 ≤ n) (q : Real) (hq : 0 < q) {s0 : Real} (hs0 : 0 < s0)
    (K : Set (State n)) (hK : MeasurableSet K)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat) (scoreScale : Real) (i : Nat) :
    IsMarkovKernel (slowWarmFallbackSchedule hn q hq hs0 K hK
      steps retries scoreScale i) := by
  unfold slowWarmFallbackSchedule
  infer_instance

instance slowWarmFallbackCostedSchedule.isMarkovKernel
    (hn : 1 ≤ n) (q : Real) (hq : 0 < q) {s0 : Real} (hs0 : 0 < s0)
    (K : Set (State n)) (hK : MeasurableSet K)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat) (scoreScale : Real) (i : Nat) :
    IsMarkovKernel (slowWarmFallbackCostedSchedule hn q hq hs0 K hK
      steps retries scoreScale i) := by
  unfold slowWarmFallbackCostedSchedule
  infer_instance

theorem map_snd_slowWarmFallbackCostedSchedule
    (hn : 1 ≤ n) (q : Real) (hq : 0 < q) {s0 : Real} (hs0 : 0 < s0)
    (K : Set (State n)) (hK : MeasurableSet K)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat) (scoreScale : Real)
    (i : Nat) (x : State n) :
    Measure.map Prod.snd
      (slowWarmFallbackCostedSchedule hn q hq hs0 K hK
        steps retries scoreScale i x) =
      slowWarmFallbackSchedule hn q hq hs0 K hK steps retries scoreScale i x := by
  letI : ∀ j, IsProbabilityMeasure (slowRadiusQFallback n s0 scoreScale j) :=
    fun j ↦ isProbabilityMeasure_slowRadiusQFallback hn hs0 scoreScale j
  unfold slowWarmFallbackCostedSchedule slowWarmFallbackSchedule
  exact map_snd_radiusQWarmFallbackCostedKernelOfSigma hn q hq K hK
    (slowSourceSigmaSq n s0) (slowSourceSigmaSq_pos hn hs0)
    steps retries (slowRadiusQFallback n s0 scoreScale) i x

theorem one_le_slowAcceptedFactor (retries : Nat → Nat) (i : Nat) :
    1 ≤ slowAcceptedFactor retries i := le_max_left _ _

theorem slowFallbackFactor_ne_top
    (hn : 1 ≤ n) {q s0 : Real} (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (i : Nat) :
    slowFallbackFactor n q s0 K i ≠ ⊤ := by
  unfold slowFallbackFactor radiusQBody
  exact gaussianBallWarmFactor_ne_top (hK.inter measurableSet_closedBall)
    (volume_inter_closedBall_ne_top K _)
    (slowSourceSigmaSq_pos hn hs0 (i + 1)) hotRefreshRadius_pos

theorem isWarm_seed_slowFallback_next
    (hn : 1 ≤ n) {q s0 : Real} (hq : 0 < q) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (i : Nat)
    (hradNext : 1 ≤ q * Real.sqrt (slowSourceSigmaSq n s0 (i + 1)) * Real.sqrt n)
    (scoreScale : Real) :
    IsWarm (slowFallbackFactor n q s0 K i)
      (Measure.map Prod.snd (slowRadiusQFallback n s0 scoreScale i))
      (slowRadiusQSeedTarget n q s0 K (i + 1)) := by
  let Knext := radiusQBody q K (slowSourceSigmaSq n s0 (i + 1))
  have hKm : MeasurableSet Knext := measurableSet_radiusQBody hK
  have hKc' : Convex Real Knext := convex_radiusQBody hKc
  have hKb : ball (0 : State n) 1 ⊆ Knext :=
    unitBall_subset_inter_closedBall hball (by simpa only [Knext, radiusQBody] using hradNext)
  have hKtop : volume Knext ≠ ⊤ := by
    dsimp only [Knext, radiusQBody]
    exact volume_inter_closedBall_ne_top K _
  have hs := slowSourceSigmaSq_pos hn hs0 (i + 1)
  rw [slowRadiusQFallback, map_snd_coldScoreSeedFallback]
  simpa only [slowFallbackFactor, slowRadiusQSeedTarget, Knext] using
    (isWarm_hotRefresh_ellGaussianProb hn hKm hKc' hKb hKtop hs
      (radiusQDelta_pos hn hq hs) (radiusQDelta_le_n n q _))

/-- One exact recursive-warm transition for the slow schedule. -/
theorem isWarm_seed_slowRadiusQWarmFallbackKernel_step
    (hn : 1 ≤ n) {m : Nat} {q s0 : Real} (hq : 0 < q) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat) (scoreScale : Real)
    {i : Nat} (hi : i + 1 < m)
    (hrad : 1 ≤ q * Real.sqrt (slowSourceSigmaSq n s0 i) * Real.sqrt n)
    (hradNext : 1 ≤ q * Real.sqrt (slowSourceSigmaSq n s0 (i + 1)) * Real.sqrt n)
    (rho : Measure (State n)) [IsProbabilityMeasure rho] {M : ENNReal}
    (hwarm : IsWarm M rho (slowRadiusQSeedTarget n q s0 K i)) :
    IsWarm (slowAcceptedFactor retries i * M + slowFallbackFactor n q s0 K i)
      (Measure.map Prod.snd
        (sampleFromKernel
          (slowWarmFallbackSchedule hn q hq hs0 K hK steps retries scoreScale i) rho))
      (slowRadiusQSeedTarget n q s0 K (i + 1)) := by
  letI : ∀ j, IsProbabilityMeasure (slowRadiusQFallback n s0 scoreScale j) :=
    fun j ↦ isProbabilityMeasure_slowRadiusQFallback hn hs0 scoreScale j
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hc : c ≠ 0 := by
    have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
    have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    dsimp only [c]
    linarith
  have hcross := isWarm_slowRadiusQ_localGraphSeed_succ_two_exp
    (m := m) hn hq hK hKc hball hs0 hi hrad
  have hacc := isWarm_seed_acceptedOutputSubmeasure_radiusQ_of_cross
    hn hq (slowSourceSigmaSq_pos hn hs0) hK hKc hball hfin hi hrad
    (slowRadiusQSeedTarget n q s0 K (i + 1)) hcross hwarm
    (steps i) (retries i)
  have hfb := isWarm_seed_slowFallback_next hn hq hs0 hK hKc hball i
    hradNext scoreScale
  have hstep := isWarm_seed_sampleFrom_gaussianWarmFallbackPhaseKernel
    (measurableSet_radiusQBody hK)
    (radiusQDelta n q (slowSourceSigmaSq n s0 i)) (slowSourceSigmaSq n s0 i) c
    (radiusQDelta_pos hn hq (slowSourceSigmaSq_pos hn hs0 i)) hc
    (steps i) (retries i) (slowRadiusQFallback n s0 scoreScale i) rho
    (slowRadiusQSeedTarget n q s0 K (i + 1)) hacc hfb
  apply hstep.mono
  apply add_le_add _ le_rfl
  calc
    (retries i : ENNReal) *
        ((16 * ENNReal.ofReal (2 * Real.exp 1)) * M) =
      ((retries i : ENNReal) * (16 * ENNReal.ofReal (2 * Real.exp 1))) * M := by
        ac_rfl
    _ ≤ slowAcceptedFactor retries i * M := by
      apply mul_le_mul_right'
      exact le_max_right _ _

/-- Generic recursive operational package for the slow schedule. -/
noncomputable def seedProjectedOperational_slowRadiusQ_recursive
    (hn : 1 ≤ n) (m : Nat) {q s0 : Real} (hq : 0 < q) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hrad : ∀ i, i < m →
      1 ≤ q * Real.sqrt (slowSourceSigmaSq n s0 i) * Real.sqrt n)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat) (scoreScale : Real)
    (tail : Nat → Measure (ScoreSeed n)) [∀ i, IsProbabilityMeasure (tail i)]
    (mu0 : Measure (ScoreSeed n)) [IsProbabilityMeasure mu0]
    (V : Nat → (Nat → ScoreSeed n) → Real) (eta : Real)
    (tau : Nat → Measure (ScoreSeed n)) [∀ i, IsProbabilityMeasure (tau i)]
    (initialWarm : ENNReal) (hinitialOne : 1 ≤ initialWarm)
    (hstart : IsWarm initialWarm (Measure.map Prod.snd mu0)
      (slowRadiusQSeedTarget n q s0 K 0))
    (htailSeed : ∀ i, Measure.map Prod.snd (tail i) = slowRadiusQSeedTarget n q s0 K i)
    (mixError : Nat → ENNReal)
    (hactiveMixTop : ∀ i, i + 1 < m → mixError i ≠ ⊤)
    (hactiveMix : ∀ i, i + 1 < m → ∀ rho : Measure (State n),
      IsWarm (2 * recursiveWarmBudget initialWarm (slowAcceptedFactor retries)
          (slowFallbackFactor n q s0 K) i) rho (slowRadiusQSeedTarget n q s0 K i) →
      IsProbabilityMeasure rho →
      TVLe (sampleFromKernel
        (slowWarmFallbackSchedule hn q hq hs0 K hK steps retries scoreScale i) rho)
        (tau i) (mixError i))
    (u : (i : Nat) → (Finset.Iic i → ScoreSeed n) → Real)
    (v : Nat → State n → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i, accuracyU
      (inhomogeneousPathMeasure (stateScheduleFromSeed
        (activeReferenceTailSchedule m
          (slowWarmFallbackSchedule hn q hq hs0 K hK
            steps retries scoreScale) tail)) mu0)
      V (correctedAlpha m eta) i = fun omega ↦ u i (Preorder.frestrictLe i omega))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (omega (i + 1)).1)
    (hbudget : ∀ i, i + 1 < m → 2 * (mixError i).toReal ≤ correctedNu m eta) :
    SeedProjectedOperational
      (stateScheduleFromSeed (activeReferenceTailSchedule m
        (slowWarmFallbackSchedule hn q hq hs0 K hK
          steps retries scoreScale) tail))
      (activeReferenceTailSchedule m
        (slowWarmFallbackSchedule hn q hq hs0 K hK
          steps retries scoreScale) tail)
      Prod.snd Prod.fst mu0 V m eta := by
  apply seedProjectedOperational_activeReferenceTail_recursiveWarm m
    (slowWarmFallbackSchedule hn q hq hs0 K hK
      steps retries scoreScale) tail mu0 V eta
    (slowRadiusQSeedTarget n q s0 K) tau initialWarm
    (slowAcceptedFactor retries) (slowFallbackFactor n q s0 K) mixError
    hinitialOne (one_le_slowAcceptedFactor retries) hstart
  · intro i hi rho hprob hwarm
    letI : IsProbabilityMeasure rho := hprob
    exact isWarm_seed_slowRadiusQWarmFallbackKernel_step hn hq hs0 hK hKc hball
      hfin steps retries scoreScale hi (hrad i (Nat.lt_of_succ_lt hi))
      (hrad (i + 1) hi) rho hwarm
  · exact htailSeed
  · exact hactiveMixTop
  · exact hactiveMix
  · exact hu
  · exact hv
  · exact hU
  · exact hV
  · exact hbudget

noncomputable def independentStreamOperational_slowRadiusQ_recursive
    {k m : Nat} {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (ScoreSeed n)} [IsProbabilityMeasure mu0]
    {Vscalar : Nat → (Nat → ScoreSeed n) → Real} {eta : Real}
    (hop : SeedProjectedOperational (stateScheduleFromSeed Q) Q Prod.snd Prod.fst
      mu0 Vscalar m eta)
    (V : Nat → (Fin k → Nat → ScoreSeed n) → Real)
    (u : (i : Nat) → (Fin k → Finset.Iic i → ScoreSeed n) → Real)
    (v : Nat → (Fin k → ScoreSeed n) → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i, accuracyU (independentPathLaw k (stateScheduleFromSeed Q) mu0) V
      (correctedAlpha m eta) i =
        fun omega ↦ u i (fun l ↦ Preorder.frestrictLe i (omega l)))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (fun l ↦ omega l (i + 1)))
    (hbudget : ∀ i, (k : Real) * (2 * (hop.mixError i).toReal) ≤ correctedNu m eta) :
    IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd mu0 V m eta :=
  independentStreamOperational_of_seedProjected hop V u v hu hv hU hV hbudget

/-- Reuse the distributional part of an operational proof built with a larger active
cutoff at a smaller estimator length.  This is the honest `(m+1)`-cutoff/`m`-score
adapter: the statistic locality and dependence allowance are reproved at `m`. -/
noncomputable def independentStreamOperational_of_seedProjected_atLength
    {k cutoff m : Nat} {Q : Nat → Kernel (State n) (ScoreSeed n)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (ScoreSeed n)} [IsProbabilityMeasure mu0]
    {Vscalar : Nat → (Nat → ScoreSeed n) → Real} {eta : Real}
    (hop : SeedProjectedOperational (stateScheduleFromSeed Q) Q Prod.snd Prod.fst
      mu0 Vscalar cutoff eta)
    (V : Nat → (Fin k → Nat → ScoreSeed n) → Real)
    (u : (i : Nat) → (Fin k → Finset.Iic i → ScoreSeed n) → Real)
    (v : Nat → (Fin k → ScoreSeed n) → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i, accuracyU (independentPathLaw k (stateScheduleFromSeed Q) mu0) V
      (correctedAlpha m eta) i =
        fun omega ↦ u i (fun l ↦ Preorder.frestrictLe i (omega l)))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (fun l ↦ omega l (i + 1)))
    (hbudget : ∀ i, (k : Real) * (2 * (hop.mixError i).toReal) ≤ correctedNu m eta) :
    IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd mu0 V m eta where
  measurable_seed := measurable_snd
  factor := stateScheduleFromSeed_factor Q
  pi := hop.pi
  tau := hop.tau
  tau_prob := hop.tau_prob
  warmConst := hop.warmConst
  mixError := hop.mixError
  mixError_ne_top := hop.mixError_ne_top
  u := u
  v := v
  measurable_u := hu
  measurable_v := hv
  U_eq := hU
  V_eq := hV
  last_seed_warm := hop.last_seed_warm
  distributional_mixing := hop.distributional_mixing
  dependence_budget := hbudget

#print axioms isWarm_seed_slowRadiusQWarmFallbackKernel_step
#print axioms seedProjectedOperational_slowRadiusQ_recursive
#print axioms independentStreamOperational_slowRadiusQ_recursive
#print axioms independentStreamOperational_of_seedProjected_atLength

end Ttc.CVSlowRadiusQRecursiveOperational
