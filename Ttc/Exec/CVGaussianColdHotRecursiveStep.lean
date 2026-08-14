import Ttc.Exec.CVGaussianColdHotFallbackSchedule
import Ttc.Exec.CVGaussianHybridAcceptedWarm
import Ttc.Exec.CVColdResetSeedWarm
import Ttc.Exec.CVIndependentRefreshSeedLaws

/-!
# Recursive seed warmth for the literal cold/hot operation

This file fixes the actual speedy target family and the multiplicative coefficient in
the nonstationary warmness recurrence.  In the radius-four block the accepted law uses
the support-correct truncated cross-phase theorem, including the last-cold/full-body
boundary.  In the hot block it uses the accelerated Gaussian normalizer-ratio theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Ttc.CVGaussianColdHotRecursiveStep

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVHybridSchedule
open Ttc.CVCorrectedFixedBlockCost
open Ttc.CVSourceTruncatedFixedCost
open Ttc.CVColdAcceptedWarm
open Ttc.CVColdResetSeedWarm
open Ttc.CVIndependentRefreshSeedLaws
open Ttc.CVGaussianHybridAcceptedWarm
open Ttc.CVGaussianAdaptiveAcceptedWarm
open Ttc.CVGaussianWarmFallbackPhaseKernel
open Ttc.CVGaussianColdHotFallbackSchedule
open Ttc.CVColdHotScoreSeedSchedule
open Ttc.CVGaussianWarmFallbackOperational
open Ttc.CVSequentialPhaseSampler
open Ttc.FiniteContinuingRetryRandomFallback
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

noncomputable def sourceHotDelta (n : Nat) (s0 : Real) : Real :=
  fixedRadiusFourDelta n (fixedSigmaSq n s0 (coldPhases n s0))

noncomputable def coldHotSeedTarget
    (n : Nat) (N s0 : Real) (K : Set (State n)) (i : Nat) : Measure (State n) :=
  if i < coldPhases n s0 then
    ellGaussianProb (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
      (fixedRadiusFourDelta n (fixedSigmaSq n s0 i)) (fixedSigmaSq n s0 i)
  else ellGaussianProb K (sourceHotDelta n s0) (sigmaSq n N s0 i)

noncomputable def coldAcceptedFactor
    (n : Nat) (retries : Nat → Nat) (i : Nat) : ENNReal :=
  max 1 ((retries i : ENNReal) * (16 *
    (ENNReal.ofReal (((1 - 1 / (2 * (n : Real)))⁻¹) ^ n) *
      (ENNReal.ofReal (Real.exp (1 / 2)) * 2))))

noncomputable def hotAcceptedFactor
    (n : Nat) (N s0 : Real) (cold : Nat) (retries : Nat → Nat) (j : Nat) : ENNReal :=
  max 1 ((retries j : ENNReal) *
    (16 * acceleratedSeedWarmFactor n (1 + phaseRate n N s0 (cold + j))))

noncomputable def coldHotAcceptedFactor
    (n : Nat) (N s0 : Real) (cold : Nat)
    (coldRetries hotRetries : Nat → Nat) (i : Nat) : ENNReal :=
  if i < cold then coldAcceptedFactor n coldRetries i
  else hotAcceptedFactor n N s0 cold hotRetries (i - cold)

theorem one_le_coldHotAcceptedFactor
    (n : Nat) (N s0 : Real) (cold : Nat)
    (coldRetries hotRetries : Nat → Nat) (i : Nat) :
    1 ≤ coldHotAcceptedFactor n N s0 cold coldRetries hotRetries i := by
  unfold coldHotAcceptedFactor coldAcceptedFactor hotAcceptedFactor
  split <;> exact le_max_left _ _

noncomputable def coldFallback
    (n : Nat) (scoreScale s0 radius : Real) (_i : Nat) : Measure (ScoreSeed n) :=
  coldScoreSeedFallback (n := n) scoreScale s0 radius

noncomputable def hotFallback
    (n : Nat) (N s0 scoreScale : Real) (j : Nat) : Measure (ScoreSeed n) :=
  coldScoreSeedFallback (n := n) scoreScale
    (sigmaSq n N s0 (coldPhases n s0 + j + 1)) hotRefreshRadius

theorem isProbabilityMeasure_coldFallback
    (n : Nat) (scoreScale : Real) {s0 radius : Real}
    (hs0 : 0 < s0) (hradius : 0 < radius) (i : Nat) :
    IsProbabilityMeasure (coldFallback n scoreScale s0 radius i) := by
  unfold coldFallback
  exact isProbabilityMeasure_coldScoreSeedFallback scoreScale s0 radius hs0 hradius

theorem isProbabilityMeasure_hotFallback
    (hn : 1 ≤ n) {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    (scoreScale : Real) (j : Nat) :
    IsProbabilityMeasure (hotFallback n N s0 scoreScale j) := by
  unfold hotFallback
  exact isProbabilityMeasure_coldScoreSeedFallback _ _ _
    (sigmaSq_pos hn hN hs0 _) hotRefreshRadius_pos

/-- The fully specialized uncosted phase family.  Probability instances for both
sampleable fallback laws are constructed from the displayed positivity hypotheses. -/
noncomputable def sourceColdHotWarmFallbackSchedule
    (hn : 1 ≤ n) {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    (K : Set (State n)) (hK : MeasurableSet K)
    {radius : Real} (hradius : 0 < radius)
    (coldSteps hotSteps : Nat → Nat → Nat)
    (coldRetries hotRetries : Nat → Nat) (scoreScale : Real) :
    Nat → Kernel (State n) (ScoreSeed n) := by
  letI : ∀ j, IsProbabilityMeasure (coldFallback n scoreScale s0 radius j) :=
    fun j ↦ isProbabilityMeasure_coldFallback n scoreScale hs0 hradius j
  letI : ∀ j, IsProbabilityMeasure (hotFallback n N s0 scoreScale j) :=
    fun j ↦ isProbabilityMeasure_hotFallback hn hN hs0 scoreScale j
  exact coldHotWarmFallbackSchedule hn (coldPhases n s0) K hK s0 hs0
    coldSteps coldRetries (coldFallback n scoreScale s0 radius)
    (fun _ ↦ sourceHotDelta n s0)
    (fun j ↦ sigmaSq n N s0 (coldPhases n s0 + j))
    (fun _ ↦ 1 - 1 / (2 * (n : Real)))
    (fun _ ↦ fixedRadiusFourDelta_pos hn (by
      unfold fixedSigmaSq
      exact geomSchedule_pos hs0 (by positivity) (coldPhases n s0)))
    (fun _ ↦ by
      have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
      have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      linarith)
    hotSteps hotRetries (hotFallback n N s0 scoreScale)

instance sourceColdHotWarmFallbackSchedule.isMarkovKernel
    (hn : 1 ≤ n) {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    (K : Set (State n)) (hK : MeasurableSet K)
    {radius : Real} (hradius : 0 < radius)
    (coldSteps hotSteps : Nat → Nat → Nat)
    (coldRetries hotRetries : Nat → Nat) (scoreScale : Real) (i : Nat) :
    IsMarkovKernel (sourceColdHotWarmFallbackSchedule hn hN hs0 K hK hradius
      coldSteps hotSteps coldRetries hotRetries scoreScale i) := by
  letI : ∀ j, IsProbabilityMeasure (coldFallback n scoreScale s0 radius j) :=
    fun j ↦ isProbabilityMeasure_coldFallback n scoreScale hs0 hradius j
  letI : ∀ j, IsProbabilityMeasure (hotFallback n N s0 scoreScale j) :=
    fun j ↦ isProbabilityMeasure_hotFallback hn hN hs0 scoreScale j
  unfold sourceColdHotWarmFallbackSchedule coldHotWarmFallbackSchedule
  infer_instance

noncomputable def coldHotFallbackFactor
    (n : Nat) (N s0 : Real) (cold : Nat) (K : Set (State n)) (i : Nat) : ENNReal :=
  if i + 1 < cold then coldResetTruncatedWarmConst n (i + 1)
  else if i < cold then coldResetFullWarmConst (i + 1)
  else gaussianBallWarmFactor K (sigmaSq n N s0 (i + 1)) hotRefreshRadius

/-- The exact recursive step for the literal radius-four/full-body random-fallback
schedule.  The recurrence coefficient is internally fixed; no next-phase warmth
hypothesis is assumed. -/
theorem isWarm_seed_coldHotWarmFallbackSchedule_step
    (hn : 1 ≤ n) {m : Nat} {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {radius : Real} (hradius : 0 < radius)
    (hradiusShrink : radius < 1 - 1 / (2 * (n : Real)))
    (hcoldStart : 4 * (n : Real) * s0 ≤ radius ^ 2)
    (hrad : ∀ j, j < coldPhases n s0 →
      1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 j) * Real.sqrt n)
    (hradTwo : ∀ j, j ≤ coldPhases n s0 →
      1 ≤ 2 * Real.sqrt (fixedSigmaSq n s0 j) * Real.sqrt n)
    (coldSteps hotSteps : Nat → Nat → Nat)
    (coldRetries hotRetries : Nat → Nat)
    (scoreScale : Real)
    [∀ j, IsProbabilityMeasure (coldFallback n scoreScale s0 radius j)]
    [∀ j, IsProbabilityMeasure (hotFallback n N s0 scoreScale j)]
    {i : Nat} (hi : i + 1 < m)
    (rho : Measure (State n)) [IsProbabilityMeasure rho] {M : ENNReal}
    (hwarm : IsWarm M rho (coldHotSeedTarget n N s0 K i)) :
    IsWarm
      (coldHotAcceptedFactor n N s0 (coldPhases n s0)
          coldRetries hotRetries i * M +
        if i + 1 < coldPhases n s0 then coldResetTruncatedWarmConst n (i + 1)
        else if i < coldPhases n s0 then coldResetFullWarmConst (i + 1)
        else gaussianBallWarmFactor K (sigmaSq n N s0 (i + 1)) hotRefreshRadius)
      (Measure.map Prod.snd
        (sampleFromKernel
          (coldHotWarmFallbackSchedule hn (coldPhases n s0) K hK s0 hs0
            coldSteps coldRetries (coldFallback n scoreScale s0 radius)
            (fun _ ↦ sourceHotDelta n s0)
            (fun j ↦ sigmaSq n N s0 (coldPhases n s0 + j))
            (fun _ ↦ 1 - 1 / (2 * (n : Real)))
            (fun _ ↦ fixedRadiusFourDelta_pos hn (by
              unfold fixedSigmaSq
              exact geomSchedule_pos hs0 (by positivity) (coldPhases n s0)))
            (fun _ ↦ by
              have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
              have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
                rw [div_le_div_iff₀ (by positivity) (by norm_num)]
                linarith
              linarith)
            hotSteps hotRetries (hotFallback n N s0 scoreScale) i) rho))
      (coldHotSeedTarget n N s0 K (i + 1)) := by
  let cold := coldPhases n s0
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hc : c ≠ 0 := by
    have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
    have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    dsimp only [c]
    linarith
  by_cases hicold : i < cold
  · have hwarm' : IsWarm M rho
        (ellGaussianProb (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
          (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
          (fixedSigmaSq n s0 i)) := by
      simpa only [coldHotSeedTarget, cold, if_pos hicold] using hwarm
    have hicold0 : i < coldPhases n s0 := by simpa only [cold] using hicold
    by_cases hinext : i + 1 < cold
    · have hacc := isWarm_seed_acceptedOutputSubmeasure_cold_succ
          (m := cold) hn hK hKc hball hfin hs0 hinext
          (hrad i hicold) (hradTwo (i + 1) (Nat.le_of_lt hinext)) hwarm'
          (coldSteps i) (coldRetries i)
      have hfb := isWarm_seed_coldScoreSeedFallback_fixedRadiusFour
          (m := cold) hn hK hKc hball hfin hs0 hradius hradiusShrink
          hcoldStart (fun j hj ↦ hrad j hj)
          (fun j hj ↦ hradTwo j (Nat.le_of_lt hj)) hinext scoreScale
      have hstep :=
        isWarm_seed_sampleFrom_gaussianWarmFallbackPhaseKernel
          (measurableSet_fixedRadiusFourBody hK _)
          (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
          (fixedSigmaSq n s0 i) c
          (fixedRadiusFourDelta_pos hn (by
            unfold fixedSigmaSq
            exact geomSchedule_pos hs0 (by positivity) i)) hc
          (coldSteps i) (coldRetries i)
          (coldFallback n scoreScale s0 radius i) rho
          (ellGaussianProb (fixedRadiusFourBody K (fixedSigmaSq n s0 (i + 1)))
            (fixedRadiusFourDelta n (fixedSigmaSq n s0 (i + 1)))
            (fixedSigmaSq n s0 (i + 1))) hacc hfb
      have hle :
          (coldRetries i : ENNReal) * ((16 *
              (ENNReal.ofReal (((1 - 1 / (2 * (n : Real)))⁻¹) ^ n) *
                (ENNReal.ofReal (Real.exp (1 / 2)) * 2))) * M) +
              coldResetTruncatedWarmConst n (i + 1) ≤
            coldAcceptedFactor n coldRetries i * M +
              coldResetTruncatedWarmConst n (i + 1) := by
        calc
          (coldRetries i : ENNReal) * (16 *
                (ENNReal.ofReal (((1 - 1 / (2 * (n : Real)))⁻¹) ^ n) *
                  (ENNReal.ofReal (Real.exp (1 / 2)) * 2)) * M) +
              coldResetTruncatedWarmConst n (i + 1) =
            ((coldRetries i : ENNReal) * (16 *
                (ENNReal.ofReal (((1 - 1 / (2 * (n : Real)))⁻¹) ^ n) *
                  (ENNReal.ofReal (Real.exp (1 / 2)) * 2)))) * M +
              coldResetTruncatedWarmConst n (i + 1) := by ac_rfl
          _ ≤ coldAcceptedFactor n coldRetries i * M +
              coldResetTruncatedWarmConst n (i + 1) := by
            rw [coldAcceptedFactor]
            exact add_le_add (mul_le_mul_right' (le_max_right _ _) M) le_rfl
      have hmono := hstep.mono hle
      simpa only [coldHotWarmFallbackSchedule, coldHotSchedule,
        coldWarmFallbackKernel, coldHotSeedTarget, coldHotAcceptedFactor, cold, c,
        if_pos hicold, if_pos hicold0, dif_pos hicold0, if_pos hinext] using hmono
    · have hibound : i + 1 = cold := by omega
      have hibound0 : i + 1 = coldPhases n s0 := by simpa only [cold] using hibound
      have hiboundLt : i + 1 < cold + 1 := by omega
      have hacc := isWarm_seed_acceptedOutputSubmeasure_cold_full_succ
          (m := cold + 1) hn hK hKc hball hfin hs0 hiboundLt
          (hrad i hicold) (hradTwo (i + 1) (by omega)) hwarm'
          (coldSteps i) (coldRetries i)
      have hseed : IsWarm (coldResetFullWarmConst (i + 1))
          (coldBallStart (n := n) s0 radius)
          (ellGaussianProb K (sourceHotDelta n s0)
            (fixedSigmaSq n s0 (i + 1))) := by
        apply isWarm_coldBallStart_fixed_full_ellGaussianProb
          (m := cold + 1) hn hK hKc hball hfin hs0 hradius hradiusShrink
          hcoldStart (fixedRadiusFourDelta_pos hn (by
            unfold fixedSigmaSq
            exact geomSchedule_pos hs0 (by positivity) (coldPhases n s0)))
          (fixedRadiusFourDelta_le_n (n := n)) hiboundLt
      have hfb : IsWarm (coldResetFullWarmConst (i + 1))
          (Measure.map Prod.snd (coldFallback n scoreScale s0 radius i))
          (ellGaussianProb K (sourceHotDelta n s0)
            (fixedSigmaSq n s0 (i + 1))) := by
        rw [coldFallback, map_snd_coldScoreSeedFallback]
        exact hseed
      have hacc' : IsWarm
          ((coldRetries i : ENNReal) * (16 *
            (ENNReal.ofReal (((1 - 1 / (2 * (n : Real)))⁻¹) ^ n) *
              (ENNReal.ofReal (Real.exp (1 / 2)) * 2)) * M))
          (Measure.map Prod.snd
            (Ttc.FiniteContinuingRetryRandomFallback.acceptedOutputSubmeasure
              (Ttc.CVGaussianAugmentedSelectiveTV.augmentedMarginalOf
                (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
                (measurableSet_fixedRadiusFourBody hK _)
                (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
                (fixedSigmaSq n s0 i) c
                (fixedRadiusFourDelta_pos hn (by
                  unfold fixedSigmaSq
                  exact geomSchedule_pos hs0 (by positivity) i)) hc
                (coldSteps i)
                (Measure.map (Ttc.CVGaussianScoreSeedPhaseKernel.seedEmbedding c) rho)
                (coldRetries i))))
          (ellGaussianProb K (sourceHotDelta n s0)
            (fixedSigmaSq n s0 (i + 1))) := by
        simpa only [c, sourceHotDelta, hibound] using hacc
      have hstep :=
        isWarm_seed_sampleFrom_gaussianWarmFallbackPhaseKernel
          (measurableSet_fixedRadiusFourBody hK _)
          (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
          (fixedSigmaSq n s0 i) c
          (fixedRadiusFourDelta_pos hn (by
            unfold fixedSigmaSq
            exact geomSchedule_pos hs0 (by positivity) i)) hc
          (coldSteps i) (coldRetries i)
          (coldFallback n scoreScale s0 radius i) rho
          (ellGaussianProb K (sourceHotDelta n s0)
            (fixedSigmaSq n s0 (i + 1))) hacc' hfb
      have hle :
          (coldRetries i : ENNReal) * ((16 *
              (ENNReal.ofReal (((1 - 1 / (2 * (n : Real)))⁻¹) ^ n) *
                (ENNReal.ofReal (Real.exp (1 / 2)) * 2))) * M) +
              coldResetFullWarmConst (i + 1) ≤
            coldAcceptedFactor n coldRetries i * M +
              coldResetFullWarmConst (i + 1) := by
        calc
          (coldRetries i : ENNReal) * (16 *
                (ENNReal.ofReal (((1 - 1 / (2 * (n : Real)))⁻¹) ^ n) *
                  (ENNReal.ofReal (Real.exp (1 / 2)) * 2)) * M) +
              coldResetFullWarmConst (i + 1) =
            ((coldRetries i : ENNReal) * (16 *
                (ENNReal.ofReal (((1 - 1 / (2 * (n : Real)))⁻¹) ^ n) *
                  (ENNReal.ofReal (Real.exp (1 / 2)) * 2)))) * M +
              coldResetFullWarmConst (i + 1) := by ac_rfl
          _ ≤ coldAcceptedFactor n coldRetries i * M +
              coldResetFullWarmConst (i + 1) := by
            rw [coldAcceptedFactor]
            exact add_le_add (mul_le_mul_right' (le_max_right _ _) M) le_rfl
      have hmono := hstep.mono hle
      simpa only [coldHotWarmFallbackSchedule, coldHotSchedule,
        coldWarmFallbackKernel, coldHotSeedTarget, coldHotAcceptedFactor,
        cold, c, if_pos hicold, if_pos hicold0, dif_pos hicold0, if_neg hinext,
        hibound, hibound0, Nat.lt_irrefl, if_false,
        sigmaSq_cold_boundary hn hN hs0, fixedSigmaSq, coldEnd] using hmono
  · have hicold0 : ¬ i < coldPhases n s0 := by simpa only [cold] using hicold
    have hinext0 : ¬ i + 1 < coldPhases n s0 := by omega
    let j := i - cold
    have hcoldle : cold ≤ i := Nat.le_of_not_gt hicold
    have hindex : cold + j = i := by
      dsimp only [j]
      omega
    have hdelta : 0 < sourceHotDelta n s0 := by
      unfold sourceHotDelta
      exact fixedRadiusFourDelta_pos hn (by
        unfold fixedSigmaSq
        exact geomSchedule_pos hs0 (by positivity) (coldPhases n s0))
    have hdeltan : sourceHotDelta n s0 ≤ 1 / (2 * (n : Real)) := by
      unfold sourceHotDelta
      exact fixedRadiusFourDelta_le_n
    have hwarm' : IsWarm M rho
        (ellGaussianProb K (sourceHotDelta n s0) (sigmaSq n N s0 i)) := by
      simpa only [coldHotSeedTarget, if_neg hicold0] using hwarm
    have hacc := activeAcceptedWarm_gaussian_hybrid
      (m := m) hn hN hs0 hK hKc hball hfin hdelta hdeltan
      (fun _ ↦ M) (fun t ↦ hotSteps (t - cold))
      (fun t ↦ hotRetries (t - cold)) i hi rho inferInstance hwarm'
    have hfb0 := isWarm_hotRefresh_ellGaussianProb hn hK hKc hball hfin
      (sigmaSq_pos hn hN hs0 (i + 1)) hdelta hdeltan
    have hfb : IsWarm
        (gaussianBallWarmFactor K (sigmaSq n N s0 (i + 1)) hotRefreshRadius)
        (Measure.map Prod.snd (hotFallback n N s0 scoreScale j))
        (ellGaussianProb K (sourceHotDelta n s0) (sigmaSq n N s0 (i + 1))) := by
      rw [hotFallback, map_snd_coldScoreSeedFallback, hindex]
      simpa only [Nat.add_assoc] using hfb0
    have hacc' : IsWarm
        ((hotRetries j : ENNReal) *
          (16 * acceleratedSeedWarmFactor n (1 + phaseRate n N s0 i) * M))
        (Measure.map Prod.snd
          (Ttc.FiniteContinuingRetryRandomFallback.acceptedOutputSubmeasure
            (Ttc.CVGaussianAugmentedSelectiveTV.augmentedMarginalOf K hK
              (sourceHotDelta n s0) (sigmaSq n N s0 i) c hdelta hc
              (hotSteps j)
              (Measure.map (Ttc.CVGaussianScoreSeedPhaseKernel.seedEmbedding c) rho)
              (hotRetries j))))
        (ellGaussianProb K (sourceHotDelta n s0) (sigmaSq n N s0 (i + 1))) := by
      simpa only [hybridAcceptedBudget, j, hindex, c] using hacc
    have hstep := isWarm_seed_sampleFrom_gaussianWarmFallbackPhaseKernel
      hK (sourceHotDelta n s0) (sigmaSq n N s0 i) c hdelta hc
      (hotSteps j) (hotRetries j) (hotFallback n N s0 scoreScale j) rho
      (ellGaussianProb K (sourceHotDelta n s0) (sigmaSq n N s0 (i + 1)))
      hacc' hfb
    have hle :
        (hotRetries j : ENNReal) *
            ((16 * acceleratedSeedWarmFactor n (1 + phaseRate n N s0 i)) * M) +
          gaussianBallWarmFactor K (sigmaSq n N s0 (i + 1)) hotRefreshRadius ≤
        hotAcceptedFactor n N s0 cold hotRetries j * M +
          gaussianBallWarmFactor K (sigmaSq n N s0 (i + 1)) hotRefreshRadius := by
      calc
        (hotRetries j : ENNReal) *
              ((16 * acceleratedSeedWarmFactor n (1 + phaseRate n N s0 i)) * M) +
            gaussianBallWarmFactor K (sigmaSq n N s0 (i + 1)) hotRefreshRadius =
          ((hotRetries j : ENNReal) *
              (16 * acceleratedSeedWarmFactor n (1 + phaseRate n N s0 (cold + j)))) * M +
            gaussianBallWarmFactor K (sigmaSq n N s0 (i + 1)) hotRefreshRadius := by
              rw [hindex]
              ac_rfl
        _ ≤ hotAcceptedFactor n N s0 cold hotRetries j * M +
            gaussianBallWarmFactor K (sigmaSq n N s0 (i + 1)) hotRefreshRadius := by
          rw [hotAcceptedFactor]
          exact add_le_add (mul_le_mul_right' (le_max_right _ _) M) le_rfl
    have hmono := hstep.mono hle
    simpa only [coldHotWarmFallbackSchedule, coldHotSchedule,
      warmFallbackSchedule, coldHotSeedTarget, coldHotAcceptedFactor,
      cold, c, j, if_neg hicold, if_neg hicold0, dif_neg hicold0,
      if_neg hinext0, hindex] using hmono

#print axioms one_le_coldHotAcceptedFactor
#print axioms isWarm_seed_coldHotWarmFallbackSchedule_step

end Ttc.CVGaussianColdHotRecursiveStep
