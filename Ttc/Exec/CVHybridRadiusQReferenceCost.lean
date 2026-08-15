import Ttc.Exec.CVHybridRadiusQRecursiveStep
import Ttc.Exec.CVGaussianCappedCostEnvelope

/-! Expected reference cost for the selected-radius hybrid fallback phase. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace Ttc.CVHybridRadiusQReferenceCost

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVHybridSchedule Ttc.CVAdaptiveRadiusQPrimitives
open Ttc.CVHybridRadiusQRecursiveStep Ttc.CVHybridRadiusQFallbackSchedule
open Ttc.CVGaussianWarmFallbackCostedPhaseKernel
open Ttc.CVGaussianWarmFallbackAnalytic
open Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.CVConcreteAugmentedRetryCutoffBudget
open Ttc.CVHeterogeneousHistoryReference
open Ttc.FiniteContinuingRetryGaussianAugmentedPhase
open Ttc.FiniteContinuingRetry
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- Exact identification of the heterogeneous phase mean with the generic
random-fallback retry-query mean. -/
theorem lintegral_heterogeneousStepMean_sourceHybridRadiusQCosted
    (hn : 1 ≤ n) {q N s0 : Real} (hq : 0 < q) (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat) (scoreScale : Real)
    (rho : Measure (State n)) [IsProbabilityMeasure rho] (i : Nat) :
    (∫⁻ x, heterogeneousStepMean
      (sourceHybridRadiusQWarmFallbackCostedSchedule hn q hq hN hs0 K hK
        steps retries scoreScale i) x ∂rho) =
      warmFallbackPhaseQueryMean
        (radiusQBody q K (sigmaSq n N s0 i)) (measurableSet_radiusQBody hK)
        (radiusQDelta n q (sigmaSq n N s0 i)) (sigmaSq n N s0 i)
        (1 - 1 / (2 * (n : Real)))
        (radiusQDelta_pos hn hq (sigmaSq_pos hn hN hs0 i))
        (Ttc.CVScoreSeedExceptionalCost.standardShrink_ne_zero hn)
        (steps i) (retries i) rho := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  let body := radiusQBody q K (sigmaSq n N s0 i)
  let delta := radiusQDelta n q (sigmaSq n N s0 i)
  let s := sigmaSq n N s0 i
  let hdelta : 0 < delta := radiusQDelta_pos hn hq (sigmaSq_pos hn hN hs0 i)
  have hc : c ≠ 0 := Ttc.CVScoreSeedExceptionalCost.standardShrink_ne_zero hn
  letI : IsProbabilityMeasure (hybridRadiusQFallback n N s0 scoreScale i) :=
    isProbabilityMeasure_hybridRadiusQFallback hn hN hs0 scoreScale i
  unfold sourceHybridRadiusQWarmFallbackCostedSchedule
  unfold hybridRadiusQWarmFallbackCostedKernel
  change (∫⁻ x, ∫⁻ y, y.1 ∂gaussianWarmFallbackCostedPhaseKernel
      body (measurableSet_radiusQBody hK) delta s c hdelta hc
        (steps i) (retries i) (hybridRadiusQFallback n N s0 scoreScale i) x ∂rho) = _
  unfold warmFallbackPhaseQueryMean augmentedPhaseQueryMean
    Ttc.CVSequentialPhaseSampler.sampleFromKernel
  rw [Measure.lintegral_bind
    (augmentedGaussianRetryStateKernel body (measurableSet_radiusQBody hK)
      delta s c hdelta hc (steps i) (retries i)).aemeasurable
    measurable_accumulatedCost.aemeasurable,
    lintegral_map
      (measurable_accumulatedCost.lintegral_kernel (κ :=
        augmentedGaussianRetryStateKernel body (measurableSet_radiusQBody hK)
          delta s c hdelta hc (steps i) (retries i)))
      (measurable_seedEmbedding c)]
  apply lintegral_congr
  intro x
  exact lintegral_fst_gaussianWarmFallbackCostedPhaseKernel
    (measurableSet_radiusQBody hK) delta s c hdelta hc
      (steps i) (retries i) (hybridRadiusQFallback n N s0 scoreScale i) x

/-- An `M`-warm incoming reference seed pays the generic retry envelope.  This is the
cost half of the retained-reference phase interface for the selected-radius schedule. -/
theorem sourceHybridRadiusQ_referenceCost_le_of_warm
    (hn : 2 ≤ n) {q N s0 : Real} (hq : 1 < q) (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat) (scoreScale : Real)
    (rho : Measure (State n)) [IsProbabilityMeasure rho]
    {M : ENNReal} (hMtop : M ≠ ⊤) (i : Nat)
    (hrad : 1 ≤ q * Real.sqrt (sigmaSq n N s0 i) * Real.sqrt n)
    (hwarm : IsWarm M rho (hybridRadiusQSeedTarget n q N s0 K i)) :
    (∫⁻ x, heterogeneousStepMean
      (sourceHybridRadiusQWarmFallbackCostedSchedule (by omega : 1 ≤ n)
        q (zero_lt_one.trans hq) hN hs0 K hK steps retries scoreScale i) x ∂rho) ≤
      ENNReal.ofReal (retryReferenceMeanEnvelope M.toReal (steps i) (retries i)) := by
  let hn1 : 1 ≤ n := by omega
  let body := radiusQBody q K (sigmaSq n N s0 i)
  let s := sigmaSq n N s0 i
  let sigma := Real.sqrt s
  let delta := radiusQDelta n q s
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hs : 0 < s := sigmaSq_pos hn1 hN hs0 i
  have hsigma : 0 < sigma := Real.sqrt_pos.2 hs
  have hsigmaSq : sigma ^ 2 = s := Real.sq_sqrt hs.le
  have hdelta : 0 < delta := radiusQDelta_pos hn1 (zero_lt_one.trans hq) hs
  have hc : c ≠ 0 := Ttc.CVScoreSeedExceptionalCost.standardShrink_ne_zero hn1
  have hc0 : 0 < c := by
    change 0 < 1 - 1 / (2 * (n : Real))
    have hnR : (1 : Real) ≤ n := by exact_mod_cast hn1
    have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hc1 : c < 1 := by
    change 1 - 1 / (2 * (n : Real)) < 1
    have hpos : 0 < 1 / (2 * (n : Real)) := by positivity
    linarith
  have hdeltaC : delta ≤ 1 - c := by
    change radiusQDelta n q s ≤ 1 - (1 - 1 / (2 * (n : Real)))
    simpa only [sub_sub_cancel] using radiusQDelta_le_n n q s
  have hbodyM : MeasurableSet body := measurableSet_radiusQBody hK
  have hbodyC : Convex Real body := convex_radiusQBody hKc
  have hbodyBall : ball (0 : State n) 1 ⊆ body :=
    unitBall_subset_inter_closedBall hball (by simpa only [body, s, radiusQBody] using hrad)
  have hbodyTop : volume body ≠ ⊤ := by
    dsimp only [body, radiusQBody]
    exact volume_inter_closedBall_ne_top K _
  have hmass0 : ellGaussianMeasure body delta s Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero_of_ball hbodyM hbodyC hbodyBall
      hc0 hc1 hdelta hdeltaC hs
  have hmassTop : ellGaussianMeasure body delta s Set.univ ≠ ⊤ :=
    ellGaussianMeasure_univ_ne_top hs body delta hbodyTop
  let pi := ellGaussianProb body delta s
  letI : IsProbabilityMeasure pi := isProbabilityMeasure_ellGaussianProb hmass0 hmassTop
  have hwarm' : IsWarm (ENNReal.ofReal M.toReal) rho pi := by
    rw [ENNReal.ofReal_toReal hMtop]
    simpa only [pi, body, delta, s, hybridRadiusQSeedTarget] using hwarm
  have hkilled : ∀ j, j < retries i → IsWarm (ENNReal.ofReal M.toReal)
      (Ttc.FiniteContinuingRetryExpectedCost.runningCurrent
        (Ttc.CVGaussianAugmentedSelectiveTV.augmentedMarginalOf body hbodyM delta s c
          hdelta hc (steps i) (Measure.map (seedEmbedding c) rho) j)) pi := by
    intro j _hj
    exact isWarm_runningCurrent_augmentedMarginalOf_gaussian hbodyM hdelta hc
      rho hwarm' (steps i) j
  have hcostRaw := warmFallbackPhaseQueryMean_le_referenceEnvelope
    (K := body) (q := q) (delta := delta) (sigma := sigma)
    (R := q * sigma * Real.sqrt n) (c := c)
    hn hbodyM hbodyC hbodyBall hq hdelta hsigma hc
    (radiusQDelta_le_n n q s)
    (by simpa only [delta, sigma] using radiusQDelta_le_radius n q s)
    (by positivity : 0 ≤ q * sigma * Real.sqrt n) le_rfl
    (fun x hx ↦ norm_le_radiusQBody hx) (steps i) rho pi
    (by simpa only [pi, hsigmaSq]) ENNReal.toReal_nonneg (retries i)
    (by simpa only [hsigmaSq] using hkilled)
  have hcost : warmFallbackPhaseQueryMean body hbodyM delta s c hdelta hc
      (steps i) (retries i) rho ≤
      ENNReal.ofReal (retryReferenceMeanEnvelope M.toReal (steps i) (retries i)) := by
    simpa only [hsigmaSq] using hcostRaw
  rw [lintegral_heterogeneousStepMean_sourceHybridRadiusQCosted hn1
    (zero_lt_one.trans hq) hN hs0 hK steps retries scoreScale rho i]
  simpa only [body, delta, s, c] using hcost

/-- At the exact radius-`q` truncated stationary law the retained reference pays the
retry envelope with warmness one.  This is the phase-cost specialization used by a
reference construction which resets the seed to the current stationary law. -/
theorem sourceHybridRadiusQ_stationaryReferenceCost_le
    (hn : 2 ≤ n) {q N s0 : Real} (hq : 1 < q) (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat) (scoreScale : Real)
    (i : Nat)
    (hrad : 1 ≤ q * Real.sqrt (sigmaSq n N s0 i) * Real.sqrt n) :
    (∫⁻ x, heterogeneousStepMean
      (sourceHybridRadiusQWarmFallbackCostedSchedule (by omega : 1 ≤ n)
        q (zero_lt_one.trans hq) hN hs0 K hK steps retries scoreScale i) x
      ∂(hybridRadiusQSeedTarget n q N s0 K i)) ≤
      ENNReal.ofReal (retryReferenceMeanEnvelope 1 (steps i) (retries i)) := by
  let body := radiusQBody q K (sigmaSq n N s0 i)
  let delta := radiusQDelta n q (sigmaSq n N s0 i)
  have hs : 0 < sigmaSq n N s0 i := sigmaSq_pos (by omega) hN hs0 i
  have hdelta : 0 < delta := radiusQDelta_pos (by omega) (zero_lt_one.trans hq) hs
  have hbodyM : MeasurableSet body := measurableSet_radiusQBody hK
  have hbodyC : Convex Real body := convex_radiusQBody hKc
  have hbodyBall : ball (0 : State n) 1 ⊆ body :=
    unitBall_subset_inter_closedBall hball
      (by simpa only [body, radiusQBody] using hrad)
  have hbodyTop : volume body ≠ ⊤ := by
    dsimp only [body, radiusQBody]
    exact volume_inter_closedBall_ne_top K _
  have hmass0 : ellGaussianMeasure body delta (sigmaSq n N s0 i) Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero_of_ball hbodyM hbodyC hbodyBall
      (by
        change 0 < 1 - 1 / (2 * (n : Real))
        have hnR : (1 : Real) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
        have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith
        linarith)
      (by
        change 1 - 1 / (2 * (n : Real)) < 1
        have hpos : 0 < 1 / (2 * (n : Real)) := by positivity
        linarith)
      hdelta
      (by
        change radiusQDelta n q (sigmaSq n N s0 i) ≤
          1 - (1 - 1 / (2 * (n : Real)))
        simpa only [sub_sub_cancel] using
          radiusQDelta_le_n n q (sigmaSq n N s0 i))
      hs
  have hmassTop :
      ellGaussianMeasure body delta (sigmaSq n N s0 i) Set.univ ≠ ⊤ :=
    ellGaussianMeasure_univ_ne_top hs body delta hbodyTop
  letI : IsProbabilityMeasure (hybridRadiusQSeedTarget n q N s0 K i) := by
    simpa only [hybridRadiusQSeedTarget, body, delta] using
      (isProbabilityMeasure_ellGaussianProb hmass0 hmassTop)
  simpa using sourceHybridRadiusQ_referenceCost_le_of_warm hn hq hN hs0 hK hKc
    hball steps retries scoreScale
    (hybridRadiusQSeedTarget n q N s0 K i) (M := 1) (by simp) i hrad
    (IsWarm.refl _)

#print axioms lintegral_heterogeneousStepMean_sourceHybridRadiusQCosted
#print axioms sourceHybridRadiusQ_referenceCost_le_of_warm
#print axioms sourceHybridRadiusQ_stationaryReferenceCost_le

end Ttc.CVHybridRadiusQReferenceCost
