import Ttc.Exec.CVSlowRadiusQReferencePhaseTV
import Ttc.Exec.CVGaussianCappedCostEnvelope

/-! Expected retained-reference cost for an arbitrary positive slow variance schedule. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace Ttc.CVSlowRadiusQReferenceCost

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVAdaptiveRadiusQPrimitives Ttc.CVSlowRadiusQFallbackSchedule
open Ttc.CVGaussianWarmFallbackCostedPhaseKernel
open Ttc.CVGaussianWarmFallbackAnalytic Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.CVConcreteAugmentedRetryCutoffBudget Ttc.CVHeterogeneousHistoryReference
open Ttc.FiniteContinuingRetryGaussianAugmentedPhase Ttc.FiniteContinuingRetry
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

theorem lintegral_heterogeneousStepMean_radiusQCostedOfSigma
    (hn : 1 ≤ n) {q : Real} (hq : 0 < q)
    (sigmaSq : Nat → Real) (hsigma : ∀ i, 0 < sigmaSq i)
    {K : Set (State n)} (hK : MeasurableSet K)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)]
    (rho : Measure (State n)) [IsProbabilityMeasure rho] (i : Nat) :
    (∫⁻ x, heterogeneousStepMean
      (radiusQWarmFallbackCostedKernelOfSigma hn q hq K hK sigmaSq hsigma
        steps retries fallback i) x ∂rho) =
      warmFallbackPhaseQueryMean
        (radiusQBody q K (sigmaSq i)) (measurableSet_radiusQBody hK)
        (radiusQDelta n q (sigmaSq i)) (sigmaSq i)
        (1 - 1 / (2 * (n : Real)))
        (radiusQDelta_pos hn hq (hsigma i))
        (Ttc.CVScoreSeedExceptionalCost.standardShrink_ne_zero hn)
        (steps i) (retries i) rho := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  let body := radiusQBody q K (sigmaSq i)
  let delta := radiusQDelta n q (sigmaSq i)
  let s := sigmaSq i
  let hdelta : 0 < delta := radiusQDelta_pos hn hq (hsigma i)
  have hc : c ≠ 0 := Ttc.CVScoreSeedExceptionalCost.standardShrink_ne_zero hn
  unfold radiusQWarmFallbackCostedKernelOfSigma
  change (∫⁻ x, ∫⁻ y, y.1 ∂gaussianWarmFallbackCostedPhaseKernel
      body (measurableSet_radiusQBody hK) delta s c hdelta hc
        (steps i) (retries i) (fallback i) x ∂rho) = _
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
      (steps i) (retries i) (fallback i) x

theorem radiusQCostedOfSigma_referenceCost_le_of_warm
    (hn : 2 ≤ n) {q : Real} (hq : 1 < q)
    (sigmaSq : Nat → Real) (hsigma : ∀ i, 0 < sigmaSq i)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n)) [∀ i, IsProbabilityMeasure (fallback i)]
    (rho : Measure (State n)) [IsProbabilityMeasure rho]
    {M : ENNReal} (hMtop : M ≠ ⊤) (i : Nat)
    (hrad : 1 ≤ q * Real.sqrt (sigmaSq i) * Real.sqrt n)
    (hwarm : IsWarm M rho
      (ellGaussianProb (radiusQBody q K (sigmaSq i))
        (radiusQDelta n q (sigmaSq i)) (sigmaSq i))) :
    (∫⁻ x, heterogeneousStepMean
      (radiusQWarmFallbackCostedKernelOfSigma (by omega : 1 ≤ n) q
        (zero_lt_one.trans hq) K hK sigmaSq hsigma steps retries fallback i) x ∂rho) ≤
      ENNReal.ofReal (retryReferenceMeanEnvelope M.toReal (steps i) (retries i)) := by
  let hn1 : 1 ≤ n := by omega
  let body := radiusQBody q K (sigmaSq i)
  let s := sigmaSq i
  let sigma := Real.sqrt s
  let delta := radiusQDelta n q s
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hs : 0 < s := hsigma i
  have hsigma0 : 0 < sigma := Real.sqrt_pos.2 hs
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
    unitBall_subset_inter_closedBall hball
      (by simpa only [body, s, radiusQBody] using hrad)
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
    simpa only [pi, body, delta, s] using hwarm
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
    hn hbodyM hbodyC hbodyBall hq hdelta hsigma0 hc
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
  rw [lintegral_heterogeneousStepMean_radiusQCostedOfSigma hn1
    (zero_lt_one.trans hq) sigmaSq hsigma hK steps retries fallback rho i]
  simpa only [body, delta, s, c] using hcost

#print axioms lintegral_heterogeneousStepMean_radiusQCostedOfSigma
#print axioms radiusQCostedOfSigma_referenceCost_le_of_warm

end Ttc.CVSlowRadiusQReferenceCost
