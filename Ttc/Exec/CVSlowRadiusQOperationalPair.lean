import Ttc.Exec.CVSlowRadiusQFallbackSchedule
import Ttc.Exec.CVGaussianWarmFallbackZeroSafe
import Ttc.Exec.CVGaussianAdaptiveMixing

/-! Local graph-law accuracy for a radius-`q` fallback kernel on an arbitrary
positive variance schedule.  Keeping the local truncated target is important:
its seed marginal is the accepted law used by the next retained phase. -/

set_option autoImplicit false

namespace Ttc.CVSlowRadiusQOperationalPair

open MeasureTheory ProbabilityTheory Metric Set Pointwise
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler
open Ttc.CVAdaptiveRadiusQPrimitives Ttc.CVSlowRadiusQFallbackSchedule
open Ttc.CVGaussianWarmFallbackPhaseKernel Ttc.CVGaussianWarmFallbackZeroSafe
open Ttc.CVGaussianWarmFallbackAnalytic Ttc.CVGaussianAugmentedSelectiveTV
open Ttc.CVGaussianScoreSeedPhaseKernel Ttc.CVCombinedContinuingAccept
open Ttc.CVContinuingRetryParameters Ttc.FiniteContinuingRetryProjectedWarm
open scoped ENNReal Classical BigOperators

variable {n m : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

theorem tvLe_radiusQWarmFallbackKernelOfSigma_localPair_adjustable_zeroSafe_of_eq
    (hn : 21 ≤ n) {q : Real} (hq : 1 < q)
    (sigmaSq : Nat → Real) (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ j, IsProbabilityMeasure (fallback j)]
    (i : Nat) (hi : i < m)
    (rho : Measure (State n)) [IsProbabilityMeasure rho]
    {M eta zeta : ENNReal} (hM1 : 1 ≤ M) (hMtop : M ≠ ⊤)
    (heta0 : eta ≠ 0) (hetatop : eta ≠ ⊤) (heta1 : eta ≤ 1)
    (hzeta0 : zeta ≠ 0) (hzetatop : zeta ≠ ⊤)
    (hzeta16 : zeta ≤ ENNReal.ofReal (1 / 16 : Real))
    (hrad : 1 ≤ q * Real.sqrt (sigmaSq i) * Real.sqrt n)
    (hwarm : IsWarm M rho
      (ellGaussianProb
        (radiusQBody q K (sigmaSq i))
        (radiusQDelta n q (sigmaSq i)) (sigmaSq i)))
    (L : Nat)
    (hsteps : steps i = fun _ ↦
      Ttc.CVGaussianAdaptiveMixing.adjustableSpeedyDeadline n
        (radiusQDelta n q (sigmaSq i)) (sigmaSq i) (M / eta) zeta)
    (hretries : retries i = L) :
    TVLe
      (sampleFromKernel
        (radiusQWarmFallbackKernelOfSigma (by omega : 1 ≤ n) q
          (zero_lt_one.trans hq) K hK sigmaSq hsigma steps retries fallback i) rho)
      (scoreSeedReference (1 - 1 / (2 * (n : Real)))
        (coolLaw m sigmaSq (radiusQBody q K (sigmaSq i)) i))
      (32 * zeta + (eta + continuingContraction ^ L)) := by
  have hn1 : 1 ≤ n := by omega
  have hq0 : 0 < q := zero_lt_one.trans hq
  let s := sigmaSq i
  let delta := radiusQDelta n q s
  let body := radiusQBody q K s
  let c : Real := 1 - 1 / (2 * (n : Real))
  let pi := ellGaussianProb body delta s
  let deadline := fun W : ENNReal ↦
    Ttc.CVGaussianAdaptiveMixing.adjustableSpeedyDeadline n delta s W zeta
  have hs : 0 < s := by simpa only [s] using hsigma i
  have hdelta : 0 < delta := radiusQDelta_pos hn1 hq0 hs
  have hbodyM : MeasurableSet body := measurableSet_radiusQBody hK
  have hbodyC : Convex Real body := convex_radiusQBody hKc
  have hbodyBall : ball (0 : State n) 1 ⊆ body :=
    unitBall_subset_inter_closedBall hball
      (by simpa only [body, radiusQBody, s] using hrad)
  have hbody0 : volume body ≠ 0 :=
    volume_inter_closedBall_ne_zero hball
      (by simpa only [body, radiusQBody, s] using hrad)
  have hbodyTop : volume body ≠ ⊤ := by
    dsimp only [body, radiusQBody]
    exact volume_inter_closedBall_ne_top K _
  have hc0 : 0 < c := by
    dsimp [c]
    have hnR : (1 : Real) ≤ n := by exact_mod_cast hn1
    have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hc1 : c < 1 := by
    dsimp [c]
    have hnR : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn1
    have : 0 < 1 / (2 * (n : Real)) := by positivity
    linarith
  have hcne : c ≠ 0 := hc0.ne'
  have hdeltan : delta ≤ 1 / (2 * (n : Real)) := radiusQDelta_le_n n q s
  have hdeltaC : delta ≤ 1 - c := by dsimp only [c]; linarith
  have hM0 : ellGaussianMeasure body delta s Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero_of_ball hbodyM hbodyC hbodyBall
      hc0 hc1 hdelta hdeltaC hs
  have hMfinite : ellGaussianMeasure body delta s Set.univ ≠ ⊤ :=
    ellGaussianMeasure_univ_ne_top hs body delta hbodyTop
  letI : IsProbabilityMeasure pi := by
    dsimp only [pi]
    exact isProbabilityMeasure_ellGaussianProb hM0 hMfinite
  let rhoPair := Measure.map (seedEmbedding c) rho
  letI : IsProbabilityMeasure rhoPair :=
    Measure.isProbabilityMeasure_map (measurable_seedEmbedding c).aemeasurable
  have hkilled : ∀ j, IsWarm M
      (runningCurrent
        (augmentedMarginalOf body hbodyM delta s c hdelta hcne
          (fun _ ↦ deadline (M / eta)) rhoPair j)) pi := by
    intro j
    exact isWarm_runningCurrent_augmentedMarginalOf_gaussian
      hbodyM hdelta hcne rho (by simpa only [pi, body, delta, s] using hwarm)
      (fun _ ↦ deadline (M / eta)) j
  have hMetaTop : M / eta ≠ ⊤ := ENNReal.div_ne_top hMtop heta0
  have hMeta1 : 1 ≤ M / eta := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl heta0) (Or.inl hetatop)).2
    rw [one_mul]
    exact heta1.trans hM1
  have hmix : ∀ nu : Measure (State n),
      IsWarm (M / eta) nu pi → IsProbabilityMeasure nu →
        TVLe
          (sampleFromKernel
            (iteratedKernel (lazy (speedyMetropolisGaussian body delta s))
              (deadline (M / eta))) nu) pi zeta := by
    intro nu hnu hprob
    letI : IsProbabilityMeasure nu := hprob
    apply Ttc.CVGaussianAdaptiveMixing.tvLe_adjustableSpeedyDeadline
      (q := q) (R := q * Real.sqrt s * Real.sqrt n)
      hn hq hs hdelta
      (by simpa only [delta] using radiusQDelta_le_radius n q s)
      hbodyM hbodyC hbody0 (by positivity)
      (fun x hx ↦ norm_le_radiusQBody hx) le_rfl
      hMeta1 hMetaTop hzeta0 hzetatop (hzeta16.trans (by norm_num))
      (by simpa only [pi] using hnu)
  have heighth : ENNReal.ofReal (1 / 8 : Real) ≤
      SpeedyRejection.proposal pi (combinedAccept body c s) := by
    simpa only [pi, body, delta, s, c] using
      (Ttc.CVIdealCombinedAccepted.eighth_le_ellGaussianProb_combinedAccept
        hn1 hbodyM hbodyC hbodyBall hbodyTop hdelta hdeltan hs)
  have hpair : TVLe
      (sampleFromKernel
        (gaussianWarmFallbackPhaseKernel body hbodyM delta s c hdelta hcne
          (fun _ ↦ deadline (M / eta)) L (fallback i)) rho)
      (scoreSeedReference c
        (Measure.map (combinedOutput c)
          (condOn (SpeedyRejection.proposal pi) (combinedAccept body c s))))
      (32 * zeta + (eta + continuingContraction ^ L)) := by
    rw [sampleFrom_gaussianWarmFallbackPhaseKernel]
    exact tvLe_gaussianWarmFallbackPhase_selective_zeroSafe
      hbodyM hdelta hcne deadline rhoPair (fallback i) L
      (pi := pi) (tau := pi) heta0 hkilled hmix heighth hzeta16
  have hideal : Measure.map (combinedOutput c)
        (condOn (SpeedyRejection.proposal pi) (combinedAccept body c s)) =
      coolLaw m sigmaSq body i := by
    simpa only [pi, body, delta, s, c] using
      (Ttc.CVIdealCombinedAccepted.map_combinedOutput_condOn_ellGaussianProb_eq_coolLaw
        hn1 hsigma hbodyM hbodyC hbodyBall hbodyTop hdelta hdeltan hi)
  rw [hideal] at hpair
  have hlocalKernel :
      radiusQWarmFallbackKernelOfSigma hn1 q hq0 K hK sigmaSq hsigma
          steps retries fallback i =
        gaussianWarmFallbackPhaseKernel body hbodyM delta s c hdelta hcne
          (fun _ ↦ deadline (M / eta)) L (fallback i) := by
    unfold radiusQWarmFallbackKernelOfSigma
    rw [hsteps, hretries]
  rw [hlocalKernel]
  simpa only [c] using hpair

#print axioms
  tvLe_radiusQWarmFallbackKernelOfSigma_localPair_adjustable_zeroSafe_of_eq

end Ttc.CVSlowRadiusQOperationalPair
