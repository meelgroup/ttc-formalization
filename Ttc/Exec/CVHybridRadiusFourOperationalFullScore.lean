import Ttc.Exec.CVHybridRadiusFourFullScore
import Ttc.Exec.CVGaussianWarmFallbackZeroSafe
import Ttc.Exec.CVGaussianAdaptiveMixing

/-!
# Operational full-score accuracy on the hybrid radius-four schedule

This file keeps the walk on the phasewise radius-four body, proves the ordinary
zero-safe selective-TV statement there with `q = 4`, projects away the raw seed, and
then pays the radius-four tail to recover the public full-body cooling score law.
-/

set_option autoImplicit false

namespace Ttc.CVHybridRadiusFourOperationalFullScore

open MeasureTheory ProbabilityTheory Metric Set Pointwise
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler
open Ttc.CVHybridSchedule
open Ttc.CVHybridRadiusFourFallbackSchedule
open Ttc.CVHybridRadiusFourFullScore
open Ttc.CVSourceTruncatedFixedCost
open Ttc.CVGaussianWarmFallbackPhaseKernel
open Ttc.CVGaussianWarmFallbackZeroSafe
open Ttc.CVGaussianWarmFallbackAnalytic
open Ttc.CVGaussianAugmentedSelectiveTV
open Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.CVCombinedContinuingAccept
open Ttc.CVContinuingRetryParameters
open Ttc.FiniteContinuingRetryProjectedWarm
open scoped ENNReal Classical BigOperators

variable {n m : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- Every operational hybrid phase can stay on its radius-four truncation while its
score marginal targets the full-body cooling law.  The local mixing term is the usual
zero-safe retry error; the final summand is the dimension-exponential truncation tail.
-/
theorem tvLe_hybridRadiusFourWarmFallbackKernel_fullPair_adjustable_zeroSafe_of_eq
    (hn : 21 ≤ n) {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ j, IsProbabilityMeasure (fallback j)]
    (i : Nat) (hi : i < m)
    (rho : Measure (State n)) [IsProbabilityMeasure rho]
    {M eta zeta : ENNReal} (hM1 : 1 ≤ M) (hMtop : M ≠ ⊤)
    (heta0 : eta ≠ 0) (hetatop : eta ≠ ⊤) (heta1 : eta ≤ 1)
    (hzeta0 : zeta ≠ 0) (hzetatop : zeta ≠ ⊤)
    (hzeta16 : zeta ≤ ENNReal.ofReal (1 / 16 : Real))
    (hrad : 1 ≤ 4 * Real.sqrt (sigmaSq n N s0 i) * Real.sqrt n)
    (hwarm : IsWarm M rho
      (ellGaussianProb
        (fixedRadiusFourBody K (sigmaSq n N s0 i))
        (fixedRadiusFourDelta n (sigmaSq n N s0 i))
        (sigmaSq n N s0 i)))
    (L : Nat)
    (hsteps : steps i = fun _ ↦
      Ttc.CVGaussianAdaptiveMixing.adjustableSpeedyDeadline n
        (fixedRadiusFourDelta n (sigmaSq n N s0 i))
        (sigmaSq n N s0 i) (M / eta) zeta)
    (hretries : retries i = L) :
    TVLe
      (sampleFromKernel
        (hybridRadiusFourWarmFallbackKernel (by omega : 1 ≤ n)
          K hK N s0 hN hs0 steps retries fallback i) rho)
      (scoreSeedReference (1 - 1 / (2 * (n : Real)))
        (coolLaw m (sigmaSq n N s0) K i))
      (32 * zeta + (eta + continuingContraction ^ L) +
        ENNReal.ofReal ((4 * Real.exp (-(15 : Real) / 2)) ^ n)) := by
  have hn1 : 1 ≤ n := by omega
  let s := sigmaSq n N s0 i
  let delta := fixedRadiusFourDelta n s
  let body := fixedRadiusFourBody K s
  let c : Real := 1 - 1 / (2 * (n : Real))
  let pi := ellGaussianProb body delta s
  let deadline := fun W : ENNReal ↦
    Ttc.CVGaussianAdaptiveMixing.adjustableSpeedyDeadline n delta s W zeta
  have hs : 0 < s := by
    simpa only [s] using sigmaSq_pos hn1 hN hs0 i
  have hdelta : 0 < delta := fixedRadiusFourDelta_pos hn1 hs
  have hbodyM : MeasurableSet body := measurableSet_fixedRadiusFourBody hK _
  have hbodyC : Convex Real body := convex_fixedRadiusFourBody hKc _
  have hbodyBall : ball (0 : State n) 1 ⊆ body :=
    unitBall_subset_inter_closedBall hball (by simpa only [s] using hrad)
  have hbody0 : volume body ≠ 0 :=
    volume_inter_closedBall_ne_zero hball (by simpa only [s] using hrad)
  have hbodyTop : volume body ≠ ⊤ := volume_inter_closedBall_ne_top K _
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
  have hdeltan : delta ≤ 1 / (2 * (n : Real)) := fixedRadiusFourDelta_le_n
  have hdeltaC : delta ≤ 1 - c := by
    dsimp only [c]
    linarith
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
      (q := 4) (R := 4 * Real.sqrt s * Real.sqrt n)
      hn (by norm_num) hs hdelta
      (by
        simpa only [body, delta, s,
          max_eq_left (by norm_num : (8 : Real) ≥ 2 * 4)] using
          (fixedRadiusFourDelta_le_radius (n := n) (s := s)))
      hbodyM hbodyC hbody0 (by positivity)
      (fun x hx ↦ norm_le_fixedRadiusFour hx) le_rfl
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
      coolLaw m (sigmaSq n N s0) body i := by
    simpa only [pi, body, delta, s, c] using
      (Ttc.CVIdealCombinedAccepted.map_combinedOutput_condOn_ellGaussianProb_eq_coolLaw
        hn1 (sigmaSq_pos hn1 hN hs0) hbodyM hbodyC hbodyBall hbodyTop
        hdelta hdeltan hi)
  rw [hideal] at hpair
  have htail := tvLe_hybridRadiusFour_coolLaw_full
    (m := m) hn1 hN hs0 hK hKc hball hfin hi hrad
  have hlocalKernel :
      hybridRadiusFourWarmFallbackKernel hn1 K hK N s0 hN hs0
          steps retries fallback i =
        gaussianWarmFallbackPhaseKernel body hbodyM delta s c hdelta hcne
          (fun _ ↦ deadline (M / eta)) L (fallback i) := by
    unfold hybridRadiusFourWarmFallbackKernel hybridRadiusFourBody
      hybridRadiusFourDelta
    rw [hsteps, hretries]
  rw [hlocalKernel]
  have htailPair := htail.map
    (by fun_prop : Measurable (fun y : State n ↦ (y, c • y)))
  exact hpair.trans (by
    simpa only [scoreSeedReference, body, s, c, add_assoc] using htailPair)

/-- Score-marginal corollary of the preceding complete graph-law theorem. -/
theorem tvLe_hybridRadiusFourWarmFallbackKernel_fullScore_adjustable_zeroSafe_of_eq
    (hn : 21 ≤ n) {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ j, IsProbabilityMeasure (fallback j)]
    (i : Nat) (hi : i < m)
    (rho : Measure (State n)) [IsProbabilityMeasure rho]
    {M eta zeta : ENNReal} (hM1 : 1 ≤ M) (hMtop : M ≠ ⊤)
    (heta0 : eta ≠ 0) (hetatop : eta ≠ ⊤) (heta1 : eta ≤ 1)
    (hzeta0 : zeta ≠ 0) (hzetatop : zeta ≠ ⊤)
    (hzeta16 : zeta ≤ ENNReal.ofReal (1 / 16 : Real))
    (hrad : 1 ≤ 4 * Real.sqrt (sigmaSq n N s0 i) * Real.sqrt n)
    (hwarm : IsWarm M rho
      (ellGaussianProb
        (fixedRadiusFourBody K (sigmaSq n N s0 i))
        (fixedRadiusFourDelta n (sigmaSq n N s0 i))
        (sigmaSq n N s0 i)))
    (L : Nat)
    (hsteps : steps i = fun _ ↦
      Ttc.CVGaussianAdaptiveMixing.adjustableSpeedyDeadline n
        (fixedRadiusFourDelta n (sigmaSq n N s0 i))
        (sigmaSq n N s0 i) (M / eta) zeta)
    (hretries : retries i = L) :
    TVLe
      (Measure.map Prod.fst
        (sampleFromKernel
          (hybridRadiusFourWarmFallbackKernel (by omega : 1 ≤ n)
            K hK N s0 hN hs0 steps retries fallback i) rho))
      (coolLaw m (sigmaSq n N s0) K i)
      (32 * zeta + (eta + continuingContraction ^ L) +
        ENNReal.ofReal ((4 * Real.exp (-(15 : Real) / 2)) ^ n)) := by
  have hpair :=
    tvLe_hybridRadiusFourWarmFallbackKernel_fullPair_adjustable_zeroSafe_of_eq
      (m := m) hn hN hs0 hK hKc hball hfin steps retries fallback i hi rho
      hM1 hMtop heta0 hetatop heta1 hzeta0 hzetatop hzeta16 hrad hwarm L
      hsteps hretries
  have hscore := hpair.map
    (measurable_fst : Measurable (Prod.fst : ScoreSeed n → State n))
  rw [map_fst_scoreSeedReference] at hscore
  exact hscore

#print axioms
  tvLe_hybridRadiusFourWarmFallbackKernel_fullPair_adjustable_zeroSafe_of_eq
#print axioms
  tvLe_hybridRadiusFourWarmFallbackKernel_fullScore_adjustable_zeroSafe_of_eq

end Ttc.CVHybridRadiusFourOperationalFullScore
