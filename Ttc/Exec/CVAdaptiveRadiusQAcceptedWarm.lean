import Ttc.Exec.CVColdAcceptedWarm
import Ttc.Exec.CVAdaptiveRadiusQCrossWarm

/-! Accepted-sublaw warmth for adaptive phases on expanding `q`-radius bodies. -/

set_option autoImplicit false

namespace Ttc.CVAdaptiveRadiusQAcceptedWarm

open MeasureTheory ProbabilityTheory Metric Set Pointwise
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryGaussian
open Ttc.FiniteContinuingRetryGaussianAugmentedPhase
open Ttc.FiniteContinuingRetryRandomFallback
open Ttc.FiniteContinuingRetryProjectedWarm
open Ttc.FiniteContinuingRetryEmbeddedSelective
open Ttc.CVGaussianAugmentedSelectiveTV
open Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.CVCombinedContinuingAccept
open Ttc.CVCombinedContinuingRetryPhaseTV
open Ttc.CVColdAcceptedWarm
open Ttc.CVAdaptiveRadiusQCrossWarm
open Ttc.CVAdaptiveRadiusQPrimitives
open Ttc.CVSourceTruncatedFixedCost
open scoped ENNReal Classical BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

private theorem restrict_le_condOn_probability
    {E : Type*} [MeasurableSpace E] (mu : Measure E) [IsProbabilityMeasure mu]
    (A : Set E) (hA : MeasurableSet A) : mu.restrict A <= Arlib.condOn mu A := by
  rw [Measure.le_iff]
  intro T hT
  rw [Measure.restrict_apply hT, Arlib.condOn_apply mu hA hT]
  by_cases h0 : mu A = 0
  · have hz : mu (T ∩ A) = 0 := measure_mono_null inter_subset_right h0
    simp [hz]
  · rw [ENNReal.div_eq_inv_mul]
    calc
      mu (T ∩ A) = 1 * mu (T ∩ A) := by rw [one_mul]
      _ <= (mu A)⁻¹ * mu (T ∩ A) := by
        gcongr
        exact ENNReal.one_le_inv.mpr prob_le_one

/-- The first-hit accepted seed is warm for any target that is cross-warm from the
shrunk current cool law.  This is the body/delta-parametric version needed by a
single globally selected truncation radius. -/
theorem isWarm_seed_acceptedOutputSubmeasure_radiusQ_of_cross
    (hn : 1 <= n) {q : Real} (hq : 0 < q)
    {m : Nat} {sigmaSq : Nat -> Real} (hsigma : forall j, 0 < sigmaSq j)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m)
    (hrad : 1 <= q * Real.sqrt (sigmaSq i) * Real.sqrt n)
    (target : Measure (State n)) {Ccross : ENNReal}
    (hcross : IsWarm Ccross
      (Measure.map (fun y : State n => (1 - 1 / (2 * (n : Real))) • y)
        (coolLaw m sigmaSq (radiusQBody q K (sigmaSq i)) i)) target)
    {rho : Measure (State n)} [IsProbabilityMeasure rho] {M : ENNReal}
    (hwarm : IsWarm M rho
      (ellGaussianProb (radiusQBody q K (sigmaSq i))
        (radiusQDelta n q (sigmaSq i)) (sigmaSq i)))
    (steps : Nat -> Nat) (L : Nat) :
    IsWarm ((L : ENNReal) * ((16 * Ccross) * M))
      (Measure.map Prod.snd
        (acceptedOutputSubmeasure
          (augmentedMarginalOf
            (radiusQBody q K (sigmaSq i))
            (measurableSet_radiusQBody hK)
            (radiusQDelta n q (sigmaSq i)) (sigmaSq i)
            (1 - 1 / (2 * (n : Real)))
            (radiusQDelta_pos hn hq (hsigma i))
            (by
              have hnR : (1 : Real) <= n := by exact_mod_cast hn
              have hhalf : 1 / (2 * (n : Real)) <= 1 / 2 := by
                rw [div_le_div_iff₀ (by positivity) (by norm_num)]
                linarith
              linarith)
            steps
            (Measure.map (seedEmbedding (1 - 1 / (2 * (n : Real)))) rho) L)))
      target := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  let Ki := radiusQBody q K (sigmaSq i)
  let di := radiusQDelta n q (sigmaSq i)
  let si := sigmaSq i
  have hsi : 0 < si := hsigma i
  have hdi : 0 < di := radiusQDelta_pos hn hq hsi
  have hc0 : 0 < c := by
    dsimp [c]
    have hnR : (1 : Real) <= n := by exact_mod_cast hn
    have hhalf : 1 / (2 * (n : Real)) <= 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hKim : MeasurableSet Ki := measurableSet_radiusQBody hK
  have hKic : Convex Real Ki := convex_radiusQBody hKc
  have hKiball : ball (0 : State n) 1 ⊆ Ki :=
    unitBall_subset_inter_closedBall hball hrad
  have hKifin : volume Ki ≠ ⊤ := volume_inter_closedBall_ne_top K _
  have hmass0 : ellGaussianMeasure Ki di si Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero_of_ball hKim hKic hKiball hc0
      (by dsimp [c]; exact sub_lt_self 1 (by positivity)) hdi
      (by simpa [c, di, one_div, mul_comm] using
        (radiusQDelta_le_n n q si)) hsi
  have hmassTop : ellGaussianMeasure Ki di si Set.univ ≠ ⊤ :=
    ellGaussianMeasure_univ_ne_top hsi Ki di hKifin
  let pi := ellGaussianProb Ki di si
  letI : IsProbabilityMeasure pi := isProbabilityMeasure_ellGaussianProb hmass0 hmassTop
  let rhoPair := Measure.map (seedEmbedding c) rho
  letI : IsProbabilityMeasure rhoPair :=
    Measure.isProbabilityMeasure_map (measurable_seedEmbedding c).aemeasurable
  apply isWarm_map_seed_acceptedOutputSubmeasure_of_running
    (phaseCandidate Ki hKim di si hdi steps)
    (costedCombinedAccept Ki c si) (measurableSet_costedCombinedAccept hKim hc0.ne')
    rejectedNext measurable_rejectedNext
    (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
    roundQueryCost measurable_roundQueryCost augmentedEmbedding measurable_augmentedEmbedding
    (by intro z; simp [augmentedEmbedding, accepted]) rhoPair Prod.snd measurable_snd
    pi target L
  · simpa only [augmentedMarginalOf, Ki, di, si, pi, rhoPair, c] using
      (Ttc.CVGaussianWarmFallbackAnalytic.isWarm_runningCurrent_augmentedMarginalOf_gaussian
        hKim hdi hc0.ne' rho hwarm steps)
  · intro j
    let nu := sampleFromKernel
      (combinedRoundCostedKernel Ki hKim di si hdi (steps j)) pi
    have hpair : Measure.map Prod.snd nu = SpeedyRejection.proposal pi := by
      dsimp only [nu]
      rw [map_snd_sampleFrom_combinedRoundCostedKernel hKim di si hdi]
      rw [← iterate_eq_sampleFrom_iteratedKernel,
        iterate_invariant ((isReversible_lazy
          (isReversible_speedyMetropolisGaussian_prob hKim di si)).invariant) (steps j)]
    have htv : TVLe (Measure.map Prod.snd nu) (SpeedyRejection.proposal pi) 0 := by
      rw [hpair]
      exact TVLe.refl _
    have hscore := Ttc.CVGaussianAcceptedWarm.isWarm_costedCombinedAccepted
      hKim hdi hc0.ne' (inferInstance : IsProbabilityMeasure pi)
      (IsWarm.refl pi) (steps j) htv
      (Ttc.CVIdealCombinedAccepted.eighth_le_ellGaussianProb_combinedAccept
        hn hKim hKic hKiball hKifin hdi
          (by simpa [di] using (radiusQDelta_le_n n q si)) hsi)
      (by simp)
    have hideal :=
      Ttc.CVIdealCombinedAccepted.map_combinedOutput_condOn_ellGaussianProb_eq_coolLaw
        (m := m) (sigmaSq := sigmaSq) (i := i) hn hsigma
        hKim hKic hKiball hKifin hdi
        (by simpa [di] using (radiusQDelta_le_n n q si))
        (Nat.lt_of_succ_lt hi)
    have hseed : IsWarm 16
        (Measure.map rejectedNext
          (Arlib.condOn nu (costedCombinedAccept Ki c si)))
        (Measure.map (fun y : State n => c • y) (coolLaw m sigmaSq Ki i)) := by
      have hs := Arlib.MarkovChains.isWarm_map (measurable_const_smul c) hscore
      rw [Measure.map_map (measurable_const_smul c) (measurable_acceptedOutput c)] at hs
      have hfun : (fun y : State n => c • y) ∘ acceptedOutput c = rejectedNext := by
        funext z
        unfold acceptedOutput rejectedNext
        simp [Ttc.CVCombinedContinuingAccept.combinedOutput,
          Ttc.CVCombinedContinuingAccept.combinedNext, hc0.ne']
      rw [hfun, hideal] at hs
      simpa only [mul_one, nu] using hs
    have hw := hseed.trans (by simpa only [c, Ki] using hcross)
    have hle : pi.bind
        (acceptedProjectedKernel (phaseCandidate Ki hKim di si hdi steps)
          (costedCombinedAccept Ki c si)
          (measurableSet_costedCombinedAccept hKim hc0.ne')
          (Prod.snd ∘ augmentedAcceptedOutput c)
          (measurable_snd.comp (measurable_augmentedAcceptedOutput c)) j) <=
        Measure.map rejectedNext
          (Arlib.condOn nu (costedCombinedAccept Ki c si)) := by
      change pi.bind
          (acceptedProjectedKernel (phaseCandidate Ki hKim di si hdi steps)
            (costedCombinedAccept Ki c si)
            (measurableSet_costedCombinedAccept (s := si) hKim hc0.ne')
            rejectedNext measurable_rejectedNext j) <= _
      rw [Measure.le_iff]
      intro T hT
      rw [Measure.bind_apply hT
        (acceptedProjectedKernel (phaseCandidate Ki hKim di si hdi steps)
          (costedCombinedAccept Ki c si)
          (measurableSet_costedCombinedAccept (s := si) hKim hc0.ne') rejectedNext
          measurable_rejectedNext j).aemeasurable,
        Measure.map_apply measurable_rejectedNext hT]
      simp_rw [acceptedProjectedKernel, Kernel.map_apply _ measurable_rejectedNext,
        Measure.map_apply measurable_rejectedNext hT]
      have hrestrict : (nu.restrict (costedCombinedAccept Ki c si))
          (rejectedNext ⁻¹' T) =
          ∫⁻ a, ((phaseCandidate Ki hKim di si hdi steps j).restrict
            (measurableSet_costedCombinedAccept (s := si) hKim hc0.ne')) a
              (rejectedNext ⁻¹' T) ∂pi := by
        rw [Measure.restrict_apply (hT.preimage measurable_rejectedNext)]
        dsimp only [nu, sampleFromKernel]
        rw [Measure.bind_apply
          ((hT.preimage measurable_rejectedNext).inter
            (measurableSet_costedCombinedAccept (s := si) hKim hc0.ne'))
          (combinedRoundCostedKernel Ki hKim di si hdi (steps j)).aemeasurable]
        apply lintegral_congr
        intro a
        rw [phaseCandidate, Kernel.restrict_apply']
        exact hT.preimage measurable_rejectedNext
      rw [← hrestrict]
      exact restrict_le_condOn_probability nu
        (costedCombinedAccept Ki c si)
        (measurableSet_costedCombinedAccept (s := si) hKim hc0.ne') _
    exact IsWarm.of_le hle hw |>.mono (by simp [mul_assoc])

/-- Concrete hybrid successor theorem used by the recursive operational sampler. -/
theorem isWarm_seed_acceptedOutputSubmeasure_radiusQ_hybrid
    (hn : 1 <= n) {q : Real} (hq : 0 < q)
    {m : Nat} {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m)
    (hrate0 : 0 <= Ttc.CVHybridSchedule.phaseRate n N s0 i)
    (hrad : 1 <= q * Real.sqrt
      (Ttc.CVHybridSchedule.sigmaSq n N s0 i) * Real.sqrt n)
    {rho : Measure (State n)} [IsProbabilityMeasure rho] {M : ENNReal}
    (hwarm : IsWarm M rho
      (ellGaussianProb
        (radiusQBody q K (Ttc.CVHybridSchedule.sigmaSq n N s0 i))
        (radiusQDelta n q (Ttc.CVHybridSchedule.sigmaSq n N s0 i))
        (Ttc.CVHybridSchedule.sigmaSq n N s0 i)))
    (steps : Nat -> Nat) (L : Nat) :
    IsWarm ((L : ENNReal) *
      ((16 * adaptiveRadiusQWarmFactor n
        (1 + Ttc.CVHybridSchedule.phaseRate n N s0 i)) * M))
      (Measure.map Prod.snd
        (acceptedOutputSubmeasure
          (augmentedMarginalOf
            (radiusQBody q K (Ttc.CVHybridSchedule.sigmaSq n N s0 i))
            (measurableSet_radiusQBody hK)
            (radiusQDelta n q (Ttc.CVHybridSchedule.sigmaSq n N s0 i))
            (Ttc.CVHybridSchedule.sigmaSq n N s0 i)
            (1 - 1 / (2 * (n : Real)))
            (radiusQDelta_pos hn hq
              (Ttc.CVHybridSchedule.sigmaSq_pos hn hN hs0 i))
            (by
              have hnR : (1 : Real) <= n := by exact_mod_cast hn
              have hhalf : 1 / (2 * (n : Real)) <= 1 / 2 := by
                rw [div_le_div_iff₀ (by positivity) (by norm_num)]
                linarith
              linarith)
            steps
            (Measure.map (seedEmbedding (1 - 1 / (2 * (n : Real)))) rho) L)))
      (ellGaussianProb
        (radiusQBody q K (Ttc.CVHybridSchedule.sigmaSq n N s0 (i + 1)))
        (radiusQDelta n q (Ttc.CVHybridSchedule.sigmaSq n N s0 (i + 1)))
        (Ttc.CVHybridSchedule.sigmaSq n N s0 (i + 1))) := by
  apply isWarm_seed_acceptedOutputSubmeasure_radiusQ_of_cross
    hn hq (Ttc.CVHybridSchedule.sigmaSq_pos hn hN hs0) hK hKc hball hfin hi hrad _
    (isWarm_standardScaledTruncated_ellGaussianProb_radiusQ_hybrid
      hn hq hN hs0 hK hKc hball hi hrate0 hrad)
    hwarm steps L

#print axioms isWarm_seed_acceptedOutputSubmeasure_radiusQ_of_cross
#print axioms isWarm_seed_acceptedOutputSubmeasure_radiusQ_hybrid

end Ttc.CVAdaptiveRadiusQAcceptedWarm
