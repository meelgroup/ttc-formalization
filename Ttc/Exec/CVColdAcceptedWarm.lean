import Ttc.Exec.CVColdCrossPhaseWarm
import Ttc.Exec.CVGaussianWarmFallbackAnalytic

/-! Accepted-sublaw warmth for changing radius-four cold phases. -/

namespace Ttc.CVColdAcceptedWarm

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
open Ttc.CVColdCrossPhaseWarm
open Ttc.CVCorrectedFixedBlockCost
open Ttc.CVSourceTruncatedFixedCost
open scoped ENNReal Classical BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

private theorem restrict_le_condOn_probability
    {E : Type*} [MeasurableSpace E] (mu : Measure E) [IsProbabilityMeasure mu]
    (A : Set E) (hA : MeasurableSet A) : mu.restrict A ≤ Arlib.condOn mu A := by
  rw [Measure.le_iff]
  intro T hT
  rw [Measure.restrict_apply hT, Arlib.condOn_apply mu hA hT]
  by_cases h0 : mu A = 0
  · have hz : mu (T ∩ A) = 0 := measure_mono_null inter_subset_right h0
    simp [hz]
  · rw [ENNReal.div_eq_inv_mul]
    calc
      mu (T ∩ A) = 1 * mu (T ∩ A) := by rw [one_mul]
      _ ≤ (mu A)⁻¹ * mu (T ∩ A) := by
        gcongr
        exact ENNReal.one_le_inv.mpr prob_le_one

/-- Projected accepted warmth from an already-established surviving-current invariant.
This is the generic final step of the first-hit argument, exposed without asking callers
to re-prove the killed-rejection invariant. -/
theorem isWarm_map_seed_acceptedOutputSubmeasure_of_running
    {X E C F G : Type*}
    [MeasurableSpace X] [MeasurableSpace E] [MeasurableSpace C]
    [MeasurableSpace F] [MeasurableSpace G]
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (embed : X → RetryState E F) (hembed : Measurable embed)
    (hRunning : ∀ x, accepted (embed x) ≠ true)
    (rho : Measure X) [IsProbabilityMeasure rho]
    (seedOut : F → G) (hseedOut : Measurable seedOut)
    (pi : Measure E) (target : Measure G) (L : Nat) {M Cwarm : ENNReal}
    (hrunning : ∀ j, IsWarm M
      (runningCurrent
        (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho j)) pi)
    (haccept : ∀ j, IsWarm Cwarm
      (pi.bind (acceptedProjectedKernel candidate A hA (seedOut ∘ out)
        (hseedOut.comp hout) j)) target) :
    IsWarm ((L : ENNReal) * (Cwarm * M))
      (Measure.map seedOut
        (acceptedOutputSubmeasure
          (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho L)))
      target := by
  rw [map_seed_acceptedOutputSubmeasure_eq_sum_projectedFirstHit candidate A hA next hnext
    out hout roundCost hcost embed hembed hRunning rho seedOut hseedOut L]
  have hinc : ∀ i : Fin L, IsWarm (Cwarm * M)
      (projectedFirstHitIncrement candidate A hA next hnext out hout roundCost hcost
        embed rho (seedOut ∘ out) (hseedOut.comp hout) i) target := by
    intro i
    have hstep := (hrunning i).bind
      (acceptedProjectedKernel candidate A hA (seedOut ∘ out)
        (hseedOut.comp hout) i)
    exact hstep.trans (haccept i) |>.mono (by rw [mul_comm])
  simpa using Arlib.isWarm_sum
    (fun i : Fin L ↦ projectedFirstHitIncrement candidate A hA next hnext out hout
      roundCost hcost embed rho (seedOut ∘ out) (hseedOut.comp hout) i)
    (fun _ : Fin L ↦ Cwarm * M) target hinc

/-- Every accepted cold first-hit seed is warm for the next changing radius-four speedy
target.  The factor is `L * (16 * coldCrossWarmFactor n) * M`: `16` is the acceptance
conditioning price and `coldCrossWarmFactor` is the support-correct body/variance bridge. -/
theorem isWarm_seed_acceptedOutputSubmeasure_cold_of_cross
    (hn : 1 ≤ n) {m : Nat}
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {s0 : Real} (hs0 : 0 < s0) {i : Nat} (hi : i + 1 < m)
    (hrad : 1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hradTwo : 1 ≤ 2 * Real.sqrt (fixedSigmaSq n s0 (i + 1)) * Real.sqrt n)
    (target : Measure (State n))
    (hcross : IsWarm
      (ENNReal.ofReal (((1 - 1 / (2 * (n : Real)))⁻¹) ^ n) *
        (ENNReal.ofReal (Real.exp (1 / 2)) * 2))
      (Measure.map (fun y : State n ↦ (1 - 1 / (2 * (n : Real))) • y)
        (coolLaw m (fixedSigmaSq n s0)
          (fixedRadiusFourBody K (fixedSigmaSq n s0 i)) i)) target)
    {rho : Measure (State n)} [IsProbabilityMeasure rho] {M : ENNReal}
    (hwarm : IsWarm M rho
      (ellGaussianProb (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
        (fixedSigmaSq n s0 i)))
    (steps : Nat → Nat) (L : Nat) :
    IsWarm ((L : ENNReal) * ((16 *
      (ENNReal.ofReal
          (((1 - 1 / (2 * (n : Real)))⁻¹) ^ n) *
        (ENNReal.ofReal (Real.exp (1 / 2)) * 2))) * M))
      (Measure.map Prod.snd
        (acceptedOutputSubmeasure
          (augmentedMarginalOf
            (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
            (measurableSet_fixedRadiusFourBody hK _)
            (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
            (fixedSigmaSq n s0 i)
            (1 - 1 / (2 * (n : Real)))
            (fixedRadiusFourDelta_pos hn (by
              unfold fixedSigmaSq
              exact geomSchedule_pos hs0 (by positivity) i))
            (by
              have hnR : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
              have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
              have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
                rw [div_le_div_iff₀ (by positivity) (by norm_num)]
                linarith
              linarith)
            steps
            (Measure.map (seedEmbedding (1 - 1 / (2 * (n : Real)))) rho) L)))
      target := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  let Ki := fixedRadiusFourBody K (fixedSigmaSq n s0 i)
  let Kj := fixedRadiusFourBody K (fixedSigmaSq n s0 (i + 1))
  let di := fixedRadiusFourDelta n (fixedSigmaSq n s0 i)
  let dj := fixedRadiusFourDelta n (fixedSigmaSq n s0 (i + 1))
  let si := fixedSigmaSq n s0 i
  have hsi : 0 < si := by
    dsimp only [si]
    unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) i
  have hsj : 0 < fixedSigmaSq n s0 (i + 1) := by
    unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) (i + 1)
  have hdi : 0 < di := by exact fixedRadiusFourDelta_pos hn hsi
  have hdj : 0 < dj := by exact fixedRadiusFourDelta_pos hn hsj
  have hc0 : 0 < c := by
    dsimp [c]
    have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
    have : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hKim : MeasurableSet Ki := measurableSet_fixedRadiusFourBody hK _
  have hKic : Convex Real Ki := convex_fixedRadiusFourBody hKc _
  have hKiball : ball (0 : State n) 1 ⊆ Ki :=
    unitBall_subset_inter_closedBall hball hrad
  have hKifin : volume Ki ≠ ⊤ := volume_inter_closedBall_ne_top K _
  have hmass0 : ellGaussianMeasure Ki di si Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero_of_ball hKim hKic hKiball hc0
      (by dsimp [c]; exact sub_lt_self 1 (by positivity)) hdi
      (by simpa [c, di] using (fixedRadiusFourDelta_le_n (n := n) (s := si))) hsi
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
          (by simpa [di] using (fixedRadiusFourDelta_le_n (n := n) (s := si))) hsi)
      (by simp)
    have hideal :=
      Ttc.CVIdealCombinedAccepted.map_combinedOutput_condOn_ellGaussianProb_eq_coolLaw
        (m := m) (sigmaSq := fixedSigmaSq n s0) (i := i)
        hn (fun q ↦ by
          unfold fixedSigmaSq
          exact geomSchedule_pos hs0 (by positivity) q)
        hKim hKic hKiball hKifin hdi
        (by simpa [di] using (fixedRadiusFourDelta_le_n (n := n) (s := si)))
        (Nat.lt_of_succ_lt hi)
    have hseed : IsWarm 16
        (Measure.map rejectedNext
          (Arlib.condOn nu (costedCombinedAccept Ki c si)))
        (Measure.map (fun y : State n ↦ c • y)
          (coolLaw m (fixedSigmaSq n s0) Ki i)) := by
      have hs := Arlib.MarkovChains.isWarm_map (measurable_const_smul c) hscore
      rw [Measure.map_map (measurable_const_smul c) (measurable_acceptedOutput c)] at hs
      have hfun : (fun y : State n ↦ c • y) ∘ acceptedOutput c = rejectedNext := by
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
          (measurable_snd.comp (measurable_augmentedAcceptedOutput c)) j) ≤
        Measure.map rejectedNext
          (Arlib.condOn nu (costedCombinedAccept Ki c si)) := by
      change pi.bind
          (acceptedProjectedKernel (phaseCandidate Ki hKim di si hdi steps)
            (costedCombinedAccept Ki c si)
            (measurableSet_costedCombinedAccept (s := si) hKim hc0.ne')
            rejectedNext measurable_rejectedNext j) ≤ _
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

/-- Cold-to-cold specialization of the cross-target accepted-sublaw theorem. -/
theorem isWarm_seed_acceptedOutputSubmeasure_cold_succ
    (hn : 1 ≤ n) {m : Nat}
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {s0 : Real} (hs0 : 0 < s0) {i : Nat} (hi : i + 1 < m)
    (hrad : 1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hradTwo : 1 ≤ 2 * Real.sqrt (fixedSigmaSq n s0 (i + 1)) * Real.sqrt n)
    {rho : Measure (State n)} [IsProbabilityMeasure rho] {M : ENNReal}
    (hwarm : IsWarm M rho
      (ellGaussianProb (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
        (fixedSigmaSq n s0 i)))
    (steps : Nat → Nat) (L : Nat) :
    IsWarm ((L : ENNReal) * ((16 *
      (ENNReal.ofReal (((1 - 1 / (2 * (n : Real)))⁻¹) ^ n) *
        (ENNReal.ofReal (Real.exp (1 / 2)) * 2))) * M))
      (Measure.map Prod.snd
        (acceptedOutputSubmeasure
          (augmentedMarginalOf
            (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
            (measurableSet_fixedRadiusFourBody hK _)
            (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
            (fixedSigmaSq n s0 i) (1 - 1 / (2 * (n : Real)))
            (fixedRadiusFourDelta_pos hn (by
              unfold fixedSigmaSq
              exact geomSchedule_pos hs0 (by positivity) i))
            (by
              have hnR : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
              have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
              have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
                rw [div_le_div_iff₀ (by positivity) (by norm_num)]
                linarith
              linarith)
            steps (Measure.map (seedEmbedding (1 - 1 / (2 * (n : Real)))) rho) L)))
      (ellGaussianProb (fixedRadiusFourBody K (fixedSigmaSq n s0 (i + 1)))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 (i + 1)))
        (fixedSigmaSq n s0 (i + 1))) := by
  apply isWarm_seed_acceptedOutputSubmeasure_cold_of_cross hn hK hKc hball hfin hs0 hi
    hrad hradTwo _ _ hwarm steps L
  exact isWarm_standardScaledTruncated_ellGaussianProb_succ
    (m := m) hn hs0 hK hKc hball hfin hi hrad hradTwo
      (fixedRadiusFourDelta_pos hn (by
        unfold fixedSigmaSq
        exact geomSchedule_pos hs0 (by positivity) (i + 1)))
      (fixedRadiusFourDelta_le_n (n := n))

/-- Last-cold-to-first-hot specialization.  It has the same accepted warmness factor;
only the support-correct cross theorem changes its target to the full body. -/
theorem isWarm_seed_acceptedOutputSubmeasure_cold_full_succ
    (hn : 1 ≤ n) {m : Nat}
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {s0 : Real} (hs0 : 0 < s0) {i : Nat} (hi : i + 1 < m)
    (hrad : 1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hradTwo : 1 ≤ 2 * Real.sqrt (fixedSigmaSq n s0 (i + 1)) * Real.sqrt n)
    {rho : Measure (State n)} [IsProbabilityMeasure rho] {M : ENNReal}
    (hwarm : IsWarm M rho
      (ellGaussianProb (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
        (fixedSigmaSq n s0 i)))
    (steps : Nat → Nat) (L : Nat) :
    IsWarm ((L : ENNReal) * ((16 *
      (ENNReal.ofReal (((1 - 1 / (2 * (n : Real)))⁻¹) ^ n) *
        (ENNReal.ofReal (Real.exp (1 / 2)) * 2))) * M))
      (Measure.map Prod.snd
        (acceptedOutputSubmeasure
          (augmentedMarginalOf
            (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
            (measurableSet_fixedRadiusFourBody hK _)
            (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
            (fixedSigmaSq n s0 i) (1 - 1 / (2 * (n : Real)))
            (fixedRadiusFourDelta_pos hn (by
              unfold fixedSigmaSq
              exact geomSchedule_pos hs0 (by positivity) i))
            (by
              have hnR : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
              have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
              have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
                rw [div_le_div_iff₀ (by positivity) (by norm_num)]
                linarith
              linarith)
            steps (Measure.map (seedEmbedding (1 - 1 / (2 * (n : Real)))) rho) L)))
      (ellGaussianProb K
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 (i + 1)))
        (fixedSigmaSq n s0 (i + 1))) := by
  apply isWarm_seed_acceptedOutputSubmeasure_cold_of_cross hn hK hKc hball hfin hs0 hi
    hrad hradTwo _ _ hwarm steps L
  exact isWarm_standardScaledTruncated_full_ellGaussianProb_succ
    (m := m) hn hs0 hK hKc hball hfin hi hrad hradTwo
      (fixedRadiusFourDelta_pos hn (by
        unfold fixedSigmaSq
        exact geomSchedule_pos hs0 (by positivity) (i + 1)))
      (fixedRadiusFourDelta_le_n (n := n))

#print axioms isWarm_seed_acceptedOutputSubmeasure_cold_succ
#print axioms isWarm_seed_acceptedOutputSubmeasure_cold_full_succ

end Ttc.CVColdAcceptedWarm
