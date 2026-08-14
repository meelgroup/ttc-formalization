import Ttc.Exec.CVColdOperationalPairTV
import Ttc.Exec.CVIdealCombinedAccepted
import Arlib.Probability.TVTensor

/-!
# Product reference after an independent cold-seed reset

Projecting the operational cold pair law to its score coordinate preserves its TV bound.
Afterwards, tensoring both the actual score law and its exact cooling target with the same
independently drawn reset seed preserves the bound again.  This is the distributional
interface for a post-phase seed-refresh kernel: the target is a product, not the old
score/seed graph law.
-/

set_option autoImplicit false

namespace Ttc.CVColdOperationalResetTV

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler
open Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.CVCombinedContinuingAccept
open Ttc.CVColdOperationalKernel
open Ttc.CVColdOperationalPairTV
open Ttc.CVCorrectedFixedBlockCost
open Ttc.CVSourceTruncatedFixedCost
open Ttc.CVContinuingRetryParameters
open scoped ENNReal Classical

variable {n m : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- After discarding the old raw seed and independently drawing `resetSeed`, the complete
new `(score,seed)` law is close to the exact product of the truncated cooling score law and
`resetSeed`.  Independent refresh costs no additional TV error. -/
theorem tvLe_coldGaussian_score_prod_resetSeed_adjustable_zeroSafe
    (hn : 21 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (s0 : Real) (hs0 : 0 < s0) (i : Nat) (hi : i < m)
    (rho : Measure (State n)) [IsProbabilityMeasure rho]
    (resetSeed : Measure (State n)) [IsProbabilityMeasure resetSeed]
    {M eta zeta : ENNReal} (hM1 : 1 ≤ M) (hMtop : M ≠ ⊤)
    (heta0 : eta ≠ 0) (hetatop : eta ≠ ⊤) (heta1 : eta ≤ 1)
    (hzeta0 : zeta ≠ 0) (hzetatop : zeta ≠ ⊤)
    (hzeta16 : zeta ≤ ENNReal.ofReal (1 / 16 : Real))
    (hrad : 1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hwarm : IsWarm M rho
      (ellGaussianProb
        (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
        (fixedSigmaSq n s0 i)))
    (L : Nat) :
    let delta := fixedRadiusFourDelta n (fixedSigmaSq n s0 i)
    let s := fixedSigmaSq n s0 i
    let deadline := fun W : ENNReal ↦
      Ttc.CVGaussianAdaptiveMixing.adjustableSpeedyDeadline n delta s W zeta
    let retrySteps : Nat → Nat → Nat := fun _ _ ↦ deadline (M / eta)
    let retries : Nat → Nat := fun _ ↦ L
    TVLe
      ((Measure.map Prod.fst
        (sampleFromKernel
          (coldGaussianKernel (by omega : 1 ≤ n) K hK s0 hs0
            retrySteps retries i) rho)).prod resetSeed)
      ((coolLaw m (fixedSigmaSq n s0)
        (fixedRadiusFourBody K s) i).prod resetSeed)
      (32 * zeta + (eta + continuingContraction ^ L)) := by
  dsimp only
  let s := fixedSigmaSq n s0 i
  let delta := fixedRadiusFourDelta n s
  let body := fixedRadiusFourBody K s
  let c : Real := 1 - 1 / (2 * (n : Real))
  let deadline := fun W : ENNReal ↦
    Ttc.CVGaussianAdaptiveMixing.adjustableSpeedyDeadline n delta s W zeta
  let retrySteps : Nat → Nat → Nat := fun _ _ ↦ deadline (M / eta)
  let retries : Nat → Nat := fun _ ↦ L
  have hn1 : 1 ≤ n := by omega
  have hsigma : ∀ j, 0 < fixedSigmaSq n s0 j := by
    intro j
    unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) j
  have hs : 0 < s := by simpa only [s] using hsigma i
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact fixedRadiusFourDelta_pos hn1 hs
  have hdeltan : delta ≤ 1 / (2 * (n : Real)) := fixedRadiusFourDelta_le_n
  have hbodyM : MeasurableSet body := measurableSet_fixedRadiusFourBody hK _
  have hbodyC : Convex Real body := convex_fixedRadiusFourBody hKc _
  have hbodyBall : ball (0 : State n) 1 ⊆ body :=
    unitBall_subset_inter_closedBall hball hrad
  have hbodyTop : volume body ≠ ⊤ := volume_inter_closedBall_ne_top K _
  let scoreTarget : Measure (State n) := Measure.map (combinedOutput c)
    (condOn
      (SpeedyRejection.proposal (ellGaussianProb body delta s))
      (combinedAccept body c s))
  have hpair := tvLe_coldGaussianKernel_adjustable_zeroSafe
    hn K hK hKc hball s0 hs0 i rho hM1 hMtop heta0 hetatop heta1
      hzeta0 hzetatop hzeta16 hrad hwarm L
  have hscore : TVLe
      (Measure.map Prod.fst
        (sampleFromKernel
          (coldGaussianKernel hn1 K hK s0 hs0 retrySteps retries i) rho))
      scoreTarget
      (32 * zeta + (eta + continuingContraction ^ L)) := by
    have hmapped := hpair.map (measurable_fst : Measurable
      (Prod.fst : State n × State n → State n))
    rw [map_fst_scoreSeedReference] at hmapped
    simpa only [s, delta, body, c, deadline, retrySteps, retries, scoreTarget] using hmapped
  have hideal : scoreTarget = coolLaw m (fixedSigmaSq n s0) body i := by
    simpa only [scoreTarget, body, delta, s, c] using
      (Ttc.CVIdealCombinedAccepted.map_combinedOutput_condOn_ellGaussianProb_eq_coolLaw
        hn1 hsigma hbodyM hbodyC hbodyBall hbodyTop hdelta hdeltan hi)
  rw [hideal] at hscore
  let actualScore := Measure.map Prod.fst
    (sampleFromKernel
      (coldGaussianKernel hn1 K hK s0 hs0 retrySteps retries i) rho)
  letI : IsProbabilityMeasure
      (sampleFromKernel
        (coldGaussianKernel hn1 K hK s0 hs0 retrySteps retries i) rho) := by
    infer_instance
  letI : IsProbabilityMeasure actualScore := by
    dsimp only [actualScore]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure (coolLaw m (fixedSigmaSq n s0) body i) :=
    coolLaw_isProbabilityMeasure hsigma hbodyBall hbodyTop i
  have hprod := hscore.prod (TVLe.refl resetSeed)
  simpa only [actualScore, body, s, delta, deadline, retrySteps, retries, add_zero] using hprod

/-- Global-schedule wrapper.  Only the current phase's retry policy is inspected. -/
theorem tvLe_coldGaussian_score_prod_resetSeed_adjustable_zeroSafe_of_eq
    (hn : 21 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (s0 : Real) (hs0 : 0 < s0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (i : Nat) (hi : i < m)
    (rho : Measure (State n)) [IsProbabilityMeasure rho]
    (resetSeed : Measure (State n)) [IsProbabilityMeasure resetSeed]
    {M eta zeta : ENNReal} (hM1 : 1 ≤ M) (hMtop : M ≠ ⊤)
    (heta0 : eta ≠ 0) (hetatop : eta ≠ ⊤) (heta1 : eta ≤ 1)
    (hzeta0 : zeta ≠ 0) (hzetatop : zeta ≠ ⊤)
    (hzeta16 : zeta ≤ ENNReal.ofReal (1 / 16 : Real))
    (hrad : 1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hwarm : IsWarm M rho
      (ellGaussianProb
        (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
        (fixedSigmaSq n s0 i)))
    (L : Nat)
    (hsteps : retrySteps i = fun _ ↦
      Ttc.CVGaussianAdaptiveMixing.adjustableSpeedyDeadline n
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
        (fixedSigmaSq n s0 i) (M / eta) zeta)
    (hretries : retries i = L) :
    TVLe
      ((Measure.map Prod.fst
        (sampleFromKernel
          (coldGaussianKernel (by omega : 1 ≤ n) K hK s0 hs0
            retrySteps retries i) rho)).prod resetSeed)
      ((coolLaw m (fixedSigmaSq n s0)
        (fixedRadiusFourBody K (fixedSigmaSq n s0 i)) i).prod resetSeed)
      (32 * zeta + (eta + continuingContraction ^ L)) := by
  let delta := fixedRadiusFourDelta n (fixedSigmaSq n s0 i)
  let s := fixedSigmaSq n s0 i
  let deadline := fun W : ENNReal ↦
    Ttc.CVGaussianAdaptiveMixing.adjustableSpeedyDeadline n delta s W zeta
  let localSteps : Nat → Nat → Nat := fun _ _ ↦ deadline (M / eta)
  let localRetries : Nat → Nat := fun _ ↦ L
  have hlocal := tvLe_coldGaussian_score_prod_resetSeed_adjustable_zeroSafe
    (m := m) hn K hK hKc hball s0 hs0 i hi rho resetSeed
      hM1 hMtop heta0 hetatop heta1 hzeta0 hzetatop hzeta16 hrad hwarm L
  have hkernel :
      coldGaussianKernel (by omega : 1 ≤ n) K hK s0 hs0
          retrySteps retries i =
        coldGaussianKernel (by omega : 1 ≤ n) K hK s0 hs0
          localSteps localRetries i := by
    unfold coldGaussianKernel coldGaussianCostedKernel
    rw [hsteps, hretries]
  rw [hkernel]
  simpa only [delta, s, deadline, localSteps, localRetries] using hlocal

#print axioms tvLe_coldGaussian_score_prod_resetSeed_adjustable_zeroSafe
#print axioms tvLe_coldGaussian_score_prod_resetSeed_adjustable_zeroSafe_of_eq

end Ttc.CVColdOperationalResetTV
