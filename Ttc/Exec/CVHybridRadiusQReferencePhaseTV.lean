import Ttc.Exec.CVHybridRadiusQOperationalLocalPair
import Ttc.Exec.CVHybridRadiusQReferenceCost
import Ttc.Exec.CVHybridRadiusQSwitchWarm

/-!
The retained-history phase interface for the selected-radius kernel.

The operational theorem is naturally a statement about the complete `(score, seed)`
graph law.  This file records the exact seed-marginal consequence for the costed
kernel.  It is deliberately stated for an arbitrary warm incoming reference law, so
it can be used both before and after the radius switch.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Ttc.CVHybridRadiusQReferencePhaseTV

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler Ttc.CVHybridSchedule
open Ttc.CVAdaptiveRadiusQPrimitives Ttc.CVHybridRadiusQFallbackSchedule
open Ttc.CVHybridRadiusQRecursiveStep
open Ttc.CVHybridRadiusQSwitchWarm
open Ttc.CVHybridRadiusQOperationalLocalPair
open Ttc.CVGaussianScoreSeedPhaseKernel
open scoped ENNReal Classical BigOperators

variable {n m : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- Seed marginal of the exact local graph reference produced by phase `i`. -/
noncomputable def radiusQLocalGraphSeedTarget
    (m n : Nat) (q N s0 : Real) (K : Set (State n)) (i : Nat) :
    Measure (State n) :=
  Measure.map (fun x : State n ↦ (1 - 1 / (2 * (n : Real))) • x)
    (coolLaw m (sigmaSq n N s0)
      (radiusQBody q K (sigmaSq n N s0 i)) i)

theorem isProbabilityMeasure_radiusQLocalGraphSeedTarget
    (hn : 1 ≤ n) (m : Nat) {q N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hball : ball (0 : State n) 1 ⊆ K)
    (i : Nat) (hrad : 1 ≤ q * Real.sqrt (sigmaSq n N s0 i) * Real.sqrt n) :
    IsProbabilityMeasure (radiusQLocalGraphSeedTarget m n q N s0 K i) := by
  let body := radiusQBody q K (sigmaSq n N s0 i)
  have hbodyBall : ball (0 : State n) 1 ⊆ body :=
    unitBall_subset_inter_closedBall hball
      (by simpa only [body, radiusQBody] using hrad)
  have hbodyTop : volume body ≠ ⊤ := by
    dsimp only [body, radiusQBody]
    exact volume_inter_closedBall_ne_top K _
  letI : IsProbabilityMeasure (coolLaw m (sigmaSq n N s0) body i) :=
    coolLaw_isProbabilityMeasure (sigmaSq_pos hn hN hs0) hbodyBall hbodyTop i
  unfold radiusQLocalGraphSeedTarget
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The retained local graph seed has exactly the switched cross warmth required by
the next phase; no accumulated operational warm factor appears. -/
theorem isWarm_radiusQLocalGraphSeedTarget_succ
    (hn : 1 ≤ n) {m : Nat} {q N s0 : Real} (hq : 0 < q)
    (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m)
    (hrate0 : 0 ≤ phaseRate n N s0 i)
    (hrad : 1 ≤ q * Real.sqrt (sigmaSq n N s0 i) * Real.sqrt n) :
    IsWarm (switchedRadiusQWarmFactor n q N s0 K i)
      (radiusQLocalGraphSeedTarget m n q N s0 K i)
      (hybridRadiusQSeedTarget n q N s0 K (i + 1)) := by
  simpa only [radiusQLocalGraphSeedTarget, hybridRadiusQSeedTarget] using
    (isWarm_standardScaled_radiusQ_hybrid_switched hn hq hN hs0 hK hKc
      hball hfin hi hrate0 hrad)

/-- Seed-marginal form of the full graph-law operational theorem.  Cost erasure is
performed internally, so the conclusion has exactly the type required by the
heterogeneous retained-history induction. -/
theorem tvLe_bind_sourceHybridRadiusQWarmFallbackCostedSchedule_nextSeed
    (hn : 21 ≤ n) {q N s0 : Real} (hq : 1 < q)
    (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat) (scoreScale : Real)
    (i : Nat) (hi : i < m)
    (rho : Measure (State n)) [IsProbabilityMeasure rho]
    {M eta zeta : ENNReal} (hM1 : 1 ≤ M) (hMtop : M ≠ ⊤)
    (heta0 : eta ≠ 0) (hetatop : eta ≠ ⊤) (heta1 : eta ≤ 1)
    (hzeta0 : zeta ≠ 0) (hzetatop : zeta ≠ ⊤)
    (hzeta16 : zeta ≤ ENNReal.ofReal (1 / 16 : Real))
    (hrad : 1 ≤ q * Real.sqrt (sigmaSq n N s0 i) * Real.sqrt n)
    (hwarm : IsWarm M rho (hybridRadiusQSeedTarget n q N s0 K i))
    (L : Nat)
    (hsteps : steps i = fun _ ↦
      Ttc.CVGaussianAdaptiveMixing.adjustableSpeedyDeadline n
        (radiusQDelta n q (sigmaSq n N s0 i))
        (sigmaSq n N s0 i) (M / eta) zeta)
    (hretries : retries i = L) :
    TVLe
      (rho.bind (Kernel.map
        (sourceHybridRadiusQWarmFallbackCostedSchedule (by omega : 1 ≤ n)
          q (zero_lt_one.trans hq) hN hs0 K hK steps retries scoreScale i)
        (fun y : ENNReal × ScoreSeed n ↦ y.2.2)))
      (radiusQLocalGraphSeedTarget m n q N s0 K i)
      (32 * zeta + (eta + Ttc.CVContinuingRetryParameters.continuingContraction ^ L)) := by
  letI : ∀ j, IsProbabilityMeasure (hybridRadiusQFallback n N s0 scoreScale j) :=
    fun j ↦ isProbabilityMeasure_hybridRadiusQFallback (by omega) hN hs0 scoreScale j
  have hpair :=
    tvLe_radiusQWarmFallbackKernelOfSigma_localPair_adjustable_zeroSafe_of_eq
      hn hq hK hKc hball (sigmaSq n N s0) (sigmaSq_pos (by omega) hN hs0)
      steps retries
      (hybridRadiusQFallback n N s0 scoreScale) i hi rho
      hM1 hMtop heta0 hetatop heta1 hzeta0 hzetatop hzeta16 hrad
      (by simpa only [hybridRadiusQSeedTarget] using hwarm) L hsteps hretries
  have hseed := hpair.map measurable_snd
  rw [map_snd_scoreSeedReference] at hseed
  have herase : ∀ x : State n,
      Measure.map (fun y : ENNReal × ScoreSeed n ↦ y.2.2)
          (sourceHybridRadiusQWarmFallbackCostedSchedule (by omega : 1 ≤ n)
            q (zero_lt_one.trans hq) hN hs0 K hK steps retries scoreScale i x) =
        Measure.map Prod.snd
          (hybridRadiusQWarmFallbackKernel (by omega : 1 ≤ n) q
            (zero_lt_one.trans hq) K hK N s0 hN hs0 steps retries
            (hybridRadiusQFallback n N s0 scoreScale) i x) := by
    intro x
    have h := congrArg (Measure.map Prod.snd)
      (map_snd_sourceHybridRadiusQWarmFallbackCostedSchedule
        (by omega : 1 ≤ n) q (zero_lt_one.trans hq) hN hs0 K hK
        steps retries scoreScale i x)
    rw [Measure.map_map measurable_snd measurable_snd] at h
    simpa only [Function.comp_def, sourceHybridRadiusQWarmFallbackSchedule] using h
  have hleft :
      rho.bind (Kernel.map
        (sourceHybridRadiusQWarmFallbackCostedSchedule (by omega : 1 ≤ n)
          q (zero_lt_one.trans hq) hN hs0 K hK steps retries scoreScale i)
        (fun y : ENNReal × ScoreSeed n ↦ y.2.2)) =
      Measure.map Prod.snd
        (sampleFromKernel
          (hybridRadiusQWarmFallbackKernel (by omega : 1 ≤ n) q
            (zero_lt_one.trans hq) K hK N s0 hN hs0 steps retries
          (hybridRadiusQFallback n N s0 scoreScale) i) rho) := by
    unfold sampleFromKernel
    ext S hS
    rw [Measure.bind_apply hS (Kernel.aemeasurable _),
      Measure.map_apply measurable_snd hS,
      Measure.bind_apply (hS.preimage measurable_snd) (Kernel.aemeasurable _)]
    apply lintegral_congr
    intro x
    rw [Kernel.map_apply _ (by fun_prop), ← Measure.map_apply measurable_snd hS,
      herase x, Measure.map_apply measurable_snd hS]
  rw [hleft]
  simpa only [radiusQLocalGraphSeedTarget,
    Ttc.CVRadiusQGenericFallbackSchedule.radiusQWarmFallbackKernelOfSigma,
    hybridRadiusQWarmFallbackKernel] using hseed

#print axioms tvLe_bind_sourceHybridRadiusQWarmFallbackCostedSchedule_nextSeed
#print axioms isWarm_radiusQLocalGraphSeedTarget_succ

end Ttc.CVHybridRadiusQReferencePhaseTV
