import Ttc.Exec.CVSlowRadiusQOperationalPair
import Ttc.Exec.CVHybridRadiusQOperationalLocalPair

/-!
Full-body graph-law accuracy for the radius-`q` kernel on an arbitrary positive
variance schedule.  The local operational theorem pays no truncation error; this
file adds the adjustable radial tail exactly once when a full-body score target is
needed by the cooling telescope.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Ttc.CVSlowRadiusQOperationalFullPair

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler
open Ttc.CVAdaptiveRadiusQPrimitives Ttc.CVSlowRadiusQFallbackSchedule
open Ttc.CVSlowRadiusQOperationalPair
open Ttc.CVSlowFullBodySourceSchedule
open Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.CVContinuingRetryParameters
open scoped ENNReal Classical

variable {n m : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- The arbitrary-schedule radius-`q` operational pair is close to the exact
full-body graph law.  The first two summands are the local mixing/retry error and
the final summand is the sole radius truncation tail. -/
theorem tvLe_radiusQWarmFallbackKernelOfSigma_fullPair_adjustable_zeroSafe_of_eq
    (hn : 21 ≤ n) {q : Real} (hq : 1 < q)
    (sigmaSq : Nat → Real) (hsigma : ∀ j, 0 < sigmaSq j)
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
    (hrad : 1 ≤ q * Real.sqrt (sigmaSq i) * Real.sqrt n)
    (hwarm : IsWarm M rho
      (ellGaussianProb (radiusQBody q K (sigmaSq i))
        (radiusQDelta n q (sigmaSq i)) (sigmaSq i)))
    (L : Nat)
    (hsteps : steps i = fun _ ↦
      Ttc.CVGaussianAdaptiveMixing.adjustableSpeedyDeadline n
        (radiusQDelta n q (sigmaSq i)) (sigmaSq i) (M / eta) zeta)
    (hretries : retries i = L) :
    TVLe
      (sampleFromKernel
        (radiusQWarmFallbackKernelOfSigma (by omega : 1 ≤ n) q
          (zero_lt_one.trans hq) K hK sigmaSq hsigma
          steps retries fallback i) rho)
      (scoreSeedReference (1 - 1 / (2 * (n : Real)))
        (coolLaw m sigmaSq K i))
      (32 * zeta + (eta + continuingContraction ^ L) +
        ENNReal.ofReal ((q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n)) := by
  have hlocal :=
    Ttc.CVSlowRadiusQOperationalPair.tvLe_radiusQWarmFallbackKernelOfSigma_localPair_adjustable_zeroSafe_of_eq
      hn hq sigmaSq hsigma hK hKc hball steps retries fallback i hi rho
      hM1 hMtop heta0 hetatop heta1 hzeta0 hzetatop hzeta16 hrad hwarm
      L hsteps hretries
  have htail :=
    Ttc.CVHybridRadiusQOperationalLocalPair.tvLe_radiusQ_coolLawOfSigma_full
      (m := m) (by omega : 1 ≤ n) hq sigmaSq hsigma
      hK hKc hball hfin hi hrad
  have htailPair := htail.map
    (by fun_prop : Measurable (fun y : State n ↦
      (y, (1 - 1 / (2 * (n : Real))) • y)))
  exact hlocal.trans (by
    simpa only [scoreSeedReference, add_assoc] using htailPair)

/-- Direct specialization to the uniformly slow schedule and its independently
sampleable fallback law. -/
theorem tvLe_slowRadiusQWarmFallbackKernel_fullPair_adjustable_zeroSafe_of_eq
    (hn : 21 ≤ n) {q s0 : Real} (hq : 1 < q) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat) (scoreScale : Real)
    (i : Nat) (hi : i < m)
    (rho : Measure (State n)) [IsProbabilityMeasure rho]
    {M eta zeta : ENNReal} (hM1 : 1 ≤ M) (hMtop : M ≠ ⊤)
    (heta0 : eta ≠ 0) (hetatop : eta ≠ ⊤) (heta1 : eta ≤ 1)
    (hzeta0 : zeta ≠ 0) (hzetatop : zeta ≠ ⊤)
    (hzeta16 : zeta ≤ ENNReal.ofReal (1 / 16 : Real))
    (hrad : 1 ≤ q * Real.sqrt (slowSourceSigmaSq n s0 i) * Real.sqrt n)
    (hwarm : IsWarm M rho
      (ellGaussianProb (radiusQBody q K (slowSourceSigmaSq n s0 i))
        (radiusQDelta n q (slowSourceSigmaSq n s0 i))
        (slowSourceSigmaSq n s0 i)))
    (L : Nat)
    (hsteps : steps i = fun _ ↦
      Ttc.CVGaussianAdaptiveMixing.adjustableSpeedyDeadline n
        (radiusQDelta n q (slowSourceSigmaSq n s0 i))
        (slowSourceSigmaSq n s0 i) (M / eta) zeta)
    (hretries : retries i = L) :
    TVLe
      (sampleFromKernel
        (@radiusQWarmFallbackKernelOfSigma n (by omega : 1 ≤ n) q
          (zero_lt_one.trans hq) K hK (slowSourceSigmaSq n s0)
          (slowSourceSigmaSq_pos (by omega) hs0) steps retries
          (slowRadiusQFallback n s0 scoreScale)
          (fun j ↦ isProbabilityMeasure_slowRadiusQFallback
            (by omega) hs0 scoreScale j) i) rho)
      (scoreSeedReference (1 - 1 / (2 * (n : Real)))
        (coolLaw m (slowSourceSigmaSq n s0) K i))
      (32 * zeta + (eta + continuingContraction ^ L) +
        ENNReal.ofReal ((q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n)) := by
  letI : ∀ j, IsProbabilityMeasure (slowRadiusQFallback n s0 scoreScale j) :=
    fun j ↦ isProbabilityMeasure_slowRadiusQFallback (by omega) hs0 scoreScale j
  exact
    tvLe_radiusQWarmFallbackKernelOfSigma_fullPair_adjustable_zeroSafe_of_eq
      hn hq (slowSourceSigmaSq n s0) (slowSourceSigmaSq_pos (by omega) hs0)
      hK hKc hball hfin steps retries (slowRadiusQFallback n s0 scoreScale)
      i hi rho hM1 hMtop heta0 hetatop heta1 hzeta0 hzetatop hzeta16
      hrad hwarm L hsteps hretries

#print axioms
  tvLe_radiusQWarmFallbackKernelOfSigma_fullPair_adjustable_zeroSafe_of_eq
#print axioms
  tvLe_slowRadiusQWarmFallbackKernel_fullPair_adjustable_zeroSafe_of_eq

end Ttc.CVSlowRadiusQOperationalFullPair
