import Ttc.Exec.CVSlowRadiusQOperationalFullPair
import Ttc.Exec.CVSlowSourceReferenceCertificate
import Ttc.Exec.CVAdaptiveRadiusQPrimitives
import Ttc.Exec.CVGaussianScoreAwareParameters

/-! Full score/seed target family for the uniformly slow source.

The retained local-graph seed law is the warmness/reference law used by the recursive
induction.  The operational mixing theorem, however, returns the full score/seed graph
law.  Keeping this family explicit prevents accidentally identifying those two laws.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Ttc.CVSlowFullScoreTarget

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.CVAdaptiveRadiusQPrimitives Ttc.CVGaussianScoreAwareParameters
open Ttc.CVSequentialPhaseSampler
open Ttc.CVSlowFullBodySourceSchedule Ttc.CVSlowSourceReferenceCertificate
open Ttc.CVSlowRadiusQOperationalFullPair
open Ttc.CVHybridRadiusQOperationalLocalPair
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

noncomputable def slowFullScoreTarget
    (m n : Nat) (q s0 : Real) (K : Set (State n)) (i : Nat) : Measure (ScoreSeed n) :=
  scoreSeedReference (1 - 1 / (2 * (n : Real)))
    (coolLaw m (slowSourceSigmaSq n s0) K i)

theorem slowFullScoreTarget_apply
    (m n : Nat) (q s0 : Real) (K : Set (State n)) (i : Nat) :
    slowFullScoreTarget m n q s0 K i =
      scoreSeedReference (1 - 1 / (2 * (n : Real)))
        (coolLaw m (slowSourceSigmaSq n s0) K i) := rfl

theorem map_fst_slowFullScoreTarget
    (m n : Nat) (q s0 : Real) (K : Set (State n)) (i : Nat) :
    Measure.map Prod.fst (slowFullScoreTarget m n q s0 K i) =
      coolLaw m (slowSourceSigmaSq n s0) K i := by
  exact map_fst_scoreSeedReference _ _

theorem isProbabilityMeasure_slowFullScoreTarget
    (hn : 1 ≤ n) {m : Nat} {q s0 : Real} (hs0 : 0 < s0)
    {K : Set (State n)} (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (i : Nat) :
    IsProbabilityMeasure (slowFullScoreTarget m n q s0 K i) := by
  unfold slowFullScoreTarget
  letI : IsProbabilityMeasure
      (coolLaw m (slowSourceSigmaSq n s0) K i) :=
    coolLaw_isProbabilityMeasure (slowSourceSigmaSq_pos hn hs0) hball hfin i
  unfold scoreSeedReference
  exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem tvLe_slowLocalScoreTarget_full
    (hn : 21 ≤ n) {m : Nat} {q s0 : Real} (hq : 1 < q) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i < m)
    (hrad : 1 ≤ q * Real.sqrt (slowSourceSigmaSq n s0 i) * Real.sqrt n) :
    TVLe
      (scoreSeedReference (1 - 1 / (2 * (n : Real)))
        (coolLaw m (slowSourceSigmaSq n s0)
          (radiusQBody q K (slowSourceSigmaSq n s0 i)) i))
      (slowFullScoreTarget m n q s0 K i)
      (ENNReal.ofReal ((q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n)) := by
  have h := tvLe_radiusQ_coolLawOfSigma_full (m := m) (by omega : 1 ≤ n) hq
    (slowSourceSigmaSq n s0) (slowSourceSigmaSq_pos (by omega : 1 ≤ n) hs0) hK hKc hball hfin hi hrad
  have hp := h.map (by fun_prop : Measurable (fun y : State n ↦
    (y, (1 - 1 / (2 * (n : Real))) • y)))
  simpa only [slowFullScoreTarget, scoreSeedReference] using hp

/-- The raw slow kernel is close to the full score/seed target whenever its incoming seed
is warm for the selected-radius truncated Gaussian.  This is the exact theorem needed for
the `distributional_mixing` field of `SeedProjectedOperational`. -/
theorem tvLe_sampleFrom_slowRawSchedule_fullTarget
    (hn : 21 ≤ n) (m k : Nat) {q eps : Real} (hq : 1 < q)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (slack boundSq : Nat → Real) (scoreScale : Real)
    (i : Nat) (hi : i + 1 < m)
    (rho : Measure (State n)) [IsProbabilityMeasure rho]
    {M eta zeta : ENNReal} (hM1 : 1 ≤ M) (hMtop : M ≠ ⊤)
    (heta0 : eta ≠ 0) (hetatop : eta ≠ ⊤) (heta1 : eta ≤ 1)
    (hzeta0 : zeta ≠ 0) (hzetatop : zeta ≠ ⊤)
    (hzeta16 : zeta ≤ ENNReal.ofReal (1 / 16 : Real))
    (hrad : 1 ≤ q * Real.sqrt (slowSourceSigmaSq n (slowSourceInitialVariance n) i) * Real.sqrt n)
    (hwarm : IsWarm M rho
      (ellGaussianProb (radiusQBody q K (slowSourceSigmaSq n (slowSourceInitialVariance n) i))
        (radiusQDelta n q (slowSourceSigmaSq n (slowSourceInitialVariance n) i))
        (slowSourceSigmaSq n (slowSourceInitialVariance n) i)))
    (L : Nat)
    (hsteps : slowScoreAwareSteps n m k q eps slack boundSq i = fun _ =>
      Ttc.CVGaussianAdaptiveMixing.adjustableSpeedyDeadline n
        (radiusQDelta n q (slowSourceSigmaSq n (slowSourceInitialVariance n) i))
        (slowSourceSigmaSq n (slowSourceInitialVariance n) i) (M / eta) zeta)
    (hretries : scoreAwareRetries m k eps slack boundSq i = L) :
    TVLe
      (sampleFromKernel
        (slowRawSchedule (by omega : 1 ≤ n) m k q eps
          (by positivity) K hK slack boundSq scoreScale i) rho)
      (slowFullScoreTarget m n q (slowSourceInitialVariance n) K i)
      (32 * zeta + (eta + Ttc.CVContinuingRetryParameters.continuingContraction ^ L) +
        ENNReal.ofReal ((q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n)) := by
  have h := tvLe_slowRadiusQWarmFallbackKernel_fullPair_adjustable_zeroSafe_of_eq
    (m := m) hn hq (by unfold slowSourceInitialVariance; positivity) hK hKc hball hfin
    (slowScoreAwareSteps n m k q eps slack boundSq)
    (scoreAwareRetries m k eps slack boundSq) scoreScale i
    (by omega) rho hM1 hMtop heta0 hetatop heta1 hzeta0 hzetatop hzeta16 hrad hwarm
    L hsteps hretries
  simpa only [slowRawSchedule, slowFullScoreTarget] using h

#print axioms map_fst_slowFullScoreTarget
#print axioms isProbabilityMeasure_slowFullScoreTarget
#print axioms tvLe_sampleFrom_slowRawSchedule_fullTarget

end Ttc.CVSlowFullScoreTarget
