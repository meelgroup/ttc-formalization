import Ttc.Exec.CVColdOperationalSeedReset
import Arlib.MarkovChains.Continuous.ColdTruncationRelativeFour

/-!
# Full-body target for the independently refreshed cold kernel

The operational cold walk runs on the radius-four truncation.  This adapter composes
its zero-safe score/seed estimate with the relative Gaussian tail theorem, so the score
component targets the public, untruncated cooling law on `K`.  Tensoring the same fresh
seed costs no further total-variation error.
-/

set_option autoImplicit false

namespace Ttc.CVColdOperationalFullTarget

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler
open Ttc.CVColdOperationalSeedReset
open Ttc.CVCorrectedFixedBlockCost
open Ttc.CVSourceTruncatedFixedCost
open scoped ENNReal Classical

variable {n m : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- Full-body score/seed accuracy for the refreshed cold kernel.  The first two error
terms are the zero-safe retry/mixing error; the last is precisely the radius-four
relative Gaussian tail from the paper. -/
theorem tvLe_coldGaussianResetKernel_fullScore_prod_nextSeed_adjustable_zeroSafe_of_eq
    (hn : 21 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤)
    (s0 : Real) (hs0 : 0 < s0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (i : Nat) (hi : i < m)
    (rho : Measure (State n)) [IsProbabilityMeasure rho]
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
      (sampleFromKernel
        (coldGaussianResetKernel (by omega : 1 ≤ n) K hK s0 hs0
          retrySteps retries i) rho)
      ((coolLaw m (fixedSigmaSq n s0) K i).prod
        (coldNextRefreshSeed n s0 i))
      (32 * zeta + (eta + Ttc.CVContinuingRetryParameters.continuingContraction ^ L) +
        ENNReal.ofReal ((4 * Real.exp (-(15 : Real) / 2)) ^ n)) := by
  have hn1 : 1 ≤ n := by omega
  let s := fixedSigmaSq n s0 i
  let body := fixedRadiusFourBody K s
  have hsigma : ∀ j, 0 < fixedSigmaSq n s0 j := by
    intro j
    unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) j
  have hs : 0 < s := hsigma i
  have hbodyBall : ball (0 : State n) 1 ⊆ body :=
    unitBall_subset_inter_closedBall hball (by simpa only [s] using hrad)
  have hbodyTop : volume body ≠ ⊤ := volume_inter_closedBall_ne_top K _
  letI : IsProbabilityMeasure (coldNextRefreshSeed n s0 i) :=
    isProbabilityMeasure_coldNextRefreshSeed hn1 s0 hs0 i
  letI : IsProbabilityMeasure (coolLaw m (fixedSigmaSq n s0) body i) :=
    coolLaw_isProbabilityMeasure hsigma hbodyBall hbodyTop i
  letI : IsProbabilityMeasure (coolLaw m (fixedSigmaSq n s0) K i) :=
    coolLaw_isProbabilityMeasure hsigma hball hfin i
  have htrunc :=
    tvLe_coldGaussianResetKernel_score_prod_nextSeed_adjustable_zeroSafe_of_eq
      (m := m) hn K hK hKc hball s0 hs0 retrySteps retries i hi rho
      hM1 hMtop heta0 hetatop heta1 hzeta0 hzetatop hzeta16 hrad hwarm
      L hsteps hretries
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hsquare : fixedSigmaSq n s0 i = (Real.sqrt s) ^ 2 := by
    simpa only [s] using (Real.sq_sqrt hs.le).symm
  have htail : TVLe
      (coolLaw m (fixedSigmaSq n s0) body i)
      (coolLaw m (fixedSigmaSq n s0) K i)
      (ENNReal.ofReal ((4 * Real.exp (-(15 : Real) / 2)) ^ n)) := by
    simpa only [body, fixedRadiusFourBody, s] using
      (tvLe_coolLaw_inter_closedBall_relative_four hn1 hsigma hsqrt hK hKc
        hball hfin hi hsquare (by simpa only [s] using hrad))
  have htailProd := htail.prod
    (TVLe.refl (coldNextRefreshSeed n s0 i))
  exact htrunc.trans (by simpa only [body, s, add_zero] using htailProd)

#print axioms
  tvLe_coldGaussianResetKernel_fullScore_prod_nextSeed_adjustable_zeroSafe_of_eq

end Ttc.CVColdOperationalFullTarget
