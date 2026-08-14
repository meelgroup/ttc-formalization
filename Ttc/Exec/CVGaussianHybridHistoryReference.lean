import Ttc.Exec.CVGaussianHistoryReferenceSpecialization
import Ttc.Exec.CVRadiusAwareScaledRawWarm

/-!
# Radius-aware retained-history reference for the concrete hybrid schedule

This constructs the `hrefWarm` family needed by a heterogeneous retained-history reference
for the full cold-plus-accelerated variance schedule.  It is the warmth component only;
the history-reference and public-certificate constructors live in separate assembly modules.
The active target is the exact score/seed graph law, the inactive tail has the declared exact
seed marginal, and the hot phases use the radius invariant rather than a
dimension-exponential ratio bound.
-/

set_option autoImplicit false

namespace Ttc.CVGaussianHybridHistoryReference

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.CVGaussianHistoryReferenceSpecialization
open Ttc.CVRadiusAwareScaledRawWarm
open Ttc.CVHybridSchedule
open scoped ENNReal

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev GaussianScoreSeed (n : Nat) := State n × State n

/-- Direct construction of the warmth family required by the Gaussian history theorem.
All active phases, including coarse accelerated phases, use the same `2e` constant. -/
theorem referenceInputFamily_warm_hybrid
    (hn : 1 ≤ n) {m : Nat} {N s0 radius : Real}
    (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ radius) (hR2 : radius ^ 2 ≤ N)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    (mu0 : Measure (GaussianScoreSeed n)) [IsProbabilityMeasure mu0]
    (target : Nat → Measure (GaussianScoreSeed n))
    [∀ i, IsProbabilityMeasure (target i)]
    (pi : Nat → Measure (State n))
    (hpi : ∀ i, pi i = ellGaussianProb K delta (sigmaSq n N s0 i))
    (htarget : ∀ i, i + 1 < m →
      target i = scoreSeedReference (1 - 1 / (2 * (n : Real)))
        (coolLaw m (sigmaSq n N s0) K i))
    (hstart : IsWarm gaussianReferenceWarm
      (Measure.map Prod.snd mu0) (pi 0))
    (htail : ∀ i, ¬ i + 1 < m →
      Measure.map Prod.snd (target i) = pi (i + 1)) :
    ∀ i, IsWarm gaussianReferenceWarm
      (Measure.map Prod.snd (referenceInputFamily mu0 target i)) (pi i) := by
  apply referenceInputFamily_warm mu0 target pi
    (fun _ ↦ gaussianReferenceWarm) m hstart
  · intro i hi
    rw [htarget i hi, hpi (i + 1)]
    have hsubset : K ⊆ closedBall (0 : State n) radius := by
      intro x hx
      exact mem_closedBall_zero_iff.2 (hKR x hx)
    exact isWarm_scoreSeedReference_hybrid_twoE hn hN hs0 hK hKc hball hfin
      hsubset hR2 hi hdelta hdeltan
  · intro i hi
    exact isWarm_exactTail_of_map_snd_eq (target i) (pi (i + 1))
      (htail i hi) (by
        unfold gaussianReferenceWarm
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        have : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
        nlinarith)

#print axioms referenceInputFamily_warm_hybrid

end Ttc.CVGaussianHybridHistoryReference
