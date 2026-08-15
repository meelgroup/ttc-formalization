import Ttc.Exec.CVHybridRadiusQReferenceCost
import Ttc.Exec.CVHybridRadiusQSwitchedCanonicalOperational

/-! Retained stationary-reference cost for switch-aware canonical deadlines. -/

set_option autoImplicit false

namespace Ttc.CVHybridRadiusQSwitchedReferenceCost

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains
open Ttc.CVHybridSchedule Ttc.CVHybridRadiusQRecursiveStep
open Ttc.CVHybridRadiusQReferenceCost
open Ttc.CVHybridRadiusQSwitchedCanonicalOperational
open Ttc.CVConcreteAugmentedRetryCutoffBudget
open Ttc.CVHeterogeneousHistoryReference
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- The exact stationary retained phase cost after substituting switch-aware canonical
mixing deadlines.  In particular the reference seed has warmness one; the recursively
growing actual-path warmness appears only inside the logarithmic deadline. -/
theorem sourceHybridRadiusQ_switchedCanonical_stationaryReferenceCost_le
    (hn : 2 ≤ n) {q N s0 : Real} (hq : 1 < q) (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K)
    (initialWarm : ENNReal) (retries : Nat → Nat)
    (etaShare zetaShare : Nat → ENNReal) (scoreScale : Real) (i : Nat)
    (hrad : 1 ≤ q * Real.sqrt (sigmaSq n N s0 i) * Real.sqrt n) :
    (∫⁻ x, heterogeneousStepMean
      (sourceHybridRadiusQWarmFallbackCostedSchedule (by omega : 1 ≤ n)
        q (zero_lt_one.trans hq) hN hs0 K hK
        (hybridRadiusQSwitchedCanonicalSteps initialWarm n q N s0 K retries
          etaShare zetaShare)
        retries scoreScale i) x
      ∂(hybridRadiusQSeedTarget n q N s0 K i)) ≤
      ENNReal.ofReal
        (retryReferenceMeanEnvelope 1
          (hybridRadiusQSwitchedCanonicalSteps initialWarm n q N s0 K retries
            etaShare zetaShare i)
          (retries i)) := by
  simpa using sourceHybridRadiusQ_stationaryReferenceCost_le hn hq hN hs0 hK hKc
    hball
    (hybridRadiusQSwitchedCanonicalSteps initialWarm n q N s0 K retries
      etaShare zetaShare)
    retries scoreScale i hrad

#print axioms sourceHybridRadiusQ_switchedCanonical_stationaryReferenceCost_le

end Ttc.CVHybridRadiusQSwitchedReferenceCost
