import Ttc.Exec.CVHybridRadiusFourFullScore
import Ttc.Exec.CVGaussianScoreSeedPhaseKernel

/-! Radius-four tail transfer for the complete score/seed graph law. -/

set_option autoImplicit false

namespace Ttc.CVHybridRadiusFourFullPair

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVHybridSchedule
open Ttc.CVHybridRadiusFourFullScore
open Ttc.CVSourceTruncatedFixedCost
open Ttc.CVGaussianScoreSeedPhaseKernel
open scoped ENNReal Classical

variable {n m : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- Compose any operational pair estimate against the truncated score/seed graph with
the radius-four tail.  Mapping the score tail through `y ↦ (y,c • y)` spends no extra
TV error and preserves the exact graph dependence required by sequential operation. -/
theorem tvLe_scoreSeedReference_hybridRadiusFour_full_of_local
    (hn : 1 ≤ n) {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i < m)
    (hrad : 1 ≤ 4 * Real.sqrt (sigmaSq n N s0 i) * Real.sqrt n)
    (c : Real) (actual : Measure (ScoreSeed n))
    {eps : ENNReal}
    (hlocal : TVLe actual
      (scoreSeedReference c
        (coolLaw m (sigmaSq n N s0)
          (fixedRadiusFourBody K (sigmaSq n N s0 i)) i)) eps) :
    TVLe actual
      (scoreSeedReference c (coolLaw m (sigmaSq n N s0) K i))
      (eps + ENNReal.ofReal ((4 * Real.exp (-(15 : Real) / 2)) ^ n)) := by
  have htail := tvLe_hybridRadiusFour_coolLaw_full
    (m := m) hn hN hs0 hK hKc hball hfin hi hrad
  have htailPair := htail.map
    (by fun_prop : Measurable (fun y : State n ↦ (y, c • y)))
  exact hlocal.trans (by
    simpa only [scoreSeedReference] using htailPair)

#print axioms tvLe_scoreSeedReference_hybridRadiusFour_full_of_local

end Ttc.CVHybridRadiusFourFullPair
