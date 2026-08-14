import Ttc.Exec.CVHybridRadiusFourFallbackSchedule
import Arlib.MarkovChains.Continuous.ColdTruncationRelativeFour

/-! Full-body score target for every radius-four hybrid phase. -/

set_option autoImplicit false

namespace Ttc.CVHybridRadiusFourFullScore

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVHybridSchedule
open Ttc.CVSourceTruncatedFixedCost
open scoped ENNReal Classical

variable {n m : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- The score law on the operational radius-four body is within the source's explicit
relative Gaussian tail of the full-body score law.  This is schedule-agnostic and hence
applies unchanged to accelerated hot phases. -/
theorem tvLe_hybridRadiusFour_coolLaw_full
    (hn : 1 <= n) {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i < m)
    (hrad : 1 <= 4 * Real.sqrt (sigmaSq n N s0 i) * Real.sqrt n) :
    TVLe
      (coolLaw m (sigmaSq n N s0)
        (fixedRadiusFourBody K (sigmaSq n N s0 i)) i)
      (coolLaw m (sigmaSq n N s0) K i)
      (ENNReal.ofReal ((4 * Real.exp (-(15 : Real) / 2)) ^ n)) := by
  have hsigma : forall j, 0 < sigmaSq n N s0 j := sigmaSq_pos hn hN hs0
  let s := sigmaSq n N s0 i
  have hs : 0 < s := hsigma i
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hsquare : sigmaSq n N s0 i = (Real.sqrt s) ^ 2 := by
    simpa only [s] using (Real.sq_sqrt hs.le).symm
  simpa only [fixedRadiusFourBody, s] using
    (tvLe_coolLaw_inter_closedBall_relative_four hn hsigma hsqrt hK hKc
      hball hfin hi hsquare (by simpa only [s] using hrad))

theorem tvLe_hybridRadiusFour_coolLaw_prod_full
    (hn : 1 <= n) {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i < m)
    (hrad : 1 <= 4 * Real.sqrt (sigmaSq n N s0 i) * Real.sqrt n)
    (seed : Measure (State n)) [IsProbabilityMeasure seed] :
    TVLe
      ((coolLaw m (sigmaSq n N s0)
        (fixedRadiusFourBody K (sigmaSq n N s0 i)) i).prod seed)
      ((coolLaw m (sigmaSq n N s0) K i).prod seed)
      (ENNReal.ofReal ((4 * Real.exp (-(15 : Real) / 2)) ^ n)) := by
  have hsigma : forall j, 0 < sigmaSq n N s0 j := sigmaSq_pos hn hN hs0
  have hbodyBall : ball (0 : State n) 1 ⊆
      fixedRadiusFourBody K (sigmaSq n N s0 i) :=
    unitBall_subset_inter_closedBall hball hrad
  have hbodyTop : volume (fixedRadiusFourBody K (sigmaSq n N s0 i)) ≠ ⊤ :=
    volume_inter_closedBall_ne_top K _
  letI : IsProbabilityMeasure
      (coolLaw m (sigmaSq n N s0)
        (fixedRadiusFourBody K (sigmaSq n N s0 i)) i) :=
    coolLaw_isProbabilityMeasure hsigma hbodyBall hbodyTop i
  letI : IsProbabilityMeasure (coolLaw m (sigmaSq n N s0) K i) :=
    coolLaw_isProbabilityMeasure hsigma hball hfin i
  simpa only [add_zero] using
    (tvLe_hybridRadiusFour_coolLaw_full hn hN hs0 hK hKc hball hfin hi hrad).prod
      (TVLe.refl seed)

#print axioms tvLe_hybridRadiusFour_coolLaw_full
#print axioms tvLe_hybridRadiusFour_coolLaw_prod_full

end Ttc.CVHybridRadiusFourFullScore
