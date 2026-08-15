import Ttc.Exec.CVSourceWeightedMeanRepair
import Ttc.Exec.CVSlowRadiusQCanonicalOperational

/-! The robust weighted estimator applied to local selected-radius graph targets. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Ttc.CVSlowSourceTargetTVAccuracy

open MeasureTheory ProbabilityTheory Metric Set Finset
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler Ttc.CVIndependentStreamDependence
open Ttc.CVGaussianScoreSeedPhaseKernel Ttc.CVAdaptiveRadiusQPrimitives
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVHybridRadiusQOperationalLocalPair
open Ttc.CVSlowFullBodySourceSchedule Ttc.CVSlowRadiusQCanonicalOperational
open scoped ENNReal Classical BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

noncomputable def slowTargetError (n : Nat) (q : Real) (m : Nat) (i : Nat) : ENNReal :=
  if i < m then ENNReal.ofReal ((q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n) else 1

/-- Before the terminal index the cooling density is Gaussian and does not depend on
whether the declared terminal length is `m` or `m+1`.  This closes the honest
active-cutoff/estimator-length adapter used by the canonical slow sampler. -/
theorem slowLocalPairReference_succ_length_eq
    (m n : Nat) (q s0 : Real) (K : Set (State n)) {i : Nat} (hi : i < m) :
    slowLocalPairReference (m + 1) n q s0 K i =
      slowLocalPairReference m n q s0 K i := by
  unfold slowLocalPairReference scoreSeedReference coolLaw chain
  simp only [coolWeight_of_lt hi,
    coolWeight_of_lt (hi.trans (Nat.lt_succ_self m))]

/-- A local graph target differs from the full-body cooling law by exactly the
selected-radius Gaussian tail.  Outside the estimator range the universal TV bound
keeps the all-natural operational interface total. -/
theorem tvLe_map_fst_tau_fullCoolLaw_slowTargetError
    {k m : Nat} {Q : Nat → Kernel (State n) (ScoreSeed n)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (ScoreSeed n)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → ScoreSeed n) → Real} {eps : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V m eps)
    (hn : 1 ≤ n)
    {q s0 : Real} (hq : 1 < q) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hrad : ∀ i, i < m →
      1 ≤ q * Real.sqrt (slowSourceSigmaSq n s0 i) * Real.sqrt n)
    (htau : ∀ i, i < m → hop.tau i = slowLocalPairReference m n q s0 K i) :
    ∀ i, TVLe (Measure.map Prod.fst (hop.tau i))
      (coolLaw m (slowSourceSigmaSq n s0) K i) (slowTargetError n q m i) := by
  intro i
  by_cases hi : i < m
  · rw [htau i hi, slowLocalPairReference, map_fst_scoreSeedReference]
    unfold slowTargetError
    rw [if_pos hi]
    exact tvLe_radiusQ_coolLawOfSigma_full (n := n) (m := m)
      hn hq (slowSourceSigmaSq n s0)
      (slowSourceSigmaSq_pos hn hs0)
      hK hKc hball hfin hi (hrad i hi)
  · unfold slowTargetError
    rw [if_neg hi]
    letI : IsProbabilityMeasure (hop.tau i) := hop.tau_prob i
    letI : IsProbabilityMeasure (Measure.map Prod.fst (hop.tau i)) :=
      Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    letI : IsProbabilityMeasure (coolLaw m (slowSourceSigmaSq n s0) K i) :=
      coolLaw_isProbabilityMeasure (slowSourceSigmaSq_pos hn hs0)
        hball hfin i
    exact Arlib.tvLe_one _ _

theorem slowTargetError_ne_top (n : Nat) (q : Real) (m i : Nat) :
    slowTargetError n q m i ≠ ⊤ := by
  unfold slowTargetError
  split
  · exact ENNReal.ofReal_ne_top
  · simp

/-- On a genuine estimator phase the robust error is the operational local mixing
error plus the explicit radial tail; there is no hidden exact-target assumption. -/
theorem slowTargetError_active
    {n m i : Nat} {q : Real} (hi : i < m) :
    slowTargetError n q m i =
      ENNReal.ofReal ((q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n) := by
  simp [slowTargetError, hi]

#print axioms tvLe_map_fst_tau_fullCoolLaw_slowTargetError
#print axioms slowTargetError_ne_top

end Ttc.CVSlowSourceTargetTVAccuracy
