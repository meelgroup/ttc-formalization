import Ttc.Exec.CVSlowSourceReferenceCertificate
import Ttc.Exec.CVFiniteHistoryAccuracyBridge

/-!
# Complete-history accuracy seam for the slow operational source schedule

This module specializes the generic finite-history transfer theorem to the exact slow
Gaussian kernel used by `CVSlowSourceReferenceCertificate`.  The resulting premise is a
single one-stream TV comparison between complete path laws.  It cannot be weakened to
the already-proved successor-seed marginal comparisons; the quantitative obstruction in
`CVFiniteHistoryAccuracyBridge` rules that out.
-/

set_option autoImplicit false

namespace Ttc.CVSlowSourceCompleteHistoryAccuracy

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability
open Ttc.CVSlowSourceReferenceCertificate
open Ttc.CVSlowRadiusQFallbackSchedule
open Ttc.CVSlowRadiusQReferencePhaseTV
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVHeterogeneousRetainedPathLaw
open Ttc.CVFiniteHistoryAccuracyBridge
open Ttc.CVIndependentStreamDependence
open Ttc.CVRelativeWeightedRetainedCertificate
open Ttc.CVSourceReferenceTVCapstone
open scoped ENNReal Classical BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- The complete one-stream law of the literal slow operational schedule.  All kernel and
probability instances are discharged internally. -/
noncomputable def slowActualOnePathLaw
    (hn : 1 ≤ n) (m k : Nat) (q eps : Real) (hq4 : 4 ≤ q)
    (K : Set (State n)) (hK : MeasurableSet K)
    (hball : ball (0 : State n) 1 ⊆ K)
    (slack boundSq : Nat → Real) (scoreScale : Real) :
    Measure (Nat → ScoreSeed n) := by
  letI : ∀ j, IsProbabilityMeasure
      (slowRadiusQFallback n (slowSourceInitialVariance n) scoreScale j) := fun j ↦
    isProbabilityMeasure_slowRadiusQFallback hn
      (by unfold slowSourceInitialVariance; positivity) scoreScale j
  letI : ∀ j, IsProbabilityMeasure (slowRetainedSeedTarget m n q K j) := fun j ↦
    isProbabilityMeasure_slowRetainedSeedTarget hn hq4 hball j
  letI : ∀ j, IsProbabilityMeasure (slowExactTail m n q K j) := fun j ↦ by
    unfold slowExactTail
    exact Measure.isProbabilityMeasure_map
      ((by fun_prop : Measurable
        (fun y : State n ↦ ((0 : State n), y))).aemeasurable)
  exact inhomogeneousPathMeasure
    (stateScheduleFromSeed
      (slowActiveSchedule hn m k q eps (lt_of_lt_of_le (by norm_num) hq4)
        K hK slack boundSq scoreScale))
    (slowInitialPair n)

instance slowActualOnePathLaw.instIsProbabilityMeasure
    (hn : 1 ≤ n) (m k : Nat) (q eps : Real) (hq4 : 4 ≤ q)
    (K : Set (State n)) (hK : MeasurableSet K)
    (hball : ball (0 : State n) 1 ⊆ K)
    (slack boundSq : Nat → Real) (scoreScale : Real) :
    IsProbabilityMeasure
      (slowActualOnePathLaw hn m k q eps hq4 K hK hball slack boundSq scoreScale) := by
  unfold slowActualOnePathLaw
  letI : ∀ j, IsProbabilityMeasure
      (slowRadiusQFallback n (slowSourceInitialVariance n) scoreScale j) := fun j ↦
    isProbabilityMeasure_slowRadiusQFallback hn
      (by unfold slowSourceInitialVariance; positivity) scoreScale j
  letI : ∀ j, IsProbabilityMeasure (slowRetainedSeedTarget m n q K j) := fun j ↦
    isProbabilityMeasure_slowRetainedSeedTarget hn hq4 hball j
  letI : IsProbabilityMeasure (slowInitialPair n) := by
    unfold slowInitialPair
    letI : IsProbabilityMeasure (slowInitialSeed n) :=
      isProbabilityMeasure_slowInitialSeed hn
    exact Measure.isProbabilityMeasure_map
      ((by fun_prop : Measurable
        (fun y : State n ↦ ((0 : State n), y))).aemeasurable)
  letI : ∀ j, IsProbabilityMeasure (slowExactTail m n q K j) := fun j ↦ by
    unfold slowExactTail
    exact Measure.isProbabilityMeasure_map
      ((by fun_prop : Measurable
        (fun y : State n ↦ ((0 : State n), y))).aemeasurable)
  infer_instance

/-- Exact complete-history replacement for the old opaque `haccuracy` premise.  An ideal
one-stream path theorem at success `33/40`, together with total operational path error
`k*error ≤ 1/40`, yields the required operational `4/5` accuracy. -/
theorem slowPathReadout_four_fifths_of_completeHistoryTV
    (hn : 1 ≤ n) (m k : Nat) {q eps : Real} (hq4 : 4 ≤ q)
    {K : Set (State n)} (hK : MeasurableSet K)
    (hball : ball (0 : State n) 1 ⊆ K)
    (slack boundSq : Nat → Real) (scoreScale : Real)
    (idealPath : Measure (Nat → ScoreSeed n)) [IsProbabilityMeasure idealPath]
    {error : ENNReal}
    (hpath : TVLe
      (slowActualOnePathLaw hn m k q eps hq4 K hK hball slack boundSq scoreScale)
      idealPath error)
    (herror : (k : ENNReal) * error ≤ ENNReal.ofReal (1 / 40 : Real))
    (readout : (Fin k → ((Finset.Iic m → State n) × State n)) → Real)
    (hreadout : Measurable readout) {lo hi : Real}
    (hideal : (33 / 40 : Real) ≤
      (Measure.pi (fun _ : Fin k ↦ idealPath)).real
        {omega | readout (independentPathScorePrefixCurrent m omega) ∈ Icc lo hi}) :
    (4 / 5 : Real) ≤
      (Measure.pi (fun _ : Fin k ↦
        slowActualOnePathLaw hn m k q eps hq4 K hK hball
          slack boundSq scoreScale)).real
        {omega | readout (independentPathScorePrefixCurrent m omega) ∈ Icc lo hi} := by
  apply four_fifths_of_independentFiniteHistoryTV_const
    (actual := slowActualOnePathLaw hn m k q eps hq4 K hK hball
      slack boundSq scoreScale)
    (ideal := idealPath) hpath herror
  · exact measurableSet_Icc.preimage
      (hreadout.comp (measurable_independentPathScorePrefixCurrent m))
  · exact hideal

/-- Strongest slow-source certificate presently obtainable without confusing a seed
marginal bound with a history bound.  Relative to the previous capstone, the opaque
operational `haccuracy` premise is replaced by (i) complete one-stream path TV and
(ii) ideal-path readout accuracy.  All phase TV/cost/warmness obligations remain closed. -/
theorem exists_sourceReferenceTVOneRunCertificate_slowSource_of_completeHistoryTV
    (hn : 21 ≤ n) (k : Nat) {N q eps : Real} (hN : 0 < N) (hq4 : 4 ≤ q)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K)
    (slack boundSq : Nat → Real) (hslack : ∀ i, 0 < slack i)
    (hbound : ∀ i, 0 < boundSq i) (scoreScale : Real)
    (readout :
      (Fin k → ((Finset.Iic (slowOperationalPhases n N) → State n) × State n)) → Real)
    (hreadout : Measurable readout)
    (idealPath : Measure (Nat → ScoreSeed n)) [IsProbabilityMeasure idealPath]
    {pathError : ENNReal}
    (hpath : TVLe
      (slowActualOnePathLaw (by omega : 1 ≤ n) (slowOperationalPhases n N) k q eps hq4
        K hK hball slack boundSq scoreScale) idealPath pathError)
    (hpathError : (k : ENNReal) * pathError ≤ ENNReal.ofReal (1 / 40 : Real))
    {runtimeConstant R requested lo hi : Real}
    (hbudget : (k : ENNReal) *
        (∑ i ∈ Finset.range (slowOperationalPhases n N),
          slowPhaseCostBound n (slowOperationalPhases n N) k q eps slack boundSq i) ≤
      Ttc.CVSourcePolynomialCutoffCapstone.sourceOneRunQueryBudget
        runtimeConstant n R requested)
    (hideal : (33 / 40 : Real) ≤
      (Measure.pi (fun _ : Fin k ↦ idealPath)).real
        {omega | readout
          (independentPathScorePrefixCurrent (slowOperationalPhases n N) omega) ∈
            Icc lo hi}) :
    ∃ reference : Measure
        (Fin k → Ttc.CVHeterogeneousHistoryReference.HeterogeneousHistoryState
          (State n) (State n)),
      SourceReferenceTVOneRunCertificate
        (@Ttc.CVHeterogeneousRetainedPathLaw.independentHeterogeneousRetainedPathLaw
          _ _ _ _ k
          (slowActiveCostedSchedule (by omega : 1 ≤ n)
            (slowOperationalPhases n N) k q eps
            (lt_of_lt_of_le (by norm_num) hq4) K hK slack boundSq scoreScale)
          (by
            letI : ∀ j, IsProbabilityMeasure
                (slowRetainedSeedTarget (slowOperationalPhases n N) n q K j) := fun j ↦
              isProbabilityMeasure_slowRetainedSeedTarget (by omega : 1 ≤ n) hq4 hball j
            letI : ∀ j, IsProbabilityMeasure
                (slowExactTail (slowOperationalPhases n N) n q K j) := fun j ↦ by
              unfold slowExactTail
              exact Measure.isProbabilityMeasure_map
                ((by fun_prop : Measurable
                  (fun y : State n ↦ ((0 : State n), y))).aemeasurable)
            intro i
            infer_instance)
          (slowInitialPair n) (slowOperationalPhases n N))
        reference (fun omega ↦ ∑ j, (omega j).1.1)
        (fun omega ↦ readout
          (Ttc.CVHeterogeneousRetainedPathLaw.independentStoredScorePrefixCurrent
            (slowOperationalPhases n N) omega))
        runtimeConstant n R requested lo hi := by
  apply exists_sourceReferenceTVOneRunCertificate_slowSource hn k hN hq4 heps heps1
    hK hKc hball slack boundSq hslack hbound scoreScale readout hreadout hbudget
  have hacc := slowPathReadout_four_fifths_of_completeHistoryTV
    (n := n) (by omega : 1 ≤ n) (slowOperationalPhases n N) k hq4 hK hball
    slack boundSq scoreScale idealPath hpath hpathError readout hreadout hideal
  simpa only [slowActualOnePathLaw, independentPathLaw,
    Ttc.CVIndependentStreamMoments.independentStreamLaw] using hacc

#print axioms slowActualOnePathLaw
#print axioms slowPathReadout_four_fifths_of_completeHistoryTV
#print axioms exists_sourceReferenceTVOneRunCertificate_slowSource_of_completeHistoryTV

end Ttc.CVSlowSourceCompleteHistoryAccuracy
