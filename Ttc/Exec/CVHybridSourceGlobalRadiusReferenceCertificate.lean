import Ttc.Exec.CVHybridSourceSwitchedGlobalRadiusOperational
import Ttc.Exec.CVGaussianCappedCostedSchedule
import Ttc.Exec.CVRelativeWeightedRetainedCertificate
import Ttc.Exec.CVColdHotScheduleSplit

/-!
Retained-reference certificate seam for the literal source selected-radius schedule.

The theorem in this file fixes the executable kernels, exact source phase count,
global radius, score-aware shares, retries, and inactive exact tail.  Its remaining
arguments are precisely the analytic/statistical certificate obligations.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Ttc.CVHybridSourceGlobalRadiusReferenceCertificate

open MeasureTheory ProbabilityTheory Metric Set Finset
open Arlib Arlib.Probability Arlib.MarkovChains
open Ttc.CVCorrected Ttc.CVHybridSchedule Ttc.CVSequentialPhaseSampler
open Ttc.CVSeedProjectedDependence Ttc.CVScoreSeedPhaseKernel
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVGaussianScoreAwareParameters
open Ttc.CVHybridRadiusQRecursiveStep Ttc.CVHybridRadiusQCanonicalOperational
open Ttc.CVHybridRadiusQSwitchedCanonicalOperational
open Ttc.CVHybridSourceSwitchedGlobalRadiusOperational
open Ttc.CVGaussianCappedCostedSchedule
open Ttc.CVHeterogeneousHistoryReference
open Ttc.CVHeterogeneousRetainedPathLaw
open Ttc.CVRelativeWeightedRetainedCertificate
open Ttc.CVSourceReferenceTVCapstone
open scoped ENNReal Classical BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

noncomputable def sourceScoreAwareSteps
    (initialWarm : ENNReal) (n k : Nat) (C eps : Real)
    (K : Set (State n)) (slack boundSq : Nat → Real) : Nat → Nat → Nat :=
  hybridRadiusQSwitchedCanonicalSteps initialWarm n
    (sourceOperationalRadiusQ n k C eps)
    (sourceOperationalN n C) (1 / (16 * (n : Real))) K
    (scoreAwareRetries (sourceOperationalPhases n C) k eps slack boundSq)
    (scoreAwareEta (sourceOperationalPhases n C) k eps slack boundSq)
    (scoreAwareZeta (sourceOperationalPhases n C) k eps slack boundSq)

noncomputable def sourceGlobalRadiusRawSchedule
    (hn : 1 ≤ n) (k : Nat) (C eps : Real) (hC : 1 ≤ C)
    (K : Set (State n)) (hK : MeasurableSet K)
    (slack boundSq : Nat → Real) (initialWarm : ENNReal) (scoreScale : Real) :
    Nat → Kernel (State n) (ScoreSeed n) :=
  sourceHybridRadiusQWarmFallbackSchedule (N := sourceOperationalN n C)
    (s0 := 1 / (16 * (n : Real))) hn (sourceOperationalRadiusQ n k C eps)
    (zero_lt_one.trans (sourceOperationalRadiusQ_gt_one hn k C eps))
    (by unfold sourceOperationalN; positivity)
    (by positivity : 0 < (1 / (16 * (n : Real)) : Real)) K hK
    (sourceScoreAwareSteps initialWarm n k C eps K slack boundSq)
    (scoreAwareRetries (sourceOperationalPhases n C) k eps slack boundSq) scoreScale

noncomputable def sourceGlobalRadiusRawCostedSchedule
    (hn : 1 ≤ n) (k : Nat) (C eps : Real) (hC : 1 ≤ C)
    (K : Set (State n)) (hK : MeasurableSet K)
    (slack boundSq : Nat → Real) (initialWarm : ENNReal) (scoreScale : Real) :
    Nat → Kernel (State n) (ENNReal × ScoreSeed n) :=
  sourceHybridRadiusQWarmFallbackCostedSchedule (N := sourceOperationalN n C)
    (s0 := 1 / (16 * (n : Real))) hn
    (sourceOperationalRadiusQ n k C eps)
    (zero_lt_one.trans (sourceOperationalRadiusQ_gt_one hn k C eps))
    (by unfold sourceOperationalN; positivity)
    (by positivity : 0 < (1 / (16 * (n : Real)) : Real)) K hK
    (sourceScoreAwareSteps initialWarm n k C eps K slack boundSq)
    (scoreAwareRetries (sourceOperationalPhases n C) k eps slack boundSq) scoreScale

instance sourceGlobalRadiusRawSchedule.isMarkovKernel
    (hn : 1 ≤ n) (k : Nat) (C eps : Real) (hC : 1 ≤ C)
    (K : Set (State n)) (hK : MeasurableSet K)
    (slack boundSq : Nat → Real) (initialWarm : ENNReal) (scoreScale : Real)
    (i : Nat) : IsMarkovKernel
      (sourceGlobalRadiusRawSchedule hn k C eps hC K hK slack boundSq
        initialWarm scoreScale i) := by
  unfold sourceGlobalRadiusRawSchedule
  infer_instance

instance sourceGlobalRadiusRawCostedSchedule.isMarkovKernel
    (hn : 1 ≤ n) (k : Nat) (C eps : Real) (hC : 1 ≤ C)
    (K : Set (State n)) (hK : MeasurableSet K)
    (slack boundSq : Nat → Real) (initialWarm : ENNReal) (scoreScale : Real)
    (i : Nat) : IsMarkovKernel
      (sourceGlobalRadiusRawCostedSchedule hn k C eps hC K hK slack boundSq
        initialWarm scoreScale i) := by
  unfold sourceGlobalRadiusRawCostedSchedule
  infer_instance

noncomputable def sourceGlobalRadiusActiveSchedule
    (hn : 1 ≤ n) (k : Nat) (C eps : Real) (hC : 1 ≤ C)
    (K : Set (State n)) (hK : MeasurableSet K)
    (slack boundSq : Nat → Real) (initialWarm : ENNReal) (scoreScale : Real)
    (tail : Nat → Measure (ScoreSeed n)) : Nat → Kernel (State n) (ScoreSeed n) :=
  activeReferenceTailSchedule (sourceOperationalPhases n C)
    (sourceGlobalRadiusRawSchedule hn k C eps hC K hK slack boundSq initialWarm scoreScale)
    tail

noncomputable def sourceGlobalRadiusActiveCostedSchedule
    (hn : 1 ≤ n) (k : Nat) (C eps : Real) (hC : 1 ≤ C)
    (K : Set (State n)) (hK : MeasurableSet K)
    (slack boundSq : Nat → Real) (initialWarm : ENNReal) (scoreScale : Real)
    (tail : Nat → Measure (ScoreSeed n)) :
    Nat → Kernel (State n) (ENNReal × ScoreSeed n) :=
  costedActiveReferenceTailSchedule (sourceOperationalPhases n C)
    (sourceGlobalRadiusRawCostedSchedule hn k C eps hC K hK slack boundSq
      initialWarm scoreScale) tail

instance sourceGlobalRadiusActiveSchedule.isMarkovKernel
    (hn : 1 ≤ n) (k : Nat) (C eps : Real) (hC : 1 ≤ C)
    (K : Set (State n)) (hK : MeasurableSet K)
    (slack boundSq : Nat → Real) (initialWarm : ENNReal) (scoreScale : Real)
    (tail : Nat → Measure (ScoreSeed n)) [∀ i, IsProbabilityMeasure (tail i)]
    (i : Nat) : IsMarkovKernel
      (sourceGlobalRadiusActiveSchedule hn k C eps hC K hK slack boundSq
        initialWarm scoreScale tail i) := by
  unfold sourceGlobalRadiusActiveSchedule
  infer_instance

instance sourceGlobalRadiusActiveCostedSchedule.isMarkovKernel
    (hn : 1 ≤ n) (k : Nat) (C eps : Real) (hC : 1 ≤ C)
    (K : Set (State n)) (hK : MeasurableSet K)
    (slack boundSq : Nat → Real) (initialWarm : ENNReal) (scoreScale : Real)
    (tail : Nat → Measure (ScoreSeed n)) [∀ i, IsProbabilityMeasure (tail i)]
    (i : Nat) : IsMarkovKernel
      (sourceGlobalRadiusActiveCostedSchedule hn k C eps hC K hK slack boundSq
        initialWarm scoreScale tail i) := by
  unfold sourceGlobalRadiusActiveCostedSchedule
  infer_instance

theorem map_snd_sourceGlobalRadiusActiveCostedSchedule
    (hn : 1 ≤ n) (k : Nat) (C eps : Real) (hC : 1 ≤ C)
    (K : Set (State n)) (hK : MeasurableSet K)
    (slack boundSq : Nat → Real) (initialWarm : ENNReal) (scoreScale : Real)
    (tail : Nat → Measure (ScoreSeed n)) [∀ i, IsProbabilityMeasure (tail i)]
    (i : Nat) (x : State n) :
    Measure.map Prod.snd
        (sourceGlobalRadiusActiveCostedSchedule hn k C eps hC K hK slack boundSq
          initialWarm scoreScale tail i x) =
      sourceGlobalRadiusActiveSchedule hn k C eps hC K hK slack boundSq
        initialWarm scoreScale tail i x := by
  apply map_snd_costedActiveReferenceTailSchedule
  intro j y
  exact map_snd_sourceHybridRadiusQWarmFallbackCostedSchedule
    (N := sourceOperationalN n C) (s0 := 1 / (16 * (n : Real))) hn
    (sourceOperationalRadiusQ n k C eps)
    (zero_lt_one.trans (sourceOperationalRadiusQ_gt_one hn k C eps))
    (by unfold sourceOperationalN; positivity)
    (by positivity : 0 < (1 / (16 * (n : Real)) : Real)) K hK
    (sourceScoreAwareSteps initialWarm n k C eps K slack boundSq)
    (scoreAwareRetries (sourceOperationalPhases n C) k eps slack boundSq)
    scoreScale j y

/-- Concrete retained-reference wrapper at the exact source schedule.  Unlike the
generic certificate constructor, no kernel, phase count, radius, retry schedule, or
cost-erasure premise remains. -/
theorem exists_sourceReferenceTVOneRunCertificate_hybridSourceGlobalRadius
    (hn : 21 ≤ n) (k : Nat) {C eps : Real}
    (hC : 1 ≤ C)
    (K : Set (State n)) (hK : MeasurableSet K)
    (slack boundSq : Nat → Real) (initialWarm : ENNReal) (scoreScale : Real)
    (tail : Nat → Measure (ScoreSeed n)) [∀ i, IsProbabilityMeasure (tail i)]
    (mu : Measure (ScoreSeed n)) [IsProbabilityMeasure mu]
    (nu0 : Measure (HeterogeneousHistoryState (State n) (State n)))
    [IsProbabilityMeasure nu0]
    (tau : Nat → Measure (State n)) [∀ i, IsProbabilityMeasure (tau i)]
    (e B : Nat → ENNReal) {d initialBudget : ENNReal}
    (hinitTV : TVLe (initialHeterogeneousHistoryLaw mu) nu0 d)
    (hinitState : Measure.map Prod.snd nu0 = tau 0)
    (hinitMean : (∫⁻ z, z.1.1 ∂nu0) ≤ initialBudget)
    (hphaseSeedTV : ∀ i,
      TVLe ((tau i).bind
        (Kernel.map
          (sourceGlobalRadiusActiveCostedSchedule (by omega : 1 ≤ n) k C eps hC
            K hK slack boundSq initialWarm scoreScale tail i)
          (fun y : ENNReal × ScoreSeed n ↦ y.2.2)))
        (tau (i + 1)) (e i))
    (hphaseCost : ∀ i,
      (∫⁻ x, heterogeneousStepMean
        (sourceGlobalRadiusActiveCostedSchedule (by omega : 1 ≤ n) k C eps hC
          K hK slack boundSq initialWarm scoreScale tail i) x ∂tau i) ≤ B i)
    (readout :
      (Fin k → ((Finset.Iic (sourceOperationalPhases n C) → State n) × State n)) →
        Real)
    (hreadout : Measurable readout)
    {runtimeConstant R requested lo hi : Real}
    (herror : (k : ENNReal) * (d + ∑ i ∈ range (sourceOperationalPhases n C), e i) ≤
      ENNReal.ofReal (1 / 40 : Real))
    (hbudget : (k : ENNReal) *
        (initialBudget + ∑ i ∈ range (sourceOperationalPhases n C), B i) ≤
      Ttc.CVSourcePolynomialCutoffCapstone.sourceOneRunQueryBudget
        runtimeConstant n R requested)
    (haccuracy : 4 / 5 ≤
      (Ttc.CVIndependentStreamDependence.independentPathLaw k
        (stateScheduleFromSeed
          (sourceGlobalRadiusActiveSchedule (by omega : 1 ≤ n) k C eps hC K hK
            slack boundSq initialWarm scoreScale tail)) mu).real
        {omega | readout
          (independentPathScorePrefixCurrent (sourceOperationalPhases n C) omega) ∈
            Icc lo hi}) :
    ∃ reference : Measure
        (Fin k → HeterogeneousHistoryState (State n) (State n)),
      SourceReferenceTVOneRunCertificate
        (independentHeterogeneousRetainedPathLaw k
          (sourceGlobalRadiusActiveCostedSchedule (by omega : 1 ≤ n) k C eps hC K hK
            slack boundSq initialWarm scoreScale tail)
          mu (sourceOperationalPhases n C))
        reference (fun omega ↦ ∑ j, (omega j).1.1)
        (fun omega ↦ readout
          (independentStoredScorePrefixCurrent (sourceOperationalPhases n C) omega))
      runtimeConstant n R requested lo hi := by
  apply exists_sourceReferenceTVOneRunCertificate_of_pathReadoutAccuracy
    (sourceGlobalRadiusActiveCostedSchedule (by omega : 1 ≤ n) k C eps hC K hK
      slack boundSq initialWarm scoreScale tail)
    (sourceGlobalRadiusActiveSchedule (by omega : 1 ≤ n) k C eps hC K hK
      slack boundSq initialWarm scoreScale tail)
    mu
    (map_snd_sourceGlobalRadiusActiveCostedSchedule (by omega : 1 ≤ n) k C eps hC K hK
      slack boundSq initialWarm scoreScale tail)
    nu0 tau e B hinitTV hinitState hinitMean hphaseSeedTV hphaseCost n
    (sourceOperationalPhases n C) k readout hreadout herror hbudget haccuracy

/-- Strongest currently closed retained-reference constructor for the switched source
schedule.  The initial reference is fixed to the actual zero-cost initial history, so
all initial coupling and initial-cost premises disappear.  The remaining phase-TV,
phase-cost, aggregate scalar, and ordinary-path accuracy hypotheses are displayed
directly; in particular there is no audit or certificate structure argument. -/
theorem exists_sourceReferenceTVOneRunCertificate_hybridSourceGlobalRadius_of_retainedPhases
    (hn : 21 ≤ n) (k : Nat) {C eps : Real}
    (hC : 1 ≤ C)
    (K : Set (State n)) (hK : MeasurableSet K)
    (slack boundSq : Nat → Real) (initialWarm : ENNReal) (scoreScale : Real)
    (tail : Nat → Measure (ScoreSeed n)) [∀ i, IsProbabilityMeasure (tail i)]
    (mu : Measure (ScoreSeed n)) [IsProbabilityMeasure mu]
    (tau : Nat → Measure (State n)) [∀ i, IsProbabilityMeasure (tau i)]
    (e B : Nat → ENNReal)
    (htau0 : Measure.map Prod.snd mu = tau 0)
    (hphaseSeedTV : ∀ i,
      TVLe ((tau i).bind
        (Kernel.map
          (sourceGlobalRadiusActiveCostedSchedule (by omega : 1 ≤ n) k C eps hC
            K hK slack boundSq initialWarm scoreScale tail i)
          (fun y : ENNReal × ScoreSeed n ↦ y.2.2)))
        (tau (i + 1)) (e i))
    (hphaseCost : ∀ i,
      (∫⁻ x, heterogeneousStepMean
        (sourceGlobalRadiusActiveCostedSchedule (by omega : 1 ≤ n) k C eps hC
          K hK slack boundSq initialWarm scoreScale tail i) x ∂tau i) ≤ B i)
    (readout :
      (Fin k → ((Finset.Iic (sourceOperationalPhases n C) → State n) × State n)) →
        Real)
    (hreadout : Measurable readout)
    {runtimeConstant R requested lo hi : Real}
    (herror : (k : ENNReal) *
        (∑ i ∈ range (sourceOperationalPhases n C), e i) ≤
      ENNReal.ofReal (1 / 40 : Real))
    (hbudget : (k : ENNReal) *
        (∑ i ∈ range (sourceOperationalPhases n C), B i) ≤
      Ttc.CVSourcePolynomialCutoffCapstone.sourceOneRunQueryBudget
        runtimeConstant n R requested)
    (haccuracy : 4 / 5 ≤
      (Ttc.CVIndependentStreamDependence.independentPathLaw k
        (stateScheduleFromSeed
          (sourceGlobalRadiusActiveSchedule (by omega : 1 ≤ n) k C eps hC K hK
            slack boundSq initialWarm scoreScale tail)) mu).real
        {omega | readout
          (independentPathScorePrefixCurrent (sourceOperationalPhases n C) omega) ∈
            Icc lo hi}) :
    ∃ reference : Measure
        (Fin k → HeterogeneousHistoryState (State n) (State n)),
      SourceReferenceTVOneRunCertificate
        (independentHeterogeneousRetainedPathLaw k
          (sourceGlobalRadiusActiveCostedSchedule (by omega : 1 ≤ n) k C eps hC K hK
            slack boundSq initialWarm scoreScale tail)
          mu (sourceOperationalPhases n C))
        reference (fun omega ↦ ∑ j, (omega j).1.1)
        (fun omega ↦ readout
          (independentStoredScorePrefixCurrent (sourceOperationalPhases n C) omega))
        runtimeConstant n R requested lo hi := by
  apply exists_sourceReferenceTVOneRunCertificate_hybridSourceGlobalRadius
    hn k hC K hK slack boundSq initialWarm scoreScale tail mu
    (initialHeterogeneousHistoryLaw mu) tau e B
    (d := 0) (initialBudget := 0)
    (TVLe.refl _)
  · unfold initialHeterogeneousHistoryLaw
    rw [Measure.map_map measurable_snd measurable_initialHeterogeneousHistoryState]
    change Measure.map Prod.snd mu = tau 0
    exact htau0
  · unfold initialHeterogeneousHistoryLaw
    change (∫⁻ z, (Prod.fst ∘ Prod.fst) z
      ∂Measure.map initialHeterogeneousHistoryState mu) ≤ 0
    rw [lintegral_map (measurable_fst.comp measurable_fst)
      measurable_initialHeterogeneousHistoryState]
    simp [initialHeterogeneousHistoryState]
  · exact hphaseSeedTV
  · exact hphaseCost
  · exact hreadout
  · simpa using herror
  · simpa using hbudget
  · exact haccuracy

#print axioms map_snd_sourceGlobalRadiusActiveCostedSchedule
#print axioms exists_sourceReferenceTVOneRunCertificate_hybridSourceGlobalRadius
#print axioms
  exists_sourceReferenceTVOneRunCertificate_hybridSourceGlobalRadius_of_retainedPhases

end Ttc.CVHybridSourceGlobalRadiusReferenceCertificate
