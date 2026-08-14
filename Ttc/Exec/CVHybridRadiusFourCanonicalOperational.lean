import Ttc.Exec.CVHybridRadiusFourRecursiveOperational
import Ttc.Exec.CVHybridRadiusFourOperationalFullScore
import Ttc.Exec.CVIdealCombinedAccepted

/-!
# Canonical adjustable-deadline operation on the hybrid radius-four schedule

This module eliminates the generic phase-mixing premise from the recursive operation.
The remaining dependence budget is deliberately explicit: it includes one fixed
radius-four Gaussian-tail term per active phase.  Consequently this constructor is a
finite-input certificate, but not by itself an unconditional all-input runtime theorem;
an all-input theorem must replace the fixed radius `4` by an input-dependent adjustable
radius so that the summed tail is allocated below the source error budget.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Ttc.CVHybridRadiusFourCanonicalOperational

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVCorrected
open Ttc.CVHybridSchedule
open Ttc.CVSequentialPhaseSampler
open Ttc.CVSeedProjectedDependence
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVRecursiveWarmOperational
open Ttc.CVWarmBudgetRecurrence
open Ttc.CVIndependentStreamDependence
open Ttc.CVHybridRadiusFourRecursiveStep
open Ttc.CVHybridRadiusFourRecursiveOperational
open Ttc.CVHybridRadiusFourOperationalFullScore
open Ttc.CVHybridRadiusFourFallbackSchedule
open Ttc.CVGaussianAdaptiveMixing
open Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVContinuingRetryParameters
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

noncomputable def hybridRadiusFourWarmBudget
    (initialWarm : ENNReal) (n : Nat) (N s0 : Real) (K : Set (State n))
    (retries : Nat → Nat) : Nat → ENNReal :=
  recursiveWarmBudget initialWarm
    (hybridRadiusFourAcceptedFactor n N s0 retries)
    (hybridRadiusFourFallbackFactor n N s0 K)

noncomputable def hybridRadiusFourCanonicalSteps
    (initialWarm : ENNReal) (n : Nat) (N s0 : Real) (K : Set (State n))
    (retries : Nat → Nat) (etaShare zetaShare : Nat → ENNReal) : Nat → Nat → Nat :=
  fun i _ ↦ adjustableSpeedyDeadline n
    (hybridRadiusFourDelta n N s0 i) (sigmaSq n N s0 i)
    ((2 * hybridRadiusFourWarmBudget initialWarm n N s0 K retries i) / etaShare i)
    (zetaShare i)

noncomputable def hybridRadiusFourCanonicalMixError
    (n : Nat) (etaShare zetaShare : Nat → ENNReal) (retries : Nat → Nat) :
    Nat → ENNReal := fun i ↦
  32 * zetaShare i + (etaShare i + continuingContraction ^ retries i) +
    ENNReal.ofReal ((4 * Real.exp (-(15 : Real) / 2)) ^ n)

noncomputable def hybridRadiusFourFullPairReference
    (m n : Nat) (N s0 : Real) (K : Set (State n)) (i : Nat) :
    Measure (ScoreSeed n) :=
  scoreSeedReference (1 - 1 / (2 * (n : Real)))
    (coolLaw m (sigmaSq n N s0) K i)

theorem isProbabilityMeasure_hybridRadiusFourFullPairReference
    (hn : 1 ≤ n) (m : Nat) {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    (K : Set (State n)) (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (i : Nat) :
    IsProbabilityMeasure (hybridRadiusFourFullPairReference m n N s0 K i) := by
  unfold hybridRadiusFourFullPairReference scoreSeedReference
  letI : IsProbabilityMeasure (coolLaw m (sigmaSq n N s0) K i) :=
    coolLaw_isProbabilityMeasure (sigmaSq_pos hn hN hs0) hball hfin i
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Fully mixed recursive operation at the literal adjustable deadline.  No phase-TV
or geometric mixing premise remains.  `hbudget` is the exact accumulated dependence
condition and therefore honestly exposes the fixed-tail limitation. -/
noncomputable def seedProjectedOperational_hybridRadiusFour_canonical
    (hn : 21 ≤ n) (m : Nat) {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hrate0 : ∀ i, i + 1 < m → 0 ≤ phaseRate n N s0 i)
    (hrateHalf : ∀ i, i + 1 < m → phaseRate n N s0 i ≤ 1 / 2)
    (hrad : ∀ i, i < m →
      1 ≤ 4 * Real.sqrt (sigmaSq n N s0 i) * Real.sqrt n)
    (hradTwo : ∀ i, i < m →
      1 ≤ 2 * Real.sqrt (sigmaSq n N s0 i) * Real.sqrt n)
    (retries : Nat → Nat) (scoreScale : Real)
    (etaShare zetaShare : Nat → ENNReal)
    (heta0 : ∀ i, etaShare i ≠ 0) (hetatop : ∀ i, etaShare i ≠ ⊤)
    (heta1 : ∀ i, etaShare i ≤ 1)
    (hzeta0 : ∀ i, zetaShare i ≠ 0) (hzetatop : ∀ i, zetaShare i ≠ ⊤)
    (hzeta16 : ∀ i, zetaShare i ≤ ENNReal.ofReal (1 / 16 : Real))
    (tail : Nat → Measure (ScoreSeed n)) [∀ i, IsProbabilityMeasure (tail i)]
    (mu0 : Measure (ScoreSeed n)) [IsProbabilityMeasure mu0]
    (V : Nat → (Nat → ScoreSeed n) → Real) (accuracyEta : Real)
    (initialWarm : ENNReal) (hinitialOne : 1 ≤ initialWarm)
    (hinitialTop : initialWarm ≠ ⊤)
    (hstart : IsWarm initialWarm (Measure.map Prod.snd mu0)
      (hybridRadiusFourSeedTarget n N s0 K 0))
    (htailSeed : ∀ i, Measure.map Prod.snd (tail i) =
      hybridRadiusFourSeedTarget n N s0 K i)
    (u : (i : Nat) → (Finset.Iic i → ScoreSeed n) → Real)
    (v : Nat → State n → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i,
      accuracyU
          (inhomogeneousPathMeasure
            (stateScheduleFromSeed
              (activeReferenceTailSchedule m
                (sourceHybridRadiusFourWarmFallbackSchedule (by omega : 1 ≤ n)
                  hN hs0 K hK
                  (hybridRadiusFourCanonicalSteps initialWarm n N s0 K retries
                    etaShare zetaShare)
                  retries scoreScale) tail)) mu0)
          V (correctedAlpha m accuracyEta) i =
        fun omega ↦ u i (Preorder.frestrictLe i omega))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (omega (i + 1)).1)
    (hbudget : ∀ i, i + 1 < m →
      2 * (hybridRadiusFourCanonicalMixError n etaShare zetaShare retries i).toReal ≤
        correctedNu m accuracyEta) :
    SeedProjectedOperational
      (stateScheduleFromSeed
        (activeReferenceTailSchedule m
          (sourceHybridRadiusFourWarmFallbackSchedule (by omega : 1 ≤ n)
            hN hs0 K hK
            (hybridRadiusFourCanonicalSteps initialWarm n N s0 K retries
              etaShare zetaShare)
            retries scoreScale) tail))
      (activeReferenceTailSchedule m
        (sourceHybridRadiusFourWarmFallbackSchedule (by omega : 1 ≤ n)
          hN hs0 K hK
          (hybridRadiusFourCanonicalSteps initialWarm n N s0 K retries
            etaShare zetaShare)
          retries scoreScale) tail)
      Prod.snd Prod.fst mu0 V m accuracyEta := by
  let hn1 : 1 ≤ n := by omega
  let steps := hybridRadiusFourCanonicalSteps initialWarm n N s0 K retries
    etaShare zetaShare
  let accepted := hybridRadiusFourAcceptedFactor n N s0 retries
  let fallbackFactor := hybridRadiusFourFallbackFactor n N s0 K
  let warm := hybridRadiusFourWarmBudget initialWarm n N s0 K retries
  let mixError := hybridRadiusFourCanonicalMixError n etaShare zetaShare retries
  letI : ∀ i, IsProbabilityMeasure
      (hybridRadiusFourFullPairReference m n N s0 K i) := fun i ↦
    isProbabilityMeasure_hybridRadiusFourFullPairReference hn1 m hN hs0 K hball hfin i
  letI : ∀ j, IsProbabilityMeasure
      (hybridRadiusFourFallback n N s0 scoreScale j) := fun j ↦
    isProbabilityMeasure_hybridRadiusFourFallback hn1 hN hs0 scoreScale j
  apply seedProjectedOperational_hybridRadiusFour_recursive hn1 m hN hs0 hK hKc
    hball hfin hrate0 hrateHalf hrad hradTwo steps retries scoreScale tail mu0 V
    accuracyEta (hybridRadiusFourFullPairReference m n N s0 K)
    initialWarm hinitialOne hstart htailSeed mixError
  · intro i hi
    unfold mixError hybridRadiusFourCanonicalMixError
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.add_ne_top.2
        ⟨ENNReal.mul_ne_top (by simp) (hzetatop i),
          ENNReal.add_ne_top.2
            ⟨hetatop i, ENNReal.pow_ne_top (by
              norm_num [continuingContraction])⟩⟩,
        ENNReal.ofReal_ne_top⟩
  · intro i hi rho hwarm hprob
    letI : IsProbabilityMeasure rho := hprob
    have hrecOne : 1 ≤ warm i := by
      exact one_le_recursiveWarmBudget hinitialOne
        (one_le_hybridRadiusFourAcceptedFactor n N s0 retries) i
    have hrecTop : warm i ≠ ⊤ := by
      exact recursiveWarmBudget_ne_top hinitialTop
        (hybridRadiusFourAcceptedFactor_ne_top n N s0 retries)
        (hybridRadiusFourFallbackFactor_ne_top hn1 hN hs0 hK hfin) i
    have hM1 : 1 ≤ 2 * warm i := by
      calc 1 ≤ warm i := hrecOne
           _ ≤ 2 * warm i := by exact le_mul_of_one_le_left' (by norm_num)
    have hMtop : 2 * warm i ≠ ⊤ := ENNReal.mul_ne_top (by simp) hrecTop
    have hpair :=
      tvLe_hybridRadiusFourWarmFallbackKernel_fullPair_adjustable_zeroSafe_of_eq
        (m := m) hn hN hs0 hK hKc hball hfin steps retries
        (hybridRadiusFourFallback n N s0 scoreScale) i
        (Nat.lt_of_succ_lt hi) rho hM1 hMtop (heta0 i) (hetatop i) (heta1 i)
        (hzeta0 i) (hzetatop i) (hzeta16 i) (hrad i (Nat.lt_of_succ_lt hi))
        (by simpa only [warm, hybridRadiusFourWarmBudget, hybridRadiusFourSeedTarget,
          hybridRadiusFourBody, hybridRadiusFourDelta] using hwarm)
        (retries i) (by rfl) rfl
    simpa only [sourceHybridRadiusFourWarmFallbackSchedule, mixError,
      hybridRadiusFourCanonicalMixError, hybridRadiusFourFullPairReference,
      hybridRadiusFourBody, hybridRadiusFourDelta] using hpair
  · exact hu
  · exact hv
  · simpa only [steps] using hU
  · exact hV
  · simpa only [mixError] using hbudget

#print axioms seedProjectedOperational_hybridRadiusFour_canonical

end Ttc.CVHybridRadiusFourCanonicalOperational
