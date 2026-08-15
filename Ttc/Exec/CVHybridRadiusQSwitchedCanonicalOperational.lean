import Ttc.Exec.CVHybridRadiusQSwitchedRecursiveOperational
import Ttc.Exec.CVHybridRadiusQOperationalFullPair
import Ttc.Exec.CVHybridRadiusFourCanonicalOperational

/-! Canonical adjustable-deadline operation at a globally selected radius `q`. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Ttc.CVHybridRadiusQSwitchedCanonicalOperational

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVCorrected Ttc.CVHybridSchedule Ttc.CVSequentialPhaseSampler
open Ttc.CVSeedProjectedDependence Ttc.CVScoreSeedPhaseKernel
open Ttc.CVWarmBudgetRecurrence Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVHybridRadiusQRecursiveStep Ttc.CVHybridRadiusQSwitchWarm
open Ttc.CVHybridRadiusQSwitchedRecursiveOperational
open Ttc.CVHybridRadiusQOperationalFullPair Ttc.CVAdaptiveRadiusQPrimitives
open Ttc.CVGaussianAdaptiveMixing Ttc.CVContinuingRetryParameters
open Ttc.CVHybridRadiusFourCanonicalOperational
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

noncomputable def hybridRadiusQSwitchedCanonicalSteps
    (initialWarm : ENNReal) (n : Nat) (q N s0 : Real) (K : Set (State n))
    (retries : Nat → Nat) (etaShare zetaShare : Nat → ENNReal) : Nat → Nat → Nat :=
  fun i _ ↦ adjustableSpeedyDeadline n
    (radiusQDelta n q (sigmaSq n N s0 i)) (sigmaSq n N s0 i)
    ((2 * hybridRadiusQSwitchedWarmBudget initialWarm n q N s0 K retries i) / etaShare i)
    (zetaShare i)

noncomputable def hybridRadiusQCanonicalMixError
    (n : Nat) (q : Real) (etaShare zetaShare : Nat → ENNReal)
    (retries : Nat → Nat) : Nat → ENNReal := fun i ↦
  32 * zetaShare i + (etaShare i + continuingContraction ^ retries i) +
    ENNReal.ofReal ((q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n)

/-- Complete selected-radius phase mixing and actual-seed recurrence.  The global
selector can now make the displayed tail summable over all streams and phases. -/
noncomputable def seedProjectedOperational_hybridRadiusQ_switched_canonical
    (hn : 21 ≤ n) (m : Nat) {q N s0 : Real} (hq : 1 < q)
    (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hrate0 : ∀ i, i + 1 < m → 0 ≤ phaseRate n N s0 i)
    (hrad : ∀ i, i < m →
      1 ≤ q * Real.sqrt (sigmaSq n N s0 i) * Real.sqrt n)
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
      (hybridRadiusQSeedTarget n q N s0 K 0))
    (htailSeed : ∀ i, Measure.map Prod.snd (tail i) =
      hybridRadiusQSeedTarget n q N s0 K i)
    (u : (i : Nat) → (Finset.Iic i → ScoreSeed n) → Real)
    (v : Nat → State n → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i,
      accuracyU
          (inhomogeneousPathMeasure
            (stateScheduleFromSeed
              (activeReferenceTailSchedule m
                (sourceHybridRadiusQWarmFallbackSchedule (by omega : 1 ≤ n)
                  q (zero_lt_one.trans hq) hN hs0 K hK
                  (hybridRadiusQSwitchedCanonicalSteps initialWarm n q N s0 K retries
                    etaShare zetaShare) retries scoreScale) tail)) mu0)
          V (correctedAlpha m accuracyEta) i =
        fun omega ↦ u i (Preorder.frestrictLe i omega))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (omega (i + 1)).1)
    (hbudget : ∀ i, i + 1 < m →
      2 * (hybridRadiusQCanonicalMixError n q etaShare zetaShare retries i).toReal ≤
        correctedNu m accuracyEta) :
    SeedProjectedOperational
      (stateScheduleFromSeed
        (activeReferenceTailSchedule m
          (sourceHybridRadiusQWarmFallbackSchedule (by omega : 1 ≤ n)
            q (zero_lt_one.trans hq) hN hs0 K hK
            (hybridRadiusQSwitchedCanonicalSteps initialWarm n q N s0 K retries
              etaShare zetaShare) retries scoreScale) tail))
      (activeReferenceTailSchedule m
        (sourceHybridRadiusQWarmFallbackSchedule (by omega : 1 ≤ n)
          q (zero_lt_one.trans hq) hN hs0 K hK
          (hybridRadiusQSwitchedCanonicalSteps initialWarm n q N s0 K retries
            etaShare zetaShare) retries scoreScale) tail)
      Prod.snd Prod.fst mu0 V m accuracyEta := by
  let hn1 : 1 ≤ n := by omega
  let hq0 : 0 < q := zero_lt_one.trans hq
  let steps := hybridRadiusQSwitchedCanonicalSteps initialWarm n q N s0 K retries
    etaShare zetaShare
  let warm := hybridRadiusQSwitchedWarmBudget initialWarm n q N s0 K retries
  let mixError := hybridRadiusQCanonicalMixError n q etaShare zetaShare retries
  letI : ∀ i, IsProbabilityMeasure
      (hybridRadiusFourFullPairReference m n N s0 K i) := fun i ↦
    isProbabilityMeasure_hybridRadiusFourFullPairReference hn1 m hN hs0 K hball hfin i
  letI : ∀ j, IsProbabilityMeasure (hybridRadiusQFallback n N s0 scoreScale j) :=
    fun j ↦ isProbabilityMeasure_hybridRadiusQFallback hn1 hN hs0 scoreScale j
  apply seedProjectedOperational_hybridRadiusQ_switched_recursive hn1 m hq0 hN hs0 hK hKc
    hball hfin hrate0 hrad steps retries scoreScale tail mu0 V accuracyEta
    (hybridRadiusFourFullPairReference m n N s0 K) initialWarm hinitialOne hstart
    htailSeed mixError
  · intro i hi
    unfold mixError hybridRadiusQCanonicalMixError
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.add_ne_top.2
        ⟨ENNReal.mul_ne_top (by simp) (hzetatop i),
          ENNReal.add_ne_top.2 ⟨hetatop i, ENNReal.pow_ne_top (by
            norm_num [continuingContraction])⟩⟩, ENNReal.ofReal_ne_top⟩
  · intro i hi rho hwarm hprob
    letI : IsProbabilityMeasure rho := hprob
    have hrecOne : 1 ≤ warm i := one_le_recursiveWarmBudget hinitialOne
      (one_le_hybridRadiusQSwitchedAcceptedFactor n q N s0 K retries) i
    have hrecTop : warm i ≠ ⊤ := recursiveWarmBudget_ne_top hinitialTop
      (hybridRadiusQSwitchedAcceptedFactor_ne_top n q N s0 K retries)
      (hybridRadiusQFallbackFactor_ne_top hn1 hN hs0 hK hfin) i
    have hM1 : 1 ≤ 2 * warm i := hrecOne.trans
      (le_mul_of_one_le_left' (by norm_num))
    have hMtop : 2 * warm i ≠ ⊤ := ENNReal.mul_ne_top (by simp) hrecTop
    have hpair :=
      tvLe_hybridRadiusQWarmFallbackKernel_fullPair_adjustable_zeroSafe_of_eq
        (m := m) hn hq hN hs0 hK hKc hball hfin steps retries
        (hybridRadiusQFallback n N s0 scoreScale) i (Nat.lt_of_succ_lt hi) rho
        hM1 hMtop (heta0 i) (hetatop i) (heta1 i) (hzeta0 i) (hzetatop i)
        (hzeta16 i) (hrad i (Nat.lt_of_succ_lt hi))
        (by simpa only [warm, hybridRadiusQSwitchedWarmBudget, hybridRadiusQSeedTarget] using hwarm)
        (retries i) (by rfl) rfl
    simpa only [sourceHybridRadiusQWarmFallbackSchedule, mixError,
      hybridRadiusQCanonicalMixError, hybridRadiusFourFullPairReference] using hpair
  · exact hu
  · exact hv
  · simpa only [steps] using hU
  · exact hV
  · simpa only [mixError] using hbudget

#print axioms seedProjectedOperational_hybridRadiusQ_switched_canonical

end Ttc.CVHybridRadiusQSwitchedCanonicalOperational
