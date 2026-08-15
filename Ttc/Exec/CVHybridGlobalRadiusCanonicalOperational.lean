import Ttc.Exec.CVGlobalRadiusDependenceBudget
import Ttc.Exec.CVGlobalRadiusTerminalBody

/-! The canonical operational sampler at the globally selected truncation radius. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Ttc.CVHybridGlobalRadiusCanonicalOperational

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVCorrected Ttc.CVHybridSchedule Ttc.CVSequentialPhaseSampler
open Ttc.CVSeedProjectedDependence Ttc.CVScoreSeedPhaseKernel
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVIndependentStreamDependence
open Ttc.CVGaussianScoreAwareParameters
open Ttc.CVContinuingRetryParameters
open Ttc.CVHybridRadiusQRecursiveStep Ttc.CVHybridRadiusQRecursiveOperational
open Ttc.CVHybridRadiusQCanonicalOperational
open Ttc.CVGlobalLogarithmicRadius Ttc.CVGlobalRadiusDependenceBudget
open Ttc.CVGlobalRadiusTerminalBody
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- The selected logarithmic radius, score-aware shares, and retry count discharge
the entire phase-mixing premise, including the truncation tail. -/
noncomputable def seedProjectedOperational_hybridGlobalRadius_scoreAware
    (hn : 21 ≤ n) (m k : Nat) (hk : 1 ≤ k) {N s0 eps : Real}
    (hN : 0 < N) (hs0 : 0 < s0) (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hfour : ∀ i, i < m →
      1 ≤ 4 * Real.sqrt (sigmaSq n N s0 i) * Real.sqrt n)
    (scoreScale : Real) {slack boundSq : Nat → Real}
    (hslack : ∀ i, 0 < slack i) (hbound : ∀ i, 0 < boundSq i)
    (tail : Nat → Measure (ScoreSeed n)) [∀ i, IsProbabilityMeasure (tail i)]
    (mu0 : Measure (ScoreSeed n)) [IsProbabilityMeasure mu0]
    (V : Nat → (Nat → ScoreSeed n) → Real)
    (initialWarm : ENNReal) (hinitialOne : 1 ≤ initialWarm)
    (hinitialTop : initialWarm ≠ ⊤)
    (hstart : IsWarm initialWarm (Measure.map Prod.snd mu0)
      (hybridRadiusQSeedTarget n
        (globalLogarithmicRadiusQ n (dependenceRadiusCalls m k eps)) N s0 K 0))
    (htailSeed : ∀ i, Measure.map Prod.snd (tail i) =
      hybridRadiusQSeedTarget n
        (globalLogarithmicRadiusQ n (dependenceRadiusCalls m k eps)) N s0 K i)
    (u : (i : Nat) → (Finset.Iic i → ScoreSeed n) → Real)
    (v : Nat → State n → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i,
      accuracyU
          (inhomogeneousPathMeasure
            (stateScheduleFromSeed
              (activeReferenceTailSchedule m
                (sourceHybridRadiusQWarmFallbackSchedule (by omega : 1 ≤ n)
                  (globalLogarithmicRadiusQ n (dependenceRadiusCalls m k eps))
                  (by
                    have hq4 := four_le_globalLogarithmicRadiusQ (by omega : 1 ≤ n)
                      (one_le_dependenceRadiusCalls m k eps)
                    linarith)
                  hN hs0 K hK
                  (hybridRadiusQCanonicalSteps initialWarm n
                    (globalLogarithmicRadiusQ n (dependenceRadiusCalls m k eps))
                    N s0 K (scoreAwareRetries m k eps slack boundSq)
                    (scoreAwareEta m k eps slack boundSq)
                    (scoreAwareZeta m k eps slack boundSq))
                  (scoreAwareRetries m k eps slack boundSq) scoreScale) tail)) mu0)
          V (correctedAlpha m eps) i =
        fun omega ↦ u i (Preorder.frestrictLe i omega))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (omega (i + 1)).1) :
    SeedProjectedOperational
      (stateScheduleFromSeed
        (activeReferenceTailSchedule m
          (sourceHybridRadiusQWarmFallbackSchedule (by omega : 1 ≤ n)
            (globalLogarithmicRadiusQ n (dependenceRadiusCalls m k eps))
            (by
              have hq4 := four_le_globalLogarithmicRadiusQ (by omega : 1 ≤ n)
                (one_le_dependenceRadiusCalls m k eps)
              linarith)
            hN hs0 K hK
            (hybridRadiusQCanonicalSteps initialWarm n
              (globalLogarithmicRadiusQ n (dependenceRadiusCalls m k eps))
              N s0 K (scoreAwareRetries m k eps slack boundSq)
              (scoreAwareEta m k eps slack boundSq)
              (scoreAwareZeta m k eps slack boundSq))
            (scoreAwareRetries m k eps slack boundSq) scoreScale) tail))
      (activeReferenceTailSchedule m
        (sourceHybridRadiusQWarmFallbackSchedule (by omega : 1 ≤ n)
          (globalLogarithmicRadiusQ n (dependenceRadiusCalls m k eps))
          (by
            have hq4 := four_le_globalLogarithmicRadiusQ (by omega : 1 ≤ n)
              (one_le_dependenceRadiusCalls m k eps)
            linarith)
          hN hs0 K hK
          (hybridRadiusQCanonicalSteps initialWarm n
            (globalLogarithmicRadiusQ n (dependenceRadiusCalls m k eps))
            N s0 K (scoreAwareRetries m k eps slack boundSq)
            (scoreAwareEta m k eps slack boundSq)
            (scoreAwareZeta m k eps slack boundSq))
          (scoreAwareRetries m k eps slack boundSq) scoreScale) tail)
      Prod.snd Prod.fst mu0 V m eps := by
  let A := dependenceRadiusCalls m k eps
  let q := globalLogarithmicRadiusQ n A
  have hn1 : 1 ≤ n := by omega
  have hA : 1 ≤ A := one_le_dependenceRadiusCalls m k eps
  have hq4 : 4 ≤ q := four_le_globalLogarithmicRadiusQ hn1 hA
  have hq : 1 < q := lt_of_lt_of_le (by norm_num) hq4
  apply seedProjectedOperational_hybridRadiusQ_canonical hn m hq hN hs0 hK hKc
    hball hfin (fun i _ ↦ hybridPhaseRate_nonneg hn1 hN hs0 i)
    (fun i hi ↦ one_le_globalLogarithmicRadius_mul_sqrt_of_four hn1 hA (hfour i hi))
    (scoreAwareRetries m k eps slack boundSq) scoreScale
    (scoreAwareEta m k eps slack boundSq) (scoreAwareZeta m k eps slack boundSq)
  · intro i
    exact ENNReal.ofReal_ne_zero_iff.mpr (scoreAwareShare_pos heps hslack hbound i)
  · intro i; exact ENNReal.ofReal_ne_top
  · intro i
    rw [scoreAwareEta, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (scoreAwareShare_lt_one heps heps1 i).le
  · intro i
    exact ENNReal.ofReal_ne_zero_iff.mpr
      (div_pos (scoreAwareShare_pos heps hslack hbound i) (by norm_num))
  · intro i; exact ENNReal.ofReal_ne_top
  · exact scoreAwareZeta_le_sixteenth heps heps1
  · exact hinitialOne
  · exact hinitialTop
  · simpa only [q, A] using hstart
  · simpa only [q, A] using htailSeed
  · exact hu
  · exact hv
  · simpa only [q, A] using hU
  · exact hV
  · intro i hi
    have hb := hybridRadiusQCanonicalMixError_scoreAware_budget
      (n := n) (m := m) (k := k) hn1 heps heps1 hslack hbound i
    have herr0 : 0 ≤ 2 *
        (hybridRadiusQCanonicalMixError n q
          (scoreAwareEta m k eps slack boundSq)
          (scoreAwareZeta m k eps slack boundSq)
          (scoreAwareRetries m k eps slack boundSq) i).toReal := by positivity
    calc
      2 * (hybridRadiusQCanonicalMixError n q
          (scoreAwareEta m k eps slack boundSq)
          (scoreAwareZeta m k eps slack boundSq)
          (scoreAwareRetries m k eps slack boundSq) i).toReal =
          1 * (2 * (hybridRadiusQCanonicalMixError n q
            (scoreAwareEta m k eps slack boundSq)
            (scoreAwareZeta m k eps slack boundSq)
            (scoreAwareRetries m k eps slack boundSq) i).toReal) := by ring
      _ ≤ (k : Real) * (2 * (hybridRadiusQCanonicalMixError n q
            (scoreAwareEta m k eps slack boundSq)
            (scoreAwareZeta m k eps slack boundSq)
            (scoreAwareRetries m k eps slack boundSq) i).toReal) := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) herr0
      _ ≤ correctedNu m eps := by simpa only [q, A] using hb

#print axioms seedProjectedOperational_hybridGlobalRadius_scoreAware

/-- Independent-stream lift with the selected-radius tail already paid from the exact
`k`-stream dependence allowance.  Only the usual statistic locality identities remain. -/
noncomputable def independentStreamOperational_hybridGlobalRadius_scoreAware
    (hn : 1 ≤ n) {k m : Nat} (hk : 1 ≤ k)
    {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {slack boundSq : Nat → Real} (hslack : ∀ i, 0 < slack i)
    (hbound : ∀ i, 0 < boundSq i)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (ScoreSeed n)} [IsProbabilityMeasure mu0]
    {Vscalar : Nat → (Nat → ScoreSeed n) → Real}
    (hop : SeedProjectedOperational (stateScheduleFromSeed Q) Q Prod.snd Prod.fst
      mu0 Vscalar m eps)
    (hmixError : ∀ i, hop.mixError i = activeReferenceMixError m
      (hybridRadiusQCanonicalMixError n
        (globalLogarithmicRadiusQ n (dependenceRadiusCalls m k eps))
        (scoreAwareEta m k eps slack boundSq)
        (scoreAwareZeta m k eps slack boundSq)
        (scoreAwareRetries m k eps slack boundSq)) i)
    (V : Nat → (Fin k → Nat → ScoreSeed n) → Real)
    (u : (i : Nat) → (Fin k → Finset.Iic i → ScoreSeed n) → Real)
    (v : Nat → (Fin k → ScoreSeed n) → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i, accuracyU
      (independentPathLaw k (stateScheduleFromSeed Q) mu0) V
        (correctedAlpha m eps) i =
      fun omega ↦ u i (fun l ↦ Preorder.frestrictLe i (omega l)))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (fun l ↦ omega l (i + 1))) :
    IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V m eps := by
  apply independentStreamOperational_of_seedProjected hop V u v hu hv hU hV
  intro i
  rw [hmixError i]
  unfold activeReferenceMixError
  by_cases hi : i + 1 < m
  · simp only [if_pos hi]
    exact hybridRadiusQCanonicalMixError_scoreAware_budget
      (n := n) (m := m) (k := k) hn heps heps1 hslack hbound i
  · simp only [if_neg hi, ENNReal.toReal_zero, mul_zero]
    exact (correctedNu_pos (m := m) heps).le

#print axioms independentStreamOperational_hybridGlobalRadius_scoreAware

end Ttc.CVHybridGlobalRadiusCanonicalOperational
