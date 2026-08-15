import Ttc.Exec.CVHybridRadiusQSwitchedCanonicalOperational
import Ttc.Exec.CVGlobalRadiusSourceSchedule

/-! Canonical selected-radius operation at the exact source hybrid phase count. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Ttc.CVHybridSourceSwitchedGlobalRadiusOperational

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVCorrected Ttc.CVHybridSchedule Ttc.CVSequentialPhaseSampler
open Ttc.CVSeedProjectedDependence Ttc.CVScoreSeedPhaseKernel
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVGaussianScoreAwareParameters Ttc.CVContinuingRetryParameters
open Ttc.CVIndependentStreamDependence
open Ttc.CVHybridRadiusQRecursiveStep
open Ttc.CVHybridRadiusQSwitchedCanonicalOperational
open Ttc.CVGlobalRadiusSourceSchedule Ttc.CVGlobalRadiusTerminalBody
open Ttc.CVHotRefreshRadialRuntime
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

noncomputable def sourceOperationalN (n : Nat) (C : Real) : Real := C ^ 2 * n

noncomputable def sourceOperationalPhases (n : Nat) (C : Real) : Nat :=
  sourceHybridPhaseCount n (sourceOperationalN n C)

noncomputable def sourceOperationalRadiusQ
    (n k : Nat) (C eps : Real) : Real :=
  sourceGlobalLogarithmicRadiusQ n k (sourceOperationalN n C) eps

theorem sourceOperationalRadiusQ_gt_one
    {n : Nat} (hn : 1 ≤ n) (k : Nat) (C eps : Real) :
    1 < sourceOperationalRadiusQ n k C eps := by
  exact lt_of_lt_of_le (by norm_num)
    (four_le_sourceGlobalLogarithmicRadiusQ hn k (sourceOperationalN n C) eps)

theorem sourceStart_le_sigmaSq
    {n : Nat} (hn : 1 ≤ n) {N : Real} (hN : 0 < N) (i : Nat) :
    (1 / (16 * (n : Real)) : Real) ≤
      sigmaSq n N (1 / (16 * (n : Real))) i := by
  let s0 : Real := 1 / (16 * (n : Real))
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  have hs0 : 0 < s0 := by dsimp only [s0]; positivity
  have hs01 : s0 ≤ 1 := by
    dsimp only [s0]
    rw [div_le_one (by positivity : (0 : Real) < 16 * (n : Real))]
    nlinarith
  by_cases hi : i < coldPhases n s0
  · rw [sigmaSq, if_pos hi]
    unfold Arlib.GaussianCooling.geomSchedule
    have hbase : (1 : Real) ≤ 1 + 1 / (n : Real) :=
      le_add_of_nonneg_right (by positivity)
    have hp : (1 : Real) ≤ (1 + 1 / (n : Real)) ^ i := one_le_pow₀ hbase
    dsimp only [s0] at hs0 ⊢
    nlinarith [mul_nonneg hs0.le (sub_nonneg.mpr hp)]
  · exact hs01.trans
      (one_le_sigmaSq_of_not_lt_coldPhases hn hN hs0 hs01 hi)

theorem sourceRadiusFourInterior
    {n : Nat} (hn : 1 ≤ n) {N : Real} (hN : 0 < N) (i : Nat) :
    1 ≤ 4 * Real.sqrt
      (sigmaSq n N (1 / (16 * (n : Real))) i) * Real.sqrt n := by
  let s := sigmaSq n N (1 / (16 * (n : Real))) i
  have hn0 : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hs0 : 0 < s := sigmaSq_pos hn hN (by positivity) i
  have hlower := sourceStart_le_sigmaSq hn hN i
  have hscaled : 1 ≤ 16 * s * (n : Real) := by
    have h := mul_le_mul_of_nonneg_right hlower (show 0 ≤ 16 * (n : Real) by positivity)
    dsimp only [s] at h ⊢
    calc
      1 = (1 / (16 * (n : Real))) * (16 * (n : Real)) := by field_simp
      _ ≤ sigmaSq n N (1 / (16 * (n : Real))) i * (16 * (n : Real)) := h
      _ = 16 * sigmaSq n N (1 / (16 * (n : Real))) i * (n : Real) := by ring
  have hsqrtS : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs0.le
  have hsqrtN : Real.sqrt (n : Real) ^ 2 = n := Real.sq_sqrt hn0.le
  have hx0 : 0 ≤ 4 * Real.sqrt s * Real.sqrt n := by positivity
  dsimp only [s] at hsqrtS ⊢
  nlinarith [sq_nonneg (4 * Real.sqrt
    (sigmaSq n N (1 / (16 * (n : Real))) i) * Real.sqrt n - 1)]

/-- Source-specialized operational certificate: `m`, `N`, global `q`, all mixing
shares/retries, the stream×phase tail allocation, and the phase-rate proof are fixed
internally.  There is no arbitrary phase count or scalar mixing premise. -/
noncomputable def seedProjectedOperational_hybridSourceSwitchedGlobalRadius_scoreAware
    (hn : 21 ≤ n) (k : Nat) (hk : 1 ≤ k) {C eps : Real}
    (hC : 1 ≤ C) (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (scoreScale : Real) {slack boundSq : Nat → Real}
    (hslack : ∀ i, 0 < slack i) (hbound : ∀ i, 0 < boundSq i)
    (tail : Nat → Measure (ScoreSeed n)) [∀ i, IsProbabilityMeasure (tail i)]
    (mu0 : Measure (ScoreSeed n)) [IsProbabilityMeasure mu0]
    (V : Nat → (Nat → ScoreSeed n) → Real)
    (initialWarm : ENNReal) (hinitialOne : 1 ≤ initialWarm)
    (hinitialTop : initialWarm ≠ ⊤)
    (hstart : IsWarm initialWarm (Measure.map Prod.snd mu0)
      (hybridRadiusQSeedTarget n (sourceOperationalRadiusQ n k C eps)
        (sourceOperationalN n C) (1 / (16 * (n : Real))) K 0))
    (htailSeed : ∀ i, Measure.map Prod.snd (tail i) =
      hybridRadiusQSeedTarget n (sourceOperationalRadiusQ n k C eps)
        (sourceOperationalN n C) (1 / (16 * (n : Real))) K i)
    (u : (i : Nat) → (Finset.Iic i → ScoreSeed n) → Real)
    (v : Nat → State n → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i,
      accuracyU
          (inhomogeneousPathMeasure
            (stateScheduleFromSeed
              (activeReferenceTailSchedule (sourceOperationalPhases n C)
                (sourceHybridRadiusQWarmFallbackSchedule (by omega : 1 ≤ n)
                  (sourceOperationalRadiusQ n k C eps)
                  (zero_lt_one.trans
                    (sourceOperationalRadiusQ_gt_one (by omega : 1 ≤ n) k C eps))
                  (show 0 < sourceOperationalN n C by
                    unfold sourceOperationalN; positivity)
                  (by positivity : 0 < (1 / (16 * (n : Real)) : Real)) K hK
                  (hybridRadiusQSwitchedCanonicalSteps initialWarm n
                    (sourceOperationalRadiusQ n k C eps) (sourceOperationalN n C)
                    (1 / (16 * (n : Real))) K
                    (scoreAwareRetries (sourceOperationalPhases n C) k eps slack boundSq)
                    (scoreAwareEta (sourceOperationalPhases n C) k eps slack boundSq)
                    (scoreAwareZeta (sourceOperationalPhases n C) k eps slack boundSq))
                  (scoreAwareRetries (sourceOperationalPhases n C) k eps slack boundSq)
                  scoreScale) tail)) mu0)
          V (correctedAlpha (sourceOperationalPhases n C) eps) i =
        fun omega ↦ u i (Preorder.frestrictLe i omega))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (omega (i + 1)).1) :
    SeedProjectedOperational
      (stateScheduleFromSeed
        (activeReferenceTailSchedule (sourceOperationalPhases n C)
          (sourceHybridRadiusQWarmFallbackSchedule (by omega : 1 ≤ n)
            (sourceOperationalRadiusQ n k C eps)
            (zero_lt_one.trans
              (sourceOperationalRadiusQ_gt_one (by omega : 1 ≤ n) k C eps))
            (show 0 < sourceOperationalN n C by
              unfold sourceOperationalN; positivity)
            (by positivity : 0 < (1 / (16 * (n : Real)) : Real)) K hK
            (hybridRadiusQSwitchedCanonicalSteps initialWarm n
              (sourceOperationalRadiusQ n k C eps) (sourceOperationalN n C)
              (1 / (16 * (n : Real))) K
              (scoreAwareRetries (sourceOperationalPhases n C) k eps slack boundSq)
              (scoreAwareEta (sourceOperationalPhases n C) k eps slack boundSq)
              (scoreAwareZeta (sourceOperationalPhases n C) k eps slack boundSq))
            (scoreAwareRetries (sourceOperationalPhases n C) k eps slack boundSq)
            scoreScale) tail))
      (activeReferenceTailSchedule (sourceOperationalPhases n C)
        (sourceHybridRadiusQWarmFallbackSchedule (by omega : 1 ≤ n)
          (sourceOperationalRadiusQ n k C eps)
          (zero_lt_one.trans
            (sourceOperationalRadiusQ_gt_one (by omega : 1 ≤ n) k C eps))
          (show 0 < sourceOperationalN n C by
            unfold sourceOperationalN; positivity)
          (by positivity : 0 < (1 / (16 * (n : Real)) : Real)) K hK
          (hybridRadiusQSwitchedCanonicalSteps initialWarm n
            (sourceOperationalRadiusQ n k C eps) (sourceOperationalN n C)
            (1 / (16 * (n : Real))) K
            (scoreAwareRetries (sourceOperationalPhases n C) k eps slack boundSq)
            (scoreAwareEta (sourceOperationalPhases n C) k eps slack boundSq)
            (scoreAwareZeta (sourceOperationalPhases n C) k eps slack boundSq))
          (scoreAwareRetries (sourceOperationalPhases n C) k eps slack boundSq)
          scoreScale) tail)
      Prod.snd Prod.fst mu0 V (sourceOperationalPhases n C) eps := by
  let m := sourceOperationalPhases n C
  let N := sourceOperationalN n C
  let s0 : Real := 1 / (16 * (n : Real))
  let q := sourceOperationalRadiusQ n k C eps
  have hn1 : 1 ≤ n := by omega
  have hN : 0 < N := by dsimp only [N, sourceOperationalN]; positivity
  have hs0 : 0 < s0 := by dsimp only [s0]; positivity
  have hq : 1 < q := by
    simpa only [q] using sourceOperationalRadiusQ_gt_one hn1 k C eps
  apply seedProjectedOperational_hybridRadiusQ_switched_canonical hn m hq hN hs0 hK hKc
    hball hfin (fun i _ ↦ hybridPhaseRate_nonneg hn1 hN hs0 i)
    (fun i hi ↦ one_le_globalLogarithmicRadius_mul_sqrt_of_four hn1
      (one_le_sourceDependenceRadiusCalls n k N eps)
      (by simpa only [s0] using sourceRadiusFourInterior hn1 hN i))
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
  · simpa only [m, N, s0, q] using hstart
  · simpa only [m, N, s0, q] using htailSeed
  · exact hu
  · exact hv
  · simpa only [m, N, s0, q] using hU
  · exact hV
  · intro i hi
    have hb := sourceGlobalLogarithmicRadius_mixError_budget
      (n := n) (k := k) hn1 (N := N) heps heps1 hslack hbound i
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
      _ ≤ correctedNu m eps := by
        simpa only [m, N, q, sourceOperationalPhases, sourceOperationalRadiusQ,
          Ttc.CVHybridRadiusQSwitchedCanonicalOperational.hybridRadiusQCanonicalMixError,
          Ttc.CVHybridRadiusQCanonicalOperational.hybridRadiusQCanonicalMixError] using hb

#print axioms seedProjectedOperational_hybridSourceSwitchedGlobalRadius_scoreAware

/-- Independent-stream lift at the literal source phase count and selected global
radius.  In particular, there is no free phase-count or truncation-radius parameter in
this interface: the stream-by-phase tail allocation is the one from
`sourceDependenceRadiusCalls`. -/
noncomputable def independentStreamOperational_hybridSourceSwitchedGlobalRadius_scoreAware
    (hn : 1 ≤ n) {k : Nat} (hk : 1 ≤ k) {C eps : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    {slack boundSq : Nat → Real} (hslack : ∀ i, 0 < slack i)
    (hbound : ∀ i, 0 < boundSq i)
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (ScoreSeed n)} [IsProbabilityMeasure mu0]
    {Vscalar : Nat → (Nat → ScoreSeed n) → Real}
    (hop : SeedProjectedOperational (stateScheduleFromSeed Q) Q Prod.snd Prod.fst
      mu0 Vscalar (sourceOperationalPhases n C) eps)
    (hmixError : ∀ i, hop.mixError i =
      activeReferenceMixError (sourceOperationalPhases n C)
        (hybridRadiusQCanonicalMixError n (sourceOperationalRadiusQ n k C eps)
          (scoreAwareEta (sourceOperationalPhases n C) k eps slack boundSq)
          (scoreAwareZeta (sourceOperationalPhases n C) k eps slack boundSq)
          (scoreAwareRetries (sourceOperationalPhases n C) k eps slack boundSq)) i)
    (V : Nat → (Fin k → Nat → ScoreSeed n) → Real)
    (u : (i : Nat) → (Fin k → Finset.Iic i → ScoreSeed n) → Real)
    (v : Nat → (Fin k → ScoreSeed n) → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i, accuracyU
      (independentPathLaw k (stateScheduleFromSeed Q) mu0) V
        (correctedAlpha (sourceOperationalPhases n C) eps) i =
      fun omega ↦ u i (fun l ↦ Preorder.frestrictLe i (omega l)))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (fun l ↦ omega l (i + 1))) :
    IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V (sourceOperationalPhases n C) eps := by
  apply independentStreamOperational_of_seedProjected hop V u v hu hv hU hV
  intro i
  rw [hmixError i]
  unfold activeReferenceMixError
  by_cases hi : i + 1 < sourceOperationalPhases n C
  · simp only [if_pos hi]
    exact sourceGlobalLogarithmicRadius_mixError_budget
      (n := n) (k := k) hn (N := sourceOperationalN n C)
      heps heps1 hslack hbound i
  · simp only [if_neg hi, ENNReal.toReal_zero, mul_zero]
    exact (correctedNu_pos (m := sourceOperationalPhases n C) heps).le

#print axioms independentStreamOperational_hybridSourceSwitchedGlobalRadius_scoreAware

end Ttc.CVHybridSourceSwitchedGlobalRadiusOperational
