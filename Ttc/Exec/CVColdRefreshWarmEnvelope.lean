import Ttc.Exec.CVColdOperationalSeedReset
import Ttc.Volume.CVHybridSchedule

/-!
# Explicit warm envelope for the operational cold seed refresh

The actual cold reset uses radius `min (1/4) (2 sqrt(n) sqrt(s))`.  Before the cap
activates, the rejection ball contains at least half the ambient Gaussian mass and its
normalizer ratio is at most two.  After the cap activates, the fixed-ball radial bound
applies; the cap threshold itself controls the inverse-variance term.
-/

set_option autoImplicit false

namespace Ttc.CVColdRefreshWarmEnvelope

open MeasureTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVIndependentRefreshSeedLaws
open Ttc.CVColdOperationalSeedReset
open Ttc.CVSourceTruncatedFixedCost
open Ttc.CVCorrectedFixedBlockCost
open Ttc.CVHybridSchedule
open scoped ENNReal

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- Pointwise envelope for the actual capped cold refresh. -/
noncomputable def coldRefreshWarmEnvelope (n : Nat) (s : Real) : ENNReal :=
  max (ENNReal.ofReal 2)
    (hotRefreshWarmEnvelope n (4 * Real.sqrt s * Real.sqrt n) s)

/-- Branch-sensitive envelope used for deadline arithmetic.  Unlike the convenient
`max` bound above, it does not retain the irrelevant fixed-radius term before the cap
activates. -/
noncomputable def coldRefreshOperationalWarmEnvelope
    (n : Nat) (s : Real) : ENNReal :=
  if coldRefreshRadius n s ≤ hotRefreshRadius then ENNReal.ofReal 2
  else hotRefreshWarmEnvelope n (4 * Real.sqrt s * Real.sqrt n) s

/-- A phase-scaled Gaussian rejection ball has normalizer ratio at most two against any
measurable numerator set. -/
theorem gaussianBallWarmFactor_coldRefresh_le_two
    (hn : 1 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    {s : Real} (hs : 0 < s) :
    gaussianBallWarmFactor K s (coldRefreshRadius n s) ≤ ENNReal.ofReal 2 := by
  let nu : Measure (State n) := gaussianBase n s
  let B : Set (State n) := closedBall (0 : State n) (coldRefreshRadius n s)
  have hrho : 0 < coldRefreshRadius n s := coldRefreshRadius_pos hn hs
  have hBvol0 : volume B ≠ 0 :=
    (measure_closedBall_pos volume (0 : State n) hrho).ne'
  have hB0 : nu B ≠ 0 := by
    dsimp only [nu, B, gaussianBase]
    exact withDensity_gaussianWeight_ne_zero s hBvol0
  have hBtop : nu B ≠ ⊤ := by
    dsimp only [nu, B, gaussianBase]
    exact withDensity_gaussianWeight_ne_top hs measurableSet_closedBall
      measure_closedBall_lt_top.ne
  have hhalf : ENNReal.ofReal (1 / 2) * nu Set.univ ≤ nu B := by
    simpa only [nu, B, gaussianBase] using
      (half_ambientGaussian_le_coldBall (n := n) hn hs hrho
        (by rw [coldRefreshRadius_sq hn hs]))
  have hamb : nu Set.univ ≤ ENNReal.ofReal 2 * nu B := by
    calc
      nu Set.univ = ENNReal.ofReal 2 *
          (ENNReal.ofReal (1 / 2) * nu Set.univ) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 2)]
        norm_num
      _ ≤ ENNReal.ofReal 2 * nu B := mul_le_mul_left' hhalf _
  rw [gaussianBallWarmFactor, show gaussianBase n s K = nu K by rfl,
    show gaussianBase n s (closedBall (0 : State n) (coldRefreshRadius n s)) =
      nu B by rfl,
    ENNReal.div_le_iff hB0 hBtop]
  exact (measure_mono (subset_univ K)).trans hamb

/-- The exact normalizer ratio used by the operational min-radius refresh is bounded by
the two-branch explicit envelope. -/
theorem gaussianBallWarmFactor_coldNextRefreshRadius_le
    (hn : 1 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    {s : Real} (hs : 0 < s)
    (hKR : K ⊆ closedBall (0 : State n)
      (4 * Real.sqrt s * Real.sqrt n)) :
    gaussianBallWarmFactor K s (coldNextRefreshRadius n s) ≤
      coldRefreshWarmEnvelope n s := by
  by_cases hcap : coldRefreshRadius n s ≤ hotRefreshRadius
  · rw [coldNextRefreshRadius, min_eq_right hcap]
    exact (gaussianBallWarmFactor_coldRefresh_le_two hn hK hs).trans
      (le_max_left _ _)
  · have hhot : hotRefreshRadius ≤ coldRefreshRadius n s := le_of_not_ge hcap
    rw [coldNextRefreshRadius, min_eq_left hhot]
    exact (hotRefreshWarmFactor_le_envelope hK hs hKR).trans
      (le_max_right _ _)

/-- Branch-sensitive version of the preceding bound, suitable for logarithms. -/
theorem gaussianBallWarmFactor_coldNextRefreshRadius_le_operational
    (hn : 1 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    {s : Real} (hs : 0 < s)
    (hKR : K ⊆ closedBall (0 : State n)
      (4 * Real.sqrt s * Real.sqrt n)) :
    gaussianBallWarmFactor K s (coldNextRefreshRadius n s) ≤
      coldRefreshOperationalWarmEnvelope n s := by
  by_cases hcap : coldRefreshRadius n s ≤ hotRefreshRadius
  · rw [coldNextRefreshRadius, min_eq_right hcap,
      coldRefreshOperationalWarmEnvelope, if_pos hcap]
    exact gaussianBallWarmFactor_coldRefresh_le_two hn hK hs
  · have hhot : hotRefreshRadius ≤ coldRefreshRadius n s := le_of_not_ge hcap
    rw [coldNextRefreshRadius, min_eq_left hhot,
      coldRefreshOperationalWarmEnvelope, if_neg hcap]
    exact hotRefreshWarmFactor_le_envelope hK hs hKR

/-- Specialization to the radius-four operational body. -/
theorem coldNextRefreshWarmFactor_le_envelope
    (hn : 1 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    {s0 : Real} (hs0 : 0 < s0) (i : Nat) :
    coldNextRefreshWarmFactor n K s0 i ≤
      coldRefreshWarmEnvelope n (fixedSigmaSq n s0 (i + 1)) := by
  let s := fixedSigmaSq n s0 (i + 1)
  have hs : 0 < s := by
    dsimp only [s]
    unfold Ttc.CVCorrectedFixedBlockCost.fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) (i + 1)
  unfold coldNextRefreshWarmFactor
  apply gaussianBallWarmFactor_coldNextRefreshRadius_le hn
    (measurableSet_fixedRadiusFourBody hK s) hs
  exact inter_subset_right

theorem coldNextRefreshWarmFactor_le_operationalEnvelope
    (hn : 1 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    {s0 : Real} (hs0 : 0 < s0) (i : Nat) :
    coldNextRefreshWarmFactor n K s0 i ≤
      coldRefreshOperationalWarmEnvelope n (fixedSigmaSq n s0 (i + 1)) := by
  let s := fixedSigmaSq n s0 (i + 1)
  have hs : 0 < s := by
    dsimp only [s]
    unfold Ttc.CVCorrectedFixedBlockCost.fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) (i + 1)
  unfold coldNextRefreshWarmFactor
  apply gaussianBallWarmFactor_coldNextRefreshRadius_le_operational hn
    (measurableSet_fixedRadiusFourBody hK s) hs
  exact inter_subset_right

theorem coldRefreshWarmEnvelope_ne_top
    (n : Nat) (s : Real) : coldRefreshWarmEnvelope n s ≠ ⊤ := by
  unfold coldRefreshWarmEnvelope hotRefreshWarmEnvelope
  exact max_ne_top ENNReal.ofReal_ne_top (by finiteness)

theorem coldRefreshOperationalWarmEnvelope_ne_top
    (n : Nat) (s : Real) : coldRefreshOperationalWarmEnvelope n s ≠ ⊤ := by
  unfold coldRefreshOperationalWarmEnvelope
  split_ifs
  · exact ENNReal.ofReal_ne_top
  · unfold hotRefreshWarmEnvelope
    finiteness

/-- Once the fixed cap is active, its inverse-variance exponent is at most `2n`. -/
theorem hotRefresh_inverseVariance_le_two_mul_n_of_cap
    (hn : 1 ≤ n) {s : Real} (hs : 0 < s)
    (hcap : hotRefreshRadius ≤ coldRefreshRadius n s) :
    hotRefreshRadius ^ 2 / (2 * s) ≤ 2 * (n : Real) := by
  have hsq : hotRefreshRadius ^ 2 ≤ coldRefreshRadius n s ^ 2 :=
    (sq_le_sq₀ hotRefreshRadius_pos.le (coldRefreshRadius_pos hn hs).le).2 hcap
  rw [coldRefreshRadius_sq hn hs] at hsq
  rw [div_le_iff₀ (by positivity : 0 < 2 * s)]
  nlinarith

/-- In a cold phase with `s ≤ n`, even the capped branch has an `O(n log n)` refresh
logarithm. -/
theorem log_hotRefreshWarmEnvelope_coldRadius_le
    (hn : 1 ≤ n) {s : Real} (hs : 0 < s) (hsn : s ≤ n)
    (hcap : hotRefreshRadius ≤ coldRefreshRadius n s) :
    Real.log
        (hotRefreshWarmEnvelope n (4 * Real.sqrt s * Real.sqrt n) s).toReal ≤
      2 * (n : Real) + (n : Real) * Real.log (16 * (n : Real)) := by
  have hn0 : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hsqrt : Real.sqrt s ≤ Real.sqrt (n : Real) := Real.sqrt_le_sqrt hsn
  have hsqrtn : Real.sqrt (n : Real) ^ 2 = (n : Real) :=
    Real.sq_sqrt hn0.le
  have hprod : Real.sqrt s * Real.sqrt n ≤ (n : Real) := by
    calc
      Real.sqrt s * Real.sqrt n ≤ Real.sqrt n * Real.sqrt n := by
        exact mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _)
      _ = (n : Real) := by rw [← pow_two, hsqrtn]
  have hR : 4 * Real.sqrt s * Real.sqrt n ≤ 4 * (n : Real) := by nlinarith
  have hone : (1 : Real) ≤ 4 * n := by
    have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
    nlinarith
  have hmax : max 1 (4 * Real.sqrt s * Real.sqrt n) ≤ 4 * (n : Real) :=
    max_le hone hR
  have harg0 : 0 < 4 * max 1 (4 * Real.sqrt s * Real.sqrt n) := by
    have : (0 : Real) < max 1 (4 * Real.sqrt s * Real.sqrt n) :=
      one_pos.trans_le (le_max_left _ _)
    positivity
  have hlog : Real.log (4 * max 1 (4 * Real.sqrt s * Real.sqrt n)) ≤
      Real.log (16 * (n : Real)) := by
    apply Real.log_le_log harg0
    nlinarith
  rw [log_hotRefreshWarmEnvelope_toReal n hs]
  have hinv := hotRefresh_inverseVariance_le_two_mul_n_of_cap hn hs hcap
  have hnnonneg : (0 : Real) ≤ n := by positivity
  linarith [mul_le_mul_of_nonneg_left hlog hnnonneg]

/-- Unified logarithmic bound for the branch-sensitive operational cold envelope. -/
theorem log_coldRefreshOperationalWarmEnvelope_le
    (hn : 1 ≤ n) {s : Real} (hs : 0 < s) (hsn : s ≤ n) :
    Real.log (coldRefreshOperationalWarmEnvelope n s).toReal ≤
      2 * (n : Real) + (n : Real) * Real.log (16 * (n : Real)) := by
  by_cases hcap : coldRefreshRadius n s ≤ hotRefreshRadius
  · rw [coldRefreshOperationalWarmEnvelope, if_pos hcap,
      ENNReal.toReal_ofReal (by norm_num : (0 : Real) ≤ 2)]
    have hlog2n : Real.log 2 ≤ Real.log (16 * (n : Real)) := by
      apply Real.log_le_log (by norm_num)
      have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
      nlinarith
    have hlog16n0 : 0 ≤ Real.log (16 * (n : Real)) := by
      exact Real.log_nonneg (by
        have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
        nlinarith)
    have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
    calc
      Real.log 2 ≤ Real.log (16 * (n : Real)) := hlog2n
      _ ≤ (n : Real) * Real.log (16 * (n : Real)) :=
        le_mul_of_one_le_left hlog16n0 hn1
      _ ≤ 2 * (n : Real) + (n : Real) * Real.log (16 * (n : Real)) := by
        linarith
  · rw [coldRefreshOperationalWarmEnvelope, if_neg hcap]
    exact log_hotRefreshWarmEnvelope_coldRadius_le hn hs hsn (le_of_not_ge hcap)

/-- Every next variance used by a genuine cold transition remains at most `n`. -/
theorem fixedSigmaSq_succ_le_n_of_lt_coldPhases
    (hn : 2 ≤ n) {s0 : Real} (hs0 : 0 < s0) (hs01 : s0 ≤ 1)
    {i : Nat} (hi : i < coldPhases n s0) :
    fixedSigmaSq n s0 (i + 1) ≤ (n : Real) := by
  have hn1 : 1 ≤ n := by omega
  have hindex : i + 1 ≤ coldPhases n s0 := by omega
  have hsched : fixedSigmaSq n s0 (i + 1) ≤ coldEnd n s0 := by
    unfold fixedSigmaSq coldEnd
    exact (geomSchedule_strictMono hs0 (by positivity : 0 < 1 / (n : Real))).monotone
      hindex
  have hend := coldEnd_lt_one_add_inv hn1 hs0 hs01
  have hnR : (2 : Real) ≤ n := by exact_mod_cast hn
  have hinv : 1 / (n : Real) ≤ 1 := by
    rw [div_le_one (by positivity : (0 : Real) < n)]
    linarith
  linarith

/-- Schedule-level logarithmic envelope for the actual cold reset choice. -/
theorem log_coldRefreshOperationalWarmEnvelope_fixedSigmaSq_succ_le
    (hn : 2 ≤ n) {s0 : Real} (hs0 : 0 < s0) (hs01 : s0 ≤ 1)
    {i : Nat} (hi : i < coldPhases n s0) :
    Real.log
        (coldRefreshOperationalWarmEnvelope n
          (fixedSigmaSq n s0 (i + 1))).toReal ≤
      2 * (n : Real) + (n : Real) * Real.log (16 * (n : Real)) := by
  apply log_coldRefreshOperationalWarmEnvelope_le (by omega : 1 ≤ n)
  · unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) (i + 1)
  · exact fixedSigmaSq_succ_le_n_of_lt_coldPhases hn hs0 hs01 hi

#print axioms gaussianBallWarmFactor_coldRefresh_le_two
#print axioms gaussianBallWarmFactor_coldNextRefreshRadius_le
#print axioms gaussianBallWarmFactor_coldNextRefreshRadius_le_operational
#print axioms coldNextRefreshWarmFactor_le_envelope
#print axioms coldNextRefreshWarmFactor_le_operationalEnvelope
#print axioms hotRefresh_inverseVariance_le_two_mul_n_of_cap
#print axioms log_hotRefreshWarmEnvelope_coldRadius_le
#print axioms log_coldRefreshOperationalWarmEnvelope_le
#print axioms fixedSigmaSq_succ_le_n_of_lt_coldPhases
#print axioms log_coldRefreshOperationalWarmEnvelope_fixedSigmaSq_succ_le

end Ttc.CVColdRefreshWarmEnvelope
