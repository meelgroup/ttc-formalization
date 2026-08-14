import Ttc.Exec.CVColdCrossPhaseWarm
import Ttc.Exec.FiniteContinuingRetryRandomFallback

/-!
# Warm independently resampled seeds for the fixed cold schedule

An operational phase may retain its computed score and query cost while independently
resampling the raw seed used by the next phase.  The resampling law below is the explicit
ambient-Gaussian rejection law `coldBallStart`; it makes no membership query to `K`.

This file proves that one fixed such law is warm for every radius-four target in the
source fixed schedule, and also for every full-body target.  Thus a post-phase reset gives
an actual-path seed invariant without claiming that TV closeness implies warmness.
-/

set_option autoImplicit false

namespace Ttc.CVColdResetSeedWarm

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVColdCrossPhaseWarm
open Ttc.CVCorrectedFixedBlockCost
open Ttc.CVSourceTruncatedFixedCost
open Ttc.FiniteContinuingRetryRandomFallback
open scoped ENNReal Pointwise

variable {n m : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- Warmness budget for a fixed restart against the changing radius-four bodies. -/
noncomputable def coldResetTruncatedWarmConst (n i : Nat) : ENNReal :=
  ENNReal.ofReal 2 * (ENNReal.ofReal (Real.exp (1 / 2)) * 2) ^ i

/-- Warmness budget for the same restart against the untruncated fixed schedule. -/
noncomputable def coldResetFullWarmConst (i : Nat) : ENNReal :=
  ENNReal.ofReal 2 * ENNReal.ofReal (Real.exp (1 / 2)) ^ i

/-- A fixed, explicitly sampleable cold restart is warm for every radius-four cooling
law.  The factor two is the initial ambient-Gaussian rejection bound; every phase costs
at most `sqrt(e) * 2`, including the changing-body normalizer. -/
theorem isWarm_coldBallStart_fixedRadiusFour_coolLaw
    (hn : 1 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) {s0 radius : Real} (hs0 : 0 < s0)
    (hradius : 0 < radius) (hradiusOne : radius < 1)
    (hcold : 4 * (n : Real) * s0 ≤ radius ^ 2)
    (hrad : ∀ j, j < m →
      1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 j) * Real.sqrt n)
    (hradTwo : ∀ j, j < m →
      1 ≤ 2 * Real.sqrt (fixedSigmaSq n s0 j) * Real.sqrt n) :
    ∀ i, i < m →
      IsWarm (coldResetTruncatedWarmConst n i)
        (coldBallStart (n := n) s0 radius)
        (coolLaw m (fixedSigmaSq n s0)
          (fixedRadiusFourBody K (fixedSigmaSq n s0 i)) i) := by
  have hsigma : ∀ j, 0 < fixedSigmaSq n s0 j := by
    intro j
    unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) j
  intro i hi
  induction i with
  | zero =>
      let K0 := fixedRadiusFourBody K (fixedSigmaSq n s0 0)
      have hK0m : MeasurableSet K0 := measurableSet_fixedRadiusFourBody hK _
      have hK0ball : ball (0 : State n) 1 ⊆ K0 :=
        unitBall_subset_inter_closedBall hball (hrad 0 hi)
      have hclosed : closedBall (0 : State n) radius ⊆ K0 := by
        intro x hx
        apply hK0ball
        rw [mem_ball_zero_iff, ← dist_zero_right]
        exact lt_of_le_of_lt hx hradiusOne
      have hK0fin : volume K0 ≠ ⊤ := volume_inter_closedBall_ne_top K _
      have hw := isWarm_coldBallStart_gaussian hK0m hclosed hn hs0 hradius hcold
      rw [coolLaw_eq_uniformOn_gaussianWeight hsigma hK0m hK0ball hK0fin hi]
      simpa [coldResetTruncatedWarmConst, fixedSigmaSq] using hw
  | succ i ih =>
      have hii : i < m := by omega
      have hiprev : i + 1 < m := hi
      have hwprev := ih hii
      let Ki := fixedRadiusFourBody K (fixedSigmaSq n s0 i)
      let Kinext := fixedRadiusFourBody K (fixedSigmaSq n s0 (i + 1))
      let gaussianNext : Measure (State n) :=
        volume.withDensity (gaussianWeight (fixedSigmaSq n s0 (i + 1)))
      have hstep0 := isWarm_coolLaw_fixedRadiusFour_succ_of_normalizer_ratio
        (m := m) hn hs0 hK hKc hball hiprev (hrad i hii)
      have hratio : gaussianNext Kinext / gaussianNext Ki ≤ 2 := by
        simpa only [gaussianNext, Ki, Kinext] using
          (gaussianNext_fixedRadiusFour_ratio_le_two
            (K := K) hn hs0 hK hKc hball hfin (i := i) (hradTwo (i + 1) hi))
      have hstep : IsWarm (ENNReal.ofReal (Real.exp (1 / 2)) * 2)
          (coolLaw m (fixedSigmaSq n s0) Ki i)
          (coolLaw m (fixedSigmaSq n s0) Kinext (i + 1)) := by
        exact hstep0.mono (mul_le_mul_left' hratio _)
      have hcomp := hwprev.trans hstep
      simpa only [Ki, Kinext, coldResetTruncatedWarmConst, pow_succ, mul_assoc] using hcomp

/-- Speedy-law form of the preceding theorem.  The fixed rejection ball lies in the
standard shrunken radius-four body at every phase. -/
theorem isWarm_coldBallStart_fixedRadiusFour_ellGaussianProb
    (hn : 1 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) {s0 radius : Real} (hs0 : 0 < s0)
    (hradius : 0 < radius)
    (hradiusShrink : radius < 1 - 1 / (2 * (n : Real)))
    (hcold : 4 * (n : Real) * s0 ≤ radius ^ 2)
    (hrad : ∀ j, j < m →
      1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 j) * Real.sqrt n)
    (hradTwo : ∀ j, j < m →
      1 ≤ 2 * Real.sqrt (fixedSigmaSq n s0 j) * Real.sqrt n)
    {i : Nat} (hi : i < m) :
    IsWarm (coldResetTruncatedWarmConst n i)
      (coldBallStart (n := n) s0 radius)
      (ellGaussianProb
        (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
        (fixedSigmaSq n s0 i)) := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  let Ki := fixedRadiusFourBody K (fixedSigmaSq n s0 i)
  have hnR : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hc0 : 0 < c := lt_of_lt_of_le hradius hradiusShrink.le
  have hc1 : c < 1 := by
    dsimp [c]
    have : 0 < 1 / (2 * (n : Real)) := by positivity
    linarith
  have hKim : MeasurableSet Ki := measurableSet_fixedRadiusFourBody hK _
  have hKic : Convex Real Ki := convex_fixedRadiusFourBody hKc _
  have hKiball : ball (0 : State n) 1 ⊆ Ki :=
    unitBall_subset_inter_closedBall hball (hrad i hi)
  have hKifin : volume Ki ≠ ⊤ := volume_inter_closedBall_ne_top K _
  have hsubset : closedBall (0 : State n) radius ⊆ c • Ki :=
    closedBall_subset_smul_set_of_lt hKiball hradius.le
      (by simpa only [c] using hradiusShrink)
  have hsupp : coldBallStart (n := n) s0 radius (c • Ki)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr hsubset)
      (coldBallStart_compl_eq_zero s0 radius)
  have hsigma : ∀ j, 0 < fixedSigmaSq n s0 j := by
    intro j
    unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) j
  have hcool := isWarm_coldBallStart_fixedRadiusFour_coolLaw
    (m := m) hn hK hKc hball hfin hs0 hradius
      (lt_trans hradiusShrink hc1) hcold hrad hradTwo i hi
  rw [coolLaw_eq_uniformOn_gaussianWeight hsigma hKim hKiball hKifin hi] at hcool
  have hdelta := fixedRadiusFourDelta_pos hn (hsigma i)
  have hdc : fixedRadiusFourDelta n (fixedSigmaSq n s0 i) ≤ 1 - c := by
    rw [show 1 - c = 1 / (2 * (n : Real)) by dsimp [c]; ring]
    exact fixedRadiusFourDelta_le_n
  exact isWarm_ellGaussianProb_of_supported_on_shrunken hKim hKic hKiball
    hc0 hc1 hdelta hdc hsupp (by simpa only [Ki] using hcool)

/-- The same fixed restart is warm for every full-body cooling law.  Here each fixed-rate
variance update costs only `sqrt(e)`, with no changing-body factor. -/
theorem isWarm_coldBallStart_fixed_fullCoolLaw
    (hn : 1 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) {s0 radius : Real} (hs0 : 0 < s0)
    (hradius : 0 < radius) (hradiusOne : radius < 1)
    (hcold : 4 * (n : Real) * s0 ≤ radius ^ 2) :
    ∀ i, i < m →
      IsWarm (coldResetFullWarmConst i)
        (coldBallStart (n := n) s0 radius)
        (coolLaw m (fixedSigmaSq n s0) K i) := by
  have hsigma : ∀ j, 0 < fixedSigmaSq n s0 j := by
    intro j
    unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) j
  intro i hi
  induction i with
  | zero =>
      have hclosed : closedBall (0 : State n) radius ⊆ K := by
        intro x hx
        apply hball
        rw [mem_ball_zero_iff, ← dist_zero_right]
        exact lt_of_le_of_lt hx hradiusOne
      have hw := isWarm_coldBallStart_gaussian hK hclosed hn hs0 hradius hcold
      rw [coolLaw_eq_uniformOn_gaussianWeight hsigma hK hball hfin hi]
      simpa [coldResetFullWarmConst, fixedSigmaSq] using hw
  | succ i ih =>
      have hii : i < m := by omega
      have hwprev := ih hii
      have hsched : fixedSigmaSq n s0 (i + 1) =
          (1 + 1 / (n : Real)) * fixedSigmaSq n s0 i := by
        rw [fixedSigmaSq, fixedSigmaSq, geomSchedule_succ]
        ring
      have hstep := isWarm_coolLaw_succ_sqrt_exp hi hK hfin hKc hball hsigma hsched
      have hcomp := hwprev.trans hstep
      simpa only [coldResetFullWarmConst, pow_succ, mul_assoc] using hcomp

/-- Full-body speedy-law form, used at the cold-to-hot boundary and throughout the hot
block if the independent reset is retained. -/
theorem isWarm_coldBallStart_fixed_full_ellGaussianProb
    (hn : 1 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) {s0 radius : Real} (hs0 : 0 < s0)
    (hradius : 0 < radius)
    (hradiusShrink : radius < 1 - 1 / (2 * (n : Real)))
    (hcold : 4 * (n : Real) * s0 ≤ radius ^ 2)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    {i : Nat} (hi : i < m) :
    IsWarm (coldResetFullWarmConst i)
      (coldBallStart (n := n) s0 radius)
      (ellGaussianProb K delta (fixedSigmaSq n s0 i)) := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hc0 : 0 < c := lt_of_lt_of_le hradius hradiusShrink.le
  have hc1 : c < 1 := by
    dsimp [c]
    have hnR : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
    have : 0 < 1 / (2 * (n : Real)) := by positivity
    linarith
  have hsubset : closedBall (0 : State n) radius ⊆ c • K :=
    closedBall_subset_smul_set_of_lt hball hradius.le
      (by simpa only [c] using hradiusShrink)
  have hsupp : coldBallStart (n := n) s0 radius (c • K)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr hsubset)
      (coldBallStart_compl_eq_zero s0 radius)
  have hsigma : ∀ j, 0 < fixedSigmaSq n s0 j := by
    intro j
    unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) j
  have hcool := isWarm_coldBallStart_fixed_fullCoolLaw
    (m := m) hn hK hKc hball hfin hs0 hradius
      (lt_trans hradiusShrink hc1) hcold i hi
  rw [coolLaw_eq_uniformOn_gaussianWeight hsigma hK hball hfin hi] at hcool
  have hdc : delta ≤ 1 - c := by
    rw [show 1 - c = 1 / (2 * (n : Real)) by dsimp [c]; ring]
    exact hdeltan
  exact isWarm_ellGaussianProb_of_supported_on_shrunken hK hKc hball
    hc0 hc1 hdelta hdc hsupp hcool

/-- Seed-coordinate wrapper for the concrete score/seed fallback used by the operational
reset adapter. -/
theorem isWarm_seed_coldScoreSeedFallback_fixedRadiusFour
    (hn : 1 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) {s0 radius : Real} (hs0 : 0 < s0)
    (hradius : 0 < radius)
    (hradiusShrink : radius < 1 - 1 / (2 * (n : Real)))
    (hcold : 4 * (n : Real) * s0 ≤ radius ^ 2)
    (hrad : ∀ j, j < m →
      1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 j) * Real.sqrt n)
    (hradTwo : ∀ j, j < m →
      1 ≤ 2 * Real.sqrt (fixedSigmaSq n s0 j) * Real.sqrt n)
    {i : Nat} (hi : i < m) (scoreScale : Real) :
    IsWarm (coldResetTruncatedWarmConst n i)
      (Measure.map Prod.snd
        (coldScoreSeedFallback (n := n) scoreScale s0 radius))
      (ellGaussianProb
        (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
        (fixedSigmaSq n s0 i)) := by
  apply isWarm_snd_coldScoreSeedFallback
  exact isWarm_coldBallStart_fixedRadiusFour_ellGaussianProb
    (m := m) hn hK hKc hball hfin hs0 hradius hradiusShrink hcold
      hrad hradTwo hi

#print axioms isWarm_coldBallStart_fixedRadiusFour_ellGaussianProb
#print axioms isWarm_coldBallStart_fixed_full_ellGaussianProb
#print axioms isWarm_seed_coldScoreSeedFallback_fixedRadiusFour

end Ttc.CVColdResetSeedWarm
