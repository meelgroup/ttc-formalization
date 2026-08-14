import Ttc.Exec.CVColdOperationalSeedReset

/-!
# Quantitative logarithmic envelope for the cold independent refresh

The unified cold refresh radius is `min (1/4) (2 sqrt(n s))`.  In the uncapped branch
the ball contains at least half of the ambient Gaussian mass, so the exact normalizer
ratio is at most two.  In the capped branch the existing radial envelope applies, while
the cap condition itself implies that its inverse-variance term is at most `2n`.
-/

set_option autoImplicit false

namespace Ttc.CVColdRefreshWarmLog

open MeasureTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVIndependentRefreshSeedLaws
open Ttc.CVColdOperationalSeedReset
open Ttc.CVCorrectedFixedBlockCost
open Ttc.CVSourceTruncatedFixedCost
open scoped ENNReal

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- Piecewise quantitative envelope matching the two branches of the unified radius. -/
noncomputable def coldRefreshWarmEnvelope (n : Nat) (s : Real) : ENNReal :=
  if coldRefreshRadius n s ≤ hotRefreshRadius then
    ENNReal.ofReal 2
  else
    hotRefreshWarmEnvelope n (4 * Real.sqrt s * Real.sqrt n) s

/-- At the phase-scaled radius, every restricted-body Gaussian normalizer ratio is at
most two. -/
theorem gaussianBallWarmFactor_coldRefreshRadius_le_two
    (hn : 1 ≤ n) {K : Set (State n)} {s : Real} (hs : 0 < s) :
    gaussianBallWarmFactor K s (coldRefreshRadius n s) ≤ ENNReal.ofReal 2 := by
  let nu : Measure (State n) := gaussianBase n s
  let B : Set (State n) := closedBall (0 : State n) (coldRefreshRadius n s)
  have hrho : 0 < coldRefreshRadius n s := coldRefreshRadius_pos hn hs
  have hB0 : nu B ≠ 0 := by
    dsimp only [nu, gaussianBase, B]
    exact withDensity_gaussianWeight_ne_zero s
      (measure_closedBall_pos volume (0 : State n) hrho).ne'
  have hBtop : nu B ≠ ⊤ := by
    dsimp only [nu, gaussianBase, B]
    exact withDensity_gaussianWeight_ne_top hs measurableSet_closedBall
      measure_closedBall_lt_top.ne
  have hhalf : ENNReal.ofReal (1 / 2 : Real) * nu Set.univ ≤ nu B := by
    simpa only [nu, gaussianBase, B] using
      (half_ambientGaussian_le_coldBall (n := n) hn hs hrho
        (by rw [coldRefreshRadius_sq hn hs]))
  have hamb : nu Set.univ ≤ ENNReal.ofReal 2 * nu B := by
    calc
      nu Set.univ = ENNReal.ofReal 2 *
          (ENNReal.ofReal (1 / 2 : Real) * nu Set.univ) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 2)]
        norm_num
      _ ≤ ENNReal.ofReal 2 * nu B := mul_le_mul_left' hhalf _
  rw [gaussianBallWarmFactor, show gaussianBase n s K = nu K by rfl,
    show gaussianBase n s (closedBall (0 : State n) (coldRefreshRadius n s)) =
      nu B by rfl, ENNReal.div_le_iff hB0 hBtop]
  exact (measure_mono (subset_univ K)).trans hamb

/-- The exact radius-four refresh factor is bounded by the piecewise explicit envelope. -/
theorem coldNextRefreshWarmFactor_le_envelope
    (hn : 1 ≤ n) (K : Set (State n)) (s0 : Real) (i : Nat)
    (hK : MeasurableSet K) (hs0 : 0 < s0) :
    coldNextRefreshWarmFactor n K s0 i ≤
      coldRefreshWarmEnvelope n (fixedSigmaSq n s0 (i + 1)) := by
  let s := fixedSigmaSq n s0 (i + 1)
  let body := fixedRadiusFourBody K s
  have hs : 0 < s := by
    dsimp only [s]
    unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) (i + 1)
  by_cases hsmall : coldRefreshRadius n s ≤ hotRefreshRadius
  · have hradius : coldNextRefreshRadius n s = coldRefreshRadius n s := by
      exact min_eq_right hsmall
    rw [coldRefreshWarmEnvelope, if_pos hsmall]
    simpa only [coldNextRefreshWarmFactor, s, body, hradius] using
      (gaussianBallWarmFactor_coldRefreshRadius_le_two
        (K := body) hn hs)
  · have hcap : hotRefreshRadius ≤ coldRefreshRadius n s := le_of_not_ge hsmall
    have hradius : coldNextRefreshRadius n s = hotRefreshRadius := min_eq_left hcap
    rw [coldRefreshWarmEnvelope, if_neg hsmall]
    have hsub : body ⊆ closedBall (0 : State n)
        (4 * Real.sqrt s * Real.sqrt n) := fun _ hx ↦ hx.2
    simpa only [coldNextRefreshWarmFactor, s, body, hradius] using
      (hotRefreshWarmFactor_le_envelope
        (measurableSet_fixedRadiusFourBody hK s) hs hsub)

theorem coldRefreshWarmEnvelope_ne_top
    (n : Nat) {s : Real} (hs : 0 < s) :
    coldRefreshWarmEnvelope n s ≠ ⊤ := by
  unfold coldRefreshWarmEnvelope
  split_ifs
  · exact ENNReal.ofReal_ne_top
  · unfold hotRefreshWarmEnvelope
    apply ENNReal.mul_ne_top
    · rw [ENNReal.inv_ne_top]
      exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
    · exact ENNReal.ofReal_ne_top

theorem coldRefreshWarmEnvelope_toReal_pos
    (hn : 1 ≤ n) {s : Real} (hs : 0 < s) :
    0 < (coldRefreshWarmEnvelope n s).toReal := by
  unfold coldRefreshWarmEnvelope
  split_ifs with h
  · norm_num
  · exact hotRefreshWarmEnvelope_toReal_pos n hs

/-- Coarse polynomial logarithmic bound.  In the capped branch, `1/4 < 2 sqrt(ns)`
forces the inverse-variance contribution below `2n`. -/
theorem log_coldRefreshWarmEnvelope_toReal_le
    (hn : 1 ≤ n) {s : Real} (hs : 0 < s) :
    Real.log (coldRefreshWarmEnvelope n s).toReal ≤
      Real.log 2 + 2 * (n : Real) +
        (n : Real) *
          Real.log (4 * max 1 (4 * Real.sqrt s * Real.sqrt n)) := by
  unfold coldRefreshWarmEnvelope
  split_ifs with hsmall
  · rw [ENNReal.toReal_ofReal (by norm_num : (0 : Real) ≤ 2)]
    have hn0 : (0 : Real) ≤ n := by positivity
    have hR : 1 ≤ 4 * max 1 (4 * Real.sqrt s * Real.sqrt n) := by
      have hm : (1 : Real) ≤ max 1 (4 * Real.sqrt s * Real.sqrt n) :=
        le_max_left _ _
      nlinarith
    have hlog : 0 ≤ Real.log (4 * max 1 (4 * Real.sqrt s * Real.sqrt n)) :=
      Real.log_nonneg hR
    nlinarith
  · rw [log_hotRefreshWarmEnvelope_toReal n hs]
    have hcap : hotRefreshRadius < coldRefreshRadius n s := lt_of_not_ge hsmall
    have hsq : hotRefreshRadius ^ 2 < coldRefreshRadius n s ^ 2 :=
      (sq_lt_sq₀ hotRefreshRadius_pos.le (coldRefreshRadius_pos hn hs).le).2 hcap
    rw [coldRefreshRadius_sq hn hs] at hsq
    have hinv : hotRefreshRadius ^ 2 / (2 * s) ≤ 2 * (n : Real) := by
      rw [div_le_iff₀ (by positivity : 0 < 2 * s)]
      nlinarith
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith

/-- The requested bound on the exact refresh factor itself. -/
theorem log_coldNextRefreshWarmFactor_toReal_le
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (hball : ball (0 : State n) 1 ⊆ K)
    (s0 : Real) (hs0 : 0 < s0) (i : Nat)
    (hrad : 1 ≤
      4 * Real.sqrt (fixedSigmaSq n s0 (i + 1)) * Real.sqrt n) :
    Real.log (coldNextRefreshWarmFactor n K s0 i).toReal ≤
      Real.log 2 + 2 * (n : Real) +
        (n : Real) * Real.log
          (4 * max 1
            (4 * Real.sqrt (fixedSigmaSq n s0 (i + 1)) * Real.sqrt n)) := by
  let s := fixedSigmaSq n s0 (i + 1)
  let body := fixedRadiusFourBody K s
  let radius := coldNextRefreshRadius n s
  have hs : 0 < s := by
    dsimp only [s]
    unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) (i + 1)
  have hbodyBall : ball (0 : State n) 1 ⊆ body :=
    unitBall_subset_inter_closedBall hball (by simpa only [s] using hrad)
  have hnum0 : gaussianBase n s body ≠ 0 := by
    unfold gaussianBase
    exact withDensity_gaussianWeight_ne_zero s
      (volume_inter_closedBall_ne_zero hball (by simpa only [s] using hrad))
  have hdentop : gaussianBase n s (closedBall (0 : State n) radius) ≠ ⊤ := by
    unfold gaussianBase
    exact withDensity_gaussianWeight_ne_top hs measurableSet_closedBall
      measure_closedBall_lt_top.ne
  have hfactorPos : 0 < coldNextRefreshWarmFactor n K s0 i := by
    rw [coldNextRefreshWarmFactor]
    exact ENNReal.div_pos hnum0 hdentop
  have hfactorTop := coldNextRefreshWarmFactor_ne_top hn K hK s0 hs0 i
  have henvTop := coldRefreshWarmEnvelope_ne_top n hs
  have hle := coldNextRefreshWarmFactor_le_envelope hn K s0 i hK hs0
  have hrealLe : (coldNextRefreshWarmFactor n K s0 i).toReal ≤
      (coldRefreshWarmEnvelope n s).toReal := ENNReal.toReal_mono henvTop hle
  have hlog := Real.log_le_log (ENNReal.toReal_pos hfactorPos.ne' hfactorTop) hrealLe
  exact hlog.trans (by
    simpa only [s] using log_coldRefreshWarmEnvelope_toReal_le hn hs)

#print axioms coldNextRefreshWarmFactor_le_envelope
#print axioms log_coldRefreshWarmEnvelope_toReal_le
#print axioms log_coldNextRefreshWarmFactor_toReal_le

end Ttc.CVColdRefreshWarmLog
