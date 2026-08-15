import Ttc.Exec.CVSlowFullBodySourceSchedule
import Ttc.Exec.CVSlowCanonicalShareBounds
import Ttc.Exec.CVHybridInteriorPhaseScoreVariance
import Arlib.Convexity.GaussianCooling.TerminalPhase

/-! Exact Gaussian score moments for the uniformly slow source schedule. -/

set_option autoImplicit false

namespace Ttc.CVSlowGaussianPhaseMoment

open MeasureTheory Metric Set
open Arlib.GaussianCooling
open Ttc.CVSlowFullBodySourceSchedule
open Ttc.CVSlowCanonicalShareBounds

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

theorem exp_half_le_two : Real.exp (1 / 2 : Real) ≤ 2 := by
  calc
    Real.exp (1 / 2 : Real) ≤ Real.exp (Real.log 2) := by
      apply Real.exp_le_exp.mpr
      linarith [Real.log_two_gt_d9]
    _ = 2 := Real.exp_log (by norm_num)

/-- The slow schedule has exact-law factor at most two at every score coordinate,
including the final Gaussian-to-uniform coordinate.  Interior phases use the
radius-free fixed-rate CV estimate.  At and after the terminal phase, the hypothesis
`R² ≤ N` and the declared terminal variance give the paper's `exp(1/2)` bound. -/
theorem slowSource_phaseScore_interior_sq_moment_le_two
    (hn : 3 ≤ n) {N s0 R : Real} (hN : 0 < N) (hs0 : 0 < s0)
    (hsN : s0 ≤ N) (hR2 : R ^ 2 ≤ N)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R) (i : Nat) :
    let m := slowSourcePhases n N s0 + 1
    let sigmaSq := slowSourceSigmaSq n s0
    ∫ x, phaseScore m sigmaSq (interior K) i x ^ 2
        ∂(coolLaw m sigmaSq K i) ≤
      2 * (∫ x, phaseScore m sigmaSq (interior K) i x
        ∂(coolLaw m sigmaSq K i)) ^ 2 := by
  dsimp only
  let m := slowSourcePhases n N s0 + 1
  let sigmaSq := slowSourceSigmaSq n s0
  have hn1 : 1 ≤ n := by omega
  have hsigma : ∀ j, 0 < sigmaSq j := slowSourceSigmaSq_pos hn1 hs0
  rw [integral_phaseScore_interior_sq_eq hKc,
    integral_phaseScore_interior_eq hKc]
  by_cases hi : i + 1 < m
  · have hraw := coolLaw_sq_moment_le hsigma hKc hK hball hfin hi hn
      (slowSourceSigmaSq_succ n s0 i)
    refine hraw.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
    have hnR : (3 : Real) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : Real) < n := by positivity
    have : 2 / (n : Real) ≤ 1 := (div_le_one hn0).2 (by linarith)
    linarith
  · have hterm : m ≤ i + 1 := not_lt.mp hi
    have hmIndex : slowSourcePhases n N s0 ≤ i := by
      dsimp only [m] at hterm
      omega
    have hterminal := target_le_slowSourceSigmaSq_terminal hn1 hN hs0 hsN
    have hmono := sigmaSq_mono_of_fixedRate hsigma (by omega : 0 < n)
      (slowSourceSigmaSq_succ n s0) hmIndex
    have hRsig : R ^ 2 ≤ sigmaSq i := hR2.trans (hterminal.trans hmono)
    have hraw := coolLaw_sq_moment_le_terminal_paper hsigma hK hball hfin hKR
      hterm hRsig
    exact hraw.trans (mul_le_mul_of_nonneg_right exp_half_le_two (sq_nonneg _))

#print axioms exp_half_le_two
#print axioms slowSource_phaseScore_interior_sq_moment_le_two

end Ttc.CVSlowGaussianPhaseMoment
