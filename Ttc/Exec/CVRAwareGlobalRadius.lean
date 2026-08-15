import Ttc.Exec.CVGlobalLogarithmicRadius
import Ttc.Exec.CVGaussianScoreAwareMeanBudget
import Ttc.Exec.CVSlowSourceTargetTVAccuracy

/-! A run-global radius whose tail remains small after score-envelope weighting. -/

set_option autoImplicit false

namespace Ttc.CVRAwareGlobalRadius

open Ttc.CVGlobalLogarithmicRadius
open Ttc.CVGaussianScoreAwareMeanBudget
open Ttc.CVGaussianScoreAwareParameters
open Ttc.CVGaussianFactorSevenAssembly
open Ttc.CVSlowSourceTargetTVAccuracy Ttc.CVSlowFullBodySourceSchedule

/-- Call parameter enlarged by the worst score envelope `exp(R²/(2s₀))` and a
positive target floor `b`. -/
noncomputable def rAwareRadiusCalls (R s0 b : Real) : Real :=
  max 1 (Real.exp (R ^ 2 / (2 * s0)) / (20 * b))

noncomputable def rAwareGlobalRadiusQ (n : Nat) (R s0 b : Real) : Real :=
  globalLogarithmicRadiusQ n (rAwareRadiusCalls R s0 b)

/-- One global positive floor that simultaneously pays half of the first-moment
transport budget and half of the factor-seven squared-observable budget. -/
noncomputable def slowCanonicalJointTailFloor
    (m k : Nat) (eps R s0 : Real) : Real :=
  min (scoreAwareMeanEta m k eps / 4)
    (1 / (6 * Real.exp (R ^ 2 / (2 * s0))))

theorem slowCanonicalJointTailFloor_pos
    {m k : Nat} {eps R s0 : Real} (heps : 0 < eps) :
    0 < slowCanonicalJointTailFloor m k eps R s0 := by
  unfold slowCanonicalJointTailFloor scoreAwareMeanEta
  apply lt_min
  · exact div_pos (Real.sqrt_pos.2
      (mul_pos (by norm_num) (Ttc.CVGaussianBlockRetryParameters.blockShare_pos heps)))
      (by norm_num)
  · positivity

theorem slowCanonicalJointTailFloor_mean_le
    {m k : Nat} {eps R s0 ratio : Real} (heps : 0 < eps)
    (hratio : 1 ≤ ratio) :
    slowCanonicalJointTailFloor m k eps R s0 ≤
      scoreAwareMeanEta m k eps * ratio / 2 := by
  have heta0 := scoreAwareMeanEta_nonneg m k eps
  calc
    slowCanonicalJointTailFloor m k eps R s0 ≤
        scoreAwareMeanEta m k eps / 4 := min_le_left _ _
    _ ≤ scoreAwareMeanEta m k eps * ratio / 2 := by nlinarith

theorem slowCanonicalJointTailFloor_moment_le
    {m k : Nat} {eps R s0 sigma ratio : Real}
    (hs0 : 0 < s0) (hsigma : s0 ≤ sigma) (hratio : 1 ≤ ratio) :
    slowCanonicalJointTailFloor m k eps R s0 *
        (Real.exp (R ^ 2 / (2 * sigma)) * 15) ≤
      ((7 - 2) * ratio ^ 2) / 2 := by
  have hsigma0 : 0 < sigma := hs0.trans_le hsigma
  have hexp : Real.exp (R ^ 2 / (2 * sigma)) ≤
      Real.exp (R ^ 2 / (2 * s0)) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg R]
  have hfloor := min_le_right
    (scoreAwareMeanEta m k eps / 4)
    (1 / (6 * Real.exp (R ^ 2 / (2 * s0))))
  have hleft : slowCanonicalJointTailFloor m k eps R s0 *
      (Real.exp (R ^ 2 / (2 * sigma)) * 15) ≤ 5 / 2 := by
    calc
      _ ≤ (1 / (6 * Real.exp (R ^ 2 / (2 * s0)))) *
          (Real.exp (R ^ 2 / (2 * sigma)) * 15) := by
        gcongr
        exact hfloor
      _ ≤ (1 / (6 * Real.exp (R ^ 2 / (2 * s0)))) *
          (Real.exp (R ^ 2 / (2 * s0)) * 15) := by gcongr
      _ = 5 / 2 := by field_simp; norm_num
  exact hleft.trans (by nlinarith [sq_nonneg (ratio - 1)])

theorem one_le_rAwareRadiusCalls (R s0 b : Real) :
    1 ≤ rAwareRadiusCalls R s0 b := le_max_left _ _

/-- The selected tail pays the full conservative score envelope. -/
theorem rAwareGlobalRadiusQ_tail_mul_exp_le
    {n : Nat} (hn : 1 ≤ n) {R s0 b : Real}
    (hs0 : 0 < s0) (hb : 0 < b) :
    (rAwareGlobalRadiusQ n R s0 b *
        Real.exp (-(rAwareGlobalRadiusQ n R s0 b ^ 2 - 1) / 2)) ^ n *
      Real.exp (R ^ 2 / (2 * s0)) ≤ b := by
  let A := rAwareRadiusCalls R s0 b
  let q := rAwareGlobalRadiusQ n R s0 b
  let tail := (q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n
  let scale := Real.exp (R ^ 2 / (2 * s0))
  have hA : 1 ≤ A := one_le_rAwareRadiusCalls R s0 b
  have htail0 : 0 ≤ tail := by
    have hq : 0 ≤ q := (by
      dsimp only [q, rAwareGlobalRadiusQ]
      exact (by norm_num : (0 : Real) ≤ 4).trans
        (four_le_globalLogarithmicRadiusQ hn hA))
    exact pow_nonneg (mul_nonneg hq (Real.exp_pos _).le) n
  have htotal : A * tail ≤ 1 / 20 := by
    dsimp only [A, q, tail, rAwareGlobalRadiusQ]
    exact globalLogarithmicRadiusQ_totalTail_le hn hA
  have hbase : scale / (20 * b) ≤ A := by
    dsimp only [A, scale, rAwareRadiusCalls]
    exact le_max_right _ _
  have hsmall : (scale / (20 * b)) * tail ≤ 1 / 20 :=
    (mul_le_mul_of_nonneg_right hbase htail0).trans htotal
  have hb20 : 0 < 20 * b := mul_pos (by norm_num) hb
  dsimp only [tail, q, scale] at hsmall ⊢
  calc
    (rAwareGlobalRadiusQ n R s0 b *
          Real.exp (-(rAwareGlobalRadiusQ n R s0 b ^ 2 - 1) / 2)) ^ n *
        Real.exp (R ^ 2 / (2 * s0)) =
      (Real.exp (R ^ 2 / (2 * s0)) / (20 * b) *
        (rAwareGlobalRadiusQ n R s0 b *
          Real.exp (-(rAwareGlobalRadiusQ n R s0 b ^ 2 - 1) / 2)) ^ n) *
        (20 * b) := by field_simp
    _ ≤ (1 / 20 : Real) * (20 * b) := by
      exact mul_le_mul_of_nonneg_right hsmall hb20.le
    _ = b := by ring

/-- Phasewise form consumed by the target-TV mean and moment transports.  A caller only
has to choose `b` below the desired phase budget; no unweighted-tail inference is used. -/
theorem rAwareGlobalRadiusQ_phase_tail_scaled_le
    {n : Nat} (hn : 1 ≤ n) {R s0 sigma b target : Real}
    (hs0 : 0 < s0) (hsigma : s0 ≤ sigma) (hb : 0 < b)
    (hbudget : b ≤ target) :
    (rAwareGlobalRadiusQ n R s0 b *
        Real.exp (-(rAwareGlobalRadiusQ n R s0 b ^ 2 - 1) / 2)) ^ n *
      Real.exp (R ^ 2 / (2 * sigma)) ≤ target := by
  have hsigma0 : 0 < sigma := hs0.trans_le hsigma
  have hexp : Real.exp (R ^ 2 / (2 * sigma)) ≤
      Real.exp (R ^ 2 / (2 * s0)) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg R]
  have htail0 : 0 ≤
      (rAwareGlobalRadiusQ n R s0 b *
        Real.exp (-(rAwareGlobalRadiusQ n R s0 b ^ 2 - 1) / 2)) ^ n := by
    have hq : 0 ≤ rAwareGlobalRadiusQ n R s0 b :=
      (by norm_num : (0 : Real) ≤ 4).trans
        (four_le_globalLogarithmicRadiusQ hn
          (one_le_rAwareRadiusCalls R s0 b))
    exact pow_nonneg (mul_nonneg hq (Real.exp_pos _).le) n
  calc
    _ ≤ (rAwareGlobalRadiusQ n R s0 b *
          Real.exp (-(rAwareGlobalRadiusQ n R s0 b ^ 2 - 1) / 2)) ^ n *
        Real.exp (R ^ 2 / (2 * s0)) :=
      mul_le_mul_of_nonneg_left hexp htail0
    _ ≤ b := rAwareGlobalRadiusQ_tail_mul_exp_le hn hs0 hb
    _ ≤ target := hbudget

theorem initial_le_slowSourceSigmaSq
    {n : Nat} (hn : 1 ≤ n) {s0 : Real} (hs0 : 0 < s0) (i : Nat) :
    s0 ≤ slowSourceSigmaSq n s0 i := by
  unfold slowSourceSigmaSq Arlib.GaussianCooling.geomSchedule
  calc
    s0 = s0 * 1 := by ring
    _ ≤ s0 * (1 + 1 / (n : Real)) ^ i := by
      gcongr
      exact one_le_pow₀ (le_add_of_nonneg_right (by
        have hn0 : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
        positivity))

/-- Direct `slowTargetError.toReal` form used by the robust source certificate. -/
theorem slowTargetError_rAware_scaled_le
    {n m i : Nat} (hn : 1 ≤ n) {R s0 b target : Real}
    (hs0 : 0 < s0) (hb : 0 < b) (hi : i < m)
    (hbudget : b ≤ target) :
    (slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m i).toReal *
        Real.exp (R ^ 2 / (2 * slowSourceSigmaSq n s0 i)) ≤ target := by
  rw [slowTargetError_active hi, ENNReal.toReal_ofReal]
  · exact rAwareGlobalRadiusQ_phase_tail_scaled_le hn hs0
      (initial_le_slowSourceSigmaSq hn hs0 i) hb hbudget
  · have hq : 0 ≤ rAwareGlobalRadiusQ n R s0 b :=
      (by norm_num : (0 : Real) ≤ 4).trans
        (four_le_globalLogarithmicRadiusQ hn
          (one_le_rAwareRadiusCalls R s0 b))
    exact pow_nonneg (mul_nonneg hq (Real.exp_pos _).le) n

/-- Split-budget form: local operational mixing and the R-aware radial tail each spend
half of a requested phase mean budget. -/
theorem mix_add_slowTargetError_rAware_scaled_le
    {n m i : Nat} (hn : 1 ≤ n) {R s0 b target : Real} {mix : ENNReal}
    (hs0 : 0 < s0) (hb : 0 < b) (hi : i < m) (hmixTop : mix ≠ ⊤)
    (hmix : mix.toReal * Real.exp (R ^ 2 /
      (2 * slowSourceSigmaSq n s0 i)) ≤ target / 2)
    (hbudget : b ≤ target / 2) :
    (mix + slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m i).toReal *
        Real.exp (R ^ 2 / (2 * slowSourceSigmaSq n s0 i)) ≤ target := by
  rw [ENNReal.toReal_add hmixTop (slowTargetError_ne_top n _ m i)]
  have htail : (slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m i).toReal *
      Real.exp (R ^ 2 / (2 * slowSourceSigmaSq n s0 i)) ≤ target / 2 :=
    slowTargetError_rAware_scaled_le hn hs0 hb hi hbudget
  calc
    (mix.toReal + (slowTargetError n
        (rAwareGlobalRadiusQ n R s0 b) m i).toReal) *
          Real.exp (R ^ 2 / (2 * slowSourceSigmaSq n s0 i)) =
      mix.toReal * Real.exp (R ^ 2 / (2 * slowSourceSigmaSq n s0 i)) +
        (slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m i).toReal *
          Real.exp (R ^ 2 / (2 * slowSourceSigmaSq n s0 i)) := by ring
    _ ≤ target / 2 + target / 2 := add_le_add hmix htail
    _ = target := by ring

theorem scoreAwareMixError_halfSlack_mul_boundSq_le
    {m k : Nat} {eps : Real} {slack boundSq : Nat → Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hslack : ∀ i, 0 < slack i) (hbound : ∀ i, 0 < boundSq i) (i : Nat) :
    (scoreAwareMixError m k eps (fun j => slack j / 2) boundSq i).toReal *
        boundSq i ≤ slack i / 2 := by
  have hs : ∀ j, 0 < slack j / 2 := by
    intro j
    exact div_pos (hslack j) (by norm_num)
  simpa using scoreAwareMixError_mul_boundSq_le_slack
    (m := m) (k := k) (eps := eps) (slack := fun j => slack j / 2)
    (boundSq := boundSq) heps heps1 hs hbound i

/-- The same R-aware selector pays a squared-observable transport budget when its real
floor is chosen after the remaining exponential factor.  This is the exact radial-tail
seam required by the factor-seven Gaussian phase-moment transport. -/
theorem slowTargetError_rAware_mul_phaseBound_le
    {n m i : Nat} (hn : 1 ≤ n) {R s0 b slack : Real}
    (hs0 : 0 < s0) (hb : 0 < b) (hi : i < m)
    (hbudget : b *
        (Real.exp (R ^ 2 / (2 * slowSourceSigmaSq n s0 i)) * 15) ≤
      slack / 2) :
    (slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m i).toReal *
        (Real.exp (R ^ 2 / (2 * slowSourceSigmaSq n s0 i)) ^ 2 * 15) ≤
      slack / 2 := by
  have htail := slowTargetError_rAware_scaled_le
    (n := n) (m := m) (i := i) hn (R := R) (s0 := s0) (b := b)
    (target := b) hs0 hb hi (le_refl b)
  have he0 : 0 ≤ Real.exp
      (R ^ 2 / (2 * slowSourceSigmaSq n s0 i)) * 15 := by positivity
  calc
    (slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m i).toReal *
        (Real.exp (R ^ 2 / (2 * slowSourceSigmaSq n s0 i)) ^ 2 * 15) =
      ((slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m i).toReal *
        Real.exp (R ^ 2 / (2 * slowSourceSigmaSq n s0 i))) *
        (Real.exp (R ^ 2 / (2 * slowSourceSigmaSq n s0 i)) * 15) := by ring
    _ ≤ b * (Real.exp
        (R ^ 2 / (2 * slowSourceSigmaSq n s0 i)) * 15) :=
      mul_le_mul_of_nonneg_right htail he0
    _ ≤ slack / 2 := hbudget

/-- Complete phasewise second-moment split: half-slack score-aware mixing plus the
R-aware local-to-full tail fit the original factor-seven transport allowance. -/
theorem scoreAwareMix_add_slowTargetError_rAware_phaseBound_le
    {n m k chainLength i : Nat} (hn : 1 ≤ n)
    {eps R s0 b : Real} {sigmaSq : Nat → Real}
    {K : Set (EuclideanSpace Real (Fin n))} {C : Nat → Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hs0 : 0 < s0) (hb : 0 < b)
    (hi : i < m)
    (hsigma : ∀ j, 0 < sigmaSq j)
    (hball : Metric.ball (0 : EuclideanSpace Real (Fin n)) 1 ⊆ K)
    (hfin : MeasureTheory.volume K ≠ ⊤) (hC7 : ∀ j, C j < 7)
    (hsigmaSlow : sigmaSq = slowSourceSigmaSq n s0)
    (hbudget : b * (Real.exp (R ^ 2 / (2 * sigmaSq i)) * 15) ≤
      phaseMomentSlackSeven chainLength sigmaSq K C i / 2) :
    (scoreAwareMixError (m + 1) k (eps / 2)
        (fun j ↦ phaseMomentSlackSeven chainLength sigmaSq K C j / 2)
        (phaseScoreTransportBoundSqSeven R sigmaSq) i +
      slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m i).toReal *
        phaseScoreTransportBoundSqSeven R sigmaSq i ≤
      phaseMomentSlackSeven chainLength sigmaSq K C i := by
  have hslackPos : ∀ j, 0 < phaseMomentSlackSeven chainLength sigmaSq K C j :=
    phaseMomentSlackSeven_pos hsigma hball hfin hC7
  have hboundPos : ∀ j, 0 < phaseScoreTransportBoundSqSeven R sigmaSq j :=
    phaseScoreTransportBoundSqSeven_pos
  have hlocal := scoreAwareMixError_halfSlack_mul_boundSq_le
    (m := m + 1) (k := k) (eps := eps / 2)
    (slack := phaseMomentSlackSeven chainLength sigmaSq K C)
    (boundSq := phaseScoreTransportBoundSqSeven R sigmaSq)
    (by positivity) (by linarith) hslackPos hboundPos i
  have htail : (slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m i).toReal *
      phaseScoreTransportBoundSqSeven R sigmaSq i ≤
        phaseMomentSlackSeven chainLength sigmaSq K C i / 2 := by
    rw [hsigmaSlow, phaseScoreTransportBoundSqSeven]
    simpa only [show (1 + 2 * 7 : Real) = 15 by norm_num] using
      (slowTargetError_rAware_mul_phaseBound_le hn hs0 hb hi
        (by simpa only [hsigmaSlow] using hbudget))
  rw [ENNReal.toReal_add
    (scoreAwareMixError_ne_top _ _ _ _ _ _)
    (slowTargetError_ne_top n _ m i)]
  calc
    _ = (scoreAwareMixError (m + 1) k (eps / 2)
          (fun j ↦ phaseMomentSlackSeven chainLength sigmaSq K C j / 2)
          (phaseScoreTransportBoundSqSeven R sigmaSq) i).toReal *
          phaseScoreTransportBoundSqSeven R sigmaSq i +
        (slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m i).toReal *
          phaseScoreTransportBoundSqSeven R sigmaSq i := by ring
    _ ≤ phaseMomentSlackSeven chainLength sigmaSq K C i / 2 +
        phaseMomentSlackSeven chainLength sigmaSq K C i / 2 := add_le_add hlocal htail
    _ = phaseMomentSlackSeven chainLength sigmaSq K C i := by ring

#print axioms rAwareGlobalRadiusQ_tail_mul_exp_le
#print axioms slowCanonicalJointTailFloor_pos
#print axioms slowCanonicalJointTailFloor_mean_le
#print axioms slowCanonicalJointTailFloor_moment_le
#print axioms rAwareGlobalRadiusQ_phase_tail_scaled_le
#print axioms slowTargetError_rAware_scaled_le
#print axioms mix_add_slowTargetError_rAware_scaled_le
#print axioms scoreAwareMixError_halfSlack_mul_boundSq_le
#print axioms slowTargetError_rAware_mul_phaseBound_le
#print axioms scoreAwareMix_add_slowTargetError_rAware_phaseBound_le

end Ttc.CVRAwareGlobalRadius
