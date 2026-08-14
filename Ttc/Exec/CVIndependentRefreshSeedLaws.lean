import Ttc.Exec.CVColdCrossPhaseWarm
import Ttc.Exec.FiniteContinuingRetryRandomFallback

/-!
# Samplable independent seed-refresh laws for Gaussian CV phases

An always-refresh score/seed adapter needs a fresh raw-seed law after each phase.  This
file supplies two such laws without using the unknown cooling normalizer:

* a phase-scaled Gaussian ball for the radius-four cold block;
* a fixed radius-`1/4` Gaussian ball for an arbitrary finite-volume hot body.

The cold law is `2`-warm when its ball contains half of the ambient Gaussian mass.  For
the hot law no dimension-free constant is possible for arbitrary variance and body.  We
therefore retain the exact, finite Gaussian-normalizer ratio.  Only its logarithm is used
by the mixing deadline.
-/

set_option autoImplicit false

namespace Ttc.CVIndependentRefreshSeedLaws

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVColdCrossPhaseWarm
open scoped ENNReal Pointwise

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- The unnormalised ambient Gaussian measure used by `coldBallStart`. -/
noncomputable def gaussianBase (n : Nat) (s : Real) : Measure (State n) :=
  volume.withDensity (gaussianWeight s)

/-- Exact normalizer-ratio warmth of a Gaussian ball inside `K`. -/
noncomputable def gaussianBallWarmFactor
    (K : Set (State n)) (s rho : Real) : ENNReal :=
  gaussianBase n s K / gaussianBase n s (closedBall (0 : State n) rho)

/-- A fixed inner radius that lies strictly inside the standard source shrink in every
positive dimension. -/
noncomputable def hotRefreshRadius : Real := 1 / 4

/-- Explicit radial envelope for the fixed hot refresh.  Written in `ENNReal` form so
it plugs directly into the repository's mixing deadlines. -/
noncomputable def hotRefreshWarmEnvelope
    (n : Nat) (R s : Real) : ENNReal :=
  (ENNReal.ofReal (Real.exp (-(hotRefreshRadius ^ 2) / (2 * s))))⁻¹ *
    ENNReal.ofReal ((4 * max 1 R) ^ n)

/-- The phase-scaled cold refresh radius `2 sqrt(n) sqrt(s)`. -/
noncomputable def coldRefreshRadius (n : Nat) (s : Real) : Real :=
  2 * Real.sqrt (n : Real) * Real.sqrt s

theorem hotRefreshWarmEnvelope_toReal_pos
    (n : Nat) {R s : Real} (hs : 0 < s) :
    0 < (hotRefreshWarmEnvelope n R s).toReal := by
  have hR : 0 < 4 * max 1 R := by
    have : (0 : Real) < max 1 R := one_pos.trans_le (le_max_left _ _)
    positivity
  have ha : 0 < Real.exp (-(hotRefreshRadius ^ 2) / (2 * s)) := Real.exp_pos _
  unfold hotRefreshWarmEnvelope
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal ha.le,
    ENNReal.toReal_ofReal (pow_nonneg hR.le n)]
  positivity

theorem coldRefreshRadius_pos (hn : 1 ≤ n) {s : Real} (hs : 0 < s) :
    0 < coldRefreshRadius n s := by
  unfold coldRefreshRadius
  have hnR : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  positivity

theorem coldRefreshRadius_sq (hn : 1 ≤ n) {s : Real} (hs : 0 < s) :
    coldRefreshRadius n s ^ 2 = 4 * (n : Real) * s := by
  unfold coldRefreshRadius
  have hn0 : (0 : Real) ≤ n := by positivity
  rw [mul_pow, mul_pow, Real.sq_sqrt hn0, Real.sq_sqrt hs.le]
  ring

theorem hotRefreshRadius_pos : 0 < hotRefreshRadius := by
  norm_num [hotRefreshRadius]

theorem hotRefreshRadius_lt_standardShrink (hn : 1 ≤ n) :
    hotRefreshRadius < 1 - 1 / (2 * (n : Real)) := by
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  calc
    hotRefreshRadius = 1 / 4 := by rfl
    _ < 1 / 2 := by norm_num
    _ ≤ 1 - 1 / (2 * (n : Real)) := by linarith

/-- Every positive-radius Gaussian ball refresh is a probability law. -/
theorem isProbabilityMeasure_gaussianBallRefresh
    {s rho : Real} (hs : 0 < s) (hrho : 0 < rho) :
    IsProbabilityMeasure (coldBallStart (n := n) s rho) :=
  isProbabilityMeasure_coldBallStart hs hrho

/-- General finite-volume refresh theorem.  A Gaussian ball supported strictly inside
`c K` is warm for the speedy Gaussian target, at the exact Gaussian normalizer ratio.
This works at arbitrary variance and is the hot-phase fallback used below. -/
theorem isWarm_gaussianBallRefresh_ellGaussianProb
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hKtop : volume K ≠ ⊤)
    {s rho c delta : Real} (hs : 0 < s) (hrho : 0 < rho)
    (hc0 : 0 < c) (hc1 : c < 1) (hrhoc : rho < c)
    (hdelta : 0 < delta) (hdeltac : delta ≤ 1 - c) :
    IsWarm (gaussianBallWarmFactor K s rho)
      (coldBallStart (n := n) s rho) (ellGaussianProb K delta s) := by
  let nu : Measure (State n) := gaussianBase n s
  let B : Set (State n) := closedBall (0 : State n) rho
  have hBm : MeasurableSet B := measurableSet_closedBall
  have hBKc : B ⊆ c • K := by
    exact closedBall_subset_smul_set_of_lt hball hrho.le hrhoc
  have h0K : (0 : State n) ∈ K := hball (mem_ball_self one_pos)
  have hcK : c • K ⊆ K :=
    smul_subset_of_convex hKc h0K hc0.le hc1.le
  have hBK : B ⊆ K := hBKc.trans hcK
  have hBvol0 : volume B ≠ 0 :=
    (measure_closedBall_pos volume (0 : State n) hrho).ne'
  have hnuB0 : nu B ≠ 0 := by
    dsimp only [nu, gaussianBase]
    exact withDensity_gaussianWeight_ne_zero s hBvol0
  have hnuK0 : nu K ≠ 0 := by
    exact (lt_of_lt_of_le (pos_iff_ne_zero.2 hnuB0) (measure_mono hBK)).ne'
  have hnuKtop : nu K ≠ ⊤ := by
    dsimp only [nu, gaussianBase]
    exact withDensity_gaussianWeight_ne_top hs hK hKtop
  have hwarmGaussian : IsWarm (nu K / nu B)
      (Arlib.uniformOn nu B) (Arlib.uniformOn nu K) :=
    isWarm_uniformOn_subset_ratio nu hBm hK hBK hnuK0 hnuKtop
  have hsupp : coldBallStart (n := n) s rho ((c • K)ᶜ) = 0 := by
    exact measure_mono_null (compl_subset_compl.mpr hBKc)
      (coldBallStart_compl_eq_zero s rho)
  apply isWarm_ellGaussianProb_of_supported_on_shrunken hK hKc hball
    hc0 hc1 hdelta hdeltac hsupp
  simpa only [coldBallStart, gaussianBallWarmFactor, gaussianBase, nu, B] using
    hwarmGaussian

/-- The exact refresh warmth constant is genuinely finite. -/
theorem gaussianBallWarmFactor_ne_top
    {K : Set (State n)} (hK : MeasurableSet K) (hKtop : volume K ≠ ⊤)
    {s rho : Real} (hs : 0 < s) (hrho : 0 < rho) :
    gaussianBallWarmFactor K s rho ≠ ⊤ := by
  apply ENNReal.div_ne_top
  · unfold gaussianBase
    exact withDensity_gaussianWeight_ne_top hs hK hKtop
  · unfold gaussianBase
    exact withDensity_gaussianWeight_ne_zero s
      (measure_closedBall_pos volume (0 : State n) hrho).ne'

/-- Cold specialization: the phase-scaled refresh is exactly `2`-warm whenever it fits
inside the standard shrunken body. -/
theorem isWarm_coldRefresh_ellGaussianProb
    (hn : 1 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    {s c delta : Real} (hs : 0 < s) (hc0 : 0 < c) (hc1 : c < 1)
    (hfit : coldRefreshRadius n s < c)
    (hdelta : 0 < delta) (hdeltac : delta ≤ 1 - c) :
    IsWarm (ENNReal.ofReal 2)
      (coldBallStart (n := n) s (coldRefreshRadius n s))
      (ellGaussianProb K delta s) := by
  apply isWarm_coldBallStart_ellGaussianProb hK hKc hball hn hc0 hc1
    (coldRefreshRadius_pos hn hs) hfit hs
  · rw [coldRefreshRadius_sq hn hs]
  · exact hdelta
  · exact hdeltac

/-- Hot specialization: a fixed, directly samplable inner Gaussian ball works at every
positive variance.  Its constant is explicit and finite, though necessarily not
dimension-free on arbitrary bodies. -/
theorem isWarm_hotRefresh_ellGaussianProb
    (hn : 1 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (hKtop : volume K ≠ ⊤) {s delta : Real} (hs : 0 < s)
    (hdelta : 0 < delta) (hdeltan : delta ≤ 1 / (2 * (n : Real))) :
    IsWarm (gaussianBallWarmFactor K s hotRefreshRadius)
      (coldBallStart (n := n) s hotRefreshRadius)
      (ellGaussianProb K delta s) := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hnR : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hc0 : 0 < c := by
    have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
    have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    dsimp only [c]
    linarith
  have hc1 : c < 1 := by
    dsimp only [c]
    have : 0 < 1 / (2 * (n : Real)) := by positivity
    linarith
  apply isWarm_gaussianBallRefresh_ellGaussianProb hK hKc hball hKtop hs
    hotRefreshRadius_pos hc0 hc1
  · exact hotRefreshRadius_lt_standardShrink hn
  · exact hdelta
  · simpa only [c, sub_sub_cancel] using hdeltan

theorem hotRefreshWarmFactor_ne_top
    {K : Set (State n)} (hK : MeasurableSet K) (hKtop : volume K ≠ ⊤)
    {s : Real} (hs : 0 < s) :
    gaussianBallWarmFactor K s hotRefreshRadius ≠ ⊤ :=
  gaussianBallWarmFactor_ne_top hK hKtop hs hotRefreshRadius_pos

/-- Quantitative radial control of the hot normalizer ratio.  The numerator is bounded
by the volume of the moment-truncated body, and the denominator by the minimum Gaussian
weight on the radius-`1/4` ball. -/
theorem hotRefreshWarmFactor_le_envelope
    {K : Set (State n)} (hK : MeasurableSet K)
    {R s : Real} (hs : 0 < s)
    (hKR : K ⊆ closedBall (0 : State n) R) :
    gaussianBallWarmFactor K s hotRefreshRadius ≤
      hotRefreshWarmEnvelope n R s := by
  let rho : Real := hotRefreshRadius
  let R1 : Real := max 1 R
  let alpha : ENNReal := ENNReal.ofReal (Real.exp (-(rho ^ 2) / (2 * s)))
  let scale : ENNReal := ENNReal.ofReal ((4 * R1) ^ n)
  let B : Set (State n) := closedBall (0 : State n) rho
  let nu : Measure (State n) := gaussianBase n s
  have hrho : rho = 1 / 4 := rfl
  have hrho0 : 0 < rho := by simpa only [rho] using hotRefreshRadius_pos
  have hR10 : 0 ≤ R1 := by dsimp only [R1]; exact le_trans (by norm_num) (le_max_left 1 R)
  have hRle : R ≤ R1 := le_max_right 1 R
  have hKsub : K ⊆ closedBall (0 : State n) R1 := by
    exact hKR.trans (closedBall_subset_closedBall hRle)
  have halpha0 : alpha ≠ 0 := by
    dsimp only [alpha]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have halphatop : alpha ≠ ⊤ := ENNReal.ofReal_ne_top
  have hBvol0 : volume B ≠ 0 := by
    exact (measure_closedBall_pos volume (0 : State n) hrho0).ne'
  have hBvoltop : volume B ≠ ⊤ := measure_closedBall_lt_top.ne
  have hden0 : nu B ≠ 0 := by
    dsimp only [nu, gaussianBase, B]
    exact withDensity_gaussianWeight_ne_zero s hBvol0
  have hdentop : nu B ≠ ⊤ := by
    dsimp only [nu, gaussianBase, B]
    exact withDensity_gaussianWeight_ne_top hs measurableSet_closedBall
      measure_closedBall_lt_top.ne
  have hnum : nu K ≤ volume K := by
    dsimp only [nu, gaussianBase]
    rw [withDensity_apply _ hK]
    calc
      (∫⁻ x in K, gaussianWeight s x ∂volume) ≤ ∫⁻ _ in K, (1 : ENNReal) ∂volume :=
        lintegral_mono fun x ↦ gaussianWeight_le_one hs x
      _ = volume K := by rw [setLIntegral_one]
  have hvolScale : volume (closedBall (0 : State n) R1) = scale * volume B := by
    rw [Measure.addHaar_closedBall volume 0 hR10,
      Measure.addHaar_closedBall volume 0 hrho0.le,
      finrank_euclideanSpace_fin]
    dsimp only [scale, B]
    rw [hrho]
    have hcoeff : ENNReal.ofReal (R1 ^ n) =
        ENNReal.ofReal ((4 * R1) ^ n) * ENNReal.ofReal ((1 / 4 : Real) ^ n) := by
      rw [← ENNReal.ofReal_mul
        (pow_nonneg (mul_nonneg (by norm_num) hR10) n)]
      congr 1
      rw [← mul_pow]
      ring
    rw [hcoeff, mul_assoc]
  have hnumScale : nu K ≤ scale * volume B := by
    exact hnum.trans ((measure_mono hKsub).trans_eq hvolScale)
  have hdenLower : alpha * volume B ≤ nu B := by
    dsimp only [nu, gaussianBase]
    rw [withDensity_apply _ measurableSet_closedBall]
    calc
      alpha * volume B = ∫⁻ _ in B, alpha ∂volume := by rw [setLIntegral_const]
      _ ≤ ∫⁻ x in B, gaussianWeight s x ∂volume := by
        apply setLIntegral_mono (measurable_gaussianWeight s)
        intro x hx
        apply ofReal_exp_le_gaussianWeight hs
        rw [← mem_closedBall_zero_iff]
        simpa only [B]
  rw [gaussianBallWarmFactor, show gaussianBase n s K = nu K by rfl,
    show gaussianBase n s (closedBall (0 : State n) hotRefreshRadius) = nu B by rfl,
    ENNReal.div_le_iff hden0 hdentop]
  change nu K ≤ (alpha⁻¹ * scale) * nu B
  calc
    nu K ≤ scale * volume B := hnumScale
    _ = (alpha⁻¹ * scale) * (alpha * volume B) := by
      rw [show (alpha⁻¹ * scale) * (alpha * volume B) =
          (alpha⁻¹ * alpha) * (scale * volume B) by ac_rfl,
        ENNReal.inv_mul_cancel halpha0 halphatop, one_mul]
    _ ≤ (alpha⁻¹ * scale) * nu B := mul_le_mul_left' hdenLower _

/-- The real logarithm of the explicit hot envelope has the advertised radial-log
shape.  The statement keeps the harmless `max 1 R` and inverse-variance terms visible. -/
theorem log_hotRefreshWarmEnvelope_toReal
    (n : Nat) {R s : Real} (hs : 0 < s) :
    Real.log (hotRefreshWarmEnvelope n R s).toReal =
      (hotRefreshRadius ^ 2) / (2 * s) +
        (n : Real) * Real.log (4 * max 1 R) := by
  have hR : 0 < 4 * max 1 R := by
    have : (0 : Real) < max 1 R := lt_of_lt_of_le one_pos (le_max_left 1 R)
    positivity
  have ha : 0 < Real.exp (-(hotRefreshRadius ^ 2) / (2 * s)) := Real.exp_pos _
  unfold hotRefreshWarmEnvelope
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal ha.le,
    ENNReal.toReal_ofReal (pow_nonneg hR.le n), Real.log_mul (by positivity) (by positivity),
    Real.log_inv, Real.log_exp, Real.log_pow]
  ring

/-- In the hot block the variance is at least one, so the inverse-variance part of the
refresh logarithm is a universal `1/32`. -/
theorem log_hotRefreshWarmEnvelope_toReal_le_of_one_le
    (n : Nat) {R s : Real} (hs : 1 ≤ s) :
    Real.log (hotRefreshWarmEnvelope n R s).toReal ≤
      1 / 32 + (n : Real) * Real.log (4 * max 1 R) := by
  have hs0 : 0 < s := one_pos.trans_le hs
  rw [log_hotRefreshWarmEnvelope_toReal n hs0]
  have hinv : 1 / s ≤ 1 := (div_le_one hs0).2 hs
  have hrho : hotRefreshRadius ^ 2 = (1 / 16 : Real) := by
    norm_num [hotRefreshRadius]
  rw [hrho]
  have : (1 / 16 : Real) / (2 * s) ≤ 1 / 32 := by
    calc
      (1 / 16 : Real) / (2 * s) = (1 / 32) * (1 / s) := by ring
      _ ≤ (1 / 32) * 1 := mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = 1 / 32 := mul_one _
  linarith

#print axioms isWarm_gaussianBallRefresh_ellGaussianProb
#print axioms hotRefreshWarmEnvelope_toReal_pos
#print axioms gaussianBallWarmFactor_ne_top
#print axioms isWarm_coldRefresh_ellGaussianProb
#print axioms isWarm_hotRefresh_ellGaussianProb
#print axioms hotRefreshWarmFactor_le_envelope
#print axioms log_hotRefreshWarmEnvelope_toReal
#print axioms log_hotRefreshWarmEnvelope_toReal_le_of_one_le

end Ttc.CVIndependentRefreshSeedLaws
