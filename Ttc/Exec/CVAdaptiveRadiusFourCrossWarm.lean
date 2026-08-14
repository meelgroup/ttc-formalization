import Ttc.Exec.CVColdCrossPhaseWarm
import Ttc.Volume.CVHybridVarianceBudget

/-!
# Radius-four cross-phase warmth for an arbitrary cooling rate

This is the changing-body analogue of the accelerated full-body bridge.  It is stated
directly in terms of two positive variances, so it applies to both pieces of the hybrid
schedule.  The only rate hypothesis used by the radius-four tail argument is
`snext <= 2 * sold`; in particular every adaptive rate at most `1/2` is covered.
-/

set_option autoImplicit false

namespace Ttc.CVAdaptiveRadiusFourCrossWarm

open MeasureTheory ProbabilityTheory Metric Set Pointwise
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVColdCrossPhaseWarm
open Ttc.CVSourceTruncatedFixedCost
open Ttc.CVHybridSchedule
open scoped ENNReal Classical

variable {n m : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

theorem fixedRadiusFourBody_subset_of_le {K : Set (State n)}
    {sold snext : Real} (hs : sold <= snext) :
    fixedRadiusFourBody K sold ⊆ fixedRadiusFourBody K snext := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  rw [mem_closedBall_zero_iff]
  have hsqrt : Real.sqrt sold <= Real.sqrt snext := Real.sqrt_le_sqrt hs
  exact (mem_closedBall_zero_iff.mp hx.2).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) (Real.sqrt_nonneg _))

theorem standardShrink_smul_fixedRadiusFourBody_subset_of_le
    (hn : 1 <= n) {K : Set (State n)} {sold snext : Real}
    (hs : sold <= snext) :
    (1 - 1 / (2 * (n : Real))) • fixedRadiusFourBody K sold ⊆
      (1 - 1 / (2 * (n : Real))) • fixedRadiusFourBody K snext := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact ⟨x, fixedRadiusFourBody_subset_of_le hs hx, rfl⟩

/-- At the new variance, the old radius-four body retains at least half of the full
Gaussian mass whenever the variance grows by at most a factor two. -/
theorem gaussianNext_fullBody_radiusFour_ratio_le_two
    (hn : 1 <= n) {sold snext : Real} (hsold : 0 < sold) (hsnext : 0 < snext)
    (hratio : snext <= 2 * sold)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hradTwo : 1 <= 2 * Real.sqrt snext * Real.sqrt n) :
    let Ki := fixedRadiusFourBody K sold
    let gaussianNext : Measure (State n) :=
      volume.withDensity (gaussianWeight snext)
    gaussianNext K / gaussianNext Ki <= 2 := by
  dsimp only
  let sigma : Real := Real.sqrt snext
  let Ki : Set (State n) := fixedRadiusFourBody K sold
  let A2 : Set (State n) := K ∩ closedBall 0 (2 * sigma * Real.sqrt n)
  let gaussianNext : Measure (State n) := volume.withDensity (gaussianWeight snext)
  have hsigma : 0 < sigma := Real.sqrt_pos.2 hsnext
  have hsigmaSq : sigma ^ 2 = snext := Real.sq_sqrt hsnext.le
  have hsqrtOld : Real.sqrt sold ^ 2 = sold := Real.sq_sqrt hsold.le
  have hradius : 2 * sigma <= 4 * Real.sqrt sold := by
    have hs0r : 0 <= Real.sqrt sold := Real.sqrt_nonneg _
    have hsig0 : 0 <= sigma := Real.sqrt_nonneg _
    nlinarith
  have hA2A : A2 ⊆ Ki := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    rw [mem_closedBall_zero_iff]
    exact (mem_closedBall_zero_iff.mp hx.2).trans
      (mul_le_mul_of_nonneg_right hradius (Real.sqrt_nonneg _))
  have hA2m : MeasurableSet A2 := hK.inter measurableSet_closedBall
  have hKim : MeasurableSet Ki := measurableSet_fixedRadiusFourBody hK _
  have h0K : (0 : State n) ∈ K := hball (mem_ball_self one_pos)
  have htailInt := lintegral_gaussianWeight_sdiff_le_relative
    hn hsigma hK hKc h0K
  have htail : gaussianNext (K \ A2) <=
      ENNReal.ofReal ((2 * Real.exp (-(3 : Real) / 2)) ^ n) * gaussianNext K := by
    dsimp only [gaussianNext, A2, sigma] at htailInt ⊢
    rw [withDensity_apply _ (hK.diff (hK.inter measurableSet_closedBall)),
      withDensity_apply _ hK, Set.sdiff_self_inter]
    rw [hsigmaSq] at htailInt
    simpa only using htailInt
  have htailHalf : gaussianNext (K \ A2) <=
      ENNReal.ofReal (1 / 2 : Real) * gaussianNext K :=
    htail.trans (mul_le_mul_right' (relativeTwoTail_le_half hn) _)
  have hA2K : A2 ⊆ K := inter_subset_left
  have hadd : gaussianNext A2 + gaussianNext (K \ A2) = gaussianNext K := by
    have h := measure_inter_add_sdiff (μ := gaussianNext) K hA2m
    rw [inter_eq_self_of_subset_right hA2K] at h
    exact h
  have hKtop : gaussianNext K ≠ ⊤ := by
    dsimp only [gaussianNext]
    rw [withDensity_apply _ hK]
    exact lintegral_gaussianWeight_ne_top hsnext hfin
  have hA2top : gaussianNext A2 ≠ ⊤ :=
    ne_top_of_le_ne_top hKtop (measure_mono hA2K)
  have htailtop : gaussianNext (K \ A2) ≠ ⊤ :=
    ne_top_of_le_ne_top hKtop (measure_mono diff_subset)
  have htailReal : (gaussianNext (K \ A2)).toReal <=
      (1 / 2 : Real) * (gaussianNext K).toReal := by
    have hhalftop : ENNReal.ofReal (1 / 2 : Real) * gaussianNext K ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKtop
    have h := ENNReal.toReal_mono hhalftop htailHalf
    simpa using h
  have haddReal := congrArg ENNReal.toReal hadd
  rw [ENNReal.toReal_add hA2top htailtop] at haddReal
  have hKleA2Real : (gaussianNext K).toReal <=
      2 * (gaussianNext A2).toReal := by linarith
  have htwoAtop : 2 * gaussianNext A2 ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hA2top
  have hKleA2 : gaussianNext K <= 2 * gaussianNext A2 :=
    (ENNReal.toReal_le_toReal hKtop htwoAtop).mp (by simpa using hKleA2Real)
  have hK_le_twoA : gaussianNext K <= 2 * gaussianNext Ki := by
    calc
      gaussianNext K <= 2 * gaussianNext A2 := hKleA2
      _ <= 2 * gaussianNext Ki := mul_le_mul_left' (measure_mono hA2A) 2
  have hA0 : gaussianNext Ki ≠ 0 := by
    have hballKi : ball (0 : State n) 1 ⊆ Ki := by
      exact unitBall_subset_inter_closedBall hball
        (le_trans hradTwo (mul_le_mul_of_nonneg_right hradius (Real.sqrt_nonneg _)))
    dsimp only [gaussianNext]
    rw [withDensity_apply _ hKim]
    exact (lintegral_gaussianWeight_pos hsnext one_pos hballKi).ne'
  have hAtop : gaussianNext Ki ≠ ⊤ :=
    ne_top_of_le_ne_top hKtop (measure_mono inter_subset_left)
  rw [ENNReal.div_le_iff hA0 hAtop]
  simpa [mul_comm] using hK_le_twoA

theorem gaussianNext_radiusFour_ratio_le_two
    (hn : 1 <= n) {sold snext : Real} (hsold : 0 < sold) (hsnext : 0 < snext)
    (hsle : sold <= snext) (hratio : snext <= 2 * sold)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hradTwo : 1 <= 2 * Real.sqrt snext * Real.sqrt n) :
    let Ki := fixedRadiusFourBody K sold
    let Kj := fixedRadiusFourBody K snext
    let gaussianNext : Measure (State n) := volume.withDensity (gaussianWeight snext)
    gaussianNext Kj / gaussianNext Ki <= 2 := by
  dsimp only
  let gaussianNext : Measure (State n) := volume.withDensity (gaussianWeight snext)
  calc
    gaussianNext (fixedRadiusFourBody K snext) /
        gaussianNext (fixedRadiusFourBody K sold) <=
      gaussianNext K / gaussianNext (fixedRadiusFourBody K sold) :=
        ENNReal.div_le_div_right (measure_mono inter_subset_left) _
    _ <= 2 := gaussianNext_fullBody_radiusFour_ratio_le_two hn hsold hsnext
      hratio hK hKc hball hfin hradTwo

/-- Warmness factor for an expanding radius-four body.  The factors are: at most two
for the standard shrink Jacobian, `(sqrt cc)^n` for cooling, and two for the expanding
body normalizer.  Its logarithm is `O(n)` when `cc <= 3/2`. -/
noncomputable def adaptiveRadiusFourWarmFactor (n : Nat) (cc : Real) : ENNReal :=
  ENNReal.ofReal (4 * Real.sqrt cc ^ n)

theorem map_standardShrink_coolLaw_radiusFour_compl_eq_zero
    (hn : 1 <= n) {sigmaSq : Nat -> Real} (hsigma : forall j, 0 < sigmaSq j)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K)
    {i : Nat} (hi : i < m) (hsle : sigmaSq i <= sigmaSq (i + 1))
    (hrad : 1 <= 4 * Real.sqrt (sigmaSq i) * Real.sqrt n) :
    Measure.map (fun x : State n => (1 - 1 / (2 * (n : Real))) • x)
        (coolLaw m sigmaSq (fixedRadiusFourBody K (sigmaSq i)) i)
        (((1 - 1 / (2 * (n : Real))) •
          fixedRadiusFourBody K (sigmaSq (i + 1)))ᶜ) = 0 := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  let Ki : Set (State n) := fixedRadiusFourBody K (sigmaSq i)
  let Kj : Set (State n) := fixedRadiusFourBody K (sigmaSq (i + 1))
  have hc0 : 0 < c := by
    dsimp [c]
    have hnR : (1 : Real) <= n := by exact_mod_cast hn
    have : 1 / (2 * (n : Real)) <= 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hKim : MeasurableSet Ki := measurableSet_fixedRadiusFourBody hK _
  have hKiball : ball (0 : State n) 1 ⊆ Ki :=
    unitBall_subset_inter_closedBall hball hrad
  have hKifin : volume Ki ≠ ⊤ := volume_inter_closedBall_ne_top K _
  have hsmall : c • Ki ⊆ c • Kj := by
    simpa only [c, Ki, Kj] using
      standardShrink_smul_fixedRadiusFourBody_subset_of_le hn hsle
  have hsource : Measure.map (fun x : State n => c • x)
      (coolLaw m sigmaSq Ki i) (c • Ki)ᶜ = 0 := by
    rw [map_smul_coolLaw_eq_condOn hsigma hKim hKiball hKifin hi hc0,
      Arlib.condOn_apply _ MeasurableSet.univ
        (measurableSet_smul_set hKim hc0.ne').compl,
      inter_univ]
    have hempty : (c • Ki)ᶜ ∩ c • Ki = (∅ : Set (State n)) := compl_inter_self _
    rw [withDensity_apply _ (measurableSet_smul_set hKim hc0.ne').compl,
      Measure.restrict_restrict (measurableSet_smul_set hKim hc0.ne').compl,
      hempty, Measure.restrict_empty]
    simp
  exact measure_mono_null (compl_subset_compl.mpr hsmall) hsource

theorem isWarm_standardScaledTruncated_coolLaw_ratio
    (hn : 1 <= n) {sigmaSq : Nat -> Real} (hsigma : forall j, 0 < sigmaSq j)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m) {cc : Real} (hcc1 : 1 <= cc)
    (hsched : sigmaSq (i + 1) = cc * sigmaSq i)
    (hcc2 : cc <= 2)
    (hrad : 1 <= 4 * Real.sqrt (sigmaSq i) * Real.sqrt n)
    (hradTwo : 1 <= 2 * Real.sqrt (sigmaSq (i + 1)) * Real.sqrt n) :
    IsWarm (adaptiveRadiusFourWarmFactor n cc)
      (Measure.map (fun x : State n => (1 - 1 / (2 * (n : Real))) • x)
        (coolLaw m sigmaSq (fixedRadiusFourBody K (sigmaSq i)) i))
      (coolLaw m sigmaSq (fixedRadiusFourBody K (sigmaSq (i + 1))) (i + 1)) := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  let Ki : Set (State n) := fixedRadiusFourBody K (sigmaSq i)
  let Kj : Set (State n) := fixedRadiusFourBody K (sigmaSq (i + 1))
  let gaussianNext : Measure (State n) :=
    volume.withDensity (gaussianWeight (sigmaSq (i + 1)))
  have hc0 : 0 < c := by
    dsimp [c]
    have hnR : (1 : Real) <= n := by exact_mod_cast hn
    have : 1 / (2 * (n : Real)) <= 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hc1 : c <= 1 := by
    dsimp [c]
    have : 0 <= 1 / (2 * (n : Real)) := by positivity
    linarith
  have hsle : sigmaSq i <= sigmaSq (i + 1) := by
    rw [hsched]
    nlinarith [hsigma i]
  have hratio : sigmaSq (i + 1) <= 2 * sigmaSq i := by
    rw [hsched]
    nlinarith [hsigma i]
  have hKim : MeasurableSet Ki := measurableSet_fixedRadiusFourBody hK _
  have hKjm : MeasurableSet Kj := measurableSet_fixedRadiusFourBody hK _
  have hKic : Convex Real Ki := convex_fixedRadiusFourBody hKc _
  have hKiball : ball (0 : State n) 1 ⊆ Ki :=
    unitBall_subset_inter_closedBall hball hrad
  have hKjball : ball (0 : State n) 1 ⊆ Kj :=
    unitBall_subset_inter_closedBall hball (by
      exact hrad.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsle) (by norm_num))
        (Real.sqrt_nonneg _)))
  have hKifin : volume Ki ≠ ⊤ := volume_inter_closedBall_ne_top K _
  have hKjfin : volume Kj ≠ ⊤ := volume_inter_closedBall_ne_top K _
  have hself : IsWarm (ENNReal.ofReal ((c⁻¹) ^ n))
      (Measure.map (fun x : State n => c • x) (coolLaw m sigmaSq Ki i))
      (coolLaw m sigmaSq Ki i) :=
    isWarm_map_smul_coolLaw_self hsigma hKim hKic hKiball hKifin
      (Nat.lt_of_succ_lt hi) hc0 hc1
  have hphase : IsWarm (ENNReal.ofReal (Real.sqrt cc ^ n))
      (coolLaw m sigmaSq Ki i) (coolLaw m sigmaSq Ki (i + 1)) :=
    isWarm_coolLaw_succ_of_ratio hi hKim hKifin hKic hKiball hsigma hcc1 hsched
  have hKj0 : gaussianNext Kj ≠ 0 := by
    dsimp only [gaussianNext]
    rw [withDensity_apply _ hKjm]
    exact (lintegral_gaussianWeight_pos (hsigma (i + 1)) one_pos hKjball).ne'
  have hKjtop : gaussianNext Kj ≠ ⊤ := by
    dsimp only [gaussianNext]
    rw [withDensity_apply _ hKjm]
    exact lintegral_gaussianWeight_ne_top (hsigma (i + 1)) hKjfin
  have hbody : IsWarm (gaussianNext Kj / gaussianNext Ki)
      (coolLaw m sigmaSq Ki (i + 1)) (coolLaw m sigmaSq Kj (i + 1)) := by
    rw [coolLaw_eq_uniformOn_gaussianWeight hsigma hKim hKiball hKifin hi,
      coolLaw_eq_uniformOn_gaussianWeight hsigma hKjm hKjball hKjfin hi]
    exact isWarm_uniformOn_subset_ratio gaussianNext hKim hKjm
      (fixedRadiusFourBody_subset_of_le hsle) hKj0 hKjtop
  have hbodyRatio : gaussianNext Kj / gaussianNext Ki <= 2 := by
    simpa only [gaussianNext, Ki, Kj] using
      gaussianNext_radiusFour_ratio_le_two hn (hsigma i) (hsigma (i + 1))
        hsle hratio hK hKc hball hfin hradTwo
  have hall := hself.trans (hphase.trans (hbody.mono hbodyRatio))
  apply hall.mono
  have hcpow : (1 / 2 : Real) <= c ^ n := by
    dsimp [c]
    exact half_le_one_sub_inv_two_mul_pow hn
  have hcinv : (c⁻¹) ^ n <= 2 := by
    rw [inv_pow]
    exact (inv_le_comm₀ (pow_pos hc0 n) (by norm_num : (0 : Real) < 2)).2 (by
      norm_num
      exact hcpow)
  have hsqrt0 : 0 <= Real.sqrt cc ^ n := pow_nonneg (Real.sqrt_nonneg _) _
  rw [adaptiveRadiusFourWarmFactor]
  calc
    ENNReal.ofReal ((c⁻¹) ^ n) *
        (ENNReal.ofReal (Real.sqrt cc ^ n) * 2) <=
      ENNReal.ofReal 2 * (ENNReal.ofReal (Real.sqrt cc ^ n) * 2) :=
        mul_le_mul_right' (ENNReal.ofReal_le_ofReal hcinv) _
    _ = ENNReal.ofReal (4 * Real.sqrt cc ^ n) := by
      rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num,
        ← ENNReal.ofReal_mul hsqrt0,
        ← ENNReal.ofReal_mul (by norm_num : (0 : Real) <= 2)]
      congr 1
      ring

theorem isWarm_standardScaledTruncated_ellGaussianProb_ratio
    (hn : 1 <= n) {sigmaSq : Nat -> Real} (hsigma : forall j, 0 < sigmaSq j)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m) {cc : Real} (hcc1 : 1 <= cc)
    (hsched : sigmaSq (i + 1) = cc * sigmaSq i) (hcc2 : cc <= 2)
    (hrad : 1 <= 4 * Real.sqrt (sigmaSq i) * Real.sqrt n)
    (hradTwo : 1 <= 2 * Real.sqrt (sigmaSq (i + 1)) * Real.sqrt n)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta <= 1 / (2 * (n : Real))) :
    IsWarm (adaptiveRadiusFourWarmFactor n cc)
      (Measure.map (fun x : State n => (1 - 1 / (2 * (n : Real))) • x)
        (coolLaw m sigmaSq (fixedRadiusFourBody K (sigmaSq i)) i))
      (ellGaussianProb (fixedRadiusFourBody K (sigmaSq (i + 1))) delta
        (sigmaSq (i + 1))) := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  let Kj : Set (State n) := fixedRadiusFourBody K (sigmaSq (i + 1))
  have hc0 : 0 < c := by
    dsimp [c]
    have hnR : (1 : Real) <= n := by exact_mod_cast hn
    have : 1 / (2 * (n : Real)) <= 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hc1 : c < 1 := by
    dsimp [c]
    have : 0 < 1 / (2 * (n : Real)) := by positivity
    linarith
  have hsle : sigmaSq i <= sigmaSq (i + 1) := by
    rw [hsched]
    nlinarith [hsigma i]
  have hKjm : MeasurableSet Kj := measurableSet_fixedRadiusFourBody hK _
  have hKjc : Convex Real Kj := convex_fixedRadiusFourBody hKc _
  have hKjball : ball (0 : State n) 1 ⊆ Kj :=
    unitBall_subset_inter_closedBall hball (by
      exact hrad.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsle) (by norm_num))
        (Real.sqrt_nonneg _)))
  have hsupp := map_standardShrink_coolLaw_radiusFour_compl_eq_zero
    (m := m) hn hsigma hK hKc hball (Nat.lt_of_succ_lt hi) hsle hrad
  have hgauss := isWarm_standardScaledTruncated_coolLaw_ratio
    (m := m) hn hsigma hK hKc hball hfin hi hcc1 hsched hcc2 hrad hradTwo
  rw [coolLaw_eq_uniformOn_gaussianWeight hsigma hKjm hKjball
    (volume_inter_closedBall_ne_top K _) hi] at hgauss
  exact isWarm_ellGaussianProb_of_supported_on_shrunken hKjm hKjc hKjball
    hc0 hc1 hdelta (by simpa [c] using hdeltan)
    (by simpa only [c, Kj] using hsupp) (by simpa only [c, Kj] using hgauss)

/-- The hybrid variance grows monotonically and by at most a factor `3/2` whenever
the phase-rate hypothesis is available. -/
theorem hybrid_sigmaSq_step_bounds
    (hn : 1 <= n) {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0) (i : Nat)
    (hrate0 : 0 <= phaseRate n N s0 i)
    (hrateHalf : phaseRate n N s0 i <= 1 / 2) :
    sigmaSq n N s0 i <= sigmaSq n N s0 (i + 1) ∧
      sigmaSq n N s0 (i + 1) <= 2 * sigmaSq n N s0 i := by
  have hs := sigmaSq_pos hn hN hs0 i
  rw [sigmaSq_succ hn hN hs0 i]
  constructor <;> nlinarith

theorem adaptiveRadiusFourWarmFactor_le_pow_two
    {cc : Real} (hcc1 : 1 <= cc) (hcc32 : cc <= 3 / 2) :
    adaptiveRadiusFourWarmFactor n cc <=
      ENNReal.ofReal ((2 : Real) ^ (n + 2)) := by
  have hsqrt : Real.sqrt cc <= 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by nlinarith⟩
  have hpow : Real.sqrt cc ^ n <= (2 : Real) ^ n :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt n
  rw [adaptiveRadiusFourWarmFactor]
  apply ENNReal.ofReal_le_ofReal
  rw [pow_add, pow_two]
  nlinarith [pow_nonneg (show (0 : Real) <= 2 by norm_num) n]

/-- Direct hybrid-schedule specialization.  This is the source-sharp radius-four bridge
needed by the operational recurrence: the speedy delta is recomputed from the next
variance, rather than capped by the outer radius `R`. -/
theorem isWarm_standardScaledTruncated_ellGaussianProb_hybrid
    (hn : 1 <= n) {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m)
    (hrate0 : 0 <= phaseRate n N s0 i)
    (hrateHalf : phaseRate n N s0 i <= 1 / 2)
    (hrad : 1 <= 4 * Real.sqrt (sigmaSq n N s0 i) * Real.sqrt n)
    (hradTwo : 1 <= 2 * Real.sqrt (sigmaSq n N s0 (i + 1)) * Real.sqrt n) :
    IsWarm (adaptiveRadiusFourWarmFactor n (1 + phaseRate n N s0 i))
      (Measure.map (fun x : State n => (1 - 1 / (2 * (n : Real))) • x)
        (coolLaw m (sigmaSq n N s0)
          (fixedRadiusFourBody K (sigmaSq n N s0 i)) i))
      (ellGaussianProb
        (fixedRadiusFourBody K (sigmaSq n N s0 (i + 1)))
        (fixedRadiusFourDelta n (sigmaSq n N s0 (i + 1)))
        (sigmaSq n N s0 (i + 1))) := by
  have hsigma : forall j, 0 < sigmaSq n N s0 j := sigmaSq_pos hn hN hs0
  have hsched : sigmaSq n N s0 (i + 1) =
      (1 + phaseRate n N s0 i) * sigmaSq n N s0 i := by
    rw [sigmaSq_succ hn hN hs0 i]
    ring
  apply isWarm_standardScaledTruncated_ellGaussianProb_ratio
    hn hsigma hK hKc hball hfin hi (cc := 1 + phaseRate n N s0 i)
    (by linarith) hsched (by linarith) hrad hradTwo
  · exact fixedRadiusFourDelta_pos hn (hsigma (i + 1))
  · exact fixedRadiusFourDelta_le_n

/-- At a terminal variance `N`, a radius-four truncated body equals `K` as soon as the
outer-radius certificate fits inside its truncation radius. -/
theorem fixedRadiusFourBody_eq_of_outer_radius
    {K : Set (State n)} {N R : Real}
    (hKR : K ⊆ closedBall (0 : State n) R)
    (hR : R <= 4 * Real.sqrt N * Real.sqrt n) :
    fixedRadiusFourBody K N = K := by
  apply Set.Subset.antisymm inter_subset_left
  intro x hx
  exact ⟨hx, (hKR hx).trans (by simpa using hR)⟩

#print axioms fixedRadiusFourBody_subset_of_le
#print axioms gaussianNext_fullBody_radiusFour_ratio_le_two
#print axioms gaussianNext_radiusFour_ratio_le_two
#print axioms map_standardShrink_coolLaw_radiusFour_compl_eq_zero
#print axioms isWarm_standardScaledTruncated_coolLaw_ratio
#print axioms isWarm_standardScaledTruncated_ellGaussianProb_ratio
#print axioms adaptiveRadiusFourWarmFactor_le_pow_two
#print axioms isWarm_standardScaledTruncated_ellGaussianProb_hybrid
#print axioms hybrid_sigmaSq_step_bounds
#print axioms fixedRadiusFourBody_eq_of_outer_radius

end Ttc.CVAdaptiveRadiusFourCrossWarm
