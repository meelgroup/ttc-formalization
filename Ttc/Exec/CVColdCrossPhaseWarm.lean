import Ttc.Exec.CVColdOperationalKernel
import Arlib.Convexity.GaussianCooling.ScaledRawWarm
import Arlib.MarkovChains.Continuous.ColdTruncationRelative
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Cross-phase warmth for the changing radius-four cold bodies

The operational cold kernel at phase `i` walks on

`K i = K ∩ closedBall 0 (4 * sqrt (fixedSigmaSq n s0 i) * sqrt n)`.

This makes support bookkeeping essential.  A full-body cooling reference, scaled by the
source shrink, need not be supported on `K (i+1)` and therefore cannot be warm (with any
constant) for the next truncated speedy law.  The first theorem below records this exact
obstruction.

The radius-four bodies themselves are nested along the fixed schedule.  Consequently a
*truncated* predecessor reference has the required support after scaling.  The final theorem
reduces its cross-phase speedy warmth to the sole remaining analytic comparison: warmth for
the next Gaussian cooling law on the enlarged radius-four body.  No TV approximation can
replace this comparison, since TV closeness does not imply warmness.
-/

set_option autoImplicit false

namespace Ttc.CVColdCrossPhaseWarm

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open Ttc.CVCorrectedFixedBlockCost
open Ttc.CVSourceTruncatedFixedCost
open Ttc.CVGaussianScoreSeedPhaseKernel
open scoped ENNReal Pointwise

variable {n m : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-! ## A generic changing-body normalization lemma -/

/-- Conditioning the same base measure on a measurable subset is warm for conditioning on
the larger set, at the exact normalizer ratio.  This is the weighted analogue of the usual
volume-ratio warm start. -/
theorem isWarm_uniformOn_subset_ratio
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {A B : Set Omega} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ⊆ B) (hB0 : mu B ≠ 0) (hBtop : mu B ≠ ⊤) :
    IsWarm (mu B / mu A) (Arlib.uniformOn mu A) (Arlib.uniformOn mu B) := by
  intro S hS
  rw [Arlib.uniformOn_apply mu hA hS, Arlib.uniformOn_apply mu hB hS]
  have hcancel : mu B / mu A * (mu (S ∩ B) / mu B) =
      mu (S ∩ B) / mu A := by
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    have hreorder : mu B * (mu A)⁻¹ * (mu (S ∩ B) * (mu B)⁻¹) =
        (mu B * (mu B)⁻¹) * (mu (S ∩ B) * (mu A)⁻¹) := by
      ac_rfl
    rw [hreorder, ENNReal.mul_inv_cancel hB0 hBtop, one_mul]
  rw [hcancel]
  exact ENNReal.div_le_div_right
    (measure_mono (Set.inter_subset_inter_right S hAB)) _

/-- A bound on the weighted normalizer ratio gives the corresponding changing-body
warmness constant. -/
theorem isWarm_uniformOn_subset_of_ratio_le
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {A B : Set Omega} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ⊆ B) (hB0 : mu B ≠ 0) (hBtop : mu B ≠ ⊤)
    {C : ENNReal} (hratio : mu B / mu A ≤ C) :
    IsWarm C (Arlib.uniformOn mu A) (Arlib.uniformOn mu B) :=
  (isWarm_uniformOn_subset_ratio mu hA hB hAB hB0 hBtop).mono hratio

/-- The relative radius-two Gaussian tail constant is already below one half in every
positive dimension. -/
theorem relativeTwoTail_le_half (hn : 1 ≤ n) :
    ENNReal.ofReal ((2 * Real.exp (-(3 : Real) / 2)) ^ n) ≤
      ENNReal.ofReal (1 / 2 : Real) := by
  have hexp4 : (4 : Real) ≤ Real.exp (3 / 2) := by
    have h := Real.sum_le_exp_of_nonneg (x := (3 / 2 : Real)) (by norm_num) 4
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hprod : Real.exp (-(3 : Real) / 2) * Real.exp (3 / 2) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hbase : 2 * Real.exp (-(3 : Real) / 2) ≤ 1 / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hexp4
      (Real.exp_pos (-(3 : Real) / 2)).le
    nlinarith
  have hbase0 : 0 ≤ 2 * Real.exp (-(3 : Real) / 2) := by positivity
  have hbase1 : 2 * Real.exp (-(3 : Real) / 2) ≤ 1 := hbase.trans (by norm_num)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  apply ENNReal.ofReal_le_ofReal
  rw [pow_succ]
  have hpow : (2 * Real.exp (-(3 : Real) / 2)) ^ k ≤ 1 :=
    pow_le_one₀ hbase0 hbase1
  nlinarith [pow_nonneg hbase0 k]

/-- Any warm law for a radius-four speedy target must be supported on that radius-four
body.  In particular, positive outside mass is an absolute obstruction, not merely a loss
in the warmth constant. -/
theorem not_isWarm_ellGaussianProb_fixedRadiusFour_of_outside_mass
    {K : Set (State n)} (hK : MeasurableSet K) {s delta : Real}
    {mu : Measure (State n)} {M : ENNReal}
    (hout : mu (fixedRadiusFourBody K s)ᶜ ≠ 0) :
    ¬ IsWarm M mu
      (ellGaussianProb (fixedRadiusFourBody K s) delta s) := by
  intro hwarm
  have hzero := ellGaussianProb_compl_eq_zero
    (measurableSet_fixedRadiusFourBody hK s) delta s
  have hle := hwarm (fixedRadiusFourBody K s)ᶜ
    (measurableSet_fixedRadiusFourBody hK s).compl
  rw [hzero, mul_zero] at hle
  exact hout (nonpos_iff_eq_zero.mp hle)

/-- Exact score/seed form of the support obstruction.  This applies directly to the
currently declared full-body predecessor reference. -/
theorem not_isWarm_scoreSeedReference_fixedRadiusFour_of_outside_mass
    (hn : 1 ≤ n) {sigmaSq : Nat → Real} {K : Set (State n)}
    (hK : MeasurableSet K) {i : Nat} {s delta : Real} {M : ENNReal}
    (hout :
      Measure.map
        (fun x : State n ↦ (1 - 1 / (2 * (n : Real))) • x)
        (coolLaw m sigmaSq K i) (fixedRadiusFourBody K s)ᶜ ≠ 0) :
    ¬ IsWarm M
      (Measure.map Prod.snd
        (scoreSeedReference (1 - 1 / (2 * (n : Real)))
          (coolLaw m sigmaSq K i)))
      (ellGaussianProb (fixedRadiusFourBody K s) delta s) := by
  rw [map_snd_scoreSeedReference]
  exact not_isWarm_ellGaussianProb_fixedRadiusFour_of_outside_mass hK hout

/-- Fixed-rate variances increase at each step. -/
theorem fixedSigmaSq_le_succ
    (hn : 1 ≤ n) {s0 : Real} (hs0 : 0 < s0) (i : Nat) :
    fixedSigmaSq n s0 i ≤ fixedSigmaSq n s0 (i + 1) := by
  have hnR : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  rw [fixedSigmaSq, fixedSigmaSq, geomSchedule_succ]
  have hs : 0 < geomSchedule s0 (1 / (n : Real)) i :=
    geomSchedule_pos hs0 (by positivity) i
  nlinarith [div_nonneg (by norm_num : (0 : Real) ≤ 1) hnR.le]

/-- The source radius-four bodies are nested along the fixed schedule. -/
theorem fixedRadiusFourBody_subset_succ
    (hn : 1 ≤ n) {K : Set (State n)} {s0 : Real} (hs0 : 0 < s0)
    (i : Nat) :
    fixedRadiusFourBody K (fixedSigmaSq n s0 i) ⊆
      fixedRadiusFourBody K (fixedSigmaSq n s0 (i + 1)) := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  rw [mem_closedBall_zero_iff]
  have hsle := fixedSigmaSq_le_succ hn hs0 i
  have hsqrt : Real.sqrt (fixedSigmaSq n s0 i) ≤
      Real.sqrt (fixedSigmaSq n s0 (i + 1)) := Real.sqrt_le_sqrt hsle
  have hnroot : 0 ≤ Real.sqrt (n : Real) := Real.sqrt_nonneg _
  exact (mem_closedBall_zero_iff.mp hx.2).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) hnroot)

/-- Scaling a truncated predecessor by the standard source shrink leaves it inside the
scaled next radius-four body. -/
theorem standardShrink_smul_fixedRadiusFourBody_subset_succ
    (hn : 1 ≤ n) {K : Set (State n)} {s0 : Real} (hs0 : 0 < s0)
    (i : Nat) :
    (1 - 1 / (2 * (n : Real))) •
        fixedRadiusFourBody K (fixedSigmaSq n s0 i) ⊆
      (1 - 1 / (2 * (n : Real))) •
        fixedRadiusFourBody K (fixedSigmaSq n s0 (i + 1)) := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact ⟨x, fixedRadiusFourBody_subset_succ hn hs0 i hx, rfl⟩

/-- The scaled truncated cooling reference has exactly the support required by the next
radius-four speedy bridge. -/
theorem map_standardShrink_coolLaw_fixedRadiusFour_compl_eq_zero
    (hn : 1 ≤ n) {s0 : Real} (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    {i : Nat} (hi : i < m)
    (hrad : 1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n) :
    Measure.map
        (fun x : State n ↦ (1 - 1 / (2 * (n : Real))) • x)
        (coolLaw m (fixedSigmaSq n s0)
          (fixedRadiusFourBody K (fixedSigmaSq n s0 i)) i)
        (((1 - 1 / (2 * (n : Real))) •
          fixedRadiusFourBody K (fixedSigmaSq n s0 (i + 1)))ᶜ) = 0 := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  let Ki : Set (State n) := fixedRadiusFourBody K (fixedSigmaSq n s0 i)
  let Kinext : Set (State n) := fixedRadiusFourBody K (fixedSigmaSq n s0 (i + 1))
  have hnR : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hc0 : 0 < c := by
    dsimp [c]
    have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
    have : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hsigma : ∀ j, 0 < fixedSigmaSq n s0 j := by
    intro j
    unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) j
  have hKim : MeasurableSet Ki := measurableSet_fixedRadiusFourBody hK _
  have hKiball : ball (0 : State n) 1 ⊆ Ki :=
    unitBall_subset_inter_closedBall hball hrad
  have hKifin : volume Ki ≠ ⊤ := volume_inter_closedBall_ne_top K _
  have hsmall : c • Ki ⊆ c • Kinext := by
    simpa only [c, Ki, Kinext] using
      standardShrink_smul_fixedRadiusFourBody_subset_succ hn hs0 i
  have hsource : Measure.map (fun x : State n ↦ c • x)
      (coolLaw m (fixedSigmaSq n s0) Ki i) (c • Ki)ᶜ = 0 := by
    rw [map_smul_coolLaw_eq_condOn hsigma hKim hKiball hKifin hi hc0,
      Arlib.condOn_apply _ MeasurableSet.univ
        (measurableSet_smul_set hKim hc0.ne').compl,
      inter_univ]
    have hempty : (c • Ki)ᶜ ∩ c • Ki = (∅ : Set (State n)) := compl_inter_self _
    rw [withDensity_apply _ (measurableSet_smul_set hKim hc0.ne').compl,
      Measure.restrict_restrict (measurableSet_smul_set hKim hc0.ne').compl,
      hempty, Measure.restrict_empty]
    simp
  exact MeasureTheory.measure_mono_null (compl_subset_compl.mpr hsmall) hsource

/-- Exact Gaussian changing-body step.  The fixed variance update costs `sqrt(e)`; changing
from the old radius-four body to the new one costs exactly the ratio of their Gaussian
normalizers at the new variance. -/
theorem isWarm_coolLaw_fixedRadiusFour_succ_of_normalizer_ratio
    (hn : 1 ≤ n) {s0 : Real} (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K)
    {i : Nat} (hi : i + 1 < m)
    (hrad : 1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n) :
    let Ki := fixedRadiusFourBody K (fixedSigmaSq n s0 i)
    let Kinext := fixedRadiusFourBody K (fixedSigmaSq n s0 (i + 1))
    let gaussianNext : Measure (State n) :=
      volume.withDensity (gaussianWeight (fixedSigmaSq n s0 (i + 1)))
    IsWarm
      (ENNReal.ofReal (Real.exp (1 / 2)) * (gaussianNext Kinext / gaussianNext Ki))
      (coolLaw m (fixedSigmaSq n s0) Ki i)
      (coolLaw m (fixedSigmaSq n s0) Kinext (i + 1)) := by
  dsimp only
  let Ki : Set (State n) := fixedRadiusFourBody K (fixedSigmaSq n s0 i)
  let Kinext : Set (State n) := fixedRadiusFourBody K (fixedSigmaSq n s0 (i + 1))
  let gaussianNext : Measure (State n) :=
    volume.withDensity (gaussianWeight (fixedSigmaSq n s0 (i + 1)))
  have hsigma : ∀ j, 0 < fixedSigmaSq n s0 j := by
    intro j
    unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) j
  have hAm : MeasurableSet Ki := measurableSet_fixedRadiusFourBody hK _
  have hBm : MeasurableSet Kinext := measurableSet_fixedRadiusFourBody hK _
  have hAc : Convex Real Ki := convex_fixedRadiusFourBody hKc _
  have hAfin : volume Ki ≠ ⊤ := volume_inter_closedBall_ne_top K _
  have hBfin : volume Kinext ≠ ⊤ := volume_inter_closedBall_ne_top K _
  have hAball : ball (0 : State n) 1 ⊆ Ki :=
    unitBall_subset_inter_closedBall hball hrad
  have hradnext : 1 ≤
      4 * Real.sqrt (fixedSigmaSq n s0 (i + 1)) * Real.sqrt n := by
    calc
      1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n := hrad
      _ ≤ 4 * Real.sqrt (fixedSigmaSq n s0 (i + 1)) * Real.sqrt n := by
        have hsqrt := Real.sqrt_le_sqrt (fixedSigmaSq_le_succ hn hs0 i)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) (Real.sqrt_nonneg _)
  have hBball : ball (0 : State n) 1 ⊆ Kinext :=
    unitBall_subset_inter_closedBall hball hradnext
  have hAB : Ki ⊆ Kinext := fixedRadiusFourBody_subset_succ hn hs0 i
  have hsched : fixedSigmaSq n s0 (i + 1) =
      (1 + 1 / (n : Real)) * fixedSigmaSq n s0 i := by
    rw [fixedSigmaSq, fixedSigmaSq, geomSchedule_succ]
    ring
  have hphase : IsWarm (ENNReal.ofReal (Real.exp (1 / 2)))
      (coolLaw m (fixedSigmaSq n s0) Ki i)
      (coolLaw m (fixedSigmaSq n s0) Ki (i + 1)) :=
    isWarm_coolLaw_succ_sqrt_exp hi hAm hAfin hAc hAball hsigma hsched
  have hB0 : gaussianNext Kinext ≠ 0 := by
    dsimp only [gaussianNext]
    rw [withDensity_apply _ hBm]
    exact (lintegral_gaussianWeight_pos (hsigma (i + 1)) one_pos hBball).ne'
  have hBtop : gaussianNext Kinext ≠ ⊤ := by
    dsimp only [gaussianNext]
    rw [withDensity_apply _ hBm]
    exact lintegral_gaussianWeight_ne_top (hsigma (i + 1)) hBfin
  have hbody : IsWarm (gaussianNext Kinext / gaussianNext Ki)
      (coolLaw m (fixedSigmaSq n s0) Ki (i + 1))
      (coolLaw m (fixedSigmaSq n s0) Kinext (i + 1)) := by
    rw [coolLaw_eq_uniformOn_gaussianWeight hsigma hAm hAball hAfin hi,
      coolLaw_eq_uniformOn_gaussianWeight hsigma hBm hBball hBfin hi]
    exact isWarm_uniformOn_subset_ratio gaussianNext hAm hBm hAB hB0 hBtop
  exact hphase.trans hbody

/-- The changing radius-four body costs at most a factor two in Gaussian normalization.
The proof uses the relative radius-two tail at the *next* variance; that radius-two body
is contained in the previous radius-four body because the fixed variance ratio is at most
two. -/
theorem gaussianNext_fullBody_fixedRadiusFour_ratio_le_two
    (hn : 1 ≤ n) {s0 : Real} (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat}
    (hradTwo : 1 ≤
      2 * Real.sqrt (fixedSigmaSq n s0 (i + 1)) * Real.sqrt n) :
    let Ki := fixedRadiusFourBody K (fixedSigmaSq n s0 i)
    let gaussianNext : Measure (State n) :=
      volume.withDensity (gaussianWeight (fixedSigmaSq n s0 (i + 1)))
    gaussianNext K / gaussianNext Ki ≤ 2 := by
  dsimp only
  let sold : Real := fixedSigmaSq n s0 i
  let snext : Real := fixedSigmaSq n s0 (i + 1)
  let sigma : Real := Real.sqrt snext
  let Ki : Set (State n) := fixedRadiusFourBody K sold
  let Kinext : Set (State n) := fixedRadiusFourBody K snext
  let A2 : Set (State n) := K ∩ closedBall 0 (2 * sigma * Real.sqrt n)
  let gaussianNext : Measure (State n) :=
    volume.withDensity (gaussianWeight snext)
  have hnR : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hsold : 0 < sold := by
    dsimp [sold, fixedSigmaSq]
    exact geomSchedule_pos hs0 (by positivity) i
  have hsnext : 0 < snext := by
    dsimp [snext, fixedSigmaSq]
    exact geomSchedule_pos hs0 (by positivity) (i + 1)
  have hsigma : 0 < sigma := Real.sqrt_pos.2 hsnext
  have hsigmaSq : sigma ^ 2 = snext := Real.sq_sqrt hsnext.le
  have hsched : snext = sold * (1 + 1 / (n : Real)) := by
    dsimp [snext, sold, fixedSigmaSq]
    exact geomSchedule_succ s0 (1 / (n : Real)) i
  have hratioVar : snext ≤ 2 * sold := by
    have hinv : 1 / (n : Real) ≤ 1 := by
      rw [div_le_one hnR]
      exact_mod_cast hn
    rw [hsched]
    nlinarith
  have hsqrtOld : Real.sqrt sold ^ 2 = sold := Real.sq_sqrt hsold.le
  have hradius : 2 * sigma ≤ 4 * Real.sqrt sold := by
    have hs0r : 0 ≤ Real.sqrt sold := Real.sqrt_nonneg _
    have hsig0 : 0 ≤ sigma := Real.sqrt_nonneg _
    nlinarith
  have hA2A : A2 ⊆ Ki := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    rw [mem_closedBall_zero_iff]
    exact (mem_closedBall_zero_iff.mp hx.2).trans
      (mul_le_mul_of_nonneg_right hradius (Real.sqrt_nonneg _))
  have hAB : Ki ⊆ Kinext := fixedRadiusFourBody_subset_succ hn hs0 i
  have hA2m : MeasurableSet A2 := by
    exact hK.inter measurableSet_closedBall
  have hKim : MeasurableSet Ki := measurableSet_fixedRadiusFourBody hK _
  have hBim : MeasurableSet Kinext := measurableSet_fixedRadiusFourBody hK _
  have h0K : (0 : State n) ∈ K := hball (mem_ball_self one_pos)
  have htailInt := lintegral_gaussianWeight_sdiff_le_relative
    hn hsigma hK hKc h0K
  have htail : gaussianNext (K \ A2) ≤
      ENNReal.ofReal ((2 * Real.exp (-(3 : Real) / 2)) ^ n) * gaussianNext K := by
    dsimp only [gaussianNext, A2, sigma] at htailInt ⊢
    rw [withDensity_apply _ (hK.diff (hK.inter measurableSet_closedBall)),
      withDensity_apply _ hK, Set.sdiff_self_inter]
    have hsqrtNext : Real.sqrt snext ^ 2 = snext := Real.sq_sqrt hsnext.le
    simpa only [hsqrtNext] using htailInt
  have htailHalf : gaussianNext (K \ A2) ≤
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
  have hhalfReal : (ENNReal.ofReal (1 / 2 : Real) * gaussianNext K).toReal =
      (1 / 2 : Real) * (gaussianNext K).toReal := by simp
  have hhalftop : ENNReal.ofReal (1 / 2 : Real) * gaussianNext K ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKtop
  have htailReal : (gaussianNext (K \ A2)).toReal ≤
      (1 / 2 : Real) * (gaussianNext K).toReal := by
    have := ENNReal.toReal_mono hhalftop htailHalf
    simpa only [hhalfReal] using this
  have haddReal := congrArg ENNReal.toReal hadd
  rw [ENNReal.toReal_add hA2top htailtop] at haddReal
  have hKleA2Real : (gaussianNext K).toReal ≤
      2 * (gaussianNext A2).toReal := by linarith
  have htwoAtop : 2 * gaussianNext A2 ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num) hA2top
  have hKleA2 : gaussianNext K ≤ 2 * gaussianNext A2 :=
    (ENNReal.toReal_le_toReal hKtop htwoAtop).mp (by
      simpa using hKleA2Real)
  have hK_le_twoA : gaussianNext K ≤ 2 * gaussianNext Ki := by
    calc
      gaussianNext K ≤ 2 * gaussianNext A2 := hKleA2
      _ ≤ 2 * gaussianNext Ki :=
        mul_le_mul_left' (measure_mono hA2A) 2
  have hA0 : gaussianNext Ki ≠ 0 := by
    have hballKi : ball (0 : State n) 1 ⊆ Ki := by
      exact unitBall_subset_inter_closedBall hball
        (le_trans hradTwo (by
          have hradle : 2 * Real.sqrt snext ≤ 4 * Real.sqrt sold := by
            simpa only [sigma] using hradius
          exact mul_le_mul_of_nonneg_right hradle (Real.sqrt_nonneg _)))
    dsimp only [gaussianNext]
    rw [withDensity_apply _ hKim]
    exact (lintegral_gaussianWeight_pos hsnext one_pos hballKi).ne'
  have hAtop : gaussianNext Ki ≠ ⊤ :=
    ne_top_of_le_ne_top hKtop (measure_mono inter_subset_left)
  rw [ENNReal.div_le_iff hA0 hAtop]
  simpa [mul_comm] using hK_le_twoA

/-- The same factor-two normalizer bound for the next radius-four body, by monotonicity
from the stronger full-body statement. -/
theorem gaussianNext_fixedRadiusFour_ratio_le_two
    (hn : 1 ≤ n) {s0 : Real} (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat}
    (hradTwo : 1 ≤
      2 * Real.sqrt (fixedSigmaSq n s0 (i + 1)) * Real.sqrt n) :
    let Ki := fixedRadiusFourBody K (fixedSigmaSq n s0 i)
    let Kinext := fixedRadiusFourBody K (fixedSigmaSq n s0 (i + 1))
    let gaussianNext : Measure (State n) :=
      volume.withDensity (gaussianWeight (fixedSigmaSq n s0 (i + 1)))
    gaussianNext Kinext / gaussianNext Ki ≤ 2 := by
  dsimp only
  let gaussianNext : Measure (State n) :=
    volume.withDensity (gaussianWeight (fixedSigmaSq n s0 (i + 1)))
  calc
    gaussianNext (fixedRadiusFourBody K (fixedSigmaSq n s0 (i + 1))) /
        gaussianNext (fixedRadiusFourBody K (fixedSigmaSq n s0 i)) ≤
      gaussianNext K /
        gaussianNext (fixedRadiusFourBody K (fixedSigmaSq n s0 i)) := by
      exact ENNReal.div_le_div_right (measure_mono inter_subset_left) _
    _ ≤ 2 := gaussianNext_fullBody_fixedRadiusFour_ratio_le_two
      hn hs0 hK hKc hball hfin hradTwo

/-- The scaled truncated predecessor is warm for the next truncated cooling law with
an entirely explicit constant.  The three factors are respectively the shrink Jacobian,
the fixed-variance cooling step, and the changing radius-four normalizer. -/
theorem isWarm_standardScaledTruncated_coolLaw_succ
    (hn : 1 ≤ n) {s0 : Real} (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m)
    (hrad : 1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hradTwo : 1 ≤
      2 * Real.sqrt (fixedSigmaSq n s0 (i + 1)) * Real.sqrt n) :
    let c : Real := 1 - 1 / (2 * (n : Real))
    IsWarm
      (ENNReal.ofReal ((c⁻¹) ^ n) *
        (ENNReal.ofReal (Real.exp (1 / 2)) * 2))
      (Measure.map (fun x : State n ↦ c • x)
        (coolLaw m (fixedSigmaSq n s0)
          (fixedRadiusFourBody K (fixedSigmaSq n s0 i)) i))
      (coolLaw m (fixedSigmaSq n s0)
        (fixedRadiusFourBody K (fixedSigmaSq n s0 (i + 1))) (i + 1)) := by
  dsimp only
  let c : Real := 1 - 1 / (2 * (n : Real))
  let Ki : Set (State n) := fixedRadiusFourBody K (fixedSigmaSq n s0 i)
  let Kinext : Set (State n) := fixedRadiusFourBody K (fixedSigmaSq n s0 (i + 1))
  let gaussianNext : Measure (State n) :=
    volume.withDensity (gaussianWeight (fixedSigmaSq n s0 (i + 1)))
  have hsigma : ∀ j, 0 < fixedSigmaSq n s0 j := by
    intro j
    unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) j
  have hnR : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hc0 : 0 < c := by
    dsimp [c]
    have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
    have : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hc1 : c ≤ 1 := by
    dsimp [c]
    have : 0 ≤ 1 / (2 * (n : Real)) := by positivity
    linarith
  have hKim : MeasurableSet Ki := measurableSet_fixedRadiusFourBody hK _
  have hKic : Convex Real Ki := convex_fixedRadiusFourBody hKc _
  have hKiball : ball (0 : State n) 1 ⊆ Ki :=
    unitBall_subset_inter_closedBall hball hrad
  have hKifin : volume Ki ≠ ⊤ := volume_inter_closedBall_ne_top K _
  have hself : IsWarm (ENNReal.ofReal ((c⁻¹) ^ n))
      (Measure.map (fun x : State n ↦ c • x)
        (coolLaw m (fixedSigmaSq n s0) Ki i))
      (coolLaw m (fixedSigmaSq n s0) Ki i) :=
    isWarm_map_smul_coolLaw_self hsigma hKim hKic hKiball hKifin
      (Nat.lt_of_succ_lt hi) hc0 hc1
  have hstep := isWarm_coolLaw_fixedRadiusFour_succ_of_normalizer_ratio
    (m := m) hn hs0 hK hKc hball hi hrad
  have hratio : gaussianNext Kinext / gaussianNext Ki ≤ 2 := by
    simpa only [gaussianNext, Ki, Kinext] using
      (gaussianNext_fixedRadiusFour_ratio_le_two
        (K := K) hn hs0 hK hKc hball hfin (i := i) hradTwo)
  have hstep' : IsWarm (ENNReal.ofReal (Real.exp (1 / 2)) * 2)
      (coolLaw m (fixedSigmaSq n s0) Ki i)
      (coolLaw m (fixedSigmaSq n s0) Kinext (i + 1)) := by
    apply hstep.mono
    exact mul_le_mul_left' hratio _
  simpa only [c, Ki, Kinext] using hself.trans hstep'

/-- Correct cross-phase reduction for the changing cold bodies.  Once the scaled
truncated predecessor is warm for the next *Gaussian cooling law*, support transport to
the next speedy stationary law is free.  This is the exact analytic premise still needed
for a constant-warm operational cold recurrence. -/
theorem isWarm_standardScaledTruncated_ellGaussianProb_succ_of_coolLaw
    (hn : 1 ≤ n) {s0 : Real} (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K)
    {i : Nat} (hi : i + 1 < m)
    (hrad : 1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta ≤ 1 / (2 * (n : Real))) {M : ENNReal}
    (hgauss : IsWarm M
      (Measure.map
        (fun x : State n ↦ (1 - 1 / (2 * (n : Real))) • x)
        (coolLaw m (fixedSigmaSq n s0)
          (fixedRadiusFourBody K (fixedSigmaSq n s0 i)) i))
      (coolLaw m (fixedSigmaSq n s0)
        (fixedRadiusFourBody K (fixedSigmaSq n s0 (i + 1))) (i + 1))) :
    IsWarm M
      (Measure.map
        (fun x : State n ↦ (1 - 1 / (2 * (n : Real))) • x)
        (coolLaw m (fixedSigmaSq n s0)
          (fixedRadiusFourBody K (fixedSigmaSq n s0 i)) i))
      (ellGaussianProb
        (fixedRadiusFourBody K (fixedSigmaSq n s0 (i + 1))) delta
        (fixedSigmaSq n s0 (i + 1))) := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  let Kinext : Set (State n) := fixedRadiusFourBody K (fixedSigmaSq n s0 (i + 1))
  have hnR : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hc0 : 0 < c := by
    dsimp [c]
    have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
    have : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hc1 : c < 1 := by
    dsimp [c]
    have : 0 < 1 / (2 * (n : Real)) := by positivity
    linarith
  have hdc : delta ≤ 1 - c := by simpa [c] using hdeltan
  have hsigma : ∀ j, 0 < fixedSigmaSq n s0 j := by
    intro j
    unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) j
  have hnextRad : 1 ≤
      4 * Real.sqrt (fixedSigmaSq n s0 (i + 1)) * Real.sqrt n := by
    calc
      1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n := hrad
      _ ≤ 4 * Real.sqrt (fixedSigmaSq n s0 (i + 1)) * Real.sqrt n := by
        gcongr
        exact fixedSigmaSq_le_succ hn hs0 i
  have hnextm : MeasurableSet Kinext := measurableSet_fixedRadiusFourBody hK _
  have hnextc : Convex Real Kinext := convex_fixedRadiusFourBody hKc _
  have hnextball : ball (0 : State n) 1 ⊆ Kinext :=
    unitBall_subset_inter_closedBall hball hnextRad
  have hnextfin : volume Kinext ≠ ⊤ := volume_inter_closedBall_ne_top K _
  have hsupp := map_standardShrink_coolLaw_fixedRadiusFour_compl_eq_zero
    (m := m) hn hs0 hK hKc hball (Nat.lt_of_succ_lt hi) hrad
  rw [coolLaw_eq_uniformOn_gaussianWeight hsigma hnextm hnextball hnextfin hi]
    at hgauss
  exact isWarm_ellGaussianProb_of_supported_on_shrunken hnextm hnextc hnextball
    hc0 hc1 hdelta hdc (by simpa only [c, Kinext] using hsupp) hgauss

/-- Fully explicit cold cross-phase speedy warmness.  Unlike the old full-body reference,
this theorem is support-correct for the changing radius-four bodies. -/
theorem isWarm_standardScaledTruncated_ellGaussianProb_succ
    (hn : 1 ≤ n) {s0 : Real} (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m)
    (hrad : 1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hradTwo : 1 ≤
      2 * Real.sqrt (fixedSigmaSq n s0 (i + 1)) * Real.sqrt n)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta ≤ 1 / (2 * (n : Real))) :
    let c : Real := 1 - 1 / (2 * (n : Real))
    IsWarm
      (ENNReal.ofReal ((c⁻¹) ^ n) *
        (ENNReal.ofReal (Real.exp (1 / 2)) * 2))
      (Measure.map (fun x : State n ↦ c • x)
        (coolLaw m (fixedSigmaSq n s0)
          (fixedRadiusFourBody K (fixedSigmaSq n s0 i)) i))
      (ellGaussianProb
        (fixedRadiusFourBody K (fixedSigmaSq n s0 (i + 1))) delta
        (fixedSigmaSq n s0 (i + 1))) := by
  dsimp only
  apply isWarm_standardScaledTruncated_ellGaussianProb_succ_of_coolLaw
    (m := m) hn hs0 hK hKc hball hi hrad hdelta hdeltan
  exact isWarm_standardScaledTruncated_coolLaw_succ
    (m := m) hn hs0 hK hKc hball hfin hi hrad hradTwo

/-! ## The cold-to-hot boundary -/

/-- At the boundary, the same truncated predecessor is warm for the next full-body
Gaussian cooling law.  The stronger full-body normalizer theorem above keeps the body
change at factor two. -/
theorem isWarm_standardScaledTruncated_fullCoolLaw_succ
    (hn : 1 ≤ n) {s0 : Real} (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m)
    (hrad : 1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hradTwo : 1 ≤
      2 * Real.sqrt (fixedSigmaSq n s0 (i + 1)) * Real.sqrt n) :
    let c : Real := 1 - 1 / (2 * (n : Real))
    IsWarm
      (ENNReal.ofReal ((c⁻¹) ^ n) *
        (ENNReal.ofReal (Real.exp (1 / 2)) * 2))
      (Measure.map (fun x : State n ↦ c • x)
        (coolLaw m (fixedSigmaSq n s0)
          (fixedRadiusFourBody K (fixedSigmaSq n s0 i)) i))
      (coolLaw m (fixedSigmaSq n s0) K (i + 1)) := by
  dsimp only
  let c : Real := 1 - 1 / (2 * (n : Real))
  let Ki : Set (State n) := fixedRadiusFourBody K (fixedSigmaSq n s0 i)
  let gaussianNext : Measure (State n) :=
    volume.withDensity (gaussianWeight (fixedSigmaSq n s0 (i + 1)))
  have hsigma : ∀ j, 0 < fixedSigmaSq n s0 j := by
    intro j
    unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) j
  have hnR : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hc0 : 0 < c := by
    dsimp [c]
    have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
    have : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hc1 : c ≤ 1 := by
    dsimp [c]
    have : 0 ≤ 1 / (2 * (n : Real)) := by positivity
    linarith
  have hKim : MeasurableSet Ki := measurableSet_fixedRadiusFourBody hK _
  have hKic : Convex Real Ki := convex_fixedRadiusFourBody hKc _
  have hKiball : ball (0 : State n) 1 ⊆ Ki :=
    unitBall_subset_inter_closedBall hball hrad
  have hKifin : volume Ki ≠ ⊤ := volume_inter_closedBall_ne_top K _
  have hself : IsWarm (ENNReal.ofReal ((c⁻¹) ^ n))
      (Measure.map (fun x : State n ↦ c • x)
        (coolLaw m (fixedSigmaSq n s0) Ki i))
      (coolLaw m (fixedSigmaSq n s0) Ki i) :=
    isWarm_map_smul_coolLaw_self hsigma hKim hKic hKiball hKifin
      (Nat.lt_of_succ_lt hi) hc0 hc1
  have hsched : fixedSigmaSq n s0 (i + 1) =
      (1 + 1 / (n : Real)) * fixedSigmaSq n s0 i := by
    rw [fixedSigmaSq, fixedSigmaSq, geomSchedule_succ]
    ring
  have hphase : IsWarm (ENNReal.ofReal (Real.exp (1 / 2)))
      (coolLaw m (fixedSigmaSq n s0) Ki i)
      (coolLaw m (fixedSigmaSq n s0) Ki (i + 1)) :=
    isWarm_coolLaw_succ_sqrt_exp hi hKim hKifin hKic hKiball hsigma hsched
  have hbaseK0 : gaussianNext K ≠ 0 := by
    dsimp only [gaussianNext]
    rw [withDensity_apply _ hK]
    exact (lintegral_gaussianWeight_pos (hsigma (i + 1)) one_pos hball).ne'
  have hbaseKtop : gaussianNext K ≠ ⊤ := by
    dsimp only [gaussianNext]
    rw [withDensity_apply _ hK]
    exact lintegral_gaussianWeight_ne_top (hsigma (i + 1)) hfin
  have hbody : IsWarm (gaussianNext K / gaussianNext Ki)
      (coolLaw m (fixedSigmaSq n s0) Ki (i + 1))
      (coolLaw m (fixedSigmaSq n s0) K (i + 1)) := by
    rw [coolLaw_eq_uniformOn_gaussianWeight hsigma hKim hKiball hKifin hi,
      coolLaw_eq_uniformOn_gaussianWeight hsigma hK hball hfin hi]
    exact isWarm_uniformOn_subset_ratio gaussianNext hKim hK inter_subset_left
      hbaseK0 hbaseKtop
  have hratio : gaussianNext K / gaussianNext Ki ≤ 2 := by
    simpa only [gaussianNext, Ki] using
      (gaussianNext_fullBody_fixedRadiusFour_ratio_le_two
        (K := K) hn hs0 hK hKc hball hfin (i := i) hradTwo)
  have hstep : IsWarm (ENNReal.ofReal (Real.exp (1 / 2)) * 2)
      (coolLaw m (fixedSigmaSq n s0) Ki i)
      (coolLaw m (fixedSigmaSq n s0) K (i + 1)) := by
    exact (hphase.trans hbody).mono (mul_le_mul_left' hratio _)
  simpa only [c, Ki] using hself.trans hstep

/-- Final cold-to-hot boundary theorem: the scaled final truncated cold reference is
explicitly warm for the first full-body hot speedy target. -/
theorem isWarm_standardScaledTruncated_full_ellGaussianProb_succ
    (hn : 1 ≤ n) {s0 : Real} (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m)
    (hrad : 1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hradTwo : 1 ≤
      2 * Real.sqrt (fixedSigmaSq n s0 (i + 1)) * Real.sqrt n)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta ≤ 1 / (2 * (n : Real))) :
    let c : Real := 1 - 1 / (2 * (n : Real))
    IsWarm
      (ENNReal.ofReal ((c⁻¹) ^ n) *
        (ENNReal.ofReal (Real.exp (1 / 2)) * 2))
      (Measure.map (fun x : State n ↦ c • x)
        (coolLaw m (fixedSigmaSq n s0)
          (fixedRadiusFourBody K (fixedSigmaSq n s0 i)) i))
      (ellGaussianProb K delta (fixedSigmaSq n s0 (i + 1))) := by
  dsimp only
  let c : Real := 1 - 1 / (2 * (n : Real))
  let Ki : Set (State n) := fixedRadiusFourBody K (fixedSigmaSq n s0 i)
  let Kinext : Set (State n) := fixedRadiusFourBody K (fixedSigmaSq n s0 (i + 1))
  have hnR : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hc0 : 0 < c := by
    dsimp [c]
    have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
    have : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hc1 : c < 1 := by
    dsimp [c]
    have : 0 < 1 / (2 * (n : Real)) := by positivity
    linarith
  have hdc : delta ≤ 1 - c := by simpa [c] using hdeltan
  have hsigma : ∀ j, 0 < fixedSigmaSq n s0 j := by
    intro j
    unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) j
  have hsuppNext := map_standardShrink_coolLaw_fixedRadiusFour_compl_eq_zero
    (m := m) hn hs0 hK hKc hball (Nat.lt_of_succ_lt hi) hrad
  have hscaled : c • Kinext ⊆ c • K := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, hx.1, rfl⟩
  have hsupp : Measure.map (fun x : State n ↦ c • x)
      (coolLaw m (fixedSigmaSq n s0) Ki i) (c • K)ᶜ = 0 := by
    exact measure_mono_null (compl_subset_compl.mpr hscaled)
      (by simpa only [c, Ki, Kinext] using hsuppNext)
  have hgauss := isWarm_standardScaledTruncated_fullCoolLaw_succ
    (m := m) hn hs0 hK hKc hball hfin hi hrad hradTwo
  rw [coolLaw_eq_uniformOn_gaussianWeight hsigma hK hball hfin hi] at hgauss
  exact isWarm_ellGaussianProb_of_supported_on_shrunken hK hKc hball
    hc0 hc1 hdelta hdc hsupp (by simpa only [c, Ki] using hgauss)

#print axioms not_isWarm_ellGaussianProb_fixedRadiusFour_of_outside_mass
#print axioms not_isWarm_scoreSeedReference_fixedRadiusFour_of_outside_mass
#print axioms fixedRadiusFourBody_subset_succ
#print axioms map_standardShrink_coolLaw_fixedRadiusFour_compl_eq_zero
#print axioms isWarm_standardScaledTruncated_coolLaw_succ
#print axioms isWarm_standardScaledTruncated_ellGaussianProb_succ_of_coolLaw
#print axioms isWarm_standardScaledTruncated_ellGaussianProb_succ
#print axioms isWarm_standardScaledTruncated_fullCoolLaw_succ
#print axioms isWarm_standardScaledTruncated_full_ellGaussianProb_succ

end Ttc.CVColdCrossPhaseWarm
