import Ttc.Exec.CVAdaptiveRadiusQPrimitives
import Ttc.Exec.CVColdCrossPhaseWarm

/-! Cross-phase warmth for expanding selected-radius bodies. -/

set_option autoImplicit false

namespace Ttc.CVAdaptiveRadiusQCrossWarm

open MeasureTheory ProbabilityTheory Metric Set Pointwise
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVColdCrossPhaseWarm Ttc.CVAdaptiveRadiusQPrimitives
open scoped ENNReal Classical

variable {n m : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- Homothety gives a tail-free normalizer comparison between consecutive expanding
`q`-bodies.  This avoids needing `q ≥ 4`: the extra factor is only `(sqrt cc)^n`.-/
theorem gaussianNext_radiusQ_ratio_le_sqrt_pow
    (hn : 1 ≤ n) {q sold snext cc : Real} (hq : 0 < q)
    (hsold : 0 < sold) (hsnext : 0 < snext)
    (hcc1 : 1 ≤ cc) (hsched : snext = cc * sold)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K)
    (hradOld : 1 ≤ q * Real.sqrt sold * Real.sqrt n) :
    let Ki := radiusQBody q K sold
    let Kj := radiusQBody q K snext
    let gaussianNext : Measure (State n) := volume.withDensity (gaussianWeight snext)
    gaussianNext Kj / gaussianNext Ki ≤
      ENNReal.ofReal (Real.sqrt cc ^ n) := by
  dsimp only
  let Ki := radiusQBody q K sold
  let Kj := radiusQBody q K snext
  let a : Real := (Real.sqrt cc)⁻¹
  let gaussianNext : Measure (State n) := volume.withDensity (gaussianWeight snext)
  have hcc0 : 0 < cc := zero_lt_one.trans_le hcc1
  have hsqrtcc : 0 < Real.sqrt cc := Real.sqrt_pos.2 hcc0
  have ha : 0 < a := inv_pos.mpr hsqrtcc
  have ha1 : a ≤ 1 := by
    dsimp only [a]
    exact (inv_le_one₀ hsqrtcc).2 (Real.one_le_sqrt.mpr hcc1)
  have hsqrtNext : Real.sqrt snext = Real.sqrt cc * Real.sqrt sold := by
    rw [hsched, Real.sqrt_mul hcc0.le]
  have haRadius : a * (q * Real.sqrt snext * Real.sqrt n) =
      q * Real.sqrt sold * Real.sqrt n := by
    rw [hsqrtNext]
    dsimp only [a]
    field_simp [hsqrtcc.ne']
  have h0K : (0 : State n) ∈ K := hball (mem_ball_self one_pos)
  have hscaled : a • Kj ⊆ Ki := by
    rintro y ⟨x, hx, rfl⟩
    change x ∈ K ∩ closedBall 0 (q * Real.sqrt snext * Real.sqrt n) at hx
    change a • x ∈ K ∩ closedBall 0 (q * Real.sqrt sold * Real.sqrt n)
    refine ⟨hKc.smul_mem_of_zero_mem h0K hx.1 ⟨ha.le, ha1⟩, ?_⟩
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    have hxnorm := mem_closedBall_zero_iff.mp hx.2
    calc
      a * ‖x‖ ≤ a * (q * Real.sqrt snext * Real.sqrt n) :=
        mul_le_mul_of_nonneg_left hxnorm ha.le
      _ = q * Real.sqrt sold * Real.sqrt n := haRadius
  have hKim : MeasurableSet Ki := measurableSet_radiusQBody hK
  have hKjm : MeasurableSet Kj := measurableSet_radiusQBody hK
  have hKiball : ball (0 : State n) 1 ⊆ Ki :=
    unitBall_subset_inter_closedBall hball (by simpa only [Ki, radiusQBody] using hradOld)
  have hKi0 : gaussianNext Ki ≠ 0 := by
    dsimp only [gaussianNext]
    rw [withDensity_apply _ hKim]
    exact (lintegral_gaussianWeight_pos hsnext one_pos hKiball).ne'
  have hKitop : gaussianNext Ki ≠ ⊤ := by
    dsimp only [gaussianNext]
    rw [withDensity_apply _ hKim]
    exact lintegral_gaussianWeight_ne_top hsnext
      (volume_inter_closedBall_ne_top K _)
  have hsvar : snext ≤ snext / a ^ 2 := by
    have ha2 : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg a]
    rw [le_div_iff₀ (sq_pos_of_pos ha)]
    nlinarith
  have hmassScaled : ENNReal.ofReal (a ^ n) * gaussianNext Kj ≤
      gaussianNext (a • Kj) := by
    dsimp only [gaussianNext]
    rw [withDensity_apply _ hKjm,
      withDensity_apply _ (measurableSet_smul_set hKjm ha.ne')]
    rw [lintegral_gaussianWeight_smul_set hKjm ha snext]
    gcongr with x
    exact gaussianWeight_mono_variance hsnext hsvar x
  have hmass : ENNReal.ofReal (a ^ n) * gaussianNext Kj ≤ gaussianNext Ki :=
    hmassScaled.trans (measure_mono hscaled)
  rw [ENNReal.div_le_iff hKi0 hKitop]
  have hcancel : ENNReal.ofReal (Real.sqrt cc ^ n) * ENNReal.ofReal (a ^ n) = 1 := by
    rw [← ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg cc) n)]
    have hreal : Real.sqrt cc ^ n * a ^ n = 1 := by
      rw [← mul_pow]
      dsimp only [a]
      rw [mul_inv_cancel₀ hsqrtcc.ne', one_pow]
    rw [hreal, ENNReal.ofReal_one]
  calc
    gaussianNext Kj = 1 * gaussianNext Kj := by rw [one_mul]
    _ = (ENNReal.ofReal (Real.sqrt cc ^ n) * ENNReal.ofReal (a ^ n)) *
        gaussianNext Kj := by rw [hcancel]
    _ = ENNReal.ofReal (Real.sqrt cc ^ n) *
        (ENNReal.ofReal (a ^ n) * gaussianNext Kj) := by rw [mul_assoc]
    _ ≤ ENNReal.ofReal (Real.sqrt cc ^ n) * gaussianNext Ki :=
      mul_le_mul_left' hmass _

noncomputable def adaptiveRadiusQWarmFactor (n : Nat) (cc : Real) : ENNReal :=
  ENNReal.ofReal (2 * cc ^ n)

theorem map_standardShrink_coolLaw_radiusQ_compl_eq_zero
    (hn : 1 ≤ n) {q : Real} (hq : 0 < q)
    {sigmaSq : Nat → Real} (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K)
    {i : Nat} (hi : i < m) (hsle : sigmaSq i ≤ sigmaSq (i + 1))
    (hrad : 1 ≤ q * Real.sqrt (sigmaSq i) * Real.sqrt n) :
    Measure.map (fun x : State n ↦ (1 - 1 / (2 * (n : Real))) • x)
        (coolLaw m sigmaSq (radiusQBody q K (sigmaSq i)) i)
        (((1 - 1 / (2 * (n : Real))) •
          radiusQBody q K (sigmaSq (i + 1)))ᶜ) = 0 := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  let Ki := radiusQBody q K (sigmaSq i)
  let Kj := radiusQBody q K (sigmaSq (i + 1))
  have hc0 : 0 < c := by
    dsimp [c]
    have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
    have : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hKim : MeasurableSet Ki := measurableSet_radiusQBody hK
  have hKiball : ball (0 : State n) 1 ⊆ Ki :=
    unitBall_subset_inter_closedBall hball
      (by simpa only [Ki, radiusQBody] using hrad)
  have hKifin : volume Ki ≠ ⊤ := by
    dsimp only [Ki, radiusQBody]
    exact volume_inter_closedBall_ne_top K _
  have hsmall : c • Ki ⊆ c • Kj := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, radiusQBody_subset_of_le hq.le hsle hx, rfl⟩
  have hsource : Measure.map (fun x : State n ↦ c • x)
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

theorem isWarm_standardScaledTruncated_coolLaw_radiusQ_ratio
    (hn : 1 ≤ n) {q : Real} (hq : 0 < q)
    {sigmaSq : Nat → Real} (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K)
    {i : Nat} (hi : i + 1 < m) {cc : Real} (hcc1 : 1 ≤ cc)
    (hsched : sigmaSq (i + 1) = cc * sigmaSq i)
    (hrad : 1 ≤ q * Real.sqrt (sigmaSq i) * Real.sqrt n) :
    IsWarm (adaptiveRadiusQWarmFactor n cc)
      (Measure.map (fun x : State n ↦ (1 - 1 / (2 * (n : Real))) • x)
        (coolLaw m sigmaSq (radiusQBody q K (sigmaSq i)) i))
      (coolLaw m sigmaSq (radiusQBody q K (sigmaSq (i + 1))) (i + 1)) := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  let Ki := radiusQBody q K (sigmaSq i)
  let Kj := radiusQBody q K (sigmaSq (i + 1))
  let gaussianNext : Measure (State n) :=
    volume.withDensity (gaussianWeight (sigmaSq (i + 1)))
  have hc0 : 0 < c := by
    dsimp [c]
    have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
    have : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hc1 : c ≤ 1 := by
    dsimp [c]
    have : 0 ≤ 1 / (2 * (n : Real)) := by positivity
    linarith
  have hsle : sigmaSq i ≤ sigmaSq (i + 1) := by rw [hsched]; nlinarith [hsigma i]
  have hKim : MeasurableSet Ki := measurableSet_radiusQBody hK
  have hKjm : MeasurableSet Kj := measurableSet_radiusQBody hK
  have hKic : Convex Real Ki := convex_radiusQBody hKc
  have hKiball : ball (0 : State n) 1 ⊆ Ki :=
    unitBall_subset_inter_closedBall hball
      (by simpa only [Ki, radiusQBody] using hrad)
  have hKjball : ball (0 : State n) 1 ⊆ Kj :=
    unitBall_subset_inter_closedBall hball (by
      exact hrad.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsle) hq.le)
        (Real.sqrt_nonneg _)))
  have hKifin : volume Ki ≠ ⊤ := by
    dsimp only [Ki, radiusQBody]; exact volume_inter_closedBall_ne_top K _
  have hKjfin : volume Kj ≠ ⊤ := by
    dsimp only [Kj, radiusQBody]; exact volume_inter_closedBall_ne_top K _
  have hself : IsWarm (ENNReal.ofReal ((c⁻¹) ^ n))
      (Measure.map (fun x : State n ↦ c • x) (coolLaw m sigmaSq Ki i))
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
      (radiusQBody_subset_of_le hq.le hsle) hKj0 hKjtop
  have hbodyRatio : gaussianNext Kj / gaussianNext Ki ≤
      ENNReal.ofReal (Real.sqrt cc ^ n) := by
    simpa only [gaussianNext, Ki, Kj] using
      gaussianNext_radiusQ_ratio_le_sqrt_pow hn hq (hsigma i)
        (hsigma (i + 1)) hcc1 hsched hK hKc hball hrad
  have hall := hself.trans (hphase.trans (hbody.mono hbodyRatio))
  apply hall.mono
  have hcpow : (1 / 2 : Real) ≤ c ^ n := by
    dsimp [c]
    exact half_le_one_sub_inv_two_mul_pow hn
  have hcinv : (c⁻¹) ^ n ≤ 2 := by
    rw [inv_pow]
    exact (inv_le_comm₀ (pow_pos hc0 n) (by norm_num : (0 : Real) < 2)).2 (by
      norm_num; exact hcpow)
  have hsqrt0 : 0 ≤ Real.sqrt cc ^ n := pow_nonneg (Real.sqrt_nonneg _) _
  have hsqrtSq : Real.sqrt cc ^ n * Real.sqrt cc ^ n = cc ^ n := by
    calc
      Real.sqrt cc ^ n * Real.sqrt cc ^ n =
          (Real.sqrt cc * Real.sqrt cc) ^ n := (mul_pow _ _ _).symm
      _ = cc ^ n := by rw [Real.mul_self_sqrt (zero_lt_one.trans_le hcc1).le]
  rw [adaptiveRadiusQWarmFactor]
  calc
    ENNReal.ofReal ((c⁻¹) ^ n) *
        (ENNReal.ofReal (Real.sqrt cc ^ n) * ENNReal.ofReal (Real.sqrt cc ^ n)) ≤
      ENNReal.ofReal 2 *
        (ENNReal.ofReal (Real.sqrt cc ^ n) * ENNReal.ofReal (Real.sqrt cc ^ n)) :=
          mul_le_mul_right' (ENNReal.ofReal_le_ofReal hcinv) _
    _ = ENNReal.ofReal (2 * cc ^ n) := by
      rw [← ENNReal.ofReal_mul hsqrt0, hsqrtSq]
      exact (ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 2)).symm

theorem isWarm_standardScaledTruncated_ellGaussianProb_radiusQ_ratio
    (hn : 1 ≤ n) {q : Real} (hq : 0 < q)
    {sigmaSq : Nat → Real} (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K)
    {i : Nat} (hi : i + 1 < m) {cc : Real} (hcc1 : 1 ≤ cc)
    (hsched : sigmaSq (i + 1) = cc * sigmaSq i)
    (hrad : 1 ≤ q * Real.sqrt (sigmaSq i) * Real.sqrt n)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta ≤ 1 / (2 * (n : Real))) :
    IsWarm (adaptiveRadiusQWarmFactor n cc)
      (Measure.map (fun x : State n ↦ (1 - 1 / (2 * (n : Real))) • x)
        (coolLaw m sigmaSq (radiusQBody q K (sigmaSq i)) i))
      (ellGaussianProb (radiusQBody q K (sigmaSq (i + 1))) delta
        (sigmaSq (i + 1))) := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  let Kj := radiusQBody q K (sigmaSq (i + 1))
  have hc0 : 0 < c := by
    dsimp [c]
    have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
    have : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hc1 : c < 1 := by
    dsimp [c]
    have : 0 < 1 / (2 * (n : Real)) := by positivity
    linarith
  have hsle : sigmaSq i ≤ sigmaSq (i + 1) := by rw [hsched]; nlinarith [hsigma i]
  have hKjm : MeasurableSet Kj := measurableSet_radiusQBody hK
  have hKjc : Convex Real Kj := convex_radiusQBody hKc
  have hKjball : ball (0 : State n) 1 ⊆ Kj :=
    unitBall_subset_inter_closedBall hball (by
      exact hrad.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsle) hq.le)
        (Real.sqrt_nonneg _)))
  have hsupp := map_standardShrink_coolLaw_radiusQ_compl_eq_zero
    (m := m) hn hq hsigma hK hKc hball (Nat.lt_of_succ_lt hi) hsle hrad
  have hgauss := isWarm_standardScaledTruncated_coolLaw_radiusQ_ratio
    (m := m) hn hq hsigma hK hKc hball hi hcc1 hsched hrad
  rw [coolLaw_eq_uniformOn_gaussianWeight hsigma hKjm hKjball
    (by dsimp only [Kj, radiusQBody]; exact volume_inter_closedBall_ne_top K _) hi]
      at hgauss
  exact isWarm_ellGaussianProb_of_supported_on_shrunken hKjm hKjc hKjball
    hc0 hc1 hdelta (by simpa [c] using hdeltan)
    (by simpa only [c, Kj] using hsupp) (by simpa only [c, Kj] using hgauss)

/-- Concrete hybrid-schedule specialization of the adjustable-radius cross-phase
warmth theorem.  Unlike the radius-four version, no separate next-radius lower
bound is needed: homothety compares the two expanding `q`-bodies directly. -/
theorem isWarm_standardScaledTruncated_ellGaussianProb_radiusQ_hybrid
    (hn : 1 ≤ n) {q N s0 : Real} (hq : 0 < q)
    (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K)
    {i : Nat} (hi : i + 1 < m)
    (hrate0 : 0 ≤ Ttc.CVHybridSchedule.phaseRate n N s0 i)
    (hrad : 1 ≤ q * Real.sqrt
      (Ttc.CVHybridSchedule.sigmaSq n N s0 i) * Real.sqrt n) :
    IsWarm (adaptiveRadiusQWarmFactor n
      (1 + Ttc.CVHybridSchedule.phaseRate n N s0 i))
      (Measure.map (fun x : State n ↦ (1 - 1 / (2 * (n : Real))) • x)
        (coolLaw m (Ttc.CVHybridSchedule.sigmaSq n N s0)
          (radiusQBody q K (Ttc.CVHybridSchedule.sigmaSq n N s0 i)) i))
      (ellGaussianProb
        (radiusQBody q K (Ttc.CVHybridSchedule.sigmaSq n N s0 (i + 1)))
        (radiusQDelta n q (Ttc.CVHybridSchedule.sigmaSq n N s0 (i + 1)))
        (Ttc.CVHybridSchedule.sigmaSq n N s0 (i + 1))) := by
  apply isWarm_standardScaledTruncated_ellGaussianProb_radiusQ_ratio
    hn hq (Ttc.CVHybridSchedule.sigmaSq_pos hn hN hs0) hK hKc hball hi
    (show 1 ≤ 1 + Ttc.CVHybridSchedule.phaseRate n N s0 i by linarith)
    (by
      rw [Ttc.CVHybridSchedule.sigmaSq_succ hn hN hs0]
      ring)
    hrad
    (radiusQDelta_pos hn hq
      (Ttc.CVHybridSchedule.sigmaSq_pos hn hN hs0 (i + 1)))
    (radiusQDelta_le_n n q _)

#print axioms gaussianNext_radiusQ_ratio_le_sqrt_pow
#print axioms isWarm_standardScaledTruncated_ellGaussianProb_radiusQ_ratio
#print axioms isWarm_standardScaledTruncated_ellGaussianProb_radiusQ_hybrid

end Ttc.CVAdaptiveRadiusQCrossWarm
