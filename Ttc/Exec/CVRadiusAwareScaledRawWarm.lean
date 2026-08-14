import Arlib.Convexity.GaussianCooling.ScaledRawWarm
import Arlib.Convexity.GaussianCooling.WarmChain
import Ttc.Volume.CVHybridVarianceBudget
import Ttc.Exec.CVGaussianScoreSeedPhaseKernel

/-!
# Radius-aware constant warmth for accelerated scaled raw seeds

The ratio-only scaled-seed theorem pays `cc^(n/2)` and is exponential for the hot
`cc = 3/2` phases.  CV's accelerated schedule also has a radius invariant.  The
radius-aware cooling comparison pays only `sqrt(e)`, independently of the ratio and
dimension.  Composing it with the source shrink Jacobian (at most two) gives the
constant `2*sqrt(e)` for the actual scaled raw seed.
-/

set_option autoImplicit false

namespace Ttc.CVRadiusAwareScaledRawWarm

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.CVHybridSchedule
open scoped ENNReal Pointwise

variable {n m : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- Radius-aware replacement for the ratio-dependent scaled-raw theorem. -/
theorem isWarm_standardScaledRaw_coolLaw_succ_ellGaussianProb_radius
    (hn : 1 ≤ n) {sigmaSq : Nat → Real} (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m) {R cc : Real}
    (hKR : K ⊆ closedBall (0 : State n) R) (hcc1 : 1 ≤ cc)
    (hsched : sigmaSq (i + 1) = cc * sigmaSq i)
    (hrate : R ^ 2 * (cc - 1) ≤ cc * sigmaSq i)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta ≤ 1 / (2 * (n : Real))) :
    IsWarm (ENNReal.ofReal (2 * Real.exp (1 / 2)))
      (Measure.map
        (fun x : State n ↦ (1 - 1 / (2 * (n : Real))) • x)
        (coolLaw m sigmaSq K i))
      (ellGaussianProb K delta (sigmaSq (i + 1))) := by
  have hnreal : (0 : Real) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hc0 : 0 < c := by
    dsimp [c]
    have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
      nlinarith
    linarith
  have hc1 : c < 1 := by
    dsimp [c]
    have : 0 < 1 / (2 * (n : Real)) := by positivity
    linarith
  have hdc : delta ≤ 1 - c := by simpa [c] using hdeltan
  have him : i < m := Nat.lt_of_succ_lt hi
  have hself := isWarm_map_smul_coolLaw_self hsigma hK hKc hball hfin
    him hc0 hc1.le
  have hnext := isWarm_coolLaw_of_subset_ball_sqrt_exp hi hK hfin hball
    hsigma hKR hcc1 hsched hrate
  have hgauss := hself.trans hnext
  have hcKm : MeasurableSet (c • K) := measurableSet_smul_set hK hc0.ne'
  have hsupp : Measure.map (fun x : State n ↦ c • x)
      (coolLaw m sigmaSq K i) ((c • K)ᶜ) = 0 := by
    rw [map_smul_coolLaw_eq_condOn hsigma hK hball hfin him hc0,
      Arlib.condOn_apply _ MeasurableSet.univ hcKm.compl, inter_univ]
    have hempty : (c • K)ᶜ ∩ c • K = (∅ : Set (State n)) := compl_inter_self _
    rw [withDensity_apply _ hcKm.compl, Measure.restrict_restrict hcKm.compl,
      hempty, Measure.restrict_empty]
    simp
  rw [coolLaw_eq_uniformOn_gaussianWeight hsigma hK hball hfin hi] at hgauss
  have hraw := isWarm_ellGaussianProb_of_supported_on_shrunken hK hKc hball
    hc0 hc1 hdelta hdc hsupp hgauss
  have hcpow : (1 / 2 : Real) ≤ c ^ n := by
    dsimp [c]
    exact half_le_one_sub_inv_two_mul_pow hn
  have hcinv : (c⁻¹) ^ n ≤ 2 := by
    rw [inv_pow]
    exact (inv_le_comm₀ (pow_pos hc0 n) (by norm_num : (0 : Real) < 2)).2 (by
      norm_num
      exact hcpow)
  have hfinal := hraw.mono (show
      ENNReal.ofReal ((c⁻¹) ^ n) * ENNReal.ofReal (Real.exp (1 / 2)) ≤
        ENNReal.ofReal (2 * Real.exp (1 / 2)) by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (c⁻¹) ^ n)]
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hcinv (Real.exp_pos (1 / 2)).le))
  simpa only [c] using hfinal

/-- The new hot-phase constant is bounded by the already-used `2e` envelope. -/
theorem radiusScaledRawWarm_le_two_exp :
    ENNReal.ofReal (2 * Real.exp (1 / 2)) ≤
      ENNReal.ofReal (2 * Real.exp 1) := by
  apply ENNReal.ofReal_le_ofReal
  gcongr
  norm_num

/-- Score/seed form consumed by the retained-history Gaussian specialization. -/
theorem isWarm_scoreSeedReference_active_of_radius_twoE
    (hn : 1 ≤ n) {sigmaSq : Nat → Real} (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m) {R cc : Real}
    (hKR : K ⊆ closedBall (0 : State n) R) (hcc1 : 1 ≤ cc)
    (hsched : sigmaSq (i + 1) = cc * sigmaSq i)
    (hrate : R ^ 2 * (cc - 1) ≤ cc * sigmaSq i)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta ≤ 1 / (2 * (n : Real))) :
    IsWarm (ENNReal.ofReal (2 * Real.exp 1))
      (Measure.map Prod.snd
        (scoreSeedReference (1 - 1 / (2 * (n : Real)))
          (coolLaw m sigmaSq K i)))
      (ellGaussianProb K delta (sigmaSq (i + 1))) := by
  rw [map_snd_scoreSeedReference]
  exact (isWarm_standardScaledRaw_coolLaw_succ_ellGaussianProb_radius
    hn hsigma hK hKc hball hfin hi hKR hcc1 hsched hrate hdelta hdeltan).mono
      radiusScaledRawWarm_le_two_exp

/-- Every accelerated (post-cold-block) hybrid phase satisfies the radius criterion
when `R² ≤ N`.  This is the schedule invariant that removes the exponential hot
warmth factor. -/
theorem hybrid_hot_radius_condition
    {n : Nat} (hn : 1 ≤ n) {N s0 R : Real}
    (hN : 0 < N) (hs0 : 0 < s0) (hR2 : R ^ 2 ≤ N)
    {i : Nat} (hi : ¬ i < coldPhases n s0) :
    R ^ 2 * ((1 + phaseRate n N s0 i) - 1) ≤
      (1 + phaseRate n N s0 i) * sigmaSq n N s0 i := by
  let q := i - coldPhases n s0
  let j := adaptivePhaseChunk N (coldEnd n s0) q
  have hcold0 : 0 < coldEnd n s0 := coldEnd_pos hn hs0
  have hrate0 : 0 < adaptivePhaseRate N (coldEnd n s0) q := by
    unfold adaptivePhaseRate
    exact adaptiveChunkRate_pos hN hcold0 _
  have hstart : adaptiveChunkStart N (coldEnd n s0) j ≤
      adaptiveSigmaSq N (coldEnd n s0) q := by
    simpa only [adaptiveSigmaSq, j] using
      adaptiveChunkStart_le_geom hN hcold0 j
        (adaptiveLocalPhase N (coldEnd n s0) q)
  have hNrate : N * adaptivePhaseRate N (coldEnd n s0) q =
      adaptiveChunkStart N (coldEnd n s0) j / 2 := by
    unfold adaptivePhaseRate adaptiveChunkRate
    dsimp only [j]
    field_simp [hN.ne']
  have hRrate : R ^ 2 * adaptivePhaseRate N (coldEnd n s0) q ≤
      N * adaptivePhaseRate N (coldEnd n s0) q :=
    mul_le_mul_of_nonneg_right hR2 hrate0.le
  rw [phaseRate, if_neg hi, sigmaSq, if_neg hi]
  dsimp only [q] at hrate0 hstart hNrate hRrate ⊢
  have hsigma0 : 0 < adaptiveSigmaSq N (coldEnd n s0)
      (i - coldPhases n s0) := adaptiveSigmaSq_pos hN hcold0 _
  nlinarith

/-- Uniform `2e` reference warmth for every active phase of the complete hybrid
schedule: the fixed cold block uses the ratio route, and the accelerated block uses the
radius route above. -/
theorem isWarm_scoreSeedReference_hybrid_twoE
    {n : Nat} (hn : 1 ≤ n) {m : Nat} {N s0 R : Real}
    (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R) (hR2 : R ^ 2 ≤ N)
    {i : Nat} (hi : i + 1 < m)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta ≤ 1 / (2 * (n : Real))) :
    IsWarm (ENNReal.ofReal (2 * Real.exp 1))
      (Measure.map Prod.snd
        (scoreSeedReference (1 - 1 / (2 * (n : Real)))
          (coolLaw m (sigmaSq n N s0) K i)))
      (ellGaussianProb K delta (sigmaSq n N s0 (i + 1))) := by
  have hsigma : ∀ j, 0 < sigmaSq n N s0 j := sigmaSq_pos hn hN hs0
  have hsched : sigmaSq n N s0 (i + 1) =
      (1 + phaseRate n N s0 i) * sigmaSq n N s0 i := by
    rw [sigmaSq_succ hn hN hs0 i]
    ring
  by_cases hicold : i < coldPhases n s0
  · apply isWarm_snd_scoreSeedReference_standard hn hsigma hK hKc hball hfin
      hi (cc := 1 + phaseRate n N s0 i)
    · rw [phaseRate, if_pos hicold]
      exact le_add_of_nonneg_right (by positivity)
    · rw [phaseRate, if_pos hicold]
      have hnR : (0 : Real) < n := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
      have : 1 / (n : Real) ≤ 2 / (n : Real) := by
        rw [div_le_div_iff₀ hnR hnR]
        nlinarith
      linarith
    · exact hsched
    · exact hdelta
    · exact hdeltan
  · apply isWarm_scoreSeedReference_active_of_radius_twoE hn hsigma hK hKc
      hball hfin hi hKR (cc := 1 + phaseRate n N s0 i)
    · unfold phaseRate
      rw [if_neg hicold]
      have := adaptiveChunkRate_pos hN (coldEnd_pos hn hs0)
        (adaptivePhaseChunk N (coldEnd n s0) (i - coldPhases n s0))
      have hphase : 0 < adaptivePhaseRate N (coldEnd n s0)
          (i - coldPhases n s0) := by
        simpa only [adaptivePhaseRate] using this
      linarith
    · exact hsched
    · exact hybrid_hot_radius_condition hn hN hs0 hR2 hicold
    · exact hdelta
    · exact hdeltan

#print axioms isWarm_standardScaledRaw_coolLaw_succ_ellGaussianProb_radius
#print axioms radiusScaledRawWarm_le_two_exp
#print axioms isWarm_scoreSeedReference_active_of_radius_twoE
#print axioms hybrid_hot_radius_condition
#print axioms isWarm_scoreSeedReference_hybrid_twoE

end Ttc.CVRadiusAwareScaledRawWarm
