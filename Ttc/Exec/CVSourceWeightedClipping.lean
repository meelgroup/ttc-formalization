import Ttc.Exec.CVWeightedCorrectedAccuracy
import Ttc.Volume.CVHybridParameters

/-!
# Source-weighted clipping factors

Clipping does not require replacing every phase by one uniform `1 + 8/k` factor.
If a raw empirical phase has relative second moment `c <= 2`, clipping at `alpha`
changes its factor only to

`c / (1 - 1/(2*alpha))^2`.

The common denominator accumulates as `exp(O(m/alpha))`; with `correctedAlpha` this is
`exp(O(eps^2))`.  The numerator is therefore free to retain the source cold/hot product.
-/

set_option autoImplicit false

namespace Ttc.CVSourceWeightedClipping

open MeasureTheory ProbabilityTheory Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open Ttc.CVCorrected Ttc.CVHybridSchedule
open scoped BigOperators

variable {Omega : Type*} [MeasurableSpace Omega]

noncomputable def clippedFactor (alpha c : Real) : Real :=
  c / (1 - 1 / (2 * alpha)) ^ 2

/-- Phasewise clipping preserves the actual raw factor, paying only the common
`alpha`-denominator. -/
theorem clipped_sq_moment_le_factor
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {Wbar V : Omega -> Real} {alpha c : Real}
    (halpha : 1 < alpha) (hc0 : 0 <= c) (hc2 : c <= 2)
    (hW0 : forall omega, 0 <= Wbar omega) (hWm : Measurable Wbar)
    (hWint : Integrable Wbar mu)
    (hW2int : Integrable (fun omega => (Wbar omega) ^ 2) mu)
    (hWEpos : 0 < ∫ omega, Wbar omega ∂mu)
    (hrawSecond : ∫ omega, (Wbar omega) ^ 2 ∂mu <=
      c * (∫ omega, Wbar omega ∂mu) ^ 2)
    (hVdef : forall omega, V omega = min (Wbar omega)
      (alpha * ∫ z, Wbar z ∂mu)) :
    Integrable (fun omega => (V omega) ^ 2) mu /\
      (∫ omega, (V omega) ^ 2 ∂mu) <=
        clippedFactor alpha c * (∫ omega, V omega ∂mu) ^ 2 := by
  have halpha0 : 0 < alpha := lt_trans zero_lt_one halpha
  have hVeq : V = fun omega => min (Wbar omega)
      (alpha * ∫ z, Wbar z ∂mu) := by
    funext omega
    exact hVdef omega
  have hthreshold0 : 0 <= alpha * ∫ z, Wbar z ∂mu :=
    mul_nonneg halpha0.le hWEpos.le
  have hV0 : forall omega, 0 <= V omega := fun omega => by
    rw [hVeq]
    exact le_min (hW0 omega) hthreshold0
  have hVm : Measurable V := by
    rw [hVeq]
    exact hWm.min measurable_const
  have hVW : forall omega, V omega <= Wbar omega := fun omega => by
    rw [hVeq]
    exact min_le_left _ _
  have hV2int : Integrable (fun omega => (V omega) ^ 2) mu := by
    refine Integrable.mono' hW2int (hVm.pow_const 2).aestronglyMeasurable ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (hV0 omega) (hW0 omega)).2 (hVW omega)
  have hlower :
      (1 - 1 / (2 * alpha)) * (∫ omega, Wbar omega ∂mu) <=
        ∫ omega, V omega ∂mu := by
    have h := expect_trunc_ge_half halpha0 hW0 hWm hWint hW2int hWEpos
      hrawSecond hc2
    rw [hVeq]
    exact h
  have hden0 : 0 < 1 - 1 / (2 * alpha) := by
    have : 1 / (2 * alpha) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    linarith
  have hVsecond : (∫ omega, (V omega) ^ 2 ∂mu) <=
      ∫ omega, (Wbar omega) ^ 2 ∂mu :=
    integral_mono hV2int hW2int fun omega =>
      (sq_le_sq₀ (hV0 omega) (hW0 omega)).2 (hVW omega)
  have hmean : (∫ omega, Wbar omega ∂mu) <=
      (∫ omega, V omega ∂mu) / (1 - 1 / (2 * alpha)) := by
    rw [le_div_iff₀ hden0]
    simpa [mul_comm] using hlower
  have hcclip0 : 0 <= clippedFactor alpha c := by
    unfold clippedFactor
    positivity
  constructor
  · exact hV2int
  · calc
      (∫ omega, (V omega) ^ 2 ∂mu) <=
          ∫ omega, (Wbar omega) ^ 2 ∂mu := hVsecond
      _ <= c * (∫ omega, Wbar omega ∂mu) ^ 2 := hrawSecond
      _ <= c * ((∫ omega, V omega ∂mu) /
          (1 - 1 / (2 * alpha))) ^ 2 := by gcongr
      _ = clippedFactor alpha c * (∫ omega, V omega ∂mu) ^ 2 := by
        unfold clippedFactor
        field_simp

/-- For `alpha >= 2`, one clipping denominator costs at most `1 + 2/alpha`. -/
theorem inv_clippingDenominator_sq_le {alpha : Real} (halpha : 2 <= alpha) :
    1 / (1 - 1 / (2 * alpha)) ^ 2 <= 1 + 2 / alpha := by
  have halpha0 : 0 < alpha := lt_of_lt_of_le (by norm_num) halpha
  have hden0 : 0 < 1 - 1 / (2 * alpha) := by
    rw [sub_pos, div_lt_one (by positivity)]
    linarith
  rw [div_le_iff₀ (sq_pos_of_pos hden0)]
  field_simp [ne_of_gt halpha0]
  nlinarith [sq_nonneg (alpha - 2)]

/-- The accumulated common clipping inflation is `exp(2*i/alpha)`. -/
theorem clippingInflation_pow_le_exp {alpha : Real} (halpha : 2 <= alpha)
    (i : Nat) :
    (1 / (1 - 1 / (2 * alpha)) ^ 2) ^ i <=
      Real.exp (2 * (i : Real) / alpha) := by
  have halpha0 : 0 < alpha := lt_of_lt_of_le (by norm_num) halpha
  have hbase := inv_clippingDenominator_sq_le halpha
  have hpow := pow_le_pow_left₀ (by positivity) hbase i
  calc
    (1 / (1 - 1 / (2 * alpha)) ^ 2) ^ i <=
        (1 + 2 / alpha) ^ i := hpow
    _ <= Real.exp ((i : Real) * (2 / alpha)) :=
      one_add_pow_le_exp (by positivity) i
    _ = Real.exp (2 * (i : Real) / alpha) := by congr 1 <;> ring

/-- Prefix products of clipped factors split into the raw weighted product and the
common clipping inflation. -/
theorem prefixMomentRatio_clippedFactor
    (alpha : Real) (raw : Nat -> Real) (i : Nat) :
    prefixMomentRatio (fun j => clippedFactor alpha (raw j)) i =
      prefixMomentRatio raw i /
        (1 - 1 / (2 * alpha)) ^ (2 * i) := by
  unfold prefixMomentRatio clippedFactor
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_range, pow_mul]

/-- A source-sharp raw prefix budget plus corrected clipping gives a source-sharp
clipped prefix budget. -/
theorem clipped_prefix_le_exp
    {alpha kappa eps : Real} {raw : Nat -> Real} {m : Nat}
    (halpha : 2 <= alpha) (heps : 0 < eps)
    (hraw0 : forall j, 0 <= raw j)
    (hraw : forall i, i <= m -> prefixMomentRatio raw i <= Real.exp kappa)
    (hmAlpha : 2 * (m : Real) / alpha <= eps ^ 2 / 50000)
    (hfinal : Real.exp (kappa + eps ^ 2 / 50000) <=
      1 + eps ^ 2 / 6250) :
    forall i, i <= m ->
      prefixMomentRatio (fun j => clippedFactor alpha (raw j)) i <=
        1 + eps ^ 2 / 6250 := by
  intro i hi
  have hiR : (i : Real) <= (m : Real) := by exact_mod_cast hi
  have halpha0 : 0 < alpha := lt_of_lt_of_le (by norm_num) halpha
  have hiAlpha : 2 * (i : Real) / alpha <= eps ^ 2 / 50000 := by
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hiR (by norm_num))
      halpha0.le).trans hmAlpha
  have hinfl := clippingInflation_pow_le_exp halpha i
  have hrawNonneg : 0 <= prefixMomentRatio raw i :=
    Finset.prod_nonneg fun j _ => hraw0 (j + 1)
  rw [prefixMomentRatio_clippedFactor]
  have hdenEq :
      ((1 - 1 / (2 * alpha)) ^ (2 * i))⁻¹ =
        (1 / (1 - 1 / (2 * alpha)) ^ 2) ^ i := by
    simp only [one_div, ← inv_pow, pow_mul]
  rw [div_eq_mul_inv, hdenEq]
  calc
    prefixMomentRatio raw i *
        (1 / (1 - 1 / (2 * alpha)) ^ 2) ^ i <=
      Real.exp kappa * Real.exp (2 * (i : Real) / alpha) :=
        mul_le_mul (hraw i hi) hinfl (by positivity) (Real.exp_pos kappa).le
    _ = Real.exp (kappa + 2 * (i : Real) / alpha) := by rw [Real.exp_add]
    _ <= Real.exp (kappa + eps ^ 2 / 50000) := by
      exact Real.exp_le_exp.mpr (by linarith)
    _ <= 1 + eps ^ 2 / 6250 := hfinal

/-- The concrete `eps/100` source budget leaves ample room for clipping. -/
theorem estimator_clipping_final_budget {eps : Real}
    (heps : 0 < eps) (heps1 : eps <= 1) :
    Real.exp (varBudget (eps / 100) + eps ^ 2 / 50000) <=
      1 + eps ^ 2 / 6250 := by
  rw [Real.exp_add, exp_varBudget]
  have hx0 : 0 <= eps ^ 2 / 50000 := by positivity
  have hx1 : eps ^ 2 / 50000 <= 1 / 2 := by
    nlinarith [sq_nonneg (eps - 1)]
  have hexp := exp_le_one_add_two_mul hx0 hx1
  have heq : 1 + (eps / 100) ^ 2 / 5 = 1 + eps ^ 2 / 50000 := by ring
  rw [heq]
  calc
    (1 + eps ^ 2 / 50000) * Real.exp (eps ^ 2 / 50000) <=
        (1 + eps ^ 2 / 50000) * (1 + 2 * (eps ^ 2 / 50000)) := by
      gcongr
    _ <= 1 + eps ^ 2 / 6250 := by
      nlinarith [sq_nonneg (eps ^ 2)]

/-! ## Concrete source schedule -/

/-- Paper-indexed version of the source cold/hot empirical factor. -/
noncomputable def sourceRawFactor
    (n : Nat) (k N s0 : Real) (j : Nat) : Real :=
  phaseVarFactor n k N s0 (j - 1)

theorem phaseVarFactor_one_le {n : Nat} (hn : 1 <= n)
    {k N s0 : Real} (hk : 0 < k) (hN : 0 < N) (hs0 : 0 < s0)
    (i : Nat) :
    1 <= phaseVarFactor n k N s0 i := by
  by_cases hi : i < coldPhases n s0
  · rw [phaseVarFactor, if_pos hi]
    have hnR : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    have hq : 0 <= 2 / (k * (n : Real)) := by positivity
    linarith
  · rw [phaseVarFactor, if_neg hi]
    unfold adaptiveGlobalPhaseVarFactor
    have hsigma := adaptiveSigmaSq_pos hN (coldEnd_pos hn hs0)
      (i - coldPhases n s0)
    have hq : 0 <= adaptiveSigmaSq N (coldEnd n s0) (i - coldPhases n s0) /
        (k * N) := by positivity
    linarith

/-- Every active source empirical phase factor is at most two once `k >= 2`.
For a hot phase this uses the defining fact that its local variance is still below twice
the current chunk start. -/
theorem phaseVarFactor_le_two {n : Nat} (hn : 1 <= n)
    {k N s0 : Real} (hk : 2 <= k) (hN : 0 < N) (hs0 : 0 < s0)
    (i : Nat)
    (hbelow : adaptiveChunkStart N (coldEnd n s0)
      (adaptivePhaseChunk N (coldEnd n s0) (i - coldPhases n s0)) <= N) :
    phaseVarFactor n k N s0 i <= 2 := by
  have hk0 : 0 < k := lt_of_lt_of_le (by norm_num) hk
  by_cases hi : i < coldPhases n s0
  · rw [phaseVarFactor, if_pos hi]
    have hnR : (1 : Real) <= n := by exact_mod_cast hn
    have hfrac : 2 / (k * (n : Real)) <= 1 := by
      rw [div_le_one (mul_pos hk0 (by positivity))]
      nlinarith
    linarith
  · rw [phaseVarFactor, if_neg hi]
    unfold adaptiveGlobalPhaseVarFactor
    let t := i - coldPhases n s0
    let j := adaptivePhaseChunk N (coldEnd n s0) t
    have hend := coldEnd_pos hn hs0
    have hlocal := adaptiveLocalPhase_lt hN hend t
    have hsigmaLt : adaptiveSigmaSq N (coldEnd n s0) t <
        2 * adaptiveChunkStart N (coldEnd n s0) j := by
      exact adaptiveChunk_phase_lt_two hN hend hlocal
    have hsigmaN : adaptiveSigmaSq N (coldEnd n s0) t < 2 * N :=
      hsigmaLt.trans_le (mul_le_mul_of_nonneg_left hbelow (by norm_num))
    have hfrac : adaptiveSigmaSq N (coldEnd n s0) t / (k * N) <= 1 := by
      rw [div_le_one (mul_pos hk0 hN)]
      nlinarith
    simpa only [t] using (show
      1 + adaptiveSigmaSq N (coldEnd n s0) t / (k * N) <= 2 by linarith)

theorem prefixMomentRatio_sourceRawFactor_eq
    (n : Nat) (k N s0 : Real) (i : Nat) :
    prefixMomentRatio (sourceRawFactor n k N s0) i =
      ∏ j ∈ Finset.range i, phaseVarFactor n k N s0 j := by
  unfold prefixMomentRatio sourceRawFactor
  apply Finset.prod_congr rfl
  intro j hj
  rw [Nat.add_sub_cancel]

/-- Every source-schedule prefix is bounded by the complete cold/hot product. -/
theorem sourceRawFactor_prefix_le_full
    {n J i : Nat} (hn : 1 <= n) {k N s0 : Real}
    (hk : 0 < k) (hN : 0 < N) (hs0 : 0 < s0)
    (hi : i <= coldPhases n s0 +
      adaptiveChunkOffset N (coldEnd n s0) J) :
    prefixMomentRatio (sourceRawFactor n k N s0) i <=
      ∏ j ∈ Finset.range (coldPhases n s0 +
        adaptiveChunkOffset N (coldEnd n s0) J),
          phaseVarFactor n k N s0 j := by
  rw [prefixMomentRatio_sourceRawFactor_eq]
  apply Finset.prod_le_prod_of_subset_of_one_le
  · exact Finset.range_mono hi
  · intro j hj
    exact zero_le_one.trans (phaseVarFactor_one_le hn hk hN hs0 j)
  · intro j hj _hji
    exact phaseVarFactor_one_le hn hk hN hs0 j

/-- The tightened source sample count (`eps/100`) bounds every raw prefix by the
same source-sharp exponential budget. -/
theorem estimator_sourceRawFactor_prefix_le
    {n J i : Nat} (hn : 1 <= n) {N s0 eps : Real}
    (hN : 0 < N) (hs0 : 0 < s0) (heps : 0 < eps)
    (hbelow : forall j, j < J -> adaptiveChunkStart N (coldEnd n s0) j <= N)
    (hi : i <= coldPhases n s0 +
      adaptiveChunkOffset N (coldEnd n s0) J) :
    prefixMomentRatio
        (sourceRawFactor n
          (estimatorSamples n (coldPhases n s0) J (eps / 100) : Real) N s0) i <=
      Real.exp (varBudget (eps / 100)) := by
  let k : Real := estimatorSamples n (coldPhases n s0) J (eps / 100)
  have heps' : 0 < eps / 100 := by positivity
  have hk42 : 42 <= k := estimatorSamples_ge_42 n (coldPhases n s0) J (eps / 100)
  have hk0 : 0 < k := lt_of_lt_of_le (by norm_num) hk42
  have hprefix := sourceRawFactor_prefix_le_full (J := J) hn hk0 hN hs0 hi
  have hcold := estimatorSamples_cold_budget
    (c := coldPhases n s0) (J := J) hn heps'
  have hhot := estimatorSamples_hot_budget
    (n := n) (c := coldPhases n s0) (J := J) heps'
  have hfull := prod_phaseVarFactor_le_exp hn hk42 hN hs0 hcold hbelow hhot
  have hkappa : estimatorKappa (eps / 100) + estimatorKappa (eps / 100) =
      varBudget (eps / 100) := by unfold estimatorKappa; ring
  rw [hkappa] at hfull
  exact hprefix.trans hfull

/-- Corrected clipping plus the concrete source sample count discharges *all* prefix
moment budgets required by the dependent recursion. -/
theorem estimator_clipped_source_prefix_bundle
    {n J : Nat} (hn : 1 <= n) {N s0 eps : Real}
    (hN : 0 < N) (hs0 : 0 < s0) (heps : 0 < eps) (heps1 : eps <= 1)
    (hbelow : forall j, j < J -> adaptiveChunkStart N (coldEnd n s0) j <= N) :
    let m := coldPhases n s0 + adaptiveChunkOffset N (coldEnd n s0) J
    let raw := sourceRawFactor n
      (estimatorSamples n (coldPhases n s0) J (eps / 100) : Real) N s0
    (forall j, 0 <= clippedFactor (correctedAlpha m eps) (raw j)) /\
    (forall i, i <= m ->
      prefixMomentRatio
        (fun j => clippedFactor (correctedAlpha m eps) (raw j)) i <=
          1 + eps ^ 2 / 6250) := by
  dsimp only
  let m := coldPhases n s0 + adaptiveChunkOffset N (coldEnd n s0) J
  let k : Real := estimatorSamples n (coldPhases n s0) J (eps / 100)
  let raw := sourceRawFactor n k N s0
  have heps' : 0 < eps / 100 := by positivity
  have hk42 : 42 <= k := estimatorSamples_ge_42 n (coldPhases n s0) J (eps / 100)
  have hk0 : 0 < k := lt_of_lt_of_le (by norm_num) hk42
  have halpha : 2 <= correctedAlpha m eps := by
    have h := one_le_correctedAlpha (m := m) heps heps1
    unfold correctedAlpha
    have heps2 : eps ^ 2 <= 1 := by nlinarith [sq_nonneg eps]
    have hm0 : 0 <= (m : Real) := by positivity
    rw [le_div_iff₀ (sq_pos_of_pos heps)]
    nlinarith
  have hraw0 : forall j, 0 <= raw j := by
    intro j
    exact (phaseVarFactor_one_le hn hk0 hN hs0 (j - 1)).trans' zero_le_one
  constructor
  · intro j
    unfold clippedFactor
    exact div_nonneg (hraw0 j) (sq_nonneg _)
  · apply clipped_prefix_le_exp halpha heps hraw0
    · intro i hi
      exact estimator_sourceRawFactor_prefix_le hn hN hs0 heps hbelow hi
    · unfold correctedAlpha
      have hm0 : 0 <= (m : Real) := by positivity
      have hmp : 0 < (m : Real) + 1 := by positivity
      field_simp [ne_of_gt heps, ne_of_gt hmp]
      nlinarith
    · exact estimator_clipping_final_budget heps heps1

/-- Spending a phase-relative scalar slack and then averaging twice the source sample
count reproduces the original source empirical factor.  This is the key operational
replacement for the coarse scalar-seven route. -/
theorem doubledSamples_relativeSlack_factor
    {n : Nat} {N s0 : Real} (i : Nat) {k : Nat} (hk : 0 < k) :
    1 + ((2 * phaseVarFactor n 1 N s0 i - 1) - 1) /
        ((2 * k : Nat) : Real) =
      phaseVarFactor n (k : Real) N s0 i := by
  have hkR : (0 : Real) < k := by exact_mod_cast hk
  rw [← averaged_phaseVarFactor_eq (n := n) (k := (k : Real))
    (N := N) (s0 := s0) i]
  push_cast
  field_simp [ne_of_gt hkR]
  ring

#print axioms clipped_sq_moment_le_factor
#print axioms inv_clippingDenominator_sq_le
#print axioms clippingInflation_pow_le_exp
#print axioms clipped_prefix_le_exp
#print axioms estimator_clipping_final_budget
#print axioms phaseVarFactor_one_le
#print axioms phaseVarFactor_le_two
#print axioms estimator_sourceRawFactor_prefix_le
#print axioms estimator_clipped_source_prefix_bundle
#print axioms doubledSamples_relativeSlack_factor

end Ttc.CVSourceWeightedClipping
