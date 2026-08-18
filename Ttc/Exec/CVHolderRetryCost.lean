/-
# The `L^p(π)` cost bound that the Hölder retry lever needs

`Arlib.MarkovChains.sum_lintegral_le_of_isWarm_holder` replaces the retry loop's factor `L`
by `L·η^{1/q} + (1 − r^{1/q})⁻¹`, at the price of needing an `L^p(π)` bound on the observable
rather than an `L^1(π)` bound.  This file supplies that bound for the speedy walk's per-step
cost, at `p = 1 + 1/(2n)`.

The chain is short because every link already exists:

* `acc ≥ 3/5` a.e. on `K` — `Ttc.AdjustableLazyProperCost.adjustable_acceptance_multiplier`
  together with `Arlib.MarkovChains.ae_restrict_acceptance_floor_le_speedyMetropolisMove`, so
  the per-step cost is at most `2·ℓ⁻¹`;
* `∫ ℓ^{-(1+1/(2n))} dπ ≤ 6·∫ ℓ⁻¹ dπ` —
  `Arlib.MarkovChains.lintegral_ell_rpow_neg_ellGaussianProb_le`, the fractional moment;
* `3·∫ (ℓ·acc)⁻¹ dπ ≤ 10` — `three_mul_sum_lintegral_le_ten_mul_adjustable` at `t = 1`,
  `M = 1`, `mu = π`, which is the *existing* first-moment bound; and `acc ≤ 1` makes it
  dominate `∫ ℓ⁻¹ dπ`.

Nothing new about the walk is needed.  What is new is only that the fractional moment is
finite, which is `LocalConductanceMoment.lean`.
-/
import Ttc.Exec.AdjustableLazyProperProposalCost
import Arlib.MarkovChains.Continuous.LocalConductanceMoment
import Arlib.MarkovChains.Continuous.WarmHolder

namespace Ttc.CVHolderRetryCost

open MeasureTheory Metric
open Arlib.MarkovChains
open Ttc.AdjustableLazyProperCost
open scoped ENNReal

variable {n : Nat}

/-- The states of the walk. -/
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- **The per-step cost of the speedy walk**: the mean number of ordinary proposals spent per
proper accepted move, `(ℓ · acc)⁻¹`.  This is the integrand of every cost bound in the
adjustable chain. -/
noncomputable def stepCost (K : Set (State n)) (delta s : Real) (x : State n) : ℝ≥0∞ :=
  (ell K delta x * speedyMetropolisMove K delta s x)⁻¹

/-- The Hölder exponent, `p = 1 + 1/(2n)`. -/
noncomputable def holderP (n : Nat) : Real := 1 + 1 / (2 * (n : Real))

/-- Its conjugate, `q = 2n + 1`. -/
noncomputable def holderQ (n : Nat) : Real := 2 * (n : Real) + 1

theorem holderP_conjugate (hn : 0 < n) : (holderP n).HolderConjugate (holderQ n) := by
  have hnR : (0:Real) < (n : Real) := by exact_mod_cast hn
  rw [Real.holderConjugate_iff]
  constructor
  · rw [holderP]
    have : (0:Real) < 1 / (2 * (n : Real)) := by positivity
    linarith
  · rw [holderP, holderQ]
    field_simp

theorem holderP_le_two (hn : 0 < n) : holderP n ≤ 2 := by
  have hnR : (1:Real) ≤ (n : Real) := by exact_mod_cast hn
  rw [holderP]
  have h : 1 / (2 * (n : Real)) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  linarith

theorem one_le_holderP (hn : 0 < n) : 1 ≤ holderP n := by
  have hnR : (0:Real) < (n : Real) := by exact_mod_cast hn
  rw [holderP]
  have : (0:Real) < 1 / (2 * (n : Real)) := by positivity
  linarith

/-! ## The absolute continuity that transfers a.e. statements to `π` -/

theorem ellGaussianProb_absolutelyContinuous (K : Set (State n)) (delta s : Real) :
    ellGaussianProb K delta s ≪ volume.restrict K := by
  intro t ht
  have h0 : ellGaussianMeasure K delta s t = 0 := by
    rw [ellGaussianMeasure]
    exact withDensity_absolutelyContinuous (volume.restrict K) _ ht
  rw [ellGaussianProb, Measure.smul_apply, smul_eq_mul, h0, mul_zero]

/-! ## The `L^p(π)` bound -/

/-- **The per-step cost is at most `2·ℓ⁻¹`, a.e. on `K`.**  The acceptance floor
`3 ≤ 5·acc` gives `acc ≥ 3/5 ≥ 1/2`. -/
theorem ae_stepCost_le_two_mul_inv_ell
    (hn : 2 ≤ n) {q : Real} (hq : 1 < q)
    {K : Set (State n)} (hK : MeasurableSet K)
    {delta sigma R : Real} (hdelta : 0 < delta) (hsigma : 0 < sigma)
    (hdeltaq : delta ≤ sigma / (max 8 (2 * q) * Real.sqrt n))
    (hR : 0 ≤ R) (hRsigma : R ≤ q * sigma * Real.sqrt n)
    (hKR : ∀ x, x ∈ K → ‖x‖ ≤ R) :
    ∀ᵐ x ∂(volume.restrict K),
      stepCost K delta (sigma ^ 2) x ≤ 2 * (ell K delta x)⁻¹ := by
  have hmul := adjustable_acceptance_multiplier hn hq hsigma hdelta hdeltaq hRsigma
  have hfloor := ae_restrict_acceptance_floor_le_speedyMetropolisMove
    (by positivity : (0:Real) < sigma ^ 2) hR hdelta hK hKR
  filter_upwards [hfloor] with x hx
  have hacc : (3 : ℝ≥0∞) ≤ 5 * speedyMetropolisMove K delta (sigma ^ 2) x :=
    hmul.trans (mul_le_mul_left' hx 5)
  have haccle : speedyMetropolisMove K delta (sigma ^ 2) x ≤ 1 :=
    speedyMetropolisMove_le_one K delta (sigma ^ 2) x
  have hfin : speedyMetropolisMove K delta (sigma ^ 2) x ≠ ⊤ :=
    (haccle.trans_lt ENNReal.one_lt_top).ne
  have hbt : (5 : ℝ≥0∞) * speedyMetropolisMove K delta (sigma ^ 2) x ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hfin
  have hr : (3:Real) ≤ 5 * (speedyMetropolisMove K delta (sigma ^ 2) x).toReal := by
    have h := ENNReal.toReal_mono hbt hacc
    simpa using h
  have hr2 : (1:Real) ≤ 2 * (speedyMetropolisMove K delta (sigma ^ 2) x).toReal := by
    linarith
  have hhalf : (1 : ℝ≥0∞) ≤ 2 * speedyMetropolisMove K delta (sigma ^ 2) x := by
    have heq : (2 : ℝ≥0∞) * speedyMetropolisMove K delta (sigma ^ 2) x
        = ENNReal.ofReal (2 * (speedyMetropolisMove K delta (sigma ^ 2) x).toReal) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hfin]
      norm_num
    rw [heq, show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    exact ENNReal.ofReal_le_ofReal hr2
  have hinv : (speedyMetropolisMove K delta (sigma ^ 2) x)⁻¹ ≤ 2 := by
    rw [ENNReal.inv_le_iff_le_mul (fun h => absurd h (by norm_num))
      (fun h => absurd h hfin), mul_comm]
    exact hhalf
  have hltop : ell K delta x ≠ ⊤ := ((ell_le_one K delta x).trans_lt ENNReal.one_lt_top).ne
  rw [stepCost, ENNReal.mul_inv (Or.inr hfin) (Or.inl hltop), mul_comm]
  exact mul_le_mul_right' hinv _

/-- **The `L^p(π)` bound on the per-step cost, at `p = 1 + 1/(2n)`.**

    `∫ ((ℓ·acc)⁻¹)^{1+1/(2n)} dπ  ≤  80`

an absolute constant.  This is the hypothesis `sum_lintegral_le_of_isWarm_holder` needs, and
it is the whole reason the Hölder route beats the plain warm bound: at `p = 1` the same
integral is the existing `10/3`, and the fractional moment says the `p`-th costs only a
bounded factor more. -/
theorem lintegral_stepCost_rpow_le
    (hn : 2 ≤ n) {q : Real} (hq : 1 < q)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hKvol : volume K ≠ ⊤)
    {delta sigma R : Real} (hdelta : 0 < delta) (hsigma : 0 < sigma)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    (hdeltaq : delta ≤ sigma / (max 8 (2 * q) * Real.sqrt n))
    (hR : 0 ≤ R) (hRsigma : R ≤ q * sigma * Real.sqrt n)
    (hKR : ∀ x, x ∈ K → ‖x‖ ≤ R) :
    ∫⁻ x, (stepCost K delta (sigma ^ 2) x) ^ holderP n
        ∂(ellGaussianProb K delta (sigma ^ 2)) ≤ 80 := by
  have hn0 : 0 < n := by omega
  have hpos : (0:Real) < holderP n := lt_of_lt_of_le zero_lt_one (one_le_holderP hn0)
  set pi := ellGaussianProb K delta (sigma ^ 2) with hpidef
  -- (1) the a.e. pointwise bound, transported to `pi`
  have hae0 := ae_stepCost_le_two_mul_inv_ell hn hq hK hdelta hsigma hdeltaq hR hRsigma hKR
  have hae : ∀ᵐ x ∂pi, stepCost K delta (sigma ^ 2) x ≤ 2 * (ell K delta x)⁻¹ :=
    hae0.filter_mono (ellGaussianProb_absolutelyContinuous K delta (sigma ^ 2)).ae_le
  -- (2) raise to the power `p`
  have hstep : ∀ᵐ x ∂pi, (stepCost K delta (sigma ^ 2) x) ^ holderP n
      ≤ 4 * (ell K delta x) ^ (-(1 + 1 / (2 * (n : Real)))) := by
    filter_upwards [hae] with x hx
    have h1 : (stepCost K delta (sigma ^ 2) x) ^ holderP n
        ≤ (2 * (ell K delta x)⁻¹) ^ holderP n := ENNReal.rpow_le_rpow hx hpos.le
    refine h1.trans ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ hpos.le]
    have h2 : ((ell K delta x)⁻¹) ^ holderP n
        = (ell K delta x) ^ (-(1 + 1 / (2 * (n : Real)))) := by
      rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg]
      rfl
    rw [h2]
    refine mul_le_mul_right' ?_ _
    calc (2 : ℝ≥0∞) ^ holderP n ≤ (2 : ℝ≥0∞) ^ (2 : Real) :=
          ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (holderP_le_two hn0)
      _ = 4 := by
          rw [show (2:Real) = ((2:ℕ) : Real) by norm_num, ENNReal.rpow_natCast]
          norm_num
  -- (3) the fractional-moment bridge
  have hmom := Arlib.MarkovChains.lintegral_ell_rpow_neg_ellGaussianProb_le
    (n := n) hK hKc hball hKvol hn0 hdelta hdeltan (by positivity : (0:Real) < sigma ^ 2)
  -- (4) the existing first moment
  have hfirst : 3 * ∫⁻ x, stepCost K delta (sigma ^ 2) x ∂pi ≤ 10 := by
    have h := three_mul_sum_lintegral_le_ten_mul_adjustable hn hq hK hKc hball hdelta hsigma
      hdeltan hdeltaq hR hRsigma hKR (M := 1) (mu := pi) (Arlib.IsWarm.refl pi) 1
    simpa [stepCost, Finset.sum_range_one, Arlib.MarkovChains.iterate_zero, hpidef] using h
  -- (5) `∫ ℓ⁻¹ dπ ≤ ∫ stepCost dπ`, because `acc ≤ 1`
  have hinvle : ∫⁻ x, (ell K delta x)⁻¹ ∂pi ≤ ∫⁻ x, stepCost K delta (sigma ^ 2) x ∂pi := by
    refine lintegral_mono fun x => ?_
    rw [stepCost]
    refine ENNReal.inv_le_inv.2 ?_
    calc ell K delta x * speedyMetropolisMove K delta (sigma ^ 2) x
        ≤ ell K delta x * 1 :=
          mul_le_mul_left' (speedyMetropolisMove_le_one K delta (sigma ^ 2) x) _
      _ = ell K delta x := mul_one _
  -- (6) assemble
  calc ∫⁻ x, (stepCost K delta (sigma ^ 2) x) ^ holderP n ∂pi
      ≤ ∫⁻ x, 4 * (ell K delta x) ^ (-(1 + 1 / (2 * (n : Real)))) ∂pi :=
        lintegral_mono_ae hstep
    _ = 4 * ∫⁻ x, (ell K delta x) ^ (-(1 + 1 / (2 * (n : Real)))) ∂pi := by
        rw [lintegral_const_mul' _ _ (by norm_num)]
    _ ≤ 4 * (ENNReal.ofReal 6 * ∫⁻ x, (ell K delta x)⁻¹ ∂pi) := mul_le_mul_left' hmom 4
    _ ≤ 4 * (ENNReal.ofReal 6 * ∫⁻ x, stepCost K delta (sigma ^ 2) x ∂pi) := by
        gcongr
    _ ≤ 80 := by
        have h6 : ENNReal.ofReal 6 = (6 : ℝ≥0∞) := by
          rw [show (6:Real) = ((6:ℕ) : Real) by norm_num, ENNReal.ofReal_natCast]
          norm_num
        rw [h6, ← mul_assoc]
        calc (4 : ℝ≥0∞) * 6 * ∫⁻ x, stepCost K delta (sigma ^ 2) x ∂pi
            = 8 * (3 * ∫⁻ x, stepCost K delta (sigma ^ 2) x ∂pi) := by
              rw [← mul_assoc]; norm_num
          _ ≤ 8 * 10 := mul_le_mul_left' hfirst 8
          _ = 80 := by norm_num

/-! ### Axiom audit -/

section AxiomCheck

#print axioms holderP_conjugate
#print axioms holderP_le_two
#print axioms one_le_holderP
#print axioms ellGaussianProb_absolutelyContinuous
#print axioms ae_stepCost_le_two_mul_inv_ell
#print axioms lintegral_stepCost_rpow_le

end AxiomCheck

end Ttc.CVHolderRetryCost
