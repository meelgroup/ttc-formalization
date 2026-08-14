/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.LazyProperProposalCost
import Arlib.MarkovChains.Continuous.AdjustableRadiusSampler

/-!
# Adjustable-radius expected cost for lazy proper-proposal Gaussian walks

At radius `R <= q*σ*sqrt n`, the step restriction

`δ <= σ / (max 8 (2*q) * sqrt n)`

keeps `2Rδ <= σ²` and retains the same `3/5` acceptance floor as radius four.  Consequently
the expected proposal-count constant does not grow with `q`; `q` enters the mixing deadline
quadratically through `(max 8 (2*q))²`.  The unconditional wasted-step estimate additionally
needs `δ <= 1/(2n)`, exactly as the adjustable sampler's operational step uses the minimum of
these two restrictions.
-/

namespace Ttc.AdjustableLazyProperCost

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains
open Ttc.LazyProperCost
open scoped ENNReal

variable {n : Nat}

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-! ## Adjustable acceptance and wasted-step arithmetic -/

/-- The numeric acceptance multiplier consumed by the cost proof.  Despite the adjustable
radius, the smaller `q`-dependent step retains the constant `3/5` floor. -/
theorem adjustable_acceptance_multiplier
    (hn : 2 <= n) {q sigma delta R : Real} (hq : 1 < q)
    (hsigma : 0 < sigma) (hdelta : 0 < delta)
    (hdeltaq : delta <= sigma / (max 8 (2 * q) * Real.sqrt n))
    (hRsigma : R <= q * sigma * Real.sqrt n) :
    (3 : ENNReal) <= 5 * ENNReal.ofReal
      (Real.exp (-(2 * R * delta + delta ^ 2) / (2 * sigma ^ 2))) :=
  three_le_five_mul_acceptance_floor_adjustable hn hq hsigma hdelta hdeltaq hRsigma

/-- Adjustable-radius analogue of the radius-four `10/3` wasted-step estimate.  The
constant is independent of `q`; the necessary compensation is the smaller step size. -/
theorem three_mul_sum_lintegral_le_ten_mul_adjustable
    (hn : 2 <= n) {q : Real} (hq : 1 < q)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K)
    {delta sigma R : Real} (hdelta : 0 < delta) (hsigma : 0 < sigma)
    (hdeltan : delta <= 1 / (2 * (n : Real)))
    (hdeltaq : delta <= sigma / (max 8 (2 * q) * Real.sqrt n))
    (hR : 0 <= R) (hRsigma : R <= q * sigma * Real.sqrt n)
    (hKR : ∀ x, x ∈ K -> ‖x‖ <= R)
    {M : ENNReal} {mu : Measure (State n)}
    (hwarm : IsWarm M mu (ellGaussianProb K delta (sigma ^ 2))) (t : Nat) :
    3 * ∑ i ∈ Finset.range t,
        ∫⁻ x, (ell K delta x * speedyMetropolisMove K delta (sigma ^ 2) x)⁻¹
          ∂iterate (speedyMetropolisGaussian K delta (sigma ^ 2)) mu i
      <= 10 * ((t : ENNReal) * M) := by
  have huncond :=
    mul_sum_lintegral_inv_ell_mul_move_iterate_speedyMetropolisGaussian_le_uncond
      (by omega : 1 <= n) hK hKc hball hdelta hdeltan (by positivity : 0 < sigma ^ 2)
      hR hKR hwarm t
  have hfloor := adjustable_acceptance_multiplier hn hq hsigma hdelta hdeltaq hRsigma
  calc
    3 * ∑ i ∈ Finset.range t,
        ∫⁻ x, (ell K delta x * speedyMetropolisMove K delta (sigma ^ 2) x)⁻¹
          ∂iterate (speedyMetropolisGaussian K delta (sigma ^ 2)) mu i
      <= 5 * ENNReal.ofReal
          (Real.exp (-(2 * R * delta + delta ^ 2) / (2 * sigma ^ 2))) *
        ∑ i ∈ Finset.range t,
          ∫⁻ x, (ell K delta x * speedyMetropolisMove K delta (sigma ^ 2) x)⁻¹
            ∂iterate (speedyMetropolisGaussian K delta (sigma ^ 2)) mu i := by gcongr
    _ = 5 * (ENNReal.ofReal
          (Real.exp (-(2 * R * delta + delta ^ 2) / (2 * sigma ^ 2))) *
        ∑ i ∈ Finset.range t,
          ∫⁻ x, (ell K delta x * speedyMetropolisMove K delta (sigma ^ 2) x)⁻¹
            ∂iterate (speedyMetropolisGaussian K delta (sigma ^ 2)) mu i) := by ring
    _ <= 5 * (2 * ((t : ENNReal) * M)) := by gcongr
    _ = 10 * ((t : ENNReal) * M) := by ring

/-! ## Honest lazy execution -/

/-- Adjustable-radius expected cost for the Ionescu--Tulcea lazy proper-proposal execution.
The cost coordinate is the realized number of ordinary proposals. -/
theorem six_mul_lintegral_lazyProperTotalCost_le_ten_mul_adjustable
    (hn : 2 <= n) {q : Real} (hq : 1 < q)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K)
    {delta sigma R : Real} (hdelta : 0 < delta) (hsigma : 0 < sigma)
    (hdeltan : delta <= 1 / (2 * (n : Real)))
    (hdeltaq : delta <= sigma / (max 8 (2 * q) * Real.sqrt n))
    (hR : 0 <= R) (hRsigma : R <= q * sigma * Real.sqrt n)
    (hKR : ∀ x, x ∈ K -> ‖x‖ <= R)
    {M : ENNReal} {mu : Measure (State n)} [IsProbabilityMeasure mu]
    (hwarm : IsWarm M mu (ellGaussianProb K delta (sigma ^ 2))) (t : Nat) :
    6 * (∫⁻ omega, Ttc.SequentialCost.totalCost t omega
        ∂lazyProperExecution K hK delta (sigma ^ 2) mu) <=
      10 * ((t : ENNReal) * M) := by
  let P := lazy (speedyMetropolisGaussian K delta (sigma ^ 2))
  let pi := ellGaussianProb K delta (sigma ^ 2)
  let f : State n -> ENNReal :=
    fun x => (ell K delta x * speedyMetropolisMove K delta (sigma ^ 2) x)⁻¹
  let sumCost : ENNReal := ∑ i ∈ Finset.range t, ∫⁻ x, f x ∂iterate P mu i
  have hcost := lintegral_lazyProperTotalCost_le_half_exitMeanSum
    hK delta (sigma ^ 2) mu t
  have hinv : Kernel.Invariant P pi := by
    exact (isReversible_lazy
      (isReversible_speedyMetropolisGaussian_prob hK delta (sigma ^ 2))).invariant
  have hsum : sumCost <= (t : ENNReal) * (M * ∫⁻ x, f x ∂pi) := by
    exact sum_lintegral_iterate_le_of_isWarm hwarm (step_invariant hinv) f t
  have hstationary : 3 * (∫⁻ x, f x ∂pi) <= 10 := by
    have h := three_mul_sum_lintegral_le_ten_mul_adjustable hn hq hK hKc hball
      hdelta hsigma hdeltan hdeltaq hR hRsigma hKR
      (M := (1 : ENNReal)) (mu := pi) (IsWarm.refl pi) 1
    simpa only [f, pi, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Arlib.MarkovChains.iterate_zero, Nat.cast_one, one_mul, mul_one] using h
  have hsixhalf : (6 : ENNReal) * (2 : ENNReal)⁻¹ = 3 := by
    rw [show (6 : ENNReal) = ENNReal.ofReal 6 by norm_num,
      show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num,
      <- ENNReal.ofReal_inv_of_pos (by norm_num : (0 : Real) < 2),
      <- ENNReal.ofReal_mul (by norm_num : (0 : Real) <= 6)]
    norm_num
  calc
    6 * (∫⁻ omega, Ttc.SequentialCost.totalCost t omega
        ∂lazyProperExecution K hK delta (sigma ^ 2) mu)
      <= 6 * ((2 : ENNReal)⁻¹ * sumCost) := by
        exact mul_le_mul_right (by simpa only [sumCost, f, P] using hcost) 6
    _ = 3 * sumCost := by rw [<- mul_assoc, hsixhalf]
    _ <= 3 * ((t : ENNReal) * (M * ∫⁻ x, f x ∂pi)) := by gcongr
    _ = ((t : ENNReal) * M) * (3 * ∫⁻ x, f x ∂pi) := by ring
    _ <= ((t : ENNReal) * M) * 10 := by gcongr
    _ = 10 * ((t : ENNReal) * M) := by ring

/-! ## Visible quadratic dependence in the mixing deadline -/

/-- The real-valued adjustable mixing deadline used by the sampler. -/
noncomputable def adjustableMixingDeadline
    (n : Nat) (q M eps : Real) : Real :=
  4 * 640 ^ 2 * (max 8 (2 * q)) ^ 2 * (n : Real) ^ 2 *
    (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 + 1

/-- Once `q >= 4`, the adjustable factor is exactly quadratic in `q`. -/
theorem adjustableMixingDeadline_eq_quadratic
    {q M eps : Real} (hq : 4 <= q) :
    adjustableMixingDeadline n q M eps =
      16 * 640 ^ 2 * q ^ 2 * (n : Real) ^ 2 *
        (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 + 1 := by
  have hmax : max 8 (2 * q) = 2 * q := max_eq_right (by linarith)
  rw [adjustableMixingDeadline, hmax]
  ring

/-! ### Axiom audit -/

#print axioms adjustable_acceptance_multiplier
#print axioms three_mul_sum_lintegral_le_ten_mul_adjustable
#print axioms six_mul_lintegral_lazyProperTotalCost_le_ten_mul_adjustable
#print axioms adjustableMixingDeadline_eq_quadratic

end Ttc.AdjustableLazyProperCost
