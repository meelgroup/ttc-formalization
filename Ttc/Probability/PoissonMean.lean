/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Probability.Trajectory

/-!
# The mean of a Poisson measure

`∫⁻ k, k ∂Po(r) = r`, in `ℝ≥0∞`.

Mathlib has `ProbabilityTheory.integral_poissonMeasure` for Bochner integrals of
`f : ℕ → E`, but nothing that evaluates the mean, and nothing in `ℝ≥0∞`.  The cost analysis
needs the `ℝ≥0∞` form: `Ttc.levelLaw θ j` is a product of `Po(θᵢ/2ʲ)`, so the expected
number of surviving lattice points at level `j` is `∑ᵢ θᵢ/2ʲ`, and that sum over `j` is the
geometric series which pays for the thinning passes.

`DnfstreamXt/Analysis/ThinMean.lean` writes its own analogue for the same reason.

The proof is the textbook reindex: `n · rⁿ/n! = r · r^{n-1}/(n-1)!` for `n ≥ 1` and `0` at
`n = 0`, so the series is `r` times Mathlib's `hasSum_one_poissonMeasure`.
-/

namespace Ttc

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- **The Poisson series has mean `r`.**  The real-valued form. -/
theorem hasSum_poissonMean (r : ℝ≥0) :
    HasSum (fun n : ℕ ↦ (n : ℝ) * (Real.exp (-r) * (r : ℝ) ^ n / (Nat.factorial n))) (r : ℝ) := by
  have h1 : HasSum (fun m : ℕ ↦ (r : ℝ) * (Real.exp (-r) * (r : ℝ) ^ m / (Nat.factorial m)))
      ((r : ℝ) * 1) := (hasSum_one_poissonMeasure r).mul_left _
  rw [mul_one] at h1
  have hshift : (fun m : ℕ ↦
        (fun n : ℕ ↦ (n : ℝ) * (Real.exp (-r) * (r : ℝ) ^ n / (Nat.factorial n))) (m + 1))
      = fun m : ℕ ↦ (r : ℝ) * (Real.exp (-r) * (r : ℝ) ^ m / (Nat.factorial m)) := by
    funext m
    have hm : ((Nat.factorial (m+1) : ℕ) : ℝ) = ((m : ℝ) + 1) * ((Nat.factorial m) : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hf : ((Nat.factorial m) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
    have hne : ((m : ℝ) + 1) ≠ 0 := by positivity
    simp only [hm]
    push_cast
    field_simp
    ring
  have h2 : HasSum (fun m : ℕ ↦
      (fun n : ℕ ↦ (n : ℝ) * (Real.exp (-r) * (r : ℝ) ^ n / (Nat.factorial n))) (m + 1)) (r : ℝ) := by
    rw [hshift]; exact h1
  have h3 := (hasSum_nat_add_iff
    (f := fun n : ℕ ↦ (n : ℝ) * (Real.exp (-r) * (r : ℝ) ^ n / (Nat.factorial n))) 1).mp h2
  simpa using h3

/-- **The Poisson mean, in `ℝ≥0∞`.**  This is the form the cost analysis consumes. -/
theorem lintegral_poissonMeasure_id (r : ℝ≥0) :
    (∫⁻ k, (k : ℝ≥0∞) ∂poissonMeasure r) = (r : ℝ≥0∞) := by
  have hterm : ∀ n : ℕ,
      (∫⁻ k, (k : ℝ≥0∞)
        ∂(ENNReal.ofReal (Real.exp (-r) * (r : ℝ) ^ n / (Nat.factorial n)) •
            Measure.dirac n))
        = ENNReal.ofReal ((n : ℝ) * (Real.exp (-r) * (r : ℝ) ^ n / (Nat.factorial n))) := by
    intro n
    rw [lintegral_smul_measure, lintegral_dirac,
      ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (n : ℝ)), ENNReal.ofReal_natCast]
    ring
  rw [poissonMeasure, lintegral_sum_measure]
  simp only [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity)
      (hasSum_poissonMean r).summable,
    (hasSum_poissonMean r).tsum_eq, ENNReal.ofReal_coe_nnreal]

#print axioms hasSum_poissonMean
#print axioms lintegral_poissonMeasure_id

end Ttc
