/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.Probability.Chernoff
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.Constructions.Pi

/-! A multiplicative error bound for the number of planar hits, in Mathlib measure notation. -/

set_option autoImplicit false

noncomputable section

namespace ttc.Planar

open MeasureTheory ProbabilityTheory Arlib.Probability
open scoped ENNReal unitInterval

/-- Number of hits in a finite sequence of flags. -/
def hits {n : ℕ} (v : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i => v i = true).card

private def weight (p : I) (b : Bool) : ℝ := if b then p else 1 - p

private theorem weight_nonneg (p : I) (b : Bool) : 0 ≤ weight p b := by
  cases b <;> simp [weight, p.2.1, sub_nonneg.mpr p.2.2]

private theorem weight_sum (p : I) : ∑ b : Bool, weight p b = 1 := by
  rw [show (Finset.univ : Finset Bool) = {false, true} by decide]
  simp [weight]

private theorem real_bernoulli_singleton (p : I) (b : Bool) :
    (bernoulliMeasure true false p).real {b} = weight p b := by
  cases b <;> simp [bernoulliMeasure_real_apply, weight, unitInterval.coe_symm_eq]

/-- Chernoff for the ordinary product of Bernoulli measures. -/
theorem hits_chernoff (n : ℕ) (p : I) {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (Measure.pi fun _ : Fin n => bernoulliMeasure true false p).real
      {v | eps * ((n : ℝ) * p) < |(hits v : ℝ) - (n : ℝ) * p|} ≤
    2 * Real.exp (-(eps ^ 2 * ((n : ℝ) * p)) / 3) := by
  classical
  let μ := fun _ : Fin n => weight p
  let A := fun _ : Fin n => ({true} : Finset Bool)
  let ν := Measure.pi fun _ : Fin n => bernoulliMeasure true false p
  have hn : indicMean μ Finset.univ A = (n : ℝ) * p := by
    simp [indicMean, μ, A, weight, nsmul_eq_mul]
  have hc : ∀ v : Fin n → Bool, indicCount Finset.univ A v = hits v := by
    intro v
    simp [indicCount, hits, A]
  let F : Finset (Fin n → Bool) := Finset.univ.filter fun v =>
    eps * ((n : ℝ) * p) < |(hits v : ℝ) - (n : ℝ) * p|
  have hF : (F : Set (Fin n → Bool)) =
      {v | eps * ((n : ℝ) * p) < |(hits v : ℝ) - (n : ℝ) * p|} := by simp [F]
  have hv (v : Fin n → Bool) : ν.real {v} = ∏ j, weight p (v j) := by
    simp only [ν, measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
    exact Finset.prod_congr rfl (fun i _ => real_bernoulli_singleton p (v i))
  have H := chernoff_two_sided μ (fun _ => weight_nonneg p) (fun _ => weight_sum p)
    Finset.univ A heps heps1
  rw [hn] at H
  simp only [hc] at H
  change ν.real _ ≤ _
  rw [← hF, ← sum_measureReal_singleton F]
  simp only [hv]
  exact H

end ttc.Planar
