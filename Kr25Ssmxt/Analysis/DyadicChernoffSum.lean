import Kr25Ssmxt.Analysis.ThresholdTail

/-! The geometric summation step in the paper's union bound over all
admissible dyadic levels. -/

namespace Kr25Ssmxt

open Finset

theorem dyadic_poisson_chernoff_sum
    (a : Real) (ha : 0 ≤ a)
    (hhalf : Real.exp (-a) ≤ 1 / 2) (levels : Nat) :
    (∑ j ∈ range levels, 2 * Real.exp (-a * (2 : Real) ^ j)) ≤
      4 * Real.exp (-a) := by
  have hterm (j : Nat) :
      Real.exp (-a * (2 : Real) ^ j) ≤
        Real.exp (-a) * (1 / 2 : Real) ^ j := by
    have hpowNat : j + 1 ≤ 2 ^ j := Nat.lt_two_pow_self
    have hpow : ((j + 1 : Nat) : Real) ≤ (2 : Real) ^ j := by
      exact_mod_cast hpowNat
    have hpow' : (j : Real) + 1 ≤ (2 : Real) ^ j := by
      simpa only [Nat.cast_add, Nat.cast_one] using hpow
    have harg : -a * (2 : Real) ^ j ≤ -a * (j + 1) :=
      mul_le_mul_of_nonpos_left hpow' (by linarith)
    calc
      Real.exp (-a * (2 : Real) ^ j) ≤ Real.exp (-a * (j + 1)) :=
        Real.exp_le_exp.mpr harg
      _ = Real.exp (-a) * (Real.exp (-a)) ^ j := by
        rw [show -a * ((j : Real) + 1) = -a + (j : Real) * (-a) by ring,
          Real.exp_add, Real.exp_nat_mul]
      _ ≤ Real.exp (-a) * (1 / 2 : Real) ^ j := by
        gcongr
  calc
    (∑ j ∈ range levels, 2 * Real.exp (-a * (2 : Real) ^ j)) ≤
        ∑ j ∈ range levels,
          2 * Real.exp (-a) * (1 / 2 : Real) ^ j := by
      apply Finset.sum_le_sum
      intro j _
      nlinarith [hterm j]
    _ = 2 * Real.exp (-a) *
          (∑ j ∈ range levels, (1 / 2 : Real) ^ j) := by
      rw [Finset.mul_sum]
    _ ≤ 4 * Real.exp (-a) := by
      have hsum := sum_geometric_two_le levels
      nlinarith [Real.exp_nonneg (-a)]

theorem dyadic_poisson_chernoff_sum_reverse
    (a : Real) (ha : 0 ≤ a)
    (hhalf : Real.exp (-a) ≤ 1 / 2) (lastLevel : Nat) :
    (∑ j ∈ range (lastLevel + 1),
      2 * Real.exp (-a * (2 : Real) ^ (lastLevel - j))) ≤
      4 * Real.exp (-a) := by
  rw [show (fun j : Nat =>
      2 * Real.exp (-a * (2 : Real) ^ (lastLevel - j))) =
    (fun j => 2 * Real.exp (-a * (2 : Real) ^ j)) ∘
      (fun j => lastLevel + 1 - 1 - j) by
        funext j
        simp]
  exact (sum_range_reflect
    (fun j => 2 * Real.exp (-a * (2 : Real) ^ j))
    (lastLevel + 1)).trans_le
    (dyadic_poisson_chernoff_sum a ha hhalf (lastLevel + 1))

/-- The threshold chosen by Algorithm 1 bounds the entire sum of levelwise
Chernoff failures by its `δ/6` allocation. -/
theorem ApproxParams.dyadic_chernoff_budget
    (p : ApproxParams) (m lastLevel : Nat) :
    let a := (1 - p.ε') * p.ε' ^ 2 *
      p.Thresh m / 24
    (∑ j ∈ range (lastLevel + 1),
      2 * Real.exp (-a * (2 : Real) ^ (lastLevel - j))) ≤
      p.delta / 6 := by
  let a := (1 - p.ε') * p.ε' ^ 2 *
    p.Thresh m / 24
  have heps : p.ε' < 1 := by
    dsimp [ApproxParams.ε']
    linarith [p.epsilon_le_one]
  have ha : 0 ≤ a := by
    dsimp [a]
    have hfactor : 0 ≤ 1 - p.ε' := by linarith
    have hthreshold := p.threshold_pos m
    positivity
  have hbudget := p.concentration_tail_budget m
  have hbudget' : 4 * Real.exp (-a) ≤ p.delta / 6 := by
    have harg : -a =
        -(1 - p.ε') * p.ε' ^ 2 * p.Thresh m / 24 := by
      dsimp [a]
      ring
    rw [harg]
    exact hbudget
  have hhalf : Real.exp (-a) ≤ 1 / 2 := by
    nlinarith [hbudget', p.delta_le_one]
  exact (dyadic_poisson_chernoff_sum_reverse a ha hhalf lastLevel).trans
    hbudget'

end Kr25Ssmxt
