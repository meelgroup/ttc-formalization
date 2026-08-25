import Arlib.Probability.Poisson
import Arlib.MarkovChains.Techniques.Pinsker

/-!
# A sharp two-sided Poisson tail

This module combines the standard lower Chernoff tail with a logarithmically tilted
upper tail and the Padé lower bound for `log`.
-/

noncomputable section

namespace Kr25Ssmxt

/-- The Padé logarithm bound sharpens the upper Chernoff tail enough that it can be
combined with the standard lower tail at every relative error up to one.

PAPER: sections/analysis.tex:240-242
-/
lemma poisson_two_sided_tail_pade {mu a : Real}
    (hmu : 0 < mu) (ha : 0 < a) (hamu : a ≤ mu) :
    ∑' k : Nat, (if a ≤ |(k : Real) - mu| then Arlib.Probability.poissonPMF mu k else 0) ≤
      2 * Real.exp (-a ^ 2 / (2 * mu + a)) := by
  have hs_arg : 0 < 1 + a / mu := by positivity
  let s := Real.log (1 + a / mu)
  have hs : 0 < s := Real.log_pos (by
    dsimp [s]
    have : 0 < a / mu := div_pos ha hmu
    linarith)
  have hexp : Real.exp s = 1 + a / mu := by
    dsimp [s]
    exact Real.exp_log hs_arg
  have hpad := Arlib.MarkovChains.two_mul_sub_le_add_one_mul_log
    (t := 1 + a / mu) (by
      have : 0 ≤ a / mu := (div_pos ha hmu).le
      linarith)
  have hscaled : 2 * a ≤ (2 * mu + a) * s := by
    change 2 * ((1 + a / mu) - 1) ≤ ((1 + a / mu) + 1) * s at hpad
    have h := mul_le_mul_of_nonneg_left hpad hmu.le
    calc
      2 * a = mu * (2 * ((1 + a / mu) - 1)) := by field_simp; ring
      _ ≤ mu * (((1 + a / mu) + 1) * s) := h
      _ = (2 * mu + a) * s := by field_simp; ring
  have hupper_exp :
      mu * (Real.exp s - 1) - s * (mu + a) ≤ -a ^ 2 / (2 * mu + a) := by
    have hmean : mu * (Real.exp s - 1) = a := by
      rw [hexp]
      field_simp
    rw [hmean]
    apply (le_div_iff₀ (by linarith : 0 < 2 * mu + a)).2
    have hmul := mul_le_mul_of_nonneg_left hscaled (by linarith : 0 ≤ mu + a)
    nlinarith
  have hupper :
      ∑' k : Nat, (if mu + a ≤ (k : Real) then Arlib.Probability.poissonPMF mu k else 0) ≤
        Real.exp (-a ^ 2 / (2 * mu + a)) :=
    (Arlib.Probability.poisson_upper_tail_tilt hmu.le hs).trans
      (Real.exp_le_exp.mpr hupper_exp)
  have hlower_exp : -a ^ 2 / (2 * mu) ≤ -a ^ 2 / (2 * mu + a) := by
    rw [div_le_div_iff₀ (by positivity : 0 < 2 * mu) (by positivity : 0 < 2 * mu + a)]
    nlinarith [sq_nonneg a]
  have hlower :
      ∑' k : Nat, (if (k : Real) ≤ mu - a then Arlib.Probability.poissonPMF mu k else 0) ≤
        Real.exp (-a ^ 2 / (2 * mu + a)) :=
    (Arlib.Probability.poisson_tail_lower hmu ha hamu).trans
      (Real.exp_le_exp.mpr hlower_exp)
  have hp : ∀ k, 0 ≤ Arlib.Probability.poissonPMF mu k :=
    Arlib.Probability.poissonPMF_nonneg hmu.le
  have hsu := Arlib.Probability.summable_ite_poissonPMF hmu.le
    (fun k : Nat ⇒ mu + a ≤ (k : Real))
  have hsl := Arlib.Probability.summable_ite_poissonPMF hmu.le
    (fun k : Nat ⇒ (k : Real) ≤ mu - a)
  have hsa := Arlib.Probability.summable_ite_poissonPMF hmu.le
    (fun k : Nat ⇒ a ≤ |(k : Real) - mu|)
  calc
    ∑' k : Nat, (if a ≤ |(k : Real) - mu| then Arlib.Probability.poissonPMF mu k else 0)
        ≤ ∑' k : Nat,
            ((if mu + a ≤ (k : Real) then Arlib.Probability.poissonPMF mu k else 0) +
             (if (k : Real) ≤ mu - a then Arlib.Probability.poissonPMF mu k else 0)) :=
      Summable.tsum_le_tsum
        (fun k ⇒ Arlib.Probability.ite_abs_le_add_ite hp mu a k) hsa (hsu.add hsl)
    _ = (∑' k : Nat,
          (if mu + a ≤ (k : Real) then Arlib.Probability.poissonPMF mu k else 0)) +
        ∑' k : Nat,
          (if (k : Real) ≤ mu - a then Arlib.Probability.poissonPMF mu k else 0) :=
      Summable.tsum_add hsu hsl
    _ ≤ 2 * Real.exp (-a ^ 2 / (2 * mu + a)) := by linarith

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · combined the Padé-tilted upper tail with the existing lower tail
-/
