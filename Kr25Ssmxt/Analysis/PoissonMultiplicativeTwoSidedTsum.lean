import Kr25Ssmxt.Analysis.PadeLog
import Arlib.Probability.Poisson

/-!
# Multiplicative two-sided Poisson concentration

This is the explicit-PMF Chernoff calculation used before converting the sum to a
`poissonMeasure` event.
-/

noncomputable section

open scoped BigOperators

namespace Kr25Ssmxt

/--
The explicit Poisson mass outside a multiplicative error window has the usual
two-sided Chernoff bound.

INTERNAL: Explicit-PMF form of the Poisson concentration step used at analysis.tex:240-242.
-/
lemma poisson_multiplicative_two_sided_tsum (mu epsilon : Real)
    (hmu : 0 < mu) (hepsilon : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1) :
    ∑' k : Nat, (if epsilon * mu ≤ |(k : Real) - mu| then
      Arlib.Probability.poissonPMF mu k else 0) ≤
      2 * Real.exp (-mu * epsilon ^ 2 / 3) := by
  let a := epsilon * mu
  have ha : 0 < a := mul_pos hepsilon hmu
  have hamu : a ≤ mu := by
    dsimp [a]
    exact mul_le_of_le_one_left hmu.le hepsilon_le_one
  have hp : ∀ k, 0 ≤ Arlib.Probability.poissonPMF mu k :=
    Arlib.Probability.poissonPMF_nonneg hmu.le
  have hsu : Summable (fun k : Nat => if mu + a ≤ (k : Real) then
      Arlib.Probability.poissonPMF mu k else 0) :=
    Arlib.Probability.summable_ite_poissonPMF hmu.le _
  have hsl : Summable (fun k : Nat => if (k : Real) ≤ mu - a then
      Arlib.Probability.poissonPMF mu k else 0) :=
    Arlib.Probability.summable_ite_poissonPMF hmu.le _
  have hsa : Summable (fun k : Nat => if a ≤ |(k : Real) - mu| then
      Arlib.Probability.poissonPMF mu k else 0) :=
    Arlib.Probability.summable_ite_poissonPMF hmu.le _
  have hone : 1 < 1 + epsilon := by linarith
  have hlog : 0 < Real.log (1 + epsilon) := Real.log_pos hone
  have hden : 0 < 2 + epsilon := by linarith
  have hpade := pade_log_bound
    (t := 1 + epsilon) (by linarith : 1 ≤ 1 + epsilon)
  have hlog_lower : 2 * epsilon / (2 + epsilon) ≤ Real.log (1 + epsilon) := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hparent :
      epsilon - (1 + epsilon) * Real.log (1 + epsilon) ≤
        -epsilon ^ 2 / 3 := by
    have hmul := mul_le_mul_of_nonneg_left hlog_lower (by linarith : 0 ≤ 1 + epsilon)
    calc
      epsilon - (1 + epsilon) * Real.log (1 + epsilon) ≤
          epsilon - (1 + epsilon) * (2 * epsilon / (2 + epsilon)) :=
        sub_le_sub_left hmul epsilon
      _ = -epsilon ^ 2 / (2 + epsilon) := by
        field_simp
        ring
      _ ≤ -epsilon ^ 2 / 3 := by
        apply (div_le_div_iff₀ hden (by norm_num : (0 : Real) < 3)).2
        nlinarith [sq_nonneg epsilon]
  have hupper :
      ∑' k : Nat, (if mu + a ≤ (k : Real) then
          Arlib.Probability.poissonPMF mu k else 0) ≤
        Real.exp (-mu * epsilon ^ 2 / 3) := by
    refine (Arlib.Probability.poisson_upper_tail_tilt hmu.le hlog).trans ?_
    apply Real.exp_le_exp.mpr
    rw [Real.exp_log (by linarith : 0 < 1 + epsilon)]
    have hmul := mul_le_mul_of_nonneg_left hparent hmu.le
    dsimp [a]
    nlinarith
  have hlower :
      ∑' k : Nat, (if (k : Real) ≤ mu - a then
          Arlib.Probability.poissonPMF mu k else 0) ≤
        Real.exp (-mu * epsilon ^ 2 / 3) := by
    refine (Arlib.Probability.poisson_tail_lower hmu ha hamu).trans ?_
    apply Real.exp_le_exp.mpr
    have hmu_ne : mu ≠ 0 := ne_of_gt hmu
    dsimp [a]
    field_simp
    nlinarith [sq_nonneg epsilon]
  change (∑' k : Nat, (if a ≤ |(k : Real) - mu| then
    Arlib.Probability.poissonPMF mu k else 0)) ≤ _
  calc
    ∑' k : Nat, (if a ≤ |(k : Real) - mu| then
        Arlib.Probability.poissonPMF mu k else 0) ≤
        ∑' k : Nat, ((if mu + a ≤ (k : Real) then
          Arlib.Probability.poissonPMF mu k else 0) +
          (if (k : Real) ≤ mu - a then Arlib.Probability.poissonPMF mu k else 0)) :=
      Summable.tsum_le_tsum
        (fun k => Arlib.Probability.ite_abs_le_add_ite hp mu a k) hsa (hsu.add hsl)
    _ = (∑' k : Nat, (if mu + a ≤ (k : Real) then
          Arlib.Probability.poissonPMF mu k else 0)) +
        ∑' k : Nat, (if (k : Real) ≤ mu - a then
          Arlib.Probability.poissonPMF mu k else 0) := Summable.tsum_add hsu hsl
    _ ≤ 2 * Real.exp (-mu * epsilon ^ 2 / 3) := by nlinarith

end Kr25Ssmxt
