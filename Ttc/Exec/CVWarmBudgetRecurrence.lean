import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Explicit nonstationary warm-budget recurrence

The operational Gaussian path may have a warmness constant which compounds from one
phase to the next.  This is harmless for the retained-reference construction: the
operational constant is used only inside a logarithmic mixing deadline, while expected
cost is integrated against the separately chosen constant-warm reference law.

This file packages the exact recurrence and a finite-product envelope.  In particular,
it avoids the unsound inference that a random fallback makes the accepted contribution
constant: the accepted contribution remains `acceptedFactor i * warmBudget i`.
-/

set_option autoImplicit false

namespace Ttc.CVWarmBudgetRecurrence

open MeasureTheory Finset
open scoped ENNReal BigOperators

/-- Exact operational recurrence.  `acceptedFactor` includes the retry count and the
accepted cross-phase warm factor; `fallbackFactor` is the warmness of the independently
sampleable unresolved fallback. -/
noncomputable def recursiveWarmBudget
    (initial : ENNReal) (acceptedFactor fallbackFactor : Nat → ENNReal) :
    Nat → ENNReal
  | 0 => initial
  | i + 1 => acceptedFactor i *
      recursiveWarmBudget initial acceptedFactor fallbackFactor i + fallbackFactor i

@[simp] theorem recursiveWarmBudget_zero
    (initial : ENNReal) (acceptedFactor fallbackFactor : Nat → ENNReal) :
    recursiveWarmBudget initial acceptedFactor fallbackFactor 0 = initial := rfl

@[simp] theorem recursiveWarmBudget_succ
    (initial : ENNReal) (acceptedFactor fallbackFactor : Nat → ENNReal) (i : Nat) :
    recursiveWarmBudget initial acceptedFactor fallbackFactor (i + 1) =
      acceptedFactor i * recursiveWarmBudget initial acceptedFactor fallbackFactor i +
        fallbackFactor i := rfl

theorem one_le_recursiveWarmBudget
    {initial : ENNReal} {acceptedFactor fallbackFactor : Nat → ENNReal}
    (hinitial : 1 ≤ initial) (haccepted : ∀ i, 1 ≤ acceptedFactor i) :
    ∀ i, 1 ≤ recursiveWarmBudget initial acceptedFactor fallbackFactor i := by
  intro i
  induction i with
  | zero => simpa using hinitial
  | succ i ih =>
      rw [recursiveWarmBudget_succ]
      calc
        1 = 1 * 1 := by simp
        _ ≤ acceptedFactor i *
            recursiveWarmBudget initial acceptedFactor fallbackFactor i := by
              exact mul_le_mul (haccepted i) ih bot_le bot_le
        _ ≤ acceptedFactor i *
              recursiveWarmBudget initial acceptedFactor fallbackFactor i +
            fallbackFactor i := le_add_of_nonneg_right bot_le

theorem recursiveWarmBudget_ne_top
    {initial : ENNReal} {acceptedFactor fallbackFactor : Nat → ENNReal}
    (hinitial : initial ≠ ⊤) (haccepted : ∀ i, acceptedFactor i ≠ ⊤)
    (hfallback : ∀ i, fallbackFactor i ≠ ⊤) :
    ∀ i, recursiveWarmBudget initial acceptedFactor fallbackFactor i ≠ ⊤ := by
  intro i
  induction i with
  | zero => simpa using hinitial
  | succ i ih =>
      rw [recursiveWarmBudget_succ]
      exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (haccepted i) ih, hfallback i⟩

/-- Each additive fallback can be absorbed multiplicatively because every preceding
warm budget is at least one. -/
theorem recursiveWarmBudget_le_product
    {initial : ENNReal} {acceptedFactor fallbackFactor : Nat → ENNReal}
    (hinitial : 1 ≤ initial) (haccepted : ∀ i, 1 ≤ acceptedFactor i) :
    ∀ i, recursiveWarmBudget initial acceptedFactor fallbackFactor i ≤
      initial * ∏ j ∈ Finset.range i, (acceptedFactor j + fallbackFactor j) := by
  intro i
  induction i with
  | zero => simp [recursiveWarmBudget, hinitial]
  | succ i ih =>
      have hwarm := one_le_recursiveWarmBudget
        (fallbackFactor := fallbackFactor) hinitial haccepted i
      rw [recursiveWarmBudget_succ, Finset.prod_range_succ]
      calc
        acceptedFactor i *
              recursiveWarmBudget initial acceptedFactor fallbackFactor i +
            fallbackFactor i ≤
          acceptedFactor i *
              recursiveWarmBudget initial acceptedFactor fallbackFactor i +
            fallbackFactor i *
              recursiveWarmBudget initial acceptedFactor fallbackFactor i := by
                gcongr
                exact le_mul_of_one_le_right' hwarm
        _ = recursiveWarmBudget initial acceptedFactor fallbackFactor i *
              (acceptedFactor i + fallbackFactor i) := by
                rw [mul_add]
                ac_rfl
        _ ≤ (initial * ∏ j ∈ Finset.range i,
              (acceptedFactor j + fallbackFactor j)) *
            (acceptedFactor i + fallbackFactor i) := by
              exact mul_le_mul_right' ih _
        _ = initial * ((∏ j ∈ Finset.range i,
              (acceptedFactor j + fallbackFactor j)) *
            (acceptedFactor i + fallbackFactor i)) := by rw [mul_assoc]

/-- Real-valued form of the product envelope, ready for logarithmic deadline algebra. -/
theorem recursiveWarmBudget_toReal_le_product
    {initial : ENNReal} {acceptedFactor fallbackFactor : Nat → ENNReal}
    (hinitialOne : 1 ≤ initial) (hacceptedOne : ∀ i, 1 ≤ acceptedFactor i)
    (hinitialTop : initial ≠ ⊤) (hacceptedTop : ∀ i, acceptedFactor i ≠ ⊤)
    (hfallbackTop : ∀ i, fallbackFactor i ≠ ⊤) (i : Nat) :
    (recursiveWarmBudget initial acceptedFactor fallbackFactor i).toReal ≤
      initial.toReal * ∏ j ∈ Finset.range i,
        (acceptedFactor j + fallbackFactor j).toReal := by
  have hrecTop := recursiveWarmBudget_ne_top hinitialTop hacceptedTop hfallbackTop i
  have hfactorTop : ∀ j, acceptedFactor j + fallbackFactor j ≠ ⊤ :=
    fun j ↦ ENNReal.add_ne_top.2 ⟨hacceptedTop j, hfallbackTop j⟩
  have hprodTop :
      initial * ∏ j ∈ Finset.range i, (acceptedFactor j + fallbackFactor j) ≠ ⊤ := by
    apply ENNReal.mul_ne_top hinitialTop
    exact ENNReal.prod_ne_top fun j _ ↦ hfactorTop j
  have hle := ENNReal.toReal_mono hprodTop
    (recursiveWarmBudget_le_product hinitialOne hacceptedOne i)
  rw [ENNReal.toReal_mul, ENNReal.toReal_prod] at hle
  exact hle

/-- Taking logarithms turns the possibly compounding operational recurrence into an
additive phase sum.  This is the form consumed by the speedy-walk deadlines. -/
theorem log_recursiveWarmBudget_toReal_le_sum
    {initial : ENNReal} {acceptedFactor fallbackFactor : Nat → ENNReal}
    (hinitialOne : 1 ≤ initial) (hacceptedOne : ∀ i, 1 ≤ acceptedFactor i)
    (hinitialTop : initial ≠ ⊤) (hacceptedTop : ∀ i, acceptedFactor i ≠ ⊤)
    (hfallbackTop : ∀ i, fallbackFactor i ≠ ⊤) (i : Nat) :
    Real.log (recursiveWarmBudget initial acceptedFactor fallbackFactor i).toReal ≤
      Real.log initial.toReal + ∑ j ∈ Finset.range i,
        Real.log (acceptedFactor j + fallbackFactor j).toReal := by
  have hrecOne := one_le_recursiveWarmBudget
    (fallbackFactor := fallbackFactor) hinitialOne hacceptedOne i
  have hrecTop := recursiveWarmBudget_ne_top hinitialTop hacceptedTop hfallbackTop i
  have hrecPos : 0 <
      (recursiveWarmBudget initial acceptedFactor fallbackFactor i).toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one hrecOne)) hrecTop
  have hinitPos : 0 < initial.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one hinitialOne)) hinitialTop
  have hfactorTop : ∀ j, acceptedFactor j + fallbackFactor j ≠ ⊤ :=
    fun j ↦ ENNReal.add_ne_top.2 ⟨hacceptedTop j, hfallbackTop j⟩
  have hfactorPos : ∀ j, 0 < (acceptedFactor j + fallbackFactor j).toReal := by
    intro j
    have hone : 1 ≤ acceptedFactor j + fallbackFactor j :=
      (hacceptedOne j).trans (le_add_of_nonneg_right bot_le)
    exact ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one hone))
      (hfactorTop j)
  have hprodPos : 0 < ∏ j ∈ Finset.range i,
      (acceptedFactor j + fallbackFactor j).toReal := by
    exact Finset.prod_pos fun j _ ↦ hfactorPos j
  have hbound := recursiveWarmBudget_toReal_le_product hinitialOne hacceptedOne
    hinitialTop hacceptedTop hfallbackTop i
  have hlog := Real.log_le_log hrecPos hbound
  rw [Real.log_mul hinitPos.ne' hprodPos.ne',
    Real.log_prod (fun j _ ↦ (hfactorPos j).ne')] at hlog
  exact hlog

#print axioms one_le_recursiveWarmBudget
#print axioms recursiveWarmBudget_ne_top
#print axioms recursiveWarmBudget_le_product
#print axioms recursiveWarmBudget_toReal_le_product
#print axioms log_recursiveWarmBudget_toReal_le_sum

end Ttc.CVWarmBudgetRecurrence
