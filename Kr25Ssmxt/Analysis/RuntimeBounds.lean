import Kr25Ssmxt.Analysis.RuntimeBudgets
import Kr25Ssmxt.Analysis.PrecisionChoice
import Kr25Ssmxt.Analysis.PrecisionRequirements
import Kr25Ssmxt.Analysis.ReferenceProgram
import Kr25Ssmxt.Analysis.TTCPaperRuntime
import Kr25Ssmxt.Analysis.ComponentExpectation
import Kr25Ssmxt.Analysis.CV18RoundnessBound
import Kr25Ssmxt.Analysis.NormalizedDiameterRuntime
import Kr25Ssmxt.Analysis.ThresholdCapBound
import Kr25Ssmxt.Analysis.UniformBudgetAlgebra

namespace Kr25Ssmxt

open MeasureTheory

/-- Expected arithmetic-operation cost of the concrete charged paper TTC
program, with preprocessing and every component's explicit budget included. -/
theorem ttc_expected_runtime_explicit {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations cv18NonQueryFactor : Nat) :
    let D := prep.run F hbounded
    let b := (prep.choosePrecision D p).value
    ∫⁻ result, (result.2 : ENNReal) ∂
      ttcRefWithCost hn F hbounded p prep
        preprocessingOperations cv18NonQueryFactor ≤
      preprocessingOperations +
        ∑ i : Fin D.componentCount,
          TTCRuntime.expectedComponentBudget hn p D.componentCount b
            cv18NonQueryFactor (D.component i) := by
  exact community_expected_cost_explicit hn F hbounded p prep
    preprocessingOperations cv18NonQueryFactor

/-- Whole-run expected arithmetic cost with the normalized sampler deadline
expressed through `ρ`, `b`, and `R_max`, using the imported mixing theorem. -/
theorem ttc_expected_runtime_geometric {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations cv18NonQueryFactor : Nat) :
    let D := prep.run F hbounded
    let b := (prep.choosePrecision D p).value
    ∫⁻ result, (result.2 : ENNReal) ∂
      ttcRefWithCost hn F hbounded p prep
        preprocessingOperations cv18NonQueryFactor ≤
      preprocessingOperations +
        ∑ i : Fin D.componentCount,
          TTCRuntime.expectedComponentBudgetGeometric hn D p b
            cv18NonQueryFactor i := by
  dsimp only
  let D := prep.run F hbounded
  let choice := prep.choosePrecision D p
  have hbase := ttc_expected_runtime_explicit hn F hbounded p prep
    preprocessingOperations cv18NonQueryFactor
  dsimp only at hbase
  calc
    _ ≤ (preprocessingOperations : ENNReal) +
        ∑ i : Fin D.componentCount,
          TTCRuntime.expectedComponentBudget hn p
            D.componentCount choice.value cv18NonQueryFactor (D.component i) := hbase
    _ ≤ _ := by
      gcongr
      exact TTCRuntime.expectedComponentBudget_le_geometric
        hn D p choice.value cv18NonQueryFactor choice.adequate _

/-- Expected arithmetic cost of the paper TTC run with both imported
oracle schedules substituted into the per-component budget. -/
theorem ttc_expected_runtime_theorem3_expanded {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations cv18NonQueryFactor : Nat) :
    let D := prep.run F hbounded
    let b := (prep.choosePrecision D p).value
    ∫⁻ result, (result.2 : ENNReal) ∂
      ttcRefWithCost hn F hbounded p prep
        preprocessingOperations cv18NonQueryFactor ≤
      preprocessingOperations +
        ∑ i : Fin D.componentCount,
          TTCRuntime.expectedComponentBudgetTheorem3 hn D p b
            cv18NonQueryFactor i := by
  dsimp only
  let D := prep.run F hbounded
  let b := (prep.choosePrecision D p).value
  have hbase := ttc_expected_runtime_geometric hn F hbounded p prep
    preprocessingOperations cv18NonQueryFactor
  dsimp only at hbase
  calc
    _ ≤ (preprocessingOperations : ENNReal) +
        ∑ i : Fin D.componentCount,
          TTCRuntime.expectedComponentBudgetGeometric hn D p b
            cv18NonQueryFactor i := hbase
    _ ≤ _ := by
      gcongr
      exact TTCRuntime.expectedComponentBudgetGeometric_le_theorem3
        hn D p b cv18NonQueryFactor _

/-- The fixed CV18 non-query charge requested for Theorem 3: one
membership-equivalent allowance per query and for setup. -/
theorem ttc_expected_runtime_theorem3_fixed_charge {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations : Nat) :
    let D := prep.run F hbounded
    let b := (prep.choosePrecision D p).value
    ∫⁻ result, (result.2 : ENNReal) ∂
      ttcRefWithCost hn F hbounded p prep
        preprocessingOperations 1 ≤
      preprocessingOperations +
        ∑ i : Fin D.componentCount,
          TTCRuntime.expectedComponentBudgetTheorem3 hn D p b 1 i := by
  exact ttc_expected_runtime_theorem3_expanded hn F hbounded p prep
    preprocessingOperations 1

/-- Uniform finite-component form, exposing the paper's leading `m`.
The CV18 logarithmic maximum is over actual normalized components. -/
theorem ttc_expected_runtime_uniform_budget {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations : Nat) :
    let D := prep.run F hbounded
    let b := (prep.choosePrecision D p).value
    ∫⁻ result, (result.2 : ENNReal) ∂
      ttcRefWithCost hn F hbounded p prep
        preprocessingOperations 1 ≤
      preprocessingOperations + (D.componentCount : ENNReal) *
        TTCRuntime.theorem3UniformComponentBudget hn D p b 1 := by
  dsimp only
  let D := prep.run F hbounded
  let b := (prep.choosePrecision D p).value
  have hbase := ttc_expected_runtime_theorem3_fixed_charge hn F hbounded p prep
    preprocessingOperations
  dsimp only at hbase
  calc
    _ ≤ (preprocessingOperations : ENNReal) +
        ∑ i : Fin D.componentCount,
          TTCRuntime.expectedComponentBudgetTheorem3 hn D p b 1 i := hbase
    _ ≤ (preprocessingOperations : ENNReal) +
        ∑ _i : Fin D.componentCount,
          TTCRuntime.theorem3UniformComponentBudget hn D p b 1 := by
      gcongr
      exact TTCRuntime.expectedComponentBudgetTheorem3_le_uniform
        hn D p b 1 _
    _ = _ := by simp [D, b]

/-- Corrected expected arithmetic-operation bound for the costed paper
TTC execution. The explicit parameter factor contains the CV18 scheduled
logarithmic product and the Hit-and-Run mixing logarithm. -/
theorem ttc_expected_runtime_theorem3_headline_scale {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations : Nat) :
    let D := prep.run F hbounded
    let b := (prep.choosePrecision D p).value
    ∫⁻ result, (result.2 : ENNReal) ∂
      ttcRefWithCost hn F hbounded p prep
        preprocessingOperations 1 ≤
      preprocessingOperations + (D.componentCount : ENNReal) *
        ENNReal.ofReal (30 * (n : Real) ^ 5 *
          (TTCRuntime.RMax D : Real) *
          (TTCRuntime.Rho D) ^ 2 *
          TTCRuntime.theorem3PrecisionScale b
            (TTCRuntime.theorem3OuterRadiusMax D) *
          ((TTCRuntime.ThresholdCap p D.componentCount : Real) + 1) *
          (TTCRuntime.theorem3ParameterFactorCV18 hn D p + 1)) := by
  dsimp only
  let D := prep.run F hbounded
  let b := (prep.choosePrecision D p).value
  have hbase := ttc_expected_runtime_uniform_budget hn F hbounded p prep
    preprocessingOperations
  dsimp only at hbase
  by_cases hm : 0 < D.componentCount
  · exact hbase.trans (by
      gcongr
      exact TTCRuntime.theorem3UniformComponentBudget_le_headline_scale
        hn D p b hm)
  · have hzero : D.componentCount = 0 := by omega
    dsimp [D] at hzero
    simpa only [hzero, Nat.cast_zero, zero_mul, add_zero] using hbase

theorem ttc_theorem3_headline_budget_finite {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations : Nat) :
    let D := prep.run F hbounded
    let b := (prep.choosePrecision D p).value
    (preprocessingOperations : ENNReal) + (D.componentCount : ENNReal) *
        ENNReal.ofReal (30 * (n : Real) ^ 5 *
          (TTCRuntime.RMax D : Real) *
          (TTCRuntime.Rho D) ^ 2 *
          TTCRuntime.theorem3PrecisionScale b
            (TTCRuntime.theorem3OuterRadiusMax D) *
          ((TTCRuntime.ThresholdCap p D.componentCount : Real) + 1) *
          (TTCRuntime.theorem3ParameterFactorCV18 hn D p + 1)) ≠ ⊤ := by
  dsimp only
  exact ENNReal.add_ne_top.mpr ⟨by simp,
    ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top⟩


end Kr25Ssmxt
