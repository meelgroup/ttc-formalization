/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVEstimatorExactAccuracy

/-!
# Coupling the packed exact estimator to implementable sampler laws

The exact-law theorem and the sampler theorem meet only through total variation.  This
adapter tensorizes the elementary error over runs, phases, and samples and subtracts the
resulting failure budget from the exact estimator's success probability.
-/

namespace Ttc.CVPacked

open MeasureTheory
open Arlib.GaussianCooling
open scoped ENNReal

variable {r m k : ℕ} {E : Type*} [MeasurableSpace E]

/-- Replacing all `r*m*k` exact elementary laws by TV-close sampler laws costs at most the
declared coupling failure budget in the median estimator's relative-error success. -/
theorem measureReal_median_relErr_ge_of_tvLe
    {ν ν' : Fin r → Fin m → Fin k → Measure E}
    [∀ t i l, IsProbabilityMeasure (ν t i l)]
    [∀ t i l, IsProbabilityMeasure (ν' t i l)]
    {b : ℝ≥0∞} (hb : b ≠ ⊤) (htv : ∀ t i l, Arlib.TVLe (ν t i l) (ν' t i l) b)
    {ρ : ℝ} (hρ : (((r * m * k : ℕ) : ℝ) * b.toReal) ≤ ρ)
    {V : Arlib.Probability.RunSpace (Fin k → E) r m → ℝ} (hV : Measurable V)
    {vol ε p : ℝ}
    (hgood : 1 - p ≤
      (Arlib.Probability.runMeasure (packedPhaseLaw ν')).real
        {ω | V ω ∈ Ttc.relErr ε vol}) :
    1 - p - ρ ≤
      (Arlib.Probability.runMeasure (packedPhaseLaw ν)).real
        {ω | V ω ∈ Ttc.relErr ε vol} := by
  have hgood' : 1 - p ≤
      (Arlib.Probability.runMeasure (packedPhaseLaw ν')).real
        {ω | (1 - ε) * vol ≤ V ω ∧ V ω ≤ (1 + ε) * vol} := by
    simpa only [Ttc.relErr, Set.mem_Icc, Set.mem_setOf_eq] using hgood
  have hmain := le_measureReal_packedRun_of_failure_budget hb htv hρ hV hgood'
  simpa only [Ttc.relErr, Set.mem_Icc, Set.mem_setOf_eq] using hmain

#print axioms measureReal_median_relErr_ge_of_tvLe

end Ttc.CVPacked
