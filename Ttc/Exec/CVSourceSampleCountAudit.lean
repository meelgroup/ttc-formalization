/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Volume.CVHybridParameters
import Ttc.Volume.CVCorrectedParameters

set_option autoImplicit false

/-!
# Audit of the source-sharp CV sample count

The exact-law part of the Cousins--Vempala argument uses the phase-dependent second
moment factors.  The cold factors are `1 + 2/(k*n)`, and the hot factors are charged once
per doubling chunk.  This is the weighted budget implemented by
`CVHybridParameters.estimator_parameter_bundle`.

The later dependent/truncation paragraph of the source replaces every factor by
`1 + 8/k` and raises that uniform bound to the total number `m` of phases.  That
replacement cannot be combined with the advertised source sample count: controlling the
uniform product needs `k` proportional to `m / eps^2`, whereas the source count is
proportional only to the cold weight `c/n` plus the number of hot chunks.

The concrete arithmetic counterexamples below keep this distinction machine checked.
They do not refute the exact-law theorem; on the contrary, the final theorem records the
valid weighted parameter bundle used by
`CVHybridSchedule.packed_median_accuracy_exact_concrete`.
-/

namespace Ttc.CVSourceSampleCountAudit

open Ttc.CVCorrected Ttc.CVHybridSchedule
open MeasureTheory ProbabilityTheory Arlib.GaussianCooling

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- At a source-sized sample count, two occurrences of the later uniform factor already
exceed the paper's claimed final relative second-moment slack (with `eps = 1`). -/
theorem uniform_factor_product_counterexample :
    1 + (1 : Real) ^ 2 / 64 < (1 + 8 / (512 : Real)) ^ (2 : Nat) := by
  norm_num

/-- Accordingly, a sample count independent of the total number of phases cannot satisfy
the currently formalized uniform-phase corrected budget.  The example is deliberately
small; asymptotically the left side of `CorrectedSampleBudget` grows with `m`, while this
fixed `k` does not. -/
theorem source_scale_not_correctedSampleBudget :
    ¬ CorrectedSampleBudget 2 512 1 := by
  norm_num [CorrectedSampleBudget]

/-- The invalid implication isolated as a single proposition: even `k = 512/eps^2` and
`eps <= 1` do not imply either the uniform-factor product bound used in the dependent
paragraph or `CorrectedSampleBudget`. -/
theorem advertised_scale_does_not_imply_uniform_budget :
    let eps : Real := 1
    let k : Nat := 512
    let m : Nat := 2
    (k : Real) * eps ^ 2 = 512 ∧ eps ≤ 1 ∧
      ¬ ((1 + 8 / (k : Real)) ^ m ≤ 1 + eps ^ 2 / 64) ∧
      ¬ CorrectedSampleBudget m k eps := by
  norm_num [CorrectedSampleBudget]

/-- In contrast, the concrete source estimator has the exact phase-dependent cold/hot
budgets required by the valid exact-law accuracy theorem.  In particular its sample
count is controlled by `c/n + J`, not by the total phase count `m`.

Together with the geometric hypotheses in
`CVHybridSchedule.packed_median_accuracy_exact_concrete`, this bundle yields the
machine-checked exact-law volume estimator with the advertised `eps^-2` sample count.
-/
theorem source_estimator_weighted_exactLaw_bundle
    {n c J : Nat} (hn : 1 ≤ n) {eps : Real} (heps : 0 < eps) :
    0 < estimatorSamples n c J eps ∧
    0 ≤ estimatorKappa eps ∧
    42 ≤ (estimatorSamples n c J eps : Real) ∧
    2 * (c : Real) / (n : Real) ≤
      (estimatorSamples n c J eps : Real) * estimatorKappa eps ∧
    7 * (J : Real) ≤
      (estimatorSamples n c J eps : Real) * estimatorKappa eps ∧
    Real.exp (estimatorKappa eps + estimatorKappa eps) - 1 ≤ eps ^ 2 / 5 :=
  estimator_parameter_bundle hn heps

/-! ## The precise weighted dependent-proof interface

There is no need for a new probabilistic covariance recursion.  The existing corrected
recursion is already phrased using the actual `prefixSecondMean`.  The following lemma
shows that phase-dependent factors discharge its two second-moment scalar obligations.

Consequently the missing repair is narrower: prove that the *clipped operational*
statistics retain phase-dependent factors whose every prefix product satisfies
`hprefix`, rather than relaxing every phase to `1 + 8/k`.  The exact Gaussian schedule
already supplies the corresponding un-clipped product bound.
-/

/-- Phase-dependent relative second moments are sufficient for the corrected dependent
recursion.  This is the reusable weighted replacement for the uniform
`CorrectedSampleBudget` step.

The first conclusion is exactly `AccuracyLowerScalar`; the second is exactly the final
second-moment premise of `corrected_lem_accuracy_of_recursion`.
-/
theorem weighted_phaseFactors_discharge_recursion_scalars
    [IsProbabilityMeasure mu]
    (V : Nat -> Omega -> Real) (factor : Nat -> Real)
    {alpha nu q : Real} {m : Nat}
    (hnu : 0 <= nu)
    (hV0 : forall j omega, 0 <= V j omega)
    (hfactor0 : forall j, 0 <= factor j)
    (hratio : forall j,
      (∫ omega, (V j omega) ^ 2 ∂mu) <=
        factor j * (∫ omega, V j omega ∂mu) ^ 2)
    (hcovariance : 2 * nu * alpha ^ 2 <= 1 / (2 * alpha))
    (hprefix : forall i, i <= m ->
      (1 + 2 * nu * alpha ^ 4 * (i : Real)) * prefixMomentRatio factor i <= 2)
    (hfinal :
      (1 + 2 * nu * alpha ^ 4 * (m : Real)) * prefixMomentRatio factor m <=
        q * (1 - (m : Real) / alpha) ^ 2) :
    AccuracyLowerScalar mu V alpha nu m /\
      (1 + 2 * nu * alpha ^ 4 * (m : Real)) * prefixSecondMean mu V m <=
        q * (1 - (m : Real) / alpha) ^ 2 * (prefixMean mu V m) ^ 2 := by
  have hcoefficient0 : forall i : Nat,
      0 <= 1 + 2 * nu * alpha ^ 4 * (i : Real) := by
    intro i
    positivity
  constructor
  · refine ⟨hcovariance, ?_⟩
    intro i hi
    exact rawSecond_arithmetic_of_phaseRatios V factor hV0 hfactor0 hratio
      (hcoefficient0 (i + 1)) (hprefix (i + 1) (by omega))
  · have hpref := prefixSecondMean_le_mul_prefixMean_sq
      V factor hV0 hfactor0 hratio m
    calc
      (1 + 2 * nu * alpha ^ 4 * (m : Real)) * prefixSecondMean mu V m <=
          (1 + 2 * nu * alpha ^ 4 * (m : Real)) *
            (prefixMomentRatio factor m * (prefixMean mu V m) ^ 2) :=
        mul_le_mul_of_nonneg_left hpref (hcoefficient0 m)
      _ = ((1 + 2 * nu * alpha ^ 4 * (m : Real)) *
            prefixMomentRatio factor m) * (prefixMean mu V m) ^ 2 := by ring
      _ <= (q * (1 - (m : Real) / alpha) ^ 2) *
            (prefixMean mu V m) ^ 2 :=
        mul_le_mul_of_nonneg_right hfinal (sq_nonneg _)
      _ = q * (1 - (m : Real) / alpha) ^ 2 *
            (prefixMean mu V m) ^ 2 := by ring

#print axioms uniform_factor_product_counterexample
#print axioms source_scale_not_correctedSampleBudget
#print axioms advertised_scale_does_not_imply_uniform_budget
#print axioms source_estimator_weighted_exactLaw_bundle
#print axioms weighted_phaseFactors_discharge_recursion_scalars

end Ttc.CVSourceSampleCountAudit
