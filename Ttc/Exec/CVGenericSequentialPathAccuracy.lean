import Ttc.Exec.CVSourceCorrectedPathAccuracy

/-!
# Corrected CV accuracy for an arbitrary operational phase schedule

This removes the old specialization to `pathwiseSourcePhaseSchedule`.  In particular, the
finite continuing-retry schedule can use the already-proved corrected accuracy theorem once
it supplies `DirectSequentialOperational`.
-/

namespace Ttc.CVGenericSequentialPathAccuracy

open MeasureTheory ProbabilityTheory Set
open Arlib Arlib.Probability Arlib.GaussianCooling
open Ttc.CVCorrected Ttc.CVDirectSequentialAccuracy
open Ttc.CVSourceCorrectedPathAccuracy

variable {E : Type*} [MeasurableSpace E]

/-- Generic one-run `4/5` accuracy theorem for any inhomogeneous Markov phase schedule.

All sampler dependence is confined to `hop`.  The remaining hypotheses are precisely the
moment, truncation, exact-coupling, and telescoping premises of corrected `lem:accuracy`.
-/
theorem corrected_sequentialPath_accuracy_four_fifths
    (P : Nat → Kernel E E) [∀ i, IsMarkovKernel (P i)]
    (mu0 : Measure E) [IsProbabilityMeasure mu0]
    (V Wbar W : Nat → (Nat → E) → Real)
    {m k : Nat} {eta : Real}
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hk : CorrectedSampleBudget m k eta)
    (hVm : ∀ j, Measurable (V j)) (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hEpos : ∀ j, 0 < ∫ omega, V j omega ∂(inhomogeneousPathMeasure P mu0))
    (hVcap : ∀ j omega, V j omega ≤ 2 * correctedAlpha m eta *
      ∫ z, V j z ∂(inhomogeneousPathMeasure P mu0))
    (hV2 : ∀ j, Integrable (fun omega ↦ (V j omega) ^ 2)
      (inhomogeneousPathMeasure P mu0))
    (hV2cap : ∀ j omega, (V j omega) ^ 2 ≤ 2 * correctedAlpha m eta ^ 2 *
      ∫ z, (V j z) ^ 2 ∂(inhomogeneousPathMeasure P mu0))
    (hWbarm : ∀ j, Measurable (Wbar j))
    (hWm : ∀ j, Measurable (W j))
    (hW0 : ∀ j omega, 0 ≤ Wbar j omega)
    (hWint : ∀ j, Integrable (Wbar j) (inhomogeneousPathMeasure P mu0))
    (hWEpos : ∀ j, 0 < ∫ omega, Wbar j omega ∂(inhomogeneousPathMeasure P mu0))
    (hVdef : ∀ j omega, V j omega = min (Wbar j omega)
      (correctedAlpha m eta *
        ∫ z, Wbar j z ∂(inhomogeneousPathMeasure P mu0)))
    (hratio : ∀ j,
      (∫ omega, (V j omega) ^ 2 ∂(inhomogeneousPathMeasure P mu0)) ≤
        (1 + 8 / (k : Real)) *
          (∫ omega, V j omega ∂(inhomogeneousPathMeasure P mu0)) ^ 2)
    {Eexact : Set (Nat → E)} (hEexact : MeasurableSet Eexact)
    (hExactFail : (inhomogeneousPathMeasure P mu0).real Eexactᶜ ≤ 1 / 20)
    (hExact : ∀ omega ∈ Eexact,
      phaseProduct Wbar m omega = phaseProduct W m omega)
    (hop : DirectSequentialOperational P mu0 V m eta)
    (initialNormalizer volumeTarget : Real) (hinit : 0 ≤ initialNormalizer)
    (htarget : initialNormalizer *
      prefixMean (inhomogeneousPathMeasure P mu0) V m = volumeTarget) :
    4 / 5 ≤ (inhomogeneousPathMeasure P mu0).real
      {omega | initialNormalizer * phaseProduct W m omega ∈
        Ttc.relErr eta volumeTarget} := by
  let mu := inhomogeneousPathMeasure P mu0
  have hbad := corrected_lem_accuracy_concrete_of_directSequential V Wbar W
    heta heta1 hk hVm hV0 hEpos hVcap hV2 hV2cap hWbarm hW0 hWint hWEpos
    hVdef hratio hEexact hExactFail hExact hop
  have hgood : 4 / 5 ≤ mu.real
      {omega | phaseProduct W m omega ∈ Ttc.relErr eta (prefixMean mu V m)} :=
    corrected_lem_accuracy_four_fifths W hWm hbad le_rfl
  apply hgood.trans
  apply measureReal_mono _ (measure_ne_top _ _)
  intro omega homega
  exact scale_mem_relErr hinit homega htarget

#print axioms corrected_sequentialPath_accuracy_four_fifths

end Ttc.CVGenericSequentialPathAccuracy
