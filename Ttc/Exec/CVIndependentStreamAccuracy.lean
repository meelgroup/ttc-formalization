import Ttc.Exec.CVIndependentStreamDependence
import Ttc.Exec.CVSourceCorrectedPathAccuracy

/-!
# Corrected CV accuracy on independent scalar streams

This is the one-run accuracy consumer for the honest operational representation in which
each of the `k` empirical coordinates owns a complete scalar Markov path.  The two
dependence premises of corrected `lem:accuracy` are discharged by scalar seed-projected
mixing followed by finite-product tensorization.  The relative second-moment premise is
kept explicit: `CVIndependentStreamMoments` proves it for an empirical average once the
chosen (possibly truncated) scalar phase statistic has relative second moment at most
`9`.
-/

namespace Ttc.CVIndependentStreamAccuracy

open MeasureTheory ProbabilityTheory Set
open Arlib Arlib.Probability Arlib.GaussianCooling
open Ttc.CVCorrected
open Ttc.CVIndependentStreamDependence
open Ttc.CVSourceCorrectedPathAccuracy

variable {X Seed : Type*} [MeasurableSpace X] [MeasurableSpace Seed]

/-- Corrected one-run bad-event bound for `k` independent complete scalar streams.

All dependence-specific hypotheses are contained in `hop`.  In particular its mixing
budget is scalar (`k * (2 * epsMix) <= correctedNu`), rather than a product warmness
constant.  The remaining arguments are exactly the analytic moment/truncation and exact
coupling premises of corrected `lem:accuracy`.
-/
theorem corrected_lem_accuracy_concrete_of_independentStreams
    {k m : Nat}
    {P : Nat → Kernel X X} [∀ i, IsMarkovKernel (P i)]
    {Q : Nat → Kernel Seed X} [∀ i, IsMarkovKernel (Q i)]
    {seed : X → Seed} {mu0 : Measure X} [IsProbabilityMeasure mu0]
    (V Wbar W : Nat → (Fin k → Nat → X) → Real) {eta : Real}
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hk : CorrectedSampleBudget m k eta)
    (hVm : ∀ j, Measurable (V j)) (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hEpos : ∀ j, 0 < ∫ omega, V j omega ∂(independentPathLaw k P mu0))
    (hVcap : ∀ j omega, V j omega ≤ 2 * correctedAlpha m eta *
      ∫ z, V j z ∂(independentPathLaw k P mu0))
    (hV2 : ∀ j, Integrable (fun omega ↦ (V j omega) ^ 2)
      (independentPathLaw k P mu0))
    (hV2cap : ∀ j omega, (V j omega) ^ 2 ≤ 2 * correctedAlpha m eta ^ 2 *
      ∫ z, (V j z) ^ 2 ∂(independentPathLaw k P mu0))
    (hWbarm : ∀ j, Measurable (Wbar j))
    (hW0 : ∀ j omega, 0 ≤ Wbar j omega)
    (hWint : ∀ j, Integrable (Wbar j) (independentPathLaw k P mu0))
    (hWEpos : ∀ j, 0 < ∫ omega, Wbar j omega ∂(independentPathLaw k P mu0))
    (hVdef : ∀ j omega, V j omega = min (Wbar j omega)
      (correctedAlpha m eta *
        ∫ z, Wbar j z ∂(independentPathLaw k P mu0)))
    (hphaseMoment : ∀ j,
      (∫ omega, (V j omega) ^ 2 ∂(independentPathLaw k P mu0)) ≤
        (1 + 8 / (k : Real)) *
          (∫ omega, V j omega ∂(independentPathLaw k P mu0)) ^ 2)
    {Eexact : Set (Fin k → Nat → X)} (hEexact : MeasurableSet Eexact)
    (hExactFail : (independentPathLaw k P mu0).real Eexactᶜ ≤ 1 / 20)
    (hExact : ∀ omega ∈ Eexact,
      phaseProduct Wbar m omega = phaseProduct W m omega)
    (hop : IndependentStreamOperational k P Q seed mu0 V m eta) :
    (independentPathLaw k P mu0).real
      {omega | phaseProduct W m omega ∉
        relErr eta (prefixMean (independentPathLaw k P mu0) V m)} ≤ 1 / 5 := by
  have hdeps := hop.correctedDependencePremises
  exact corrected_lem_accuracy_concrete V Wbar W heta heta1 hk hVm hV0 hEpos
    hVcap hV2 hV2cap hdeps.1 hdeps.2 hWbarm hW0 hWint hWEpos hVdef
    hphaseMoment hEexact hExactFail hExact

/-- Publicly composable one-run `4/5` volume-accuracy certificate for independent scalar
streams.  The target normalization identity is the only volume-specific premise; no
runtime claim is made here.
-/
theorem corrected_independentStreams_accuracy_four_fifths
    {k m : Nat}
    {P : Nat → Kernel X X} [∀ i, IsMarkovKernel (P i)]
    {Q : Nat → Kernel Seed X} [∀ i, IsMarkovKernel (Q i)]
    {seed : X → Seed} {mu0 : Measure X} [IsProbabilityMeasure mu0]
    (V Wbar W : Nat → (Fin k → Nat → X) → Real) {eta : Real}
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hk : CorrectedSampleBudget m k eta)
    (hVm : ∀ j, Measurable (V j)) (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hEpos : ∀ j, 0 < ∫ omega, V j omega ∂(independentPathLaw k P mu0))
    (hVcap : ∀ j omega, V j omega ≤ 2 * correctedAlpha m eta *
      ∫ z, V j z ∂(independentPathLaw k P mu0))
    (hV2 : ∀ j, Integrable (fun omega ↦ (V j omega) ^ 2)
      (independentPathLaw k P mu0))
    (hV2cap : ∀ j omega, (V j omega) ^ 2 ≤ 2 * correctedAlpha m eta ^ 2 *
      ∫ z, (V j z) ^ 2 ∂(independentPathLaw k P mu0))
    (hWbarm : ∀ j, Measurable (Wbar j))
    (hWm : ∀ j, Measurable (W j))
    (hW0 : ∀ j omega, 0 ≤ Wbar j omega)
    (hWint : ∀ j, Integrable (Wbar j) (independentPathLaw k P mu0))
    (hWEpos : ∀ j, 0 < ∫ omega, Wbar j omega ∂(independentPathLaw k P mu0))
    (hVdef : ∀ j omega, V j omega = min (Wbar j omega)
      (correctedAlpha m eta *
        ∫ z, Wbar j z ∂(independentPathLaw k P mu0)))
    (hphaseMoment : ∀ j,
      (∫ omega, (V j omega) ^ 2 ∂(independentPathLaw k P mu0)) ≤
        (1 + 8 / (k : Real)) *
          (∫ omega, V j omega ∂(independentPathLaw k P mu0)) ^ 2)
    {Eexact : Set (Fin k → Nat → X)} (hEexact : MeasurableSet Eexact)
    (hExactFail : (independentPathLaw k P mu0).real Eexactᶜ ≤ 1 / 20)
    (hExact : ∀ omega ∈ Eexact,
      phaseProduct Wbar m omega = phaseProduct W m omega)
    (hop : IndependentStreamOperational k P Q seed mu0 V m eta)
    (initialNormalizer volumeTarget : Real) (hinit : 0 ≤ initialNormalizer)
    (htarget : initialNormalizer *
      prefixMean (independentPathLaw k P mu0) V m = volumeTarget) :
    4 / 5 ≤ (independentPathLaw k P mu0).real
      {omega | initialNormalizer * phaseProduct W m omega ∈
        Ttc.relErr eta volumeTarget} := by
  let mu := independentPathLaw k P mu0
  have hbad := corrected_lem_accuracy_concrete_of_independentStreams V Wbar W
    heta heta1 hk hVm hV0 hEpos hVcap hV2 hV2cap hWbarm hW0 hWint hWEpos
    hVdef hphaseMoment hEexact hExactFail hExact hop
  have hgood : 4 / 5 ≤ mu.real
      {omega | phaseProduct W m omega ∈ Ttc.relErr eta (prefixMean mu V m)} :=
    corrected_lem_accuracy_four_fifths W hWm hbad le_rfl
  apply hgood.trans
  apply measureReal_mono _ (measure_ne_top _ _)
  intro omega homega
  exact scale_mem_relErr hinit homega htarget

#print axioms corrected_lem_accuracy_concrete_of_independentStreams
#print axioms corrected_independentStreams_accuracy_four_fifths

end Ttc.CVIndependentStreamAccuracy
