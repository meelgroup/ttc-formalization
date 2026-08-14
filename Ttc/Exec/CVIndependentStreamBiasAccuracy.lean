import Ttc.Exec.CVCorrectedClippingBias

/-! Bias-aware corrected accuracy for independent streams. -/

namespace Ttc.CVIndependentStreamBiasAccuracy

open MeasureTheory ProbabilityTheory Set
open Arlib Arlib.Probability Arlib.GaussianCooling
open Ttc.CVCorrected Ttc.CVIndependentStreamDependence
open Ttc.CVIndependentStreamAccuracy Ttc.CVCorrectedClippingBias

variable {X Seed : Type*} [MeasurableSpace X] [MeasurableSpace Seed]

/-- The independent-stream corrected theorem with the honest clipped-prefix bias in
place of the old false exact target identity. -/
theorem corrected_independentStreams_accuracy_four_fifths_biasAware
    {k m : Nat} {P : Nat → Kernel X X} [∀ i, IsMarkovKernel (P i)]
    {Q : Nat → Kernel Seed X} [∀ i, IsMarkovKernel (Q i)]
    {seed : X → Seed} {mu0 : Measure X} [IsProbabilityMeasure mu0]
    (V Wbar W : Nat → (Fin k → Nat → X) → Real)
    {etaInner beta requested : Real}
    (heta : 0 < etaInner) (heta1 : etaInner ≤ 1)
    (hbeta : 0 ≤ beta) (hbudget : etaInner + beta + etaInner * beta ≤ requested)
    (hk : CorrectedSampleBudget m k etaInner)
    (hVm : ∀ j, Measurable (V j)) (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hEpos : ∀ j, 0 < ∫ omega, V j omega ∂(independentPathLaw k P mu0))
    (hVcap : ∀ j omega, V j omega ≤ 2 * correctedAlpha m etaInner *
      ∫ z, V j z ∂(independentPathLaw k P mu0))
    (hV2 : ∀ j, Integrable (fun omega ↦ (V j omega) ^ 2)
      (independentPathLaw k P mu0))
    (hV2cap : ∀ j omega, (V j omega) ^ 2 ≤ 2 * correctedAlpha m etaInner ^ 2 *
      ∫ z, (V j z) ^ 2 ∂(independentPathLaw k P mu0))
    (hWbarm : ∀ j, Measurable (Wbar j)) (hWm : ∀ j, Measurable (W j))
    (hW0 : ∀ j omega, 0 ≤ Wbar j omega)
    (hWint : ∀ j, Integrable (Wbar j) (independentPathLaw k P mu0))
    (hWEpos : ∀ j, 0 < ∫ omega, Wbar j omega ∂(independentPathLaw k P mu0))
    (hVdef : ∀ j omega, V j omega = min (Wbar j omega)
      (correctedAlpha m etaInner *
        ∫ z, Wbar j z ∂(independentPathLaw k P mu0)))
    (hphaseMoment : ∀ j,
      (∫ omega, (V j omega) ^ 2 ∂(independentPathLaw k P mu0)) ≤
        (1 + 8 / (k : Real)) *
          (∫ omega, V j omega ∂(independentPathLaw k P mu0)) ^ 2)
    {Eexact : Set (Fin k → Nat → X)} (hEexact : MeasurableSet Eexact)
    (hExactFail : (independentPathLaw k P mu0).real Eexactᶜ ≤ 1 / 20)
    (hExact : ∀ omega ∈ Eexact, phaseProduct Wbar m omega = phaseProduct W m omega)
    (hop : IndependentStreamOperational k P Q seed mu0 V m etaInner)
    (initialNormalizer volumeTarget : Real) (hinit : 0 ≤ initialNormalizer)
    (hvolume : 0 ≤ volumeTarget)
    (hclip : ClippedPrefixTarget (independentPathLaw k P mu0) V m
      initialNormalizer volumeTarget beta) :
    4 / 5 ≤ (independentPathLaw k P mu0).real
      {omega | initialNormalizer * phaseProduct W m omega ∈
        Ttc.relErr requested volumeTarget} := by
  let pathLaw := independentPathLaw k P mu0
  have hbad := corrected_lem_accuracy_concrete_of_independentStreams V Wbar W
    heta heta1 hk hVm hV0 hEpos hVcap hV2 hV2cap hWbarm hW0 hWint hWEpos
    hVdef hphaseMoment hEexact hExactFail hExact hop
  have hgood : 4 / 5 ≤ pathLaw.real
      {omega | phaseProduct W m omega ∈
        Ttc.relErr etaInner (prefixMean pathLaw V m)} :=
    corrected_lem_accuracy_four_fifths W hWm hbad le_rfl
  exact four_fifths_scaled_of_clippedPrefixTarget hinit heta.le hbeta hvolume hbudget
    hgood hclip

#print axioms corrected_independentStreams_accuracy_four_fifths_biasAware

end Ttc.CVIndependentStreamBiasAccuracy
