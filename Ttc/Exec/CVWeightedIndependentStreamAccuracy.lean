import Ttc.Exec.CVWeightedCorrectedAccuracy
import Ttc.Exec.CVIndependentStreamDependence
import Ttc.Exec.CVSourceCorrectedPathAccuracy
import Ttc.Exec.CVCorrectedClippingBias

/-!
# Weighted corrected accuracy for independent operational streams

This is the public path-law wrapper around `corrected_lem_accuracy_weighted`.  It
reuses the dependence witnesses already carried by `IndependentStreamOperational` and
replaces the obsolete uniform `CorrectedSampleBudget` premise by the source-sharp
prefix product bound for phase-dependent factors.
-/

set_option autoImplicit false

namespace Ttc.CVWeightedIndependentStreamAccuracy

open MeasureTheory ProbabilityTheory Set
open Arlib Arlib.Probability Arlib.GaussianCooling
open Ttc.CVCorrected
open Ttc.CVIndependentStreamDependence
open Ttc.CVWeightedCorrectedAccuracy
open Ttc.CVSourceCorrectedPathAccuracy
open Ttc.CVCorrectedClippingBias

variable {X Seed : Type*} [MeasurableSpace X] [MeasurableSpace Seed]

/-- Weighted corrected bad-event bound on independent complete scalar streams. -/
theorem corrected_lem_accuracy_weighted_of_independentStreams
    {k m : Nat}
    {P : Nat → Kernel X X} [∀ i, IsMarkovKernel (P i)]
    {Q : Nat → Kernel Seed X} [∀ i, IsMarkovKernel (Q i)]
    {seed : X → Seed} {mu0 : Measure X} [IsProbabilityMeasure mu0]
    (V Wbar W : Nat → (Fin k → Nat → X) → Real)
    (factor : Nat → Real) {eta : Real}
    (heta : 0 < eta) (heta1 : eta ≤ 1)
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
    (hfactor0 : ∀ j, 0 ≤ factor j)
    (hphaseMoment : ∀ j,
      (∫ omega, (V j omega) ^ 2 ∂(independentPathLaw k P mu0)) ≤
        factor j * (∫ omega, V j omega
          ∂(independentPathLaw k P mu0)) ^ 2)
    (hprefix : ∀ i, i ≤ m →
      prefixMomentRatio factor i ≤ 1 + eta ^ 2 / 6250)
    {Eexact : Set (Fin k → Nat → X)} (hEexact : MeasurableSet Eexact)
    (hExactFail : (independentPathLaw k P mu0).real Eexactᶜ ≤ 1 / 20)
    (hExact : ∀ omega ∈ Eexact,
      phaseProduct Wbar m omega = phaseProduct W m omega)
    (hop : IndependentStreamOperational k P Q seed mu0 V m eta) :
    (independentPathLaw k P mu0).real
      {omega | phaseProduct W m omega ∉
        relErr eta (prefixMean (independentPathLaw k P mu0) V m)} ≤ 1 / 5 := by
  have hdeps := hop.correctedDependencePremises
  exact corrected_lem_accuracy_weighted V Wbar W factor heta heta1 hVm hV0
    hEpos hVcap hV2 hV2cap hdeps.1 hdeps.2 hWbarm hW0 hWint hWEpos
    hVdef hfactor0 hphaseMoment hprefix hEexact hExactFail hExact

/-- Public one-run `4/5` accuracy with a phase-dependent moment-factor budget. -/
theorem corrected_independentStreams_accuracy_four_fifths_weighted
    {k m : Nat}
    {P : Nat → Kernel X X} [∀ i, IsMarkovKernel (P i)]
    {Q : Nat → Kernel Seed X} [∀ i, IsMarkovKernel (Q i)]
    {seed : X → Seed} {mu0 : Measure X} [IsProbabilityMeasure mu0]
    (V Wbar W : Nat → (Fin k → Nat → X) → Real)
    (factor : Nat → Real) {eta : Real}
    (heta : 0 < eta) (heta1 : eta ≤ 1)
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
    (hfactor0 : ∀ j, 0 ≤ factor j)
    (hphaseMoment : ∀ j,
      (∫ omega, (V j omega) ^ 2 ∂(independentPathLaw k P mu0)) ≤
        factor j * (∫ omega, V j omega
          ∂(independentPathLaw k P mu0)) ^ 2)
    (hprefix : ∀ i, i ≤ m →
      prefixMomentRatio factor i ≤ 1 + eta ^ 2 / 6250)
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
  let pathLaw := independentPathLaw k P mu0
  have hbad := corrected_lem_accuracy_weighted_of_independentStreams
    V Wbar W factor heta heta1 hVm hV0 hEpos hVcap hV2 hV2cap
    hWbarm hW0 hWint hWEpos hVdef hfactor0 hphaseMoment hprefix
    hEexact hExactFail hExact hop
  have hgood : 4 / 5 ≤ pathLaw.real
      {omega | phaseProduct W m omega ∈
        Ttc.relErr eta (prefixMean pathLaw V m)} :=
    corrected_lem_accuracy_four_fifths W hWm hbad le_rfl
  apply hgood.trans
  apply measureReal_mono _ (measure_ne_top _ _)
  intro omega homega
  exact scale_mem_relErr hinit homega htarget

/-- Bias-aware public one-run accuracy.  This is the form used by the operational
Gaussian estimator: its clipped prefix need only approximate, rather than equal, the
true volume. -/
theorem corrected_independentStreams_accuracy_four_fifths_weighted_biasAware
    {k m : Nat}
    {P : Nat → Kernel X X} [∀ i, IsMarkovKernel (P i)]
    {Q : Nat → Kernel Seed X} [∀ i, IsMarkovKernel (Q i)]
    {seed : X → Seed} {mu0 : Measure X} [IsProbabilityMeasure mu0]
    (V Wbar W : Nat → (Fin k → Nat → X) → Real)
    (factor : Nat → Real) {etaInner beta requested : Real}
    (heta : 0 < etaInner) (heta1 : etaInner ≤ 1)
    (hbeta : 0 ≤ beta)
    (hbudget : etaInner + beta + etaInner * beta ≤ requested)
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
    (hfactor0 : ∀ j, 0 ≤ factor j)
    (hphaseMoment : ∀ j,
      (∫ omega, (V j omega) ^ 2 ∂(independentPathLaw k P mu0)) ≤
        factor j * (∫ omega, V j omega
          ∂(independentPathLaw k P mu0)) ^ 2)
    (hprefix : ∀ i, i ≤ m →
      prefixMomentRatio factor i ≤ 1 + etaInner ^ 2 / 6250)
    {Eexact : Set (Fin k → Nat → X)} (hEexact : MeasurableSet Eexact)
    (hExactFail : (independentPathLaw k P mu0).real Eexactᶜ ≤ 1 / 20)
    (hExact : ∀ omega ∈ Eexact,
      phaseProduct Wbar m omega = phaseProduct W m omega)
    (hop : IndependentStreamOperational k P Q seed mu0 V m etaInner)
    (initialNormalizer volumeTarget : Real) (hinit : 0 ≤ initialNormalizer)
    (hvolume : 0 ≤ volumeTarget)
    (hclip : ClippedPrefixTarget (independentPathLaw k P mu0) V m
      initialNormalizer volumeTarget beta) :
    4 / 5 ≤ (independentPathLaw k P mu0).real
      {omega | initialNormalizer * phaseProduct W m omega ∈
        Ttc.relErr requested volumeTarget} := by
  let pathLaw := independentPathLaw k P mu0
  have hbad := corrected_lem_accuracy_weighted_of_independentStreams
    V Wbar W factor heta heta1 hVm hV0 hEpos hVcap hV2 hV2cap
    hWbarm hW0 hWint hWEpos hVdef hfactor0 hphaseMoment hprefix
    hEexact hExactFail hExact hop
  have hgood : 4 / 5 ≤ pathLaw.real
      {omega | phaseProduct W m omega ∈
        Ttc.relErr etaInner (prefixMean pathLaw V m)} :=
    corrected_lem_accuracy_four_fifths W hWm hbad le_rfl
  exact four_fifths_scaled_of_clippedPrefixTarget hinit heta.le hbeta hvolume
    hbudget hgood hclip

#print axioms corrected_lem_accuracy_weighted_of_independentStreams
#print axioms corrected_independentStreams_accuracy_four_fifths_weighted
#print axioms corrected_independentStreams_accuracy_four_fifths_weighted_biasAware

end Ttc.CVWeightedIndependentStreamAccuracy
