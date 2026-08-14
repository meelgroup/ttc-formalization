import Ttc.Exec.CVRelativeMeanClippingAssembly
import Ttc.Exec.CVHeterogeneousRetainedPathLaw
import Ttc.Exec.CVHeterogeneousSourceCertificate

/-!
# Weighted path accuracy to a charged retained-history certificate

This is the representation/cost capstone for the weighted estimator.  Any accuracy
proof on the ordinary score/seed paths (in particular
`relative_weighted_accuracy_four_fifths`) transfers exactly to the stored finite
score prefix, and the stationary-seed reference construction then supplies the
charged source certificate.
-/

set_option autoImplicit false

namespace Ttc.CVRelativeWeightedRetainedCertificate

open MeasureTheory ProbabilityTheory Finset Set Preorder
open Arlib
open Ttc.CVHeterogeneousHistoryReference
open Ttc.CVHeterogeneousRetainedPathLaw
open Ttc.CVHeterogeneousSourceCertificate
open Ttc.CVRetainedHistoryReferenceInduction
open Ttc.CVSourceReferenceTVCapstone
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVIdealAveragePathTelescope
open Ttc.CVIndependentStreamMoments
open scoped ENNReal Classical BigOperators

variable {Score Seed : Type*} [MeasurableSpace Score] [MeasurableSpace Seed]

/-- A path-level accuracy proof becomes a complete charged retained-history
reference-TV certificate.  No distributional approximation is introduced by the
readout: the finite stored score-prefix/current-seed law is exactly the corresponding
ordinary path law. -/
theorem exists_sourceReferenceTVOneRunCertificate_of_pathReadoutAccuracy
    [StandardBorelSpace Seed] [Nonempty Seed]
    (Q : Nat → Kernel Seed (ENNReal × (Score × Seed)))
    [∀ i, IsMarkovKernel (Q i)]
    (P : Nat → Kernel Seed (Score × Seed)) [∀ i, IsMarkovKernel (P i)]
    (mu : Measure (Score × Seed)) [IsProbabilityMeasure mu]
    (hforget : ∀ i x, Measure.map Prod.snd (Q i x) = P i x)
    (nu0 : Measure (HeterogeneousHistoryState Score Seed))
    [IsProbabilityMeasure nu0]
    (tau : Nat → Measure Seed) [∀ i, IsProbabilityMeasure (tau i)]
    (e B : Nat → ENNReal) {d initialBudget : ENNReal}
    (hinitTV : TVLe (initialHeterogeneousHistoryLaw mu) nu0 d)
    (hinitState : Measure.map Prod.snd nu0 = tau 0)
    (hinitMean : (∫⁻ z, z.1.1 ∂nu0) ≤ initialBudget)
    (hphaseSeedTV : ∀ i,
      TVLe ((tau i).bind
        (Kernel.map (Q i) (fun y : ENNReal × (Score × Seed) ↦ y.2.2)))
        (tau (i + 1)) (e i))
    (hphaseCost : ∀ i,
      (∫⁻ x, heterogeneousStepMean (Q i) x ∂tau i) ≤ B i)
    (dim m k : Nat)
    (readout : (Fin k → ((Finset.Iic m → Score) × Seed)) → Real)
    (hreadout : Measurable readout)
    {runtimeConstant R eps lo hi : Real}
    (herror : (k : ENNReal) * (d + ∑ i ∈ range m, e i) ≤
      ENNReal.ofReal (1 / 40 : Real))
    (hbudget : (k : ENNReal) *
        (initialBudget + ∑ i ∈ range m, B i) ≤
      Ttc.CVSourcePolynomialCutoffCapstone.sourceOneRunQueryBudget
        runtimeConstant dim R eps)
    (haccuracy : 4 / 5 ≤
      (Ttc.CVIndependentStreamDependence.independentPathLaw
        k (stateScheduleFromSeed P) mu).real
        {omega | readout (independentPathScorePrefixCurrent m omega) ∈ Icc lo hi}) :
    ∃ reference : Measure (Fin k → HeterogeneousHistoryState Score Seed),
      SourceReferenceTVOneRunCertificate
        (independentHeterogeneousRetainedPathLaw k Q mu m)
        reference (fun omega ↦ ∑ j, (omega j).1.1)
        (fun omega ↦ readout (independentStoredScorePrefixCurrent m omega))
        runtimeConstant dim R eps lo hi := by
  let G : Set (Fin k → ((Finset.Iic m → Score) × Seed)) :=
    {z | readout z ∈ Icc lo hi}
  have hG : MeasurableSet G := measurableSet_Icc.preimage hreadout
  have hretained : 4 / 5 ≤
      (independentHeterogeneousRetainedPathLaw k Q mu m).real
        {omega | readout (independentStoredScorePrefixCurrent m omega) ∈ Icc lo hi} := by
    rw [show {omega |
        readout (independentStoredScorePrefixCurrent m omega) ∈ Icc lo hi} =
        independentStoredScorePrefixCurrent m ⁻¹' G by rfl]
    rw [independentHeterogeneousRetainedPathLaw_real_preimage_eq
      k Q P mu hforget m G hG]
    simpa [G] using haccuracy
  have hvalue : Measurable
      (fun omega : Fin k → HeterogeneousHistoryState Score Seed ↦
        readout (independentStoredScorePrefixCurrent m omega)) :=
    hreadout.comp (measurable_independentStoredScorePrefixCurrent m)
  simpa only [independentHeterogeneousRetainedPathLaw] using
    (exists_sourceReferenceTVOneRunCertificate_of_stationarySeedPhases
      Q (initialHeterogeneousHistoryLaw mu) nu0 tau e B
      hinitTV hinitState hinitMean hphaseSeedTV hphaseCost dim m k
      (fun omega ↦ readout (independentStoredScorePrefixCurrent m omega)) hvalue
      herror hbudget hretained)

#print axioms exists_sourceReferenceTVOneRunCertificate_of_pathReadoutAccuracy

end Ttc.CVRelativeWeightedRetainedCertificate
