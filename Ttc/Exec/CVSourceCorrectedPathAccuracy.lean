/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Exec.CVSourceOneRunFromCostedPhases
import Ttc.Volume.CVDirectSequentialAccuracy

/-!
# Corrected CV accuracy on the source path schedule

This file instantiates the path-accuracy premise used by
`expectedQueryVolumeAlgorithmOfCostedPhases` from the strongest corrected dependent
accuracy theorem currently in the repository, `CVHybridCorrected.corrected_hybrid_accuracy`.

The adapter performs the two missing generic steps:

* turn the corrected bad-event bound `<= 1/5` into `4/5` success;
* multiply the phase product by the known initial normalizer and rewrite the telescoping
  target to the volume.

All moment and exact-coupling assumptions remain the named analytic hypotheses of corrected
accuracy.  Dependence is supplied by `DirectSequentialOperational`, whose warm-start
distributional mixing fields derive the required history/next-phase `NuIndep` bounds.
-/

namespace Ttc.CVSourceCorrectedPathAccuracy

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open Ttc.CVCorrected
open Ttc.CVDirectSequentialAccuracy
open Ttc.CostedPathwisePhaseLumping
open scoped ENNReal Classical Pointwise

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- The source-style state path measure attached to the pathwise accept/restart phase
kernel. -/
noncomputable def correctedSourcePathLaw
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq : Nat -> Real) (steps : Nat -> Nat)
    (hsigma : forall i, 0 < sigmaSq i)
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 <= 1)
    (mu0 : Measure (State n)) : Measure (Nat -> State n) :=
  @inhomogeneousPathMeasure _ _
    (pathwiseSourcePhaseSchedule K hK delta sigmaSq steps)
    (fun i => isMarkovKernel_pathwiseSourcePhaseSchedule K hK delta sigmaSq steps
      hsigma hc2 i) mu0

instance correctedSourcePathLaw.isProbabilityMeasure
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq : Nat -> Real) (steps : Nat -> Nat)
    (hsigma : forall i, 0 < sigmaSq i)
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 <= 1)
    (mu0 : Measure (State n)) [IsProbabilityMeasure mu0] :
    IsProbabilityMeasure (correctedSourcePathLaw K hK delta sigmaSq steps hsigma hc2 mu0) := by
  unfold correctedSourcePathLaw
  infer_instance

/-- Scaling a relative-error event by a nonnegative known normalizer. -/
theorem scale_mem_relErr {x target z eta volumeTarget : Real}
    (hz : 0 <= z) (hx : x ∈ Ttc.relErr eta target)
    (htarget : z * target = volumeTarget) :
    z * x ∈ Ttc.relErr eta volumeTarget := by
  change (1 - eta) * target <= x ∧ x <= (1 + eta) * target at hx
  change (1 - eta) * volumeTarget <= z * x ∧
    z * x <= (1 + eta) * volumeTarget
  rw [← htarget]
  constructor
  · calc
      (1 - eta) * (z * target) = z * ((1 - eta) * target) := by ring
      _ <= z * x := mul_le_mul_of_nonneg_left hx.1 hz
  · calc
      z * x <= z * ((1 + eta) * target) := mul_le_mul_of_nonneg_left hx.2 hz
      _ = (1 + eta) * (z * target) := by ring

/-- A corrected run proved at a smaller relative error also supplies the public path
accuracy premise at any larger error.  This is used with `eta = min eps 1`. -/
theorem path_accuracy_mono
    {mu : Measure (Nat -> State n)} {est : (Nat -> State n) -> Real}
    [IsFiniteMeasure mu]
    {eta eps target : Real} (heta : eta <= eps) (htarget : 0 <= target)
    (hgood : 4 / 5 <= mu.real {omega | est omega ∈ Ttc.relErr eta target}) :
    4 / 5 <= mu.real {omega | est omega ∈ Ttc.relErr eps target} := by
  exact hgood.trans (measureReal_mono (fun _ h => Ttc.CV.relErr_mono heta htarget h)
    (measure_ne_top _ _))

/-- `corrected_lem_accuracy_concrete_of_directSequential`, specialized to the pathwise
source schedule and rewritten as the exact `4/5` path-accuracy premise consumed by the
operational runtime constructor.

The `hop` argument is the honest Markov dependence interface: its `last_warm` and
`distributional_mixing` fields imply both `NuIndep` hypotheses directly from the actual
history/next-phase factorization.  No fresh-regeneration resource is used. -/
theorem corrected_sourcePath_accuracy_four_fifths
    {K : Set (State n)} (hK : MeasurableSet K)
    (delta sigmaSq : Nat -> Real) (steps : Nat -> Nat)
    (hsigma : forall i, 0 < sigmaSq i)
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 <= 1)
    (mu0 : Measure (State n)) [IsProbabilityMeasure mu0]
    (V Wbar W : Nat -> (Nat -> State n) -> Real)
    {m k : Nat} {eta : Real}
    (heta : 0 < eta) (heta1 : eta <= 1) (hk : CorrectedSampleBudget m k eta)
    (hVm : forall j, Measurable (V j)) (hV0 : forall j omega, 0 <= V j omega)
    (hEpos : forall j, 0 < ∫ omega, V j omega
      ∂correctedSourcePathLaw K hK delta sigmaSq steps hsigma hc2 mu0)
    (hVcap : forall j omega, V j omega <= 2 * correctedAlpha m eta *
      ∫ z, V j z ∂correctedSourcePathLaw K hK delta sigmaSq steps hsigma hc2 mu0)
    (hV2 : forall j, Integrable (fun omega => (V j omega) ^ 2)
      (correctedSourcePathLaw K hK delta sigmaSq steps hsigma hc2 mu0))
    (hV2cap : forall j omega, (V j omega) ^ 2 <= 2 * correctedAlpha m eta ^ 2 *
      ∫ z, (V j z) ^ 2
        ∂correctedSourcePathLaw K hK delta sigmaSq steps hsigma hc2 mu0)
    (hWbarm : forall j, Measurable (Wbar j))
    (hWm : forall j, Measurable (W j))
    (hW0 : forall j omega, 0 <= Wbar j omega)
    (hWint : forall j, Integrable (Wbar j)
      (correctedSourcePathLaw K hK delta sigmaSq steps hsigma hc2 mu0))
    (hWEpos : forall j, 0 < ∫ omega, Wbar j omega
      ∂correctedSourcePathLaw K hK delta sigmaSq steps hsigma hc2 mu0)
    (hVdef : forall j omega, V j omega = min (Wbar j omega)
      (correctedAlpha m eta * ∫ z, Wbar j z
        ∂correctedSourcePathLaw K hK delta sigmaSq steps hsigma hc2 mu0))
    (hratio : forall j,
      (∫ omega, (V j omega) ^ 2
        ∂correctedSourcePathLaw K hK delta sigmaSq steps hsigma hc2 mu0) <=
      (1 + 8 / (k : Real)) *
        (∫ omega, V j omega
          ∂correctedSourcePathLaw K hK delta sigmaSq steps hsigma hc2 mu0) ^ 2)
    {Eexact : Set (Nat -> State n)} (hEexact : MeasurableSet Eexact)
    (hExactFail : (correctedSourcePathLaw K hK delta sigmaSq steps hsigma hc2 mu0).real
      Eexact.compl <= 1 / 20)
    (hExact : forall omega, omega ∈ Eexact ->
      phaseProduct Wbar m omega = phaseProduct W m omega)
    (hop : @DirectSequentialOperational (State n) _
      (pathwiseSourcePhaseSchedule K hK delta sigmaSq steps)
      (fun i => isMarkovKernel_pathwiseSourcePhaseSchedule K hK delta sigmaSq steps
        hsigma hc2 i) mu0 inferInstance V m eta)
    (initialNormalizer volumeTarget : Real) (hinit : 0 <= initialNormalizer)
    (htarget : initialNormalizer * prefixMean
      (correctedSourcePathLaw K hK delta sigmaSq steps hsigma hc2 mu0) V m = volumeTarget) :
    4 / 5 <= (correctedSourcePathLaw K hK delta sigmaSq steps hsigma hc2 mu0).real
      {omega | initialNormalizer * phaseProduct W m omega ∈
        Ttc.relErr eta volumeTarget} := by
  let mu := correctedSourcePathLaw K hK delta sigmaSq steps hsigma hc2 mu0
  letI hP : forall i, IsMarkovKernel
      (pathwiseSourcePhaseSchedule K hK delta sigmaSq steps i) :=
    fun i => isMarkovKernel_pathwiseSourcePhaseSchedule K hK delta sigmaSq steps
      hsigma hc2 i
  have hbad := corrected_lem_accuracy_concrete_of_directSequential V Wbar W
    heta heta1 hk hVm hV0 hEpos hVcap hV2 hV2cap hWbarm hW0 hWint hWEpos
    hVdef hratio hEexact hExactFail hExact hop
  have hgood : 4 / 5 <= mu.real
      {omega | phaseProduct W m omega ∈ Ttc.relErr eta (prefixMean mu V m)} :=
    corrected_lem_accuracy_four_fifths W hWm hbad le_rfl
  apply hgood.trans
  apply measureReal_mono _ (measure_ne_top _ _)
  intro omega homega
  exact scale_mem_relErr hinit homega htarget

#print axioms scale_mem_relErr
#print axioms path_accuracy_mono
#print axioms corrected_sourcePath_accuracy_four_fifths

end Ttc.CVSourceCorrectedPathAccuracy
