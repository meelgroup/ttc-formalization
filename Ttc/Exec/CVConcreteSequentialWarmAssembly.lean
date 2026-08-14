/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Exec.CVConcreteCostedPathwiseSchedule
import Ttc.Volume.CVDirectSequentialWarm
import Ttc.Exec.CVSourceCorrectedPathAccuracy

/-!
# Sequential warm assembly for the concrete costed CV phase kernel

The raw lazy speedy execution already has the required expected membership-query estimate
from an arbitrary warm *law*.  This file applies that theorem to each actual incoming
marginal of the costed phase trajectory and builds
`concreteCostedPhaseRefinement_of_phaseMeans`.

The sole cost-side analytic residue is `AverageRestartOverhead`: the two statewise
accept/restart loops must cost at most eight times the raw walk on average under the actual
incoming marginal.  Distributional half/quarter acceptance does not prove this directly,
because the statewise kernel averages reciprocal conditional acceptance probabilities.
-/

namespace Ttc.CVConcreteSequentialWarmAssembly

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains
open Ttc.CVConcreteCostedPathwiseSchedule
open Ttc.CVSourceOneRunFromCostedPhases
open Ttc.CostedPathwisePhaseLumping
open scoped ENNReal Classical Pointwise

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- Expected raw membership-query cost from the actual incoming phase marginal. -/
noncomputable def actualRawPhaseMean
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq : Nat -> Real) (hdelta : forall i, 0 < delta i)
    (steps : Nat -> Nat) (mu0 : Measure (State n)) (i : Nat) : ENNReal :=
  ∫⁻ x, (∫⁻ omega,
    Ttc.RawGaussianLazyStoppedExecution.actualMembershipQueryCount (steps i) omega
      ∂Ttc.RawGaussianLazyStoppedExecution.lazyRawStoppedExecution K hK
        (delta i) (sigmaSq i) (hdelta i) (Measure.dirac x))
    ∂costedPhaseStateMarginal
      (concreteCostedPhaseSchedule K hK delta sigmaSq hdelta steps) mu0 i

/-- The exact missing average-cost statement for the two statewise restart loops. -/
def AverageRestartOverhead
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq : Nat -> Real) (hdelta : forall i, 0 < delta i)
    (steps : Nat -> Nat) (mu0 : Measure (State n)) (m : Nat) : Prop :=
  forall i, i < m ->
    (∫⁻ x, Ttc.SequentialCost.stepMean
        (concreteCostedPhaseSchedule K hK delta sigmaSq hdelta steps) i x
      ∂costedPhaseStateMarginal
        (concreteCostedPhaseSchedule K hK delta sigmaSq hdelta steps) mu0 i) <=
      8 * actualRawPhaseMean K hK delta sigmaSq hdelta steps mu0 i

/-- The adjustable wasted-step theorem, averaged under the actual incoming phase law.
This is the source-faithful use of warmness; no Dirac start is asserted warm. -/
theorem six_mul_actualRawPhaseMean_le_ten_mul_adjustable
    (hn : 2 <= n) {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (q delta sigma : Nat -> Real) (hdelta : forall i, 0 < delta i)
    (steps : Nat -> Nat) (mu0 : Measure (State n)) [IsProbabilityMeasure mu0]
    (hq : forall i, 1 < q i) (hsigma : forall i, 0 < sigma i)
    (hdeltan : forall i, delta i <= 1 / (2 * (n : Real)))
    (hdeltaq : forall i, delta i <= sigma i /
      (max 8 (2 * q i) * Real.sqrt n))
    (R : Nat -> Real) (hR : forall i, 0 <= R i)
    (hRsigma : forall i, R i <= q i * sigma i * Real.sqrt n)
    (hKR : forall i x, x ∈ K -> ‖x‖ <= R i)
    (M : Nat -> ENNReal)
    (hwarm : forall i, IsWarm (M i)
      (costedPhaseStateMarginal
        (concreteCostedPhaseSchedule K hK delta (fun j => (sigma j) ^ 2)
          hdelta steps) mu0 i)
      (ellGaussianProb K (delta i) ((sigma i) ^ 2)))
    (i : Nat) :
    6 * actualRawPhaseMean K hK delta (fun j => (sigma j) ^ 2)
        hdelta steps mu0 i <=
      10 * ((steps i : ENNReal) * M i) := by
  let nu := costedPhaseStateMarginal
    (concreteCostedPhaseSchedule K hK delta (fun j => (sigma j) ^ 2) hdelta steps) mu0 i
  letI : IsProbabilityMeasure nu := by
    unfold nu costedPhaseStateMarginal costedPhaseOneRunLaw
    exact Measure.isProbabilityMeasure_map
      (measurable_snd.comp (measurable_pi_apply i)).aemeasurable
  unfold actualRawPhaseMean
  rw [Ttc.CostedStatefulSpeedyPhases.lintegral_diracPhaseCost_eq_execution
    hK (delta i) ((sigma i) ^ 2) (hdelta i) (steps i) nu]
  exact Ttc.RawGaussianLazyStoppedExecution.six_mul_expected_actualMembershipQueryCount_le_ten_mul_adjustable
    hn hK hKc hball (hq i) (hdelta i) (hsigma i) (hdeltan i) (hdeltaq i)
      (hR i) (hRsigma i) (hKR i) (hwarm i) (steps i)

/-- Complete concrete cost refinement from actual-marginal warmth and the single averaged
restart-overhead hypothesis.  The deliberately coarse `80` retains the source constants
and avoids division in `ENNReal`. -/
theorem concreteCostedPhaseRefinement_of_sequentialWarm
    (hn : 2 <= n) {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (q delta sigma : Nat -> Real) (hdelta : forall i, 0 < delta i)
    (steps : Nat -> Nat) (mu0 : Measure (State n)) [IsProbabilityMeasure mu0]
    (m : Nat)
    (hq : forall i, 1 < q i) (hsigma : forall i, 0 < sigma i)
    (hdeltan : forall i, delta i <= 1 / (2 * (n : Real)))
    (hdeltaq : forall i, delta i <= sigma i /
      (max 8 (2 * q i) * Real.sqrt n))
    (R : Nat -> Real) (hR : forall i, 0 <= R i)
    (hRsigma : forall i, R i <= q i * sigma i * Real.sqrt n)
    (hKR : forall i x, x ∈ K -> ‖x‖ <= R i)
    (M : Nat -> ENNReal)
    (hwarm : forall i, IsWarm (M i)
      (costedPhaseStateMarginal
        (concreteCostedPhaseSchedule K hK delta (fun j => (sigma j) ^ 2)
          hdelta steps) mu0 i)
      (ellGaussianProb K (delta i) ((sigma i) ^ 2)))
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 <= 1)
    (hshrink : forall i x, 0 <
      iterate (lazy (speedyMetropolisGaussian K (delta i) ((sigma i) ^ 2)))
        (Measure.dirac x) (steps i) ((1 - 1 / (2 * (n : Real))) • K))
    (haccept : forall i x,
      ((Ttc.SpeedyRejection.phasePointProposal K (delta i) ((sigma i) ^ 2)
          (Measure.dirac x) (steps i)).withDensity
        (fun y => ENNReal.ofReal
          (speedyAcceptReal (1 - 1 / (2 * (n : Real))) ((sigma i) ^ 2) y))) univ ≠ 0)
    (hrestart : AverageRestartOverhead K hK delta (fun j => (sigma j) ^ 2)
      hdelta steps mu0 m) :
    CostedPhaseKernelRefinement
      (pathwiseSourcePhaseSchedule K hK delta (fun j => (sigma j) ^ 2) steps)
      (concreteCostedPhaseSchedule K hK delta (fun j => (sigma j) ^ 2) hdelta steps)
      mu0 m (fun i => 80 * ((steps i : ENNReal) * M i)) := by
  apply concreteCostedPhaseRefinement_of_phaseMeans K hK delta
    (fun j => (sigma j) ^ 2) hdelta steps (fun i => sq_pos_of_pos (hsigma i)) hc2
    mu0 m (fun i => 80 * ((steps i : ENNReal) * M i)) hshrink haccept
  intro i hi
  have hraw := six_mul_actualRawPhaseMean_le_ten_mul_adjustable hn hK hKc hball
    q delta sigma hdelta steps mu0 hq hsigma hdeltan hdeltaq R hR hRsigma hKR M hwarm i
  let A := actualRawPhaseMean K hK delta (fun j => (sigma j) ^ 2) hdelta steps mu0 i
  let B : ENNReal := (steps i : ENNReal) * M i
  calc
    (∫⁻ x, Ttc.SequentialCost.stepMean
        (concreteCostedPhaseSchedule K hK delta (fun j => (sigma j) ^ 2) hdelta steps) i x
      ∂costedPhaseStateMarginal
        (concreteCostedPhaseSchedule K hK delta (fun j => (sigma j) ^ 2)
          hdelta steps) mu0 i) <= 8 * A := hrestart i hi
    _ <= 8 * (6 * A) := mul_le_mul_left' (by
      calc A = 1 * A := by simp
           _ <= 6 * A := mul_le_mul_right' (by norm_num) A) 8
    _ <= 8 * (10 * B) := mul_le_mul_left' (by simpa only [A, B] using hraw) 8
    _ = 80 * B := by
      rw [← mul_assoc]
      norm_num

section DirectSequential

open Ttc.CVSequentialPhaseSampler
open Ttc.CVDirectSequentialAccuracy
open Ttc.CVDirectSequentialWarm
open Ttc.CVCorrected
open Arlib.GaussianCooling

variable {E : Type*} [MeasurableSpace E]

/-- Existing warmness propagation supplies the `last_warm` field of the operational
dependence package.  Thus, after this constructor, the phase-specific analytic obligation
is exactly distributional mixing of the honest pathwise kernel from an arbitrary
`2 * accumulatedWarm`-warm incoming law.

This theorem is deliberately stated for an arbitrary inhomogeneous kernel: it applies to
`pathwiseSourcePhaseSchedule` once its normalize-after-restart mixing theorem is supplied. -/
noncomputable def directSequentialOperational_of_warmPropagation
    (P : Nat → Kernel E E) [∀ i, IsMarkovKernel (P i)]
    (mu0 : Measure E) [IsProbabilityMeasure mu0]
    (V : Nat → (Nat → E) → Real) (m : Nat) (eta : Real)
    (pi tau : Nat → Measure E)
    [∀ i, IsProbabilityMeasure (pi i)] [∀ i, IsProbabilityMeasure (tau i)]
    (M0 C : ENNReal)
    (hstart : IsWarm M0 mu0 (pi 0))
    (hpreserve : ∀ i (rho : Measure E) (M : ENNReal),
      IsWarm M rho (pi i) → IsWarm M (sampleFromKernel (P i) rho) (pi i))
    (hsucc : ∀ i, IsWarm C (pi i) (pi (i + 1)))
    (mixError : Nat → ENNReal) (hmix_top : ∀ i, mixError i ≠ ⊤)
    (hmix : ∀ i (rho : Measure E),
      IsWarm (2 * accumulatedWarm M0 C i) rho (pi i) →
      IsProbabilityMeasure rho →
        TVLe (sampleFromKernel (P i) rho) (tau i) (mixError i))
    (u : (i : Nat) → (Finset.Iic i → E) → Real) (v : Nat → E → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i,
      accuracyU (inhomogeneousPathMeasure P mu0) V (correctedAlpha m eta) i =
        fun omega ↦ u i (Preorder.frestrictLe i omega))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (omega (i + 1)))
    (hbudget : ∀ i, 2 * (mixError i).toReal ≤ correctedNu m eta) :
    DirectSequentialOperational P mu0 V m eta where
  pi := pi
  tau := tau
  pi_prob := fun i ↦ inferInstance
  tau_prob := fun i ↦ inferInstance
  warmConst := accumulatedWarm M0 C
  mixError := mixError
  mixError_ne_top := hmix_top
  u := u
  v := v
  measurable_u := hu
  measurable_v := hv
  U_eq := hU
  V_eq := hV
  last_warm := fun i ↦
    isWarm_historyLast_inhomogeneousPathMeasure P mu0 pi hstart hpreserve hsucc i
  distributional_mixing := hmix
  dependence_budget := hbudget

end DirectSequential

section ConcreteDirectSequential

open Ttc.CVSequentialPhaseSampler
open Ttc.CVDirectSequentialAccuracy
open Ttc.CVCorrected
open Ttc.CVSourceCorrectedPathAccuracy
open Arlib.GaussianCooling

/-- Build the dependence package directly from warmth of the *actual incoming marginals*
of the concrete costed execution.  Full-path lumping identifies those marginals with the
history-last marginals of the source path law, so no separate warmness-preservation
argument for the nonlinear pathwise restart kernel is needed.

After the concrete refinement and marginal warmth have been established, `hmix` is the
single remaining phase-kernel hypothesis: distributional TV mixing for bind-after-statewise
normalization. -/
noncomputable def pathwiseDirectSequentialOperational_of_costedMarginalWarm
    {K : Set (State n)} (hK : MeasurableSet K)
    (delta sigmaSq : Nat → Real) (hdelta : ∀ i, 0 < delta i)
    (steps : Nat → Nat) (hsigma : ∀ i, 0 < sigmaSq i)
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1)
    (mu0 : Measure (State n)) [IsProbabilityMeasure mu0]
    (m : Nat) (phaseBound : Nat → ENNReal)
    (href : CostedPhaseKernelRefinement
      (pathwiseSourcePhaseSchedule K hK delta sigmaSq steps)
      (concreteCostedPhaseSchedule K hK delta sigmaSq hdelta steps)
      mu0 m phaseBound)
    (V : Nat → (Nat → State n) → Real) (eta : Real)
    (pi tau : Nat → Measure (State n))
    [∀ i, IsProbabilityMeasure (pi i)] [∀ i, IsProbabilityMeasure (tau i)]
    (warmConst mixError : Nat → ENNReal)
    (hwarm : ∀ i, IsWarm (warmConst i)
      (costedPhaseStateMarginal
        (concreteCostedPhaseSchedule K hK delta sigmaSq hdelta steps) mu0 i)
      (pi i))
    (hmix_top : ∀ i, mixError i ≠ ⊤)
    (hmix : ∀ i (rho : Measure (State n)),
      IsWarm (2 * warmConst i) rho (pi i) → IsProbabilityMeasure rho →
        TVLe (sampleFromKernel
          (pathwiseSourcePhaseSchedule K hK delta sigmaSq steps i) rho)
          (tau i) (mixError i))
    (u : (i : Nat) → (Finset.Iic i → State n) → Real)
    (v : Nat → State n → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i,
      accuracyU
          (correctedSourcePathLaw K hK delta sigmaSq steps hsigma hc2 mu0)
          V (correctedAlpha m eta) i =
        fun omega ↦ u i (Preorder.frestrictLe i omega))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (omega (i + 1)))
    (hbudget : ∀ i, 2 * (mixError i).toReal ≤ correctedNu m eta) :
    @DirectSequentialOperational (State n) _
      (pathwiseSourcePhaseSchedule K hK delta sigmaSq steps)
      (fun i ↦ isMarkovKernel_pathwiseSourcePhaseSchedule K hK delta sigmaSq steps
        hsigma hc2 i) mu0 inferInstance V m eta := by
  let P := pathwiseSourcePhaseSchedule K hK delta sigmaSq steps
  let Q := concreteCostedPhaseSchedule K hK delta sigmaSq hdelta steps
  let muPath := correctedSourcePathLaw K hK delta sigmaSq steps hsigma hc2 mu0
  letI hP : ∀ i, IsMarkovKernel
      (pathwiseSourcePhaseSchedule K hK delta sigmaSq steps i) :=
    fun i ↦ isMarkovKernel_pathwiseSourcePhaseSchedule K hK delta sigmaSq steps
      hsigma hc2 i
  have hpath : Measure.map (Ttc.CostedStatefulSpeedyPhases.statePath (n := n))
      (costedPhaseOneRunLaw Q mu0) = muPath := by
    change Measure.map (Ttc.SequentialCostedPathLumping.pathMap Prod.snd)
        (Ttc.SequentialCost.execution Q mu0) = _
    simpa only [P, Q, muPath, correctedSourcePathLaw] using
      (Ttc.SequentialCostedPathLumping.map_statePath_execution Q P mu0 href.forgetCost)
  have hmarg : ∀ i,
      muPath.map (fun omega ↦ omega i) = costedPhaseStateMarginal Q mu0 i := by
    intro i
    rw [← hpath]
    unfold costedPhaseStateMarginal costedPhaseOneRunLaw
    rw [Measure.map_map (measurable_pi_apply i)
      Ttc.CostedStatefulSpeedyPhases.measurable_statePath]
    rfl
  refine
    { pi := pi
      tau := tau
      pi_prob := fun i ↦ inferInstance
      tau_prob := fun i ↦ inferInstance
      warmConst := warmConst
      mixError := mixError
      mixError_ne_top := hmix_top
      u := u
      v := v
      measurable_u := hu
      measurable_v := hv
      U_eq := hU
      V_eq := hV
      last_warm := ?_
      distributional_mixing := hmix
      dependence_budget := hbudget }
  intro i
  let last : (Finset.Iic i → State n) → State n :=
    fun h ↦ h ⟨i, Finset.mem_Iic.2 le_rfl⟩
  have hlast_meas : Measurable last := measurable_pi_apply _
  have hlast :
      ((muPath.map (Preorder.frestrictLe i)).map
          last) =
        muPath.map (fun omega ↦ omega i) := by
    calc
      _ = muPath.map (last ∘ Preorder.frestrictLe i) :=
        Measure.map_map hlast_meas (Preorder.measurable_frestrictLe i)
      _ = muPath.map (fun omega ↦ omega i) := by
        congr 1
  change IsWarm (warmConst i)
    ((muPath.map (Preorder.frestrictLe i)).map last) (pi i)
  rw [hlast, hmarg i]
  exact hwarm i

end ConcreteDirectSequential

section OneRunCapstone

open Ttc.CVSourcePolynomialCutoffCapstone
open Ttc.CVSourceCorrectedPathAccuracy

/-- Feed an average-cost refinement and a source-path accuracy theorem directly into the
one-run certificate used by the polynomial cutoff/median capstone.  In particular, this
uses `CostedPhaseKernelRefinement.phaseMean`, not a false uniform Dirac-start estimate. -/
theorem sourceOneRunCertificate_of_costedPhaseRefinement
    {K : Set (State n)} (hK : MeasurableSet K)
    (delta sigmaSq : Nat → Real) (steps : Nat → Nat)
    (hsigma : ∀ i, 0 < sigmaSq i)
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1)
    (Q : Nat → Kernel (State n) (ENNReal × State n))
    [∀ i, IsMarkovKernel (Q i)]
    (mu0 : Measure (State n)) [IsProbabilityMeasure mu0]
    (m : Nat) (phaseBound : Nat → ENNReal)
    (href : CostedPhaseKernelRefinement
      (pathwiseSourcePhaseSchedule K hK delta sigmaSq steps) Q mu0 m phaseBound)
    (est : (Nat → State n) → Real) (hest : Measurable est)
    {runtimeConstant R eps lo hi : Real}
    (hsum : (∑ i ∈ Finset.range m, phaseBound i) ≤
      sourceOneRunQueryBudget runtimeConstant n R eps)
    (haccuracy : 4 / 5 ≤
      (correctedSourcePathLaw K hK delta sigmaSq steps hsigma hc2 mu0).real
        {omega | est omega ∈ Icc lo hi}) :
    SourceOneRunCertificate
      (costedPhaseOneRunLaw Q mu0) (costedPhaseOneRunQueries m)
      (costedPhaseOneRunValue est) runtimeConstant n R eps lo hi := by
  letI : IsProbabilityMeasure (costedPhaseOneRunLaw Q mu0) := by
    unfold costedPhaseOneRunLaw
    infer_instance
  refine
    { probability := inferInstance
      cost_measurable := measurable_costedPhaseOneRunQueries m
      value_measurable := measurable_costedPhaseOneRunValue hest
      expected_queries := ?_
      accuracy := ?_ }
  · exact (expected_costedPhaseOneRunQueries_le_of_phaseMeans Q mu0 m phaseBound
      href.phaseMean).trans hsum
  · rw [measureReal_costedPhaseOneRun_success hK delta sigmaSq steps hsigma hc2 Q
      href.forgetCost mu0 est hest lo hi]
    simpa only [correctedSourcePathLaw] using haccuracy

end OneRunCapstone

#print axioms six_mul_actualRawPhaseMean_le_ten_mul_adjustable
#print axioms concreteCostedPhaseRefinement_of_sequentialWarm
#print axioms directSequentialOperational_of_warmPropagation
#print axioms pathwiseDirectSequentialOperational_of_costedMarginalWarm
#print axioms sourceOneRunCertificate_of_costedPhaseRefinement

end Ttc.CVConcreteSequentialWarmAssembly
