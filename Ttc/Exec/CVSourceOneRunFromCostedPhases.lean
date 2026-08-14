/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Exec.CostedPathwisePhaseLumping
import Ttc.Exec.CVSourcePolynomialCutoffCapstone

/-!
# A concrete CV one-run certificate from costed phase kernels

This file turns a supplied state-indexed costed phase kernel into the exact common
cost/output law required by `SourceOneRunCertificate`.  Full-path lumping transports the
source-path accuracy event, while `SequentialCost.lintegral_totalCost_le_sum_uniformBounds`
adds the pointwise phase costs.  Thus the operational residue consists of the two expected
pointwise statements:

* forgetting phase cost gives `pathwiseSourcePhaseSchedule`;
* the conditional mean cost of phase `i`, averaged under its actual incoming marginal, is
  at most `phaseBound i`.

The source-path accuracy theorem and the scalar sum of phase bounds remain explicit inputs;
they are analytic/arithmetic facts, not additional execution semantics.  A stronger
pointwise-cost convenience theorem is retained for callers that genuinely have such a
bound, but the public constructor uses the averaged interface.
-/

namespace Ttc.CVSourceOneRunFromCostedPhases

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.GaussianCooling
open Ttc.CostedStatefulSpeedyPhases
open Ttc.CostedPathwisePhaseLumping
open Ttc.CVSourcePolynomialCutoffCapstone
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev CostedPath (n : Nat) := Nat -> ENNReal × State n
abbrev StatePath (n : Nat) := Nat -> State n

/-- The actual one-run law obtained by sequentially binding the supplied costed phase
kernels. -/
noncomputable def costedPhaseOneRunLaw
    (Q : Nat -> Kernel (State n) (ENNReal × State n))
    [forall i, IsMarkovKernel (Q i)] (mu0 : Measure (State n)) :
    Measure (CostedPath n) :=
  Ttc.SequentialCost.execution Q mu0

/-- The estimator reads only the projected state path. -/
def costedPhaseOneRunValue (est : StatePath n -> Real) (omega : CostedPath n) : Real :=
  est (statePath omega)

/-- The recorded membership-query count through the first `m` phases. -/
noncomputable def costedPhaseOneRunQueries (m : Nat) (omega : CostedPath n) : ENNReal :=
  Ttc.SequentialCost.totalCost m omega

/-- The actual incoming state law at phase `i` of the costed execution. -/
noncomputable def costedPhaseStateMarginal
    (Q : Nat -> Kernel (State n) (ENNReal × State n))
    [forall i, IsMarkovKernel (Q i)] (mu0 : Measure (State n)) (i : Nat) :
    Measure (State n) :=
  Measure.map (fun omega => (omega i).2) (costedPhaseOneRunLaw Q mu0)

theorem measurable_costedPhaseOneRunValue {est : StatePath n -> Real}
    (hest : Measurable est) : Measurable (costedPhaseOneRunValue est) :=
  hest.comp measurable_statePath

theorem measurable_costedPhaseOneRunQueries (m : Nat) :
    Measurable (costedPhaseOneRunQueries (n := n) m) :=
  Ttc.SequentialCost.measurable_totalCost m

/-- Pointwise conditional phase-cost bounds add to an expected total-cost bound on the
actual sequential execution. -/
theorem expected_costedPhaseOneRunQueries_le
    (Q : Nat -> Kernel (State n) (ENNReal × State n))
    [forall i, IsMarkovKernel (Q i)]
    (mu0 : Measure (State n)) [IsProbabilityMeasure mu0]
    (m : Nat) (phaseBound : Nat -> ENNReal)
    (hphase : forall i, i < m -> forall x,
      Ttc.SequentialCost.stepMean Q i x <= phaseBound i) :
    (∫⁻ omega, costedPhaseOneRunQueries m omega ∂costedPhaseOneRunLaw Q mu0) <=
      ∑ i ∈ Finset.range m, phaseBound i := by
  exact Ttc.SequentialCost.lintegral_totalCost_le_sum_uniformBounds
    Q mu0 m phaseBound hphase

/-- The exact, weakest additive cost interface: bound each conditional phase mean only
after averaging it against the actual incoming marginal.  This is the form discharged by
warm-start wasted-step estimates; a uniform Dirac-start bound is generally false. -/
theorem expected_costedPhaseOneRunQueries_le_of_phaseMeans
    (Q : Nat -> Kernel (State n) (ENNReal × State n))
    [forall i, IsMarkovKernel (Q i)]
    (mu0 : Measure (State n)) [IsProbabilityMeasure mu0]
    (m : Nat) (phaseBound : Nat -> ENNReal)
    (hphaseMean : forall i, i < m ->
      (∫⁻ x, Ttc.SequentialCost.stepMean Q i x
        ∂costedPhaseStateMarginal Q mu0 i) <= phaseBound i) :
    (∫⁻ omega, costedPhaseOneRunQueries m omega ∂costedPhaseOneRunLaw Q mu0) <=
      ∑ i ∈ Finset.range m, phaseBound i := by
  unfold costedPhaseOneRunQueries costedPhaseOneRunLaw at ⊢
  rw [Ttc.SequentialCost.lintegral_totalCost_eq_sum_stateMeans]
  apply Finset.sum_le_sum
  intro i hi
  simpa only [costedPhaseStateMarginal, costedPhaseOneRunLaw] using
    hphaseMean i (Finset.mem_range.1 hi)

/-- Full-path lumping transports a measurable source-path success event to the actual
costed execution without a TV loss. -/
theorem measureReal_costedPhaseOneRun_success
    {K : Set (State n)} (hK : MeasurableSet K)
    (delta sigmaSq : Nat -> Real) (steps : Nat -> Nat)
    (hsigma : forall i, 0 < sigmaSq i)
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 <= 1)
    (Q : Nat -> Kernel (State n) (ENNReal × State n))
    [forall i, IsMarkovKernel (Q i)]
    (hforget : forall i x, Measure.map Prod.snd (Q i x) =
      pathwiseSourcePhaseSchedule K hK delta sigmaSq steps i x)
    (mu0 : Measure (State n)) [IsProbabilityMeasure mu0]
    (est : StatePath n -> Real) (hest : Measurable est) (lo hi : Real) :
    (costedPhaseOneRunLaw Q mu0).real
        {omega | costedPhaseOneRunValue est omega ∈ Icc lo hi} =
      (@inhomogeneousPathMeasure _ _
        (pathwiseSourcePhaseSchedule K hK delta sigmaSq steps)
        (fun i => isMarkovKernel_pathwiseSourcePhaseSchedule K hK delta sigmaSq steps
          hsigma hc2 i) mu0).real
        {omega | est omega ∈ Icc lo hi} := by
  let G : Set (StatePath n) := {omega | est omega ∈ Icc lo hi}
  have hG : MeasurableSet G := measurableSet_Icc.preimage hest
  have h := measureReal_stateEvent_eq_costedPathwisePhaseExecution K hK delta sigmaSq
    steps hsigma hc2 Q hforget mu0 G hG
  simpa only [costedPhaseOneRunLaw, costedPhaseOneRunValue, G,
    preimage_setOf_eq] using h

/-- Minimal operational refinement of a state schedule by recorded-cost kernels.
The cost field is deliberately averaged against the actual incoming phase marginal; a
uniform point-start waiting-time bound is unavailable for the proper-proposal walk. -/
structure CostedPhaseKernelRefinement
    (P : Nat -> Kernel (State n) (State n))
    (Q : Nat -> Kernel (State n) (ENNReal × State n))
    [forall i, IsMarkovKernel (Q i)]
    (mu0 : Measure (State n)) (m : Nat) (phaseBound : Nat -> ENNReal) : Prop where
  forgetCost : forall i x, Measure.map Prod.snd (Q i x) = P i x
  phaseMean : forall i, i < m ->
    (∫⁻ x, Ttc.SequentialCost.stepMean Q i x
      ∂costedPhaseStateMarginal Q mu0 i) <= phaseBound i

/-- Fixed-input constructor for the exact one-run certificate consumed by the source
cutoff capstone.  The only kernel-specific premises are `hforget` and `hphase`. -/
theorem sourceOneRunCertificate_of_costedPhases
    {K : Set (State n)} (hK : MeasurableSet K)
    (delta sigmaSq : Nat -> Real) (steps : Nat -> Nat)
    (hsigma : forall i, 0 < sigmaSq i)
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 <= 1)
    (Q : Nat -> Kernel (State n) (ENNReal × State n))
    [forall i, IsMarkovKernel (Q i)]
    (hforget : forall i x, Measure.map Prod.snd (Q i x) =
      pathwiseSourcePhaseSchedule K hK delta sigmaSq steps i x)
    (mu0 : Measure (State n)) [IsProbabilityMeasure mu0]
    (m : Nat) (phaseBound : Nat -> ENNReal)
    (hphase : forall i, i < m -> forall x,
      Ttc.SequentialCost.stepMean Q i x <= phaseBound i)
    (est : StatePath n -> Real) (hest : Measurable est)
    {runtimeConstant R eps lo hi : Real}
    (hsum : (∑ i ∈ Finset.range m, phaseBound i) <=
      sourceOneRunQueryBudget runtimeConstant n R eps)
    (haccuracy : 4 / 5 <=
      (@inhomogeneousPathMeasure _ _
        (pathwiseSourcePhaseSchedule K hK delta sigmaSq steps)
        (fun i => isMarkovKernel_pathwiseSourcePhaseSchedule K hK delta sigmaSq steps
          hsigma hc2 i) mu0).real {omega | est omega ∈ Icc lo hi}) :
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
  · exact (expected_costedPhaseOneRunQueries_le Q mu0 m phaseBound hphase).trans hsum
  · rw [measureReal_costedPhaseOneRun_success hK delta sigmaSq steps hsigma hc2 Q
      hforget mu0 est hest lo hi]
    exact haccuracy

/-! ## Input-indexed public assembly -/

/-- All generic public one-run certificates follow from state-indexed costed phase kernels.

`P a` is the declared state-path schedule and `Q a` is its operational costed refinement.
The two genuinely operational assumptions are pointwise:

* `hforget a i x` identifies the state marginal of one costed phase;
* `hphaseMean a i` bounds its conditional expected cost under the actual incoming law.

`hsum` is deterministic runtime arithmetic, and `haccuracy` is the already-proved
source-path accuracy theorem. -/
theorem sourcePublicOneRunCertificates_of_costedPhases
    (runtimeConstant : Real) (radialR : Set (Ttc.Space n) -> Real)
    (P : Ttc.CVAdaptive.VolumeInput n -> Nat -> Kernel (State n) (State n))
    [forall a i, IsMarkovKernel (P a i)]
    (Q : Ttc.CVAdaptive.VolumeInput n -> Nat ->
      Kernel (State n) (ENNReal × State n))
    [forall a i, IsMarkovKernel (Q a i)]
    (mu0 : Ttc.CVAdaptive.VolumeInput n -> Measure (State n))
    [forall a, IsProbabilityMeasure (mu0 a)]
    (m : Ttc.CVAdaptive.VolumeInput n -> Nat)
    (phaseBound : Ttc.CVAdaptive.VolumeInput n -> Nat -> ENNReal)
    (est : Ttc.CVAdaptive.VolumeInput n -> StatePath n -> Real)
    (hest : forall a, Measurable (est a))
    (hop : forall a, CostedPhaseKernelRefinement (P a) (Q a) (mu0 a)
      (m a) (phaseBound a))
    (hsum : forall a, (∑ i ∈ Finset.range (m a), phaseBound a i) <=
      sourceOneRunQueryBudget runtimeConstant n (radialR a.1) a.2.1)
    (haccuracy : forall (K : Set (Ttc.Space n)) (eps p : Real),
      0 < eps -> 0 < p -> p < 1 -> Convex Real K ->
      Metric.ball (0 : Ttc.Space n) 1 ⊆ K -> volume K ≠ ⊤ ->
      4 / 5 <= (inhomogeneousPathMeasure (P (K, eps, p)) (mu0 (K, eps, p))).real
        {omega | est (K, eps, p) omega ∈
          Icc ((1 - eps) * (volume K).toReal)
            ((1 + eps) * (volume K).toReal)}) :
    SourcePublicOneRunCertificates n runtimeConstant radialR
      (fun _a => CostedPath n)
      (fun a => costedPhaseOneRunLaw (Q a) (mu0 a))
      (fun a => costedPhaseOneRunQueries (m a))
      (fun a => costedPhaseOneRunValue (est a)) := by
  refine
    { probability := ?_
      cost_measurable := ?_
      value_measurable := ?_
      expected_queries := ?_
      accuracy := ?_ }
  · intro a
    unfold costedPhaseOneRunLaw
    infer_instance
  · intro a
    exact measurable_costedPhaseOneRunQueries (m a)
  · intro a
    exact measurable_costedPhaseOneRunValue (hest a)
  · intro a
    exact (expected_costedPhaseOneRunQueries_le_of_phaseMeans (Q a) (mu0 a) (m a)
      (phaseBound a) (hop a).phaseMean).trans (hsum a)
  · intro K eps p heps hp hp1 hKc hball hfin
    let a : Ttc.CVAdaptive.VolumeInput n := (K, eps, p)
    have hpath : Measure.map (statePath (n := n))
        (costedPhaseOneRunLaw (Q a) (mu0 a)) =
        inhomogeneousPathMeasure (P a) (mu0 a) := by
      change Measure.map (Ttc.SequentialCostedPathLumping.pathMap Prod.snd)
        (Ttc.SequentialCost.execution (Q a) (mu0 a)) = _
      exact Ttc.SequentialCostedPathLumping.map_statePath_execution
        (Q a) (P a) (mu0 a) (hop a).forgetCost
    let G : Set (StatePath n) := {omega | est a omega ∈
      Icc ((1 - eps) * (volume K).toReal) ((1 + eps) * (volume K).toReal)}
    have hG : MeasurableSet G := measurableSet_Icc.preimage (hest a)
    have heq : (costedPhaseOneRunLaw (Q a) (mu0 a)).real
        (statePath ⁻¹' G) =
        (inhomogeneousPathMeasure (P a) (mu0 a)).real G := by
      apply measureReal_stateEvent_eq_of_path_lumping (Q a) (P a) (mu0 a) hpath G hG
    change 4 / 5 <= (costedPhaseOneRunLaw (Q a) (mu0 a)).real (statePath ⁻¹' G)
    rw [heq]
    exact haccuracy K eps p heps hp hp1 hKc hball hfin

/-- The conditional public expected-query volume oracle obtained from costed phase kernels.
No packaging hypothesis remains beyond the pointwise phase interfaces and the separate
source-path accuracy/runtime arithmetic premises displayed above. -/
noncomputable def expectedQueryVolumeAlgorithmOfCostedPhases
    (runtimeConstant : Real) (radialR : Set (Ttc.Space n) -> Real)
    (P : Ttc.CVAdaptive.VolumeInput n -> Nat -> Kernel (State n) (State n))
    [forall a i, IsMarkovKernel (P a i)]
    (Q : Ttc.CVAdaptive.VolumeInput n -> Nat ->
      Kernel (State n) (ENNReal × State n))
    [forall a i, IsMarkovKernel (Q a i)]
    (mu0 : Ttc.CVAdaptive.VolumeInput n -> Measure (State n))
    [forall a, IsProbabilityMeasure (mu0 a)]
    (m : Ttc.CVAdaptive.VolumeInput n -> Nat)
    (phaseBound : Ttc.CVAdaptive.VolumeInput n -> Nat -> ENNReal)
    (est : Ttc.CVAdaptive.VolumeInput n -> StatePath n -> Real)
    (hest : forall a, Measurable (est a))
    (hop : forall a, CostedPhaseKernelRefinement (P a) (Q a) (mu0 a)
      (m a) (phaseBound a))
    (hsum : forall a, (∑ i ∈ Finset.range (m a), phaseBound a i) <=
      sourceOneRunQueryBudget runtimeConstant n (radialR a.1) a.2.1)
    (haccuracy : forall (K : Set (Ttc.Space n)) (eps p : Real),
      0 < eps -> 0 < p -> p < 1 -> Convex Real K ->
      Metric.ball (0 : Ttc.Space n) 1 ⊆ K -> volume K ≠ ⊤ ->
      4 / 5 <= (inhomogeneousPathMeasure (P (K, eps, p)) (mu0 (K, eps, p))).real
        {omega | est (K, eps, p) omega ∈
          Icc ((1 - eps) * (volume K).toReal)
            ((1 + eps) * (volume K).toReal)}) :
    Ttc.ExpectedQueryVolumeAlgorithm n :=
  expectedQueryVolumeAlgorithmOfSourceOneRunCertificates n runtimeConstant radialR
    (fun _a => CostedPath n)
    (fun a => costedPhaseOneRunLaw (Q a) (mu0 a))
    (fun a => costedPhaseOneRunQueries (m a))
    (fun a => costedPhaseOneRunValue (est a))
    (sourcePublicOneRunCertificates_of_costedPhases runtimeConstant radialR P Q mu0 m
      phaseBound est hest hop hsum haccuracy)

#print axioms expected_costedPhaseOneRunQueries_le
#print axioms expected_costedPhaseOneRunQueries_le_of_phaseMeans
#print axioms measureReal_costedPhaseOneRun_success
#print axioms sourceOneRunCertificate_of_costedPhases
#print axioms sourcePublicOneRunCertificates_of_costedPhases
#print axioms expectedQueryVolumeAlgorithmOfCostedPhases

end Ttc.CVSourceOneRunFromCostedPhases
