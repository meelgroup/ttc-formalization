import Ttc.Exec.FiniteContinuingRetryGaussianSelfPhase
import Ttc.Exec.FiniteContinuingRetrySelfDecomposition
import Ttc.Exec.CVConcreteSequentialWarmAssembly
import Ttc.Exec.CVGenericSequentialPathAccuracy

/-! Sequential operational schedule made from self-fallback finite Gaussian retries. -/

namespace Ttc.CVFiniteContinuingSelfSchedule

open MeasureTheory ProbabilityTheory Set
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler
open Ttc.CVDirectSequentialAccuracy
open Ttc.CVConcreteSequentialWarmAssembly
open Ttc.CVDirectSequentialWarm
open Ttc.CVSourceOneRunFromCostedPhases
open Ttc.CostedPathwisePhaseLumping
open Ttc.FiniteContinuingRetryGaussianSelfPhase
open Ttc.FiniteContinuingRetrySelfDecomposition
open scoped ENNReal Classical Pointwise

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

noncomputable def selfRetryCostedSchedule
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat) :
    Nat → Kernel (State n) (ENNReal × State n) := fun i ↦
  gaussianSelfFinitePhaseCostedKernel K hK (delta i) (sigmaSq i) (shrink i)
    (hdelta i) (hshrink i) (retrySteps i) (retries i)

instance selfRetryCostedSchedule.isMarkovKernel
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat) (i : Nat) :
    IsMarkovKernel (selfRetryCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
      retrySteps retries i) := by
  unfold selfRetryCostedSchedule
  infer_instance

noncomputable def selfRetryStateSchedule
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat) :
    Nat → Kernel (State n) (State n) := fun i ↦
  Kernel.map (selfRetryCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
    retrySteps retries i) Prod.snd

instance selfRetryStateSchedule.isMarkovKernel
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat) (i : Nat) :
    IsMarkovKernel (selfRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink
      retrySteps retries i) := by
  unfold selfRetryStateSchedule
  exact Kernel.IsMarkovKernel.map _ measurable_snd

theorem map_snd_selfRetryCostedSchedule
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (i : Nat) (x : State n) :
    Measure.map Prod.snd
      (selfRetryCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
        retrySteps retries i x) =
      selfRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink
        retrySteps retries i x := by
  unfold selfRetryStateSchedule
  rw [Kernel.map_apply _ measurable_snd]

theorem sampleFromKernel_map_self {B D : Type*} [MeasurableSpace B] [MeasurableSpace D]
    (Q : Kernel (State n) B) [IsMarkovKernel Q]
    (f : B → D) (hf : Measurable f)
    (rho : Measure (State n)) [IsProbabilityMeasure rho] :
    sampleFromKernel (Kernel.map Q f) rho = Measure.map f (sampleFromKernel Q rho) := by
  unfold sampleFromKernel
  rw [← Kernel.deterministic_comp_eq_map hf Q, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map hf]

/-- Arbitrary-law output identity for one self-fallback phase. -/
theorem sampleFrom_selfRetryStateSchedule
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (rho : Measure (State n)) [IsProbabilityMeasure rho] (i : Nat) :
    sampleFromKernel
      (selfRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink
        retrySteps retries i) rho =
      Measure.map Ttc.FiniteContinuingRetry.output
        (Ttc.FiniteContinuingRetrySelfFallback.selfMarginal
          (fun j ↦ Ttc.FiniteContinuingRetryGaussian.combinedRoundCostedKernel
            K hK (delta i) (sigmaSq i) (hdelta i) (retrySteps i j))
          (Ttc.FiniteContinuingRetryGaussian.costedCombinedAccept K (shrink i) (sigmaSq i))
          (Ttc.FiniteContinuingRetryGaussian.measurableSet_costedCombinedAccept hK
            (hshrink i))
          Ttc.FiniteContinuingRetryGaussian.rejectedNext
          (Ttc.FiniteContinuingRetryGaussian.acceptedOutput (shrink i))
          Ttc.FiniteContinuingRetryGaussian.measurable_rejectedNext
          (Ttc.FiniteContinuingRetryGaussian.measurable_acceptedOutput (shrink i))
          Ttc.FiniteContinuingRetryGaussian.roundQueryCost
          Ttc.FiniteContinuingRetryGaussian.measurable_roundQueryCost rho (retries i)) := by
  unfold selfRetryStateSchedule
  rw [sampleFromKernel_map_self _ Prod.snd measurable_snd rho]
  unfold selfRetryCostedSchedule gaussianSelfFinitePhaseCostedKernel
  rw [sampleFromKernel_map_self _ selfPhaseCostOutput measurable_selfPhaseCostOutput rho,
    Measure.map_map measurable_snd measurable_selfPhaseCostOutput]
  change Measure.map Ttc.FiniteContinuingRetry.output
      (sampleFromKernel
        (gaussianSelfRetryStateKernel K hK (delta i) (sigmaSq i) (shrink i)
          (hdelta i) (hshrink i) (retrySteps i) (retries i)) rho) = _
  rw [sampleFrom_gaussianSelfRetryStateKernel]

/-- Local accepted-increment domination plus incoming-to-next-target warmth supplies the
complete phase-to-next-target warmness recurrence used above. -/
theorem isWarm_sampleFrom_selfRetryStateSchedule_of_firstHit
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (rho piNext : Measure (State n)) [IsProbabilityMeasure rho]
    (i : Nat) {M Cwarm : ENNReal}
    (hrho : IsWarm M rho piNext)
    (hincrement : ∀ j : Fin (retries i),
      IsWarm (Cwarm * M)
        (firstHitIncrement
          (fun q ↦ Ttc.FiniteContinuingRetryGaussian.combinedRoundCostedKernel
            K hK (delta i) (sigmaSq i) (hdelta i) (retrySteps i q))
          (Ttc.FiniteContinuingRetryGaussian.costedCombinedAccept K (shrink i) (sigmaSq i))
          (Ttc.FiniteContinuingRetryGaussian.measurableSet_costedCombinedAccept hK
            (hshrink i))
          Ttc.FiniteContinuingRetryGaussian.rejectedNext
          (Ttc.FiniteContinuingRetryGaussian.acceptedOutput (shrink i))
          Ttc.FiniteContinuingRetryGaussian.measurable_rejectedNext
          (Ttc.FiniteContinuingRetryGaussian.measurable_acceptedOutput (shrink i))
          Ttc.FiniteContinuingRetryGaussian.roundQueryCost
          Ttc.FiniteContinuingRetryGaussian.measurable_roundQueryCost rho j) piNext) :
    IsWarm (((retries i : Nat) : ENNReal) * (Cwarm * M) + M)
      (sampleFromKernel
        (selfRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink
          retrySteps retries i) rho) piNext := by
  rw [sampleFrom_selfRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink
    retrySteps retries rho i]
  exact isWarm_map_output_selfMarginal_of_firstHit
    (fun q ↦ Ttc.FiniteContinuingRetryGaussian.combinedRoundCostedKernel
      K hK (delta i) (sigmaSq i) (hdelta i) (retrySteps i q))
    (Ttc.FiniteContinuingRetryGaussian.costedCombinedAccept K (shrink i) (sigmaSq i))
    (Ttc.FiniteContinuingRetryGaussian.measurableSet_costedCombinedAccept hK (hshrink i))
    Ttc.FiniteContinuingRetryGaussian.rejectedNext
    (Ttc.FiniteContinuingRetryGaussian.acceptedOutput (shrink i))
    Ttc.FiniteContinuingRetryGaussian.measurable_rejectedNext
    (Ttc.FiniteContinuingRetryGaussian.measurable_acceptedOutput (shrink i))
    Ttc.FiniteContinuingRetryGaussian.roundQueryCost
    Ttc.FiniteContinuingRetryGaussian.measurable_roundQueryCost rho piNext (retries i)
    hrho hincrement

/-- The sole cost binder is averaged against the actual incoming marginal, exactly as in
`CostedPhaseKernelRefinement`; no point-start cost claim is introduced. -/
theorem selfRetryCostedPhaseRefinement
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (mu0 : Measure (State n)) [IsProbabilityMeasure mu0]
    (m : Nat) (phaseBound : Nat → ENNReal)
    (hphase : ∀ i, i < m →
      (∫⁻ x, Ttc.SequentialCost.stepMean
        (selfRetryCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
          retrySteps retries) i x
        ∂costedPhaseStateMarginal
          (selfRetryCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
            retrySteps retries) mu0 i) ≤ phaseBound i) :
    CostedPhaseKernelRefinement
      (selfRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink
        retrySteps retries)
      (selfRetryCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
        retrySteps retries)
      mu0 m phaseBound where
  forgetCost := map_snd_selfRetryCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
    retrySteps retries
  phaseMean := hphase

/-- Warmness propagation for a schedule with an explicit phase-dependent budget.  This is
the natural interface for self-fallback rejection: accepted mass and unresolved mass may
increase the bound, but the next phase receives one declared `warmBudget (i+1)`. -/
theorem isWarm_historyLast_of_budgetRecurrence
    (P : Nat → Kernel (State n) (State n)) [∀ i, IsMarkovKernel (P i)]
    (mu0 : Measure (State n)) [IsProbabilityMeasure mu0]
    (pi : Nat → Measure (State n)) (warmBudget : Nat → ENNReal)
    (hstart : IsWarm (warmBudget 0) mu0 (pi 0))
    (hstep : ∀ i (rho : Measure (State n)),
      IsWarm (warmBudget i) rho (pi i) →
      IsProbabilityMeasure rho →
        IsWarm (warmBudget (i + 1)) (sampleFromKernel (P i) rho) (pi (i + 1)))
    (i : Nat) :
    IsWarm (warmBudget i)
      (((inhomogeneousPathMeasure P mu0).map (Preorder.frestrictLe i)).map
        (fun h ↦ h ⟨i, Finset.mem_Iic.2 le_rfl⟩)) (pi i) := by
  have heval : ∀ j, IsWarm (warmBudget j)
      ((inhomogeneousPathMeasure P mu0).map (fun omega ↦ omega j)) (pi j) := by
    intro j
    induction j with
    | zero =>
        simpa only [map_eval_inhomogeneousPathMeasure_zero] using hstart
    | succ j ih =>
        rw [map_eval_inhomogeneousPathMeasure_succ]
        letI : IsProbabilityMeasure
            ((inhomogeneousPathMeasure P mu0).map (fun omega ↦ omega j)) :=
          Measure.isProbabilityMeasure_map (measurable_pi_apply j).aemeasurable
        exact hstep j _ ih inferInstance
  let last : (Finset.Iic i → State n) → State n :=
    fun z ↦ z ⟨i, Finset.mem_Iic.2 le_rfl⟩
  have hlast : Measurable last := measurable_pi_apply _
  have hmap : Measure.map last
      (Measure.map (Preorder.frestrictLe i) (inhomogeneousPathMeasure P mu0)) =
      Measure.map (fun omega : Nat → State n ↦ omega i)
        (inhomogeneousPathMeasure P mu0) := by
    calc
      _ = Measure.map (last ∘ Preorder.frestrictLe i)
          (inhomogeneousPathMeasure P mu0) :=
        Measure.map_map hlast (Preorder.measurable_frestrictLe i)
      _ = Measure.map (fun omega : Nat → State n ↦ omega i)
          (inhomogeneousPathMeasure P mu0) := by congr 1
  change IsWarm (warmBudget i)
    (Measure.map last
      (Measure.map (Preorder.frestrictLe i) (inhomogeneousPathMeasure P mu0))) (pi i)
  rw [hmap]
  exact heval i

/-- `DirectSequentialOperational` from one honest phase-to-next-target warmness recurrence.
This is the shortest operational interface for the self-fallback schedule. -/
noncomputable def selfRetryDirectSequentialOperational_of_budgetRecurrence
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (mu0 : Measure (State n)) [IsProbabilityMeasure mu0]
    (V : Nat → (Nat → State n) → Real) (m : Nat) (eta : Real)
    (pi tau : Nat → Measure (State n))
    [∀ i, IsProbabilityMeasure (pi i)] [∀ i, IsProbabilityMeasure (tau i)]
    (warmBudget mixError : Nat → ENNReal)
    (hstart : IsWarm (warmBudget 0) mu0 (pi 0))
    (hstep : ∀ i (rho : Measure (State n)),
      IsWarm (warmBudget i) rho (pi i) →
      IsProbabilityMeasure rho →
        IsWarm (warmBudget (i + 1))
          (sampleFromKernel
            (selfRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink
              retrySteps retries i) rho) (pi (i + 1)))
    (hmix_top : ∀ i, mixError i ≠ ⊤)
    (hmix : ∀ i (rho : Measure (State n)),
      IsWarm (2 * warmBudget i) rho (pi i) → IsProbabilityMeasure rho →
        TVLe
          (sampleFromKernel
            (selfRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink
              retrySteps retries i) rho)
          (tau i) (mixError i))
    (u : (i : Nat) → (Finset.Iic i → State n) → Real)
    (v : Nat → State n → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i,
      accuracyU
          (inhomogeneousPathMeasure
            (selfRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink
              retrySteps retries) mu0)
          V (Ttc.CVCorrected.correctedAlpha m eta) i =
        fun omega ↦ u i (Preorder.frestrictLe i omega))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (omega (i + 1)))
    (hbudget : ∀ i, 2 * (mixError i).toReal ≤ Ttc.CVCorrected.correctedNu m eta) :
    DirectSequentialOperational
      (selfRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink retrySteps retries)
      mu0 V m eta where
  pi := pi
  tau := tau
  pi_prob := fun _ ↦ inferInstance
  tau_prob := fun _ ↦ inferInstance
  warmConst := warmBudget
  mixError := mixError
  mixError_ne_top := hmix_top
  u := u
  v := v
  measurable_u := hu
  measurable_v := hv
  U_eq := hU
  V_eq := hV
  last_warm := fun i ↦ isWarm_historyLast_of_budgetRecurrence
    (selfRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink retrySteps retries)
    mu0 pi warmBudget hstart hstep i
  distributional_mixing := hmix
  dependence_budget := hbudget

/-- Alternative assembly from warmth of the *actual costed incoming marginals*.  This
avoids committing to any particular phase-to-phase warmness recurrence: full-path cost
erasure identifies these marginals with the history-last laws used by LV2 dependence. -/
noncomputable def selfRetryDirectSequentialOperational_of_costedMarginalWarm
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (mu0 : Measure (State n)) [IsProbabilityMeasure mu0]
    (m : Nat) (phaseBound : Nat → ENNReal)
    (href : CostedPhaseKernelRefinement
      (selfRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink
        retrySteps retries)
      (selfRetryCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
        retrySteps retries) mu0 m phaseBound)
    (V : Nat → (Nat → State n) → Real) (eta : Real)
    (pi tau : Nat → Measure (State n))
    [∀ i, IsProbabilityMeasure (pi i)] [∀ i, IsProbabilityMeasure (tau i)]
    (warmConst mixError : Nat → ENNReal)
    (hwarm : ∀ i, IsWarm (warmConst i)
      (costedPhaseStateMarginal
        (selfRetryCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
          retrySteps retries) mu0 i) (pi i))
    (hmix_top : ∀ i, mixError i ≠ ⊤)
    (hmix : ∀ i (rho : Measure (State n)),
      IsWarm (2 * warmConst i) rho (pi i) → IsProbabilityMeasure rho →
        TVLe
          (sampleFromKernel
            (selfRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink
              retrySteps retries i) rho)
          (tau i) (mixError i))
    (u : (i : Nat) → (Finset.Iic i → State n) → Real)
    (v : Nat → State n → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i,
      accuracyU
          (inhomogeneousPathMeasure
            (selfRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink
              retrySteps retries) mu0)
          V (Ttc.CVCorrected.correctedAlpha m eta) i =
        fun omega ↦ u i (Preorder.frestrictLe i omega))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (omega (i + 1)))
    (hbudget : ∀ i, 2 * (mixError i).toReal ≤ Ttc.CVCorrected.correctedNu m eta) :
    DirectSequentialOperational
      (selfRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink retrySteps retries)
      mu0 V m eta := by
  let P := selfRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink
    retrySteps retries
  let Q := selfRetryCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
    retrySteps retries
  let muPath := inhomogeneousPathMeasure P mu0
  have hpath : Measure.map (Ttc.CostedStatefulSpeedyPhases.statePath (n := n))
      (costedPhaseOneRunLaw Q mu0) = muPath := by
    change Measure.map (Ttc.SequentialCostedPathLumping.pathMap Prod.snd)
      (Ttc.SequentialCost.execution Q mu0) = _
    simpa only [P, Q, muPath] using
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
      pi_prob := fun _ ↦ inferInstance
      tau_prob := fun _ ↦ inferInstance
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
  have hlast : ((muPath.map (Preorder.frestrictLe i)).map last) =
      muPath.map (fun omega ↦ omega i) := by
    calc
      _ = muPath.map (last ∘ Preorder.frestrictLe i) :=
        Measure.map_map hlast_meas (Preorder.measurable_frestrictLe i)
      _ = muPath.map (fun omega ↦ omega i) := by congr 1
  change IsWarm (warmConst i) ((muPath.map (Preorder.frestrictLe i)).map last) (pi i)
  rw [hlast, hmarg i]
  exact hwarm i

/-- Direct corrected-dependence package for the self-fallback schedule.  Retry-specific
analysis is confined to warmth preservation and distributional mixing; all Markov/history
factorization is discharged here. -/
noncomputable def selfRetryDirectSequentialOperational
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (mu0 : Measure (State n)) [IsProbabilityMeasure mu0]
    (V : Nat → (Nat → State n) → Real) (m : Nat) (eta : Real)
    (pi tau : Nat → Measure (State n))
    [∀ i, IsProbabilityMeasure (pi i)] [∀ i, IsProbabilityMeasure (tau i)]
    (M0 C : ENNReal) (hstart : IsWarm M0 mu0 (pi 0))
    (hpreserve : ∀ i (rho : Measure (State n)) (M : ENNReal),
      IsWarm M rho (pi i) →
        IsWarm M
          (sampleFromKernel
            (selfRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink
              retrySteps retries i) rho) (pi i))
    (hsucc : ∀ i, IsWarm C (pi i) (pi (i + 1)))
    (mixError : Nat → ENNReal) (hmix_top : ∀ i, mixError i ≠ ⊤)
    (hmix : ∀ i (rho : Measure (State n)),
      IsWarm (2 * accumulatedWarm M0 C i) rho (pi i) →
      IsProbabilityMeasure rho →
        TVLe
          (sampleFromKernel
            (selfRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink
              retrySteps retries i) rho)
          (tau i) (mixError i))
    (u : (i : Nat) → (Finset.Iic i → State n) → Real)
    (v : Nat → State n → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i,
      accuracyU
          (inhomogeneousPathMeasure
            (selfRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink
              retrySteps retries) mu0)
          V (Ttc.CVCorrected.correctedAlpha m eta) i =
        fun omega ↦ u i (Preorder.frestrictLe i omega))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (omega (i + 1)))
    (hbudget : ∀ i, 2 * (mixError i).toReal ≤ Ttc.CVCorrected.correctedNu m eta) :
    DirectSequentialOperational
      (selfRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink retrySteps retries)
      mu0 V m eta :=
  directSequentialOperational_of_warmPropagation
    (selfRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink retrySteps retries)
    mu0 V m eta pi tau M0 C hstart hpreserve hsucc mixError hmix_top hmix
    u v hu hv hU hV hbudget

#print axioms map_snd_selfRetryCostedSchedule
#print axioms sampleFrom_selfRetryStateSchedule
#print axioms isWarm_sampleFrom_selfRetryStateSchedule_of_firstHit
#print axioms selfRetryCostedPhaseRefinement
#print axioms isWarm_historyLast_of_budgetRecurrence
#print axioms selfRetryDirectSequentialOperational_of_budgetRecurrence
#print axioms selfRetryDirectSequentialOperational_of_costedMarginalWarm
#print axioms selfRetryDirectSequentialOperational

end Ttc.CVFiniteContinuingSelfSchedule
