/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Exec.RawGaussianStoppedQueryCost
import Ttc.Exec.AdjustableLazyProperProposalCost

/-!
# Lazy sequential execution of stopped raw membership-query paths

This file totalizes the raw stopped experiment at genuinely stuck points, applies the fair
lazy coin, and composes finitely many steps.  Every active increment is the `ENNReal` count
of the retained raw membership queries; it is not a separately postulated work charge.
-/

namespace Ttc.RawGaussianLazyStoppedExecution

open MeasureTheory ProbabilityTheory Function Set
open Arlib Arlib.MarkovChains
open Ttc.MembershipQuery Ttc.RawGaussianMembership Ttc.RawGaussianQueryCost
open Ttc.RawGaussianStoppedQueryCost Ttc.LazyProperCost
open scoped ENNReal Classical

variable {n : Nat}

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- Before totalization, mapping the retained raw path to cost and stopped state is exactly
the repository's existing costed proper-proposal experiment. -/
theorem rawProperProposalCostedKernel_eq_existingRaw
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (x : State n) :
    rawProperProposalCostedKernel hK delta s hdelta x =
      properProposalCostedKernelRaw K hK delta s x := by
  let rawToMarked : State n × (Nat → RawRound n) →
      State n × LiftedGaussianPath n :=
    fun p => (p.1, mapPath rawRoundOutput p.2)
  let rawOut : State n × (Nat → RawRound n) → ENNReal × State n :=
    fun p => (rawPathMembershipQueryCost
      (MembershipOracle.ofMeasurableSet K hK) p,
      firstProperMarkedState (mapPath rawRoundOutput p.2))
  let markedOut : State n × LiftedGaussianPath n → ENNReal × State n :=
    fun p => (properProposalWaitCost p, firstProperMarkedState p.2)
  have hrawToMarked : Measurable rawToMarked :=
    measurable_fst.prodMk
      ((measurable_mapPath measurable_rawRoundOutput).comp measurable_snd)
  have hrawOut : Measurable rawOut :=
    (measurable_rawPathMembershipQueryCost _).prodMk
      (measurable_firstProperMarkedState.comp
        ((measurable_mapPath measurable_rawRoundOutput).comp measurable_snd))
  have hmarkedOut : Measurable markedOut :=
    measurable_properProposalWaitCost.prodMk
      (measurable_firstProperMarkedState.comp measurable_snd)
  have hfactor : rawOut = markedOut ∘ rawToMarked := by
    funext p
    apply Prod.ext
    · exact rawPathMembershipQueryCost_eq_waitCost _ p
    · rfl
  rw [rawProperProposalCostedKernel, Kernel.map_apply _ hrawOut,
    rawStartedTrajectoryKernel_apply]
  rw [hfactor, ← Measure.map_map hmarkedOut hrawToMarked]
  have hpairRaw : Measurable (fun omega : Nat → RawRound n => (x, omega)) :=
    measurable_const.prodMk measurable_id
  have hpairMarked : Measurable (fun omega : LiftedGaussianPath n => (x, omega)) :=
    measurable_const.prodMk measurable_id
  have hstarted :
      ((rawTrajectoryKernel hK delta s hdelta x).map (fun omega => (x, omega))).map
          rawToMarked =
        (properProposalTrajectoryKernel K hK delta s x).map (fun omega => (x, omega)) := by
    calc
      ((rawTrajectoryKernel hK delta s hdelta x).map (fun omega => (x, omega))).map
          rawToMarked =
        (rawTrajectoryKernel hK delta s hdelta x).map
          (rawToMarked ∘ fun omega => (x, omega)) := by
            rw [Measure.map_map hrawToMarked hpairRaw]
      _ = (rawTrajectoryKernel hK delta s hdelta x).map
          ((fun omega : LiftedGaussianPath n => (x, omega)) ∘ mapPath rawRoundOutput) := by
            rfl
      _ = ((rawTrajectoryKernel hK delta s hdelta x).map
          (mapPath rawRoundOutput)).map (fun omega => (x, omega)) := by
            rw [Measure.map_map hpairMarked
              (measurable_mapPath measurable_rawRoundOutput)]
      _ = (properProposalTrajectoryKernel K hK delta s x).map
          (fun omega => (x, omega)) := by
            rw [map_rawTrajectoryKernel_outputPath hK delta s hdelta x]
  rw [hstarted, properProposalCostedKernelRaw,
    Kernel.map_apply _ hmarkedOut]
  have hstartedExisting :
      properProposalStartedTrajectoryKernel K hK delta s x =
        (properProposalTrajectoryKernel K hK delta s x).map (fun omega => (x, omega)) := by
    ext A hA
    rw [properProposalStartedTrajectoryKernel, Kernel.compProd_apply hA,
      Kernel.id_apply, lintegral_dirac']
    · rw [Kernel.prodMkLeft_apply, Measure.map_apply (by fun_prop) hA]
    · exact Kernel.measurable_kernel_prodMk_left' hA x
  rw [hstartedExisting]

/-- Total raw costed step.  Only genuinely stuck states are parked with zero queries; every
other branch runs the retained infinite raw path. -/
noncomputable def rawProperProposalCostedKernelTotal
    (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta) :
    Kernel (State n) (ENNReal × State n) :=
  Kernel.piecewise (measurableSet_stuckPoints hK delta)
    (Kernel.deterministic (fun x => (0, x)) (by fun_prop))
    (rawProperProposalCostedKernel hK delta s hdelta)

instance (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) :
    IsMarkovKernel (rawProperProposalCostedKernelTotal K hK delta s hdelta) := by
  unfold rawProperProposalCostedKernelTotal
  infer_instance

/-- Totalizing the retained-query implementation recovers exactly the existing costed
kernel, including its cost/state joint law. -/
theorem rawProperProposalCostedKernelTotal_eq_existing
    (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta) :
    rawProperProposalCostedKernelTotal K hK delta s hdelta =
      properProposalCostedKernel K hK delta s := by
  ext x : 1
  rw [rawProperProposalCostedKernelTotal, properProposalCostedKernel,
    Kernel.piecewise_apply, Kernel.piecewise_apply]
  split_ifs
  · rfl
  · exact rawProperProposalCostedKernel_eq_existingRaw hK delta s hdelta x

/-- One fair lazy step whose active branch is the actual stopped raw query experiment. -/
noncomputable def lazyRawStoppedCostedKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta) :
    Kernel (State n) (ENNReal × State n) :=
  lazyCostedKernel (rawProperProposalCostedKernelTotal K hK delta s hdelta)

instance (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) : IsMarkovKernel
      (lazyRawStoppedCostedKernel K hK delta s hdelta) := by
  unfold lazyRawStoppedCostedKernel
  infer_instance

theorem lazyRawStoppedCostedKernel_eq_existing
    (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta) :
    lazyRawStoppedCostedKernel K hK delta s hdelta =
      lazyProperProposalCostedKernel K hK delta s := by
  rw [lazyRawStoppedCostedKernel, lazyProperProposalCostedKernel,
    rawProperProposalCostedKernelTotal_eq_existing]

theorem map_snd_lazyRawStoppedCostedKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (x : State n) :
    (lazyRawStoppedCostedKernel K hK delta s hdelta x).map Prod.snd =
      lazy (speedyMetropolisGaussian K delta s) x := by
  rw [lazyRawStoppedCostedKernel_eq_existing]
  exact map_snd_lazyProperProposalCostedKernel hK delta s x

noncomputable def lazyRawStoppedSchedule
    (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta) :
    Nat → Kernel (State n) (ENNReal × State n) :=
  fun _ => lazyRawStoppedCostedKernel K hK delta s hdelta

instance (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) (i : Nat) :
    IsMarkovKernel (lazyRawStoppedSchedule K hK delta s hdelta i) := by
  unfold lazyRawStoppedSchedule
  infer_instance

noncomputable def lazyRawStoppedExecution
    (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (mu : Measure (State n)) : Measure (Nat → ENNReal × State n) :=
  Ttc.SequentialCost.execution (lazyRawStoppedSchedule K hK delta s hdelta) mu

instance (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) (mu : Measure (State n)) [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (lazyRawStoppedExecution K hK delta s hdelta mu) := by
  unfold lazyRawStoppedExecution
  infer_instance

/-- The state output of the actual-query execution is exactly the usual lazy speedy iterate. -/
theorem map_lazyRawStoppedExecution_output
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (mu : Measure (State n)) [IsProbabilityMeasure mu] (t : Nat) :
    (lazyRawStoppedExecution K hK delta s hdelta mu).map
        (fun omega => (omega t).2) =
      iterate (lazy (speedyMetropolisGaussian K delta s)) mu t := by
  induction t with
  | zero =>
      exact Ttc.SequentialCost.map_execution_output_zero
        (lazyRawStoppedSchedule K hK delta s hdelta) mu
  | succ t ih =>
      change Measure.map (fun omega => (omega (t + 1)).2)
          (Ttc.SequentialCost.execution
            (lazyRawStoppedSchedule K hK delta s hdelta) mu) = _
      rw [Ttc.SequentialCost.map_execution_output_succ
          (lazyRawStoppedSchedule K hK delta s hdelta)
          (fun _ => lazy (speedyMetropolisGaussian K delta s))
          (fun _i x => map_snd_lazyRawStoppedCostedKernel hK delta s hdelta x)]
      rw [show Measure.map (fun omega => (omega t).2)
          (Ttc.SequentialCost.execution
            (lazyRawStoppedSchedule K hK delta s hdelta) mu) =
            iterate (lazy (speedyMetropolisGaussian K delta s)) mu t by
        simpa only [lazyRawStoppedExecution] using ih]
      rfl

/-- Total actual membership queries in the first `t` lazy stopped raw steps. -/
noncomputable def actualMembershipQueryCount (t : Nat)
    (omega : Nat → ENNReal × State n) : ENNReal :=
  Ttc.SequentialCost.totalCost t omega

theorem measurable_actualMembershipQueryCount (t : Nat) :
    Measurable (actualMembershipQueryCount (n := n) t) :=
  Ttc.SequentialCost.measurable_totalCost t

/-- The expected total of the directly composed raw-query increments agrees with the older
costed execution.  This theorem follows from equality of every one-step cost/state joint law
and the exact state marginals of both executions. -/
theorem expected_actualMembershipQueryCount_eq_existing
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (mu : Measure (State n)) [IsProbabilityMeasure mu] (t : Nat) :
    ∫⁻ omega, actualMembershipQueryCount t omega
        ∂lazyRawStoppedExecution K hK delta s hdelta mu =
      ∫⁻ omega, Ttc.SequentialCost.totalCost t omega
        ∂lazyProperExecution K hK delta s mu := by
  change (∫⁻ omega, Ttc.SequentialCost.totalCost t omega
      ∂Ttc.SequentialCost.execution
        (lazyRawStoppedSchedule K hK delta s hdelta) mu) = _
  rw [Ttc.SequentialCost.lintegral_totalCost_eq_sum_stateMeans,
    show lazyProperExecution K hK delta s mu =
      Ttc.SequentialCost.execution (lazyProperSchedule K hK delta s) mu by rfl,
    Ttc.SequentialCost.lintegral_totalCost_eq_sum_stateMeans]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show Measure.map (fun omega => (omega i).2)
        (Ttc.SequentialCost.execution
          (lazyRawStoppedSchedule K hK delta s hdelta) mu) =
      iterate (lazy (speedyMetropolisGaussian K delta s)) mu i by
        simpa only [lazyRawStoppedExecution] using
          map_lazyRawStoppedExecution_output hK delta s hdelta mu i,
    show Measure.map (fun omega => (omega i).2)
        (Ttc.SequentialCost.execution (lazyProperSchedule K hK delta s) mu) =
      iterate (lazy (speedyMetropolisGaussian K delta s)) mu i by
        simpa only [lazyProperExecution] using
          map_lazyProperExecution_output hK delta s mu i]
  apply lintegral_congr
  intro x
  unfold Ttc.SequentialCost.stepMean lazyRawStoppedSchedule lazyProperSchedule
  rw [lazyRawStoppedCostedKernel_eq_existing]

/-- Adjustable-radius bound for expected *recorded membership queries*.  The constants and
geometry are inherited from the proved adjustable acceptance estimate; the equality to the
existing execution above transfers that analysis to the raw traced implementation. -/
theorem six_mul_expected_actualMembershipQueryCount_le_ten_mul_adjustable
    (hn : 2 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : Metric.ball (0 : State n) 1 ⊆ K)
    {q delta sigma R : Real} (hq : 1 < q)
    (hdelta : 0 < delta) (hsigma : 0 < sigma)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    (hdeltaq : delta ≤ sigma / (max 8 (2 * q) * Real.sqrt n))
    (hR : 0 ≤ R) (hRsigma : R ≤ q * sigma * Real.sqrt n)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    {M : ENNReal} {mu : Measure (State n)} [IsProbabilityMeasure mu]
    (hwarm : IsWarm M mu (ellGaussianProb K delta (sigma ^ 2))) (t : Nat) :
    6 * (∫⁻ omega, actualMembershipQueryCount t omega
        ∂lazyRawStoppedExecution K hK delta (sigma ^ 2) hdelta mu) ≤
      10 * ((t : ENNReal) * M) := by
  rw [expected_actualMembershipQueryCount_eq_existing hK delta
    (sigma ^ 2) hdelta mu t]
  exact Ttc.AdjustableLazyProperCost.six_mul_lintegral_lazyProperTotalCost_le_ten_mul_adjustable
    hn hq hK hKc hball hdelta hsigma hdeltan hdeltaq hR hRsigma hKR hwarm t

#print axioms rawProperProposalCostedKernelTotal_eq_existing
#print axioms map_lazyRawStoppedExecution_output
#print axioms expected_actualMembershipQueryCount_eq_existing
#print axioms six_mul_expected_actualMembershipQueryCount_le_ten_mul_adjustable

end Ttc.RawGaussianLazyStoppedExecution
