import Ttc.Exec.SequentialExecutionKernel
import Ttc.Exec.RawGaussianLazyStoppedExecution
import Ttc.Volume.CVDirectSequentialAccuracy

/-! Phase-level composition of the stateful recorded-query speedy execution. -/

namespace Ttc.CostedStatefulSpeedyPhases

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.GaussianCooling Arlib.MarkovChains
open Ttc.RawGaussianLazyStoppedExecution
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- Collapse a full stopped-raw lazy walk to its accumulated actual query count and final
state.  This is a genuine kernel of the incoming state. -/
noncomputable def speedyPhaseCostedKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (t : Nat) : Kernel (State n) (ENNReal × State n) :=
  Kernel.map
    (Ttc.SequentialCost.executionKernel
      (lazyRawStoppedSchedule K hK delta s hdelta))
    (fun omega => (Ttc.SequentialCost.totalCost t omega, (omega t).2))

instance (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) (t : Nat) :
    IsMarkovKernel (speedyPhaseCostedKernel K hK delta s hdelta t) := by
  unfold speedyPhaseCostedKernel
  exact Kernel.IsMarkovKernel.map _
    ((Ttc.SequentialCost.measurable_totalCost t).prodMk
      (measurable_snd.comp (measurable_pi_apply t)))

/-- Forgetting phase cost gives exactly the deterministic-time lazy speedy transition. -/
theorem map_snd_speedyPhaseCostedKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (t : Nat) (x : State n) :
    Measure.map Prod.snd (speedyPhaseCostedKernel K hK delta s hdelta t x) =
      Ttc.CVSequentialPhaseSampler.iteratedKernel
        (lazy (speedyMetropolisGaussian K delta s)) t x := by
  have hf : Measurable (fun omega : Nat → ENNReal × State n =>
      (Ttc.SequentialCost.totalCost t omega, (omega t).2)) :=
    (Ttc.SequentialCost.measurable_totalCost t).prodMk
      (measurable_snd.comp (measurable_pi_apply t))
  rw [speedyPhaseCostedKernel, Kernel.map_apply _ hf]
  rw [Measure.map_map measurable_snd hf]
  change Measure.map (fun omega : Nat → ENNReal × State n => (omega t).2)
      (Ttc.SequentialCost.executionKernel
        (lazyRawStoppedSchedule K hK delta s hdelta) x) = _
  have hexec := Ttc.SequentialCost.execution_dirac
    (lazyRawStoppedSchedule K hK delta s hdelta) x
  rw [← hexec]
  change Measure.map (fun omega : Nat → ENNReal × State n => (omega t).2)
      (Ttc.SequentialCost.execution (lazyRawStoppedSchedule K hK delta s hdelta)
        (Measure.dirac x)) = _
  rw [show Measure.map (fun omega : Nat → ENNReal × State n => (omega t).2)
      (Ttc.SequentialCost.execution (lazyRawStoppedSchedule K hK delta s hdelta)
        (Measure.dirac x)) =
        iterate (lazy (speedyMetropolisGaussian K delta s)) (Measure.dirac x) t by
    simpa only [lazyRawStoppedExecution] using
      map_lazyRawStoppedExecution_output hK delta s hdelta (Measure.dirac x) t]
  rw [Ttc.CVSequentialPhaseSampler.iterate_eq_sampleFrom_iteratedKernel]
  unfold Ttc.CVSequentialPhaseSampler.sampleFromKernel
  rw [Measure.dirac_bind]
  exact Kernel.measurable _

/-- Conditional expected phase cost is literally the expectation of the recorded-query
count in the underlying stopped-raw execution from that incoming point. -/
theorem stepMean_speedyPhaseCostedKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (t : Nat) (x : State n) :
    Ttc.SequentialCost.stepMean
        (fun _ => speedyPhaseCostedKernel K hK delta s hdelta t) 0 x =
      ∫⁻ omega, actualMembershipQueryCount t omega
        ∂lazyRawStoppedExecution K hK delta s hdelta (Measure.dirac x) := by
  have hf : Measurable (fun omega : Nat → ENNReal × State n =>
      (Ttc.SequentialCost.totalCost t omega, (omega t).2)) :=
    (Ttc.SequentialCost.measurable_totalCost t).prodMk
      (measurable_snd.comp (measurable_pi_apply t))
  unfold Ttc.SequentialCost.stepMean speedyPhaseCostedKernel
  rw [Kernel.map_apply _ hf]
  rw [lintegral_map measurable_fst hf]
  change (∫⁻ omega, Ttc.SequentialCost.totalCost t omega
      ∂Ttc.SequentialCost.executionKernel
        (lazyRawStoppedSchedule K hK delta s hdelta) x) = _
  rw [← Ttc.SequentialCost.execution_dirac
    (lazyRawStoppedSchedule K hK delta s hdelta) x]
  rfl

/-- Averaging the conditional phase cost over an incoming law is exactly the expected cost
of running the stopped-raw execution from that law. -/
theorem lintegral_diracPhaseCost_eq_execution
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (t : Nat) (mu : Measure (State n)) [IsProbabilityMeasure mu] :
    ∫⁻ x, (∫⁻ path, actualMembershipQueryCount t path
      ∂lazyRawStoppedExecution K hK delta s hdelta (Measure.dirac x)) ∂mu =
      ∫⁻ path, actualMembershipQueryCount t path
        ∂lazyRawStoppedExecution K hK delta s hdelta mu := by
  let Q := lazyRawStoppedSchedule K hK delta s hdelta
  have hbind := Ttc.SequentialCost.bind_executionKernel Q mu
  change (∫⁻ x, (∫⁻ path, Ttc.SequentialCost.totalCost t path
      ∂Ttc.SequentialCost.execution Q (Measure.dirac x)) ∂mu) =
    ∫⁻ path, Ttc.SequentialCost.totalCost t path ∂Ttc.SequentialCost.execution Q mu
  rw [← hbind]
  rw [Measure.lintegral_bind (Kernel.measurable (Ttc.SequentialCost.executionKernel Q)).aemeasurable
    (Ttc.SequentialCost.measurable_totalCost t).aemeasurable]
  apply lintegral_congr
  intro x
  rw [Ttc.SequentialCost.execution_dirac Q x]

/-- Varying phase-level costed transition family. -/
noncomputable def speedyPhaseSchedule
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq : Nat → Real) (hdelta : ∀ i, 0 < delta i) (steps : Nat → Nat) :
    Nat → Kernel (State n) (ENNReal × State n) :=
  fun i => speedyPhaseCostedKernel K hK (delta i) (sigmaSq i) (hdelta i) (steps i)

instance (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq : Nat → Real) (hdelta : ∀ i, 0 < delta i) (steps : Nat → Nat)
    (i : Nat) : IsMarkovKernel (speedyPhaseSchedule K hK delta sigmaSq hdelta steps i) := by
  unfold speedyPhaseSchedule
  infer_instance

noncomputable def speedyPhaseStateSchedule
    (K : Set (State n)) (delta sigmaSq : Nat → Real) (steps : Nat → Nat) :
    Nat → Kernel (State n) (State n) :=
  fun i => Ttc.CVSequentialPhaseSampler.iteratedKernel
    (lazy (speedyMetropolisGaussian K (delta i) (sigmaSq i))) (steps i)

instance (K : Set (State n)) (delta sigmaSq : Nat → Real) (steps : Nat → Nat)
    (i : Nat) : IsMarkovKernel (speedyPhaseStateSchedule K delta sigmaSq steps i) := by
  unfold speedyPhaseStateSchedule
  infer_instance

/-- Forget all phase cost increments while retaining the complete state history. -/
def statePath (omega : Nat → ENNReal × State n) : Nat → State n :=
  fun i => (omega i).2

theorem measurable_statePath : Measurable (statePath (n := n)) := by
  exact measurable_pi_lambda _ fun i =>
    measurable_snd.comp (measurable_pi_apply i)

/-- Minimal full-path bridge needed to transport the corrected dependent-accuracy theorem
to the costed execution.  The premise is intentionally the full path-law equality; equality
of each one-time marginal is insufficient for the history/next-state `NuIndep` fields. -/
theorem measureReal_stateEvent_eq_of_path_lumping
    (Q : Nat → Kernel (State n) (ENNReal × State n)) [∀ i, IsMarkovKernel (Q i)]
    (P : Nat → Kernel (State n) (State n)) [∀ i, IsMarkovKernel (P i)]
    (mu0 : Measure (State n)) [IsProbabilityMeasure mu0]
    (hpath : Measure.map statePath (Ttc.SequentialCost.execution Q mu0) =
      inhomogeneousPathMeasure P mu0)
    (G : Set (Nat → State n)) (hG : MeasurableSet G) :
    (Ttc.SequentialCost.execution Q mu0).real (statePath ⁻¹' G) =
      (inhomogeneousPathMeasure P mu0).real G := by
  change ((Ttc.SequentialCost.execution Q mu0) (statePath ⁻¹' G)).toReal =
    ((inhomogeneousPathMeasure P mu0) G).toReal
  rw [← Measure.map_apply measurable_statePath hG, hpath]

/-- Exact phase-by-phase state marginal recursion for the actual recorded-query execution. -/
theorem map_speedyPhaseExecution_output_succ
    {K : Set (State n)} (hK : MeasurableSet K)
    (delta sigmaSq : Nat → Real) (hdelta : ∀ i, 0 < delta i) (steps : Nat → Nat)
    (mu0 : Measure (State n)) [IsProbabilityMeasure mu0] (i : Nat) :
    Measure.map (fun omega => (omega (i + 1)).2)
        (Ttc.SequentialCost.execution
          (speedyPhaseSchedule K hK delta sigmaSq hdelta steps) mu0) =
      (Measure.map (fun omega => (omega i).2)
        (Ttc.SequentialCost.execution
          (speedyPhaseSchedule K hK delta sigmaSq hdelta steps) mu0)).bind
        (speedyPhaseStateSchedule K delta sigmaSq steps i) := by
  exact Ttc.SequentialCost.map_execution_output_succ
    (speedyPhaseSchedule K hK delta sigmaSq hdelta steps)
    (speedyPhaseStateSchedule K delta sigmaSq steps)
    (fun i x => map_snd_speedyPhaseCostedKernel hK (delta i) (sigmaSq i)
      (hdelta i) (steps i) x) mu0 i

#print axioms map_snd_speedyPhaseCostedKernel
#print axioms map_speedyPhaseExecution_output_succ
#print axioms measureReal_stateEvent_eq_of_path_lumping

end Ttc.CostedStatefulSpeedyPhases
