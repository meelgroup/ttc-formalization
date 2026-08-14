import Ttc.Exec.CostedStatefulSpeedyPhases
import Ttc.Exec.AdjustableLazyProperProposalCost

/-!
# Expected membership-query cost of a stateful speedy phase schedule

This is the operational, multi-phase form of Cousins--Vempala's
`lem:speedy-to-ball`.  Every transition is the retained raw proposal execution, so the
cost is the actual number of membership queries.  The bound is averaged against the
*actual incoming marginal* of each phase; no independent restart or detached accounting
function is used.
-/

namespace Ttc.CostedStatefulSpeedyRuntime

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.GaussianCooling Arlib.MarkovChains
open Ttc.CostedStatefulSpeedyPhases
open Ttc.RawGaussianLazyStoppedExecution
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- A phase-dependent retained-query speedy schedule. -/
noncomputable def phaseSchedule
    (K : Nat → Set (State n)) (hK : ∀ i, MeasurableSet (K i))
    (delta sigmaSq : Nat → Real) (hdelta : ∀ i, 0 < delta i)
    (steps : Nat → Nat) : Nat → Kernel (State n) (ENNReal × State n) :=
  fun i ↦ speedyPhaseCostedKernel (K i) (hK i) (delta i) (sigmaSq i)
    (hdelta i) (steps i)

instance (K : Nat → Set (State n)) (hK : ∀ i, MeasurableSet (K i))
    (delta sigmaSq : Nat → Real) (hdelta : ∀ i, 0 < delta i)
    (steps : Nat → Nat) (i : Nat) :
    IsMarkovKernel (phaseSchedule K hK delta sigmaSq hdelta steps i) := by
  unfold phaseSchedule
  infer_instance

/-- Multi-phase form of `lem:speedy-to-ball`: once the paper's proved one-phase bound is
supplied for each actual incoming marginal, the recorded costs add with no independence
assumption. -/
theorem six_mul_lintegral_totalCost_le_sum_of_phase_bounds
    (Q : Nat → Kernel (State n) (ENNReal × State n)) [∀ i, IsMarkovKernel (Q i)]
    (mu0 : Measure (State n)) [IsProbabilityMeasure mu0]
    (steps : Nat → Nat) (M : Nat → ENNReal) (phases : Nat)
    (hphase : ∀ i, i < phases →
      6 * (∫⁻ x, Ttc.SequentialCost.stepMean Q i x
        ∂(Ttc.SequentialCost.execution Q mu0).map (fun omega ↦ (omega i).2)) ≤
        10 * ((steps i : ENNReal) * M i)) :
    6 * (∫⁻ omega, Ttc.SequentialCost.totalCost phases omega
      ∂Ttc.SequentialCost.execution Q mu0) ≤
      ∑ i ∈ Finset.range phases,
        10 * ((steps i : ENNReal) * M i) := by
  rw [Ttc.SequentialCost.lintegral_totalCost_eq_sum_stateMeans, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  exact hphase i (Finset.mem_range.1 hi)

#print axioms six_mul_lintegral_totalCost_le_sum_of_phase_bounds

end Ttc.CostedStatefulSpeedyRuntime
