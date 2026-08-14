/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.SequentialCostedKernel
import Arlib.Probability.TVTimeout

/-!
# A costed sequential execution as a kernel of its initial state

`SequentialCost.execution Q mu` is a measure-valued construction.  To apply randomized
TV data processing and timeout transfer, the same experiment must be exposed as a Markov
kernel from its initial state to the entire costed path.  This file packages that kernel
directly from Ionescu--Tulcea and identifies binding an initial law with `execution`.
-/

namespace Ttc.SequentialCost

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {S : Type*} [MeasurableSpace S]

/-- The singleton time-zero history carrying state `x` and zero initial cost. -/
def initialHistory (x : S) : (i : Finset.Iic 0) -> ENNReal × S :=
  fun _ => (0, x)

theorem measurable_initialHistory : Measurable (initialHistory (S := S)) := by
  exact measurable_pi_lambda _ fun _ => measurable_const.prodMk measurable_id

/-- Ionescu--Tulcea execution, viewed as a kernel of the initial state. -/
noncomputable def executionKernel (Q : Nat -> Kernel S (ENNReal × S))
    [forall i, IsMarkovKernel (Q i)] : Kernel S (Nat -> ENNReal × S) :=
  Kernel.comap
    (Kernel.traj
      (Arlib.Probability.inhomogeneousHistoryKernel (stepKernel Q)) 0)
    (initialHistory (S := S)) measurable_initialHistory

instance (Q : Nat -> Kernel S (ENNReal × S))
    [forall i, IsMarkovKernel (Q i)] : IsMarkovKernel (executionKernel Q) := by
  unfold executionKernel
  infer_instance

theorem executionKernel_apply (Q : Nat -> Kernel S (ENNReal × S))
    [forall i, IsMarkovKernel (Q i)] (x : S) :
    executionKernel Q x =
      Kernel.traj (Arlib.Probability.inhomogeneousHistoryKernel (stepKernel Q)) 0
        (initialHistory x) := rfl

/-- Binding an initial state law through `executionKernel` is exactly the previously
defined sequential execution measure. -/
theorem bind_executionKernel (Q : Nat -> Kernel S (ENNReal × S))
    [forall i, IsMarkovKernel (Q i)]
    (mu : Measure S) [SFinite mu] :
    mu.bind (executionKernel Q) = execution Q mu := by
  rw [execution, Arlib.Probability.inhomogeneousPathMeasure,
    Kernel.trajMeasure, Arlib.MarkovChains.zeroCostLaw]
  rw [executionKernel, Arlib.MarkovChains.bind_comap]
  congr 1
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- The path law from a deterministic state is the kernel value at that state. -/
theorem execution_dirac (Q : Nat -> Kernel S (ENNReal × S))
    [forall i, IsMarkovKernel (Q i)] (x : S) :
    execution Q (Measure.dirac x) = executionKernel Q x := by
  rw [← bind_executionKernel Q (Measure.dirac x), Measure.dirac_bind]
  exact Kernel.measurable (executionKernel Q)

/-- Timeout transfer specialized to a full costed sequential execution. -/
theorem totalCost_timeout_le_of_tvLe
    (Q : Nat -> Kernel S (ENNReal × S)) [forall i, IsMarkovKernel (Q i)]
    {mu nu : Measure S} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {eps : ENNReal} (htv : Arlib.TVLe mu nu eps)
    (t : Nat) {L B : ENNReal} (hL0 : L ≠ 0) (hLtop : L ≠ ⊤)
    (hmean : (∫⁻ omega, totalCost t omega ∂execution Q nu) <= B) :
    execution Q mu {omega | L <= totalCost t omega} <= B / L + eps := by
  rw [← bind_executionKernel Q mu]
  rw [← bind_executionKernel Q nu] at hmean
  exact Arlib.bind_kernel_timeout_le_of_tvLe htv (executionKernel Q)
    (totalCost t) (measurable_totalCost t) hL0 hLtop hmean

#print axioms bind_executionKernel
#print axioms totalCost_timeout_le_of_tvLe

end Ttc.SequentialCost
