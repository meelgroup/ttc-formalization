/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.MarkovChains.Continuous.CostedRestartTrajectory
import Arlib.Probability.InhomogeneousMarkov

/-!
# Sequential costed kernels

This file supplies the execution-composition interface needed by adaptive cooling loops.
At time `i`, a costed kernel `Q i` reads the current state and returns an `ENNReal` cost
increment together with the next state.  Ionescu--Tulcea composes the time-dependent family
into one trajectory law.  The finite-prefix total cost is therefore an actual random
variable, not an arithmetic proxy.

The results are generic.  No kernel in this file is claimed to count Gaussian-walk
membership queries; an instantiation must still construct such a kernel and identify its
cost coordinate with an operational query count.
-/

namespace Ttc.SequentialCost

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {S : Type*} [MeasurableSpace S]

/-- Forget the previous increment and execute the costed kernel scheduled at time `i`. -/
noncomputable def stepKernel (Q : Nat -> Kernel S (ENNReal × S)) (i : Nat) :
    Kernel (ENNReal × S) (ENNReal × S) :=
  Arlib.MarkovChains.restartedCostKernel (Q i)

instance (Q : Nat -> Kernel S (ENNReal × S)) [∀ i, IsMarkovKernel (Q i)] (i : Nat) :
    IsMarkovKernel (stepKernel Q i) := by
  unfold stepKernel
  infer_instance

/-- Ionescu--Tulcea law of the whole time-dependent costed execution.  Coordinate zero has
cost zero and state law `mu`; coordinate `i+1` is the result of `Q i`. -/
noncomputable def execution (Q : Nat -> Kernel S (ENNReal × S))
    [∀ i, IsMarkovKernel (Q i)] (mu : Measure S) : Measure (Nat -> ENNReal × S) :=
  Arlib.Probability.inhomogeneousPathMeasure (stepKernel Q)
    (Arlib.MarkovChains.zeroCostLaw mu)

instance (Q : Nat -> Kernel S (ENNReal × S)) [∀ i, IsMarkovKernel (Q i)]
    (mu : Measure S) [IsProbabilityMeasure mu] : IsProbabilityMeasure (execution Q mu) := by
  unfold execution
  infer_instance

/-- Total cost of the first `t` scheduled steps. -/
noncomputable def totalCost (t : Nat) (omega : Nat -> ENNReal × S) : ENNReal :=
  ∑ i ∈ Finset.range t, (omega (i + 1)).1

theorem measurable_totalCost (t : Nat) : Measurable (totalCost (S := S) t) := by
  unfold totalCost
  fun_prop

/-! ## Coordinate recursion -/

/-- The time-zero coordinate of an inhomogeneous Markov path has its initial law. -/
theorem map_eval_inhomogeneousPathMeasure_zero
    {E : Type*} [MeasurableSpace E] (P : Nat -> Kernel E E)
    [∀ i, IsMarkovKernel (P i)] (mu : Measure E) [IsProbabilityMeasure mu] :
    (Arlib.Probability.inhomogeneousPathMeasure P mu).map (fun omega => omega 0) = mu := by
  have hdet := Kernel.traj_map_frestrictLe_of_le (X := fun _ : Nat => E)
    (κ := Arlib.Probability.inhomogeneousHistoryKernel P) (a := 0) (b := 0) le_rfl
  have hmap : Kernel.map
        (Kernel.traj (X := fun _ : Nat => E)
          (Arlib.Probability.inhomogeneousHistoryKernel P) 0)
        (fun x => x 0)
      = Kernel.deterministic
          (fun x : (_i : Finset.Iic 0) -> E => x ⟨0, Finset.mem_Iic.2 le_rfl⟩)
          (measurable_pi_apply _) := by
    rw [show (fun x : Nat -> E => x 0) =
        (fun h : (_i : Finset.Iic 0) -> E => h ⟨0, Finset.mem_Iic.2 le_rfl⟩) ∘
          Preorder.frestrictLe 0 from rfl,
      Kernel.map_comp_right _ (Preorder.measurable_frestrictLe 0) (measurable_pi_apply _),
      hdet, Kernel.deterministic_map _ (measurable_pi_apply _)]
    rfl
  rw [Arlib.Probability.inhomogeneousPathMeasure, Kernel.trajMeasure,
    Measure.map_comp _ _ (by fun_prop), hmap, Measure.deterministic_comp_eq_map,
    Measure.map_map (by fun_prop) (by fun_prop)]
  simp [Function.comp_def]

/-- One coordinate step of an inhomogeneous Markov path. -/
theorem map_eval_inhomogeneousPathMeasure_succ
    {E : Type*} [MeasurableSpace E] (P : Nat -> Kernel E E)
    [∀ i, IsMarkovKernel (P i)] (mu : Measure E) [IsProbabilityMeasure mu] (i : Nat) :
    (Arlib.Probability.inhomogeneousPathMeasure P mu).map (fun omega => omega (i + 1)) =
      ((Arlib.Probability.inhomogeneousPathMeasure P mu).map (fun omega => omega i)).bind
        (P i) := by
  have hjoint := Arlib.Probability.map_history_next_inhomogeneousPathMeasure P mu i
  have hsnd := congrArg Measure.snd hjoint
  rw [Measure.snd_compProd] at hsnd
  rw [Measure.snd, Measure.map_map (by fun_prop) (by fun_prop)] at hsnd
  rw [Arlib.Probability.inhomogeneousHistoryKernel,
    Arlib.MarkovChains.bind_comap,
    Measure.map_map (measurable_pi_apply _) (by fun_prop)] at hsnd
  simp only [Function.comp_def, Preorder.frestrictLe_apply] at hsnd
  exact hsnd.symm

/-- The extended `(increment,state)` marginal follows the scheduled kernel recursion. -/
theorem map_execution_succ
    (Q : Nat -> Kernel S (ENNReal × S)) [∀ i, IsMarkovKernel (Q i)]
    (mu : Measure S) [IsProbabilityMeasure mu] (i : Nat) :
    (execution Q mu).map (fun omega => omega (i + 1)) =
      ((execution Q mu).map (fun omega => omega i)).bind (stepKernel Q i) := by
  exact map_eval_inhomogeneousPathMeasure_succ (stepKernel Q)
    (Arlib.MarkovChains.zeroCostLaw mu) i

/-- Mapping the next-state coordinate through one extended costed step gives the supplied
uncosted state kernel. -/
theorem map_snd_bind_stepKernel
    (Q : Nat -> Kernel S (ENNReal × S)) [∀ i, IsMarkovKernel (Q i)]
    (P : Nat -> Kernel S S) [∀ i, IsMarkovKernel (P i)]
    (hforget : ∀ i x, Measure.map Prod.snd (Q i x) = P i x)
    (nu : Measure (ENNReal × S)) [SFinite nu] (i : Nat) :
    Measure.map Prod.snd (nu.bind (stepKernel Q i)) =
      (Measure.map Prod.snd nu).bind (P i) := by
  ext A hA
  rw [Measure.map_apply measurable_snd hA,
    Measure.bind_apply (hA.preimage measurable_snd) (Kernel.aemeasurable _),
    Measure.bind_apply hA (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe (P i) hA) measurable_snd]
  apply lintegral_congr
  intro z
  change Q i z.2 (Prod.snd ⁻¹' A) = P i z.2 A
  rw [← Measure.map_apply measurable_snd hA, hforget]

/-- At time zero, forgetting the zero increment recovers the initial state law. -/
theorem map_execution_output_zero
    (Q : Nat -> Kernel S (ENNReal × S)) [∀ i, IsMarkovKernel (Q i)]
    (mu : Measure S) [IsProbabilityMeasure mu] :
    (execution Q mu).map (fun omega => (omega 0).2) = mu := by
  rw [show (fun omega : Nat -> ENNReal × S => (omega 0).2) =
      Prod.snd ∘ (fun omega => omega 0) from rfl,
    ← Measure.map_map (μ := execution Q mu) (f := fun omega => omega 0)
      (g := Prod.snd) measurable_snd (measurable_pi_apply 0),
    execution,
    map_eval_inhomogeneousPathMeasure_zero]
  unfold Arlib.MarkovChains.zeroCostLaw
  rw [Measure.map_map (μ := mu) (f := fun x : S => (0, x)) (g := Prod.snd)
    measurable_snd (by fun_prop)]
  simp [Function.comp_def]

/-- State-output marginal recursion.  If forgetting each cost coordinate of `Q i` gives
`P i`, then the state at time `i+1` is the time-`i` state marginal bound through `P i`. -/
theorem map_execution_output_succ
    (Q : Nat -> Kernel S (ENNReal × S)) [∀ i, IsMarkovKernel (Q i)]
    (P : Nat -> Kernel S S) [∀ i, IsMarkovKernel (P i)]
    (hforget : ∀ i x, Measure.map Prod.snd (Q i x) = P i x)
    (mu : Measure S) [IsProbabilityMeasure mu] (i : Nat) :
    (execution Q mu).map (fun omega => (omega (i + 1)).2) =
      ((execution Q mu).map (fun omega => (omega i).2)).bind (P i) := by
  rw [show (fun omega : Nat -> ENNReal × S => (omega (i + 1)).2) =
      Prod.snd ∘ (fun omega => omega (i + 1)) from rfl,
    ← Measure.map_map (μ := execution Q mu) (f := fun omega => omega (i + 1))
      (g := Prod.snd) measurable_snd (measurable_pi_apply (i + 1)),
    map_execution_succ,
    map_snd_bind_stepKernel Q P hforget,
    Measure.map_map measurable_snd (measurable_pi_apply i)]
  rfl

/-! ## Expected total cost -/

/-- Conditional one-step expected cost from state `x` at scheduled time `i`. -/
noncomputable def stepMean (Q : Nat -> Kernel S (ENNReal × S)) (i : Nat) (x : S) : ENNReal :=
  ∫⁻ y, y.1 ∂Q i x

theorem measurable_stepMean (Q : Nat -> Kernel S (ENNReal × S))
    [∀ i, IsMarkovKernel (Q i)] (i : Nat) : Measurable (stepMean Q i) := by
  exact Measurable.lintegral_kernel_prod_right (κ := Q i) measurable_snd.fst

/-- Expectation of the finite-prefix cost is the sum of its increment-coordinate
expectations. -/
theorem lintegral_totalCost_eq_sum_incrementMarginals
    (Q : Nat -> Kernel S (ENNReal × S)) [∀ i, IsMarkovKernel (Q i)]
    (mu : Measure S) [IsProbabilityMeasure mu] (t : Nat) :
    ∫⁻ omega, totalCost t omega ∂execution Q mu =
      ∑ i ∈ Finset.range t,
        ∫⁻ z, z.1 ∂(execution Q mu).map (fun omega => omega (i + 1)) := by
  simp only [totalCost]
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [lintegral_map measurable_fst (measurable_pi_apply (i + 1))]
  · intro i hi
    exact measurable_fst.comp (measurable_pi_apply (i + 1))

/-- One increment expectation is the current state marginal's average of the conditional
one-step mean. -/
theorem lintegral_incrementMarginal_eq_stateMean
    (Q : Nat -> Kernel S (ENNReal × S)) [∀ i, IsMarkovKernel (Q i)]
    (mu : Measure S) [IsProbabilityMeasure mu] (i : Nat) :
    ∫⁻ z, z.1 ∂(execution Q mu).map (fun omega => omega (i + 1)) =
      ∫⁻ x, stepMean Q i x ∂(execution Q mu).map (fun omega => (omega i).2) := by
  rw [map_execution_succ]
  rw [Measure.lintegral_bind (Kernel.measurable (stepKernel Q i)).aemeasurable
    measurable_fst.aemeasurable]
  have hmarg : Measure.map Prod.snd
      ((execution Q mu).map (fun omega => omega i)) =
        (execution Q mu).map (fun omega => (omega i).2) := by
    rw [Measure.map_map (μ := execution Q mu) measurable_snd (measurable_pi_apply i)]
    rfl
  let xi : Measure (ENNReal × S) := (execution Q mu).map (fun omega => omega i)
  calc
    (∫⁻ z, (∫⁻ y, y.1 ∂stepKernel Q i z) ∂xi) =
        ∫⁻ z, stepMean Q i z.2 ∂xi := by rfl
    _ = ∫⁻ x, stepMean Q i x ∂Measure.map Prod.snd xi := by
      rw [lintegral_map (measurable_stepMean Q i) measurable_snd]
    _ = ∫⁻ x, stepMean Q i x ∂(execution Q mu).map (fun omega => (omega i).2) := by
      rw [hmarg]

/-- Exact sequential composition formula: expected realized cost is the sum of the
conditional one-step means averaged against the actual state marginal at each time. -/
theorem lintegral_totalCost_eq_sum_stateMeans
    (Q : Nat -> Kernel S (ENNReal × S)) [∀ i, IsMarkovKernel (Q i)]
    (mu : Measure S) [IsProbabilityMeasure mu] (t : Nat) :
    ∫⁻ omega, totalCost t omega ∂execution Q mu =
      ∑ i ∈ Finset.range t,
        ∫⁻ x, stepMean Q i x ∂(execution Q mu).map (fun omega => (omega i).2) := by
  rw [lintegral_totalCost_eq_sum_incrementMarginals]
  apply Finset.sum_congr rfl
  intro i hi
  exact lintegral_incrementMarginal_eq_stateMean Q mu i

/-- State-dependent upper bounds on the conditional means compose additively. -/
theorem lintegral_totalCost_le_sum_stateBounds
    (Q : Nat -> Kernel S (ENNReal × S)) [∀ i, IsMarkovKernel (Q i)]
    (mu : Measure S) [IsProbabilityMeasure mu] (t : Nat)
    (bound : Nat -> S -> ENNReal)
    (hbound : ∀ i, i < t -> ∀ x, stepMean Q i x ≤ bound i x) :
    ∫⁻ omega, totalCost t omega ∂execution Q mu ≤
      ∑ i ∈ Finset.range t,
        ∫⁻ x, bound i x ∂(execution Q mu).map (fun omega => (omega i).2) := by
  rw [lintegral_totalCost_eq_sum_stateMeans]
  apply Finset.sum_le_sum
  intro i hi
  apply lintegral_mono
  exact hbound i (Finset.mem_range.1 hi)

/-- A uniform bound for each scheduled conditional mean gives the familiar sum of scalar
one-step budgets. -/
theorem lintegral_totalCost_le_sum_uniformBounds
    (Q : Nat -> Kernel S (ENNReal × S)) [∀ i, IsMarkovKernel (Q i)]
    (mu : Measure S) [IsProbabilityMeasure mu] (t : Nat)
    (bound : Nat -> ENNReal)
    (hbound : ∀ i, i < t -> ∀ x, stepMean Q i x ≤ bound i) :
    ∫⁻ omega, totalCost t omega ∂execution Q mu ≤
      ∑ i ∈ Finset.range t, bound i := by
  rw [lintegral_totalCost_eq_sum_stateMeans]
  apply Finset.sum_le_sum
  intro i hi
  let nu : Measure S := (execution Q mu).map (fun omega => (omega i).2)
  letI : IsProbabilityMeasure nu :=
    Measure.isProbabilityMeasure_map (measurable_snd.comp (measurable_pi_apply i)).aemeasurable
  calc
    (∫⁻ x, stepMean Q i x ∂(execution Q mu).map (fun omega => (omega i).2))
        ≤ ∫⁻ _x, bound i ∂nu := lintegral_mono (hbound i (Finset.mem_range.1 hi))
    _ = bound i := by simp

/-! ### Axiom audit -/

#print axioms map_execution_output_succ
#print axioms lintegral_totalCost_eq_sum_stateMeans
#print axioms lintegral_totalCost_le_sum_uniformBounds

end Ttc.SequentialCost
