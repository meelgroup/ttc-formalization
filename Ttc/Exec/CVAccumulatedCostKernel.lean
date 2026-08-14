import Ttc.Exec.SequentialCostedKernel

/-!
# Accumulating a costed phase kernel

`SequentialCost` stores per-phase increments in a path.  The exact-state reference
induction instead keeps one cumulative cost beside the current state.  This file gives
the measure-theoretic adapter between those equivalent views.
-/

namespace Ttc.CVAccumulatedCostKernel

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- Add a newly sampled phase cost to the incoming cumulative cost. -/
def addPhaseCost (z : ENNReal × (ENNReal × X)) : ENNReal × X :=
  (z.1 + z.2.1, z.2.2)

theorem measurable_addPhaseCost :
    Measurable (addPhaseCost : ENNReal × (ENNReal × X) → ENNReal × X) := by
  exact (measurable_fst.add (measurable_fst.comp measurable_snd)).prodMk
    (measurable_snd.comp measurable_snd)

/-- Cumulative-cost lift of a cost-increment kernel. -/
noncomputable def accumulatedCostKernel (Q : Kernel X (ENNReal × X)) :
    Kernel (ENNReal × X) (ENNReal × X) :=
  Kernel.map
    ((Kernel.deterministic (fun z : ENNReal × X ↦ z.1) measurable_fst) ×ₖ
      (Kernel.comap Q Prod.snd measurable_snd))
    addPhaseCost

instance accumulatedCostKernel.instIsMarkovKernel
    (Q : Kernel X (ENNReal × X)) [IsMarkovKernel Q] :
    IsMarkovKernel (accumulatedCostKernel Q) := by
  unfold accumulatedCostKernel
  exact Kernel.IsMarkovKernel.map _ measurable_addPhaseCost

/-- The next-state marginal forgets the incoming cumulative cost. -/
theorem map_snd_accumulatedCostKernel
    (Q : Kernel X (ENNReal × X)) [IsMarkovKernel Q] (z : ENNReal × X) :
    Measure.map Prod.snd (accumulatedCostKernel Q z) =
      Measure.map Prod.snd (Q z.2) := by
  unfold accumulatedCostKernel
  rw [Kernel.map_apply _ measurable_addPhaseCost,
    Measure.map_map measurable_snd measurable_addPhaseCost]
  change Measure.map (Prod.snd ∘ Prod.snd)
      (((Kernel.deterministic (fun z : ENNReal × X ↦ z.1) measurable_fst) ×ₖ
        (Kernel.comap Q Prod.snd measurable_snd)) z) = _
  rw [← Measure.map_map measurable_snd measurable_snd]
  change Measure.map Prod.snd
      (Kernel.snd
        ((Kernel.deterministic (fun z : ENNReal × X ↦ z.1) measurable_fst) ×ₖ
          (Kernel.comap Q Prod.snd measurable_snd)) z) = _
  rw [Kernel.snd_prod]
  rfl

/-- State recursion after binding an arbitrary cumulative-cost law. -/
theorem map_snd_bind_accumulatedCostKernel
    (Q : Kernel X (ENNReal × X)) [IsMarkovKernel Q]
    (nu : Measure (ENNReal × X)) [SFinite nu] :
    Measure.map Prod.snd (nu.bind (accumulatedCostKernel Q)) =
      (Measure.map Prod.snd nu).bind
        (Kernel.map Q Prod.snd) := by
  ext A hA
  rw [Measure.map_apply measurable_snd hA,
    Measure.bind_apply (hA.preimage measurable_snd) (Kernel.aemeasurable _),
    Measure.bind_apply hA (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe (Kernel.map Q Prod.snd) hA)
      measurable_snd]
  apply lintegral_congr
  intro z
  rw [← Measure.map_apply measurable_snd hA,
    map_snd_accumulatedCostKernel]
  rw [Kernel.map_apply _ measurable_snd]

/-- Pointwise mean of the updated cumulative cost. -/
theorem lintegral_fst_accumulatedCostKernel
    (Q : Kernel X (ENNReal × X)) [IsMarkovKernel Q] (z : ENNReal × X) :
    (∫⁻ y, y.1 ∂accumulatedCostKernel Q z) =
      z.1 + Ttc.SequentialCost.stepMean (fun _ ↦ Q) 0 z.2 := by
  unfold accumulatedCostKernel Ttc.SequentialCost.stepMean
  rw [Kernel.map_apply _ measurable_addPhaseCost,
    lintegral_map measurable_fst measurable_addPhaseCost]
  change (∫⁻ y : ENNReal × (ENNReal × X), y.1 + y.2.1
      ∂((Kernel.deterministic (fun z : ENNReal × X ↦ z.1) measurable_fst) ×ₖ
        (Kernel.comap Q Prod.snd measurable_snd)) z) = _
  rw [Kernel.prod_apply, lintegral_prod _ (by fun_prop)]
  simp

/-- Expected cumulative cost equals the old expectation plus the phase mean averaged
against the old state marginal. -/
theorem lintegral_fst_bind_accumulatedCostKernel
    (Q : Kernel X (ENNReal × X)) [IsMarkovKernel Q]
    (nu : Measure (ENNReal × X)) [SFinite nu] :
    (∫⁻ y, y.1 ∂nu.bind (accumulatedCostKernel Q)) =
      (∫⁻ z, z.1 ∂nu) +
        ∫⁻ x, Ttc.SequentialCost.stepMean (fun _ ↦ Q) 0 x
          ∂Measure.map Prod.snd nu := by
  rw [Measure.lintegral_bind (Kernel.measurable (accumulatedCostKernel Q)).aemeasurable
    measurable_fst.aemeasurable]
  simp_rw [lintegral_fst_accumulatedCostKernel]
  rw [lintegral_add_left measurable_fst]
  congr 1
  rw [lintegral_map
    (Ttc.SequentialCost.measurable_stepMean (fun _ ↦ Q) 0) measurable_snd]

#print axioms map_snd_bind_accumulatedCostKernel
#print axioms lintegral_fst_bind_accumulatedCostKernel

end Ttc.CVAccumulatedCostKernel
