import Ttc.Exec.CVAccumulatedCostKernel

/-!
# Costed phase kernels retaining the complete state history

This adapter turns a cost-increment kernel `Q i : X → (cost × X)` into a kernel whose
state contains cumulative cost, a full history buffer, and the current state.  It is the
concrete representation needed by the history-preserving reset induction.
-/

namespace Ttc.CVHistoryCostedKernel

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

variable {X : Type*} [MeasurableSpace X]

abbrev HistoryPayload (X : Type*) := ENNReal × (Nat → X)
abbrev HistoryState (X : Type*) := HistoryPayload X × X

/-- Append the sampled state at index `i+1` and add its phase cost. -/
def appendPhase (i : Nat)
    (z : HistoryPayload X × (ENNReal × X)) : HistoryState X :=
  ((z.1.1 + z.2.1, Function.update z.1.2 (i + 1) z.2.2), z.2.2)

theorem measurable_update_history (i : Nat) :
    Measurable (fun z : (Nat → X) × X ↦ Function.update z.1 (i + 1) z.2) := by
  exact measurable_update'

theorem measurable_appendPhase (i : Nat) :
    Measurable (appendPhase (X := X) i) := by
  unfold appendPhase
  have hhistory : Measurable
      (fun z : HistoryPayload X × (ENNReal × X) ↦
        Function.update z.1.2 (i + 1) z.2.2) := by
    exact (measurable_update_history (X := X) i).comp
      ((measurable_snd.comp measurable_fst).prodMk
        (measurable_snd.comp measurable_snd))
  exact (((measurable_fst.comp measurable_fst).add
      (measurable_fst.comp measurable_snd)).prodMk hhistory).prodMk
        (measurable_snd.comp measurable_snd)

/-- Lift one cost-increment phase while retaining cumulative cost and full history. -/
noncomputable def historyCostedKernel
    (Q : Kernel X (ENNReal × X)) (i : Nat) :
    Kernel (HistoryState X) (HistoryState X) :=
  Kernel.map
    ((Kernel.deterministic (fun z : HistoryState X ↦ z.1) measurable_fst) ×ₖ
      (Kernel.comap Q Prod.snd measurable_snd))
    (appendPhase i)

instance historyCostedKernel.instIsMarkovKernel
    (Q : Kernel X (ENNReal × X)) [IsMarkovKernel Q] (i : Nat) :
    IsMarkovKernel (historyCostedKernel Q i) := by
  unfold historyCostedKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_appendPhase i)

/-- The current-state marginal is exactly the state marginal of the underlying costed
phase kernel; neither accumulated cost nor stored history affects it. -/
theorem map_snd_historyCostedKernel
    (Q : Kernel X (ENNReal × X)) [IsMarkovKernel Q]
    (i : Nat) (z : HistoryState X) :
    Measure.map Prod.snd (historyCostedKernel Q i z) =
      Measure.map Prod.snd (Q z.2) := by
  unfold historyCostedKernel
  rw [Kernel.map_apply _ (measurable_appendPhase i),
    Measure.map_map measurable_snd (measurable_appendPhase i)]
  change Measure.map (Prod.snd ∘ Prod.snd)
      (((Kernel.deterministic (fun z : HistoryState X ↦ z.1) measurable_fst) ×ₖ
        (Kernel.comap Q Prod.snd measurable_snd)) z) = _
  rw [← Measure.map_map measurable_snd measurable_snd]
  change Measure.map Prod.snd
      (Kernel.snd
        ((Kernel.deterministic (fun z : HistoryState X ↦ z.1) measurable_fst) ×ₖ
          (Kernel.comap Q Prod.snd measurable_snd)) z) = _
  rw [Kernel.snd_prod]
  rfl

/-- Pointwise expected cumulative cost after one history-appending phase. -/
theorem lintegral_historyCost_historyCostedKernel
    (Q : Kernel X (ENNReal × X)) [IsMarkovKernel Q]
    (i : Nat) (z : HistoryState X) :
    (∫⁻ y, y.1.1 ∂historyCostedKernel Q i z) =
      z.1.1 + Ttc.SequentialCost.stepMean (fun _ ↦ Q) 0 z.2 := by
  unfold historyCostedKernel Ttc.SequentialCost.stepMean
  rw [Kernel.map_apply _ (measurable_appendPhase i)]
  change (∫⁻ y, (Prod.fst ∘ Prod.fst) y
      ∂Measure.map (appendPhase i)
        (((Kernel.deterministic (fun z : HistoryState X ↦ z.1) measurable_fst) ×ₖ
          (Kernel.comap Q Prod.snd measurable_snd)) z)) = _
  rw [lintegral_map (measurable_fst.comp measurable_fst) (measurable_appendPhase i)]
  change (∫⁻ y : HistoryPayload X × (ENNReal × X), y.1.1 + y.2.1
      ∂((Kernel.deterministic (fun z : HistoryState X ↦ z.1) measurable_fst) ×ₖ
        (Kernel.comap Q Prod.snd measurable_snd)) z) = _
  rw [Kernel.prod_apply, lintegral_prod _ (by fun_prop)]
  rw [Kernel.deterministic_apply measurable_fst, Kernel.comap_apply]
  simp_rw [lintegral_add_left measurable_const]
  rw [lintegral_dirac']
  · simp
  · fun_prop

/-- Bound-law recursion for the current-state marginal. -/
theorem map_snd_bind_historyCostedKernel
    (Q : Kernel X (ENNReal × X)) [IsMarkovKernel Q]
    (i : Nat) (nu : Measure (HistoryState X)) [SFinite nu] :
    Measure.map Prod.snd (nu.bind (historyCostedKernel Q i)) =
      (Measure.map Prod.snd nu).bind (Kernel.map Q Prod.snd) := by
  ext S hS
  rw [Measure.map_apply measurable_snd hS,
    Measure.bind_apply (hS.preimage measurable_snd) (Kernel.aemeasurable _),
    Measure.bind_apply hS (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe (Kernel.map Q Prod.snd) hS) measurable_snd]
  apply lintegral_congr
  intro z
  rw [← Measure.map_apply measurable_snd hS, map_snd_historyCostedKernel]
  rw [Kernel.map_apply _ measurable_snd]

/-- The complete-history representation has exactly the same additive expected-cost
recursion as the cumulative-cost-only representation. -/
theorem lintegral_historyCost_bind_historyCostedKernel
    (Q : Kernel X (ENNReal × X)) [IsMarkovKernel Q]
    (i : Nat) (nu : Measure (HistoryState X)) [SFinite nu] :
    (∫⁻ y, y.1.1 ∂nu.bind (historyCostedKernel Q i)) =
      (∫⁻ z, z.1.1 ∂nu) +
        ∫⁻ x, Ttc.SequentialCost.stepMean (fun _ ↦ Q) 0 x
          ∂Measure.map Prod.snd nu := by
  change (∫⁻ y, (Prod.fst ∘ Prod.fst) y
      ∂nu.bind (historyCostedKernel Q i)) = _
  rw [Measure.lintegral_bind (Kernel.measurable (historyCostedKernel Q i)).aemeasurable
    (measurable_fst.comp measurable_fst).aemeasurable]
  simp_rw [show ∀ z : HistoryState X,
      (∫⁻ y, (Prod.fst ∘ Prod.fst) y ∂historyCostedKernel Q i z) =
        z.1.1 + Ttc.SequentialCost.stepMean (fun _ ↦ Q) 0 z.2 by
      intro z
      simpa only [Function.comp_apply] using
        lintegral_historyCost_historyCostedKernel Q i z]
  change (∫⁻ z, (Prod.fst ∘ Prod.fst) z +
      Ttc.SequentialCost.stepMean (fun _ ↦ Q) 0 z.2 ∂nu) = _
  rw [lintegral_add_left (measurable_fst.comp measurable_fst)]
  congr 1
  rw [lintegral_map
    (Ttc.SequentialCost.measurable_stepMean (fun _ ↦ Q) 0) measurable_snd]

#print axioms map_snd_historyCostedKernel
#print axioms lintegral_historyCost_bind_historyCostedKernel

end Ttc.CVHistoryCostedKernel
