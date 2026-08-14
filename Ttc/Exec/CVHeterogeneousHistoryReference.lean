import Ttc.Exec.CVRetainedHistoryReferenceInduction
import Ttc.Exec.CVAccumulatedCostKernel

/-!
# Retained score history with a separate current seed

The older history adapter stores the full phase output as both a history entry and the
next Markov state.  For CV this identifies the retained estimator score with the warm
seed and forces a reference path to inherit the warmth of the coarse scaled-score law.

This adapter separates those roles.  A phase kernel has type

`Seed → (cost × (Score × Seed))`.

The score is appended to the immutable estimator history, while only the last seed is
used as the next Markov state.  Consequently a reference reset may replace the seed by
an exact stationary target without changing any score already used by the estimator or
the accumulated query cost.  The remaining premise is stated sharply: the *seed
marginal* of each costed phase must be TV-close to the next stationary target.
-/

set_option autoImplicit false

namespace Ttc.CVHeterogeneousHistoryReference

open MeasureTheory ProbabilityTheory Finset
open Arlib
open Ttc.CVRetainedHistoryReferenceInduction
open scoped ENNReal Classical BigOperators

variable {Score Seed : Type*} [MeasurableSpace Score] [MeasurableSpace Seed]

abbrev HeterogeneousHistoryPayload (Score : Type*) := ENNReal × (Nat → Score)
abbrev HeterogeneousHistoryState (Score Seed : Type*) :=
  HeterogeneousHistoryPayload Score × Seed

/-- Add the phase cost and score to history, retaining only the new seed as state. -/
def appendHeterogeneousPhase (i : Nat)
    (z : HeterogeneousHistoryPayload Score × (ENNReal × (Score × Seed))) :
    HeterogeneousHistoryState Score Seed :=
  ((z.1.1 + z.2.1, Function.update z.1.2 (i + 1) z.2.2.1), z.2.2.2)

theorem measurable_appendHeterogeneousPhase (i : Nat) :
    Measurable (appendHeterogeneousPhase (Score := Score) (Seed := Seed) i) := by
  unfold appendHeterogeneousPhase
  have hhistory : Measurable
      (fun z : HeterogeneousHistoryPayload Score × (ENNReal × (Score × Seed)) ↦
        Function.update z.1.2 (i + 1) z.2.2.1) := by
    exact measurable_update'.comp
      ((measurable_snd.comp measurable_fst).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  exact (((measurable_fst.comp measurable_fst).add
      (measurable_fst.comp measurable_snd)).prodMk hhistory).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_snd))

/-- Lift a costed score/seed kernel while keeping score history and current seed
separate. -/
noncomputable def heterogeneousHistoryKernel
    (Q : Kernel Seed (ENNReal × (Score × Seed))) (i : Nat) :
    Kernel (HeterogeneousHistoryState Score Seed)
      (HeterogeneousHistoryState Score Seed) :=
  Kernel.map
    ((Kernel.deterministic
        (fun z : HeterogeneousHistoryState Score Seed ↦ z.1) measurable_fst) ×ₖ
      (Kernel.comap Q Prod.snd measurable_snd))
    (appendHeterogeneousPhase i)

instance heterogeneousHistoryKernel.instIsMarkovKernel
    (Q : Kernel Seed (ENNReal × (Score × Seed))) [IsMarkovKernel Q] (i : Nat) :
    IsMarkovKernel (heterogeneousHistoryKernel Q i) := by
  unfold heterogeneousHistoryKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_appendHeterogeneousPhase i)

/-- Expected query increment of a heterogeneous phase. -/
noncomputable def heterogeneousStepMean
    (Q : Kernel Seed (ENNReal × (Score × Seed))) (x : Seed) : ENNReal :=
  ∫⁻ y, y.1 ∂Q x

theorem measurable_heterogeneousStepMean
    (Q : Kernel Seed (ENNReal × (Score × Seed))) :
    Measurable (heterogeneousStepMean Q) := by
  exact measurable_fst.lintegral_kernel

/-- The next-state marginal is precisely the new-seed marginal of `Q`. -/
theorem map_snd_heterogeneousHistoryKernel
    (Q : Kernel Seed (ENNReal × (Score × Seed))) [IsMarkovKernel Q]
    (i : Nat) (z : HeterogeneousHistoryState Score Seed) :
    Measure.map Prod.snd (heterogeneousHistoryKernel Q i z) =
      Measure.map (fun y : ENNReal × (Score × Seed) ↦ y.2.2) (Q z.2) := by
  unfold heterogeneousHistoryKernel
  rw [Kernel.map_apply _ (measurable_appendHeterogeneousPhase i),
    Measure.map_map measurable_snd (measurable_appendHeterogeneousPhase i)]
  change Measure.map (fun y : HeterogeneousHistoryPayload Score ×
      (ENNReal × (Score × Seed)) ↦ y.2.2.2)
      (((Kernel.deterministic
          (fun z : HeterogeneousHistoryState Score Seed ↦ z.1) measurable_fst) ×ₖ
        (Kernel.comap Q Prod.snd measurable_snd)) z) = _
  change Measure.map
      ((fun y : ENNReal × (Score × Seed) ↦ y.2.2) ∘ Prod.snd)
      (((Kernel.deterministic
          (fun z : HeterogeneousHistoryState Score Seed ↦ z.1) measurable_fst) ×ₖ
        (Kernel.comap Q Prod.snd measurable_snd)) z) = _
  rw [← Measure.map_map (by fun_prop :
      Measurable (fun y : ENNReal × (Score × Seed) ↦ y.2.2)) measurable_snd]
  change Measure.map (fun y : ENNReal × (Score × Seed) ↦ y.2.2)
      (Kernel.snd
        ((Kernel.deterministic
          (fun z : HeterogeneousHistoryState Score Seed ↦ z.1) measurable_fst) ×ₖ
          (Kernel.comap Q Prod.snd measurable_snd)) z) = _
  rw [Kernel.snd_prod]
  rfl

/-- Pointwise accumulated-cost identity. -/
theorem lintegral_historyCost_heterogeneousHistoryKernel
    (Q : Kernel Seed (ENNReal × (Score × Seed))) [IsMarkovKernel Q]
    (i : Nat) (z : HeterogeneousHistoryState Score Seed) :
    (∫⁻ y, y.1.1 ∂heterogeneousHistoryKernel Q i z) =
      z.1.1 + heterogeneousStepMean Q z.2 := by
  unfold heterogeneousHistoryKernel heterogeneousStepMean
  rw [Kernel.map_apply _ (measurable_appendHeterogeneousPhase i)]
  change (∫⁻ y, (Prod.fst ∘ Prod.fst) y
      ∂Measure.map (appendHeterogeneousPhase i)
        (((Kernel.deterministic
          (fun z : HeterogeneousHistoryState Score Seed ↦ z.1) measurable_fst) ×ₖ
          (Kernel.comap Q Prod.snd measurable_snd)) z)) = _
  rw [lintegral_map (measurable_fst.comp measurable_fst)
    (measurable_appendHeterogeneousPhase i)]
  change (∫⁻ y : HeterogeneousHistoryPayload Score ×
      (ENNReal × (Score × Seed)), y.1.1 + y.2.1
      ∂((Kernel.deterministic
        (fun z : HeterogeneousHistoryState Score Seed ↦ z.1) measurable_fst) ×ₖ
        (Kernel.comap Q Prod.snd measurable_snd)) z) = _
  rw [Kernel.prod_apply, lintegral_prod _ (by fun_prop)]
  rw [Kernel.deterministic_apply measurable_fst, Kernel.comap_apply]
  simp_rw [lintegral_add_left measurable_const]
  rw [lintegral_dirac']
  · simp
  · fun_prop

theorem map_snd_bind_heterogeneousHistoryKernel
    (Q : Kernel Seed (ENNReal × (Score × Seed))) [IsMarkovKernel Q]
    (i : Nat) (nu : Measure (HeterogeneousHistoryState Score Seed)) [SFinite nu] :
    Measure.map Prod.snd (nu.bind (heterogeneousHistoryKernel Q i)) =
      (Measure.map Prod.snd nu).bind
        (Kernel.map Q (fun y : ENNReal × (Score × Seed) ↦ y.2.2)) := by
  ext S hS
  rw [Measure.map_apply measurable_snd hS,
    Measure.bind_apply (hS.preimage measurable_snd) (Kernel.aemeasurable _),
    Measure.bind_apply hS (Kernel.aemeasurable _),
    lintegral_map
      (Kernel.measurable_coe
        (Kernel.map Q (fun y : ENNReal × (Score × Seed) ↦ y.2.2)) hS)
      measurable_snd]
  apply lintegral_congr
  intro z
  rw [← Measure.map_apply measurable_snd hS,
    map_snd_heterogeneousHistoryKernel]
  rw [Kernel.map_apply _ (by fun_prop)]

theorem lintegral_historyCost_bind_heterogeneousHistoryKernel
    (Q : Kernel Seed (ENNReal × (Score × Seed))) [IsMarkovKernel Q]
    (i : Nat) (nu : Measure (HeterogeneousHistoryState Score Seed)) [SFinite nu] :
    (∫⁻ y, y.1.1 ∂nu.bind (heterogeneousHistoryKernel Q i)) =
      (∫⁻ z, z.1.1 ∂nu) +
        ∫⁻ x, heterogeneousStepMean Q x ∂Measure.map Prod.snd nu := by
  change (∫⁻ y, (Prod.fst ∘ Prod.fst) y
      ∂nu.bind (heterogeneousHistoryKernel Q i)) = _
  rw [Measure.lintegral_bind
    (Kernel.measurable (heterogeneousHistoryKernel Q i)).aemeasurable
    (measurable_fst.comp measurable_fst).aemeasurable]
  simp_rw [show ∀ z : HeterogeneousHistoryState Score Seed,
      (∫⁻ y, (Prod.fst ∘ Prod.fst) y ∂heterogeneousHistoryKernel Q i z) =
        z.1.1 + heterogeneousStepMean Q z.2 by
      intro z
      simpa only [Function.comp_apply] using
        lintegral_historyCost_heterogeneousHistoryKernel Q i z]
  change (∫⁻ z, (Prod.fst ∘ Prod.fst) z +
      heterogeneousStepMean Q z.2 ∂nu) = _
  rw [lintegral_add_left (measurable_fst.comp measurable_fst)]
  congr 1
  rw [lintegral_map
    (measurable_heterogeneousStepMean Q) measurable_snd]

/-- Reference induction driven only by seed-marginal TV and exact-stationary expected
phase cost.  This is the sharp operational seam for a constant-warm implementation. -/
theorem exists_heterogeneousHistoryReference_of_seedKernels
    [StandardBorelSpace Seed] [Nonempty Seed]
    (Q : Nat → Kernel Seed (ENNReal × (Score × Seed)))
    [∀ i, IsMarkovKernel (Q i)]
    (mu0 nu0 : Measure (HeterogeneousHistoryState Score Seed))
    [IsProbabilityMeasure mu0] [IsProbabilityMeasure nu0]
    (tau : Nat → Measure Seed) [∀ i, IsProbabilityMeasure (tau i)]
    (e B : Nat → ENNReal) {d initialBudget : ENNReal}
    (hinitTV : TVLe mu0 nu0 d)
    (hinitState : Measure.map Prod.snd nu0 = tau 0)
    (hinitMean : (∫⁻ z, z.1.1 ∂nu0) ≤ initialBudget)
    (hphaseSeedTV : ∀ i,
      TVLe ((tau i).bind
        (Kernel.map (Q i) (fun y : ENNReal × (Score × Seed) ↦ y.2.2)))
        (tau (i + 1)) (e i))
    (hphaseCost : ∀ i,
      (∫⁻ x, heterogeneousStepMean (Q i) x ∂tau i) ≤ B i)
    (t : Nat) :
    ∃ reference : Measure (HeterogeneousHistoryState Score Seed),
      IsProbabilityMeasure reference ∧
      Measure.map Prod.snd reference = tau t ∧
      TVLe
        (retainedPathLaw (fun i ↦ heterogeneousHistoryKernel (Q i) i) mu0 t)
        reference (d + ∑ i ∈ range t, e i) ∧
      (∫⁻ z, z.1.1 ∂reference) ≤
        initialBudget + ∑ i ∈ range t, B i := by
  apply exists_exactHistoryReference_terminal
    (fun a : HeterogeneousHistoryPayload Score ↦ a.1) measurable_fst
    (fun i ↦ heterogeneousHistoryKernel (Q i) i)
    mu0 nu0 tau e B hinitTV hinitState hinitMean
  · intro i nu hprob hstate
    letI : IsProbabilityMeasure nu := hprob
    rw [map_snd_bind_heterogeneousHistoryKernel, hstate]
    exact hphaseSeedTV i
  · intro i nu hprob hstate
    letI : IsProbabilityMeasure nu := hprob
    rw [lintegral_historyCost_bind_heterogeneousHistoryKernel, hstate]
    exact add_le_add_right (hphaseCost i) _

#print axioms map_snd_heterogeneousHistoryKernel
#print axioms lintegral_historyCost_bind_heterogeneousHistoryKernel
#print axioms exists_heterogeneousHistoryReference_of_seedKernels

end Ttc.CVHeterogeneousHistoryReference
