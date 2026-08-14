/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVSequentialDependence
import Ttc.Volume.CVSampler

/-!
# Distributional warm starts for a sequential phase kernel

This file supplies the operational part of the LV2 event-conditioning argument for any
honest Markov transition kernel.  In particular, conditioning an event in the realized
history and then taking the next transition is exactly the same as restarting that
transition from the corresponding conditional last-state distribution.  Mixing is only
required from warm *distributions*, never from every point.

The result applies directly to the (iterated) speedy-walk kernel.  The repository's
`Ttc.CVSampler.phaseLaw`, however, performs a globally normalized rejection operation on
the output measure.  That measure transformer is not currently exposed as a Markov
kernel, so the final rejection-normalized phase law cannot yet be substituted for `Q`
below without a pathwise acceptance/restart construction.
-/

namespace Ttc.CVSequentialPhaseSampler

open MeasureTheory ProbabilityTheory
open Arlib Arlib.Probability Arlib.GaussianCooling
open scoped ENNReal

/-- Run one (possibly multi-step) phase kernel from an arbitrary starting law. -/
noncomputable def sampleFromKernel
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (Q : Kernel A B) (rho : Measure A) : Measure B :=
  rho.bind Q

instance sampleFromKernel.isProbabilityMeasure
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (Q : Kernel A B) [IsMarkovKernel Q] (rho : Measure A)
    [IsProbabilityMeasure rho] : IsProbabilityMeasure (sampleFromKernel Q rho) := by
  unfold sampleFromKernel
  infer_instance

/-- The rectangle identity behind conditional restart.  It is deliberately stated for
an arbitrary start law and an arbitrary Markov kernel, so it can be reused for a whole
phase kernel rather than only a single walk step. -/
theorem compProd_rectangle_eq_conditional_restart
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {rho : Measure A} [IsProbabilityMeasure rho]
    (Q : Kernel A B) [IsMarkovKernel Q]
    {S : Set A} {T : Set B} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hhalf : 1 / 2 <= rho.real S) :
    (rho ⊗ₘ Q).real (Prod.fst ⁻¹' S ∩ Prod.snd ⁻¹' T) =
      rho.real S * (sampleFromKernel Q (condOn rho S)).real T := by
  have hS0 : rho S ≠ 0 := by
    intro hz
    have : rho.real S = 0 := by simp [Measure.real, hz]
    linarith
  have hStop : rho S ≠ ⊤ := measure_ne_top rho S
  have hrect : Prod.fst ⁻¹' S ∩ Prod.snd ⁻¹' T = S ×ˢ T := by ext x; simp
  have hbind : sampleFromKernel Q (condOn rho S) T =
      (rho S)⁻¹ * ∫⁻ a in S, Q a T ∂rho := by
    rw [sampleFromKernel, condOn_def, Measure.bind_apply hT Q.aemeasurable,
      lintegral_smul_measure]
    simp only [smul_eq_mul]
  rw [Measure.real, hrect, Measure.compProd_apply_prod hS hT]
  change (∫⁻ a in S, Q a T ∂rho).toReal =
    (rho S).toReal * (sampleFromKernel Q (condOn rho S) T).toReal
  rw [hbind, ← ENNReal.toReal_mul]
  exact congrArg ENNReal.toReal
    (ENNReal.mul_inv_cancel_left hS0 hStop).symm

/-- Warmness is preserved by measurable pushforward. -/
theorem isWarm_map
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {rho eta : Measure A} {M : ENNReal} (h : IsWarm M rho eta)
    {f : A → B} (hf : Measurable f) : IsWarm M (rho.map f) (eta.map f) := by
  intro T hT
  rw [Measure.map_apply hf hT, Measure.map_apply hf hT]
  exact h (f ⁻¹' T) (hf hT)

/-- Conditioning an event in a history law of mass at least one half makes the induced
last-state law at most twice as warm as its unconditioned last-state marginal. -/
theorem isWarm_map_condOn_of_half
    {H A : Type*} [MeasurableSpace H] [MeasurableSpace A]
    {rho : Measure H} [IsProbabilityMeasure rho] {pi : Measure A}
    {last : H → A} (hlast : Measurable last) {M : ENNReal}
    (hwarm : IsWarm M (rho.map last) pi)
    {S : Set H} (hS : MeasurableSet S) (hhalf : 1 / 2 ≤ rho.real S) :
    IsWarm (2 * M) ((condOn rho S).map last) pi := by
  have hself : IsWarm 2 (condOn rho S) rho := by
    simpa using
      (CVSequentialDependence.isWarm_condOn_of_half (IsWarm.refl rho) hS hhalf)
  exact (isWarm_map hself hlast).trans hwarm

/-- A conditional history followed by a kernel depending measurably on its last state is
the same as restarting the kernel from the conditional last-state distribution. -/
theorem compProd_comap_rectangle_eq_conditional_restart
    {H A B : Type*} [MeasurableSpace H] [MeasurableSpace A] [MeasurableSpace B]
    {rho : Measure H} [IsProbabilityMeasure rho]
    (Q : Kernel A B) [IsMarkovKernel Q] {last : H → A} (hlast : Measurable last)
    {S : Set H} {T : Set B} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hhalf : 1 / 2 ≤ rho.real S) :
    (rho ⊗ₘ Kernel.comap Q last hlast).real
        (Prod.fst ⁻¹' S ∩ Prod.snd ⁻¹' T) =
      rho.real S *
        (sampleFromKernel Q ((condOn rho S).map last)).real T := by
  have hS0 : rho S ≠ 0 := by
    intro hz
    have : rho.real S = 0 := by simp [Measure.real, hz]
    linarith
  have hStop : rho S ≠ ⊤ := measure_ne_top rho S
  have hrect : Prod.fst ⁻¹' S ∩ Prod.snd ⁻¹' T = S ×ˢ T := by ext x; simp
  have hbind : sampleFromKernel Q ((condOn rho S).map last) T =
      (rho S)⁻¹ * ∫⁻ h in S, Q (last h) T ∂rho := by
    rw [sampleFromKernel, Measure.bind_apply hT Q.aemeasurable,
      lintegral_map (Q.measurable_coe hT) hlast,
      condOn_def, lintegral_smul_measure]
    simp only [smul_eq_mul]
  rw [Measure.real, hrect, Measure.compProd_apply_prod hS hT]
  simp only [Kernel.comap_apply]
  change (∫⁻ h in S, Q (last h) T ∂rho).toReal =
    (rho S).toReal *
      (sampleFromKernel Q ((condOn rho S).map last) T).toReal
  rw [hbind, ← ENNReal.toReal_mul]
  exact congrArg ENNReal.toReal
    (ENNReal.mul_inv_cancel_left hS0 hStop).symm

/-- Operational LV2 Lemma 4.3 for a transition depending on the last state of an
arbitrary history.  A distributional warm-start guarantee for `Q` gives quantitative
independence between the whole history and the next state. -/
theorem nuIndep_compProd_comap_of_distributionalWarm
    {H A B : Type*} [MeasurableSpace H] [MeasurableSpace A] [MeasurableSpace B]
    {rho : Measure H} [IsProbabilityMeasure rho]
    {pi : Measure A} {tau : Measure B} [IsProbabilityMeasure tau]
    (Q : Kernel A B) [IsMarkovKernel Q] {last : H → A} (hlast : Measurable last)
    {M eps : ENNReal} (hwarm : IsWarm M (rho.map last) pi) (heps : eps ≠ ⊤)
    (hmix : ∀ eta : Measure A, IsWarm (2 * M) eta pi →
      IsProbabilityMeasure eta → TVLe (sampleFromKernel Q eta) tau eps) :
    NuIndep (rho ⊗ₘ Kernel.comap Q last hlast) Prod.fst Prod.snd
      (2 * eps.toReal) := by
  let joint : Measure (H × B) := rho ⊗ₘ Kernel.comap Q last hlast
  letI : IsProbabilityMeasure joint := by dsimp [joint]; infer_instance
  apply CVSequentialDependence.nuIndep_of_largeEvent_conditionedSampler
    (μ := joint) (τ := tau) (H := Prod.fst) (Y := Prod.snd)
    measurable_fst measurable_snd
    (fun S => sampleFromKernel Q ((condOn rho S).map last)) heps
  · intro S hS hhalfJoint
    have hfst : joint.fst = rho := by
      dsimp [joint]
      exact Measure.fst_compProd rho (Kernel.comap Q last hlast)
    have hhalf : 1 / 2 ≤ rho.real S := by
      change 1 / 2 ≤ (joint (Prod.fst ⁻¹' S)).toReal at hhalfJoint
      rw [← Measure.fst_apply hS, hfst] at hhalfJoint
      exact hhalfJoint
    letI : IsProbabilityMeasure (condOn rho S) :=
      Arlib.isProbabilityMeasure_condOn rho (by
        intro hz
        have : rho.real S = 0 := by simp [Measure.real, hz]
        linarith) (measure_ne_top rho S)
    letI : IsProbabilityMeasure ((condOn rho S).map last) :=
      Measure.isProbabilityMeasure_map hlast.aemeasurable
    exact sampleFromKernel.isProbabilityMeasure Q _
  · intro S T hS hT hhalfJoint
    have hfst : joint.fst = rho := by
      dsimp [joint]
      exact Measure.fst_compProd rho (Kernel.comap Q last hlast)
    have hhalf : 1 / 2 ≤ rho.real S := by
      change 1 / 2 ≤ (joint (Prod.fst ⁻¹' S)).toReal at hhalfJoint
      rw [← Measure.fst_apply hS, hfst] at hhalfJoint
      exact hhalfJoint
    have hmarg : joint.real (Prod.fst ⁻¹' S) = rho.real S := by
      change (joint (Prod.fst ⁻¹' S)).toReal = (rho S).toReal
      rw [← Measure.fst_apply hS, hfst]
    rw [hmarg]
    exact compProd_comap_rectangle_eq_conditional_restart Q hlast hS hT hhalf
  · intro S hS hhalfJoint
    have hfst : joint.fst = rho := by
      dsimp [joint]
      exact Measure.fst_compProd rho (Kernel.comap Q last hlast)
    have hhalf : 1 / 2 ≤ rho.real S := by
      change 1 / 2 ≤ (joint (Prod.fst ⁻¹' S)).toReal at hhalfJoint
      rw [← Measure.fst_apply hS, hfst] at hhalfJoint
      exact hhalfJoint
    have hstart : IsWarm (2 * M) ((condOn rho S).map last) pi :=
      isWarm_map_condOn_of_half hlast hwarm hS hhalf
    letI : IsProbabilityMeasure (condOn rho S) :=
      Arlib.isProbabilityMeasure_condOn rho (by
        intro hz
        have : rho.real S = 0 := by simp [Measure.real, hz]
        linarith) (measure_ne_top rho S)
    letI : IsProbabilityMeasure ((condOn rho S).map last) :=
      Measure.isProbabilityMeasure_map hlast.aemeasurable
    exact hmix _ hstart inferInstance

/-! ## The actual inhomogeneous trajectory -/

/-- Distributional version of the inhomogeneous Markov dependence bridge.  At time `i`,
the start supplied to `P i` after conditioning on any history event is the pushforward of
the conditioned history law by its last-coordinate map.  The preceding theorem proves
that this restart is exact and costs only the factor `2` in warmness from LV2.

This is the operational replacement for the stronger pointwise premise in
`nuIndep_history_next_inhomogeneousPathMeasure`. -/
theorem nuIndep_history_next_inhomogeneous_of_distributionalWarm
    {E : Type*} [MeasurableSpace E]
    (P : Nat → Kernel E E) [∀ i, IsMarkovKernel (P i)]
    (mu : Measure E) [IsProbabilityMeasure mu] (i : Nat)
    {pi tau : Measure E} [IsProbabilityMeasure tau] {M eps : ENNReal}
    (hwarm : IsWarm M
      (((inhomogeneousPathMeasure P mu).map (Preorder.frestrictLe i)).map
        (fun h => h ⟨i, Finset.mem_Iic.2 le_rfl⟩)) pi)
    (heps : eps ≠ ⊤)
    (hmix : ∀ eta : Measure E, IsWarm (2 * M) eta pi →
      IsProbabilityMeasure eta → TVLe (sampleFromKernel (P i) eta) tau eps) :
    NuIndep (inhomogeneousPathMeasure P mu) (Preorder.frestrictLe i)
      (fun omega => omega (i + 1)) (2 * eps.toReal) := by
  let rho := (inhomogeneousPathMeasure P mu).map (Preorder.frestrictLe i)
  let last : (Finset.Iic i → E) → E :=
    fun h => h ⟨i, Finset.mem_Iic.2 le_rfl⟩
  have hlast : Measurable last := measurable_pi_apply _
  letI : IsProbabilityMeasure rho := by
    dsimp [rho]
    exact Measure.isProbabilityMeasure_map
      (Preorder.measurable_frestrictLe i).aemeasurable
  have hdep : NuIndep
      (rho ⊗ₘ Kernel.comap (P i) last hlast)
      (Prod.fst : ((Finset.Iic i → E) × E) → (Finset.Iic i → E))
      (Prod.snd : ((Finset.Iic i → E) × E) → E)
      (2 * eps.toReal) := by
    apply nuIndep_compProd_comap_of_distributionalWarm (P i) hlast
      (M := M) (eps := eps) (pi := pi) (tau := tau)
    · simpa [rho, last] using hwarm
    · exact heps
    · exact hmix
  have hjoint : rho ⊗ₘ Kernel.comap (P i) last hlast =
      (inhomogeneousPathMeasure P mu).map
        (fun omega => (Preorder.frestrictLe i omega, omega (i + 1))) := by
    simpa [rho, last, inhomogeneousHistoryKernel] using
      (map_history_next_inhomogeneousPathMeasure P mu i)
  intro S T hS hT
  have hrect := hdep S T hS hT
  rw [hjoint] at hrect
  have hpair : Measurable
      (fun omega : Nat → E => (Preorder.frestrictLe i omega, omega (i + 1))) := by
    fun_prop
  have hST : MeasurableSet
      (Prod.fst ⁻¹' S ∩ Prod.snd ⁻¹' T : Set ((Finset.Iic i → E) × E)) :=
    (hS.preimage measurable_fst).inter (hT.preimage measurable_snd)
  have hS' : MeasurableSet
      (Prod.fst ⁻¹' S : Set ((Finset.Iic i → E) × E)) :=
    hS.preimage measurable_fst
  have hT' : MeasurableSet
      (Prod.snd ⁻¹' T : Set ((Finset.Iic i → E) × E)) :=
    hT.preimage measurable_snd
  rw [Measure.real, Measure.map_apply hpair hST, Measure.real,
    Measure.map_apply hpair hS', Measure.real, Measure.map_apply hpair hT'] at hrect
  change |(inhomogeneousPathMeasure P mu).real
      (Preorder.frestrictLe i ⁻¹' S ∩ (fun omega => omega (i + 1)) ⁻¹' T) -
        (inhomogeneousPathMeasure P mu).real (Preorder.frestrictLe i ⁻¹' S) *
          (inhomogeneousPathMeasure P mu).real
            ((fun omega => omega (i + 1)) ⁻¹' T)| ≤ 2 * eps.toReal at hrect
  exact hrect

/-- Measurable functions of the phase history and of the new state inherit the same
dependence coefficient.  This is the form consumed by the corrected `U_i,V_(i+1)`
recursion. -/
theorem nuIndep_historyStatistics_inhomogeneous_of_distributionalWarm
    {E : Type*} [MeasurableSpace E]
    (P : Nat → Kernel E E) [∀ i, IsMarkovKernel (P i)]
    (mu : Measure E) [IsProbabilityMeasure mu] (i : Nat)
    {pi tau : Measure E} [IsProbabilityMeasure tau] {M eps : ENNReal}
    (hwarm : IsWarm M
      (((inhomogeneousPathMeasure P mu).map (Preorder.frestrictLe i)).map
        (fun h => h ⟨i, Finset.mem_Iic.2 le_rfl⟩)) pi)
    (heps : eps ≠ ⊤)
    (hmix : ∀ eta : Measure E, IsWarm (2 * M) eta pi →
      IsProbabilityMeasure eta → TVLe (sampleFromKernel (P i) eta) tau eps)
    {C D : Type*} [MeasurableSpace C] [MeasurableSpace D]
    (f : (Finset.Iic i → E) → C) (g : E → D)
    (hf : Measurable f) (hg : Measurable g) :
    NuIndep (inhomogeneousPathMeasure P mu)
      (fun omega => f (Preorder.frestrictLe i omega))
      (fun omega => g (omega (i + 1))) (2 * eps.toReal) :=
  (nuIndep_history_next_inhomogeneous_of_distributionalWarm
    P mu i hwarm heps hmix).comp hf hg

/-! ## A whole speedy Gaussian phase as a kernel -/

/-- Kernel-level iteration, with composition oriented to match
`MarkovChains.iterate`. -/
noncomputable def iteratedKernel {A : Type*} [MeasurableSpace A]
    (P : Kernel A A) : Nat → Kernel A A
  | 0 => Kernel.id
  | t + 1 => P ∘ₖ iteratedKernel P t

instance iteratedKernel.isMarkovKernel
    {A : Type*} [MeasurableSpace A] (P : Kernel A A) [IsMarkovKernel P] (t : Nat) :
    IsMarkovKernel (iteratedKernel P t) := by
  induction t with
  | zero =>
      simp only [iteratedKernel]
      infer_instance
  | succ t ih =>
      simp only [iteratedKernel]
      infer_instance

/-- The honest `t`-step lazy speedy Gaussian transition kernel.  Unlike
`CVSampler.phaseLaw`, this object is linear in an arbitrary starting measure. -/
noncomputable def lazySpeedyGaussianPhaseKernel {n : Nat}
    (K : Set (EuclideanSpace ℝ (Fin n))) (delta sigmaSq : ℝ) (t : Nat) :
    Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
  iteratedKernel (Arlib.MarkovChains.lazy
    (Arlib.MarkovChains.speedyMetropolisGaussian K delta sigmaSq)) t

instance lazySpeedyGaussianPhaseKernel.isMarkovKernel {n : Nat}
    (K : Set (EuclideanSpace ℝ (Fin n))) (delta sigmaSq : ℝ) (t : Nat) :
    IsMarkovKernel (lazySpeedyGaussianPhaseKernel K delta sigmaSq t) := by
  unfold lazySpeedyGaussianPhaseKernel
  infer_instance

/-- `MarkovChains.iterate`, used by every Gaussian mixing theorem in the repository, is
exactly sampling from the power kernel. -/
theorem iterate_eq_sampleFrom_iteratedKernel
    {A : Type*} [MeasurableSpace A] (P : Kernel A A) (rho : Measure A) (t : Nat) :
    Arlib.MarkovChains.iterate P rho t = sampleFromKernel (iteratedKernel P t) rho := by
  induction t with
  | zero =>
      rw [Arlib.MarkovChains.iterate_zero]
      simp only [iteratedKernel]
      change rho = rho.bind Kernel.id
      exact Measure.id_comp.symm
  | succ t ih =>
      rw [Arlib.MarkovChains.iterate_succ, ih, Arlib.MarkovChains.step_eq_comp]
      simp only [iteratedKernel]
      unfold sampleFromKernel
      exact Measure.comp_assoc

/-- Concrete arbitrary-start law identity for a whole lazy speedy Gaussian phase. -/
theorem sampleFrom_lazySpeedyGaussianPhaseKernel_eq_iterate {n : Nat}
    (K : Set (EuclideanSpace ℝ (Fin n))) (delta sigmaSq : ℝ)
    (rho : Measure (EuclideanSpace ℝ (Fin n))) (t : Nat) :
    sampleFromKernel (lazySpeedyGaussianPhaseKernel K delta sigmaSq t) rho =
      Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy
          (Arlib.MarkovChains.speedyMetropolisGaussian K delta sigmaSq)) rho t := by
  symm
  exact iterate_eq_sampleFrom_iteratedKernel _ _ _

/-! Axiom audit. -/

#print axioms compProd_rectangle_eq_conditional_restart
#print axioms isWarm_map
#print axioms isWarm_map_condOn_of_half
#print axioms compProd_comap_rectangle_eq_conditional_restart
#print axioms nuIndep_compProd_comap_of_distributionalWarm
#print axioms nuIndep_history_next_inhomogeneous_of_distributionalWarm
#print axioms nuIndep_historyStatistics_inhomogeneous_of_distributionalWarm
#print axioms iterate_eq_sampleFrom_iteratedKernel
#print axioms sampleFrom_lazySpeedyGaussianPhaseKernel_eq_iterate

end Ttc.CVSequentialPhaseSampler
