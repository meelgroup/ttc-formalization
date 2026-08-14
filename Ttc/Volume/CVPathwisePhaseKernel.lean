/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVSequentialPhaseSampler
import Ttc.Volume.SpeedyAcceptanceRejection
import Mathlib.Probability.Kernel.WithDensity

/-!
# A pathwise accept/restart kernel for a Gaussian cooling phase

Normalizing a measure-valued expression is nonlinear.  To obtain an honest transition
kernel we normalize separately at every input state.  `normalizeOr` also supplies a
Markov fallback on the zero-mass branch, making the construction total without pretending
that conditioning a zero measure is a probability law.

Applied twice -- first to rejection into the shrunken body, then to the speedy acceptance
weight -- this gives `pathwisePhaseKernel`.  At every state where the two rejection masses
are positive, its value is exactly `CVSampler.phaseLaw` started from that point mass and
therefore exactly the explicit `firstAcceptedPoint` law.
-/

namespace Ttc.CVPathwisePhaseKernel

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.Probability
open Ttc.CVSequentialPhaseSampler Ttc.SpeedyRejection
open scoped ENNReal Pointwise

/-- Reciprocal total mass, except that a zero measure receives weight zero. -/
noncomputable def normalizationWeight
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (kappa : Kernel A B) (a : A) (_b : B) : ENNReal :=
  if kappa a Set.univ = 0 then 0 else (kappa a Set.univ)⁻¹

/-- Weight selecting exactly the zero-total-mass inputs. -/
noncomputable def zeroMassWeight
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (kappa : Kernel A B) (a : A) (_c : C) : ENNReal :=
  if kappa a Set.univ = 0 then 1 else 0

theorem measurable_uncurry_normalizationWeight
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (kappa : Kernel A B) :
    Measurable (Function.uncurry (normalizationWeight kappa)) := by
  unfold normalizationWeight Function.uncurry
  have hm : Measurable fun p : A × B => kappa p.1 Set.univ :=
    (kappa.measurable_coe MeasurableSet.univ).comp measurable_fst
  exact Measurable.ite (measurableSet_eq_fun hm measurable_const)
    measurable_const hm.inv

theorem measurable_uncurry_zeroMassWeight
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (kappa : Kernel A B) :
    Measurable (Function.uncurry (zeroMassWeight (C := C) kappa)) := by
  unfold zeroMassWeight Function.uncurry
  have hm : Measurable fun p : A × C => kappa p.1 Set.univ :=
    (kappa.measurable_coe MeasurableSet.univ).comp measurable_fst
  exact Measurable.ite (measurableSet_eq_fun hm measurable_const)
    measurable_const measurable_const

/-- Normalize `kappa a` when it has positive mass; otherwise use the Markov law
`fallback a`.  This is a genuine kernel even on the zero-mass branch. -/
noncomputable def normalizeOr
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (kappa fallback : Kernel A B) [IsSFiniteKernel kappa] [IsSFiniteKernel fallback] :
    Kernel A B :=
  Kernel.withDensity kappa (normalizationWeight kappa) +
    Kernel.withDensity fallback (zeroMassWeight (C := B) kappa)

instance normalizeOr.isSFiniteKernel
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (kappa fallback : Kernel A B) [IsSFiniteKernel kappa] [IsSFiniteKernel fallback] :
    IsSFiniteKernel (normalizeOr kappa fallback) := by
  unfold normalizeOr
  have hn : ∀ a b, normalizationWeight kappa a b ≠ ⊤ := by
    intro a b
    unfold normalizationWeight
    split_ifs with h
    · simp
    · exact ENNReal.inv_ne_top.mpr h
  have hz : ∀ a b, zeroMassWeight (C := B) kappa a b ≠ ⊤ := by
    intro a b
    unfold zeroMassWeight
    split_ifs <;> simp
  letI : IsSFiniteKernel (Kernel.withDensity kappa (normalizationWeight kappa)) :=
    Kernel.IsSFiniteKernel.withDensity kappa hn
  letI : IsSFiniteKernel
      (Kernel.withDensity fallback (zeroMassWeight (C := B) kappa)) :=
    Kernel.IsSFiniteKernel.withDensity fallback hz
  infer_instance

/-- On the positive-mass branch `normalizeOr` is ordinary normalization. -/
theorem normalizeOr_apply_of_ne_zero
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (kappa fallback : Kernel A B) [IsSFiniteKernel kappa] [IsSFiniteKernel fallback]
    (a : A) (h0 : kappa a Set.univ ≠ 0) :
    normalizeOr kappa fallback a = Arlib.condOn (kappa a) Set.univ := by
  rw [normalizeOr, Kernel.add_apply,
    Kernel.withDensity_apply _ (measurable_uncurry_normalizationWeight kappa),
    Kernel.withDensity_apply _ (measurable_uncurry_zeroMassWeight (C := B) kappa)]
  have hn : normalizationWeight kappa a = fun _ : B => (kappa a Set.univ)⁻¹ := by
    funext b
    simp [normalizationWeight, h0]
  have hz : zeroMassWeight (C := B) kappa a = fun _ : B => 0 := by
    funext b
    simp [zeroMassWeight, h0]
  rw [hn, hz, MeasureTheory.withDensity_const, MeasureTheory.withDensity_const,
    zero_smul, add_zero, Arlib.condOn_def, Measure.restrict_univ]

/-- On the zero-mass branch `normalizeOr` is exactly the supplied fallback. -/
theorem normalizeOr_apply_of_eq_zero
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (kappa fallback : Kernel A B) [IsSFiniteKernel kappa] [IsSFiniteKernel fallback]
    (a : A) (h0 : kappa a Set.univ = 0) :
    normalizeOr kappa fallback a = fallback a := by
  rw [normalizeOr, Kernel.add_apply,
    Kernel.withDensity_apply _ (measurable_uncurry_normalizationWeight kappa),
    Kernel.withDensity_apply _ (measurable_uncurry_zeroMassWeight (C := B) kappa)]
  have hn : normalizationWeight kappa a = fun _ : B => 0 := by
    funext b
    simp [normalizationWeight, h0]
  have hz : zeroMassWeight (C := B) kappa a = fun _ : B => 1 := by
    funext b
    simp [zeroMassWeight, h0]
  rw [hn, hz, MeasureTheory.withDensity_const, MeasureTheory.withDensity_const,
    zero_smul, one_smul, zero_add]

instance normalizeOr.isMarkovKernel
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (kappa fallback : Kernel A B) [IsFiniteKernel kappa]
    [IsMarkovKernel fallback] : IsMarkovKernel (normalizeOr kappa fallback) := by
  constructor
  intro a
  by_cases h0 : kappa a Set.univ = 0
  · rw [normalizeOr_apply_of_eq_zero kappa fallback a h0]
    infer_instance
  · rw [normalizeOr_apply_of_ne_zero kappa fallback a h0]
    exact Arlib.isProbabilityMeasure_condOn _ h0 (measure_ne_top _ _)

/-- Kernel conditioning into a measurable event, with a fallback on inputs from which the
event is unreachable. -/
noncomputable def conditionOr
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (kappa fallback : Kernel A B) [IsFiniteKernel kappa] [IsSFiniteKernel fallback]
    {S : Set B} (hS : MeasurableSet S) : Kernel A B :=
  normalizeOr (kappa.restrict hS) fallback

theorem conditionOr_apply_of_ne_zero
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (kappa fallback : Kernel A B) [IsFiniteKernel kappa] [IsSFiniteKernel fallback]
    {S : Set B} (hS : MeasurableSet S) (a : A) (h0 : kappa a S ≠ 0) :
    conditionOr kappa fallback hS a = Arlib.condOn (kappa a) S := by
  rw [conditionOr, normalizeOr_apply_of_ne_zero]
  · rw [Kernel.restrict_apply, Arlib.condOn_def, Arlib.condOn_def,
      Measure.restrict_univ, Measure.restrict_apply_univ]
  · simpa [Kernel.restrict_apply, Measure.restrict_apply_univ] using h0

/-! ## Normalization does not commute with mixing -/

/-- Binding the statewise-normalized kernel puts the normalization denominator *inside*
the integral over starts. -/
theorem bind_normalizeOr_apply
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (rho : Measure A) (kappa fallback : Kernel A B)
    [IsFiniteKernel kappa] [IsSFiniteKernel fallback]
    (hpos : ∀ a, kappa a Set.univ ≠ 0) {T : Set B} (hT : MeasurableSet T) :
    (rho.bind (normalizeOr kappa fallback)) T =
      ∫⁻ a, kappa a T / kappa a Set.univ ∂rho := by
  rw [Measure.bind_apply hT (normalizeOr kappa fallback).aemeasurable]
  apply lintegral_congr
  intro a
  rw [normalizeOr_apply_of_ne_zero kappa fallback a (hpos a),
    Arlib.condOn_apply _ MeasurableSet.univ hT, Set.inter_univ]

/-- Normalizing only after mixing puts a single denominator *outside* the integral.
Together with `bind_normalizeOr_apply`, this is the precise mismatch: the two expressions
are not equal unless extra control on the input-dependent acceptance masses is available. -/
theorem condOn_bind_apply
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (rho : Measure A) (kappa : Kernel A B) [IsFiniteKernel kappa]
    {T : Set B} (hT : MeasurableSet T) :
    Arlib.condOn (rho.bind kappa) Set.univ T =
      (∫⁻ a, kappa a T ∂rho) / (∫⁻ a, kappa a Set.univ ∂rho) := by
  rw [Arlib.condOn_apply _ MeasurableSet.univ hT, Set.inter_univ,
    Measure.bind_apply hT kappa.aemeasurable,
    Measure.bind_apply MeasurableSet.univ kappa.aemeasurable]

/-- A two-state sub-Markov kernel with input-dependent total mass: mass `1` at `true`
and mass `1/2` at `false`. -/
noncomputable def normalizationMismatchKernel : Kernel Bool Bool :=
  Kernel.withDensity Kernel.id
    (fun x _y => if x then (1 : ENNReal) else 1 / 2)

instance normalizationMismatchKernel.isFiniteKernel :
    IsFiniteKernel normalizationMismatchKernel := by
  unfold normalizationMismatchKernel
  apply Kernel.isFiniteKernel_withDensity_of_bounded Kernel.id
    (B := 1) (by simp)
  intro x y
  cases x <;> norm_num

theorem normalizationMismatchKernel_apply (x : Bool) :
    normalizationMismatchKernel x =
      (if x then (1 : ENNReal) else 1 / 2) • Measure.dirac x := by
  rw [normalizationMismatchKernel,
    Kernel.withDensity_apply _ (Measurable.of_discrete), Kernel.id_apply,
    dirac_withDensity]

theorem normalizationMismatchKernel_univ_ne_zero (x : Bool) :
    normalizationMismatchKernel x Set.univ ≠ 0 := by
  rw [normalizationMismatchKernel_apply, Measure.smul_apply, smul_eq_mul]
  cases x <;> norm_num

/-- Statewise normalization erases the two different acceptance masses and leaves the
identity kernel. -/
theorem normalizeOr_normalizationMismatchKernel_eq_id :
    normalizeOr normalizationMismatchKernel Kernel.id = Kernel.id := by
  ext x S hS
  rw [normalizeOr_apply_of_ne_zero _ _ x
    (normalizationMismatchKernel_univ_ne_zero x),
    Arlib.condOn_apply _ MeasurableSet.univ hS,
    normalizationMismatchKernel_apply, Set.inter_univ,
    Measure.smul_apply, smul_eq_mul, Measure.smul_apply, smul_eq_mul,
    Kernel.id_apply]
  rw [Measure.dirac_apply' _ hS,
    Measure.dirac_apply' _ MeasurableSet.univ]
  cases x with
  | false =>
      by_cases hx : false ∈ S
      · simp only [Bool.false_eq_true, if_false, Set.indicator_of_mem hx,
          Set.indicator_of_mem (Set.mem_univ false), Pi.one_apply, mul_one]
        simp only [one_div]
        exact ENNReal.div_self (a := (2 : ENNReal)⁻¹) (by norm_num) (by norm_num)
      · simp [Set.indicator_of_notMem hx]
  | true => simp

/-- Concrete counterexample: binding a start law through statewise normalization is not
the same as mixing the unnormalized laws and normalizing once.  Thus `phaseLaw rho` cannot
in general be represented by binding `rho` through the pointwise phase kernel. -/
theorem bind_normalizeOr_ne_condOn_bind :
    Arlib.MarkovChains.piHalf.bind
        (normalizeOr normalizationMismatchKernel Kernel.id) ≠
      Arlib.condOn
        (Arlib.MarkovChains.piHalf.bind normalizationMismatchKernel) Set.univ := by
  intro hEq
  have htrue := congrArg (fun mu : Measure Bool => mu ({true} : Set Bool)) hEq
  rw [normalizeOr_normalizationMismatchKernel_eq_id, Measure.id_comp,
    Arlib.MarkovChains.piHalf_singleton] at htrue
  have hraw : Arlib.MarkovChains.piHalf.bind normalizationMismatchKernel =
      (1 / 2 : ENNReal) • Measure.dirac true +
        (1 / 4 : ENNReal) • Measure.dirac false := by
    rw [Arlib.MarkovChains.piHalf, Measure.comp_smul, Measure.comp_add]
    simp only [Measure.dirac_bind normalizationMismatchKernel.measurable,
      normalizationMismatchKernel_apply]
    simp only [if_true, Bool.false_eq_true, if_false, one_smul, smul_add]
    rw [smul_smul]
    congr 1
    simp only [one_div]
    symm
    have h4 : (4 : ENNReal) = 2 * 2 := by norm_num
    rw [h4]
    exact congrArg (fun z : ENNReal => z • Measure.dirac false)
      (ENNReal.mul_inv (a := (2 : ENNReal)) (b := (2 : ENNReal))
        (by simp) (by simp))
  rw [hraw, Arlib.condOn_apply _ MeasurableSet.univ (MeasurableSet.singleton true)] at htrue
  simp only [Set.inter_univ, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (MeasurableSet.singleton true),
    Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_of_mem (Set.mem_singleton true),
    Set.indicator_of_notMem (by simp : false ∉ ({true} : Set Bool)), Pi.one_apply,
    Set.indicator_of_mem (Set.mem_univ true),
    Set.indicator_of_mem (Set.mem_univ false), mul_one, mul_zero, add_zero] at htrue
  have hreal := congrArg ENNReal.toReal htrue
  have hden : (((1 / 2 : ENNReal) + 1 / 4).toReal) = 3 / 4 := by
    rw [ENNReal.toReal_add (by simp) (by simp)]
    norm_num
  simp only [ENNReal.toReal_div] at hreal
  rw [hden] at hreal
  norm_num at hreal

instance conditionOr.isMarkovKernel
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (kappa fallback : Kernel A B) [IsFiniteKernel kappa]
    [IsMarkovKernel fallback] {S : Set B} (hS : MeasurableSet S) :
    IsMarkovKernel (conditionOr kappa fallback hS) := by
  unfold conditionOr
  infer_instance

variable {n : Nat}

theorem lazySpeedyGaussianPhaseKernel_apply_eq_iterate_dirac
    (K : Set (Space n)) (delta sigmaSq : Real) (t : Nat) (x : Space n) :
    lazySpeedyGaussianPhaseKernel K delta sigmaSq t x =
      iterate (lazy (speedyMetropolisGaussian K delta sigmaSq)) (Measure.dirac x) t := by
  rw [← sampleFrom_lazySpeedyGaussianPhaseKernel_eq_iterate]
  unfold sampleFromKernel
  exact (Measure.dirac_bind
    (lazySpeedyGaussianPhaseKernel K delta sigmaSq t).measurable x).symm

/-- The statewise phase proposal after rejection into the shrunken body and rescaling.
If that body is unreachable from an input, the identity fallback makes the kernel total. -/
noncomputable def pathwisePhasePointKernel
    (K : Set (Space n)) (hK : MeasurableSet K) (delta sigmaSq : Real) (t : Nat) :
    Kernel (Space n) (Space n) :=
  let c : Real := 1 - 1 / (2 * (n : Real))
  Kernel.map
    (conditionOr (lazySpeedyGaussianPhaseKernel K delta sigmaSq t) Kernel.id
      (hK.const_smul₀ c))
    (fun x : Space n => c⁻¹ • x)

instance pathwisePhasePointKernel.isMarkovKernel
    (K : Set (Space n)) (hK : MeasurableSet K) (delta sigmaSq : Real) (t : Nat) :
    IsMarkovKernel (pathwisePhasePointKernel K hK delta sigmaSq t) := by
  unfold pathwisePhasePointKernel
  dsimp only
  apply Kernel.IsMarkovKernel.map
  exact measurable_const_smul _

/-- On every state from which the shrunken body has positive probability, the pointwise
proposal is exactly the proposal appearing in `CVSampler.phaseLaw` for a point-mass start. -/
theorem pathwisePhasePointKernel_apply_eq_phasePointProposal
    (K : Set (Space n)) (hK : MeasurableSet K) (delta sigmaSq : Real) (t : Nat)
    (x : Space n)
    (hshrink : iterate (lazy (speedyMetropolisGaussian K delta sigmaSq))
      (Measure.dirac x) t
        ((1 - 1 / (2 * (n : Real))) • K) ≠ 0) :
    pathwisePhasePointKernel K hK delta sigmaSq t x =
      phasePointProposal K delta sigmaSq (Measure.dirac x) t := by
  unfold pathwisePhasePointKernel phasePointProposal
  dsimp only
  rw [Kernel.map_apply _ (measurable_const_smul _), conditionOr_apply_of_ne_zero]
  · rw [lazySpeedyGaussianPhaseKernel_apply_eq_iterate_dirac]
  · rw [lazySpeedyGaussianPhaseKernel_apply_eq_iterate_dirac]
    exact hshrink

/-- The acceptance density used by the final statewise rejection kernel. -/
noncomputable def pathwiseAcceptDensity (c sigmaSq : Real)
    (_x y : Space n) : ENNReal :=
  ENNReal.ofReal (speedyAcceptReal c sigmaSq y)

theorem measurable_uncurry_pathwiseAcceptDensity (c sigmaSq : Real) :
    Measurable (Function.uncurry (pathwiseAcceptDensity (n := n) c sigmaSq)) := by
  unfold pathwiseAcceptDensity Function.uncurry
  exact ENNReal.measurable_ofReal.comp
    ((measurable_speedyAcceptReal c sigmaSq).comp measurable_snd)

/-- The final speedy acceptance weight, as a kernel density independent of the input. -/
noncomputable def pathwiseAcceptedKernel
    (K : Set (Space n)) (hK : MeasurableSet K) (delta sigmaSq : Real) (t : Nat) :
    Kernel (Space n) (Space n) :=
  let c : Real := 1 - 1 / (2 * (n : Real))
  Kernel.withDensity (pathwisePhasePointKernel K hK delta sigmaSq t)
    (pathwiseAcceptDensity c sigmaSq)

instance pathwiseAcceptedKernel.isSFiniteKernel
    (K : Set (Space n)) (hK : MeasurableSet K) (delta sigmaSq : Real) (t : Nat) :
    IsSFiniteKernel (pathwiseAcceptedKernel K hK delta sigmaSq t) := by
  unfold pathwiseAcceptedKernel
  apply Kernel.IsSFiniteKernel.withDensity
  intro x y
  exact ENNReal.ofReal_ne_top

theorem isFiniteKernel_pathwiseAcceptedKernel
    (K : Set (Space n)) (hK : MeasurableSet K) (delta : Real) {sigmaSq : Real}
    (t : Nat) (hsigma : 0 < sigmaSq)
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1) :
    IsFiniteKernel (pathwiseAcceptedKernel K hK delta sigmaSq t) := by
  unfold pathwiseAcceptedKernel
  dsimp only
  apply Kernel.isFiniteKernel_withDensity_of_bounded
    (B := 1) _ (by simp)
  intro x y
  unfold pathwiseAcceptDensity
  rw [ENNReal.ofReal_le_one]
  exact speedyAcceptReal_le_one hsigma hc2 y

theorem pathwiseAcceptedKernel_apply_eq
    (K : Set (Space n)) (hK : MeasurableSet K) (delta sigmaSq : Real) (t : Nat)
    (x : Space n) :
    pathwiseAcceptedKernel K hK delta sigmaSq t x =
      (pathwisePhasePointKernel K hK delta sigmaSq t x).withDensity
        (fun y => ENNReal.ofReal
          (speedyAcceptReal (1 - 1 / (2 * (n : Real))) sigmaSq y)) := by
  unfold pathwiseAcceptedKernel
  dsimp only
  rw [Kernel.withDensity_apply _
    (measurable_uncurry_pathwiseAcceptDensity
      (n := n) (1 - 1 / (2 * (n : Real))) sigmaSq)]
  rfl

/-- The honest pathwise accept/restart transition.  The proposal kernel itself is the
fallback only on the impossible zero-acceptance branch. -/
noncomputable def pathwisePhaseKernel
    (K : Set (Space n)) (hK : MeasurableSet K) (delta sigmaSq : Real) (t : Nat) :
    Kernel (Space n) (Space n) :=
  normalizeOr (pathwiseAcceptedKernel K hK delta sigmaSq t)
    (pathwisePhasePointKernel K hK delta sigmaSq t)

theorem isMarkovKernel_pathwisePhaseKernel
    (K : Set (Space n)) (hK : MeasurableSet K) (delta : Real) {sigmaSq : Real}
    (t : Nat) (hsigma : 0 < sigmaSq)
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1) :
    IsMarkovKernel (pathwisePhaseKernel K hK delta sigmaSq t) := by
  letI : IsFiniteKernel (pathwiseAcceptedKernel K hK delta sigmaSq t) :=
    isFiniteKernel_pathwiseAcceptedKernel K hK delta t hsigma hc2
  unfold pathwisePhaseKernel
  infer_instance

/-- At every input for which both rejection stages have positive mass, the pathwise
kernel is exactly the old law transformer applied to a point mass. -/
theorem pathwisePhaseKernel_apply_eq_phaseLaw_dirac
    (K : Set (Space n)) (hK : MeasurableSet K) (delta : Real) {sigmaSq : Real}
    (t : Nat) (x : Space n)
    (hshrink : iterate (lazy (speedyMetropolisGaussian K delta sigmaSq))
      (Measure.dirac x) t
        ((1 - 1 / (2 * (n : Real))) • K) ≠ 0)
    (haccept : ((phasePointProposal K delta sigmaSq (Measure.dirac x) t).withDensity
      fun y => ENNReal.ofReal
        (speedyAcceptReal (1 - 1 / (2 * (n : Real))) sigmaSq y)) Set.univ ≠ 0) :
    pathwisePhaseKernel K hK delta sigmaSq t x =
      Ttc.CVSampler.phaseLaw K delta sigmaSq (Measure.dirac x) t := by
  have hpoint := pathwisePhasePointKernel_apply_eq_phasePointProposal
    K hK delta sigmaSq t x hshrink
  have haccKernel : pathwiseAcceptedKernel K hK delta sigmaSq t x Set.univ ≠ 0 := by
    rw [pathwiseAcceptedKernel_apply_eq, hpoint]
    exact haccept
  rw [pathwisePhaseKernel, normalizeOr_apply_of_ne_zero _ _ x haccKernel,
    pathwiseAcceptedKernel_apply_eq, hpoint]
  rfl

/-- The pointwise phase kernel is realized by the explicit first-accepted-point loop. -/
theorem pathwisePhaseKernel_apply_eq_firstAcceptedPoint
    (K : Set (Space n)) (hK : MeasurableSet K) (delta : Real) {sigmaSq : Real}
    (t : Nat) (x : Space n) (hsigma : 0 < sigmaSq)
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1)
    (hshrink : iterate (lazy (speedyMetropolisGaussian K delta sigmaSq))
      (Measure.dirac x) t
        ((1 - 1 / (2 * (n : Real))) • K) ≠ 0)
    (haccept : ((phasePointProposal K delta sigmaSq (Measure.dirac x) t).withDensity
      fun y => ENNReal.ofReal
        (speedyAcceptReal (1 - 1 / (2 * (n : Real))) sigmaSq y)) Set.univ ≠ 0) :
    pathwisePhaseKernel K hK delta sigmaSq t x =
      Measure.map (firstAcceptedPoint (1 - 1 / (2 * (n : Real))) sigmaSq)
        (roundsMeasure
          (proposal (phasePointProposal K delta sigmaSq (Measure.dirac x) t))) := by
  rw [pathwisePhaseKernel_apply_eq_phaseLaw_dirac K hK delta t x hshrink haccept]
  symm
  letI : IsProbabilityMeasure
      (phasePointProposal K delta sigmaSq (Measure.dirac x) t) := by
    rw [← pathwisePhasePointKernel_apply_eq_phasePointProposal
      K hK delta sigmaSq t x hshrink]
    infer_instance
  exact map_firstAcceptedPoint_eq_phaseLaw K delta (Measure.dirac x) t
    hsigma hc2 haccept

/-- Honest target-TV theorem for the operational replacement.  A mixture of statewise
phase laws is close to a target whenever every statewise law is close.  This is deliberately
a pointwise premise: the repository's existing distributional warm-start theorem controls
the normalize-after-mixing law instead, and `bind_normalizeOr_apply`/`condOn_bind_apply`
show why it cannot discharge this premise. -/
theorem tvLe_bind_pathwisePhaseKernel_of_pointwise
    (rho : Measure (Space n)) [IsProbabilityMeasure rho]
    (tau : Measure (Space n)) [IsProbabilityMeasure tau]
    (K : Set (Space n)) (hK : MeasurableSet K) (delta : Real) {sigmaSq : Real}
    (t : Nat)
    {eps : ENNReal}
    (hpoint : ∀ x, TVLe (pathwisePhaseKernel K hK delta sigmaSq t x) tau eps) :
    TVLe (rho.bind (pathwisePhaseKernel K hK delta sigmaSq t)) tau eps := by
  intro T hT
  constructor
  · rw [Measure.bind_apply hT
      (pathwisePhaseKernel K hK delta sigmaSq t).aemeasurable]
    calc
      ∫⁻ x, pathwisePhaseKernel K hK delta sigmaSq t x T ∂rho ≤
          ∫⁻ _x, tau T + eps ∂rho :=
        lintegral_mono fun x => (hpoint x T hT).1
      _ = tau T + eps := by simp
  · calc
      tau T ≤ ∫⁻ _x, tau T ∂rho := by simp
      _ ≤ ∫⁻ x, pathwisePhaseKernel K hK delta sigmaSq t x T + eps ∂rho :=
        lintegral_mono fun x => (hpoint x T hT).2
      _ = (rho.bind (pathwisePhaseKernel K hK delta sigmaSq t)) T + eps := by
        rw [Measure.bind_apply hT
          (pathwisePhaseKernel K hK delta sigmaSq t).aemeasurable]
        rw [lintegral_add_left
          ((pathwisePhaseKernel K hK delta sigmaSq t).measurable_coe hT)]
        simp

/-! Axiom audit for the generic operational layer. -/

#print axioms normalizeOr_apply_of_ne_zero
#print axioms normalizeOr_apply_of_eq_zero
#print axioms conditionOr_apply_of_ne_zero
#print axioms bind_normalizeOr_apply
#print axioms condOn_bind_apply
#print axioms bind_normalizeOr_ne_condOn_bind
#print axioms pathwisePhasePointKernel_apply_eq_phasePointProposal
#print axioms isMarkovKernel_pathwisePhaseKernel
#print axioms pathwisePhaseKernel_apply_eq_phaseLaw_dirac
#print axioms pathwisePhaseKernel_apply_eq_firstAcceptedPoint
#print axioms tvLe_bind_pathwisePhaseKernel_of_pointwise

end Ttc.CVPathwisePhaseKernel
