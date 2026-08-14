/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Probability.AdaptiveTVTelescope
import Ttc.Volume.RejectionCutoff
import Ttc.Volume.CVSequentialDependence
import Arlib.MarkovChains.Continuous.MixingFromConductance

/-!
# Bounded adaptive rejection versus ideal fresh rejection

Cousins--Vempala describe a rejection stage using fresh iid samples from a proposal law,
while their implemented process naturally exposes history-dependent conditional laws.
This file gives the exact finite-horizon repair: compare the two retained-history processes
one transition at a time and then apply the same measurable first-accepted cutoff.

The only model-specific premise is `hideal`: the ideal history process really has the same
cutoff-output law as iid `roundsMeasure nu`.  It is immediate for an append-fresh-draw
kernel; keeping it explicit avoids asserting that a sequential Markov walk supplies a
fresh draw from its whole current marginal.
-/

namespace Ttc.CV

open MeasureTheory ProbabilityTheory Set
open Arlib Arlib.Probability Arlib.GaussianCooling
open scoped ENNReal BigOperators

variable {E H : Type*} [MeasurableSpace E] [MeasurableSpace H]

/-- A logarithmic rejection cutoff for a proposal whose acceptance mass is at least
`1/4`. -/
noncomputable def quarterAcceptanceCutoff (b : Real) : Nat :=
  Arlib.MarkovChains.mixingTime 1 (1 / 4) b

/-- The iid no-acceptance tail at `quarterAcceptanceCutoff b` is at most `b`. -/
theorem compl_pow_quarterAcceptanceCutoff_le
    (nu : Measure E) [IsProbabilityMeasure nu]
    {A : Set E} (hA : MeasurableSet A)
    (hquarter : ENNReal.ofReal (1 / 4 : Real) ≤ nu A)
    {b : Real} (hb : 0 < b) :
    nu Aᶜ ^ quarterAcceptanceCutoff b ≤ ENNReal.ofReal b := by
  have hcomp : nu Aᶜ ≤ ENNReal.ofReal (3 / 4 : Real) := by
    rw [prob_compl_eq_one_sub hA]
    calc
      1 - nu A ≤ 1 - ENNReal.ofReal (1 / 4 : Real) :=
        tsub_le_tsub_left hquarter 1
      _ = ENNReal.ofReal (3 / 4 : Real) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by norm_num)]
        norm_num
  have hreal : (3 / 4 : Real) ^ quarterAcceptanceCutoff b ≤ b := by
    have h := Arlib.MarkovChains.mul_pow_le_of_mixingTime_le
      (M := (1 : Real)) (c := 1 / 4) (eps := b)
      (by norm_num) (by norm_num) (by norm_num) hb (t := quarterAcceptanceCutoff b) le_rfl
    simpa only [one_mul, show (1 - 1 / 4 : Real) = 3 / 4 by norm_num] using h
  calc
    nu Aᶜ ^ quarterAcceptanceCutoff b ≤
        (ENNReal.ofReal (3 / 4 : Real)) ^ quarterAcceptanceCutoff b := by gcongr
    _ = ENNReal.ofReal ((3 / 4 : Real) ^ quarterAcceptanceCutoff b) := by
      rw [ENNReal.ofReal_pow (by norm_num : (0 : Real) ≤ 3 / 4)]
    _ ≤ ENNReal.ofReal b := ENNReal.ofReal_le_ofReal hreal

/-- The cutoff grows only logarithmically in the requested rejection-tail budget. -/
theorem quarterAcceptanceCutoff_le {b : Real} (hb : 0 < b) (hb1 : b ≤ 1) :
    (quarterAcceptanceCutoff b : Real) ≤ 4 * Real.log (1 / b) + 1 := by
  have h := Arlib.MarkovChains.mixingTime_le
    (M := (1 : Real)) (c := 1 / 4) (eps := b) (by norm_num) hb hb1
  change (Arlib.MarkovChains.mixingTime 1 (1 / 4) b : Real) ≤ _
  calc
    (Arlib.MarkovChains.mixingTime 1 (1 / 4) b : Real) ≤
        Real.log (1 / b) / (1 / 4) + 1 := h
    _ = 4 * Real.log (1 / b) + 1 := by ring

/-- Adaptive rejection with phase-dependent transition errors.  After `T` retained-history
transitions, postprocess by the same `firstAcceptedCutoff` used for iid rejection.  The
total error is the initial-history error, the sum of conditional transition errors, and
the ideal geometric rejection tail. -/
theorem tvLe_adaptive_firstAcceptedCutoff_condOn
    (P Q : Nat → Kernel H H) [∀ t, IsMarkovKernel (P t)] [∀ t, IsMarkovKernel (Q t)]
    {mu muIdeal : Measure H} [IsProbabilityMeasure mu] [IsProbabilityMeasure muIdeal]
    (read : H → RoundSpace E) (hread : Measurable read)
    (nu : Measure E) [IsProbabilityMeasure nu]
    {A : Set E} (hA : MeasurableSet A) (hApos : 0 < nu A)
    (T : Nat) (fallback : E)
    {d : ENNReal} (e : Nat → ENNReal)
    (hstart : TVLe mu muIdeal d)
    (hstep : ∀ i h, TVLe (P i h) (Q i h) (e i))
    (hideal :
      (Arlib.adaptiveMarginal Q muIdeal T).map
          (firstAcceptedCutoff A T fallback ∘ read) =
        (roundsMeasure nu).map (firstAcceptedCutoff A T fallback)) :
    TVLe
      ((Arlib.adaptiveMarginal P mu T).map
        (firstAcceptedCutoff A T fallback ∘ read))
      (Arlib.condOn nu A)
      ((d + ∑ i ∈ Finset.range T, e i) + nu Aᶜ ^ T) := by
  have hout : Measurable (firstAcceptedCutoff A T fallback ∘ read) :=
    (measurable_firstAcceptedCutoff hA T fallback).comp hread
  apply TVLe.map_adaptiveMarginal_to_target P Q _ hout e hstart hstep T
  rw [hideal]
  exact tvLe_firstAcceptedCutoff_condOn nu hA hApos T fallback

/-- Uniform-error specialization: `T` adaptive retries cost `T * e` in TV, plus the iid
geometric tail. -/
theorem tvLe_adaptive_firstAcceptedCutoff_condOn_const
    (P Q : Nat → Kernel H H) [∀ t, IsMarkovKernel (P t)] [∀ t, IsMarkovKernel (Q t)]
    {mu muIdeal : Measure H} [IsProbabilityMeasure mu] [IsProbabilityMeasure muIdeal]
    (read : H → RoundSpace E) (hread : Measurable read)
    (nu : Measure E) [IsProbabilityMeasure nu]
    {A : Set E} (hA : MeasurableSet A) (hApos : 0 < nu A)
    (T : Nat) (fallback : E) {d e : ENNReal}
    (hstart : TVLe mu muIdeal d)
    (hstep : ∀ i h, TVLe (P i h) (Q i h) e)
    (hideal :
      (Arlib.adaptiveMarginal Q muIdeal T).map
          (firstAcceptedCutoff A T fallback ∘ read) =
        (roundsMeasure nu).map (firstAcceptedCutoff A T fallback)) :
    TVLe
      ((Arlib.adaptiveMarginal P mu T).map
        (firstAcceptedCutoff A T fallback ∘ read))
      (Arlib.condOn nu A) ((d + T * e) + nu Aᶜ ^ T) := by
  have hout : Measurable (firstAcceptedCutoff A T fallback ∘ read) :=
    (measurable_firstAcceptedCutoff hA T fallback).comp hread
  apply TVLe.map_adaptiveMarginal_const_to_target P Q _ hout hstart hstep T
  rw [hideal]
  exact tvLe_firstAcceptedCutoff_condOn nu hA hApos T fallback

/-! ## LV2 dependence from bounded adaptive rejection -/

/-- A bounded, history-dependent rejection implementation implies the LV2
`lem:delta-ind` coefficient once every large outer-history event exposes its conditional
execution.

Unlike `FreshRegenerationResource`, the actual retry kernels `P S i` need not be iid and
may depend on their full internal state.  Only their pointwise distance to the ideal fresh
kernel is charged.  Thus the conclusion remains valid for sequential retries, provided
the caller proves the ordinary conditional-law factorization `hfactor` and the per-retry
mixing estimate `hstep`.

The factor two is the source LV2 argument: one error compares a large-event conditional
law to the target and the other compares the unconditional next marginal to it. -/
theorem nuIndep_of_largeEvent_adaptiveRejection
    {Omega Outer : Type*} [MeasurableSpace Omega] [MeasurableSpace Outer]
    {rho : Measure Omega} [IsProbabilityMeasure rho]
    {outer : Omega → Outer} {next : Omega → E}
    (houter : Measurable outer) (hnext : Measurable next)
    (P Q : Set Outer → Nat → Kernel H H)
    [∀ S i, IsMarkovKernel (P S i)] [∀ S i, IsMarkovKernel (Q S i)]
    (start idealStart : Set Outer → Measure H)
    [∀ S, IsProbabilityMeasure (start S)]
    [∀ S, IsProbabilityMeasure (idealStart S)]
    (read : H → RoundSpace E) (hread : Measurable read)
    (nu : Measure E) [IsProbabilityMeasure nu]
    {Accept : Set E} (hAccept : MeasurableSet Accept) (hAcceptPos : 0 < nu Accept)
    (rounds : Nat) (fallback : E) (eps : ENNReal) (heps : eps ≠ ⊤)
    (d stepErr : Set Outer → ENNReal)
    (hstart : ∀ S, TVLe (start S) (idealStart S) (d S))
    (hstep : ∀ S i h, TVLe (P S i h) (Q S i h) (stepErr S))
    (hideal : ∀ S,
      (Arlib.adaptiveMarginal (Q S) (idealStart S) rounds).map
          (firstAcceptedCutoff Accept rounds fallback ∘ read) =
        (roundsMeasure nu).map (firstAcceptedCutoff Accept rounds fallback))
    (hbudget : ∀ S, (d S + rounds * stepErr S) + nu Acceptᶜ ^ rounds ≤ eps)
    (hfactor : ∀ S T, MeasurableSet S → MeasurableSet T →
      1 / 2 ≤ rho.real (outer ⁻¹' S) →
      rho.real (outer ⁻¹' S ∩ next ⁻¹' T) =
        rho.real (outer ⁻¹' S) *
          (((Arlib.adaptiveMarginal (P S) (start S) rounds).map
            (firstAcceptedCutoff Accept rounds fallback ∘ read)).real T)) :
    NuIndep rho outer next (2 * eps.toReal) := by
  letI : IsProbabilityMeasure (Arlib.condOn nu Accept) :=
    Arlib.isProbabilityMeasure_condOn nu hAcceptPos.ne' (measure_ne_top nu Accept)
  apply Ttc.CVSequentialDependence.nuIndep_of_largeEvent_conditionedSampler
    (μ := rho) (τ := Arlib.condOn nu Accept)
    (H := outer) (Y := next) houter hnext
    (fun S => (Arlib.adaptiveMarginal (P S) (start S) rounds).map
      (firstAcceptedCutoff Accept rounds fallback ∘ read)) heps
  · intro S hS hlarge
    exact Measure.isProbabilityMeasure_map
      ((measurable_firstAcceptedCutoff hAccept rounds fallback).comp hread).aemeasurable
  · exact hfactor
  · intro S hS hlarge
    exact (tvLe_adaptive_firstAcceptedCutoff_condOn_const
      (P S) (Q S) read hread nu hAccept hAcceptPos rounds fallback
      (hstart S) (hstep S) (hideal S)).mono (hbudget S)

/-- The adaptive-rejection dependence theorem supplies both dependence fields of the
corrected `lem:accuracy`, including the squared statistics.  This wrapper is independent
of the Gaussian implementation; phase-specific uses feed
`nuIndep_of_largeEvent_adaptiveRejection` into `hdep`. -/
theorem correctedAccuracy_dependencePremises_of_adaptiveRejection
    {Omega Hist State : Type*} [MeasurableSpace Omega] [MeasurableSpace Hist]
    [MeasurableSpace State]
    {rho : Measure Omega} [IsProbabilityMeasure rho]
    (V : Nat → Omega → Real) {m : Nat} {eta : Real}
    (H : Nat → Omega → Hist) (Y : Nat → Omega → State)
    (u : Nat → Hist → Real) (v : Nat → State → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i,
      accuracyU rho V (Ttc.CVCorrected.correctedAlpha m eta) i =
        fun omega => u i (H i omega))
    (hV : ∀ i, V (i + 1) = fun omega => v i (Y i omega))
    (phaseNu : Nat → Real)
    (hbudget : ∀ i, phaseNu i ≤ Ttc.CVCorrected.correctedNu m eta)
    (hdep : ∀ i, NuIndep rho (H i) (Y i) (phaseNu i)) :
    (∀ i, NuIndep rho
      (accuracyU rho V (Ttc.CVCorrected.correctedAlpha m eta) i) (V (i + 1))
      (Ttc.CVCorrected.correctedNu m eta)) ∧
    (∀ i, NuIndep rho
      (fun omega =>
        (accuracyU rho V (Ttc.CVCorrected.correctedAlpha m eta) i omega) ^ 2)
      (fun omega => (V (i + 1) omega) ^ 2)
      (Ttc.CVCorrected.correctedNu m eta)) := by
  constructor
  · intro i
    rw [hU i, hV i]
    exact (hdep i).comp (hu i) (hv i) |>.mono (hbudget i)
  · intro i
    rw [hU i, hV i]
    have hstats := (hdep i).comp (hu i) (hv i)
    have hsq : Measurable (fun x : Real => x ^ 2) := measurable_id.pow_const 2
    exact (hstats.comp hsq hsq).mono (hbudget i)

#print axioms tvLe_adaptive_firstAcceptedCutoff_condOn
#print axioms tvLe_adaptive_firstAcceptedCutoff_condOn_const
#print axioms nuIndep_of_largeEvent_adaptiveRejection
#print axioms correctedAccuracy_dependencePremises_of_adaptiveRejection
#print axioms compl_pow_quarterAcceptanceCutoff_le
#print axioms quarterAcceptanceCutoff_le

end Ttc.CV
