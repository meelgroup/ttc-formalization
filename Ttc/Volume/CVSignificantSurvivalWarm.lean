/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVSequentialPhaseSampler

/-!
# Warm starts after a significant survival event

For a continuing rejection phase, retry `j` starts from the preceding history conditioned
on survival through retry `j - 1`.  If that survival event has probability at least `eta`,
conditioning inflates an `M`-warm law by only `eta⁻¹`.  This file records that statement
at the law and history-last levels and packages the resulting distributional mixing call.

The result does not claim that survival remains significant for arbitrarily many retries.
A finite retry construction must either prove the displayed lower bound at every retry or
cut off when it fails.
-/

namespace Ttc.CVSignificantSurvivalWarm

open MeasureTheory ProbabilityTheory
open Arlib Arlib.Probability Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler
open scoped ENNReal

/-- Conditioning on an event of mass at least `eta` changes `M`-warmth to `M / eta`.
This is the arbitrary-mass version of
`CVSequentialDependence.isWarm_condOn_of_half`. -/
theorem isWarm_condOn_of_mass
    {E : Type*} [MeasurableSpace E] {mu pi : Measure E} {M eta : ENNReal}
    (hwarm : IsWarm M mu pi) {S : Set E} (hS : MeasurableSet S)
    (hmass : eta ≤ mu S) :
    IsWarm (M / eta) (condOn mu S) pi := by
  have hcond := Arlib.GaussianCooling.isWarm_condOn hwarm hS
  exact hcond.mono (by
    rw [div_eq_mul_inv]
    exact mul_le_mul_left' (ENNReal.inv_le_inv.2 hmass) M)

/-- Conditioning a history event and retaining its last state has the same `eta⁻¹`
warmness inflation. -/
theorem isWarm_map_condOn_of_mass
    {H E : Type*} [MeasurableSpace H] [MeasurableSpace E]
    {rho : Measure H} {pi : Measure E} {last : H → E}
    (hlast : Measurable last) {M eta : ENNReal}
    (hwarm : IsWarm M (rho.map last) pi)
    {S : Set H} (hS : MeasurableSet S) (hmass : eta ≤ rho S) :
    IsWarm (M / eta) ((condOn rho S).map last) pi := by
  have hself : IsWarm (1 / eta) (condOn rho S) rho :=
    isWarm_condOn_of_mass (IsWarm.refl rho) hS hmass
  have hmap := (Ttc.CVSequentialPhaseSampler.isWarm_map hself hlast).trans hwarm
  simpa only [one_div, one_mul, mul_one, div_eq_mul_inv, mul_comm] using hmap

/-- A real-probability lower bound can be fed directly to the `ENNReal` theorem. -/
theorem isWarm_map_condOn_of_real_mass
    {H E : Type*} [MeasurableSpace H] [MeasurableSpace E]
    {rho : Measure H} [IsProbabilityMeasure rho]
    {pi : Measure E} {last : H → E} (hlast : Measurable last)
    {M : ENNReal} (hwarm : IsWarm M (rho.map last) pi)
    {S : Set H} (hS : MeasurableSet S) {eta : Real} (heta0 : 0 ≤ eta)
    (hmass : eta ≤ rho.real S) :
    IsWarm (M / ENNReal.ofReal eta) ((condOn rho S).map last) pi := by
  apply isWarm_map_condOn_of_mass hlast hwarm hS
  have htop : rho S ≠ ⊤ := measure_ne_top rho S
  apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top htop).mp
  simpa [Measure.real, ENNReal.toReal_ofReal heta0] using hmass

/-- Per-retry distributional mixing from a significant survival event.

The deadline may depend on `M / eta`; the theorem merely wires the exact conditioned
history start into that sampler specification.  This is the form needed for a finite
continuing-rejection phase. -/
theorem tvLe_sampleFromKernel_map_condOn_of_mass
    {H E F : Type*} [MeasurableSpace H] [MeasurableSpace E] [MeasurableSpace F]
    {rho : Measure H} [IsProbabilityMeasure rho]
    {pi : Measure E} {tau : Measure F} [IsProbabilityMeasure tau]
    (Q : Kernel E F) [IsMarkovKernel Q]
    {last : H → E} (hlast : Measurable last)
    {M eta eps : ENNReal} (heta0 : eta ≠ 0)
    (hwarm : IsWarm M (rho.map last) pi)
    {S : Set H} (hS : MeasurableSet S) (hmass : eta ≤ rho S)
    (hmix : ∀ nu : Measure E,
      IsWarm (M / eta) nu pi → IsProbabilityMeasure nu →
        TVLe (sampleFromKernel Q nu) tau eps) :
    TVLe (sampleFromKernel Q ((condOn rho S).map last)) tau eps := by
  have hS0 : rho S ≠ 0 := by
    intro hzero
    have : eta = 0 := le_antisymm (by simpa [hzero] using hmass) bot_le
    exact heta0 this
  letI : IsProbabilityMeasure (condOn rho S) :=
    Arlib.isProbabilityMeasure_condOn rho hS0 (measure_ne_top rho S)
  letI : IsProbabilityMeasure ((condOn rho S).map last) :=
    Measure.isProbabilityMeasure_map hlast.aemeasurable
  exact hmix _ (isWarm_map_condOn_of_mass hlast hwarm hS hmass) inferInstance

/-- Deadline-indexed version of the preceding retry theorem. -/
theorem tvLe_retry_at_distributionalWarmDeadline
    {H E F : Type*} [MeasurableSpace H] [MeasurableSpace E] [MeasurableSpace F]
    {rho : Measure H} [IsProbabilityMeasure rho]
    {pi : Measure E} {tau : Measure F} [IsProbabilityMeasure tau]
    (phase : Nat → Kernel E F) [∀ t, IsMarkovKernel (phase t)]
    (deadline : ENNReal → Nat)
    {last : H → E} (hlast : Measurable last)
    {M eta eps : ENNReal} (heta0 : eta ≠ 0)
    (hwarm : IsWarm M (rho.map last) pi)
    {S : Set H} (hS : MeasurableSet S) (hmass : eta ≤ rho S)
    (hmix : ∀ nu : Measure E,
      IsWarm (M / eta) nu pi → IsProbabilityMeasure nu →
        TVLe (sampleFromKernel (phase (deadline (M / eta))) nu) tau eps) :
    TVLe
      (sampleFromKernel (phase (deadline (M / eta))) ((condOn rho S).map last))
      tau eps :=
  tvLe_sampleFromKernel_map_condOn_of_mass
    (phase (deadline (M / eta))) hlast heta0 hwarm hS hmass hmix

#print axioms isWarm_condOn_of_mass
#print axioms isWarm_map_condOn_of_mass
#print axioms isWarm_map_condOn_of_real_mass
#print axioms tvLe_sampleFromKernel_map_condOn_of_mass
#print axioms tvLe_retry_at_distributionalWarmDeadline

end Ttc.CVSignificantSurvivalWarm
