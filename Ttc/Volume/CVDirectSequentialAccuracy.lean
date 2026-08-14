/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVDirectMetropolisPhase
import Ttc.Volume.CVCorrectedParameters

/-!
# Corrected accuracy from a stateful direct-Metropolis phase trajectory

The source volume algorithm is stateful: the endpoint of one phase is the start of the
next.  For an honest Markov phase kernel, conditioning the realized history and restarting
from its last-state distribution is an exact kernel identity.  This file packages that
identity with distributional warm-start mixing and discharges both dependence hypotheses
of the corrected `lem:accuracy`.

Unlike the fresh-restart implementation, this interface does not assume access to a fresh
draw from the entire previous-phase law.  Unlike the speedy rejection implementation, one
ordinary Metropolis proposal is already one recorded membership query.  The remaining
analytic input is a polynomial deterministic-time mixing theorem for every `2*M`-warm
start; the warm LS branch is designed to provide exactly that theorem.
-/

namespace Ttc.CVDirectSequentialAccuracy

open MeasureTheory ProbabilityTheory
open Arlib Arlib.Probability Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler Ttc.CVCorrected
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E]

/-- Operational data sufficient to turn distributional warm mixing of each honest phase
kernel into the two `NuIndep` premises used by corrected `lem:accuracy`.

`V (i+1)` is a statistic of the new phase state, while `accuracyU ... i` is a statistic of
the history through phase `i`.  Their displayed factorizations are precisely what licenses
postcomposition of the history/next-state dependence theorem. -/
structure DirectSequentialOperational
    (P : Nat → Kernel E E) [∀ i, IsMarkovKernel (P i)]
    (mu0 : Measure E) [IsProbabilityMeasure mu0]
    (V : Nat → (Nat → E) → Real) (m : Nat) (eta : Real) where
  pi : Nat → Measure E
  tau : Nat → Measure E
  pi_prob : ∀ i, IsProbabilityMeasure (pi i)
  tau_prob : ∀ i, IsProbabilityMeasure (tau i)
  warmConst : Nat → ENNReal
  mixError : Nat → ENNReal
  mixError_ne_top : ∀ i, mixError i ≠ ⊤
  u : (i : Nat) → (Finset.Iic i → E) → Real
  v : Nat → E → Real
  measurable_u : ∀ i, Measurable (u i)
  measurable_v : ∀ i, Measurable (v i)
  U_eq : ∀ i,
    accuracyU (inhomogeneousPathMeasure P mu0) V (correctedAlpha m eta) i =
      fun omega ↦ u i (Preorder.frestrictLe i omega)
  V_eq : ∀ i, V (i + 1) = fun omega ↦ v i (omega (i + 1))
  last_warm : ∀ i,
    IsWarm (warmConst i)
      (((inhomogeneousPathMeasure P mu0).map (Preorder.frestrictLe i)).map
        (fun h ↦ h ⟨i, Finset.mem_Iic.2 le_rfl⟩)) (pi i)
  distributional_mixing : ∀ i (rho : Measure E),
    IsWarm (2 * warmConst i) rho (pi i) → IsProbabilityMeasure rho →
      TVLe (sampleFromKernel (P i) rho) (tau i) (mixError i)
  dependence_budget : ∀ i,
    2 * (mixError i).toReal ≤ correctedNu m eta

attribute [instance] DirectSequentialOperational.pi_prob
attribute [instance] DirectSequentialOperational.tau_prob

/-- Markov restart plus distributional warm mixing automatically supplies both the ordinary
and squared dependence premises of corrected `lem:accuracy`. -/
theorem DirectSequentialOperational.correctedDependencePremises
    {P : Nat → Kernel E E} [∀ i, IsMarkovKernel (P i)]
    {mu0 : Measure E} [IsProbabilityMeasure mu0]
    {V : Nat → (Nat → E) → Real} {m : Nat} {eta : Real}
    (hop : DirectSequentialOperational P mu0 V m eta) :
    (∀ i, NuIndep (inhomogeneousPathMeasure P mu0)
      (accuracyU (inhomogeneousPathMeasure P mu0) V (correctedAlpha m eta) i)
      (V (i + 1)) (correctedNu m eta)) ∧
    (∀ i, NuIndep (inhomogeneousPathMeasure P mu0)
      (fun omega ↦
        (accuracyU (inhomogeneousPathMeasure P mu0) V
          (correctedAlpha m eta) i omega) ^ 2)
      (fun omega ↦ (V (i + 1) omega) ^ 2) (correctedNu m eta)) := by
  constructor
  · intro i
    letI : IsProbabilityMeasure (hop.pi i) := hop.pi_prob i
    letI : IsProbabilityMeasure (hop.tau i) := hop.tau_prob i
    have hdep := nuIndep_historyStatistics_inhomogeneous_of_distributionalWarm
      P mu0 i (hop.last_warm i) (hop.mixError_ne_top i)
      (hop.distributional_mixing i) (hop.u i) (hop.v i)
      (hop.measurable_u i) (hop.measurable_v i)
    rw [← hop.U_eq i, ← hop.V_eq i] at hdep
    exact hdep.mono (hop.dependence_budget i)
  · intro i
    letI : IsProbabilityMeasure (hop.pi i) := hop.pi_prob i
    letI : IsProbabilityMeasure (hop.tau i) := hop.tau_prob i
    have hdep := nuIndep_historyStatistics_inhomogeneous_of_distributionalWarm
      P mu0 i (hop.last_warm i) (hop.mixError_ne_top i)
      (hop.distributional_mixing i) (hop.u i) (hop.v i)
      (hop.measurable_u i) (hop.measurable_v i)
    rw [← hop.U_eq i, ← hop.V_eq i] at hdep
    exact (hdep.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)).mono
      (hop.dependence_budget i)

/-- Corrected one-run accuracy for a stateful inhomogeneous Markov execution.  All generic
moment/truncation hypotheses are exactly those of `corrected_lem_accuracy_concrete`; the
two dependence binders have been replaced by one operational Markov/mixing package. -/
theorem corrected_lem_accuracy_concrete_of_directSequential
    {P : Nat → Kernel E E} [∀ i, IsMarkovKernel (P i)]
    {mu0 : Measure E} [IsProbabilityMeasure mu0]
    (V Wbar W : Nat → (Nat → E) → Real) {m k : Nat} {eta : Real}
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hk : CorrectedSampleBudget m k eta)
    (hVm : ∀ j, Measurable (V j)) (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hEpos : ∀ j, 0 < ∫ omega, V j omega ∂(inhomogeneousPathMeasure P mu0))
    (hVcap : ∀ j omega, V j omega ≤ 2 * correctedAlpha m eta *
      ∫ z, V j z ∂(inhomogeneousPathMeasure P mu0))
    (hV2 : ∀ j, Integrable (fun omega ↦ (V j omega) ^ 2)
      (inhomogeneousPathMeasure P mu0))
    (hV2cap : ∀ j omega, (V j omega) ^ 2 ≤ 2 * correctedAlpha m eta ^ 2 *
      ∫ z, (V j z) ^ 2 ∂(inhomogeneousPathMeasure P mu0))
    (hWm : ∀ j, Measurable (Wbar j)) (hW0 : ∀ j omega, 0 ≤ Wbar j omega)
    (hWint : ∀ j, Integrable (Wbar j) (inhomogeneousPathMeasure P mu0))
    (hWEpos : ∀ j, 0 < ∫ omega, Wbar j omega ∂(inhomogeneousPathMeasure P mu0))
    (hVdef : ∀ j omega, V j omega = min (Wbar j omega)
      (correctedAlpha m eta *
        ∫ z, Wbar j z ∂(inhomogeneousPathMeasure P mu0)))
    (hratio : ∀ j,
      (∫ omega, (V j omega) ^ 2 ∂(inhomogeneousPathMeasure P mu0)) ≤
        (1 + 8 / (k : Real)) *
          (∫ omega, V j omega ∂(inhomogeneousPathMeasure P mu0)) ^ 2)
    {Eexact : Set (Nat → E)} (hEexact : MeasurableSet Eexact)
    (hExactFail : (inhomogeneousPathMeasure P mu0).real Eexactᶜ ≤ 1 / 20)
    (hExact : ∀ omega ∈ Eexact, phaseProduct Wbar m omega = phaseProduct W m omega)
    (hop : DirectSequentialOperational P mu0 V m eta) :
    (inhomogeneousPathMeasure P mu0).real
      {omega | phaseProduct W m omega ∉
        relErr eta (prefixMean (inhomogeneousPathMeasure P mu0) V m)} ≤ 1 / 5 := by
  have hdeps := hop.correctedDependencePremises
  exact corrected_lem_accuracy_concrete V Wbar W heta heta1 hk hVm hV0 hEpos hVcap
    hV2 hV2cap hdeps.1 hdeps.2 hWm hW0 hWint hWEpos hVdef hratio
    hEexact hExactFail hExact

end Ttc.CVDirectSequentialAccuracy

#print axioms Ttc.CVDirectSequentialAccuracy.DirectSequentialOperational.correctedDependencePremises
#print axioms Ttc.CVDirectSequentialAccuracy.corrected_lem_accuracy_concrete_of_directSequential
