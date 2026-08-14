/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVAdaptiveTerminalExact
import Ttc.Volume.CVPackedCouplingAccuracy
import Ttc.Volume.CVEndpointAccuracy

/-!
# Sampler coupling and cold correction for the terminal CV estimator

This is the probability-theoretic join used after the final Gaussian-to-uniform phase.  It
tensorizes coordinatewise sampler TV error and replaces the unknown cold restricted
normalizer by the known ambient Gaussian normalizer.  Since the exact telescope already ends
at `volume K`, no hot-end bias remains.
-/

namespace Ttc.CVAdaptive

open MeasureTheory ProbabilityTheory
open Arlib.GaussianCooling
open scoped ENNReal

/-- Generic coupling/cold-end wrapper for a packed CV estimator whose exact-law target is
already the desired value. -/
theorem packed_terminal_accuracy_of_tv_and_cold
    {r m k : ℕ} {E : Type*} [MeasurableSpace E]
    {ν ν' : Fin r → Fin m → Fin k → Measure E}
    [hν : ∀ t i l, IsProbabilityMeasure (ν t i l)]
    [hν' : ∀ t i l, IsProbabilityMeasure (ν' t i l)]
    {g : Fin r → Fin m → Fin k → E → ℝ}
    (hg : ∀ t i l, Measurable (g t i l))
    (hg0 : ∀ t i l x, 0 ≤ g t i l x) (hk : 0 < k) (hr : 0 < r)
    {A0 Z0 V eps eta p : ℝ} (hA0 : 0 < A0) (hZ0 : 0 < Z0)
    (heps0 : 0 ≤ eps) (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (hA0le : A0 ≤ Z0) (hcold : A0 ∈ Ttc.relErr eta Z0)
    {b : ℝ≥0∞} (hb : b ≠ ⊤) (htv : ∀ t i l, Arlib.TVLe (ν t i l) (ν' t i l) b)
    {ρ : ℝ} (hρ : (((r * m * k : ℕ) : ℝ) * b.toReal) ≤ ρ)
    (hexact : 1 - p ≤ (Arlib.Probability.runMeasure (packedPhaseLaw ν')).real
      {ω | Arlib.Probability.medianSel
        (fun t => A0 * ∏ i, Ttc.CVPacked.phaseAvg g t i ω) ∈ Ttc.relErr eps V}) :
    1 - p - ρ ≤ (Arlib.Probability.runMeasure (packedPhaseLaw ν)).real
      {ω | Arlib.Probability.medianSel
        (fun t => Z0 * ∏ i, Ttc.CVPacked.phaseAvg g t i ω) ∈
          Ttc.relErr ((eps + eta) / (1 - eta)) V} := by
  let X : Fin r → Arlib.Probability.RunSpace (Fin k → E) r m → ℝ :=
    fun t ω => ∏ i, Ttc.CVPacked.phaseAvg g t i ω
  have hmeas : Measurable (fun ω => Arlib.Probability.medianSel
      (fun t => A0 * X t ω)) :=
    Arlib.Probability.measurable_medianSel fun t => measurable_const.mul
      (Finset.measurable_fun_prod _ fun i _ => Ttc.CVPacked.measurable_phaseAvg hg t i)
  have hcoupled : 1 - p - ρ ≤
      (Arlib.Probability.runMeasure (packedPhaseLaw ν)).real
        {ω | Arlib.Probability.medianSel (fun t => A0 * X t ω) ∈ Ttc.relErr eps V} := by
    exact Ttc.CVPacked.measureReal_median_relErr_ge_of_tvLe hb htv hρ hmeas
      (by simpa only [X] using hexact)
  have hX0 : ∀ t ω, 0 ≤ X t ω := by
    intro t ω
    apply Finset.prod_nonneg
    intro i _
    unfold Ttc.CVPacked.phaseAvg Ttc.CVEst.avgOf
    exact div_nonneg (Finset.sum_nonneg fun l _ => hg0 t i l _) (by positivity)
  haveI : IsProbabilityMeasure (Arlib.Probability.runMeasure (packedPhaseLaw ν)) := by
    unfold Arlib.Probability.runMeasure
    infer_instance
  have hend := Ttc.CV.measureReal_median_replace_cold (p := p + ρ) hr hA0 hZ0 hX0
    heps0 heta0 heta1 hA0le hcold (by
      simpa only [sub_add_eq_sub_sub] using hcoupled)
  simpa only [X, sub_add_eq_sub_sub] using hend

#print axioms packed_terminal_accuracy_of_tv_and_cold

end Ttc.CVAdaptive
