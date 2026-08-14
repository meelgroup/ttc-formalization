import Ttc.Exec.CVSourceSampleCountAudit

/-!
# Corrected dependent accuracy with phase-dependent moment factors

This file removes `CorrectedSampleBudget` from the corrected dependence argument.
The replacement hypothesis is exactly the source-sharp one: every prefix product of
the actual phase factors is small.  Thus the dependence recursion itself does not force
the uniform `(1 + 8/k)^m` relaxation.
-/

set_option autoImplicit false

namespace Ttc.CVWeightedCorrectedAccuracy

open MeasureTheory Set ProbabilityTheory Arlib.GaussianCooling
open Ttc.CVCorrected Ttc.CVSourceSampleCountAudit

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- The corrected scalar bundle needs only a source-sharp prefix-product estimate.
No sample-count condition involving the total phase count occurs. -/
theorem weighted_corrected_parameter_bundle [IsProbabilityMeasure mu]
    (V : Nat -> Omega -> Real) (factor : Nat -> Real)
    {m : Nat} {eps : Real}
    (heps : 0 < eps) (heps1 : eps <= 1)
    (hV0 : forall j omega, 0 <= V j omega)
    (hfactor0 : forall j, 0 <= factor j)
    (hratio : forall j,
      (∫ omega, (V j omega) ^ 2 ∂mu) <=
        factor j * (∫ omega, V j omega ∂mu) ^ 2)
    (hprefix : forall i, i <= m ->
      prefixMomentRatio factor i <= 1 + eps ^ 2 / 6250) :
    let alpha := correctedAlpha m eps
    let nu := correctedNu m eps
    let q := correctedQ eps
    let epsc := correctedInnerAccuracy eps
    let eta := correctedMeanAccuracy eps
    (1 <= alpha) /\
    AccuracyLowerScalar mu V alpha nu m /\
    (forall i, i < m ->
      1 + 2 * nu * alpha ^ 2 * ((i + 1 : Nat) : Real) <= 2) /\
    (0 < 1 - (m : Real) / alpha) /\
    ((m : Real) / alpha <= eta) /\
    (2 * nu * alpha ^ 2 * (m : Real) <= eta) /\
    (epsc + eta + epsc * eta <= eps) /\
    ((1 + 2 * nu * alpha ^ 4 * (m : Real)) * prefixSecondMean mu V m <=
      q * (1 - (m : Real) / alpha) ^ 2 * (prefixMean mu V m) ^ 2) /\
    ((q - 1) / epsc ^ 2 + 3 * (m : Real) / alpha + 1 / 20 <= 1 / 5) := by
  dsimp
  have halpha1 := one_le_correctedAlpha (m := m) heps heps1
  have halpha0 := correctedAlpha_pos (m := m) heps
  have htrunc := phase_div_correctedAlpha_le (m := m) heps
  have heps2le : eps ^ 2 <= 1 := by nlinarith [sq_nonneg eps]
  have hcoeffPrefix : forall i, i <= m ->
      (1 + 2 * correctedNu m eps * correctedAlpha m eps ^ 4 * (i : Real)) *
          prefixMomentRatio factor i <= 2 := by
    intro i hi
    have hdepend := correctedNu_alpha_four_mul_le (m := m) (r := i) heps
      (hi.trans (Nat.le_succ m))
    calc
      (1 + 2 * correctedNu m eps * correctedAlpha m eps ^ 4 * (i : Real)) *
          prefixMomentRatio factor i <=
        (1 + eps ^ 2 / 50000) * (1 + eps ^ 2 / 6250) := by
          exact mul_le_mul (by linarith) (hprefix i hi)
            (Finset.prod_nonneg fun j _ => hfactor0 (j + 1)) (by positivity)
      _ <= 2 := by nlinarith [sq_nonneg (eps ^ 2)]
  have hfinalCoeff :
      (1 + 2 * correctedNu m eps * correctedAlpha m eps ^ 4 * (m : Real)) *
          prefixMomentRatio factor m <=
        correctedQ eps * (1 - (m : Real) / correctedAlpha m eps) ^ 2 := by
    have hdepend := correctedNu_alpha_four_mul_le (m := m) (r := m) heps
      (Nat.le_succ m)
    have hleft :
        (1 + 2 * correctedNu m eps * correctedAlpha m eps ^ 4 * (m : Real)) *
            prefixMomentRatio factor m <=
          (1 + eps ^ 2 / 50000) * (1 + eps ^ 2 / 6250) := by
      exact mul_le_mul (by linarith) (hprefix m le_rfl)
        (Finset.prod_nonneg fun j _ => hfactor0 (j + 1)) (by positivity)
    have htrunc0 : 0 <= (m : Real) / correctedAlpha m eps := by positivity
    have hsquare :
        (1 - eps ^ 2 / 100000) ^ 2 <=
          (1 - (m : Real) / correctedAlpha m eps) ^ 2 := by
      apply (sq_le_sq₀ (by nlinarith) (by nlinarith)).2
      nlinarith
    have hnum :
        (1 + eps ^ 2 / 50000) * (1 + eps ^ 2 / 6250) <=
          (1 + eps ^ 2 / 1000) * (1 - eps ^ 2 / 100000) ^ 2 := by
      nlinarith [sq_nonneg (eps ^ 2),
        mul_nonneg (sq_nonneg eps) (sub_nonneg.mpr heps2le)]
    unfold correctedQ
    exact hleft.trans (hnum.trans
      (mul_le_mul_of_nonneg_left hsquare (by positivity)))
  rcases weighted_phaseFactors_discharge_recursion_scalars V factor
      (correctedNu_nonneg (m := m) (ε := eps)) hV0 hfactor0 hratio
      (corrected_covariance_scalar heps heps1) hcoeffPrefix hfinalCoeff with
    ⟨haccuracy, hsecond⟩
  refine ⟨halpha1, haccuracy, ?_, ?_, ?_, ?_, ?_, hsecond, ?_⟩
  · intro i hi
    have hi' : i + 1 <= m := Nat.succ_le_iff.mpr hi
    have hfour := correctedNu_alpha_four_mul_le (m := m) (r := i + 1) heps
      (hi'.trans (Nat.le_succ m))
    have halpha2 : 1 <= correctedAlpha m eps ^ 2 := one_le_pow₀ halpha1
    nlinarith [correctedNu_nonneg (m := m) (ε := eps)]
  · nlinarith
  · unfold correctedMeanAccuracy
    have heps2eps : eps ^ 2 <= eps := by nlinarith [sq_nonneg eps]
    nlinarith
  · exact corrected_mean_dependence_le heps heps1
  · unfold correctedInnerAccuracy correctedMeanAccuracy
    nlinarith [sq_nonneg eps]
  · unfold correctedQ correctedInnerAccuracy
    have ht : 3 * (m : Real) / correctedAlpha m eps <=
        3 * eps ^ 2 / 100000 := by
      calc
        3 * (m : Real) / correctedAlpha m eps =
            3 * ((m : Real) / correctedAlpha m eps) := by ring
        _ <= 3 * (eps ^ 2 / 100000) :=
          mul_le_mul_of_nonneg_left htrunc (by norm_num)
        _ = 3 * eps ^ 2 / 100000 := by ring
    rw [show ((1 + eps ^ 2 / 1000) - 1) / (eps / 4) ^ 2 = 2 / 125 by
      field_simp [ne_of_gt heps]
      ring]
    nlinarith

/-- Plug-in corrected dependent accuracy theorem with a nonuniform phase-factor budget.
This is the direct source-sharp replacement for `corrected_lem_accuracy_concrete`. -/
theorem corrected_lem_accuracy_weighted [IsProbabilityMeasure mu]
    (V Wbar W : Nat -> Omega -> Real) (factor : Nat -> Real)
    {m : Nat} {eps : Real}
    (heps : 0 < eps) (heps1 : eps <= 1)
    (hVm : forall j, Measurable (V j)) (hV0 : forall j omega, 0 <= V j omega)
    (hEpos : forall j, 0 < ∫ omega, V j omega ∂mu)
    (hVcap : forall j omega, V j omega <=
      2 * correctedAlpha m eps * ∫ z, V j z ∂mu)
    (hV2 : forall j, Integrable (fun omega => (V j omega) ^ 2) mu)
    (hV2cap : forall j omega, (V j omega) ^ 2 <=
      2 * correctedAlpha m eps ^ 2 * ∫ z, (V j z) ^ 2 ∂mu)
    (hindep : forall i, NuIndep mu
      (accuracyU mu V (correctedAlpha m eps) i) (V (i + 1))
      (correctedNu m eps))
    (hindepSq : forall i, NuIndep mu
      (fun omega => (accuracyU mu V (correctedAlpha m eps) i omega) ^ 2)
      (fun omega => (V (i + 1) omega) ^ 2) (correctedNu m eps))
    (hWm : forall j, Measurable (Wbar j)) (hW0 : forall j omega, 0 <= Wbar j omega)
    (hWint : forall j, Integrable (Wbar j) mu)
    (hWEpos : forall j, 0 < ∫ omega, Wbar j omega ∂mu)
    (hVdef : forall j omega, V j omega = min (Wbar j omega)
      (correctedAlpha m eps * ∫ z, Wbar j z ∂mu))
    (hfactor0 : forall j, 0 <= factor j)
    (hratio : forall j, (∫ omega, (V j omega) ^ 2 ∂mu) <=
      factor j * (∫ omega, V j omega ∂mu) ^ 2)
    (hprefix : forall i, i <= m ->
      prefixMomentRatio factor i <= 1 + eps ^ 2 / 6250)
    {Eexact : Set Omega} (hEexact : MeasurableSet Eexact)
    (hExactFail : mu.real Eexact.compl <= 1 / 20)
    (hExact : forall omega, omega ∈ Eexact ->
      phaseProduct Wbar m omega = phaseProduct W m omega) :
    mu.real {omega | phaseProduct W m omega ∉ relErr eps (prefixMean mu V m)} <=
      1 / 5 := by
  rcases weighted_corrected_parameter_bundle V factor heps heps1 hV0 hfactor0
      hratio hprefix with
    ⟨halpha, hscalar, hcoef, hmeanPos, hmeanLo, hmeanHi, hcompose, hsecond,
      hbudget⟩
  have hq : 0 <= correctedQ eps := by unfold correctedQ; positivity
  have hepsc : 0 < correctedInnerAccuracy eps := by
    unfold correctedInnerAccuracy
    positivity
  have heta : 0 <= correctedMeanAccuracy eps := by
    unfold correctedMeanAccuracy
    positivity
  have hbad := corrected_lem_accuracy_of_recursion V Wbar W
    halpha hq hepsc heta hVm hV0 hEpos hVcap hV2 hV2cap hindep hindepSq
    hWm hW0 hWint hWEpos hVdef hscalar hcoef hmeanPos hsecond hmeanLo hmeanHi
    hcompose hEexact hExactFail hExact
  exact hbad.trans hbudget

#print axioms weighted_corrected_parameter_bundle
#print axioms corrected_lem_accuracy_weighted

end Ttc.CVWeightedCorrectedAccuracy
