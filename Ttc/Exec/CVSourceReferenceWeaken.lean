/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Exec.CVSourceReferenceTVCapstone
import Ttc.Exec.CVRadialLogEnvelope

/-!
# Weakening a source/reference one-run certificate

`SourceReferenceTVOneRunCertificate` is produced by the slow canonical construction at one
set of parameters and consumed at another.  Only two of its seven fields mention those
parameters, and both weaken monotonically:

* `reference_expected_queries` weakens when the query budget grows;
* `accuracy` weakens when the accepted output window grows.

This file records the monotonicity of the source-shaped budget in the runtime constant, in
the radius, and in `1/eps`; the widening of a relative-error window, both under an exact and
under an approximate identification of the terminal chain value with the true volume; and
the resulting certificate-level weakening lemma.
-/

set_option autoImplicit false

namespace Ttc.CVSourceReferenceWeaken

open MeasureTheory Set
open Ttc.CVSourcePolynomialCutoffCapstone
open Ttc.CVRadialLogEnvelope
open Ttc.CVSourceReferenceTVCapstone
open scoped ENNReal

/-! ## Widening a relative-error window -/

/-- A relative-error window around an exactly identified value widens with the relative
error. -/
theorem Icc_relErr_subset
    {epsSmall epsBig vT vol : Real}
    (hle : epsSmall ≤ epsBig) (hvT : 0 ≤ vT) (heq : vT = vol) :
    Icc ((1 - epsSmall) * vT) ((1 + epsSmall) * vT) ⊆
      Icc ((1 - epsBig) * vol) ((1 + epsBig) * vol) := by
  subst heq
  refine Set.Icc_subset_Icc ?_ ?_
  · nlinarith [mul_nonneg (sub_nonneg.mpr hle) hvT]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hle) hvT]

/-- A relative-error window around a value that is itself only known to within a relative
error `theta` of the true volume widens into the window of relative error
`epsSmall + theta + epsSmall * theta`. -/
theorem Icc_relErr_subset_of_approx
    {epsSmall epsBig vT vol theta : Real}
    (hvol : 0 ≤ vol) (heps : 0 ≤ epsSmall) (_htheta : 0 ≤ theta)
    (_htheta1 : theta < 1)
    (happrox : |vT - vol| ≤ theta * vol)
    (hle : epsSmall + theta + epsSmall * theta ≤ epsBig) :
    Icc ((1 - epsSmall) * vT) ((1 + epsSmall) * vT) ⊆
      Icc ((1 - epsBig) * vol) ((1 + epsBig) * vol) := by
  obtain ⟨h₁, h₂⟩ := abs_le.mp happrox
  have hslack : (0 : Real) ≤ epsBig - epsSmall - theta - epsSmall * theta := by linarith
  refine Set.Icc_subset_Icc ?_ ?_
  · nlinarith [mul_le_mul_of_nonneg_left h₁ heps, mul_nonneg hvol hslack]
  · nlinarith [mul_le_mul_of_nonneg_left h₂ heps, mul_nonneg hvol hslack]

/-! ## Monotonicity of the source-shaped one-run budget -/

/-- The source-shaped one-run budget is monotone in the runtime constant. -/
theorem sourceOneRunQueryBudget_mono_constant
    {rc rc' R eps : Real} {n : Nat} (h : rc ≤ rc')
    (hcore : 0 ≤ max (R ^ 2 * (n : Real) ^ 2) ((n : Real) ^ 3) / eps ^ 2 *
      sourceLogFactor n ^ 2 * sourceLogFactor (1 / eps) ^ 2 *
      sourceLogFactor ((n : Real) / eps) ^ 2) :
    sourceOneRunQueryBudget rc n R eps ≤ sourceOneRunQueryBudget rc' n R eps := by
  unfold sourceOneRunQueryBudget sourceOneRunQueryEnvelope
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h hcore)

/-- The source-shaped one-run budget is monotone in the radius. -/
theorem sourceOneRunQueryBudget_mono_radius
    {rc R R' eps : Real} {n : Nat} (hrc : 0 ≤ rc) (hR : 0 ≤ R) (hRR : R ≤ R') :
    sourceOneRunQueryBudget rc n R eps ≤ sourceOneRunQueryBudget rc n R' eps := by
  unfold sourceOneRunQueryBudget sourceOneRunQueryEnvelope
  refine ENNReal.ofReal_le_ofReal ?_
  have hlog : (0 : Real) ≤ sourceLogFactor n := (sourceLogFactor_pos _).le
  have hlog1 : (0 : Real) ≤ sourceLogFactor (1 / eps) := (sourceLogFactor_pos _).le
  have hlog2 : (0 : Real) ≤ sourceLogFactor ((n : Real) / eps) := (sourceLogFactor_pos _).le
  gcongr

/-- The source-shaped one-run budget is monotone in `1/eps`: shrinking the accuracy
parameter can only increase the budget. -/
theorem sourceOneRunQueryBudget_mono_eps
    {rc R eps eps' : Real} {n : Nat} (hrc : 0 ≤ rc) (hn : 1 ≤ n)
    (heps : 0 < eps') (hee : eps' ≤ eps) (_heps1 : eps < 1) :
    sourceOneRunQueryBudget rc n R eps ≤ sourceOneRunQueryBudget rc n R eps' := by
  unfold sourceOneRunQueryBudget sourceOneRunQueryEnvelope
  refine ENNReal.ofReal_le_ofReal ?_
  have heps0 : (0 : Real) < eps := lt_of_lt_of_le heps hee
  have hn0 : (1 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hinv : 1 / eps ≤ 1 / eps' := by
    apply one_div_le_one_div_of_le heps hee
  have hinvpos : (0 : Real) < 1 / eps := by positivity
  have hne : (n : Real) / eps ≤ (n : Real) / eps' := by
    apply div_le_div_of_nonneg_left (by linarith) heps hee
  have hnepos : (0 : Real) < (n : Real) / eps := by positivity
  have hL1 : sourceLogFactor (1 / eps) ≤ sourceLogFactor (1 / eps') :=
    sourceLogFactor_mono_of_pos hinvpos hinv
  have hL2 : sourceLogFactor ((n : Real) / eps) ≤ sourceLogFactor ((n : Real) / eps') :=
    sourceLogFactor_mono_of_pos hnepos hne
  have hsq : eps' ^ 2 ≤ eps ^ 2 := by
    gcongr
  have hlog : (0 : Real) ≤ sourceLogFactor n := (sourceLogFactor_pos _).le
  have hmax : (0 : Real) ≤ max (R ^ 2 * (n : Real) ^ 2) ((n : Real) ^ 3) :=
    le_max_of_le_right (by positivity)
  have hL1pos : (0 : Real) ≤ sourceLogFactor (1 / eps) := (sourceLogFactor_pos _).le
  have hL2pos : (0 : Real) ≤ sourceLogFactor ((n : Real) / eps) := (sourceLogFactor_pos _).le
  have hsqpos : (0 : Real) < eps' ^ 2 := by positivity
  gcongr

end Ttc.CVSourceReferenceWeaken

namespace Ttc.CVSourceReferenceTVCapstone

open MeasureTheory Set
open Ttc.CVSourcePolynomialCutoffCapstone
open scoped ENNReal

/-! ## Weakening the certificate -/

/-- The `4/5` accuracy field survives replacing the accepted output window by any larger
set of values.  This is the form consumed by the `Icc` widening lemmas, which produce a
set inclusion rather than a pair of endpoint inequalities. -/
theorem SourceReferenceTVOneRunCertificate.accuracy_mono_of_subset
    {Omega : Type*} [MeasurableSpace Omega] {actual : Measure Omega}
    [IsFiniteMeasure actual]
    {value : Omega → Real} {S T : Set Real} (hST : S ⊆ T)
    (h : 4 / 5 ≤ actual.real {omega | value omega ∈ S}) :
    4 / 5 ≤ actual.real {omega | value omega ∈ T} :=
  h.trans (measureReal_mono fun _ homega => hST homega)

/-- The `4/5` accuracy field survives widening the accepted output window. -/
theorem SourceReferenceTVOneRunCertificate.accuracy_mono
    {Omega : Type*} [MeasurableSpace Omega] {actual : Measure Omega}
    [IsFiniteMeasure actual]
    {value : Omega → Real} {lo hi lo' hi' : Real}
    (_hmeas : Measurable value)
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi')
    (h : 4 / 5 ≤ actual.real {omega | value omega ∈ Icc lo hi}) :
    4 / 5 ≤ actual.real {omega | value omega ∈ Icc lo' hi'} :=
  SourceReferenceTVOneRunCertificate.accuracy_mono_of_subset
    (Set.Icc_subset_Icc hlo hhi) h

/-- The certificate weakens along any growth of the query budget and any enlargement of
the accepted output window, the latter given as a set inclusion.  The budget comparison is
kept as a single opaque hypothesis so that callers may discharge it by the monotonicity
lemmas above or directly. -/
theorem SourceReferenceTVOneRunCertificate.weaken_of_subset
    {Omega : Type*} [MeasurableSpace Omega]
    {actual reference : Measure Omega} {cost : Omega → ENNReal}
    {value : Omega → Real} {rc rc' : Real} {n : Nat}
    {R R' eps eps' lo hi lo' hi' : Real}
    (hcert : SourceReferenceTVOneRunCertificate actual reference cost value
      rc n R eps lo hi)
    (hbudget : sourceOneRunQueryBudget rc n R eps ≤
      sourceOneRunQueryBudget rc' n R' eps')
    (hwindow : Icc lo hi ⊆ Icc lo' hi') :
    SourceReferenceTVOneRunCertificate actual reference cost value
      rc' n R' eps' lo' hi' := by
  letI : IsProbabilityMeasure actual := hcert.actual_probability
  exact
    { actual_probability := hcert.actual_probability
      reference_probability := hcert.reference_probability
      cost_measurable := hcert.cost_measurable
      value_measurable := hcert.value_measurable
      path_tv := hcert.path_tv
      reference_expected_queries := hcert.reference_expected_queries.trans hbudget
      accuracy :=
        SourceReferenceTVOneRunCertificate.accuracy_mono_of_subset hwindow hcert.accuracy }

/-- The certificate weakens along any growth of the query budget and any widening of the
accepted output window.  The budget comparison is kept as a single opaque hypothesis so
that callers may discharge it by the monotonicity lemmas above or directly. -/
theorem SourceReferenceTVOneRunCertificate.weaken
    {Omega : Type*} [MeasurableSpace Omega]
    {actual reference : Measure Omega} {cost : Omega → ENNReal}
    {value : Omega → Real} {rc rc' : Real} {n : Nat}
    {R R' eps eps' lo hi lo' hi' : Real}
    (hcert : SourceReferenceTVOneRunCertificate actual reference cost value
      rc n R eps lo hi)
    (hbudget : sourceOneRunQueryBudget rc n R eps ≤
      sourceOneRunQueryBudget rc' n R' eps')
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    SourceReferenceTVOneRunCertificate actual reference cost value
      rc' n R' eps' lo' hi' :=
  hcert.weaken_of_subset hbudget (Set.Icc_subset_Icc hlo hhi)

end Ttc.CVSourceReferenceTVCapstone

#print axioms Ttc.CVSourceReferenceWeaken.Icc_relErr_subset
#print axioms Ttc.CVSourceReferenceWeaken.Icc_relErr_subset_of_approx
#print axioms Ttc.CVSourceReferenceWeaken.sourceOneRunQueryBudget_mono_constant
#print axioms Ttc.CVSourceReferenceWeaken.sourceOneRunQueryBudget_mono_radius
#print axioms Ttc.CVSourceReferenceWeaken.sourceOneRunQueryBudget_mono_eps
#print axioms
  Ttc.CVSourceReferenceTVCapstone.SourceReferenceTVOneRunCertificate.accuracy_mono_of_subset
#print axioms
  Ttc.CVSourceReferenceTVCapstone.SourceReferenceTVOneRunCertificate.accuracy_mono
#print axioms
  Ttc.CVSourceReferenceTVCapstone.SourceReferenceTVOneRunCertificate.weaken_of_subset
#print axioms Ttc.CVSourceReferenceTVCapstone.SourceReferenceTVOneRunCertificate.weaken
