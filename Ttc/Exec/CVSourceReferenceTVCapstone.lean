import Ttc.Exec.CVExceptionalReferenceGlobalTimeout
import Ttc.Exec.CVSourcePolynomialCutoffCapstone

/-!
# Source cutoff from a costed reference path

This is the alternate source capstone needed by the exceptional-reference argument.
The operational law is required to be accurate, but its *unbounded* expected query cost
is never assumed.  Instead a full cost/output path law is TV-close to a reference law
whose expected cost has the source-shaped bound.  A single cutoff of size forty times
the reference budget spends `1/40` on Markov and `1/40` on TV.  The public query random
variable is the genuinely stopped operational cost.
-/

namespace Ttc.CVSourceReferenceTVCapstone

open MeasureTheory ProbabilityTheory Set
open Arlib Arlib.GaussianCooling Arlib.Probability
open Ttc.CVCostedRuntimeCutoff
open Ttc.CVSourcePolynomialCutoffCapstone
open Ttc.CVExceptionalReferenceGlobalTimeout
open Ttc.CVCostedAdjustableOuterMedian
open scoped ENNReal Classical

/-- A cutoff leaving equal `1/40` allowances for reference Markov and path TV. -/
noncomputable def sourceReferenceCutoff
    (runtimeConstant : Real) (n : Nat) (R eps : Real) : ENNReal :=
  40 * (sourceOneRunQueryBudget runtimeConstant n R eps + 1)

theorem sourceReferenceCutoff_ne_zero (runtimeConstant : Real) (n : Nat)
    (R eps : Real) : sourceReferenceCutoff runtimeConstant n R eps ≠ 0 := by
  simp [sourceReferenceCutoff]

theorem sourceReferenceCutoff_ne_top (runtimeConstant : Real) (n : Nat)
    (R eps : Real) : sourceReferenceCutoff runtimeConstant n R eps ≠ ⊤ := by
  unfold sourceReferenceCutoff sourceOneRunQueryBudget
  exact ENNReal.mul_ne_top (by norm_num)
    (ENNReal.add_ne_top.mpr <| by simp)

theorem sourceReferenceCutoff_ratio (runtimeConstant : Real) (n : Nat)
    (R eps : Real) :
    sourceOneRunQueryBudget runtimeConstant n R eps /
        sourceReferenceCutoff runtimeConstant n R eps ≤
      ENNReal.ofReal (1 / 40 : Real) := by
  rw [ENNReal.div_le_iff_le_mul
    (Or.inl (sourceReferenceCutoff_ne_zero runtimeConstant n R eps))
    (Or.inl (sourceReferenceCutoff_ne_top runtimeConstant n R eps))]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : Real) < 40)]
  norm_num only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  unfold sourceReferenceCutoff
  calc
    sourceOneRunQueryBudget runtimeConstant n R eps ≤
        sourceOneRunQueryBudget runtimeConstant n R eps + 1 := le_add_right le_rfl
    _ = (1 / 40 : ENNReal) *
        (40 * (sourceOneRunQueryBudget runtimeConstant n R eps + 1)) := by
      rw [← mul_assoc, ENNReal.div_eq_inv_mul, mul_one,
        ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

/-- One-run certificate using only the reference expected cost.  `path_tv` is deliberately
on the complete operational sample space, before projecting away the query count. -/
structure SourceReferenceTVOneRunCertificate
    {Omega : Type*} [MeasurableSpace Omega]
    (actual reference : Measure Omega) (cost : Omega → ENNReal)
    (value : Omega → Real) (runtimeConstant : Real) (n : Nat)
    (R eps lo hi : Real) : Prop where
  actual_probability : IsProbabilityMeasure actual
  reference_probability : IsProbabilityMeasure reference
  cost_measurable : Measurable cost
  value_measurable : Measurable value
  path_tv : TVLe actual reference (ENNReal.ofReal (1 / 40 : Real))
  reference_expected_queries :
    (∫⁻ omega, cost omega ∂reference) ≤
      sourceOneRunQueryBudget runtimeConstant n R eps
  accuracy : 4 / 5 ≤ actual.real {omega | value omega ∈ Icc lo hi}

/-- The only timeout is a single global event under the actual path law. -/
theorem sourceReference_timeout_le_one_twentieth
    {Omega : Type*} [MeasurableSpace Omega]
    (actual reference : Measure Omega) (cost : Omega → ENNReal)
    (value : Omega → Real) {runtimeConstant R eps lo hi : Real} {n : Nat}
    (hcert : SourceReferenceTVOneRunCertificate actual reference cost value
      runtimeConstant n R eps lo hi) :
    actual {omega | sourceReferenceCutoff runtimeConstant n R eps ≤ cost omega} ≤
      ENNReal.ofReal (1 / 20 : Real) := by
  letI : IsProbabilityMeasure actual := hcert.actual_probability
  letI : IsProbabilityMeasure reference := hcert.reference_probability
  have htimeout := globalTimeout_le_of_jointPathTV hcert.path_tv cost
    hcert.cost_measurable
    (sourceReferenceCutoff_ne_zero runtimeConstant n R eps)
    (sourceReferenceCutoff_ne_top runtimeConstant n R eps)
    hcert.reference_expected_queries
  calc
    actual {omega | sourceReferenceCutoff runtimeConstant n R eps ≤ cost omega} ≤
        sourceOneRunQueryBudget runtimeConstant n R eps /
          sourceReferenceCutoff runtimeConstant n R eps +
            ENNReal.ofReal (1 / 40 : Real) := htimeout
    _ ≤ ENNReal.ofReal (1 / 40 : Real) + ENNReal.ofReal (1 / 40 : Real) := by
      gcongr
      exact sourceReferenceCutoff_ratio runtimeConstant n R eps
    _ = ENNReal.ofReal (1 / 20 : Real) := by
      rw [← ENNReal.ofReal_add (by norm_num : (0 : Real) ≤ 1 / 40)
        (by norm_num : (0 : Real) ≤ 1 / 40)]
      norm_num

theorem sourceReference_timeout_measureReal_le_one_twentieth
    {Omega : Type*} [MeasurableSpace Omega]
    (actual reference : Measure Omega) (cost : Omega → ENNReal)
    (value : Omega → Real) {runtimeConstant R eps lo hi : Real} {n : Nat}
    (hcert : SourceReferenceTVOneRunCertificate actual reference cost value
      runtimeConstant n R eps lo hi) :
    actual.real {omega | sourceReferenceCutoff runtimeConstant n R eps ≤ cost omega} ≤
      1 / 20 := by
  change (actual {omega | sourceReferenceCutoff runtimeConstant n R eps ≤ cost omega}).toReal ≤
    1 / 20
  apply ENNReal.toReal_le_of_le_ofReal (by norm_num)
  exact sourceReference_timeout_le_one_twentieth actual reference cost value hcert

/-- Raw `4/5` accuracy survives the reference-driven global cutoff with probability
`3/4`.  No expectation under `actual` occurs in the statement or proof. -/
theorem sourceReference_cutoff_success_three_quarters
    {Omega : Type*} [MeasurableSpace Omega]
    (actual reference : Measure Omega) (cost : Omega → ENNReal)
    (value : Omega → Real) {runtimeConstant R eps lo hi fallback : Real} {n : Nat}
    (hcert : SourceReferenceTVOneRunCertificate actual reference cost value
      runtimeConstant n R eps lo hi) :
    3 / 4 ≤ actual.real {omega |
      cutoffValue (sourceReferenceCutoff runtimeConstant n R eps) fallback cost value omega ∈
        Icc lo hi} := by
  letI : IsProbabilityMeasure actual := hcert.actual_probability
  let G : Set Omega := {omega | value omega ∈ Icc lo hi}
  let T : Set Omega :=
    {omega | sourceReferenceCutoff runtimeConstant n R eps ≤ cost omega}
  let Bad : Set Omega := {omega |
    cutoffValue (sourceReferenceCutoff runtimeConstant n R eps) fallback cost value omega ∉
      Icc lo hi}
  have hG : MeasurableSet G := measurableSet_Icc.preimage hcert.value_measurable
  have hT : MeasurableSet T := measurableSet_le measurable_const hcert.cost_measurable
  have hcut : Measurable
      (cutoffValue (sourceReferenceCutoff runtimeConstant n R eps) fallback cost value) :=
    measurable_cutoffValue hcert.cost_measurable hcert.value_measurable
  have hBad : MeasurableSet Bad := (measurableSet_Icc.preimage hcut).compl
  have hGc : actual.real Gᶜ ≤ 1 / 5 := by
    rw [measureReal_compl hG, probReal_univ]
    have hacc := hcert.accuracy
    change 4 / 5 ≤ actual.real G at hacc
    linarith
  have htimeout : actual.real T ≤ 1 / 20 := by
    simpa only [T] using
      sourceReference_timeout_measureReal_le_one_twentieth actual reference cost value hcert
  have hsub : Bad ⊆ Gᶜ ∪ T := by
    intro omega hbad
    by_cases hfinish : cost omega < sourceReferenceCutoff runtimeConstant n R eps
    · left
      change value omega ∉ Icc lo hi
      simpa [Bad, cutoffValue, hfinish] using hbad
    · right
      exact le_of_not_gt hfinish
  have hbadLe : actual.real Bad ≤ 1 / 4 := by
    calc
      actual.real Bad ≤ actual.real (Gᶜ ∪ T) :=
        measureReal_mono hsub (measure_ne_top actual _)
      _ ≤ actual.real Gᶜ + actual.real T := measureReal_union_le _ _
      _ ≤ 1 / 5 + 1 / 20 := add_le_add hGc htimeout
      _ = 1 / 4 := by norm_num
  have hgood : {omega |
      cutoffValue (sourceReferenceCutoff runtimeConstant n R eps) fallback cost value omega ∈
        Icc lo hi} = Badᶜ := by
    ext omega
    simp only [Bad, mem_setOf_eq, mem_compl_iff]
    tauto
  rw [hgood, measureReal_compl hBad, probReal_univ]
  linarith

/-- Median amplification of iid actual runs, with the per-run success supplied by the
reference path rather than by an actual expected-cost hypothesis. -/
theorem sourceReference_median_cutoff_accuracy
    {Omega : Type*} [MeasurableSpace Omega]
    (actual reference : Measure Omega) (cost : Omega → ENNReal)
    (value : Omega → Real) {runtimeConstant R eps lo hi fallback p : Real} {n : Nat}
    (hcert : SourceReferenceTVOneRunCertificate actual reference cost value
      runtimeConstant n R eps lo hi) (hp : 0 < p) :
    1 - p ≤ (sourceOuterLaw actual (outerCutoffReps p)).real {omega |
      medianSel (fun i => cutoffValue
        (sourceReferenceCutoff runtimeConstant n R eps) fallback cost value (omega i)) ∈
          Icc lo hi} := by
  letI : IsProbabilityMeasure actual := hcert.actual_probability
  let mu : Measure (Fin (outerCutoffReps p) → Omega) :=
    Measure.pi (fun _ : Fin (outerCutoffReps p) => actual)
  letI : IsProbabilityMeasure mu := by
    dsimp only [mu]
    infer_instance
  apply Arlib.GaussianCooling.median_boost (μ := mu) (outerCutoffReps_pos p)
    (v := fun i omega => cutoffValue
      (sourceReferenceCutoff runtimeConstant n R eps) fallback cost value (omega i))
    (z := fun omega => medianSel (fun i => cutoffValue
      (sourceReferenceCutoff runtimeConstant n R eps) fallback cost value (omega i)))
    (q := (3 : Real) / 4)
  · intro i
    exact (measurable_cutoffValue hcert.cost_measurable hcert.value_measurable).comp
      (measurable_pi_apply i)
  · exact iIndepFun_pi fun _ =>
      (measurable_cutoffValue hcert.cost_measurable hcert.value_measurable).aemeasurable
  · intro omega
    exact medianSel_isMedian _
  · intro i
    have hmp := measurePreserving_eval
      (fun _ : Fin (outerCutoffReps p) => actual) i
    let S : Set Omega := {omega | cutoffValue
      (sourceReferenceCutoff runtimeConstant n R eps) fallback cost value omega ∈ Icc lo hi}
    have hS : MeasurableSet S := measurableSet_Icc.preimage
      (measurable_cutoffValue hcert.cost_measurable hcert.value_measurable)
    have heq : mu.real {omega | cutoffValue
        (sourceReferenceCutoff runtimeConstant n R eps) fallback cost value (omega i) ∈
          Icc lo hi} = actual.real S := by
      change (mu ((fun omega : Fin (outerCutoffReps p) → Omega => omega i) ⁻¹' S)).toReal =
        (actual S).toReal
      rw [← Measure.map_apply (measurable_pi_apply i) hS, hmp.map_eq]
    rw [heq]
    exact sourceReference_cutoff_success_three_quarters actual reference cost value hcert
  · norm_num
  · exact hp
  · simpa using outerCutoffReps_spec p

/-! ## Public stopped-cost oracle -/

abbrev SourceReferenceOuterCoin (r : Nat) (Omega : Type*) := Fin r → Omega

noncomputable def sourceReferenceOuterEstimator
    {Omega : Type*} (runtimeConstant : Real) (n : Nat) (R eps fallback : Real)
    (cost : Omega → ENNReal) (value : Omega → Real) {r : Nat}
    (omega : SourceReferenceOuterCoin r Omega) : Real :=
  medianSel fun i => cutoffValue (sourceReferenceCutoff runtimeConstant n R eps)
    fallback cost value (omega i)

noncomputable def sourceReferenceOuterQueryCost
    {Omega : Type*} (runtimeConstant : Real) (n : Nat) (R eps : Real)
    (cost : Omega → ENNReal) {r : Nat}
    (omega : SourceReferenceOuterCoin r Omega) : ENNReal :=
  ∑ i, min (cost (omega i)) (sourceReferenceCutoff runtimeConstant n R eps)

noncomputable def sourceReferencePublicExpectedBound
    (runtimeConstant : Real) (n : Nat) (radialR : Set (Ttc.Space n) → Real)
    (K : Set (Ttc.Space n)) (eps p : Real) : ENNReal :=
  (outerCutoffReps p : ENNReal) *
    sourceReferenceCutoff runtimeConstant n (radialR K) eps

theorem measurable_sourceReferenceOuterQueryCost
    {Omega : Type*} [MeasurableSpace Omega]
    {runtimeConstant R eps : Real} {n r : Nat} {cost : Omega → ENNReal}
    (hcost : Measurable cost) :
    Measurable (sourceReferenceOuterQueryCost runtimeConstant n R eps cost :
      SourceReferenceOuterCoin r Omega → ENNReal) := by
  unfold sourceReferenceOuterQueryCost
  apply Finset.measurable_fun_sum
  intro i hi
  exact (hcost.comp (measurable_pi_apply i)).min measurable_const

theorem sourceReferenceOuter_expectedQueryCost_le
    {Omega : Type*} [MeasurableSpace Omega]
    (oneLaw : Measure Omega) [IsProbabilityMeasure oneLaw]
    {runtimeConstant R eps : Real} {n r : Nat} {cost : Omega → ENNReal} :
    (∫⁻ omega, sourceReferenceOuterQueryCost runtimeConstant n R eps cost omega
      ∂sourceOuterLaw oneLaw r) ≤
      (r : ENNReal) * sourceReferenceCutoff runtimeConstant n R eps := by
  calc
    _ ≤ ∫⁻ _omega, (r : ENNReal) * sourceReferenceCutoff runtimeConstant n R eps
        ∂sourceOuterLaw oneLaw r := by
      apply lintegral_mono
      intro omega
      unfold sourceReferenceOuterQueryCost
      calc
        ∑ i, min (cost (omega i)) (sourceReferenceCutoff runtimeConstant n R eps) ≤
            ∑ _i : Fin r, sourceReferenceCutoff runtimeConstant n R eps := by
          exact Finset.sum_le_sum fun _ _ => min_le_right _ _
        _ = (r : ENNReal) * sourceReferenceCutoff runtimeConstant n R eps := by simp
    _ = (r : ENNReal) * sourceReferenceCutoff runtimeConstant n R eps := by
      simp [sourceOuterLaw]

/-- Input-indexed actual/reference certificates.  The reference law is used only for the
single-run timeout proof; the public algorithm executes and charges the stopped actual law. -/
structure SourcePublicReferenceTVCertificates
    (n : Nat) (runtimeConstant : Real) (radialR : Set (Ttc.Space n) → Real)
    (Omega : Ttc.CVAdaptive.VolumeInput n → Type)
    [∀ a, MeasurableSpace (Omega a)]
    (actual reference : ∀ a, Measure (Omega a))
    (cost : ∀ a, Omega a → ENNReal) (value : ∀ a, Omega a → Real) : Prop where
  actual_probability : ∀ a, IsProbabilityMeasure (actual a)
  reference_probability : ∀ a, IsProbabilityMeasure (reference a)
  cost_measurable : ∀ a, Measurable (cost a)
  value_measurable : ∀ a, Measurable (value a)
  path_tv : ∀ a, TVLe (actual a) (reference a) (ENNReal.ofReal (1 / 40 : Real))
  reference_expected_queries : ∀ a,
    (∫⁻ omega, cost a omega ∂reference a) ≤
      sourceOneRunQueryBudget runtimeConstant n (radialR a.1) a.2.1
  accuracy : ∀ (K : Set (Ttc.Space n)) (eps p : Real),
    0 < eps → 0 < p → p < 1 → Convex Real K →
    Metric.ball (0 : Ttc.Space n) 1 ⊆ K → volume K ≠ ⊤ →
    4 / 5 ≤ (actual (K, eps, p)).real {omega | value (K, eps, p) omega ∈
      Icc ((1 - eps) * (volume K).toReal) ((1 + eps) * (volume K).toReal)}

/-- Public expected-query volume oracle obtained without any unbounded actual-mean
hypothesis.  Its cost is exactly the sum of the stopped actual run costs. -/
noncomputable def expectedQueryVolumeAlgorithmOfSourceReferenceTVCertificates
    (n : Nat) (runtimeConstant : Real)
    (radialR : Set (Ttc.Space n) → Real)
    (Omega : Ttc.CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ a, MeasurableSpace (Omega a)]
    (actual reference : ∀ a, Measure (Omega a))
    (cost : ∀ a, Omega a → ENNReal) (value : ∀ a, Omega a → Real)
    (hcert : SourcePublicReferenceTVCertificates n runtimeConstant radialR
      Omega actual reference cost value) : Ttc.ExpectedQueryVolumeAlgorithm n := by
  let X : Ttc.CVAdaptive.VolumeInput n → Type := fun a =>
    SourceReferenceOuterCoin (outerCutoffReps a.2.2) (Omega a)
  letI : ∀ a, MeasurableSpace (X a) := fun a => inferInstance
  let nu : ∀ a, Measure (X a) := fun a =>
    sourceOuterLaw (actual a) (outerCutoffReps a.2.2)
  let localEst : ∀ a, X a → Real := fun a =>
    sourceReferenceOuterEstimator runtimeConstant n (radialR a.1) a.2.1 0
      (cost a) (value a)
  let localCost : ∀ a, X a → ENNReal := fun a =>
    sourceReferenceOuterQueryCost runtimeConstant n (radialR a.1) a.2.1 (cost a)
  let bound : Ttc.CVAdaptive.VolumeInput n → ENNReal := fun a =>
    sourceReferencePublicExpectedBound runtimeConstant n radialR a.1 a.2.1 a.2.2
  letI : ∀ a, IsProbabilityMeasure (actual a) := hcert.actual_probability
  letI : ∀ a, IsProbabilityMeasure (reference a) := hcert.reference_probability
  letI : ∀ a, IsProbabilityMeasure (nu a) := by
    intro a
    dsimp only [nu, X, sourceOuterLaw]
    infer_instance
  apply Ttc.ExpectedQueryVolumeAlgorithm.ofInputCostedLaws n X nu localEst localCost
    (bound := bound)
  · intro a
    dsimp only [localEst, X, sourceReferenceOuterEstimator]
    apply measurable_medianSel
    intro i
    exact (measurable_cutoffValue (hcert.cost_measurable a)
      (hcert.value_measurable a)).comp (measurable_pi_apply i)
  · intro a
    dsimp only [localCost, X]
    exact measurable_sourceReferenceOuterQueryCost (hcert.cost_measurable a)
  · intro a
    dsimp only [localCost, nu, X, bound, sourceReferencePublicExpectedBound]
    exact sourceReferenceOuter_expectedQueryCost_le (actual a)
  · intro K eps p heps hp hp1 hKc hball hfin
    let a : Ttc.CVAdaptive.VolumeInput n := (K, eps, p)
    let cert : SourceReferenceTVOneRunCertificate (actual a) (reference a)
        (cost a) (value a) runtimeConstant n (radialR K) eps
        ((1 - eps) * (volume K).toReal) ((1 + eps) * (volume K).toReal) :=
      { actual_probability := hcert.actual_probability a
        reference_probability := hcert.reference_probability a
        cost_measurable := hcert.cost_measurable a
        value_measurable := hcert.value_measurable a
        path_tv := hcert.path_tv a
        reference_expected_queries := hcert.reference_expected_queries a
        accuracy := hcert.accuracy K eps p heps hp hp1 hKc hball hfin }
    dsimp only [nu, localEst, X, sourceReferenceOuterEstimator]
    exact sourceReference_median_cutoff_accuracy
      (actual a) (reference a) (cost a) (value a) cert hp

#print axioms sourceReference_timeout_le_one_twentieth
#print axioms sourceReference_cutoff_success_three_quarters
#print axioms sourceReference_median_cutoff_accuracy
#print axioms expectedQueryVolumeAlgorithmOfSourceReferenceTVCertificates

end Ttc.CVSourceReferenceTVCapstone
