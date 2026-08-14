import Ttc.Exec.TVCostPreservingResetLift
import Mathlib.MeasureTheory.Measure.Sub

/-! # Maximal coupling from the common part of two probability measures -/

namespace Ttc.TVMaximalCoupling

open MeasureTheory ProbabilityTheory Set
open Arlib
open scoped ENNReal Classical

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableEq X]

instance instIsFiniteMeasureInf (alpha tau : Measure X) [IsFiniteMeasure alpha] :
    IsFiniteMeasure (alpha ⊓ tau) :=
  ⟨lt_of_le_of_lt ((Measure.le_iff'.mp inf_le_left) Set.univ)
    (measure_lt_top alpha Set.univ)⟩

noncomputable def commonDefect (alpha tau : Measure X) : ENNReal :=
  1 - (alpha ⊓ tau) Set.univ

noncomputable def maximalCoupling (alpha tau : Measure X) : Measure (X × X) :=
  let common := alpha ⊓ tau
  let d := commonDefect alpha tau
  if d = 0 then
    Measure.map (fun x ↦ (x, x)) alpha
  else
    Measure.map (fun x ↦ (x, x)) common +
      d⁻¹ • ((alpha - common).prod (tau - common))

theorem common_le_left (alpha tau : Measure X) : alpha ⊓ tau ≤ alpha := inf_le_left
theorem common_le_right (alpha tau : Measure X) : alpha ⊓ tau ≤ tau := inf_le_right

theorem commonDefect_ne_top (alpha tau : Measure X) :
    commonDefect alpha tau ≠ ⊤ := by
  unfold commonDefect
  exact ne_top_of_le_ne_top ENNReal.one_ne_top (tsub_le_self)

theorem residual_mass_left
    (alpha tau : Measure X) [IsProbabilityMeasure alpha] [IsProbabilityMeasure tau] :
    (alpha - (alpha ⊓ tau)) Set.univ = commonDefect alpha tau := by
  rw [Measure.sub_apply MeasurableSet.univ (common_le_left alpha tau)]
  simp [commonDefect]

theorem residual_mass_right
    (alpha tau : Measure X) [IsProbabilityMeasure alpha] [IsProbabilityMeasure tau] :
    (tau - (alpha ⊓ tau)) Set.univ = commonDefect alpha tau := by
  rw [Measure.sub_apply MeasurableSet.univ (common_le_right alpha tau)]
  simp [commonDefect]

theorem eq_of_commonDefect_eq_zero
    (alpha tau : Measure X) [IsProbabilityMeasure alpha] [IsProbabilityMeasure tau]
    (hzero : commonDefect alpha tau = 0) : alpha = tau := by
  have hlmass : (alpha - (alpha ⊓ tau)) Set.univ = 0 := by
    rw [residual_mass_left, hzero]
  have hrmass : (tau - (alpha ⊓ tau)) Set.univ = 0 := by
    rw [residual_mass_right, hzero]
  have hlzero : alpha - (alpha ⊓ tau) = 0 :=
    Measure.measure_univ_eq_zero.mp hlmass
  have hrzero : tau - (alpha ⊓ tau) = 0 :=
    Measure.measure_univ_eq_zero.mp hrmass
  have hladd := Measure.sub_add_cancel_of_le (common_le_left alpha tau)
  have hradd := Measure.sub_add_cancel_of_le (common_le_right alpha tau)
  rw [hlzero, zero_add] at hladd
  rw [hrzero, zero_add] at hradd
  exact hladd.symm.trans hradd

theorem map_fst_maximalCoupling
    (alpha tau : Measure X) [IsProbabilityMeasure alpha] [IsProbabilityMeasure tau] :
    Measure.map Prod.fst (maximalCoupling alpha tau) = alpha := by
  unfold maximalCoupling
  dsimp only
  split_ifs with hzero
  · rw [Measure.map_map measurable_fst (by fun_prop)]
    rw [show Prod.fst ∘ (fun x : X ↦ (x, x)) = id by rfl, Measure.map_id]
  · rw [Measure.map_add _ _ measurable_fst, Measure.map_map measurable_fst (by fun_prop),
      Measure.map_smul, Measure.map_fst_prod]
    rw [show Prod.fst ∘ (fun x : X ↦ (x, x)) = id by rfl, Measure.map_id,
      residual_mass_right alpha tau, smul_smul,
      ENNReal.inv_mul_cancel hzero (commonDefect_ne_top alpha tau), one_smul]
    rw [add_comm]
    exact Measure.sub_add_cancel_of_le (common_le_left alpha tau)

theorem map_snd_maximalCoupling
    (alpha tau : Measure X) [IsProbabilityMeasure alpha] [IsProbabilityMeasure tau] :
    Measure.map Prod.snd (maximalCoupling alpha tau) = tau := by
  unfold maximalCoupling
  dsimp only
  split_ifs with hzero
  · rw [Measure.map_map measurable_snd (by fun_prop)]
    rw [show Prod.snd ∘ (fun x : X ↦ (x, x)) = id by rfl, Measure.map_id,
      eq_of_commonDefect_eq_zero alpha tau hzero]
  · rw [Measure.map_add _ _ measurable_snd, Measure.map_map measurable_snd (by fun_prop),
      Measure.map_smul, Measure.map_snd_prod]
    rw [show Prod.snd ∘ (fun x : X ↦ (x, x)) = id by rfl, Measure.map_id,
      residual_mass_left alpha tau, smul_smul,
      ENNReal.inv_mul_cancel hzero (commonDefect_ne_top alpha tau), one_smul]
    rw [add_comm]
    exact Measure.sub_add_cancel_of_le (common_le_right alpha tau)

instance maximalCoupling.instIsProbabilityMeasure
    (alpha tau : Measure X) [IsProbabilityMeasure alpha] [IsProbabilityMeasure tau] :
    IsProbabilityMeasure (maximalCoupling alpha tau) := by
  refine ⟨?_⟩
  have h := congrArg (fun xi : Measure X ↦ xi Set.univ)
    (map_fst_maximalCoupling alpha tau)
  rw [Measure.map_apply measurable_fst MeasurableSet.univ] at h
  simpa using h

theorem maximalCoupling_failure_le_defect
    (alpha tau : Measure X) [IsProbabilityMeasure alpha] [IsProbabilityMeasure tau] :
    maximalCoupling alpha tau {p | p.1 ≠ p.2} ≤ commonDefect alpha tau := by
  unfold maximalCoupling
  dsimp only
  split_ifs with hzero
  · have hBad : MeasurableSet {p : X × X | p.1 ≠ p.2} :=
      (measurableSet_eq_fun measurable_fst measurable_snd).compl
    rw [Measure.map_apply (by fun_prop) hBad]
    simp [hzero]
  · have hBad : MeasurableSet {p : X × X | p.1 ≠ p.2} :=
      (measurableSet_eq_fun measurable_fst measurable_snd).compl
    rw [Measure.add_apply, Measure.map_apply (by fun_prop) hBad]
    simp only [preimage_setOf_eq, ne_eq, not_true_eq_false, setOf_false, measure_empty,
      zero_add, Measure.smul_apply, smul_eq_mul]
    calc
      (commonDefect alpha tau)⁻¹ *
          ((alpha - (alpha ⊓ tau)).prod (tau - (alpha ⊓ tau))) {p | p.1 ≠ p.2} ≤
        (commonDefect alpha tau)⁻¹ *
          ((alpha - (alpha ⊓ tau)).prod (tau - (alpha ⊓ tau))) Set.univ := by
            gcongr
            exact subset_univ _
      _ = commonDefect alpha tau := by
        rw [← univ_prod_univ, Measure.prod_prod,
          residual_mass_left alpha tau, residual_mass_right alpha tau,
          ← mul_assoc, ENNReal.inv_mul_cancel hzero (commonDefect_ne_top alpha tau),
          one_mul]

theorem isCoupling_maximalCoupling
    (alpha tau : Measure X) [IsProbabilityMeasure alpha] [IsProbabilityMeasure tau] :
    Ttc.TVCostPreservingResetLift.IsCoupling
      (maximalCoupling alpha tau) alpha tau :=
  ⟨map_fst_maximalCoupling alpha tau, map_snd_maximalCoupling alpha tau⟩

/-- The common-part defect is bounded by the eventwise TV slack.  The use of
`toMeasurable alpha t` is what extends the measurable-set TV hypothesis to the arbitrary
set occurring in `Measure.inf_apply`. -/
theorem commonDefect_le_of_tvLe
    (alpha tau : Measure X) [IsProbabilityMeasure alpha] [IsProbabilityMeasure tau]
    {eps : ENNReal} (htv : TVLe alpha tau eps) :
    commonDefect alpha tau ≤ eps := by
  have hlower : 1 - eps ≤ (alpha ⊓ tau) Set.univ := by
    rw [Measure.inf_apply MeasurableSet.univ]
    apply le_sInf
    intro z hz
    obtain ⟨t, rfl⟩ := hz
    simp only [inter_univ]
    let u := toMeasurable alpha t
    have hu : MeasurableSet u := measurableSet_toMeasurable _ _
    have hat : alpha u = alpha t := by
      exact measure_toMeasurable t
    have htuc : tau uᶜ ≤ tau tᶜ := by
      exact measure_mono (compl_subset_compl.mpr (subset_toMeasurable alpha t))
    have hprob : tau u + tau uᶜ = 1 := by
      rw [measure_add_measure_compl hu, measure_univ]
    have hsum : 1 ≤ (alpha t + tau tᶜ) + eps := by
      calc
        1 = tau u + tau uᶜ := hprob.symm
        _ ≤ (alpha u + eps) + tau uᶜ := by
          gcongr
          exact htv.right hu
        _ ≤ (alpha t + eps) + tau tᶜ := by
          rw [hat]
          gcongr
        _ = (alpha t + tau tᶜ) + eps := by ac_rfl
    exact (tsub_le_iff_right.mpr hsum)
  unfold commonDefect
  rw [tsub_le_iff_right]
  have h := tsub_le_iff_right.mp hlower
  simpa [add_comm] using h

/-- Maximal coupling directly at a supplied `TVLe` bound. -/
theorem maximalCoupling_failure_le_of_tvLe
    (alpha tau : Measure X) [IsProbabilityMeasure alpha] [IsProbabilityMeasure tau]
    {eps : ENNReal} (htv : TVLe alpha tau eps) :
    maximalCoupling alpha tau {p | p.1 ≠ p.2} ≤ eps :=
  (maximalCoupling_failure_le_defect alpha tau).trans
    (commonDefect_le_of_tvLe alpha tau htv)

/-- **Constructive cost-preserving reset from TV.**  On a standard Borel state space,
the maximal coupling and regular conditional kernel produce a joint reset that preserves
the retained cost/history marginal, has exact target state marginal, and spends exactly
the supplied TV error. -/
theorem exists_costPreserving_reset_of_tvLe
    {A : Type*} [MeasurableSpace A]
    [StandardBorelSpace X] [Nonempty X]
    (mu : Measure (A × X)) [IsProbabilityMeasure mu]
    (tau : Measure X) [IsProbabilityMeasure tau]
    {eps : ENNReal} (htv : TVLe (Measure.map Prod.snd mu) tau eps) :
    ∃ nu : Measure (A × X),
      IsProbabilityMeasure nu ∧
      Measure.map Prod.fst nu = Measure.map Prod.fst mu ∧
      Measure.map Prod.snd nu = tau ∧ TVLe mu nu eps := by
  letI : IsProbabilityMeasure (Measure.map Prod.snd mu) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  exact Ttc.TVCostPreservingResetLift.exists_costPreserving_reset_of_coupling
    mu tau (maximalCoupling (Measure.map Prod.snd mu) tau)
    (isCoupling_maximalCoupling (Measure.map Prod.snd mu) tau)
    (maximalCoupling_failure_le_of_tvLe (Measure.map Prod.snd mu) tau htv)

#print axioms map_fst_maximalCoupling
#print axioms maximalCoupling_failure_le_defect
#print axioms commonDefect_le_of_tvLe
#print axioms exists_costPreserving_reset_of_tvLe

end Ttc.TVMaximalCoupling
