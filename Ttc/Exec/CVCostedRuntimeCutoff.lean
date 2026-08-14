/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Exec.CostedAmbientGaussianRejection
import Ttc.Volume.CVRuntimeAmplification
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# The CV expected-runtime cutoff argument

The operational phase laws record their query count in `ENNReal` (and assign `infinity` to
nontermination).  This file proves the final paragraph after `lem:accuracy`: an expected
cost bound and a deterministic cutoff whose Markov ratio is at most `1/20` reduce success
from `4/5` to at worst `3/4`; independent cutoff runs are then median-amplified.
-/

namespace Ttc.CVCostedRuntimeCutoff

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Return the recorded value below the cutoff, and a fixed fallback on timeout. -/
noncomputable def cutoffValue (L : ENNReal) (fallback : Real)
    (cost : Omega → ENNReal) (value : Omega → Real) (omega : Omega) : Real :=
  if cost omega < L then value omega else fallback

theorem measurable_cutoffValue {L : ENNReal} {fallback : Real}
    {cost : Omega → ENNReal} {value : Omega → Real}
    (hcost : Measurable cost) (hvalue : Measurable value) :
    Measurable (cutoffValue L fallback cost value) := by
  exact hvalue.piecewise (measurableSet_lt hcost measurable_const) measurable_const

/-- ENNReal Markov inequality in the exact interface needed by a costed execution. -/
theorem timeout_le_of_lintegral_le
    {mu : Measure Omega} {cost : Omega → ENNReal} (hcost : Measurable cost)
    {B L : ENNReal} (hL0 : L ≠ 0) (hLtop : L ≠ ⊤)
    (hmean : (∫⁻ omega, cost omega ∂mu) ≤ B) :
    mu {omega | L ≤ cost omega} ≤ B / L := by
  exact (meas_ge_le_lintegral_div hcost.aemeasurable hL0 hLtop).trans
    (ENNReal.div_le_div_right hmean L)

theorem timeout_measureReal_le_one_twentieth
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {cost : Omega → ENNReal} (hcost : Measurable cost)
    {B L : ENNReal} (hL0 : L ≠ 0) (hLtop : L ≠ ⊤)
    (hmean : (∫⁻ omega, cost omega ∂mu) ≤ B)
    (hratio : B / L ≤ ENNReal.ofReal (1 / 20 : Real)) :
    mu.real {omega | L ≤ cost omega} ≤ 1 / 20 := by
  change (mu {omega | L ≤ cost omega}).toReal ≤ 1 / 20
  apply ENNReal.toReal_le_of_le_ofReal (by norm_num : (0 : Real) ≤ 1 / 20)
  exact (timeout_le_of_lintegral_le hcost hL0 hLtop hmean).trans hratio

/-- The source's constant calculation on an actual cost/output law. -/
theorem cutoff_success_three_quarters
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {cost : Omega → ENNReal} {value : Omega → Real}
    {B L : ENNReal} {fallback lo hi : Real}
    (hcost : Measurable cost) (hvalue : Measurable value)
    (hL0 : L ≠ 0) (hLtop : L ≠ ⊤)
    (hmean : (∫⁻ omega, cost omega ∂mu) ≤ B)
    (hratio : B / L ≤ ENNReal.ofReal (1 / 20 : Real))
    (haccuracy : 4 / 5 ≤ mu.real {omega | value omega ∈ Icc lo hi}) :
    3 / 4 ≤ mu.real
      {omega | cutoffValue L fallback cost value omega ∈ Icc lo hi} := by
  let G : Set Omega := {omega | value omega ∈ Icc lo hi}
  let T : Set Omega := {omega | L ≤ cost omega}
  let Bad : Set Omega :=
    {omega | cutoffValue L fallback cost value omega ∉ Icc lo hi}
  have hG : MeasurableSet G := measurableSet_Icc.preimage hvalue
  have hT : MeasurableSet T := measurableSet_le measurable_const hcost
  have hcut : Measurable (cutoffValue L fallback cost value) :=
    measurable_cutoffValue hcost hvalue
  have hBad : MeasurableSet Bad := (measurableSet_Icc.preimage hcut).compl
  have hGc : mu.real Gᶜ ≤ 1 / 5 := by
    rw [measureReal_compl hG, probReal_univ]
    have := haccuracy
    change 4 / 5 ≤ mu.real G at this
    linarith
  have htimeout : mu.real T ≤ 1 / 20 := by
    exact timeout_measureReal_le_one_twentieth hcost hL0 hLtop hmean hratio
  have hsub : Bad ⊆ Gᶜ ∪ T := by
    intro omega hbad
    by_cases hfinish : cost omega < L
    · left
      change value omega ∉ Icc lo hi
      simpa [Bad, cutoffValue, hfinish] using hbad
    · right
      change L ≤ cost omega
      exact le_of_not_gt hfinish
  have hbadLe : mu.real Bad ≤ 1 / 4 := by
    calc
      mu.real Bad ≤ mu.real (Gᶜ ∪ T) :=
        measureReal_mono hsub (measure_ne_top mu _)
      _ ≤ mu.real Gᶜ + mu.real T := measureReal_union_le _ _
      _ ≤ 1 / 5 + 1 / 20 := add_le_add hGc htimeout
      _ = 1 / 4 := by norm_num
  have hgood :
      {omega | cutoffValue L fallback cost value omega ∈ Icc lo hi} = Badᶜ := by
    ext omega
    simp only [Bad, mem_setOf_eq, mem_compl_iff]
    tauto
  rw [hgood, measureReal_compl hBad, probReal_univ]
  linarith

/-- Independent, deterministically cutoff runs recover arbitrary confidence by their median. -/
theorem median_cutoff_success
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {r : Nat} (hr : 0 < r)
    {cost : Fin r → Omega → ENNReal} {value : Fin r → Omega → Real}
    {B L : ENNReal} {fallback lo hi p : Real} {median : Omega → Real}
    (hcost : ∀ i, Measurable (cost i)) (hvalue : ∀ i, Measurable (value i))
    (hL0 : L ≠ 0) (hLtop : L ≠ ⊤)
    (hmean : ∀ i, (∫⁻ omega, cost i omega ∂mu) ≤ B)
    (hratio : B / L ≤ ENNReal.ofReal (1 / 20 : Real))
    (haccuracy : ∀ i, 4 / 5 ≤ mu.real {omega | value i omega ∈ Icc lo hi})
    (hindep : iIndepFun
      (fun i ↦ cutoffValue L fallback (cost i) (value i)) mu)
    (hmedian : ∀ omega, Arlib.GaussianCooling.IsMedian
      (fun i ↦ cutoffValue L fallback (cost i) (value i) omega) (median omega))
    (hp : 0 < p)
    (hreps : Real.log (1 / p) / (2 * (3 / 4 - 1 / 2) ^ 2) ≤ (r : Real)) :
    1 - p ≤ mu.real {omega | median omega ∈ Icc lo hi} := by
  apply Arlib.GaussianCooling.median_boost (μ := mu) hr
    (v := fun i ↦ cutoffValue L fallback (cost i) (value i))
    (z := median) (q := (3 : Real) / 4)
  · intro i
    exact measurable_cutoffValue (hcost i) (hvalue i)
  · exact hindep
  · exact hmedian
  · intro i
    exact cutoff_success_three_quarters (hcost i) (hvalue i) hL0 hLtop
      (hmean i) hratio (haccuracy i)
  · norm_num
  · exact hp
  · simpa using hreps

#print axioms timeout_le_of_lintegral_le
#print axioms cutoff_success_three_quarters
#print axioms median_cutoff_success

end Ttc.CVCostedRuntimeCutoff
