/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Convexity.GaussianCooling.Estimator

/-!
# Turning the CV expected-cost run into a bounded run

This is the probability-theoretic last paragraph after `lem:accuracy`.  A run is accurate
with probability at least `4/5`.  If it is stopped at a deterministic query cutoff whose
timeout probability is at most `1/20`, the stopped run is still accurate with probability
at least `3/4`.  Independent stopped runs can therefore be median-amplified to confidence
`1-p`.

The theorem deliberately takes the timeout estimate as a hypothesis.  In the operational
CV development that estimate is supplied by the costed Gaussian kernels and Markov's
inequality; keeping the two statements separate prevents an expected cost from being
mistaken for a worst-case cost.
-/

namespace Ttc.CVRuntime

open MeasureTheory ProbabilityTheory Set

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Return the run's value if it finishes within `T` queries, and a fixed fallback
otherwise.  The associated executable cutoff always uses at most `T` queries. -/
def cutoffValue (T : Nat) (fallback : Real) (cost : Omega -> Nat) (value : Omega -> Real)
    (omega : Omega) : Real :=
  if cost omega <= T then value omega else fallback

theorem measurable_cutoffValue {T : Nat} {fallback : Real} {cost : Omega -> Nat}
    {value : Omega -> Real} (hcost : Measurable cost) (hvalue : Measurable value) :
    Measurable (cutoffValue T fallback cost value) := by
  exact hvalue.piecewise (hcost measurableSet_Iic) measurable_const

/-- The source's constant-probability calculation:

`1 - (1/5 + 1/20) = 3/4`.
-/
theorem cutoff_success_three_quarters {mu : Measure Omega} [IsProbabilityMeasure mu]
    {value : Omega -> Real} {cost : Omega -> Nat} {T : Nat} {fallback L U : Real}
    (hvalue : Measurable value) (hcost : Measurable cost)
    (haccuracy : 4 / 5 <= mu.real {omega | value omega ∈ Icc L U})
    (htimeout : mu.real {omega | T < cost omega} <= 1 / 20) :
    3 / 4 <= mu.real {omega | cutoffValue T fallback cost value omega ∈ Icc L U} := by
  let G : Set Omega := {omega | value omega ∈ Icc L U}
  let H : Set Omega := {omega | cost omega <= T}
  let B : Set Omega := {omega | cutoffValue T fallback cost value omega ∉ Icc L U}
  have hG : MeasurableSet G := measurableSet_Icc.preimage hvalue
  have hH : MeasurableSet H := hcost measurableSet_Iic
  have hcut : Measurable (cutoffValue T fallback cost value) :=
    measurable_cutoffValue hcost hvalue
  have hB : MeasurableSet B := (measurableSet_Icc.preimage hcut).compl
  have hGc : mu.real G.compl <= 1 / 5 := by
    change mu.real (Gᶜ) <= 1 / 5
    rw [measureReal_compl hG, probReal_univ]
    have haccG : 4 / 5 <= mu.real G := by simpa only [G] using haccuracy
    linarith
  have hHc : mu.real H.compl <= 1 / 20 := by
    have heq : H.compl = {omega | T < cost omega} := by
      ext omega
      change (¬ cost omega <= T) <-> T < cost omega
      omega
    rw [heq]
    exact htimeout
  have hsub : B ⊆ G.compl ∪ H.compl := by
    intro omega homega
    by_cases hfinish : cost omega <= T
    · left
      simp only [B, cutoffValue, hfinish, if_true, mem_setOf_eq] at homega
      change value omega ∉ Icc L U
      exact homega
    · right
      change ¬ cost omega <= T
      exact hfinish
  have hbad : mu.real B <= 1 / 4 := by
    calc
      mu.real B <= mu.real (G.compl ∪ H.compl) :=
        measureReal_mono hsub (measure_ne_top mu _)
      _ <= mu.real G.compl + mu.real H.compl := measureReal_union_le _ _
      _ <= 1 / 5 + 1 / 20 := add_le_add hGc hHc
      _ = 1 / 4 := by norm_num
  have hgood : {omega | cutoffValue T fallback cost value omega ∈ Icc L U} = B.compl := by
    ext omega
    change cutoffValue T fallback cost value omega ∈ Icc L U <->
      ¬ (cutoffValue T fallback cost value omega ∉ Icc L U)
    tauto
  rw [hgood]
  change 3 / 4 <= mu.real (Bᶜ)
  rw [measureReal_compl hB, probReal_univ]
  linarith

/-- Median amplification of independently repeated, deterministically stopped CV runs.
The per-run success constant is exactly `3/4`, so the repetition threshold is
`log(1/p) / (2 (3/4 - 1/2)^2)`. -/
theorem median_cutoff_success {mu : Measure Omega} [IsProbabilityMeasure mu]
    {r : Nat} (hr : 0 < r)
    {value : Fin r -> Omega -> Real} {cost : Fin r -> Omega -> Nat}
    {T : Nat} {fallback : Real} {median : Omega -> Real} {L U p : Real}
    (hvalue : forall i, Measurable (value i))
    (hcost : forall i, Measurable (cost i))
    (hindep : iIndepFun (fun i => cutoffValue T fallback (cost i) (value i)) mu)
    (hmedian : forall omega,
      Arlib.GaussianCooling.IsMedian
        (fun i => cutoffValue T fallback (cost i) (value i) omega) (median omega))
    (haccuracy : forall i, 4 / 5 <= mu.real {omega | value i omega ∈ Icc L U})
    (htimeout : forall i, mu.real {omega | T < cost i omega} <= 1 / 20)
    (hp : 0 < p)
    (hreps : Real.log (1 / p) / (2 * (3 / 4 - 1 / 2) ^ 2) <= (r : Real)) :
    1 - p <= mu.real {omega | median omega ∈ Icc L U} := by
  apply Arlib.GaussianCooling.median_boost (μ := mu) hr
    (v := fun i => cutoffValue T fallback (cost i) (value i))
    (z := median) (q := (3 : Real) / 4)
  · intro i
    exact measurable_cutoffValue (hcost i) (hvalue i)
  · exact hindep
  · exact hmedian
  · intro i
    exact cutoff_success_three_quarters (hvalue i) (hcost i) (haccuracy i) (htimeout i)
  · norm_num
  · exact hp
  · simpa using hreps

/-- The deterministic query charge of `r` cutoff runs is at most `r*T`, regardless of
whether any underlying unbounded run would have terminated. -/
theorem total_cutoff_cost_le (r T : Nat) (cost : Fin r -> Omega -> Nat) (omega : Omega) :
    (∑ i : Fin r, min (cost i omega) T) <= r * T := by
  calc
    (∑ i : Fin r, min (cost i omega) T) <= ∑ _i : Fin r, T := by
      exact Finset.sum_le_sum fun _ _ => min_le_right _ _
    _ = r * T := by simp

#print axioms cutoff_success_three_quarters
#print axioms median_cutoff_success
#print axioms total_cutoff_cost_le

end Ttc.CVRuntime
