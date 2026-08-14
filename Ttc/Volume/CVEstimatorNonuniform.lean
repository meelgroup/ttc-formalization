/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVEstimator

/-!
# The Cousins--Vempala estimator with phase-dependent variance factors

This file isolates the estimator bookkeeping used by the accelerated part of Gaussian cooling.
At phase `i`, `k` independent scores of exact mean `ν i` and relative second moment at most
`c i` are averaged.  Thus the phase average has relative second moment at most

`1 + (c i - 1) / k`.

The phase averages are then multiplied.  Independence of the phase blocks factors both moments,
giving the exact nonuniform budget

`∏ i, (1 + (c i - 1) / k)`.

## Independence interface

The sufficient independence contract has two clauses:

* the `k` coordinates inside each phase are jointly independent;
* the `Fin k -> Real` phase vectors are jointly independent across phases.

Together these express independence of all coordinates in precisely the two groupings the proof
uses.  Mathlib currently has no grouping theorem deriving the second clause from a single flat
`iIndepFun` hypothesis indexed by `Fin m × Fin k`; its available
`iIndepFun.indepFun_finset` theorem only gives independence of two blocks.  Keeping both clauses
explicit avoids hiding that interface gap.
-/

namespace Ttc

open MeasureTheory ProbabilityTheory Arlib.GaussianCooling

namespace CVEst

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- The vector of all `k` coordinates in one phase. -/
def phaseVector {m k : Nat} (Y : Fin m -> Fin k -> Omega -> Real) (i : Fin m) :
    Omega -> (Fin k -> Real) :=
  fun omega j => Y i j omega

/-- The arithmetic mean as a measurable function on a finite coordinate vector. -/
noncomputable def avgVector (k : Nat) (x : Fin k -> Real) : Real :=
  (∑ j, x j) / (k : Real)

omit [MeasurableSpace Omega] in
theorem avgOf_eq_avgVector {m k : Nat} (Y : Fin m -> Fin k -> Omega -> Real)
    (i : Fin m) :
    avgOf k (Y i) = fun omega => avgVector k (phaseVector Y i omega) := by
  rfl

theorem measurable_avgVector (k : Nat) : Measurable (avgVector k) := by
  unfold avgVector
  fun_prop

/-- The two-level independence contract for all coordinates of the estimator. -/
def CoordinateIndep {m k : Nat} (Y : Fin m -> Fin k -> Omega -> Real)
    (mu : Measure Omega) : Prop :=
  (forall i, iIndepFun (Y i) mu) /\ iIndepFun (phaseVector Y) mu

theorem CoordinateIndep.within {m k : Nat} {Y : Fin m -> Fin k -> Omega -> Real}
    (h : CoordinateIndep Y mu) (i : Fin m) : iIndepFun (Y i) mu :=
  h.1 i

theorem CoordinateIndep.pairwiseWithin {m k : Nat}
    {Y : Fin m -> Fin k -> Omega -> Real} (h : CoordinateIndep Y mu) (i : Fin m) :
    Pairwise fun j j' => IndepFun (Y i j) (Y i j') mu :=
  fun _ _ hjj => (h.within i).indepFun hjj

/-- Independent phase vectors give independent empirical phase averages. -/
theorem CoordinateIndep.avgPhases {m k : Nat}
    {Y : Fin m -> Fin k -> Omega -> Real} (h : CoordinateIndep Y mu) :
    iIndepFun (fun i => avgOf k (Y i)) mu := by
  rw [show (fun i => avgOf k (Y i)) =
      fun i omega => avgVector k (phaseVector Y i omega) by
    funext i omega
    rfl]
  exact h.2.comp (fun _ => avgVector k) (fun _ => measurable_avgVector k)

/-- The exact mean of every phase average, with phase-dependent means. -/
theorem integral_phaseAvg [IsProbabilityMeasure mu] {m k : Nat} (hk : 0 < k)
    {Y : Fin m -> Fin k -> Omega -> Real} {nu : Fin m -> Real}
    (hL2 : forall i j, MemLp (Y i j) 2 mu)
    (hmean : forall i j, (∫ omega, Y i j omega ∂mu) = nu i) (i : Fin m) :
    (∫ omega, avgOf k (Y i) omega ∂mu) = nu i :=
  integral_avgOf hk (fun j => (hL2 i j).integrable one_le_two) (hmean i)

/-- The phase-dependent relative second-moment bound after averaging `k` coordinates. -/
theorem phaseAvg_sq_moment_le [IsProbabilityMeasure mu] {m k : Nat} (hk : 0 < k)
    {Y : Fin m -> Fin k -> Omega -> Real} {nu c : Fin m -> Real}
    (hL2 : forall i j, MemLp (Y i j) 2 mu) (hindep : CoordinateIndep Y mu)
    (hmean : forall i j, (∫ omega, Y i j omega ∂mu) = nu i)
    (hsq : forall i j, (∫ omega, (Y i j omega) ^ 2 ∂mu) <= c i * (nu i) ^ 2)
    (i : Fin m) :
    (∫ omega, (avgOf k (Y i) omega) ^ 2 ∂mu) <=
      (1 + (c i - 1) / (k : Real)) * (nu i) ^ 2 :=
  avgOf_sq_moment_le hk (hL2 i) (hindep.pairwiseWithin i) (hmean i) (hsq i)

/-! ## A product theorem with nonuniform factors -/

/-- A phase-dependent version of `Arlib.GaussianCooling.prod_sq_div_le`.

If independent factors `W i` have relative second-moment factors `d i`, the product has
factor `prod i, d i`. -/
theorem prod_sq_moment_le_factors {I : Type*} [Fintype I] {W : I -> Omega -> Real}
    {d : I -> Real} (hindep : iIndepFun W mu)
    (hmeas : forall i, AEStronglyMeasurable (W i) mu)
    (hsq : forall i, (∫ omega, (W i omega) ^ 2 ∂mu) <=
      d i * (∫ omega, W i omega ∂mu) ^ 2) :
    (∫ omega, (∏ i, W i omega) ^ 2 ∂mu) <=
      (∏ i, d i) * (∫ omega, ∏ i, W i omega ∂mu) ^ 2 := by
  rw [integral_prod_sq hindep hmeas, integral_prod_eq_prod_integral' hindep hmeas]
  calc
    (∏ i, ∫ omega, (W i omega) ^ 2 ∂mu) <=
        ∏ i, d i * (∫ omega, W i omega ∂mu) ^ 2 :=
      Finset.prod_le_prod
        (fun i _ => integral_nonneg fun omega => sq_nonneg (W i omega))
        (fun i _ => hsq i)
    _ = (∏ i, d i) * (∏ i, ∫ omega, W i omega ∂mu) ^ 2 := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow]

/-- The product of the empirical phase averages has the product of the phase means as its exact
mean. -/
theorem integral_prod_phaseAvg [IsProbabilityMeasure mu] {m k : Nat} (hk : 0 < k)
    {Y : Fin m -> Fin k -> Omega -> Real} {nu : Fin m -> Real}
    (hL2 : forall i j, MemLp (Y i j) 2 mu) (hindep : CoordinateIndep Y mu)
    (hmean : forall i j, (∫ omega, Y i j omega ∂mu) = nu i) :
    (∫ omega, ∏ i, avgOf k (Y i) omega ∂mu) = ∏ i, nu i := by
  rw [integral_prod_eq_prod_integral' hindep.avgPhases
    (fun i => (memLp_avgOf (hL2 i)).aestronglyMeasurable)]
  exact Finset.prod_congr rfl fun i _ => integral_phaseAvg hk hL2 hmean i

/-- **Exact nonuniform Cousins--Vempala estimator budget.**

At phase `i`, averaging `k` independent samples changes the single-sample relative second moment
factor `c i` into `1 + (c i - 1) / k`.  Independence across phase vectors then multiplies these
factors, with no uniform upper bound or phase-count relaxation. -/
theorem prod_phaseAvg_sq_moment_le [IsProbabilityMeasure mu] {m k : Nat} (hk : 0 < k)
    {Y : Fin m -> Fin k -> Omega -> Real} {nu c : Fin m -> Real}
    (hL2 : forall i j, MemLp (Y i j) 2 mu) (hindep : CoordinateIndep Y mu)
    (hmean : forall i j, (∫ omega, Y i j omega ∂mu) = nu i)
    (hsq : forall i j, (∫ omega, (Y i j omega) ^ 2 ∂mu) <= c i * (nu i) ^ 2) :
    (∫ omega, (∏ i, avgOf k (Y i) omega) ^ 2 ∂mu) <=
      (∏ i, (1 + (c i - 1) / (k : Real))) *
        (∫ omega, ∏ i, avgOf k (Y i) omega ∂mu) ^ 2 := by
  refine prod_sq_moment_le_factors hindep.avgPhases
    (fun i => (memLp_avgOf (hL2 i)).aestronglyMeasurable) ?_
  intro i
  rw [integral_phaseAvg hk hL2 hmean i]
  exact phaseAvg_sq_moment_le hk hL2 hindep hmean hsq i

/-- The same exact budget, with the product mean rewritten as `prod i, nu i`. -/
theorem prod_phaseAvg_sq_moment_le_mean [IsProbabilityMeasure mu] {m k : Nat} (hk : 0 < k)
    {Y : Fin m -> Fin k -> Omega -> Real} {nu c : Fin m -> Real}
    (hL2 : forall i j, MemLp (Y i j) 2 mu) (hindep : CoordinateIndep Y mu)
    (hmean : forall i j, (∫ omega, Y i j omega ∂mu) = nu i)
    (hsq : forall i j, (∫ omega, (Y i j omega) ^ 2 ∂mu) <= c i * (nu i) ^ 2) :
    (∫ omega, (∏ i, avgOf k (Y i) omega) ^ 2 ∂mu) <=
      (∏ i, (1 + (c i - 1) / (k : Real))) * (∏ i, nu i) ^ 2 := by
  rw [← integral_prod_phaseAvg hk hL2 hindep hmean]
  exact prod_phaseAvg_sq_moment_le hk hL2 hindep hmean hsq

/-- An already-established product budget immediately gives the usual `exp kappa` relative
second-moment bound.  This is the interface consumed by `ChunkedVarBudget`. -/
theorem prod_phaseAvg_sq_moment_le_exp_of_prod [IsProbabilityMeasure mu]
    {m k : Nat} (hk : 0 < k) {Y : Fin m -> Fin k -> Omega -> Real}
    {nu c : Fin m -> Real} {kappa : Real}
    (hL2 : forall i j, MemLp (Y i j) 2 mu) (hindep : CoordinateIndep Y mu)
    (hmean : forall i j, (∫ omega, Y i j omega ∂mu) = nu i)
    (hsq : forall i j, (∫ omega, (Y i j omega) ^ 2 ∂mu) <= c i * (nu i) ^ 2)
    (hbudget : (∏ i, (1 + (c i - 1) / (k : Real))) <= Real.exp kappa) :
    (∫ omega, (∏ i, avgOf k (Y i) omega) ^ 2 ∂mu) <=
      Real.exp kappa * (∫ omega, ∏ i, avgOf k (Y i) omega ∂mu) ^ 2 :=
  (prod_phaseAvg_sq_moment_le hk hL2 hindep hmean hsq).trans
    (mul_le_mul_of_nonneg_right hbudget (sq_nonneg _))

/-- A sum of nonnegative phase excesses controls their product by an exponential. -/
theorem prod_one_add_le_exp_sum {I : Type*} [Fintype I] {x : I -> Real}
    (hx : forall i, 0 <= x i) :
    (∏ i, (1 + x i)) <= Real.exp (∑ i, x i) := by
  simpa using Real.prod_one_add_le_exp_sum Finset.univ hx

/-- The exponential corollary in additive-budget form. -/
theorem prod_phaseAvg_sq_moment_le_exp [IsProbabilityMeasure mu]
    {m k : Nat} (hk : 0 < k) {Y : Fin m -> Fin k -> Omega -> Real}
    {nu c : Fin m -> Real} {kappa : Real}
    (hL2 : forall i j, MemLp (Y i j) 2 mu) (hindep : CoordinateIndep Y mu)
    (hmean : forall i j, (∫ omega, Y i j omega ∂mu) = nu i)
    (hsq : forall i j, (∫ omega, (Y i j omega) ^ 2 ∂mu) <= c i * (nu i) ^ 2)
    (hc : forall i, 1 <= c i)
    (hsum : (∑ i, (c i - 1) / (k : Real)) <= kappa) :
    (∫ omega, (∏ i, avgOf k (Y i) omega) ^ 2 ∂mu) <=
      Real.exp kappa * (∫ omega, ∏ i, avgOf k (Y i) omega ∂mu) ^ 2 := by
  apply prod_phaseAvg_sq_moment_le_exp_of_prod hk hL2 hindep hmean hsq
  refine (prod_one_add_le_exp_sum (fun i => div_nonneg (sub_nonneg.mpr (hc i)) ?_)).trans ?_
  · exact_mod_cast hk.le
  · exact Real.exp_le_exp.mpr hsum

/-! ### Axiom audit -/

#print axioms CoordinateIndep.avgPhases
#print axioms integral_phaseAvg
#print axioms phaseAvg_sq_moment_le
#print axioms prod_sq_moment_le_factors
#print axioms integral_prod_phaseAvg
#print axioms prod_phaseAvg_sq_moment_le
#print axioms prod_phaseAvg_sq_moment_le_mean
#print axioms prod_phaseAvg_sq_moment_le_exp_of_prod
#print axioms prod_one_add_le_exp_sum
#print axioms prod_phaseAvg_sq_moment_le_exp

end CVEst

end Ttc
