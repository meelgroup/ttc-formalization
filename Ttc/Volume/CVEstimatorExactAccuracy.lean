/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVEstimatorNonuniform
import Ttc.Volume.CVPackedRun
import Ttc.Volume.AdaptivePhaseScoreVariance

/-!
# Exact-law accuracy for the nonuniform Cousins--Vempala estimator

This file closes the probability-theoretic exact-law route:

1. an overall relative second-moment bound by `exp kappa` gives a direct Chebyshev bound;
2. exact phase means telescope, so one run targets the endpoint of the cooling chain;
3. independent repetitions and a median amplify `4 / 5` to `1 - p`;
4. the final theorem instantiates the result on the packed `RunSpace (Fin k -> E) r m`.

Approximate sampler laws deliberately do not occur here.  They belong in the coupling layer.
-/

namespace Ttc

open MeasureTheory ProbabilityTheory Arlib.GaussianCooling

namespace CVEst

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- Algebraic bridge from the raw adaptive phase factor proved for one sample to the
factor after averaging `k` samples.  Consequently the product hypothesis in the capstone
is definitionally the product controlled by `prod_globalPhaseVarFactor_le_exp`. -/
theorem averaged_adaptiveGlobalPhaseVarFactor_eq {k : Nat} (N s0 : Real) (i : Nat) :
    1 + (Arlib.GaussianCooling.Chunked.adaptiveGlobalPhaseVarFactor 1 N s0 i - 1) /
        (k : Real) =
      Arlib.GaussianCooling.Chunked.adaptiveGlobalPhaseVarFactor (k : Real) N s0 i := by
  unfold Arlib.GaussianCooling.Chunked.adaptiveGlobalPhaseVarFactor
  ring

/-! ## Direct Chebyshev from the overall product moment -/

/-- An overall `exp kappa` relative second-moment bound gives the exact relative-error tail
bound, without returning to per-phase estimates. -/
theorem relErr_ge_of_sq_moment_exp [IsProbabilityMeasure mu]
    {X : Omega -> Real} {kappa epsilon : Real} (hkappa : 0 <= kappa)
    (hepsilon : 0 < epsilon) (hX : MemLp X 2 mu)
    (hpos : 0 < (∫ omega, X omega ∂mu))
    (hsq : (∫ omega, (X omega) ^ 2 ∂mu) <=
      Real.exp kappa * (∫ omega, X omega ∂mu) ^ 2) :
    1 - (Real.exp kappa - 1) / epsilon ^ 2 <=
      mu.real {omega | X omega ∈ relErr epsilon (∫ omega, X omega ∂mu)} := by
  have hbad := CV.measure_notMem_relErr_le (μ := mu) hX hepsilon hpos hsq
  exact measureReal_ge_of_compl_le
    (div_nonneg (sub_nonneg.mpr (Real.one_le_exp hkappa)) (sq_nonneg epsilon)) hbad

/-- The paper's one-run `4 / 5` confidence, directly from the overall product moment. -/
theorem relErr_four_fifths_of_sq_moment_exp [IsProbabilityMeasure mu]
    {X : Omega -> Real} {kappa epsilon : Real} (hkappa : 0 <= kappa)
    (hepsilon : 0 < epsilon) (hX : MemLp X 2 mu)
    (hpos : 0 < (∫ omega, X omega ∂mu))
    (hsq : (∫ omega, (X omega) ^ 2 ∂mu) <=
      Real.exp kappa * (∫ omega, X omega ∂mu) ^ 2)
    (hbudget : Real.exp kappa - 1 <= epsilon ^ 2 / 5) :
    4 / 5 <= mu.real {omega | X omega ∈ relErr epsilon (∫ omega, X omega ∂mu)} := by
  have hmain := relErr_ge_of_sq_moment_exp hkappa hepsilon hX hpos hsq
  have htail : (Real.exp kappa - 1) / epsilon ^ 2 <= 1 / 5 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  linarith

/-! ## Exact telescope and one run -/

/-- A direct overall moment theorem for a product estimator whose exact mean is a telescoping
ratio.  Multiplication by the positive cold-start value moves relative error from the ratio
`A m / A 0` to the endpoint `A m`. -/
theorem run_four_fifths_of_product_moment [IsProbabilityMeasure mu]
    {m : Nat} {X : Omega -> Real} {A : Nat -> Real} {kappa epsilon : Real}
    (hkappa : 0 <= kappa) (hepsilon : 0 < epsilon)
    (hApos : forall i, 0 < A i) (hX : MemLp X 2 mu)
    (hmean : (∫ omega, X omega ∂mu) = A m / A 0)
    (hsq : (∫ omega, (X omega) ^ 2 ∂mu) <=
      Real.exp kappa * (∫ omega, X omega ∂mu) ^ 2)
    (hbudget : Real.exp kappa - 1 <= epsilon ^ 2 / 5) :
    4 / 5 <= mu.real {omega | A 0 * X omega ∈ relErr epsilon (A m)} := by
  have hpos : 0 < (∫ omega, X omega ∂mu) := by
    rw [hmean]
    exact div_pos (hApos m) (hApos 0)
  have hmain := relErr_four_fifths_of_sq_moment_exp hkappa hepsilon hX hpos hsq hbudget
  have hcancel : A 0 * (A m / A 0) = A m := by
    rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt (hApos 0))]
  have hset : {omega | A 0 * X omega ∈ relErr epsilon (A m)} =
      {omega | X omega ∈ relErr epsilon (∫ omega, X omega ∂mu)} := by
    ext omega
    simp only [Set.mem_setOf_eq, hmean]
    have hiff := mem_relErr_smul (ε := epsilon) (b := A m / A 0)
      (y := X omega) (hApos 0)
    rwa [hcancel] at hiff
  rwa [hset]

/-- One exact-law run of the nonuniform empirical estimator.

The additive condition on the phase factors is precisely the hypothesis of
`prod_phaseAvg_sq_moment_le_exp`; exact sample means are the consecutive ratios of `A`,
so `integral_prod_phaseAvg` and `CV.prod_fin_ratio` telescope the estimator mean. -/
theorem run_four_fifths_exact [IsProbabilityMeasure mu]
    {m k : Nat} (hk : 0 < k) {Y : Fin m -> Fin k -> Omega -> Real}
    {A : Nat -> Real} {c : Fin m -> Real} {kappa epsilon : Real}
    (hkappa : 0 <= kappa) (hepsilon : 0 < epsilon)
    (hApos : forall i, 0 < A i)
    (hL2 : forall i j, MemLp (Y i j) 2 mu)
    (hindep : CoordinateIndep Y mu)
    (hprod : MemLp (fun omega => ∏ i, avgOf k (Y i) omega) 2 mu)
    (hmean : forall i j, (∫ omega, Y i j omega ∂mu) =
      A ((i : Nat) + 1) / A (i : Nat))
    (hsq : forall i j, (∫ omega, (Y i j omega) ^ 2 ∂mu) <=
      c i * (A ((i : Nat) + 1) / A (i : Nat)) ^ 2)
    (hc : forall i, 1 <= c i)
    (hsum : (∑ i, (c i - 1) / (k : Real)) <= kappa)
    (hbudget : Real.exp kappa - 1 <= epsilon ^ 2 / 5) :
    4 / 5 <= mu.real {omega |
      A 0 * ∏ i, avgOf k (Y i) omega ∈ relErr epsilon (A m)} := by
  let nu : Fin m -> Real := fun i => A ((i : Nat) + 1) / A (i : Nat)
  have hmean' : forall i j, (∫ omega, Y i j omega ∂mu) = nu i := hmean
  have hsq' : forall i j, (∫ omega, (Y i j omega) ^ 2 ∂mu) <= c i * (nu i) ^ 2 := hsq
  have hprodMean : (∫ omega, ∏ i, avgOf k (Y i) omega ∂mu) = A m / A 0 := by
    rw [integral_prod_phaseAvg hk hL2 hindep hmean']
    exact CV.prod_fin_ratio (fun i => ne_of_gt (hApos i)) m
  have hprodSq := prod_phaseAvg_sq_moment_le_exp hk hL2 hindep hmean' hsq' hc hsum
  exact run_four_fifths_of_product_moment hkappa hepsilon hApos hprod hprodMean
    hprodSq hbudget

/-- The same exact-law theorem with the multiplicative phase budget left explicit.  This is
the direct consumer of adaptive chunk accounting such as
`Chunked.prod_globalPhaseVarFactor_le_exp`. -/
theorem run_four_fifths_exact_of_factorProduct [IsProbabilityMeasure mu]
    {m k : Nat} (hk : 0 < k) {Y : Fin m -> Fin k -> Omega -> Real}
    {A : Nat -> Real} {c : Fin m -> Real} {kappa epsilon : Real}
    (hkappa : 0 <= kappa) (hepsilon : 0 < epsilon)
    (hApos : forall i, 0 < A i)
    (hL2 : forall i j, MemLp (Y i j) 2 mu)
    (hindep : CoordinateIndep Y mu)
    (hprod : MemLp (fun omega => ∏ i, avgOf k (Y i) omega) 2 mu)
    (hmean : forall i j, (∫ omega, Y i j omega ∂mu) =
      A ((i : Nat) + 1) / A (i : Nat))
    (hsq : forall i j, (∫ omega, (Y i j omega) ^ 2 ∂mu) <=
      c i * (A ((i : Nat) + 1) / A (i : Nat)) ^ 2)
    (hfactor : (∏ i, (1 + (c i - 1) / (k : Real))) <= Real.exp kappa)
    (hbudget : Real.exp kappa - 1 <= epsilon ^ 2 / 5) :
    4 / 5 <= mu.real {omega |
      A 0 * ∏ i, avgOf k (Y i) omega ∈ relErr epsilon (A m)} := by
  let phaseMean : Fin m -> Real := fun i => A ((i : Nat) + 1) / A (i : Nat)
  have hmean' : forall i j, (∫ omega, Y i j omega ∂mu) = phaseMean i := hmean
  have hsq' : forall i j, (∫ omega, (Y i j omega) ^ 2 ∂mu) <=
      c i * (phaseMean i) ^ 2 := hsq
  have hprodMean : (∫ omega, ∏ i, avgOf k (Y i) omega ∂mu) = A m / A 0 := by
    rw [integral_prod_phaseAvg hk hL2 hindep hmean']
    exact CV.prod_fin_ratio (fun i => ne_of_gt (hApos i)) m
  have hprodSq := prod_phaseAvg_sq_moment_le_exp_of_prod hk hL2 hindep hmean'
    hsq' hfactor
  exact run_four_fifths_of_product_moment hkappa hepsilon hApos hprod hprodMean
    hprodSq hbudget

/-! ## Independent repetitions -/

/-- Median amplification of exact-law runs.  This theorem is independent of how the runs are
represented; `packed_median_accuracy_exact` below supplies all plumbing for `RunSpace`. -/
theorem median_accuracy_exact [IsProbabilityMeasure mu]
    {m k r : Nat} (hk : 0 < k) (hr : 0 < r)
    {Y : Fin r -> Fin m -> Fin k -> Omega -> Real} {z : Omega -> Real}
    {A : Nat -> Real} {c : Fin m -> Real} {kappa epsilon p : Real}
    (hkappa : 0 <= kappa) (hepsilon : 0 < epsilon)
    (hApos : forall i, 0 < A i)
    (hL2 : forall t i j, MemLp (Y t i j) 2 mu)
    (hindep : forall t, CoordinateIndep (Y t) mu)
    (hprod : forall t, MemLp (fun omega => ∏ i, avgOf k (Y t i) omega) 2 mu)
    (hmean : forall t i j, (∫ omega, Y t i j omega ∂mu) =
      A ((i : Nat) + 1) / A (i : Nat))
    (hsq : forall t i j, (∫ omega, (Y t i j omega) ^ 2 ∂mu) <=
      c i * (A ((i : Nat) + 1) / A (i : Nat)) ^ 2)
    (hc : forall i, 1 <= c i)
    (hsum : (∑ i, (c i - 1) / (k : Real)) <= kappa)
    (hbudget : Real.exp kappa - 1 <= epsilon ^ 2 / 5)
    (hrunMeas : forall t, Measurable fun omega =>
      A 0 * ∏ i, avgOf k (Y t i) omega)
    (hrunIndep : iIndepFun (fun t omega =>
      A 0 * ∏ i, avgOf k (Y t i) omega) mu)
    (hmedian : forall omega, IsMedian
      (fun t => A 0 * ∏ i, avgOf k (Y t i) omega) (z omega))
    (hp : 0 < p)
    (hrp : Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2) <= (r : Real)) :
    1 - p <= mu.real {omega | z omega ∈ relErr epsilon (A m)} := by
  apply CV.median_relErr_ge hr hrunMeas hrunIndep hmedian
    (fun t => run_four_fifths_exact hk hkappa hepsilon hApos
      (hL2 t) (hindep t) (hprod t) (hmean t) (hsq t) hc hsum hbudget)
    hp hrp

/-- Median amplification with the exact multiplicative phase budget, matching adaptive
chunk-product accounting directly. -/
theorem median_accuracy_exact_of_factorProduct [IsProbabilityMeasure mu]
    {m k r : Nat} (hk : 0 < k) (hr : 0 < r)
    {Y : Fin r -> Fin m -> Fin k -> Omega -> Real} {z : Omega -> Real}
    {A : Nat -> Real} {c : Fin m -> Real} {kappa epsilon p : Real}
    (hkappa : 0 <= kappa) (hepsilon : 0 < epsilon)
    (hApos : forall i, 0 < A i)
    (hL2 : forall t i j, MemLp (Y t i j) 2 mu)
    (hindep : forall t, CoordinateIndep (Y t) mu)
    (hprod : forall t, MemLp (fun omega => ∏ i, avgOf k (Y t i) omega) 2 mu)
    (hmean : forall t i j, (∫ omega, Y t i j omega ∂mu) =
      A ((i : Nat) + 1) / A (i : Nat))
    (hsq : forall t i j, (∫ omega, (Y t i j omega) ^ 2 ∂mu) <=
      c i * (A ((i : Nat) + 1) / A (i : Nat)) ^ 2)
    (hfactor : (∏ i, (1 + (c i - 1) / (k : Real))) <= Real.exp kappa)
    (hbudget : Real.exp kappa - 1 <= epsilon ^ 2 / 5)
    (hrunMeas : forall t, Measurable fun omega =>
      A 0 * ∏ i, avgOf k (Y t i) omega)
    (hrunIndep : iIndepFun (fun t omega =>
      A 0 * ∏ i, avgOf k (Y t i) omega) mu)
    (hmedian : forall omega, IsMedian
      (fun t => A 0 * ∏ i, avgOf k (Y t i) omega) (z omega))
    (hp : 0 < p)
    (hrp : Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2) <= (r : Real)) :
    1 - p <= mu.real {omega | z omega ∈ relErr epsilon (A m)} := by
  apply CV.median_relErr_ge hr hrunMeas hrunIndep hmedian
    (fun t => run_four_fifths_exact_of_factorProduct hk hkappa hepsilon hApos
      (hL2 t) (hindep t) (hprod t) (hmean t) (hsq t) hfactor hbudget)
    hp hrp

end CVEst

/-! ## Packed `RunSpace` adapter -/

namespace CVPacked

open MeasureTheory ProbabilityTheory

variable {r m k : Nat} {E : Type*} [MeasurableSpace E]

/-- The square of a packed elementary score has the square moment of its declared marginal. -/
theorem integral_sampleScore_sq
    (nu : Fin r -> Fin m -> Fin k -> Measure E)
    [forall t i j, IsProbabilityMeasure (nu t i j)]
    {g : Fin r -> Fin m -> Fin k -> E -> Real}
    (hg : forall t i j, Measurable (g t i j)) (t : Fin r) (i : Fin m) (j : Fin k) :
    (∫ omega, (sampleScore g t i j omega) ^ 2
      ∂(Arlib.Probability.runMeasure (Arlib.GaussianCooling.packedPhaseLaw nu))) =
      ∫ x, (g t i j x) ^ 2 ∂(nu t i j) := by
  simpa only [sampleScore] using
    (integral_sampleScore nu (fun t i j => (hg t i j).pow_const 2) t i j)

/-- Products of packed phase averages are independent across runs. -/
theorem iIndepFun_packedRuns
    (nu : Fin r -> Fin m -> Fin k -> Measure E)
    [forall t i j, IsProbabilityMeasure (nu t i j)]
    {g : Fin r -> Fin m -> Fin k -> E -> Real}
    (hg : forall t i j, Measurable (g t i j)) (a0 : Real) :
    iIndepFun (fun t omega => a0 * ∏ i, phaseAvg g t i omega)
      (Arlib.Probability.runMeasure (Arlib.GaussianCooling.packedPhaseLaw nu)) := by
  let f : Fin r -> Fin m -> (Fin k -> E) -> Real := fun t i eta =>
    CVEst.avgOf k (fun j eta' => g t i j (eta' j)) eta
  have hf : forall t i, Measurable (f t i) := by
    intro t i
    unfold f CVEst.avgOf
    exact (Finset.measurable_fun_sum _ fun j _ =>
      (hg t i j).comp (measurable_pi_apply j)).div measurable_const
  have h := Arlib.Probability.iIndepFun_runs
    (Arlib.GaussianCooling.packedPhaseLaw nu) hf a0
  have heq : (fun (t : Fin r) omega => a0 * ∏ i, phaseAvg g t i omega) =
      fun (t : Fin r) omega => a0 * ∏ (i : Fin m),
        Arlib.Probability.score f (t : Nat) (i : Nat) omega := by
    funext t omega
    apply congrArg (a0 * .)
    apply Finset.prod_congr rfl
    intro i _
    rw [Arlib.Probability.score_coe]
    rfl
  rw [heq]
  exact h

/-- Exact-law CV accuracy on the concrete packed run space.  Each `(run, phase)` coordinate
contains `k` independent elementary samples; the displayed median is the existing measurable
`medianSel` of the `r` run products. -/
theorem packed_median_accuracy_exact
    (nu : Fin r -> Fin m -> Fin k -> Measure E)
    [forall t i j, IsProbabilityMeasure (nu t i j)]
    {g : Fin r -> Fin m -> Fin k -> E -> Real}
    (hg : forall t i j, Measurable (g t i j))
    (hk : 0 < k) (hr : 0 < r)
    {A : Nat -> Real} {c : Fin m -> Real} {kappa epsilon p : Real}
    (hkappa : 0 <= kappa) (hepsilon : 0 < epsilon)
    (hApos : forall i, 0 < A i)
    (hL2 : forall t i j, MemLp (g t i j) 2 (nu t i j))
    (hprod : forall t, MemLp (fun omega => ∏ i, phaseAvg g t i omega) 2
      (Arlib.Probability.runMeasure (Arlib.GaussianCooling.packedPhaseLaw nu)))
    (hmean : forall t i j, (∫ x, g t i j x ∂(nu t i j)) =
      A ((i : Nat) + 1) / A (i : Nat))
    (hsq : forall t i j, (∫ x, (g t i j x) ^ 2 ∂(nu t i j)) <=
      c i * (A ((i : Nat) + 1) / A (i : Nat)) ^ 2)
    (hfactor : (∏ i, (1 + (c i - 1) / (k : Real))) <= Real.exp kappa)
    (hbudget : Real.exp kappa - 1 <= epsilon ^ 2 / 5)
    (hp : 0 < p)
    (hrp : Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2) <= (r : Real)) :
    1 - p <=
      (Arlib.Probability.runMeasure (Arlib.GaussianCooling.packedPhaseLaw nu)).real
        {omega | Arlib.Probability.medianSel
          (fun t => A 0 * ∏ i, phaseAvg g t i omega) ∈ relErr epsilon (A m)} := by
  let mu := Arlib.Probability.runMeasure (Arlib.GaussianCooling.packedPhaseLaw nu)
  let Y : Fin r -> Fin m -> Fin k ->
      Arlib.Probability.RunSpace (Fin k -> E) r m -> Real := sampleScore g
  apply CVEst.median_accuracy_exact_of_factorProduct (mu := mu) hk hr hkappa hepsilon hApos
    (fun t i j => memLp_sampleScore nu t i j (hL2 t i j))
    (fun t => coordinateIndep_sampleScore nu hg t)
    (fun t => by simpa only [Y, phaseAvg] using hprod t)
    (fun t i j => by
      simpa only [Y] using (integral_sampleScore nu hg t i j).trans (hmean t i j))
    (fun t i j => by
      simpa only [Y] using (integral_sampleScore_sq nu hg t i j).trans_le (hsq t i j))
    hfactor hbudget
    (fun t => (measurable_const.mul
      (Finset.measurable_fun_prod _ fun i _ => measurable_phaseAvg hg t i)))
    (by simpa only [Y, phaseAvg] using iIndepFun_packedRuns nu hg (A 0))
    (fun omega => Arlib.Probability.medianSel_isMedian _)
    hp hrp

end CVPacked

/-! ### Axiom audit -/

#print axioms Ttc.CVEst.averaged_adaptiveGlobalPhaseVarFactor_eq
#print axioms Ttc.CVEst.relErr_ge_of_sq_moment_exp
#print axioms Ttc.CVEst.relErr_four_fifths_of_sq_moment_exp
#print axioms Ttc.CVEst.run_four_fifths_of_product_moment
#print axioms Ttc.CVEst.run_four_fifths_exact
#print axioms Ttc.CVEst.run_four_fifths_exact_of_factorProduct
#print axioms Ttc.CVEst.median_accuracy_exact
#print axioms Ttc.CVEst.median_accuracy_exact_of_factorProduct
#print axioms Ttc.CVPacked.coordinateIndep_sampleScore
#print axioms Ttc.CVPacked.iIndepFun_packedRuns
#print axioms Ttc.CVPacked.packed_median_accuracy_exact

end Ttc
