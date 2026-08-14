import Ttc.Exec.CVWeightedOperationalPhaseFactor
import Ttc.Exec.CVSourceWeightedClipping

/-!
# Product arithmetic for operational weighted CV factors

An exact phase factor `C i` becomes `C i + slack i` after TV transport, and averaging
`k` independent streams turns this into

`1 + (C i + slack i - 1) / k`.

This file compares the product of those operational factors with the source product.
The entire price of the additive transport slacks is

`exp ((sum i, slack i) / k)`.

The result composes with `CVSourceWeightedClipping`: clipping contributes the separate
`exp (2*m/alpha)` term.  Thus both losses can be paid by tightening the source variance
budget by a universal constant factor, without changing its `eps^-2` sample scaling.
-/

set_option autoImplicit false

namespace Ttc.CVWeightedOperationalProductArithmetic

open scoped BigOperators
open Arlib.GaussianCooling
open Ttc.CVHybridSchedule
open Ttc.CVSourceWeightedClipping

/-- The source empirical second-moment factor in phase `i`. -/
noncomputable def sourceEmpiricalFactor
    (k : Nat) (C : Nat -> Real) (i : Nat) : Real :=
  1 + (C i - 1) / (k : Real)

/-- The operational factor after allocating additive TV-transport slack. -/
noncomputable def operationalEmpiricalFactor
    (k : Nat) (C slack : Nat -> Real) (i : Nat) : Real :=
  1 + (C i + slack i - 1) / (k : Real)

/-- Adding nonnegative scalar slack costs at most its exponential budget after
independent-stream averaging. -/
theorem operationalEmpiricalFactor_le_source_mul_exp
    {k : Nat} (hk : 0 < k) {C slack : Nat -> Real} {i : Nat}
    (hC : 1 <= C i) (hs : 0 <= slack i) :
    operationalEmpiricalFactor k C slack i <=
      sourceEmpiricalFactor k C i * Real.exp (slack i / (k : Real)) := by
  have hkR : 0 < (k : Real) := by exact_mod_cast hk
  have hbase : 1 <= sourceEmpiricalFactor k C i := by
    unfold sourceEmpiricalFactor
    have : 0 <= (C i - 1) / (k : Real) :=
      div_nonneg (by linarith) hkR.le
    linarith
  have hsdiv : 0 <= slack i / (k : Real) := div_nonneg hs hkR.le
  have hadd : operationalEmpiricalFactor k C slack i =
      sourceEmpiricalFactor k C i + slack i / (k : Real) := by
    unfold operationalEmpiricalFactor sourceEmpiricalFactor
    field_simp
    ring
  rw [hadd]
  calc
    sourceEmpiricalFactor k C i + slack i / (k : Real) <=
        sourceEmpiricalFactor k C i *
          (1 + slack i / (k : Real)) := by
      nlinarith
    _ <= sourceEmpiricalFactor k C i * Real.exp (slack i / (k : Real)) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [add_comm] using Real.add_one_le_exp (slack i / (k : Real))
      · linarith

/-- Prefix products of operational factors are bounded by the source raw product times
the exponential of the total allocated slack divided by the stream count. -/
theorem prefixMomentRatio_operational_le_source_mul_exp_sum
    {k : Nat} (hk : 0 < k) {C slack : Nat -> Real}
    (hC : forall i, 1 <= C i) (hs : forall i, 0 <= slack i) (m : Nat) :
    prefixMomentRatio (operationalEmpiricalFactor k C slack) m <=
      prefixMomentRatio (sourceEmpiricalFactor k C) m *
        Real.exp ((Finset.range m).sum (fun j => slack (j + 1) / (k : Real))) := by
  unfold prefixMomentRatio
  calc
    (Finset.range m).prod (fun j => operationalEmpiricalFactor k C slack (j + 1)) <=
        (Finset.range m).prod (fun j =>
          sourceEmpiricalFactor k C (j + 1) *
            Real.exp (slack (j + 1) / (k : Real))) := by
      apply Finset.prod_le_prod
      · intro j _
        have hkR : 0 < (k : Real) := by exact_mod_cast hk
        unfold operationalEmpiricalFactor
        have hq : 0 <= (C (j + 1) + slack (j + 1) - 1) / (k : Real) :=
          div_nonneg (by linarith [hC (j + 1), hs (j + 1)]) hkR.le
        linarith
      · intro j _
        exact operationalEmpiricalFactor_le_source_mul_exp hk (hC _) (hs _)
    _ = (Finset.range m).prod (fun j => sourceEmpiricalFactor k C (j + 1)) *
        Real.exp ((Finset.range m).sum (fun j => slack (j + 1) / (k : Real))) := by
      rw [Finset.prod_mul_distrib, <- Real.exp_sum]

/-! ## Constant per-phase operational slack -/

/-- If the scalar slack is `k*d`, averaging divides it back to the additive empirical
slack `d`.  This is the convenient allocation `d = eps^2/(C*(m+1))`. -/
theorem operationalEmpiricalFactor_mul_slack_eq_add
    {k : Nat} (hk : 0 < k) {C : Nat -> Real} (d : Real) (i : Nat) :
    operationalEmpiricalFactor k C (fun _ => (k : Real) * d) i =
      sourceEmpiricalFactor k C i + d := by
  have hkR : (0 : Real) < k := by exact_mod_cast hk
  unfold operationalEmpiricalFactor sourceEmpiricalFactor
  field_simp [ne_of_gt hkR]
  ring

/-- The abstract source empirical factor specializes exactly to `phaseVarFactor` at
sample count `k`. -/
theorem sourceEmpiricalFactor_phaseVar_eq
    {n k : Nat} {N s0 : Real} (j : Nat) :
    sourceEmpiricalFactor k
        (fun t => phaseVarFactor n 1 N s0 (t - 1)) j =
      sourceRawFactor n (k : Real) N s0 j := by
  unfold sourceEmpiricalFactor sourceRawFactor
  exact averaged_phaseVarFactor_eq (n := n) (k := (k : Real))
    (N := N) (s0 := s0) (j - 1)

/-- With scalar slack `k*d` in every phase, the operational prefix costs only
`exp(i*d)` over the paper's phase-dependent raw product. -/
theorem prefixMomentRatio_phaseVar_mul_slack_le
    {n k : Nat} (hk : 0 < k) {N s0 d : Real}
    (hphase : forall j, 1 <= phaseVarFactor n 1 N s0 j) (hd : 0 <= d)
    (i : Nat) :
    prefixMomentRatio
        (operationalEmpiricalFactor k
          (fun t => phaseVarFactor n 1 N s0 (t - 1))
          (fun _ => (k : Real) * d)) i <=
      prefixMomentRatio (sourceRawFactor n (k : Real) N s0) i *
        Real.exp ((i : Real) * d) := by
  have hkR : (0 : Real) < k := by exact_mod_cast hk
  have h := prefixMomentRatio_operational_le_source_mul_exp_sum hk
    (C := fun t => phaseVarFactor n 1 N s0 (t - 1))
    (slack := fun _ => (k : Real) * d)
    (fun t => hphase (t - 1)) (fun _ => mul_nonneg hkR.le hd) i
  have hsource : prefixMomentRatio
      (sourceEmpiricalFactor k (fun t => phaseVarFactor n 1 N s0 (t - 1))) i =
        prefixMomentRatio (sourceRawFactor n (k : Real) N s0) i := by
    unfold prefixMomentRatio
    apply Finset.prod_congr rfl
    intro j _
    exact sourceEmpiricalFactor_phaseVar_eq (n := n) (k := k)
      (N := N) (s0 := s0) (j + 1)
  rw [hsource] at h
  convert h using 1
  congr 2
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp [ne_of_gt hkR]

/-- Explicitly, choosing `d = eps^2/(D*(m+1))` spends at most `eps^2/D` over every
prefix.  The denominator `m+1` also handles the zero-phase case without branching. -/
theorem prefixMomentRatio_phaseVar_eps_slack_le
    {n k m : Nat} (hk : 0 < k) {N s0 eps D : Real}
    (hphase : forall j, 1 <= phaseVarFactor n 1 N s0 j)
    (heps : 0 <= eps) (hD : 0 < D) {i : Nat} (hi : i <= m) :
    prefixMomentRatio
        (operationalEmpiricalFactor k
          (fun t => phaseVarFactor n 1 N s0 (t - 1))
          (fun _ => (k : Real) * (eps ^ 2 / (D * ((m : Real) + 1))))) i <=
      prefixMomentRatio (sourceRawFactor n (k : Real) N s0) i *
        Real.exp (eps ^ 2 / D) := by
  have hm1 : 0 < (m : Real) + 1 := by positivity
  have hd : 0 <= eps ^ 2 / (D * ((m : Real) + 1)) := by positivity
  have h := prefixMomentRatio_phaseVar_mul_slack_le hk hphase hd i
  refine h.trans ?_
  have hiR : (i : Real) <= (m : Real) := by exact_mod_cast hi
  have hexp : Real.exp ((i : Real) *
      (eps ^ 2 / (D * ((m : Real) + 1)))) <= Real.exp (eps ^ 2 / D) := by
    apply Real.exp_le_exp.mpr
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hfrac : (i : Real) / ((m : Real) + 1) <= 1 := by
      rw [div_le_one hm1]
      linarith
    calc
      (i : Real) * (eps ^ 2 * (D * ((m : Real) + 1))⁻¹) =
          (eps ^ 2 * D⁻¹) * ((i : Real) / ((m : Real) + 1)) := by
        field_simp [ne_of_gt hD, ne_of_gt hm1]
      _ <= (eps ^ 2 * D⁻¹) * 1 := by gcongr
      _ = eps ^ 2 * D⁻¹ := by ring
  apply mul_le_mul_of_nonneg_left hexp
  unfold prefixMomentRatio
  apply Finset.prod_nonneg
  intro j _
  rw [← sourceEmpiricalFactor_phaseVar_eq (n := n) (k := k)
    (N := N) (s0 := s0) (j + 1)]
  unfold sourceEmpiricalFactor
  have hquot : 0 <=
      (phaseVarFactor n 1 N s0 (j + 1 - 1) - 1) / (k : Real) :=
    div_nonneg (by linarith [hphase (j + 1 - 1)]) (by positivity)
  linarith

/-- Combined operational-slack and clipping comparison.  This is the direct reusable
interface for the weighted recursion: `kappa` is any source raw-product exponent,
`slackBudget` pays TV transport, and `2*m/alpha` pays clipping. -/
theorem clipped_operational_prefix_le_exp
    {k : Nat} (hk : 0 < k) {C slack : Nat -> Real}
    (hC : forall i, 1 <= C i) (hs : forall i, 0 <= slack i)
    {alpha kappa slackBudget : Real} (halpha : 2 <= alpha) {m : Nat}
    (hsource : forall i, i <= m ->
      prefixMomentRatio (sourceEmpiricalFactor k C) i <= Real.exp kappa)
    (hslack : forall i, i <= m ->
      (Finset.range i).sum (fun j => slack (j + 1) / (k : Real)) <= slackBudget) :
    forall i, i <= m ->
      prefixMomentRatio (fun j =>
        clippedFactor alpha (operationalEmpiricalFactor k C slack j)) i <=
          Real.exp (kappa + slackBudget + 2 * (i : Real) / alpha) := by
  intro i hi
  have hop := prefixMomentRatio_operational_le_source_mul_exp_sum hk hC hs i
  have hoper0 : forall j, 0 <= operationalEmpiricalFactor k C slack j := by
    intro j
    unfold operationalEmpiricalFactor
    have hkR : 0 < (k : Real) := by exact_mod_cast hk
    have : 0 <= C j + slack j - 1 := by linarith [hC j, hs j]
    positivity
  have hoper : prefixMomentRatio (operationalEmpiricalFactor k C slack) i <=
      Real.exp (kappa + slackBudget) := by
    calc
      prefixMomentRatio (operationalEmpiricalFactor k C slack) i <=
          prefixMomentRatio (sourceEmpiricalFactor k C) i *
            Real.exp ((Finset.range i).sum
              (fun j => slack (j + 1) / (k : Real))) := hop
      _ <= Real.exp kappa * Real.exp slackBudget := by
        exact mul_le_mul (hsource i hi)
          (Real.exp_le_exp.mpr (hslack i hi)) (by positivity) (by positivity)
      _ = Real.exp (kappa + slackBudget) := by rw [Real.exp_add]
  rw [prefixMomentRatio_clippedFactor]
  have hdenEq :
      ((1 - 1 / (2 * alpha)) ^ (2 * i))⁻¹ =
        (1 / (1 - 1 / (2 * alpha)) ^ 2) ^ i := by
    simp only [one_div, <- inv_pow, pow_mul]
  rw [div_eq_mul_inv, hdenEq]
  calc
    prefixMomentRatio (operationalEmpiricalFactor k C slack) i *
        (1 / (1 - 1 / (2 * alpha)) ^ 2) ^ i <=
      Real.exp (kappa + slackBudget) *
        Real.exp (2 * (i : Real) / alpha) :=
      mul_le_mul hoper (clippingInflation_pow_le_exp halpha i)
        (by positivity) (by positivity)
    _ = Real.exp (kappa + slackBudget + 2 * (i : Real) / alpha) := by
      calc
        Real.exp (kappa + slackBudget) * Real.exp (2 * (i : Real) / alpha) =
            Real.exp ((kappa + slackBudget) + 2 * (i : Real) / alpha) :=
          (Real.exp_add _ _).symm
        _ = Real.exp (kappa + slackBudget + 2 * (i : Real) / alpha) := by ring

/-- A final target follows once the three explicit exponent budgets fit it.  This form
is convenient for changing the universal constant in the source sample count. -/
theorem clipped_operational_prefix_le_target
    {k : Nat} (hk : 0 < k) {C slack : Nat -> Real}
    (hC : forall i, 1 <= C i) (hs : forall i, 0 <= slack i)
    {alpha kappa slackBudget target : Real} (halpha : 2 <= alpha) {m : Nat}
    (hsource : forall i, i <= m ->
      prefixMomentRatio (sourceEmpiricalFactor k C) i <= Real.exp kappa)
    (hslack : forall i, i <= m ->
      (Finset.range i).sum (fun j => slack (j + 1) / (k : Real)) <= slackBudget)
    (hbudget : Real.exp (kappa + slackBudget + 2 * (m : Real) / alpha) <= target) :
    forall i, i <= m ->
      prefixMomentRatio (fun j =>
        clippedFactor alpha (operationalEmpiricalFactor k C slack j)) i <= target := by
  intro i hi
  have hiR : (i : Real) <= (m : Real) := by exact_mod_cast hi
  have halpha0 : 0 < alpha := lt_of_lt_of_le (by norm_num) halpha
  calc
    prefixMomentRatio (fun j =>
        clippedFactor alpha (operationalEmpiricalFactor k C slack j)) i <=
      Real.exp (kappa + slackBudget + 2 * (i : Real) / alpha) :=
        clipped_operational_prefix_le_exp hk hC hs halpha hsource hslack i hi
    _ <= Real.exp (kappa + slackBudget + 2 * (m : Real) / alpha) := by
      apply Real.exp_le_exp.mpr
      have hmul : 2 * (i : Real) <= 2 * (m : Real) := by linarith
      have hdiv : 2 * (i : Real) / alpha <= 2 * (m : Real) / alpha :=
        (div_le_div_iff_of_pos_right halpha0).2 hmul
      linarith
    _ <= target := hbudget

#print axioms operationalEmpiricalFactor_le_source_mul_exp
#print axioms prefixMomentRatio_operational_le_source_mul_exp_sum
#print axioms clipped_operational_prefix_le_exp
#print axioms clipped_operational_prefix_le_target

end Ttc.CVWeightedOperationalProductArithmetic
