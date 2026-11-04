import Kr25Ssmxt.Analysis.NormalizedHitAndRunGeometry
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Expected number of independent rejection attempts

`geometricMeasure p` counts failed proposals. The operation trace charges one
additional attempt for the successful proposal.
-/

namespace Kr25Ssmxt

open MeasureTheory ProbabilityTheory

theorem geometricMeasure_integral_attempts (p : unitInterval) (hp : 0 < (p : Real)) :
    ∫ failures : Nat, ((failures : Real) + 1) ∂geometricMeasure p =
      (p : Real)⁻¹ := by
  let r : Real := 1 - p
  have hr0 : 0 ≤ r := by dsimp [r]; linarith [p.property.2]
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hrnorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hs1 : Summable (fun n : Nat => (n : Real) * r ^ n) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hrnorm).summable
  have hs2 : Summable (fun n : Nat => r ^ n) :=
    summable_geometric_of_norm_lt_one hrnorm
  have hpne : p ≠ 0 := by
    intro h
    exact hp.ne' (congrArg Subtype.val h)
  rw [integral_geometricMeasure hpne]
  simp only [smul_eq_mul]
  calc
    (∑' n : Nat, (1 - p : Real) ^ n * p * ((n : Real) + 1)) =
        (p : Real) * ∑' n : Nat, ((n : Real) * r ^ n + r ^ n) := by
      rw [← tsum_mul_left]
      congr 1
      funext n
      dsimp [r]
      ring
    _ = (p : Real) * ((∑' n : Nat, (n : Real) * r ^ n) +
        ∑' n : Nat, r ^ n) := by rw [hs1.tsum_add hs2]
    _ = (p : Real)⁻¹ := by
      rw [tsum_coe_mul_geometric_of_norm_lt_one hrnorm,
        tsum_geometric_of_lt_one hr0 hr1]
      dsimp [r]
      have hp0 : (p : Real) ≠ 0 := hp.ne'
      field_simp [hp0]
      <;> ring

theorem geometricMeasure_integrable_attempts (p : unitInterval)
    (hp : 0 < (p : Real)) :
    Integrable (fun failures : Nat => (failures : Real) + 1) (geometricMeasure p) := by
  let r : Real := 1 - p
  have hr0 : 0 ≤ r := by dsimp [r]; linarith [p.property.2]
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hrnorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hs1 : Summable (fun n : Nat => (n : Real) * r ^ n) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hrnorm).summable
  have hs2 : Summable (fun n : Nat => r ^ n) :=
    summable_geometric_of_norm_lt_one hrnorm
  have hs : Summable (fun n : Nat => (r ^ n * (p : Real)) * ‖(n : Real) + 1‖) := by
    have hs' : Summable (fun n : Nat => (p : Real) * ((n : Real) * r ^ n + r ^ n)) :=
      (hs1.add hs2).mul_left _
    have hfun : (fun n : Nat => (r ^ n * (p : Real)) * ‖(n : Real) + 1‖) =
        (fun n : Nat => (p : Real) * ((n : Real) * r ^ n + r ^ n)) := by
      funext n
      have hn : 0 ≤ (n : Real) + 1 := by positivity
      simp only [Real.norm_eq_abs, abs_of_nonneg hn]
      ring
    rw [hfun]
    exact hs'
  have hpne : p ≠ 0 := by
    intro h
    exact hp.ne' (congrArg Subtype.val h)
  exact (integrable_geometricMeasure_iff hpne).2 (by simpa [r] using hs)

theorem geometricMeasure_lintegral_attempts (p : unitInterval)
    (hp : 0 < (p : Real)) :
    ∫⁻ failures : Nat, ((failures + 1 : Nat) : ENNReal) ∂geometricMeasure p =
      ENNReal.ofReal ((p : Real)⁻¹) := by
  have hInt := geometricMeasure_integrable_attempts p hp
  have hnonneg : 0 ≤ᵐ[geometricMeasure p]
      (fun failures : Nat => (failures : Real) + 1) :=
    Filter.Eventually.of_forall (fun _ => by positivity)
  have h := ofReal_integral_eq_lintegral_ofReal hInt hnonneg
  rw [geometricMeasure_integral_attempts p hp] at h
  have hfun : (fun n : Nat => ENNReal.ofReal ((n : Real) + 1)) =
      (fun n : Nat => ((n + 1 : Nat) : ENNReal)) := by
    funext n
    simp [ENNReal.ofReal_add, Nat.cast_add]
  rw [← hfun]
  exact h.symm

theorem geometricMeasure_expected_attempts_le_two (p : unitInterval)
    (hp : (1 / 2 : Real) ≤ p) :
    ∫⁻ failures : Nat, ((failures + 1 : Nat) : ENNReal) ∂geometricMeasure p ≤ 2 := by
  have hp0 : 0 < (p : Real) := by linarith
  rw [geometricMeasure_lintegral_attempts p hp0]
  have htwo : (2 : ENNReal) = ENNReal.ofReal 2 := by norm_num
  rw [htwo]
  apply ENNReal.ofReal_le_ofReal
  rw [inv_eq_one_div]
  exact (div_le_iff₀ hp0).2 (by nlinarith)

theorem acceptedRoundedWithAttempts_expected_attempts {n : Nat}
    (mu : Measure (EuclideanSpace Real (Fin n))) (P : PolytopeData n) (b : Nat)
    [IsProbabilityMeasure (acceptedRoundedLatticeLaw mu P b)] :
    ∫⁻ result, (result.2 : ENNReal) ∂acceptedRoundedWithAttempts mu P b =
      ∫⁻ failures : Nat, ((failures + 1 : Nat) : ENNReal) ∂
        geometricMeasure (roundedAcceptanceProbability mu P b) := by
  unfold acceptedRoundedWithAttempts
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  change (∫⁻ pair : Nat × LatticePoint n,
      ((pair.1 + 1 : Nat) : ENNReal) ∂
        (geometricMeasure (roundedAcceptanceProbability mu P b)).prod
          (acceptedRoundedLatticeLaw mu P b)) = _
  rw [lintegral_prod _ (by fun_prop)]
  simp only [lintegral_const, measure_univ, mul_one]

theorem normalizedHitAndRunPointWithCost_expected_bound {n : Nat}
    (P : PolytopeData n) (b : Nat) (eta : Real)
    [IsProbabilityMeasure (acceptedRoundedLatticeLaw
      (normalizedHitAndRunContinuousLaw P b eta) P b)]
    (haccept : (1 / 2 : Real) ≤
      (roundedAcceptanceProbability (normalizedHitAndRunContinuousLaw P b eta) P b : Real)) :
    ∫⁻ result, (result.2 : ENNReal) ∂normalizedHitAndRunPointWithCostLaw P b eta ≤
      2 * TTCRuntime.samplingAttemptOperations n P.presentation.facetCount
        (normalizedHitAndRunSteps P b eta) := by
  unfold normalizedHitAndRunPointWithCostLaw
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  simp only [Nat.cast_mul]
  rw [lintegral_mul_const _ (by fun_prop)]
  rw [acceptedRoundedWithAttempts_expected_attempts]
  exact mul_le_mul_of_nonneg_right (geometricMeasure_expected_attempts_le_two _ haccept)
    (by positivity)

theorem normalizedHitAndRunBatchWithCost_expected_bound {n : Nat}
    (P : PolytopeData n) (count b : Nat) (eta : Real)
    [IsProbabilityMeasure (acceptedRoundedLatticeLaw
      (normalizedHitAndRunContinuousLaw P b eta) P b)]
    (haccept : (1 / 2 : Real) ≤
      (roundedAcceptanceProbability (normalizedHitAndRunContinuousLaw P b eta) P b : Real)) :
    ∫⁻ result, (result.2 : ENNReal) ∂
        normalizedHitAndRunBatchWithCostLaw P count b eta ≤
      count * (2 * TTCRuntime.samplingAttemptOperations n P.presentation.facetCount
        (normalizedHitAndRunSteps P b eta)) := by
  let μ := normalizedHitAndRunPointWithCostLaw P b eta
  letI : IsProbabilityMeasure
      (acceptedRoundedWithAttempts (normalizedHitAndRunContinuousLaw P b eta) P b) := by
    unfold acceptedRoundedWithAttempts
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure μ := by
    unfold μ normalizedHitAndRunPointWithCostLaw
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  letI : ∀ _ : Fin count, IsProbabilityMeasure μ := fun _ => inferInstance
  unfold normalizedHitAndRunBatchWithCostLaw
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  simp only [Nat.cast_sum]
  rw [lintegral_finsetSum Finset.univ (by intros; fun_prop)]
  have hcoord (i : Fin count) :
      (∫⁻ draws : Fin count → LatticePoint n × Nat,
        ((draws i).2 : ENNReal) ∂Measure.pi (fun _ : Fin count => μ)) =
      ∫⁻ result, (result.2 : ENNReal) ∂μ := by
    have hmap : (Measure.pi (fun _ : Fin count => μ)).map (Function.eval i) = μ :=
      (measurePreserving_eval (μ := fun _ : Fin count => μ) i).map_eq
    calc
      _ = ∫⁻ result, (result.2 : ENNReal) ∂
          (Measure.pi (fun _ : Fin count => μ)).map (Function.eval i) := by
        rw [lintegral_map (by fun_prop) (by fun_prop)]
      _ = _ := by rw [hmap]
  dsimp only [μ] at hcoord
  simp_rw [hcoord]
  have hpoint := normalizedHitAndRunPointWithCost_expected_bound P b eta haccept
  calc
    (∑ _i : Fin count, ∫⁻ result, (result.2 : ENNReal) ∂μ) =
        count * (∫⁻ result, (result.2 : ENNReal) ∂μ) := by simp
    _ ≤ count * (2 * TTCRuntime.samplingAttemptOperations n P.presentation.facetCount
        (normalizedHitAndRunSteps P b eta)) :=
      mul_le_mul_of_nonneg_left hpoint (by positivity)

end Kr25Ssmxt
