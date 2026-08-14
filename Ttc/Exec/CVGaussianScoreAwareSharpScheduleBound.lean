import Ttc.Exec.CVGaussianSourceSharpCost
import Ttc.Exec.CVGaussianAdaptiveMixing

/-!
# Deterministic cost of the score-aware Gaussian reference schedule

The retained-history reference has a noncompounding warmness constant.  This file
separates that reference warmness from the (possibly much larger) warmness argument fed
to the operational mixing deadline and computes the resulting phase-cost sum.

For the score-aware operation every retry in phase `i` uses the same deadline.  Hence its
reference mean is exactly

`10 * retries_i * deadline_i * referenceWarm`.

The final theorems give both the exact phase sum and a uniform deterministic upper bound.
They also expose the precise remaining arithmetic obligation for comparison with the
source `eps^-2` envelope.  In particular, no compounding operational warmness multiplies
the expected reference cost; it occurs only inside the logarithm in the deadline.
-/

namespace Ttc.CVGaussianScoreAwareSharpScheduleBound

open MeasureTheory
open Ttc.CVGaussianSourceSharpCost
open Ttc.CVGaussianScoreAwareParameters
open Ttc.CVGaussianAdaptiveMixing
open Ttc.CVConcreteAugmentedRetryCutoffBudget
open Ttc.CVSourcePolynomialCutoffCapstone
open scoped ENNReal BigOperators

/-- The source adjacent-Gaussian reference warmness, used uniformly at every active
phase. -/
noncomputable def gaussianReferenceWarm : ENNReal :=
  ENNReal.ofReal (2 * Real.exp 1)

theorem gaussianReferenceWarm_ne_top : gaussianReferenceWarm ≠ ⊤ := by
  unfold gaussianReferenceWarm
  exact ENNReal.ofReal_ne_top

theorem gaussianReferenceWarm_toReal :
    gaussianReferenceWarm.toReal = 2 * Real.exp 1 := by
  rw [gaussianReferenceWarm, ENNReal.toReal_ofReal]
  positivity

theorem gaussianReferenceWarm_toReal_nonneg :
    0 ≤ gaussianReferenceWarm.toReal := by
  rw [gaussianReferenceWarm_toReal]
  positivity

/-- The literal score-aware retry count is logarithmic in the reciprocal selected
share.  This is the schedule-specific `L` estimate, before lower-bounding the concrete
moment slack. -/
theorem scoreAwareRetries_lt_logb
    {m k : Nat} {eps : Real} {slack boundSq : Nat → Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hslack : ∀ i, 0 < slack i) (hbound : ∀ i, 0 < boundSq i) (i : Nat) :
    (scoreAwareRetries m k eps slack boundSq i : Real) <
      16 * (Real.logb 2
        (1 / scoreAwareShare m k eps slack boundSq i) + 1) := by
  have hindex := Ttc.CVAdaptive.explicitDyadicTailIndex_lt_logb_add_one
    (scoreAwareShare_pos (m := m) (k := k) heps hslack hbound i)
    (scoreAwareShare_lt_one (m := m) (k := k) heps heps1 i)
  rw [scoreAwareRetries]
  push_cast
  nlinarith

/-- The real expression rounded by `adjustableSpeedyDeadline`. -/
noncomputable def adjustableSpeedyDeadlineExpression
    (n : Nat) (delta sigmaSq : Real) (M eta : ENNReal) : Real :=
  4 * 640 ^ 2 * sigmaSq * (n : Real) *
      (Real.log M.toReal + 2 * Real.log (1 / eta.toReal)) /
        (delta * Real.log 2) ^ 2 + 1

/-- Monotonicity of the ceiling turns any real deadline estimate into a natural deadline
estimate.  This isolates the remaining logarithmic warmness/share calculation. -/
theorem adjustableSpeedyDeadline_le_ceil_of_expression_le
    {n : Nat} {delta sigmaSq : Real} {M eta : ENNReal} {B : Real}
    (hB : adjustableSpeedyDeadlineExpression n delta sigmaSq M eta ≤ B) :
    adjustableSpeedyDeadline n delta sigmaSq M eta ≤ ⌈B⌉₊ + 1 := by
  unfold adjustableSpeedyDeadlineExpression at hB
  unfold adjustableSpeedyDeadline
  exact Nat.add_le_add_right (Nat.ceil_mono hB) 1

/-- A concrete obstruction to manufacturing `T` from the current operational interface:
even with `n = delta = sigmaSq = eta = 1`, the literal adjustable deadline is unbounded as
the admitted operational warmness grows.  Thus a polynomial `T` requires an upper bound
for the chosen warmness recurrence; positivity/finiteness alone cannot suffice. -/
theorem exists_adjustableSpeedyDeadline_gt (T : Nat) :
    ∃ M : ENNReal, M ≠ ⊤ ∧
      T < adjustableSpeedyDeadline 1 1 1 M 1 := by
  let A : Real := ((T : Real) + 1) * Real.log 2 ^ 2 + 1
  let M : ENNReal := ENNReal.ofReal (Real.exp A)
  refine ⟨M, by simp [M], ?_⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hspec := adjustableSpeedyDeadline_spec 1 1 1 M 1
  have hMreal : M.toReal = Real.exp A := by
    simp [M, (Real.exp_pos A).le]
  rw [hMreal, Real.log_exp, ENNReal.toReal_one, one_div_one, Real.log_one] at hspec
  have hstrict : (T : Real) <
      4 * 640 ^ 2 * 1 * ((1 : Nat) : Real) * (A + 2 * 0) /
          (1 * Real.log 2) ^ 2 + 1 := by
    dsimp only [A]
    norm_num only [Nat.cast_one, mul_one, one_mul, mul_zero, add_zero]
    field_simp [hlog2.ne']
    have hT0 : (0 : Real) ≤ T := by positivity
    nlinarith [sq_pos_of_pos hlog2]
  have hcast : (T : Real) <
      (adjustableSpeedyDeadline 1 1 1 M 1 : Real) := hstrict.trans_le hspec
  exact_mod_cast hcast

/-- The literal score-aware schedule.  The attempt index is ignored because every retry
in one phase is run to the same adjustable-radius mixing deadline. -/
noncomputable def scoreAwareGaussianSteps
    (n : Nat) (delta : Real) (sigmaSq : Nat → Real)
    (m k : Nat) (eps : Real) (slack boundSq : Nat → Real)
    (operationalWarm : Nat → ENNReal) (i _attempt : Nat) : Nat :=
  adjustableSpeedyDeadline n delta (sigmaSq i)
    ((2 * operationalWarm i) / scoreAwareEta m k eps slack boundSq i)
    (scoreAwareZeta m k eps slack boundSq i)

/-- Exact retry-envelope formula for a phase whose retry attempts all use one deadline. -/
theorem retryReferenceMeanEnvelope_const
    (M : Real) (T L : Nat) :
    retryReferenceMeanEnvelope M (fun _ ↦ T) L =
      10 * (L : Real) * (T : Real) * M := by
  unfold retryReferenceMeanEnvelope
  simp
  ring

/-- Exact active-phase formula for the concrete score-aware schedule, with the reference
warmness kept separate from the operational warmness used to select the deadline. -/
theorem gaussianActiveMeanEnvelopeReal_scoreAware
    (n m k : Nat) (eps delta : Real) (sigmaSq : Nat → Real)
    (slack boundSq : Nat → Real) (operationalWarm : Nat → ENNReal) (i : Nat) :
    gaussianActiveMeanEnvelopeReal m (fun _ ↦ gaussianReferenceWarm)
        (scoreAwareGaussianSteps n delta sigmaSq m k eps slack boundSq operationalWarm)
        (scoreAwareRetries m k eps slack boundSq) i =
      if i + 1 < m then
        10 * (scoreAwareRetries m k eps slack boundSq i : Real) *
          (adjustableSpeedyDeadline n delta (sigmaSq i)
            ((2 * operationalWarm i) / scoreAwareEta m k eps slack boundSq i)
            (scoreAwareZeta m k eps slack boundSq i) : Real) *
          (2 * Real.exp 1)
      else 0 := by
  unfold gaussianActiveMeanEnvelopeReal scoreAwareGaussianSteps
  split_ifs
  · rw [retryReferenceMeanEnvelope_const, gaussianReferenceWarm_toReal]
  · rfl

/-- Exact deterministic phase sum.  This is the sharp residual that must be bounded by
the source envelope; it contains no multiplicative compounding warmness. -/
theorem sharpReferencePhaseSum_scoreAware_eq
    (n m k : Nat) (eps delta : Real) (sigmaSq : Nat → Real)
    (slack boundSq : Nat → Real) (operationalWarm : Nat → ENNReal) :
    (k : Real) * ∑ i ∈ Finset.range m,
        gaussianActiveMeanEnvelopeReal m (fun _ ↦ gaussianReferenceWarm)
          (scoreAwareGaussianSteps n delta sigmaSq m k eps slack boundSq operationalWarm)
          (scoreAwareRetries m k eps slack boundSq) i =
      (k : Real) * ∑ i ∈ Finset.range m,
        if i + 1 < m then
          10 * (scoreAwareRetries m k eps slack boundSq i : Real) *
            (adjustableSpeedyDeadline n delta (sigmaSq i)
              ((2 * operationalWarm i) / scoreAwareEta m k eps slack boundSq i)
              (scoreAwareZeta m k eps slack boundSq i) : Real) *
            (2 * Real.exp 1)
        else 0 := by
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact gaussianActiveMeanEnvelopeReal_scoreAware n m k eps delta sigmaSq
    slack boundSq operationalWarm i

/-- A uniform retry/deadline bound gives the expected elementary product bound. -/
theorem sharpReferencePhaseSum_scoreAware_le_uniform
    (n m k L T : Nat) (eps delta : Real) (sigmaSq : Nat → Real)
    (slack boundSq : Nat → Real) (operationalWarm : Nat → ENNReal)
    (hretries : ∀ i < m, scoreAwareRetries m k eps slack boundSq i ≤ L)
    (hdeadline : ∀ i < m,
      adjustableSpeedyDeadline n delta (sigmaSq i)
        ((2 * operationalWarm i) / scoreAwareEta m k eps slack boundSq i)
        (scoreAwareZeta m k eps slack boundSq i) ≤ T) :
    (k : Real) * ∑ i ∈ Finset.range m,
        gaussianActiveMeanEnvelopeReal m (fun _ ↦ gaussianReferenceWarm)
          (scoreAwareGaussianSteps n delta sigmaSq m k eps slack boundSq operationalWarm)
          (scoreAwareRetries m k eps slack boundSq) i ≤
      10 * (k : Real) * (m : Real) * (L : Real) * (T : Real) *
        (2 * Real.exp 1) := by
  rw [sharpReferencePhaseSum_scoreAware_eq]
  have hk0 : (0 : Real) ≤ k := by positivity
  rw [show 10 * (k : Real) * (m : Real) * (L : Real) * (T : Real) *
      (2 * Real.exp 1) =
    (k : Real) * (10 * (m : Real) * (L : Real) * (T : Real) *
      (2 * Real.exp 1)) by ring]
  apply mul_le_mul_of_nonneg_left _ hk0
  calc
    (∑ i ∈ Finset.range m,
        if i + 1 < m then
          10 * (scoreAwareRetries m k eps slack boundSq i : Real) *
            (adjustableSpeedyDeadline n delta (sigmaSq i)
              ((2 * operationalWarm i) / scoreAwareEta m k eps slack boundSq i)
              (scoreAwareZeta m k eps slack boundSq i) : Real) *
            (2 * Real.exp 1)
        else 0) ≤
      ∑ _i ∈ Finset.range m,
        10 * (L : Real) * (T : Real) * (2 * Real.exp 1) := by
      apply Finset.sum_le_sum
      intro i hi
      have him : i < m := Finset.mem_range.mp hi
      split_ifs
      · have hr : (scoreAwareRetries m k eps slack boundSq i : Real) ≤ L := by
          exact_mod_cast hretries i him
        have hd : (adjustableSpeedyDeadline n delta (sigmaSq i)
            ((2 * operationalWarm i) / scoreAwareEta m k eps slack boundSq i)
            (scoreAwareZeta m k eps slack boundSq i) : Real) ≤ T := by
          exact_mod_cast hdeadline i him
        gcongr
      · positivity
    _ = 10 * (m : Real) * (L : Real) * (T : Real) * (2 * Real.exp 1) := by
      simp
      ring

/-- Direct source-budget adapter.  The only remaining premise is now an ordinary real
inequality between the explicit uniform schedule product and the source envelope. -/
theorem sharpReferencePhaseSum_scoreAware_le_sourceBudget
    {runtimeConstant radius : Real}
    (n m k L T : Nat) (eps delta : Real) (sigmaSq : Nat → Real)
    (slack boundSq : Nat → Real) (operationalWarm : Nat → ENNReal)
    (hretries : ∀ i < m, scoreAwareRetries m k eps slack boundSq i ≤ L)
    (hdeadline : ∀ i < m,
      adjustableSpeedyDeadline n delta (sigmaSq i)
        ((2 * operationalWarm i) / scoreAwareEta m k eps slack boundSq i)
        (scoreAwareZeta m k eps slack boundSq i) ≤ T)
    (hsource : 10 * (k : Real) * (m : Real) * (L : Real) * (T : Real) *
        (2 * Real.exp 1) ≤
      sourceOneRunQueryEnvelope runtimeConstant n radius eps) :
    (k : ENNReal) * ∑ i ∈ Finset.range m,
        gaussianActiveMeanEnvelope m (fun _ ↦ gaussianReferenceWarm)
          (scoreAwareGaussianSteps n delta sigmaSq m k eps slack boundSq operationalWarm)
          (scoreAwareRetries m k eps slack boundSq) i ≤
      sourceOneRunQueryBudget runtimeConstant n radius eps := by
  apply sharpPhaseSum_le_sourceBudget_of_real
  exact (sharpReferencePhaseSum_scoreAware_le_uniform n m k L T eps delta sigmaSq
    slack boundSq operationalWarm hretries hdeadline).trans hsource

#print axioms gaussianActiveMeanEnvelopeReal_scoreAware
#print axioms scoreAwareRetries_lt_logb
#print axioms adjustableSpeedyDeadline_le_ceil_of_expression_le
#print axioms exists_adjustableSpeedyDeadline_gt
#print axioms sharpReferencePhaseSum_scoreAware_eq
#print axioms sharpReferencePhaseSum_scoreAware_le_uniform
#print axioms sharpReferencePhaseSum_scoreAware_le_sourceBudget

end Ttc.CVGaussianScoreAwareSharpScheduleBound
