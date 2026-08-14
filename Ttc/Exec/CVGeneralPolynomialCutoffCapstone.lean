import Ttc.Exec.CVConcreteAugmentedRetryCutoffBudget
import Ttc.Volume.CVCorrectedExplicitRadiusRuntime
import Ttc.Volume.ExpectedQueryBodyRegularization

/-!
# Generalized polynomial cutoff capstone for continuing-retry CV

The conservative corrected dependence parameter forces an `eps^-10` factor into a
per-phase Markov cutoff.  This file therefore provides a separate, honestly named public
capstone parameterized by the resulting input-dependent real envelope.  It does not use
or claim the sharper `sourceOneRunQueryEnvelope` from Cousins--Vempala.
-/

namespace Ttc.CVGeneralPolynomialCutoffCapstone

open MeasureTheory ProbabilityTheory Set
open Arlib.Probability Arlib.GaussianCooling
open Ttc.CVConcreteAugmentedRetryCutoffBudget
open Ttc.CVContinuingRetryParameters
open Ttc.CVSourcePolynomialCutoffCapstone
open Ttc.CVCorrectedRuntime
open Ttc.CVAdaptive
open Ttc.AdjustableLazyProperCost
open Ttc.CVCostedRuntimeCutoff
open Ttc.CVCostedAdjustableOuterMedian
open scoped ENNReal Classical BigOperators

/-- Exact expansion explaining the degraded accuracy exponent: the current corrected
allowance gives `1 / correctedNu = 100000^5 (m+1)^5 / eps^10`. -/
theorem continuingOneRunQueryEnvelope_eq_expanded
    {B eps : Real} {phases m : Nat} (heps : 0 < eps) :
    continuingOneRunQueryEnvelope B phases m eps =
      (phases : Real) *
        (8 * (B + 1) * (100000 ^ 5 * ((m : Real) + 1) ^ 5) / eps ^ 10) := by
  unfold continuingOneRunQueryEnvelope Ttc.CVCorrected.correctedNu
    Ttc.CVCorrected.correctedAlpha
  field_simp [ne_of_gt heps]

/-- Exact real warm factor used for the ideal reference seed in timeout analysis. -/
noncomputable def continuingReferenceWarm : Real := 2 * Real.exp 1

/-- Significant-survival mixing uses the conditioned warmness `M / eta`. -/
noncomputable def continuingConditionedWarm (m : Nat) (eps : Real) : Real :=
  continuingReferenceWarm / continuingShare m eps

/-- Real mixing tolerance corresponding to `continuingZeta`. -/
noncomputable def continuingMixTolerance (m : Nat) (eps : Real) : Real :=
  Ttc.CVCorrected.correctedNu m eps / 256

/-- One uniform retry deadline obtained from the adjustable-radius formula. -/
noncomputable def continuingUniformMixingSteps
    (n : Nat) (q : Real) (m : Nat) (eps : Real) : Nat :=
  ⌈adjustableMixingDeadline n q (continuingConditionedWarm m eps)
    (continuingMixTolerance m eps)⌉₊ + 1

theorem continuingUniformMixingDeadline_le_steps
    (n : Nat) (q : Real) (m : Nat) (eps : Real) :
    adjustableMixingDeadline n q (continuingConditionedWarm m eps)
        (continuingMixTolerance m eps) ≤
      (continuingUniformMixingSteps n q m eps : Real) := by
  have hceil := Nat.le_ceil (adjustableMixingDeadline n q
    (continuingConditionedWarm m eps) (continuingMixTolerance m eps))
  rw [continuingUniformMixingSteps]
  push_cast
  linarith

theorem continuingUniformMixingSteps_cast_lt
    {n m : Nat} {q eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (continuingUniformMixingSteps n q m eps : Real) <
      adjustableMixingDeadline n q (continuingConditionedWarm m eps)
        (continuingMixTolerance m eps) + 2 := by
  have hshare : 0 < continuingShare m eps := continuingShare_pos heps
  have hM : 0 < continuingConditionedWarm m eps := by
    unfold continuingConditionedWarm continuingReferenceWarm
    positivity
  have htol : 0 < continuingMixTolerance m eps := by
    unfold continuingMixTolerance
    positivity [correctedNu_pos (m := m) heps]
  have hdeadline : 0 ≤ adjustableMixingDeadline n q
      (continuingConditionedWarm m eps) (continuingMixTolerance m eps) := by
    unfold adjustableMixingDeadline
    have hlogM : 0 ≤ Real.log (continuingConditionedWarm m eps) := by
      apply Real.log_nonneg
      unfold continuingConditionedWarm
      rw [le_div_iff₀ hshare]
      have href : 1 ≤ continuingReferenceWarm := by
        unfold continuingReferenceWarm
        have hexp : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
        nlinarith
      have hshare1 : continuingShare m eps ≤ 1 :=
        (continuingShare_lt_one heps heps1).le
      simpa using hshare1.trans href
    have htol1 : continuingMixTolerance m eps ≤ 1 := by
      unfold continuingMixTolerance
      have hnu := correctedNu_le_one (m := m) heps heps1
      nlinarith
    have hinv : 1 ≤ 1 / continuingMixTolerance m eps := by
      rw [le_div_iff₀ htol]
      simpa using htol1
    have hlogtol : 0 ≤ Real.log (1 / continuingMixTolerance m eps) :=
      Real.log_nonneg hinv
    have hlogs : 0 ≤ Real.log (continuingConditionedWarm m eps) +
        2 * Real.log (1 / continuingMixTolerance m eps) := by positivity
    have hnum : 0 ≤ 4 * 640 ^ 2 * (max 8 (2 * q)) ^ 2 * (n : Real) ^ 2 *
        (Real.log (continuingConditionedWarm m eps) +
          2 * Real.log (1 / continuingMixTolerance m eps)) := by positivity
    exact add_nonneg (div_nonneg hnum (sq_nonneg (Real.log 2))) (by norm_num)
  have hceil := Nat.ceil_lt_add_one hdeadline
  rw [continuingUniformMixingSteps]
  push_cast
  linarith

/-! ## Concrete corrected schedule envelope -/

noncomputable def generalizedPhaseCount (n : Nat) (R eps : Real) : Nat :=
  terminalPhaseCount n R (polynomialEndpointSigmaSq n (eps / 4))

noncomputable def generalizedSampleCount (n : Nat) (R eps : Real) : Nat :=
  correctedRuntimeSamples (generalizedPhaseCount n R eps) eps

noncomputable def generalizedCoordinateCalls (n : Nat) (R eps : Real) : Nat :=
  (generalizedPhaseCount n R eps + 1) * generalizedSampleCount n R eps

noncomputable def generalizedRadiusQ (n : Nat) (R eps : Real) : Real :=
  correctedExplicitQPoly n R eps

noncomputable def generalizedUniformSteps (n : Nat) (R eps : Real) : Nat :=
  continuingUniformMixingSteps n (generalizedRadiusQ n R eps)
    (generalizedPhaseCount n R eps) eps

/-- Explicit one-run bound for all `(phase,sample)` coordinates. -/
noncomputable def generalizedRetryOneRunEnvelope
    (n : Nat) (R eps : Real) : Real :=
  explicitContinuingOneRunQueryEnvelope continuingReferenceWarm
    (generalizedUniformSteps n R eps) (generalizedCoordinateCalls n R eps)
    (generalizedPhaseCount n R eps) eps

noncomputable def generalizedRetryOneRunBudget
    (n : Nat) (R eps : Real) : ENNReal :=
  ENNReal.ofReal (generalizedRetryOneRunEnvelope n R eps)

theorem generalizedRetryOneRunEnvelope_nonneg
    {n : Nat} {R eps : Real} (heps : 0 < eps) :
    0 ≤ generalizedRetryOneRunEnvelope n R eps := by
  unfold generalizedRetryOneRunEnvelope explicitContinuingOneRunQueryEnvelope
  apply continuingOneRunQueryEnvelope_nonneg
  · unfold explicitRetryPhaseMeanEnvelope continuingReferenceWarm
    positivity
  · exact heps

/-- Machine-checked decomposition of the generalized envelope into the existing
polynomial phase/sample bounds, logarithmic retry bound, and explicit mixing deadline.
This is deliberately a componentwise statement: no source-rate simplification is made. -/
theorem generalizedRetry_parameter_bounds
    {n : Nat} {R eps : Real} (hn : 1 ≤ n) (hR : 0 < R)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hsource : (1 / 2 : Real) ^ n ≤ eps / 4) :
    ((generalizedCoordinateCalls n R eps : Real) < correctedCallPoly n R eps) ∧
    ((explicitContinuingRetries (generalizedPhaseCount n R eps) eps : Real) <
      16 * (Real.logb 2
        (1 / continuingShare (generalizedPhaseCount n R eps) eps) + 1)) ∧
    ((generalizedUniformSteps n R eps : Real) <
      adjustableMixingDeadline n (generalizedRadiusQ n R eps)
        (continuingConditionedWarm (generalizedPhaseCount n R eps) eps)
        (continuingMixTolerance (generalizedPhaseCount n R eps) eps) + 2) := by
  constructor
  · simpa only [generalizedCoordinateCalls, generalizedSampleCount,
      generalizedPhaseCount, runwiseSamplerCalls] using
      corrected_runwise_calls_lt_poly hn hR heps hsource
  constructor
  · exact explicitContinuingRetries_lt_logb heps heps1
  · exact continuingUniformMixingSteps_cast_lt heps heps1

theorem generalizedRetryOneRunEnvelope_eq_eps_ten
    {n : Nat} {R eps : Real} (heps : 0 < eps) :
    generalizedRetryOneRunEnvelope n R eps =
      (generalizedCoordinateCalls n R eps : Real) *
        (8 *
          (explicitRetryPhaseMeanEnvelope continuingReferenceWarm
              (generalizedUniformSteps n R eps) (generalizedPhaseCount n R eps) eps + 1) *
          (100000 ^ 5 * ((generalizedPhaseCount n R eps : Real) + 1) ^ 5) /
          eps ^ 10) := by
  unfold generalizedRetryOneRunEnvelope explicitContinuingOneRunQueryEnvelope
  exact continuingOneRunQueryEnvelope_eq_expanded heps

/-! ## Public capstone for an arbitrary honest one-run envelope -/

noncomputable def generalizedOneRunCutoff (E : Real) : ENNReal :=
  20 * (ENNReal.ofReal E + 1)

theorem generalizedOneRunCutoff_ne_zero (E : Real) :
    generalizedOneRunCutoff E ≠ 0 := by simp [generalizedOneRunCutoff]

theorem generalizedOneRunCutoff_ne_top (E : Real) :
    generalizedOneRunCutoff E ≠ ⊤ := by
  unfold generalizedOneRunCutoff
  exact ENNReal.mul_ne_top (by norm_num)
    (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, by simp⟩)

theorem generalizedOneRunCutoff_ratio (E : Real) :
    ENNReal.ofReal E / generalizedOneRunCutoff E ≤
      ENNReal.ofReal (1 / 20 : Real) := by
  rw [ENNReal.div_le_iff_le_mul
    (Or.inl (generalizedOneRunCutoff_ne_zero E))
    (Or.inl (generalizedOneRunCutoff_ne_top E))]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : Real) < 20)]
  norm_num only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  unfold generalizedOneRunCutoff
  calc
    ENNReal.ofReal E ≤ ENNReal.ofReal E + 1 := le_add_right le_rfl
    _ = (1 / 20 : ENNReal) * (20 * (ENNReal.ofReal E + 1)) := by
      rw [← mul_assoc, ENNReal.div_eq_inv_mul, mul_one,
        ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

noncomputable def generalizedOuterEstimator
    {Omega : Type*} (E fallback : Real) (cost : Omega → ENNReal)
    (value : Omega → Real) {r : Nat} (omega : SourceOuterCoin r Omega) : Real :=
  medianSel fun i ↦ cutoffValue (generalizedOneRunCutoff E)
    fallback cost value (omega i)

noncomputable def generalizedOuterQueryCost
    {Omega : Type*} (E : Real) (cost : Omega → ENNReal)
    {r : Nat} (omega : SourceOuterCoin r Omega) : ENNReal :=
  ∑ i, min (cost (omega i)) (generalizedOneRunCutoff E)

noncomputable def generalizedPublicExpectedBound
    {n : Nat}
    (oneEnvelope : Ttc.CVAdaptive.VolumeInput n → Real)
    (a : Ttc.CVAdaptive.VolumeInput n) : ENNReal :=
  (outerCutoffReps a.2.2 : ENNReal) * generalizedOneRunCutoff (oneEnvelope a)

noncomputable def generalizedAmplifiedEnvelope (E p : Real) : Real :=
  (8 * Real.log (1 / p) + 2) * (20 * (E + 1))

theorem generalizedPublicExpectedBound_le_amplified
    {n : Nat} {oneEnvelope : Ttc.CVAdaptive.VolumeInput n → Real}
    {a : Ttc.CVAdaptive.VolumeInput n} (hE : 0 ≤ oneEnvelope a)
    (hp : 0 < a.2.2) (hp1 : a.2.2 < 1) :
    generalizedPublicExpectedBound oneEnvelope a ≤
      ENNReal.ofReal (generalizedAmplifiedEnvelope (oneEnvelope a) a.2.2) := by
  have hr := outerCutoffReps_cast_lt_eight_log_add_two hp hp1
  have hfactor : 0 ≤ 20 * (oneEnvelope a + 1) := by positivity
  have hreal : (outerCutoffReps a.2.2 : Real) *
      (20 * (oneEnvelope a + 1)) ≤
        generalizedAmplifiedEnvelope (oneEnvelope a) a.2.2 := by
    unfold generalizedAmplifiedEnvelope
    exact mul_le_mul_of_nonneg_right hr.le hfactor
  rw [show generalizedPublicExpectedBound oneEnvelope a =
      ENNReal.ofReal ((outerCutoffReps a.2.2 : Real) *
        (20 * (oneEnvelope a + 1))) by
    unfold generalizedPublicExpectedBound generalizedOneRunCutoff
    rw [ENNReal.ofReal_mul (by positivity : (0 : Real) ≤ (outerCutoffReps a.2.2 : Real)),
      ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 20),
      ENNReal.ofReal_add hE (by norm_num : (0 : Real) ≤ 1)]
    norm_num]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The concrete public envelope uses the enclosing `cvRadius` and the requested
accuracy.  Confidence enters only later through `generalizedAmplifiedEnvelope`. -/
noncomputable def concreteGeneralizedPublicOneEnvelope
    (n : Nat) (a : Ttc.CVAdaptive.VolumeInput n) : Real :=
  generalizedRetryOneRunEnvelope n (Ttc.CV.cvRadius a.1) a.2.1

theorem generalizedOuterQueryCost_le
    {Omega : Type*} (E : Real) (cost : Omega → ENNReal) {r : Nat}
    (omega : SourceOuterCoin r Omega) :
    generalizedOuterQueryCost E cost omega ≤
      (r : ENNReal) * generalizedOneRunCutoff E := by
  unfold generalizedOuterQueryCost
  calc
    _ ≤ ∑ _i : Fin r, generalizedOneRunCutoff E := by
      apply Finset.sum_le_sum
      intro i hi
      exact min_le_right _ _
    _ = _ := by simp

theorem measurable_generalizedOuterQueryCost
    {Omega : Type*} [MeasurableSpace Omega] {E : Real} {cost : Omega → ENNReal}
    (hcost : Measurable cost) {r : Nat} :
    Measurable (generalizedOuterQueryCost E cost : SourceOuterCoin r Omega → ENNReal) := by
  unfold generalizedOuterQueryCost
  apply Finset.measurable_fun_sum
  intro i hi
  exact (hcost.comp (measurable_pi_apply i)).min measurable_const

/-- Public one-run certificates against any input-dependent real envelope. -/
structure GeneralizedPublicOneRunCertificates
    (n : Nat) (oneEnvelope : Ttc.CVAdaptive.VolumeInput n → Real)
    (Omega : Ttc.CVAdaptive.VolumeInput n → Type)
    [∀ a, MeasurableSpace (Omega a)]
    (oneLaw : ∀ a, Measure (Omega a))
    (cost : ∀ a, Omega a → ENNReal)
    (value : ∀ a, Omega a → Real) : Prop where
  probability : ∀ a, IsProbabilityMeasure (oneLaw a)
  cost_measurable : ∀ a, Measurable (cost a)
  value_measurable : ∀ a, Measurable (value a)
  expected_queries : ∀ a,
    (∫⁻ omega, cost a omega ∂oneLaw a) ≤ ENNReal.ofReal (oneEnvelope a)
  accuracy : ∀ (K : Set (Ttc.Space n)) (eps p : Real),
    0 < eps → 0 < p → p < 1 → Convex Real K →
    Metric.ball (0 : Ttc.Space n) 1 ⊆ K → volume K ≠ ⊤ →
    4 / 5 ≤ (oneLaw (K, eps, p)).real
      {omega | value (K, eps, p) omega ∈
        Icc ((1 - eps) * (volume K).toReal) ((1 + eps) * (volume K).toReal)}

/-- Unconditional semantic expected-query oracle obtained from an honest one-run law.
When `oneEnvelope a = generalizedRetryOneRunEnvelope n R eps`, its bound is the explicit
generalized polynomial/logarithmic envelope above, not the sharper source envelope. -/
noncomputable def expectedQueryVolumeAlgorithmOfGeneralizedCertificates
    (n : Nat) (oneEnvelope : Ttc.CVAdaptive.VolumeInput n → Real)
    (Omega : Ttc.CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ a, MeasurableSpace (Omega a)]
    (oneLaw : ∀ a, Measure (Omega a))
    (cost : ∀ a, Omega a → ENNReal)
    (value : ∀ a, Omega a → Real)
    (hcert : GeneralizedPublicOneRunCertificates n oneEnvelope Omega oneLaw cost value) :
    Ttc.ExpectedQueryVolumeAlgorithm n := by
  let X : Ttc.CVAdaptive.VolumeInput n → Type := fun a ↦
    SourceOuterCoin (outerCutoffReps a.2.2) (Omega a)
  letI : ∀ a, MeasurableSpace (X a) := fun a ↦ inferInstance
  let nu : ∀ a, Measure (X a) := fun a ↦
    sourceOuterLaw (oneLaw a) (outerCutoffReps a.2.2)
  let localEst : ∀ a, X a → Real := fun a ↦
    generalizedOuterEstimator (oneEnvelope a) 0 (cost a) (value a)
  let localCost : ∀ a, X a → ENNReal := fun a ↦
    generalizedOuterQueryCost (oneEnvelope a) (cost a)
  let bound : Ttc.CVAdaptive.VolumeInput n → ENNReal := fun a ↦
    generalizedPublicExpectedBound oneEnvelope a
  letI : ∀ a, IsProbabilityMeasure (oneLaw a) := hcert.probability
  letI : ∀ a, IsProbabilityMeasure (nu a) := by
    intro a
    dsimp only [nu, X, sourceOuterLaw]
    infer_instance
  apply Ttc.ExpectedQueryVolumeAlgorithm.ofInputCostedLaws n X nu localEst localCost
    (bound := bound)
  · intro a
    dsimp only [localEst, X]
    apply measurable_medianSel
    intro i
    exact (measurable_cutoffValue (hcert.cost_measurable a)
      (hcert.value_measurable a)).comp (measurable_pi_apply i)
  · intro a
    dsimp only [localCost, X]
    exact measurable_generalizedOuterQueryCost (hcert.cost_measurable a)
  · intro a
    dsimp only [localCost, nu, X, bound, generalizedPublicExpectedBound]
    calc
      _ ≤ ∫⁻ _omega, (outerCutoffReps a.2.2 : ENNReal) *
          generalizedOneRunCutoff (oneEnvelope a) ∂sourceOuterLaw
            (oneLaw a) (outerCutoffReps a.2.2) :=
        lintegral_mono (generalizedOuterQueryCost_le (oneEnvelope a) (cost a))
      _ = _ := by simp [sourceOuterLaw]
  · intro K eps p heps hp hp1 hKc hball hfin
    let a : Ttc.CVAdaptive.VolumeInput n := (K, eps, p)
    dsimp only [nu, localEst, X]
    have hmain := Ttc.CVCorrectedHybridRuntimeAssembly.median_cutoff_success_iid
      (oneLaw := oneLaw a) (r := outerCutoffReps p) (outerCutoffReps_pos p)
      (hcert.cost_measurable a) (hcert.value_measurable a)
      (B := ENNReal.ofReal (oneEnvelope a))
      (L := generalizedOneRunCutoff (oneEnvelope a))
      (generalizedOneRunCutoff_ne_zero (oneEnvelope a))
      (generalizedOneRunCutoff_ne_top (oneEnvelope a))
      (hcert.expected_queries a) (generalizedOneRunCutoff_ratio (oneEnvelope a))
      (fallback := 0) (hcert.accuracy K eps p heps hp hp1 hKc hball hfin)
      hp (outerCutoffReps_spec p)
    simpa only [sourceOuterLaw, generalizedOuterEstimator] using hmain

noncomputable def expectedQueryVolumeAlgorithmOfConcreteGeneralizedCertificates
    (n : Nat) (Omega : Ttc.CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ a, MeasurableSpace (Omega a)]
    (oneLaw : ∀ a, Measure (Omega a))
    (cost : ∀ a, Omega a → ENNReal)
    (value : ∀ a, Omega a → Real)
    (hcert : GeneralizedPublicOneRunCertificates n
      (concreteGeneralizedPublicOneEnvelope n) Omega oneLaw cost value) :
    Ttc.ExpectedQueryVolumeAlgorithm n :=
  expectedQueryVolumeAlgorithmOfGeneralizedCertificates n
    (concreteGeneralizedPublicOneEnvelope n) Omega oneLaw cost value hcert

#print axioms continuingOneRunQueryEnvelope_eq_expanded
#print axioms continuingUniformMixingDeadline_le_steps
#print axioms generalizedRetry_parameter_bounds
#print axioms generalizedRetryOneRunEnvelope_eq_eps_ten
#print axioms generalizedOneRunCutoff_ratio
#print axioms generalizedPublicExpectedBound_le_amplified
#print axioms expectedQueryVolumeAlgorithmOfGeneralizedCertificates
#print axioms expectedQueryVolumeAlgorithmOfConcreteGeneralizedCertificates

end Ttc.CVGeneralPolynomialCutoffCapstone
