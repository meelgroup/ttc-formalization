/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Exec.CVCostedAdjustableOuterMedian
import Arlib.MarkovChains.Continuous.ProperProposalLazyCutoff
import Ttc.Exec.CVSourceTruncatedFixedCost
import Ttc.Exec.CostedStatefulSpeedyPhases
import Ttc.Volume.CVCorrectedLogarithmicRadiusRuntime

/-!
# Source-shaped polynomial cutoff capstone for the CV volume algorithm

The last paragraph of the proof of Theorem 1.1 in Cousins--Vempala first proves a
`4/5` one-run accuracy statement, uses Markov's inequality to spend `1/20` on a runtime
cutoff, and then takes the median of independent cutoff runs.  This file packages exactly
that argument with the displayed source-shaped query envelope

`max {R^2 n^2, n^3} eps^-2 log^2 n log^2(1/eps) log^2(n/eps)`.

The logarithms below are clipped below by one.  This is the usual explicit interpretation
of the paper's `O*` expression and keeps the advertised bound nonnegative on every input.

The only unproved premise is `SourceOneRunCertificate`.  It deliberately refers to an
*actual common law* carrying both the estimator and its recorded membership-query cost.
It is not currently instantiated by the repository: independent cold restarts multiply
the actual wasted-step bound by an exponential warmness constant, while the source's
constant-cost treatment of all `sigma^2 <= 1` phases is false (see
`CVCorrectedFixedBlockCost.source_fixed_succ_not_ambientEligible`).  The stateful raw lazy
execution and its per-phase cutoff are available in `ProperProposalLazyCutoff`; what remains
is a sequential constant-warm phase execution whose output satisfies the corrected
dependent accuracy theorem.
-/

namespace Ttc.CVSourcePolynomialCutoffCapstone

open MeasureTheory ProbabilityTheory Set
open Arlib.GaussianCooling
open Arlib.Probability
open Ttc.CVCostedRuntimeCutoff
open Ttc.CVCostedAdjustableOuterMedian
open scoped ENNReal Classical

/-- A log factor with the conventional harmless lower clipping used to make an `O*`
display into a globally nonnegative explicit expression. -/
noncomputable def sourceLogFactor (x : Real) : Real := max 1 (Real.log x)

set_option linter.unusedVariables false in
/-- **The one-run query budget scalar.**  This is the `runtimeConstant` itself: the whole
content of a one-run bound is the scalar a construction proves its expected query count is
under, and the `(n, R, eps)` slots are retained only so that every consumer's signature is
unchanged.

⚠ **This used to be `runtimeConstant * cvBaseClipped n R eps`** — Cousins–Vempala's own
Theorem 1.1 expression, multiplied in.  That factor was never earned: every discharge site
proves `expected queries ≤ runtimeConstant` and then reaches this envelope through
`Ttc.CVSlowEffectiveOverhead.le_sourceOneRunQueryEnvelope_of_le`, whose entire content was
`le_mul_of_one_le_right` at `1 ≤ cvBaseClipped`.  See `lean/PLAN-SHAPE.md`.

The paper-contract layer is untouched: `Ttc.cvComplexityShapeClipped` and
`Ttc.CVTheorem11Implementation` still state Theorem 1.1's expression, and
`Ttc.CVSourceTheorem11Arithmetic.sourceAmplifiedQueryEnvelope_le_cvComplexityShapeClipped`
still proves this budget fits it. -/
noncomputable def sourceOneRunQueryEnvelope
    (runtimeConstant : Real) (n : Nat) (R eps : Real) : Real :=
  runtimeConstant

theorem sourceLogFactor_pos (x : Real) : 0 < sourceLogFactor x := by
  unfold sourceLogFactor
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem sourceOneRunQueryEnvelope_nonneg {runtimeConstant : Real}
    (hconstant : 0 <= runtimeConstant) (n : Nat) (R eps : Real) :
    0 <= sourceOneRunQueryEnvelope runtimeConstant n R eps := by
  unfold sourceOneRunQueryEnvelope
  positivity

/-- ENNReal form of the source-shaped one-run budget. -/
noncomputable def sourceOneRunQueryBudget
    (runtimeConstant : Real) (n : Nat) (R eps : Real) : ENNReal :=
  ENNReal.ofReal (sourceOneRunQueryEnvelope runtimeConstant n R eps)

/-- Twenty times the one-run envelope, with one unit of slack.  The slack makes the
deadline nonzero even on degenerate inputs. -/
noncomputable def sourceOneRunCutoff
    (runtimeConstant : Real) (n : Nat) (R eps : Real) : ENNReal :=
  20 * (sourceOneRunQueryBudget runtimeConstant n R eps + 1)

theorem sourceOneRunCutoff_ne_zero (runtimeConstant : Real) (n : Nat) (R eps : Real) :
    sourceOneRunCutoff runtimeConstant n R eps ≠ 0 := by
  simp [sourceOneRunCutoff]

theorem sourceOneRunCutoff_ne_top (runtimeConstant : Real) (n : Nat) (R eps : Real) :
    sourceOneRunCutoff runtimeConstant n R eps ≠ ⊤ := by
  unfold sourceOneRunCutoff sourceOneRunQueryBudget
  exact ENNReal.mul_ne_top (by norm_num)
    (ENNReal.add_ne_top.mpr <| by simp)

theorem sourceOneRunCutoff_ratio (runtimeConstant : Real) (n : Nat) (R eps : Real) :
    sourceOneRunQueryBudget runtimeConstant n R eps /
        sourceOneRunCutoff runtimeConstant n R eps <=
      ENNReal.ofReal (1 / 20 : Real) := by
  rw [ENNReal.div_le_iff_le_mul
    (Or.inl (sourceOneRunCutoff_ne_zero runtimeConstant n R eps))
    (Or.inl (sourceOneRunCutoff_ne_top runtimeConstant n R eps))]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : Real) < 20)]
  norm_num only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  unfold sourceOneRunCutoff
  calc
    sourceOneRunQueryBudget runtimeConstant n R eps <=
        sourceOneRunQueryBudget runtimeConstant n R eps + 1 :=
      le_add_right le_rfl
    _ = (1 / 20 : ENNReal) *
        (20 * (sourceOneRunQueryBudget runtimeConstant n R eps + 1)) := by
      rw [← mul_assoc, ENNReal.div_eq_inv_mul, mul_one,
        ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

/-- The single honest operational seam still needed for the source runtime proof.

The probability law, output, and recorded query cost all live on the same coin space.
Thus this cannot be discharged by a purely distributional sampler or a detached arithmetic
proposal count. -/
structure SourceOneRunCertificate
    {Omega : Type*} [MeasurableSpace Omega]
    (oneLaw : Measure Omega) (cost : Omega -> ENNReal) (value : Omega -> Real)
    (runtimeConstant : Real) (n : Nat) (R eps lo hi : Real) : Prop where
  probability : IsProbabilityMeasure oneLaw
  cost_measurable : Measurable cost
  value_measurable : Measurable value
  expected_queries :
    (∫⁻ omega, cost omega ∂oneLaw) <=
      sourceOneRunQueryBudget runtimeConstant n R eps
  accuracy : 4 / 5 <= oneLaw.real {omega | value omega ∈ Icc lo hi}

/-- Independent copies of one certified run. -/
abbrev SourceOuterCoin (r : Nat) (Omega : Type*) := Fin r -> Omega

noncomputable def sourceOuterLaw
    {Omega : Type*} [MeasurableSpace Omega] (oneLaw : Measure Omega) (r : Nat) :
    Measure (SourceOuterCoin r Omega) :=
  Measure.pi fun _ : Fin r => oneLaw

/-- Median of independently repeated runs, replacing a timed-out run by `fallback`. -/
noncomputable def sourceOuterEstimator
    {Omega : Type*} (runtimeConstant : Real) (n : Nat) (R eps fallback : Real)
    (cost : Omega -> ENNReal) (value : Omega -> Real) {r : Nat}
    (omega : SourceOuterCoin r Omega) : Real :=
  medianSel fun i => cutoffValue (sourceOneRunCutoff runtimeConstant n R eps)
    fallback cost value (omega i)

/-- Actual stopped cost of the independent outer repetitions. -/
noncomputable def sourceOuterQueryCost
    {Omega : Type*} (runtimeConstant : Real) (n : Nat) (R eps : Real)
    (cost : Omega -> ENNReal) {r : Nat}
    (omega : SourceOuterCoin r Omega) : ENNReal :=
  ∑ i, min (cost (omega i)) (sourceOneRunCutoff runtimeConstant n R eps)

/-- Exact deterministic bound after cutting off each run. -/
noncomputable def sourceOuterCutoffBudget
    (runtimeConstant : Real) (n r : Nat) (R eps : Real) : ENNReal :=
  (r : ENNReal) * sourceOneRunCutoff runtimeConstant n R eps

theorem sourceOuterQueryCost_le
    {Omega : Type*} (runtimeConstant : Real) (n : Nat) (R eps : Real)
    (cost : Omega -> ENNReal) {r : Nat}
    (omega : SourceOuterCoin r Omega) :
    sourceOuterQueryCost runtimeConstant n R eps cost omega <=
      sourceOuterCutoffBudget runtimeConstant n r R eps := by
  unfold sourceOuterQueryCost sourceOuterCutoffBudget
  calc
    ∑ i, min (cost (omega i)) (sourceOneRunCutoff runtimeConstant n R eps) <=
        ∑ _i : Fin r, sourceOneRunCutoff runtimeConstant n R eps := by
      apply Finset.sum_le_sum
      intro i hi
      exact min_le_right _ _
    _ = (r : ENNReal) * sourceOneRunCutoff runtimeConstant n R eps := by simp

theorem measurable_sourceOuterQueryCost
    {Omega : Type*} [MeasurableSpace Omega]
    {runtimeConstant R eps : Real} {n r : Nat} {cost : Omega -> ENNReal}
    (hcost : Measurable cost) :
    Measurable (sourceOuterQueryCost runtimeConstant n R eps cost :
      SourceOuterCoin r Omega -> ENNReal) := by
  unfold sourceOuterQueryCost
  apply Finset.measurable_fun_sum
  intro i hi
  exact (hcost.comp (measurable_pi_apply i)).min measurable_const

/-- The cutoff cost bound is also an expected membership-query bound on the iid law. -/
theorem sourceOuter_expectedQueryCost_le
    {Omega : Type*} [MeasurableSpace Omega]
    (oneLaw : Measure Omega) [IsProbabilityMeasure oneLaw]
    {runtimeConstant R eps : Real} {n r : Nat} {cost : Omega -> ENNReal} :
    (∫⁻ omega, sourceOuterQueryCost runtimeConstant n R eps cost omega
      ∂sourceOuterLaw oneLaw r) <=
      sourceOuterCutoffBudget runtimeConstant n r R eps := by
  calc
    _ <= ∫⁻ _omega, sourceOuterCutoffBudget runtimeConstant n r R eps
        ∂sourceOuterLaw oneLaw r :=
      lintegral_mono (sourceOuterQueryCost_le runtimeConstant n R eps cost)
    _ = sourceOuterCutoffBudget runtimeConstant n r R eps := by simp [sourceOuterLaw]

/-- Explicit real form of the full cutoff budget.  Its dependence on confidence is
`8*log(1/p)+2`, and hence exactly one logarithmic amplification factor. -/
noncomputable def sourceAmplifiedQueryEnvelope
    (runtimeConstant : Real) (n : Nat) (R eps p : Real) : Real :=
  (8 * Real.log (1 / p) + 2) *
    (20 * (sourceOneRunQueryEnvelope runtimeConstant n R eps + 1))

theorem outerCutoffReps_cast_lt_eight_log_add_two
    {p : Real} (hp : 0 < p) (hp1 : p < 1) :
    (outerCutoffReps p : Real) < 8 * Real.log (1 / p) + 2 := by
  have hinv : 1 < 1 / p := by
    rw [lt_div_iff₀ hp]
    simpa using hp1
  have hlog : 0 <= Real.log (1 / p) := (Real.log_pos hinv).le
  have harg : 0 <=
      Real.log (1 / p) / (2 * (3 / 4 - 1 / 2) ^ 2) := by positivity
  have hceil := Nat.ceil_lt_add_one harg
  rw [outerCutoffReps]
  push_cast
  norm_num at hceil ⊢
  linarith

theorem sourceOuterCutoffBudget_le_explicit
    {n : Nat} {runtimeConstant R eps p : Real} (hconstant : 0 <= runtimeConstant)
    (hp : 0 < p) (hp1 : p < 1) :
    sourceOuterCutoffBudget runtimeConstant n (outerCutoffReps p) R eps <=
      ENNReal.ofReal (sourceAmplifiedQueryEnvelope runtimeConstant n R eps p) := by
  have hr := outerCutoffReps_cast_lt_eight_log_add_two hp hp1
  have hlog : 0 <= Real.log (1 / p) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hp]
    simpa using hp1.le
  have hE := sourceOneRunQueryEnvelope_nonneg hconstant n R eps
  have hfactor : 0 <=
      20 * (sourceOneRunQueryEnvelope runtimeConstant n R eps + 1) := by positivity
  have hreal :
      (outerCutoffReps p : Real) *
          (20 * (sourceOneRunQueryEnvelope runtimeConstant n R eps + 1)) <=
        sourceAmplifiedQueryEnvelope runtimeConstant n R eps p := by
    unfold sourceAmplifiedQueryEnvelope
    exact mul_le_mul_of_nonneg_right hr.le hfactor
  rw [show sourceOuterCutoffBudget runtimeConstant n (outerCutoffReps p) R eps =
      ENNReal.ofReal ((outerCutoffReps p : Real) *
        (20 * (sourceOneRunQueryEnvelope runtimeConstant n R eps + 1))) by
    unfold sourceOuterCutoffBudget sourceOneRunCutoff sourceOneRunQueryBudget
    rw [ENNReal.ofReal_mul (by positivity : (0 : Real) <= (outerCutoffReps p : Real)),
      ENNReal.ofReal_mul (by positivity : (0 : Real) <= 20),
      ENNReal.ofReal_add hE (by norm_num : (0 : Real) <= 1)]
    norm_num]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The source-faithful runtime capstone: one certified `4/5` execution, a `1/20` timeout
budget, and independent median amplification give confidence `1-p`. -/
theorem source_median_cutoff_accuracy
    {Omega : Type*} [MeasurableSpace Omega]
    (oneLaw : Measure Omega) (cost : Omega -> ENNReal) (value : Omega -> Real)
    {n : Nat} {runtimeConstant R eps lo hi fallback p : Real}
    (hcert : SourceOneRunCertificate oneLaw cost value
      runtimeConstant n R eps lo hi)
    (hp : 0 < p) :
    1 - p <= (sourceOuterLaw oneLaw (outerCutoffReps p)).real
      {omega | sourceOuterEstimator runtimeConstant n R eps fallback cost value omega ∈
        Icc lo hi} := by
  letI : IsProbabilityMeasure oneLaw := hcert.probability
  have hmain := Ttc.CVCorrectedHybridRuntimeAssembly.median_cutoff_success_iid
    (oneLaw := oneLaw) (r := outerCutoffReps p) (outerCutoffReps_pos p)
    hcert.cost_measurable hcert.value_measurable
    (B := sourceOneRunQueryBudget runtimeConstant n R eps)
    (L := sourceOneRunCutoff runtimeConstant n R eps)
    (sourceOneRunCutoff_ne_zero runtimeConstant n R eps)
    (sourceOneRunCutoff_ne_top runtimeConstant n R eps)
    hcert.expected_queries (sourceOneRunCutoff_ratio runtimeConstant n R eps)
    (fallback := fallback) hcert.accuracy hp (outerCutoffReps_spec p)
  simpa only [sourceOuterLaw, sourceOuterEstimator] using hmain

/-- Combined accuracy and explicit expected-query statement.  This is the strongest
Theorem-1.1-shaped conclusion available without inventing the missing sequential warm
execution. -/
theorem source_polynomial_cutoff_capstone
    {Omega : Type*} [MeasurableSpace Omega]
    (oneLaw : Measure Omega) (cost : Omega -> ENNReal) (value : Omega -> Real)
    {n : Nat} {runtimeConstant R eps lo hi fallback p : Real}
    (hcert : SourceOneRunCertificate oneLaw cost value
      runtimeConstant n R eps lo hi)
    (hconstant : 0 <= runtimeConstant) (hp : 0 < p) (hp1 : p < 1) :
    (1 - p <= (sourceOuterLaw oneLaw (outerCutoffReps p)).real
      {omega | sourceOuterEstimator runtimeConstant n R eps fallback cost value omega ∈
        Icc lo hi}) ∧
    ((∫⁻ omega, sourceOuterQueryCost runtimeConstant n R eps cost omega
        ∂sourceOuterLaw oneLaw (outerCutoffReps p)) <=
      ENNReal.ofReal (sourceAmplifiedQueryEnvelope runtimeConstant n R eps p)) := by
  letI : IsProbabilityMeasure oneLaw := hcert.probability
  constructor
  · exact source_median_cutoff_accuracy oneLaw cost value hcert hp
  · exact (sourceOuter_expectedQueryCost_le oneLaw).trans
      (sourceOuterCutoffBudget_le_explicit hconstant hp hp1)

/-! ## Conditional public oracle -/

/-- Exact public expected-cost bound used by the conditional oracle. -/
noncomputable def sourcePublicExpectedBound
    (runtimeConstant : Real) (n : Nat) (radialR : Set (Ttc.Space n) -> Real)
    (K : Set (Ttc.Space n)) (eps p : Real) : ENNReal :=
  sourceOuterCutoffBudget runtimeConstant n (outerCutoffReps p) (radialR K) eps

theorem sourcePublicExpectedBound_le_polynomial
    {runtimeConstant : Real} (hconstant : 0 <= runtimeConstant) {n : Nat}
    (radialR : Set (Ttc.Space n) -> Real) (K : Set (Ttc.Space n))
    {eps p : Real} (hp : 0 < p) (hp1 : p < 1) :
    sourcePublicExpectedBound runtimeConstant n radialR K eps p <=
      ENNReal.ofReal (sourceAmplifiedQueryEnvelope runtimeConstant n (radialR K) eps p) := by
  exact sourceOuterCutoffBudget_le_explicit hconstant hp hp1

/-- Input-indexed one-run operational certificates for a public volume oracle.  Probability,
measurability and expected cost are required for every input so the public coin law is
total; the `4/5` accuracy field is required only on the valid-input branch. -/
structure SourcePublicOneRunCertificates
    (n : Nat) (runtimeConstant : Real) (radialR : Set (Ttc.Space n) -> Real)
    (Omega : Ttc.CVAdaptive.VolumeInput n -> Type)
    [forall a, MeasurableSpace (Omega a)]
    (oneLaw : forall a, Measure (Omega a))
    (cost : forall a, Omega a -> ENNReal)
    (value : forall a, Omega a -> Real) : Prop where
  probability : forall a, IsProbabilityMeasure (oneLaw a)
  cost_measurable : forall a, Measurable (cost a)
  value_measurable : forall a, Measurable (value a)
  expected_queries : forall a,
    (∫⁻ omega, cost a omega ∂oneLaw a) <=
      sourceOneRunQueryBudget runtimeConstant n (radialR a.1) a.2.1
  accuracy : forall (K : Set (Ttc.Space n)) (eps p : Real),
    0 < eps -> 0 < p -> p < 1 -> Convex Real K ->
    Metric.ball (0 : Ttc.Space n) 1 ⊆ K -> volume K ≠ ⊤ ->
    4 / 5 <= (oneLaw (K, eps, p)).real
      {omega | value (K, eps, p) omega ∈
        Icc ((1 - eps) * (volume K).toReal) ((1 + eps) * (volume K).toReal)}

/-- Public expected-query volume oracle conditional only on constructing, for every input,
the concrete one-run cost/output law certified by `SourceOneRunCertificate`.

The outer iid law, cutoff, median, confidence amplification, measurability, and explicit
query envelope are all constructed here.  Consequently the remaining public-runtime
obligation is literally `hcert`; no further packaging or amplification binder remains. -/
noncomputable def expectedQueryVolumeAlgorithmOfSourceOneRunCertificates
    (n : Nat) (runtimeConstant : Real)
    (radialR : Set (Ttc.Space n) -> Real)
    (Omega : Ttc.CVAdaptive.VolumeInput n -> Type)
    [mOmega : forall a, MeasurableSpace (Omega a)]
    (oneLaw : forall a, Measure (Omega a))
    (cost : forall a, Omega a -> ENNReal)
    (value : forall a, Omega a -> Real)
    (hcert : SourcePublicOneRunCertificates n runtimeConstant radialR
      Omega oneLaw cost value) :
    Ttc.ExpectedQueryVolumeAlgorithm n := by
  let X : Ttc.CVAdaptive.VolumeInput n -> Type := fun a =>
    SourceOuterCoin (outerCutoffReps a.2.2) (Omega a)
  letI : forall a, MeasurableSpace (X a) := fun a => inferInstance
  let nu : forall a, Measure (X a) := fun a =>
    sourceOuterLaw (oneLaw a) (outerCutoffReps a.2.2)
  let localEst : forall a, X a -> Real := fun a =>
    sourceOuterEstimator runtimeConstant n (radialR a.1) a.2.1 0 (cost a) (value a)
  let localCost : forall a, X a -> ENNReal := fun a =>
    sourceOuterQueryCost runtimeConstant n (radialR a.1) a.2.1 (cost a)
  let bound : Ttc.CVAdaptive.VolumeInput n -> ENNReal := fun a =>
    sourcePublicExpectedBound runtimeConstant n radialR a.1 a.2.1 a.2.2
  letI : forall a, IsProbabilityMeasure (oneLaw a) := hcert.probability
  letI : forall a, IsProbabilityMeasure (nu a) := by
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
    exact measurable_sourceOuterQueryCost (hcert.cost_measurable a)
  · intro a
    dsimp only [localCost, nu, X, bound]
    exact sourceOuter_expectedQueryCost_le (oneLaw a)
  · intro K eps p heps hp hp1 hKc hball hfin
    let a : Ttc.CVAdaptive.VolumeInput n := (K, eps, p)
    dsimp only [nu, localEst, X]
    let cert : SourceOneRunCertificate (oneLaw a) (cost a) (value a)
        runtimeConstant n (radialR K) eps
          ((1 - eps) * (volume K).toReal) ((1 + eps) * (volume K).toReal) :=
      { probability := hcert.probability a
        cost_measurable := hcert.cost_measurable a
        value_measurable := hcert.value_measurable a
        expected_queries := hcert.expected_queries a
        accuracy := hcert.accuracy K eps p heps hp hp1 hKc hball hfin }
    exact source_median_cutoff_accuracy (oneLaw a) (cost a) (value a) cert hp

#print axioms sourceOneRunCutoff_ratio
#print axioms sourceOuter_expectedQueryCost_le
#print axioms sourceOuterCutoffBudget_le_explicit
#print axioms source_median_cutoff_accuracy
#print axioms source_polynomial_cutoff_capstone
#print axioms sourcePublicExpectedBound_le_polynomial
#print axioms expectedQueryVolumeAlgorithmOfSourceOneRunCertificates

end Ttc.CVSourcePolynomialCutoffCapstone
