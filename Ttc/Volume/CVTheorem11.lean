/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.ExpectedQueryOracle
import Arlib.Probability.UniformOn
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Cousins--Vempala Theorem 1.1: accuracy and complexity certificate

This file records the full *contract* of Theorem 1.1 of arXiv:1409.6011 without
postulating that its implementation has been formalised.  Accuracy is the existing
`Ttc.VolumeAlgorithm` interface.  `CVTheorem11Implementation` additionally asks for an
operational membership-query cost and a proof of the paper's displayed bound.

The multiplicative constant is deliberately a field of the certificate.  The paper
states the result with `O`, and does not publish a numerical value for the constant;
nothing below manufactures one.  In particular, merely defining this structure does
not produce an inhabitant of it.
-/

namespace Ttc

open MeasureTheory Filter Asymptotics

/-- `E_K (‖X‖²)` for the uniform probability measure on `K`.  The admissibility
predicate below explicitly excludes the two degenerate cases in which `uniformOn` is
not a probability measure. -/
noncomputable def cvSecondMoment {n : ℕ} (K : Set (Space n)) : ℝ :=
  ∫ x, ‖x‖ ^ 2 ∂(Arlib.uniformOn volume K)

/-- The geometric hypotheses of the general form of Cousins--Vempala Theorem 1.1.
`R2` is an explicit upper bound for the paper's `E_K(‖X‖²)`. -/
def CVAdmissible {n : ℕ} (K : Set (Space n)) (R2 : ℝ) : Prop :=
  Convex ℝ K ∧
  Metric.ball (0 : Space n) 1 ⊆ K ∧
  volume K ≠ 0 ∧ volume K ≠ ⊤ ∧
  cvSecondMoment K ≤ R2

/-- The expression inside the `O` in the general runtime statement following
Theorem 1.1.  It counts membership-oracle operations, not machine instructions.

The theorem is normally used with `0 < ε`, `ε < 1`, `0 < p`, `p < 1`, and positive
dimension.  Those guards belong to the certificate, rather than being hidden by
altering the logarithms in this exact transcription. -/
noncomputable def cvComplexityShape (n : ℕ) (R2 ε p : ℝ) : ℝ :=
  (max (R2 * (n : ℝ) ^ 2) ((n : ℝ) ^ 3) / ε ^ 2) *
    Real.log n ^ 2 * Real.log (1 / ε) ^ 2 *
      Real.log (n / ε) ^ 2 * Real.log (1 / p)

/-- Globally valid version of the Theorem 1.1 query shape.  The paper states an
asymptotic bound in the regime in which all logarithms are bounded away from zero.  A
pointwise implementation contract must clip those logarithms: without the clipping the
right hand side is zero in dimension one and tends to zero as `p` tends to one, although
an implementation still has to perform a run. -/
noncomputable def cvComplexityShapeClipped (n : ℕ) (R2 ε p : ℝ) : ℝ :=
  (max (R2 * (n : ℝ) ^ 2) ((n : ℝ) ^ 3) / ε ^ 2) *
    max 1 (Real.log n) ^ 2 * max 1 (Real.log (1 / ε)) ^ 2 *
      max 1 (Real.log (n / ε)) ^ 2 * max 1 (Real.log (1 / p))

theorem cvComplexityShapeClipped_nonneg (n : ℕ) (R2 ε p : ℝ)
    (hR2 : 0 ≤ R2) : 0 ≤ cvComplexityShapeClipped n R2 ε p := by
  unfold cvComplexityShapeClipped
  positivity

/-- `E_K(‖X‖²) = O(n)` with its hidden roundness constant exposed as `κ`.
This pointwise form is what can be passed to a concrete dimension-indexed family. -/
def CVWellRounded {n : ℕ} (K : Set (Space n)) (κ : ℝ) : Prop :=
  cvSecondMoment K ≤ κ * n

/-- A genuine implementation witness for Theorem 1.1.

No inhabitant is declared here.  Supplying one requires both an accuracy algorithm and
an operational membership-oracle implementation whose query count satisfies
`queryCost_le`.  The universal `runtimeConstant` represents precisely the unpublished
constant hidden by the paper's `O`; because it is outside all input quantifiers it
cannot vary with `n`, `K`, `ε`, `p`, or `R2`. -/
structure CVTheorem11Implementation where
  algorithm : (n : ℕ) → VolumeAlgorithm n
  /-- The result returned by the implementation.  The current development has no
  datatype of membership-oracle programs, so this is deliberately an abstract
  execution witness rather than executable Lean code. -/
  run : (n : ℕ) → Set (Space n) → ℝ → ℝ → (algorithm n).Ω → ℝ
  /-- The execution witness implements the estimator whose accuracy is certified by
  `VolumeAlgorithm.correct`. -/
  run_eq_est : ∀ (n : ℕ) (K : Set (Space n)) (ε p : ℝ) (ω : (algorithm n).Ω),
    run n K ε p ω = (algorithm n).est K ε p ω
  /-- Membership-oracle queries used on this input. -/
  queryCost : (n : ℕ) → Set (Space n) → ℝ → ℝ → ℕ
  runtimeConstant : ℝ
  runtimeConstant_nonneg : 0 ≤ runtimeConstant
  queryCost_le : ∀ (n : ℕ) (K : Set (Space n)) (ε p R2 : ℝ),
    1 ≤ n → 0 < ε → ε < 1 → 0 < p → p < 1 → CVAdmissible K R2 →
    (queryCost n K ε p : ℝ) ≤ runtimeConstant * cvComplexityShape n R2 ε p

/-- Honest operational form of Cousins--Vempala Theorem 1.1.

Membership-query rejection loops have random length, so their correct cost statement is
an expectation of the query counter on the same probability space as the estimator.  The
clipped logarithms make the paper's asymptotic display into a valid pointwise bound on its
whole advertised input domain. -/
structure CVTheorem11ExpectedImplementation where
  algorithm : (n : ℕ) → ExpectedQueryVolumeAlgorithm n
  runtimeConstant : ℝ
  runtimeConstant_nonneg : 0 ≤ runtimeConstant
  expectedBound_le : ∀ (n : ℕ) (K : Set (Space n)) (ε p R2 : ℝ),
    1 ≤ n → 0 < ε → ε < 1 → 0 < p → p < 1 → CVAdmissible K R2 →
    (algorithm n).expectedBound K ε p ≤
      ENNReal.ofReal (runtimeConstant * cvComplexityShapeClipped n R2 ε p)

/-- The old literal transcription collapses to zero in dimension one.  This explains why
`CVTheorem11ExpectedImplementation` uses the globally clipped shape rather than silently
claiming that a positive-cost execution satisfies the old contract. -/
theorem cvComplexityShape_one (R2 ε p : ℝ) :
    cvComplexityShape 1 R2 ε p = 0 := by
  simp [cvComplexityShape]

/-- The accuracy half of Theorem 1.1, projected from an implementation certificate.
The moment bound is present through `CVAdmissible`, even though (as in the mathematics)
it is needed only to obtain the advertised runtime and not to prove accuracy. -/
theorem CVTheorem11Implementation.correct (I : CVTheorem11Implementation)
    (n : ℕ) (K : Set (Space n)) (ε p R2 : ℝ)
    (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1) (hK : CVAdmissible K R2) :
    1 - p ≤ ((I.algorithm n).μ
      {ω | (I.algorithm n).est K ε p ω ∈ relErr ε (volume K).toReal}).toReal :=
  (I.algorithm n).correct K ε p hε hp hp1 hK.1 hK.2.1 hK.2.2.2.1

/-- Any inhabitant of the old literal contract is forced to report zero queries in
dimension one.  This is a formal, not merely documentary, obstruction to using that
contract for the operational rejection sampler. -/
theorem CVTheorem11Implementation.queryCost_eq_zero_dim_one
    (I : CVTheorem11Implementation) (K : Set (Space 1)) (ε p R2 : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hp : 0 < p) (hp1 : p < 1)
    (hK : CVAdmissible K R2) : I.queryCost 1 K ε p = 0 := by
  have hle := I.queryCost_le 1 K ε p R2 (by omega) hε hε1 hp hp1 hK
  rw [cvComplexityShape_one, mul_zero] at hle
  have heq : (I.queryCost 1 K ε p : ℝ) = 0 :=
    le_antisymm hle (Nat.cast_nonneg _)
  exact_mod_cast heq

/-- Accuracy projection from the honest expected-query implementation. -/
theorem CVTheorem11ExpectedImplementation.correct
    (I : CVTheorem11ExpectedImplementation)
    (n : ℕ) (K : Set (Space n)) (ε p R2 : ℝ)
    (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1) (hK : CVAdmissible K R2) :
    1 - p ≤ ((I.algorithm n).μ
      {ω | (I.algorithm n).est K ε p ω ∈ relErr ε (volume K).toReal}).toReal :=
  (I.algorithm n).accuracy K ε p hε hp hp1 hK.1 hK.2.1 hK.2.2.2.1

/-- Expected membership-query conclusion, about the very same coins as the estimator. -/
theorem CVTheorem11ExpectedImplementation.expectedQueryCost_le
    (I : CVTheorem11ExpectedImplementation)
    (n : ℕ) (K : Set (Space n)) (ε p R2 : ℝ)
    (hn : 1 ≤ n) (hε : 0 < ε) (hε1 : ε < 1)
    (hp : 0 < p) (hp1 : p < 1) (hK : CVAdmissible K R2) :
    (∫⁻ ω, (I.algorithm n).queryCost K ε p ω ∂(I.algorithm n).μ) ≤
      ENNReal.ofReal (I.runtimeConstant * cvComplexityShapeClipped n R2 ε p) :=
  (I.algorithm n).expectedQueryCost_le K ε p |>.trans
    (I.expectedBound_le n K ε p R2 hn hε hε1 hp hp1 hK)

/-- The order-notation form of the well-rounded runtime, for a fixed accuracy,
confidence, and explicit roundness constant `κ`.  A caller chooses `cost n` from an
actual family of admissible bodies and executions. -/
def CVWellRoundedRuntimeOrder (cost : ℕ → ℝ) (κ ε p : ℝ) : Prop :=
  cost =O[atTop] (fun n => cvComplexityShape n (κ * n) ε p)

/-- A uniform pointwise certificate implies the corresponding order statement.
This lemma is intentionally generic: obtaining its premise from
`CVTheorem11Implementation.queryCost_le` still requires a dimension-indexed family of
admissible bodies. -/
theorem cvWellRoundedRuntimeOrder_of_bound (cost : ℕ → ℝ) (κ ε p C : ℝ)
    (_hC : 0 ≤ C)
    (h : ∀ n, ‖cost n‖ ≤ C * ‖cvComplexityShape n (κ * n) ε p‖) :
    CVWellRoundedRuntimeOrder cost κ ε p := by
  exact IsBigO.of_bound C (Filter.Eventually.of_forall h)

#print axioms CVTheorem11ExpectedImplementation.correct
#print axioms CVTheorem11ExpectedImplementation.expectedQueryCost_le
#print axioms CVTheorem11Implementation.queryCost_eq_zero_dim_one

end Ttc
