import Arlib.MarkovChains.Continuous.HitAndRun
import Arlib.MarkovChains.Continuous.Warmness
import Arlib.Probability.TV

/-!
# Lovász--Vempala Theorem 1.1 as a sampler contract

This file records the explicit transition deadline in Theorem 1.1 of Lovász and
Vempala, *Hit-and-Run from a Corner* (2005):

`10^10 n^2 (R^2 / r^2) log (M / eps)`.

The analytic theorem is not silently postulated.  Its presently unformalised part is the
field of `HitAndRunTheorem11Input`.  In particular, constructing that structure requires
proving the paper's mixing theorem.  The integer deadline and the fact that it is strictly
larger than the real-valued threshold are proved below without additional assumptions.

The paper phrases its exceptional-start hypothesis using a Radon--Nikodym density.  The
measure inequality below is the equivalent form actually needed by a sampler interface:
away from a measurable exceptional set `S`, the start is dominated by `M` times the
uniform target, while the start gives `S` mass at most `eps / 2`.

The number here counts hit-and-run transitions.  It does not claim that a transition
(sampling a direction and finding a chord endpoint) has unit bit/arithmetic cost.
-/

namespace Ttc

open MeasureTheory Metric
open scoped ENNReal

/-- The real-valued transition threshold in Theorem 1.1 of *Hit-and-Run from a Corner*. -/
noncomputable def hitAndRunTheorem11Threshold
    (n : ℕ) (r R M eps : ℝ) : ℝ :=
  (10 : ℝ) ^ 10 * (n : ℝ) ^ 2 * R ^ 2 / r ^ 2 * Real.log (M / eps)

/-- A natural-number deadline strictly beyond the real threshold.

`Nat.floor + 1`, rather than a ceiling, reflects the strict inequality `m > ...` in the
paper.  The threshold is nonnegative in every intended application (`r,R > 0`, `M ≥ 1`,
`0 < eps ≤ 1`). -/
noncomputable def hitAndRunTheorem11Steps
    (n : ℕ) (r R M eps : ℝ) : ℕ :=
  ⌊hitAndRunTheorem11Threshold n r R M eps⌋₊ + 1

/-- The chosen number of transitions satisfies the paper's strict deadline. -/
theorem hitAndRunTheorem11Threshold_lt_steps
    (n : ℕ) {r R M eps : ℝ}
    (hr : 0 < r) (hR : 0 ≤ R) (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    hitAndRunTheorem11Threshold n r R M eps
      < (hitAndRunTheorem11Steps n r R M eps : ℝ) := by
  have hlog : 0 ≤ Real.log (M / eps) := by
    apply Real.log_nonneg
    exact (one_le_div heps0).2 (le_trans heps1 hM)
  have hthreshold : 0 ≤ hitAndRunTheorem11Threshold n r R M eps := by
    unfold hitAndRunTheorem11Threshold
    exact mul_nonneg
      (div_nonneg (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg (n : ℝ))) (sq_nonneg R))
        (sq_nonneg r)) hlog
  simpa [hitAndRunTheorem11Steps] using
    (Nat.lt_floor_add_one (hitAndRunTheorem11Threshold n r R M eps))

/-- Explicit analytic input corresponding to Lovász--Vempala Theorem 1.1.

Keeping this as data makes the formalisation boundary auditable: no declaration in this
file asserts the missing weighted-isoperimetric/localisation argument. -/
structure HitAndRunTheorem11Input where
  mixing : ∀ {n : ℕ} (hn : 1 ≤ n)
      {K : Set (EuclideanSpace ℝ (Fin n))}
      (hKm : MeasurableSet K) (hKc : Convex ℝ K) (hKcl : IsClosed K)
      {zin zout : EuclideanSpace ℝ (Fin n)} {r R : ℝ}
      (hr : 0 < r) (hR : 0 ≤ R)
      (hin : closedBall zin r ⊆ K) (hout : K ⊆ closedBall zout R)
      {sigma : Measure (EuclideanSpace ℝ (Fin n))}
      [IsProbabilityMeasure sigma]
      {M eps : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
      {S : Set (EuclideanSpace ℝ (Fin n))} (hSm : MeasurableSet S)
      (hS : sigma S ≤ ENNReal.ofReal (eps / 2))
      (hdom : ∀ A, MeasurableSet A →
        sigma (A \ S) ≤ ENNReal.ofReal M *
          Arlib.uniformOn volume K (A \ S))
      {m : ℕ}
      (hm : hitAndRunTheorem11Threshold n r R M eps < (m : ℝ)),
      Arlib.TVLe
        (Arlib.MarkovChains.iterate (Arlib.MarkovChains.hitAndRun K) sigma m)
        (Arlib.uniformOn volume K) (ENNReal.ofReal eps)

/-- The contract instantiated at the canonical `floor + 1` transition count. -/
theorem HitAndRunTheorem11Input.at_steps
    (H : HitAndRunTheorem11Input) {n : ℕ} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKm : MeasurableSet K) (hKc : Convex ℝ K) (hKcl : IsClosed K)
    {zin zout : EuclideanSpace ℝ (Fin n)} {r R : ℝ}
    (hr : 0 < r) (hR : 0 ≤ R)
    (hin : closedBall zin r ⊆ K) (hout : K ⊆ closedBall zout R)
    {sigma : Measure (EuclideanSpace ℝ (Fin n))}
    [IsProbabilityMeasure sigma]
    {M eps : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hSm : MeasurableSet S)
    (hS : sigma S ≤ ENNReal.ofReal (eps / 2))
    (hdom : ∀ A, MeasurableSet A →
      sigma (A \ S) ≤ ENNReal.ofReal M * Arlib.uniformOn volume K (A \ S)) :
    Arlib.TVLe
      (Arlib.MarkovChains.iterate (Arlib.MarkovChains.hitAndRun K) sigma
        (hitAndRunTheorem11Steps n r R M eps))
      (Arlib.uniformOn volume K) (ENNReal.ofReal eps) := by
  exact H.mixing hn hKm hKc hKcl hr hR hin hout hM heps0 heps1 hSm hS hdom
    (hitAndRunTheorem11Threshold_lt_steps n hr hR hM heps0 heps1)

end Ttc
