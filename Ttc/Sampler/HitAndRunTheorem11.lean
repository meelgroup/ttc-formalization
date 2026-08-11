import Arlib.MarkovChains.Continuous.HitAndRun
import Arlib.MarkovChains.Continuous.Warmness
import Arlib.Probability.TV

/-!
# Lovász--Vempala Theorem 1.1 as a sampler contract

This file records the explicit transition deadline for Theorem 1.1 of Lovász and
Vempala, *Hit-and-Run from a Corner* (2005).

The paper prints `10^10 n^2 (R^2 / r^2) log (M / eps)`.  **That constant is wrong**, and
this file does not use it: the deadline below is
`2^56 n^2 (R^2 / r^2) log (8 M / eps^2)`, the shape actually proved in
`Arlib/MarkovChains/Continuous/HitAndRunMixing.lean`.  See
`Ttc.hitAndRunTheorem11Threshold` for the derivation showing the paper's constant is short
by a factor `≈ 2×10^5`, and for why the true constant lies strictly between the two.

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

/-- The real-valued transition threshold for Theorem 1.1 of *Hit-and-Run from a Corner*,
**at a constant this repository can actually prove**.

⚠ **This is deliberately NOT the paper's printed `10¹⁰ n² (R²/r²) log(M/eps)`, because that
constant is wrong.** `Arlib/MarkovChains/Continuous/HitAndRunMixing.lean` derives the chain:
Theorem 4.2 gives `Φ ≥ 1/(2²⁴ n D)` at inradius `1`; rescaling by `r` with `D ≤ 2R` gives
`Φ ≥ r/(2²⁵ n R)`; and Lovász–Simonovits Corollary 1.5 then needs
`m ≳ (2/Φ²)·ln(√M/eps) = 2⁵¹·n²(R²/r²)·ln(…)`.  Since `2⁵¹ ≈ 2.25×10¹⁵`, the paper's
`10¹⁰` is short by a factor `≈ 2×10⁵`.  Equivalently, `10¹⁰` would require
`Φ ≥ 1.4×10⁻⁵·r/(nR)` — constant `≈ 2¹⁶` — where Theorem 4.2 delivers `2²⁵`.  §5 of the
paper writes only "`C n²R²/r² ln(M/ε)` steps (`C` is a constant)", so the discrepancy never
appears in its text.

**The theorem is true; only the printed constant is wrong.**  The body below is exactly
`Arlib.MarkovChains.lvThreshold`, the shape that *is* proved (`tvLe_iterate_hitAndRun`).
Note the log argument is `8M/eps²`, not `M/eps` — this is not a bare constant swap.

Of the resulting `≈10⁷` gap against the paper, about `2×10⁵` is the paper's own arithmetic
and a factor `64` is this repository's `2²⁷` against Theorem 4.2's `2²⁴` (itself one factor
`10` in Lemma 3.3), so the true constant is smaller than `2⁵⁶` but provably larger than
`10¹⁰`. -/
noncomputable def hitAndRunTheorem11Threshold
    (n : ℕ) (r R M eps : ℝ) : ℝ :=
  2 ^ 56 * (n : ℝ) ^ 2 * R ^ 2 / r ^ 2 * Real.log (8 * M / eps ^ 2)

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
  have hlog : 0 ≤ Real.log (8 * M / eps ^ 2) := by
    apply Real.log_nonneg
    refine (one_le_div (by positivity)).2 ?_
    calc eps ^ 2 ≤ 1 ^ 2 := by nlinarith
      _ ≤ 8 * M := by nlinarith
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
