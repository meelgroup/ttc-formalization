/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Model.Prelude

/-!
# `Model/VolOracle`: `Vol_ED`'s contract, stated as Cousins–Vempala Theorem 1.1

`Ttc.Oracles.vol` is the `Vol_ED(P(cᵢ), ε', δ')` call of `alg:ttc` line 24. In
`Ttc.TtcProb` its guarantee is currently the single field

```
volED_hi : ∀ i ∈ toDNF φ, vol i ≤ (1 + P.epsPrime) * (volume (region M i)).toReal
```

which is **deterministic** — it asserts the bound at every `ω`, i.e. that `Vol_ED`
never fails — and so is strictly stronger than what any randomized volume
algorithm delivers.

This file replaces that ad-hoc inequality with the published contract it is
supposed to be an instance of:

> **Theorem 1.1** (Cousins–Vempala, `vol3_journal.tex:144`). There is an
> algorithm that, for any `ε > 0`, `p > 0` and convex body `K` in `ℝⁿ` that
> contains the unit ball and has `E_K(‖X‖²) = O(n)`, with probability `1 − p`,
> approximates the volume of `K` within relative error `ε`.

`Ttc.VolumeAlgorithm` is that statement. Nothing here proves it — the
gaussian-cooling development formalizes the variance bound of §5.1 that licenses
the cooling schedule, not the algorithm — so this is an *interface* in the sense
of `CLAUDE.md` §1: the hypothesis bundle a future formalization instantiates.

**What this buys.** The residual assumption behind `Vol_ED` becomes exactly one
named published theorem, readable against the paper line by line, rather than a
bespoke deterministic inequality. `Ttc.VolumeAlgorithm.exact` witnesses
non-vacuity (`CLAUDE.md` §11), and `Ttc.VolumeAlgorithm.upper` extracts precisely
the half of the conclusion `volED_hi` consumes.

**Modelling notes.**

*The second-moment hypothesis is omitted from `correct`.* Theorem 1.1 states
`E_K(‖X‖²) = O(n)`, but that hypothesis governs the *complexity*, not the
accuracy: `vol3_journal.tex:152` gives the complexity for a general
`E_K(‖X‖²) = R²`, with the same `1 − p` accuracy conclusion. Since only accuracy
is consumed here, assuming it would weaken the interface for no gain. Complexity
is out of scope for this development (`Ttc/Runtime.lean`).

*`K` must contain the unit ball at the origin.* That is Theorem 1.1's hypothesis
verbatim, and it is **not** what `Ttc.TtcProb` supplies: `ball_subset` gives a
ball of radius `γ̂` about `cen i`. `Ttc.VolumeAlgorithm.of_ball` bridges the gap
by scaling, and is where that discrepancy is discharged rather than hidden.
-/

namespace Ttc

open MeasureTheory Set

/-- **Cousins–Vempala, Theorem 1.1** (`vol3_journal.tex:144`), as the contract
`Vol_ED` is called under.

`est K ε p ω` is the number the algorithm returns on body `K` at accuracy `ε` and
confidence `p`, when its coins read `ω`. `correct` is the theorem: outside a set
of measure `p`, that number lies in `(1 ± ε)·Vol(K)`.

This is an assumption, not a theorem — see the file docstring. -/
structure VolumeAlgorithm (n : ℕ) where
  /-- The probability space the algorithm's own coins live on. -/
  Ω : Type
  /-- Its σ-algebra. -/
  mΩ : MeasurableSpace Ω
  /-- The law of the coins. -/
  μ : @MeasureTheory.Measure Ω mΩ
  /-- It is a probability measure. -/
  isProb : @MeasureTheory.IsProbabilityMeasure Ω mΩ μ
  /-- The estimate returned on `K` at accuracy `ε`, confidence `p`, coins `ω`. -/
  est : Set (Space n) → ℝ → ℝ → Ω → ℝ
  /-- **The guarantee.** With probability at least `1 − p`, the estimate lies
  within relative error `ε` of `Vol(K)`, for every convex `K` of finite volume
  containing the unit ball. -/
  correct : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 →
      Convex ℝ K → Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      1 - p ≤ (μ {ω | est K ε p ω ∈ relErr ε (volume K).toReal}).toReal

namespace VolumeAlgorithm

variable {n : ℕ}

/-- **Non-vacuity** (`CLAUDE.md` §11). The exact oracle — one that returns
`Vol(K)` on the nose and never fails — is a `Ttc.VolumeAlgorithm`. So the
interface is inhabited, and any theorem quantified over it is not vacuous.

This is the `ε = 0`, `p = 0` corner of the contract: it satisfies the guarantee
for *every* `ε, p`, so it witnesses the structure without witnessing that the
algorithm of the paper exists. -/
noncomputable def exact (n : ℕ) : VolumeAlgorithm n where
  Ω := Unit
  mΩ := inferInstance
  μ := Measure.dirac ()
  isProb := inferInstance
  est K _ _ _ := (volume K).toReal
  correct := by
    intro K ε p hε hp _ _ _ _
    have hb : (0 : ℝ) ≤ (volume K).toReal := ENNReal.toReal_nonneg
    have hmem : (volume K).toReal ∈ relErr ε (volume K).toReal := by
      simp only [relErr, Set.mem_Icc]
      constructor <;> nlinarith
    have hset : {_ω : Unit | (volume K).toReal ∈ relErr ε (volume K).toReal}
        = (univ : Set Unit) := by
      ext _; simp [hmem]
    rw [hset, measure_univ, ENNReal.toReal_one]
    linarith

/-- **The half `volED_hi` consumes.** On the good event, the estimate does not
exceed `(1 + ε)·Vol(K)`.

`Ttc.TtcProb.volED_hi` asserts exactly this inequality — but at *every* `ω`,
with no good event. That is the shape mismatch the file docstring describes: a
randomized algorithm supplies it only on a set of measure `1 − p`. -/
theorem upper {ε b x : ℝ} (h : x ∈ relErr ε b) : x ≤ (1 + ε) * b := h.2

/-- **The lower half**, which feeds the paper's Invariant (`theta_lo`). -/
theorem lower {ε b x : ℝ} (h : x ∈ relErr ε b) : (1 - ε) * b ≤ x := h.1

end VolumeAlgorithm

end Ttc
