/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.EstData

/-!
# `Volume/Oracle`: `Vol_ED`'s contract, stated as Cousins–Vempala Theorem 1.1

`Ttc.Oracles.vol` is the `Vol_ED(P(cᵢ), ε', δ')` call of `alg:ttc` line 24. Its
guarantee used to be a single `Ttc.TtcProb` field,

```
volED_hi : ∀ i ∈ toDNF φ, vol i ≤ (1 + P.epsPrime) * (volume (region M i)).toReal
```

which was **deterministic** — it asserted the bound at every `ω`, i.e. that
`Vol_ED` never fails — and so was strictly stronger than what any randomized
volume algorithm delivers. That field is gone; what replaces it is the published
contract it was supposed to be an instance of:

> **Theorem 1.1** (Cousins–Vempala, `vol3_journal.tex:144`). There is an
> algorithm that, for any `ε > 0`, `p > 0` and convex body `K` in `ℝⁿ` that
> contains the unit ball and has `E_K(‖X‖²) = O(n)`, with probability `1 − p`,
> approximates the volume of `K` within relative error `ε`.

**Nothing here proves it.** This is an *interface* in the sense of `CLAUDE.md`
§1: the hypothesis bundle a future formalization instantiates. See
[`CV-ROADMAP.md`](../../CV-ROADMAP.md) for what closing it involves, and
[`END-TO-END-PLAN.md`](../../END-TO-END-PLAN.md) Phase 5 for the plan.

Everything *proved* about it — the rounding bridge that discharges Theorem 1.1's
"contains the unit ball" hypothesis, the union bound over the `m` calls, and the
former field recovered as a theorem — lives in `Ttc/Volume/Bridge.lean`, so that
this file stays what it claims to be: declarations and assumptions, no proofs.

`Ttc.roundBody`, the normalisation `Vol_ED` is called on, used to be defined here and now
lives one file down in [`Ttc/Volume/EstData.lean`](EstData.lean), together with the rest of
what the constructed oracle *computes* — so that `Model/Pseudocode` can reach those
definitions without importing this structure. The name is unchanged.

**Modelling notes.**

*The second-moment hypothesis is omitted from `correct`.* Theorem 1.1 states
`E_K(‖X‖²) = O(n)`, but that hypothesis governs the *complexity*, not the
accuracy: `vol3_journal.tex:152` gives the complexity for a general
`E_K(‖X‖²) = R²`, with the same `1 − p` accuracy conclusion. Since only accuracy
is consumed here, assuming it would weaken the interface for no gain. Complexity
is out of scope (`Ttc/Runtime.lean`).

*`K` must contain the unit ball at the origin.* That is Theorem 1.1's hypothesis
verbatim, and it is **not** what `Ttc.TtcProb` supplies: `ball_subset` gives a
ball of radius `γ̂` about `cen i`. `Ttc.VolumeAlgorithm.of_ball`
(`Ttc/Volume/Bridge.lean`) bridges the gap by scaling along `Ttc.roundBody`, and
is where that discrepancy is discharged rather than hidden.
-/

namespace Ttc

open MeasureTheory Pointwise

/-- **Cousins–Vempala, Theorem 1.1** (`vol3_journal.tex:144`), as the contract
`Vol_ED` is called under.

`est K ε p ω` is the number the algorithm returns on body `K` at accuracy `ε` and
confidence `p`, when its coins read `ω`. `correct` is the theorem: outside a set
of measure `p`, that number lies in `(1 ± ε)·Vol(K)`.

This is an assumption, not a theorem — see the section docstring. -/
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
  /-- **The estimate is a measurable function of the coins.** Not part of the
  paper's statement, and not a mathematical assumption about the algorithm: it is
  what makes "the failure event" a set with a measure at all. Without it the
  *complement* of the good event has no upper bound — subadditivity alone gives
  `1 ≤ μ(S) + μ(Sᶜ)`, the wrong direction — so the `m` calls of `alg:ttc` could
  not be union-bounded. Any algorithm reading finitely many coins satisfies it. -/
  est_meas : ∀ (K : Set (Space n)) (ε p : ℝ), @Measurable Ω ℝ mΩ _ (est K ε p)
  /-- **The guarantee.** With probability at least `1 − p`, the estimate lies
  within relative error `ε` of `Vol(K)`, for every convex `K` of finite volume
  containing the unit ball. -/
  correct : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 →
      Convex ℝ K → Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      1 - p ≤ (μ {ω | est K ε p ω ∈ relErr ε (volume K).toReal}).toReal

/-- **The good event of the `m` `Vol_ED` calls**: every call's rescaled estimate
lands within a relative `ε'` of its polytope's volume.

Indexed by position in the DNF, so `m` is literally the loop count of `alg:ttc`
line 23. `cen j` and `γ` describe the inscribed ball of `K j`; the estimate is the
one Theorem 1.1 delivers on the *normalised* body `Ttc.roundBody`, rescaled by
`γⁿ` (`Ttc.VolumeAlgorithm.of_ball`). -/
def volGood {n m : ℕ} (V : VolumeAlgorithm n) (γ ε' δ' : ℝ)
    (cen : Fin m → Space n) (K : Fin m → Set (Space n)) : Set V.Ω :=
  {ω | ∀ j, γ ^ n * V.est (roundBody (cen j) γ (K j)) ε' δ' ω
        ∈ relErr ε' (volume (K j)).toReal}

end Ttc
