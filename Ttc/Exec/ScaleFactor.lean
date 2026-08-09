/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.Inputs

/-!
# `Exec/ScaleFactor`: the dilation that makes `hvol` automatic

`Ttc.ttc_volume_estimate` carries a hypothesis

```
hvol : P.thresh / 4 ≤ volSol (atomSet atoms) φ
```

— "the solution set is at least a quarter of the threshold".  It is not decoration.
TTC's sketch is a `Poisson(Λ)` count with `Λ ≤ Vol(Sol F)`, and a Poisson variable
concentrates multiplicatively only once its mean is large; `Thresh` is exactly the
mean at which the Chernoff bound of `lem:chernoff` becomes useful.  An instance whose
solution set is small compared to `Thresh` is not one the estimator can handle.

But `hvol` is a hypothesis **about `Vol(Sol F)`**, the very quantity the algorithm is
trying to estimate.  Asking the caller for it is close to circular.  This file removes
the circularity the way the paper's own preprocessing does: **dilate the input**.

## The idea

Scaling `ℝⁿ` by `c ≥ 1` scales every volume by `cⁿ`, so running TTC on the dilated
instance and dividing the answer by `cⁿ` returns an estimate of the original volume,
with the same relative error.  Dilation is therefore free — and it can be used to push
`Vol(Sol F)` above `Thresh` before the estimator ever sees the instance.

The only thing needed to pick `c` is a **lower bound** on `Vol(Sol F)`, and the
algorithm already computes one: `alg:prec` (line 86) produces the inscribed radius
`γ̂`, a radius such that every polytope of the decomposition contains a ball of radius
`γ̂`.  One such ball already gives

```
Vol(Sol F) ≥ Vol(B(·, γ̂)) = γ̂ⁿ · Vₙ,        Vₙ := Vol(unit ball of ℝⁿ)
```

(`Ttc.ball_volume_le_volSol` below), and after dilating by `c` the inscribed radius is
`c·γ̂`, so the same bound reads `(c·γ̂)ⁿ · Vₙ`.  Choosing `c` to make that at least
`Thresh` is `Ttc.thresh_le_scaled_ball_volume`.

**No knowledge of `Vol` is required**: `Ttc.scaleFactor` is a function of `n`, the
parameter block, and `γ̂` only.  That is what makes this a preprocessing step rather
than a hypothesis.

## Why `max 1 (…)` and not an `n`-th root

The "exact" scale factor is `(Thresh / (Vₙ γ̂ⁿ))^{1/n}`, which needs `Real.rpow` and a
pile of `rpow`-arithmetic side conditions.  We use instead

```
c := max 1 (Thresh / (Vₙ · γ̂ⁿ))
```

which **overshoots**, deliberately.  Because `1 ≤ c` and `n ≥ 1` we have `c ≤ cⁿ`
(`le_self_pow`), so the un-rooted quotient already clears the threshold once raised to
the `n`-th power — the `n`-th root is replaced by a monotonicity step.  The cost is a
larger dilation than strictly necessary, and that cost is nil: the final estimate is
divided by `cⁿ`, so any `c` that clears the threshold is as good as any other.  The
`max 1` is what makes `1 ≤ c` available; it also keeps `c` a genuine dilation (never a
contraction) when the instance is already large enough.

## What is landed

| result | content |
| --- | --- |
| `Ttc.unitBallVol` | `Vₙ = Vol(B(0,1))` in `ℝⁿ`, as a plain real — no Gamma function |
| `Ttc.unitBallVol_pos` | `0 < Vₙ` |
| `Ttc.volume_ball_eq` | `Vol(B(x,r)) = rⁿ · Vₙ` for `r > 0` |
| `Ttc.volume_ball_eq_of_one_le_dim` | the same for `r ≥ 0`, when `n ≥ 1` |
| `Ttc.scaleFactor` | `c = max 1 (Thresh / (Vₙ γ̂ⁿ))` |
| `Ttc.one_le_scaleFactor`, `Ttc.scaleFactor_pos` | `1 ≤ c`, `0 < c` |
| `Ttc.thresh_le_scaled_ball_volume` | `Thresh ≤ (c·γ̂)ⁿ · Vₙ` |
| `Ttc.ball_volume_le_volSol` | `γ̂ⁿ · Vₙ ≤ Vol(Sol F)` from one inscribed ball |
| `Ttc.ball_volume_le_volSol_atomSet` | the same at `Ttc.atomSet` |

The dilation algebra itself — that scaling the atoms scales `volSol` by `cⁿ` — lives
elsewhere; this file supplies the scale factor and the two volume bounds it is chosen
to reconcile.

## Two small honesties about the hypotheses

* `Ttc.volume_ball_eq` is stated at `0 < r`, not `0 ≤ r`.  At `n = 0` and `r = 0` the
  `0 ≤ r` form is **false**: `Vol(∅) = 0` but `r ^ 0 · V₀ = 1`.  The `0 ≤ r` form is
  recovered under `1 ≤ n` as `Ttc.volume_ball_eq_of_one_le_dim`, and every consumer
  here has one of the two.
* `Ttc.ball_volume_le_volSol` takes the cube index `i` as an explicit argument rather
  than asserting existence: the index type `{d : Cube A // d ∈ D}` can be empty for a
  general `D`, and nothing in this file rules that out.
-/

namespace Ttc

open MeasureTheory Metric

variable {A : Type*} {n : ℕ}

/-! ## 1. The unit-ball volume

Abstractly, as a real.  Nothing below needs its closed form (`π^{n/2}/Γ(n/2+1)`); all
that is used is positivity and the Haar scaling law, and both come from the
measure-theoretic API.

`Ttc.unitBallVol` — line A10 of the preprocessing — is **defined in
`Model/Pseudocode`**, with the rest of the amended algorithm's vocabulary; only its
theory is here.
-/

/-- **`0 < Vₙ`.**  The unit ball is open and nonempty, so its measure is positive
(`MeasureTheory.measure_ball_pos`, Lebesgue measure being open-positive), and it is
bounded, so its measure is finite (`MeasureTheory.measure_ball_lt_top`); `toReal` is
positive exactly when both hold. -/
theorem unitBallVol_pos (n : ℕ) : 0 < unitBallVol n :=
  ENNReal.toReal_pos (measure_ball_pos volume (0 : Space n) one_pos).ne'
    measure_ball_lt_top.ne

/-- **The Haar scaling law, in real form: `Vol(B(x,r)) = rⁿ · Vₙ`.**

`MeasureTheory.Measure.addHaar_ball_mul_of_pos` gives it in `ℝ≥0∞`, with the exponent
`Module.finrank ℝ (Ttc.Space n)`, which is `n` by `finrank_euclideanSpace_fin`.
Translation-invariance is what removes the centre `x`.

Stated at `0 < r`; see the module docstring for why `0 ≤ r` would be false at `n = 0`,
and `Ttc.volume_ball_eq_of_one_le_dim` for the `0 ≤ r` form under `1 ≤ n`. -/
theorem volume_ball_eq (n : ℕ) (x : Space n) {r : ℝ} (hr : 0 < r) :
    (volume (Metric.ball x r)).toReal = r ^ n * unitBallVol n := by
  have hfr : Module.finrank ℝ (Space n) = n := finrank_euclideanSpace_fin
  have h := Measure.addHaar_ball_mul_of_pos (volume : Measure (Space n)) x hr 1
  rw [mul_one, hfr] at h
  rw [h, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), unitBallVol]

/-- **`Vol(B(x,r)) = rⁿ · Vₙ` for every `r ≥ 0`, once `n ≥ 1`.**  The extra hypothesis
buys the degenerate radius: at `r = 0` both sides are `0`, which needs `n ≠ 0`. -/
theorem volume_ball_eq_of_one_le_dim (n : ℕ) (hn : 1 ≤ n) (x : Space n) {r : ℝ}
    (hr : 0 ≤ r) :
    (volume (Metric.ball x r)).toReal = r ^ n * unitBallVol n := by
  rcases hr.lt_or_eq with h | h
  · exact volume_ball_eq n x h
  · subst h
    simp [Metric.ball_zero, zero_pow (by omega : n ≠ 0)]

/-! ## 2. The scale factor

A function of `n`, `P` and `γ̂` alone — in particular **not** of `Vol(Sol F)`.

`Ttc.scaleFactor` — line A10 of the preprocessing — is **defined in
`Model/Pseudocode`**; only its theory is here.
-/

/-- **`1 ≤ c`.**  Immediate from the `max`; this is the half of the definition that
replaces the `n`-th root, via `le_self_pow`. -/
theorem one_le_scaleFactor (n : ℕ) (P : Params) (gammaHat : ℝ) :
    1 ≤ scaleFactor n P gammaHat := le_max_left _ _

/-- **`0 < c`.**  A dilation, never a contraction or a collapse. -/
theorem scaleFactor_pos (n : ℕ) (P : Params) (gammaHat : ℝ) :
    0 < scaleFactor n P gammaHat :=
  lt_of_lt_of_le zero_lt_one (one_le_scaleFactor n P gammaHat)

/-- **The payoff: the dilated inscribed ball clears the threshold.**

`Vₙ · (c·γ̂)ⁿ ≥ Thresh` at `c = Ttc.scaleFactor n P gammaHat`, for `n ≥ 1` and
`γ̂ > 0`.  Combined with `Ttc.ball_volume_le_volSol` applied to the dilated instance,
this is what makes `hvol` automatic instead of hypothetical.

The proof is the un-rooting step: with `K := Thresh/(Vₙ γ̂ⁿ)` one has
`K · (Vₙ γ̂ⁿ) = Thresh` exactly, `K ≤ c` by `le_max_right`, and `c ≤ cⁿ` by
`le_self_pow` (needing `1 ≤ c` and `n ≠ 0`) — so `Thresh ≤ cⁿ · (Vₙ γ̂ⁿ)`, which is
the claim after `mul_pow`. -/
theorem thresh_le_scaled_ball_volume (n : ℕ) (hn : 1 ≤ n) (P : Params)
    {gammaHat : ℝ} (hg : 0 < gammaHat) :
    P.thresh ≤ (scaleFactor n P gammaHat * gammaHat) ^ n * unitBallVol n := by
  have hV : 0 < unitBallVol n := unitBallVol_pos n
  have hbase : 0 < unitBallVol n * gammaHat ^ n := mul_pos hV (pow_pos hg n)
  have hc1 : 1 ≤ scaleFactor n P gammaHat := one_le_scaleFactor n P gammaHat
  have hK : P.thresh / (unitBallVol n * gammaHat ^ n) ≤ scaleFactor n P gammaHat :=
    le_max_right _ _
  have hcn : scaleFactor n P gammaHat ≤ scaleFactor n P gammaHat ^ n :=
    le_self_pow₀ hc1 (by omega)
  calc P.thresh
      = P.thresh / (unitBallVol n * gammaHat ^ n) * (unitBallVol n * gammaHat ^ n) := by
        field_simp
    _ ≤ scaleFactor n P gammaHat ^ n * (unitBallVol n * gammaHat ^ n) :=
        mul_le_mul_of_nonneg_right (hK.trans hcn) hbase.le
    _ = (scaleFactor n P gammaHat * gammaHat) ^ n * unitBallVol n := by
        rw [mul_pow]; ring

/-! ## 3. One inscribed ball lower-bounds `Vol(Sol F)`

This is the input side of the same reconciliation: the algorithm knows `γ̂`, and `γ̂`
alone certifies a volume lower bound.  No volume additivity, and no disjointness of the
decomposition, is used — a single cube suffices, exactly as in
`Ttc/Witness/TwoCubeVol.lean`.
-/

/-- **`γ̂ⁿ · Vₙ ≤ Vol(Sol F)` from one inscribed ball.**

The ball `B(cen i, γ̂)` sits inside the region of cube `i` by hypothesis, and that
region sits inside `Sol(F)` by the soundness half of `thm:decomposition`
(`Ttc.region_subset_sol`); `measure_mono` and `ENNReal.toReal_mono` transport the
inclusion, the latter's side condition "the larger side is finite" being `hbdd` via
`Ttc.volume_ne_top_of_isBounded`.  `Ttc.volume_ball_eq` evaluates the left side.

`i` is an explicit argument, not an existential: `{d : Cube A // d ∈ D}` may be empty
for a general `D`. -/
theorem ball_volume_le_volSol {M : A → Set (Space n)} {φ : BForm A} {D : DNF A}
    (hD : IsDNFOf D φ) (hbdd : Bornology.IsBounded (sol M φ))
    {cen : {d : Cube A // d ∈ D} → Space n} {gammaHat : ℝ} (hg : 0 < gammaHat)
    (hball : ∀ i, Metric.ball (cen i) gammaHat ⊆ region M i.val)
    (i : {d : Cube A // d ∈ D}) :
    gammaHat ^ n * unitBallVol n ≤ volSol M φ := by
  have hsub : Metric.ball (cen i) gammaHat ⊆ sol M φ :=
    (hball i).trans (region_subset_sol hD i.property)
  have h := ENNReal.toReal_mono (volume_ne_top_of_isBounded hbdd) (measure_mono hsub)
  rwa [volume_ball_eq n (cen i) hg] at h

/-- **`Ttc.ball_volume_le_volSol` in the shape the executable statement uses**, over
`Ttc.atomSet` at a family of linear atoms.  `Ttc.atomSet` unfolds to
`fun a => (atoms a).halfspace` definitionally, so this is the previous theorem with no
work. -/
theorem ball_volume_le_volSol_atomSet {atoms : A → LinAtom n} {φ : BForm A} {D : DNF A}
    (hD : IsDNFOf D φ)
    (hbdd : Bornology.IsBounded (sol (fun a => (atoms a).halfspace) φ))
    {cen : {d : Cube A // d ∈ D} → Space n} {gammaHat : ℝ} (hg : 0 < gammaHat)
    (hball : ∀ i, Metric.ball (cen i) gammaHat
      ⊆ region (fun a => (atoms a).halfspace) i.val)
    (i : {d : Cube A // d ∈ D}) :
    gammaHat ^ n * unitBallVol n ≤ volSol (atomSet atoms) φ :=
  ball_volume_le_volSol hD hbdd hg hball i

end Ttc

#print axioms Ttc.unitBallVol_pos
#print axioms Ttc.volume_ball_eq
#print axioms Ttc.volume_ball_eq_of_one_le_dim
#print axioms Ttc.one_le_scaleFactor
#print axioms Ttc.scaleFactor_pos
#print axioms Ttc.thresh_le_scaled_ball_volume
#print axioms Ttc.ball_volume_le_volSol
#print axioms Ttc.ball_volume_le_volSol_atomSet
