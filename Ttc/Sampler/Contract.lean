/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Ttc.Lattice.Assembled
import Ttc.Volume.Bridge

/-!
# `Sampler/Contract`: `eq:almostuniform`, and the Invariant's window

`GenerateSamples` is only **almost** uniform: `sections/related.tex:21` asks of
the distribution `D` it draws from that

```
∀ x ∈ K ∩ 𝕃ⁿ,  (1 − ε)/|K ∩ 𝕃ⁿ| ≤ Pr[x] ≤ (1 + ε)/|K ∩ 𝕃ⁿ|.
```

`Ttc.AlmostUniform` is that predicate. This file proves it does what
`analysis.tex:271` uses it for: combined with `Vol_ED`'s two-sided accuracy and
with `lem:lattice`, it puts each lattice point's rate `θ x = D x · t` inside the
paper's Invariant window

```
(1 − ε')²(1 − η)/10^(ρ·n)  ≤  θ x  ≤  (1 + ε')²(1 + η)/10^(ρ·n),
```

which is exactly the pair of `Ttc.TtcProb` fields `theta_lo`/`theta_hi`.
-/

namespace Ttc

open MeasureTheory

/-! ## `eq:almostuniform`

Stated over a `Set` with `Set.ncard`, not over a `Finset` with `Finset.card`.
Two reasons: the set the paper quantifies over is `K ∩ 𝕃ⁿ`, an *intersection of
two sets* rather than a listed finite collection, and `Ttc.latticeCount`
(`Model/Prelude`) already measures exactly that intersection with `Set.ncard`.
Composing with the rest of `Ttc` therefore needs no bridge lemma at all.

`Set.ncard` of an infinite set is `0`, and `x / 0 = 0` in Lean, so on an infinite
`S` the predicate degenerates to `0 ≤ D x ∧ D x ≤ 0`. That is a *stronger*
statement than intended, never a weaker one, so nothing below is vacuous — and
the consumers all carry `0 < S.ncard` anyway.
-/

/-- **`eq:almostuniform`** (`sections/related.tex:21`). The mass `D` puts on each
point of `S` is within a multiplicative `(1 ± ε)` of the uniform mass `1/|S|`.

`D` is not required to be a probability distribution: no `∑ = 1` is asked for,
because nothing downstream reads one — `Ttc.theta_window` consumes only the
pointwise two-sided bound. -/
def AlmostUniform {α : Type*} (D : α → ℝ) (S : Set α) (eps : ℝ) : Prop :=
  ∀ x ∈ S, (1 - eps) / S.ncard ≤ D x ∧ D x ≤ (1 + eps) / S.ncard

namespace AlmostUniform

variable {α : Type*} {D : α → ℝ} {S : Set α} {eps : ℝ} {x : α}

/-- The lower half of `eq:almostuniform`, on its own. -/
theorem lower (h : AlmostUniform D S eps) (hx : x ∈ S) :
    (1 - eps) / S.ncard ≤ D x := (h x hx).1

/-- The upper half of `eq:almostuniform`, on its own. -/
theorem upper (h : AlmostUniform D S eps) (hx : x ∈ S) :
    D x ≤ (1 + eps) / S.ncard := (h x hx).2

/-- An almost-uniform mass is nonnegative, provided the accuracy `ε` is at most
`1`. This is the only place `ε ≤ 1` is needed on the sampler side, and it is what
makes the products in `Ttc.theta_window` orientable. -/
theorem nonneg (h : AlmostUniform D S eps) (heps : eps ≤ 1) (hx : x ∈ S) : 0 ≤ D x :=
  le_trans (div_nonneg (by linarith) (Nat.cast_nonneg _)) (h.lower hx)

end AlmostUniform

/-- **Non-vacuity** (`CLAUDE.md` §11). The *exactly* uniform mass `1/|S|` is
almost uniform at every accuracy `ε ≥ 0`, over any `S` whatsoever — so
`Ttc.AlmostUniform` is not an empty hypothesis, and `Ttc.theta_window` below is
not proving a window about nothing.

Note this holds even when `S` is infinite (`S.ncard = 0`), where both sides
collapse to `0`. -/
theorem almostUniform_uniform {α : Type*} (S : Set α) {eps : ℝ} (heps : 0 ≤ eps) :
    AlmostUniform (fun _ => 1 / (S.ncard : ℝ)) S eps := by
  intro x _
  have hinv : (0 : ℝ) ≤ ((S.ncard : ℝ))⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  constructor
  · simp only [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith) hinv
  · simp only [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith) hinv

/-! ## The Invariant's window

`analysis.tex:271` composes three two-sided facts into the Invariant. Written
with `N = |P ∩ 𝕃ⁿ|`, `V = Vol(P)`, `t` the value `Vol_ED(P, ε', δ')` returned,
`D x` the sampler's mass at `x` and `R = 10^(ρ·n)`:

* `(1 − ε')·V ≤ t ≤ (1 + ε')·V`      — `Vol_ED`'s accuracy;
* `(1 − ε')/N ≤ D x ≤ (1 + ε')/N`    — `eq:almostuniform`;
* `(1 − η)·N/R ≤ V ≤ (1 + η)·N/R`    — `lem:lattice`, normalised.

The rate is `θ x = D x · t`, and the three factors telescope: the `N` from the
sampler cancels the `N` from `lem:lattice`, and the `V` from `lem:lattice`
cancels the `V` from `Vol_ED`, leaving `1/R` scaled by `(1 ± ε')²(1 ± η)`.

Everything here is pure real arithmetic over named scalars — no `Ttc.TtcProb`,
no measure theory — so it is reusable and cheap to check. `N` is a *real*, with
`0 < N` carried explicitly: `Set.ncard` of a degenerate cube is `0`, and
`x / 0 = 0` would silently make the lower bound false, so the positivity may not
be left implicit. -/

/-- **The Invariant, lower half.** `θ x = D x · t ≥ (1 − ε)²(1 − η)/R`.

Only the *lower* halves of the three inputs are needed; `0 ≤ D x` is derived from
the sampler's lower bound rather than assumed, which is why `ε ≤ 1` appears. -/
theorem theta_lower_bound {N V t D eps eta R : ℝ}
    (hN : 0 < N) (hR : 0 < R) (heps1 : eps ≤ 1) (heta1 : eta ≤ 1)
    (hvol : (1 - eps) * V ≤ t)
    (huni : (1 - eps) / N ≤ D)
    (hlat : (1 - eta) * (N / R) ≤ V) :
    (1 - eps) ^ 2 * (1 - eta) / R ≤ D * t := by
  have h1e : (0 : ℝ) ≤ 1 - eps := by linarith
  have h1n : (0 : ℝ) ≤ 1 - eta := by linarith
  have hD : 0 ≤ D := le_trans (div_nonneg h1e hN.le) huni
  have ht : (1 - eps) * ((1 - eta) * (N / R)) ≤ t :=
    le_trans (mul_le_mul_of_nonneg_left hlat h1e) hvol
  have htnn : (0 : ℝ) ≤ (1 - eps) * ((1 - eta) * (N / R)) := by positivity
  calc (1 - eps) ^ 2 * (1 - eta) / R
      = ((1 - eps) / N) * ((1 - eps) * ((1 - eta) * (N / R))) := by
        field_simp
    _ ≤ D * t := mul_le_mul huni ht htnn hD

/-- **The Invariant, upper half.** `θ x = D x · t ≤ (1 + ε)²(1 + η)/R`.

`0 ≤ t` is a hypothesis here rather than a derivation: the upper halves alone
cannot orient a product, and in `Ttc.theta_window` it comes free from the lower
halves. No sign condition on `D` is needed — `D ≤ (1 + ε)/N` and `0 ≤ t` already
orient the product. -/
theorem theta_upper_bound {N V t D eps eta R : ℝ}
    (hN : 0 < N) (hR : 0 < R) (heps0 : 0 ≤ eps) (ht0 : 0 ≤ t)
    (hvol : t ≤ (1 + eps) * V)
    (huni : D ≤ (1 + eps) / N)
    (hlat : V ≤ (1 + eta) * (N / R)) :
    D * t ≤ (1 + eps) ^ 2 * (1 + eta) / R := by
  have hb : (0 : ℝ) ≤ (1 + eps) / N := div_nonneg (by linarith) hN.le
  have ht : t ≤ (1 + eps) * ((1 + eta) * (N / R)) :=
    le_trans hvol (mul_le_mul_of_nonneg_left hlat (by linarith))
  calc D * t ≤ ((1 + eps) / N) * ((1 + eps) * ((1 + eta) * (N / R))) :=
        mul_le_mul huni ht ht0 hb
    _ = (1 + eps) ^ 2 * (1 + eta) / R := by field_simp

/-- **THE WINDOW.** `analysis.tex:271`'s Invariant, from its three stated inputs.

Given a polytope with `N > 0` lattice points and volume `V`, an estimate `t`
accurate to a relative `ε`, a sampler mass `D` almost uniform to a relative `ε`,
and `lem:lattice` relating `V` to `N/R`, the rate `θ = D · t` satisfies

`(1 − ε)²(1 − η)/R ≤ θ ≤ (1 + ε)²(1 + η)/R`,

which is exactly the pair `Ttc.TtcProb.theta_lo` / `Ttc.TtcProb.theta_hi` at
`ε = ε'`, `η = ε/8` and `R = 10^(ρ·n)`. -/
theorem theta_window {N V t D eps eta R : ℝ}
    (hN : 0 < N) (hR : 0 < R) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (heta1 : eta ≤ 1)
    (hvolLo : (1 - eps) * V ≤ t) (hvolHi : t ≤ (1 + eps) * V)
    (huniLo : (1 - eps) / N ≤ D) (huniHi : D ≤ (1 + eps) / N)
    (hlatLo : (1 - eta) * (N / R) ≤ V) (hlatHi : V ≤ (1 + eta) * (N / R)) :
    (1 - eps) ^ 2 * (1 - eta) / R ≤ D * t ∧
      D * t ≤ (1 + eps) ^ 2 * (1 + eta) / R := by
  have hNR : (0 : ℝ) ≤ N / R := by positivity
  have hV0 : 0 ≤ V := le_trans (mul_nonneg (by linarith) hNR) hlatLo
  have ht0 : 0 ≤ t := le_trans (by nlinarith) hvolLo
  exact ⟨theta_lower_bound hN hR heps1 heta1 hvolLo huniLo hlatLo,
    theta_upper_bound hN hR heps0 ht0 hvolHi huniHi hlatHi⟩

/-! ## Wiring to `Ttc`'s objects

`Ttc.theta_window` above is stated over bare reals. This section instantiates it
at the development's actual quantities — `Ttc.latticeCount`,
`Ttc.normalisedCount`, `Ttc.latticeScale`, `Ttc.Params.epsPrime`,
`Ttc.Params.eta` — so that its conclusion is *syntactically* the pair of
`Ttc.TtcProb` fields `theta_lo`/`theta_hi`.

**Two instantiations, because the repo's two inputs live at two different
granularities.** `analysis.tex:271` runs the argument once per polytope `P^i`:
its `lem:lattice` input is `Vol(P^i) ∈ [(1±η)|P^i ∩ 𝕃ⁿ|/10^(ρn)]` and its
`Vol_ED` input is `t ∈ [(1±ε')Vol(P^i)]`. In this repo:

* `Ttc.TtcProb.volED_lo`/`volED_hi` (`Ttc/Volume/Bridge.lean:272`) are **per
  cube**, about `Vol(P(cᵢ))` and `T.vol i`;
* `Ttc.TtcProb.lattice_lo`/`lattice_hi` (`Ttc/Lattice/Assembled.lean:222`) are
  **global**, about `Vol(Sol(F))` and `|Sol(F) ∩ 𝕃ⁿ|` — `Ttc.lattice_of_dnf` is
  only ever instantiated at the whole formula.

So no single lemma can consume both as theorems. `theta_window_cube_of_almostUniform`
is the paper's shape: it uses `volED_lo`/`volED_hi` and takes the *per-cube*
`lem:lattice` as a hypothesis. `theta_window_of_almostUniform` is the global
shape: it uses `lattice_lo`/`lattice_hi` and takes the accuracy of the *total*
volume estimate as a hypothesis. Both are fully proved; between them every input
named in the task is discharged from an existing theorem.
-/

namespace TtcProb

variable {A : Type*} {n : ℕ} (T : TtcProb A n)

/-- `ε' = ε/12 ≥ 0`, from `0 < ε`. -/
theorem epsPrime_nonneg : 0 ≤ T.P.epsPrime := by
  have h := T.hε0
  rw [Params.epsPrime, T.eps_eq]
  linarith

/-- `ε' = ε/12 ≤ 1`, from `ε ≤ 1`. -/
theorem epsPrime_le_one : T.P.epsPrime ≤ 1 := by
  have h := T.hε1
  rw [Params.epsPrime, T.eps_eq]
  linarith

/-- `η = ε/8 ≥ 0`, from `0 < ε`. -/
theorem eta_nonneg : 0 ≤ T.P.eta := by
  have h := T.hε0
  rw [Params.eta, T.eps_eq]
  linarith

/-- `η = ε/8 ≤ 1`, from `ε ≤ 1`. -/
theorem eta_le_one : T.P.eta ≤ 1 := by
  have h := T.hε1
  rw [Params.eta, T.eps_eq]
  linarith

/-- `10^(ρ·n) > 0` — the denominator of the Invariant never vanishes, so the
window's divisions are genuine. -/
theorem latticeScale_pow_pos : 0 < (latticeScale T.ρ) ^ n :=
  pow_pos (latticeScale_pos T.ρ) n

/-- **`lem:lattice`, lower half, with the count spelled out.** `Ttc.TtcProb.lattice_lo`
with `T.L` replaced by `|Sol(F) ∩ 𝕃ⁿ| / 10^(ρ·n)` and `ε/8` by `η`, which is the
exact shape `Ttc.theta_window`'s `hlatLo` wants. -/
theorem lattice_lo_normalised :
    (1 - T.P.eta) * ((latticeCount T.M T.φ T.ρ : ℝ) / (latticeScale T.ρ) ^ n)
      ≤ volSol T.M T.φ := by
  have h := T.lattice_lo
  have hη : T.P.eta = T.ε / 8 := by rw [Params.eta, T.eps_eq]
  rw [hη]
  rwa [T.L_eq, normalisedCount] at h

/-- **`lem:lattice`, upper half, with the count spelled out.** -/
theorem lattice_hi_normalised :
    volSol T.M T.φ
      ≤ (1 + T.P.eta) * ((latticeCount T.M T.φ T.ρ : ℝ) / (latticeScale T.ρ) ^ n) := by
  have h := T.lattice_hi
  have hη : T.P.eta = T.ε / 8 := by rw [Params.eta, T.eps_eq]
  rw [hη]
  rwa [T.L_eq, normalisedCount] at h

/-- **The Invariant for a single polytope** — `analysis.tex:271`'s own shape.

`Vol_ED`'s two-sided accuracy on `P(cᵢ)` is *not* a hypothesis: it is
`Ttc.TtcProb.volED_lo`/`volED_hi`, theorems of `Ttc/Volume/Bridge.lean`. What is
assumed is `eq:almostuniform` for this cube's sampler (another agent's job), the
per-cube `lem:lattice` (`hlatLo`/`hlatHi` — see the section docstring: the repo
proves `lem:lattice` only for `Sol(F)`), and that the cube is not lattice-empty.

The conclusion is literally `theta_lo`/`theta_hi` with `θ x := D x · vol i`. -/
theorem theta_window_cube_of_almostUniform
    {i : Cube A} (hi : i ∈ T.toDNF T.φ)
    {D : Space n → ℝ} {x : Space n}
    (hN : 0 < (region T.M i ∩ fineLattice n (latticeScale T.ρ)).ncard)
    (hunif : AlmostUniform D (region T.M i ∩ fineLattice n (latticeScale T.ρ))
      T.P.epsPrime)
    (hlatLo : (1 - T.P.eta) *
        (((region T.M i ∩ fineLattice n (latticeScale T.ρ)).ncard : ℝ)
          / (latticeScale T.ρ) ^ n) ≤ (volume (region T.M i)).toReal)
    (hlatHi : (volume (region T.M i)).toReal ≤ (1 + T.P.eta) *
        (((region T.M i ∩ fineLattice n (latticeScale T.ρ)).ncard : ℝ)
          / (latticeScale T.ρ) ^ n))
    (hx : x ∈ region T.M i ∩ fineLattice n (latticeScale T.ρ)) :
    (1 - T.P.epsPrime) ^ 2 * (1 - T.P.eta) / (latticeScale T.ρ) ^ n ≤ D x * T.vol i ∧
      D x * T.vol i
        ≤ (1 + T.P.epsPrime) ^ 2 * (1 + T.P.eta) / (latticeScale T.ρ) ^ n := by
  have hNR : (0 : ℝ) < ((region T.M i ∩ fineLattice n (latticeScale T.ρ)).ncard : ℝ) := by
    exact_mod_cast hN
  exact theta_window hNR T.latticeScale_pow_pos T.epsPrime_nonneg T.epsPrime_le_one
    T.eta_le_one (T.volED_lo i hi) (T.volED_hi i hi) (hunif.lower hx) (hunif.upper hx)
    hlatLo hlatHi

/-- **The Invariant for the whole solution set.**

`lem:lattice` is *not* a hypothesis here: it is `Ttc.TtcProb.lattice_lo`/`lattice_hi`,
theorems of `Ttc/Lattice/Assembled.lean`. What is assumed is `eq:almostuniform`
for a sampler on `Sol(F) ∩ 𝕃ⁿ`, that the total estimate `t` is accurate to a
relative `ε'`, and that `Sol(F)` is not lattice-empty.

Same conclusion as `Ttc.TtcProb.theta_window_cube_of_almostUniform`, hence again
literally `theta_lo`/`theta_hi`, with `θ x := D x · t`. -/
theorem theta_window_of_almostUniform
    {D : Space n → ℝ} {t : ℝ} {x : Space n}
    (hN : 0 < latticeCount T.M T.φ T.ρ)
    (hunif : AlmostUniform D (sol T.M T.φ ∩ fineLattice n (latticeScale T.ρ))
      T.P.epsPrime)
    (hvolLo : (1 - T.P.epsPrime) * volSol T.M T.φ ≤ t)
    (hvolHi : t ≤ (1 + T.P.epsPrime) * volSol T.M T.φ)
    (hx : x ∈ sol T.M T.φ ∩ fineLattice n (latticeScale T.ρ)) :
    (1 - T.P.epsPrime) ^ 2 * (1 - T.P.eta) / (latticeScale T.ρ) ^ n ≤ D x * t ∧
      D x * t ≤ (1 + T.P.epsPrime) ^ 2 * (1 + T.P.eta) / (latticeScale T.ρ) ^ n := by
  have hNR : (0 : ℝ) < (latticeCount T.M T.φ T.ρ : ℝ) := by exact_mod_cast hN
  exact theta_window hNR T.latticeScale_pow_pos T.epsPrime_nonneg T.epsPrime_le_one
    T.eta_le_one hvolLo hvolHi (hunif.lower hx) (hunif.upper hx)
    T.lattice_lo_normalised T.lattice_hi_normalised

end TtcProb

/-! ## Axiom profile (`CLAUDE.md` §4) -/

#print axioms theta_window
#print axioms almostUniform_uniform
#print axioms TtcProb.theta_window_cube_of_almostUniform
#print axioms TtcProb.theta_window_of_almostUniform

end Ttc
