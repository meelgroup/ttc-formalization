/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Sampler.Rates
import Ttc.Sampler.Contract

/-!
# `Exec/RegimeSum`: the general lower bound on the total level-`0` rate mass

`alg:ttc`'s `big` guard asks that the total level-`0` rate `Λ = ∑ₛ θ s` be at
least a constant fraction of the threshold; `sections/analysis.tex:295` states it
as `Λ ≥ (1 − ε')·Thresh/8`. This file proves the *general* lower bound behind
that inequality — general in the sense that the DNF `D` may have arbitrarily many
cubes, and different enumerated lattice points may be assigned to different cubes.

## The bound is **pointwise**, so no fiber counting is needed

The one structural surprise is that this needs no combinatorics at all. One might
expect to have to count, for each cube `i ∈ D`, how many of the `N = |Sol(F) ∩ 𝕃ⁿ|`
enumerated points `Ttc.cubeAt` assigned to `i` — a fiber count — and then sum the
per-cube contributions. That is not necessary, because the per-point bound

```
θ s = sampD (cubeAt s) (ptE s) · vol (cubeAt s)  ≥  (1 − ε')²(1 − η) / 10^(ρ·n)
```

*does not mention the cube at all* once it is proved: the cube's own lattice-point
count `Nᵢ = |P(cᵢ) ∩ 𝕃ⁿ|` appears in the sampler's lower bound `(1 − ε')/Nᵢ` and
again, inverted, in the volume lower bound `vol cᵢ ≥ (1 − ε')(1 − η)·Nᵢ/10^(ρ·n)`,
and the two occurrences cancel. Every enumerated point therefore contributes at
least `(1 − ε')²(1 − η)/10^(ρ·n)` **regardless of which cube it was assigned to**,
and the sum is just `N` copies of that — which is `(1 − ε')²(1 − η)` times
`Ttc.normalisedCount M φ ρ = N/10^(ρ·n)` by definition.

This is what makes `analysis.tex:295` provable from a *volume* hypothesis
(`hvolLo`, the `Vol_ED` accuracy, together with `hlat`, `lem:lattice` per cube)
rather than from any assumption about how `Ttc.cubeOf` distributes points among
overlapping cubes — which is fortunate, since `Ttc.cubeOf` is a classical choice
and nothing is known about that distribution.

`Ttc.Box.sum_rates_box_ge` (`Exec/Regime`) is the single-cube special case, where
`Ttc.cubeAt` is constant and `Nᵢ = N`; `Ttc.rate_ge_pointwise` below is the same
argument with `Ttc.cubeAt s` varying, and with the extra `lem:lattice` factor.

## Finiteness is load-bearing

`Set.ncard` of an infinite set is `0`, and `x / 0 = 0` in Lean, so on a
lattice-infinite region `Ttc.AlmostUniform`'s lower bound would degenerate to
`0 ≤ sampD i x` and prove nothing. `hfinLat` is exactly what rules that out: it
turns "`P(cᵢ) ∩ 𝕃ⁿ` contains the enumerated point" into `0 < Nᵢ`, via
`Set.ncard_pos`.

Every hypothesis below is abstract — nothing is assumed about `sampD` or `vol`
beyond `eq:almostuniform` and the two volume inequalities — so this file is
independent of how those two are later constructed.
-/

namespace Ttc

open MeasureTheory

variable {A : Type*} {n : ℕ}

/-! ## The pointwise bound

The crux. Stated for a single index `s`, with the cube it is assigned to left
implicit — the conclusion mentions only the global scale `10^(ρ·n)`.
-/

/-- **The Invariant's lower half at every enumerated point.**

For each `s`, the rate `Ttc.rates M φ D ρ sampD vol s` is at least
`(1 − ε')²(1 − η)/10^(ρ·n)`, whichever cube of `D` the point `ptE s` happened to
be assigned to by `Ttc.cubeAt`.

The proof is `Ttc.theta_lower_bound` (`Sampler/Contract`) instantiated at
`N = |P(cᵢ) ∩ 𝕃ⁿ|`, `V = Vol(P(cᵢ))`, `t = vol cᵢ`, `D = sampD cᵢ (ptE s)` and
`R = 10^(ρ·n)`, for `cᵢ = Ttc.cubeAt M φ D ρ s`. The only work is producing
`0 < N`, and that is where `hfinLat` is spent: `ptE s` lies in the region
(`Ttc.cubeAt_spec`) and in the lattice (`Ttc.latticeEnum_mem`), so the
intersection is a nonempty finite set. -/
theorem rate_ge_pointwise {M : A → Set (Space n)} {φ : BForm A} {D : DNF A} {ρ : ℤ}
    (hDNF : IsDNFOf D φ) (hle : HasLatticeEnum M φ ρ)
    (sampD : Cube A → Space n → ℝ) (vol : Cube A → ℝ) {ep η : ℝ}
    (hep1 : ep ≤ 1) (hη1 : η ≤ 1)
    (hfinLat : ∀ i : {c : Cube A // c ∈ D},
      (region M i.val ∩ fineLattice n (latticeScale ρ)).Finite)
    (hAU : ∀ i : {c : Cube A // c ∈ D},
      AlmostUniform (sampD i.val) (region M i.val ∩ fineLattice n (latticeScale ρ)) ep)
    (hvolLo : ∀ i : {c : Cube A // c ∈ D},
      (1 - ep) * (volume (region M i.val)).toReal ≤ vol i.val)
    (hlat : ∀ i : {c : Cube A // c ∈ D},
      (1 - η) * (((region M i.val ∩ fineLattice n (latticeScale ρ)).ncard : ℝ)
          / (latticeScale ρ) ^ n)
        ≤ (volume (region M i.val)).toReal)
    (s : Fin (latticeCount M φ ρ)) :
    (1 - ep) ^ 2 * (1 - η) / (latticeScale ρ) ^ n ≤ rates M φ D ρ sampD vol s := by
  obtain ⟨hmem, hreg⟩ := cubeAt_spec hDNF hle s
  -- the cube `ptE s` was assigned to, as an element of the index subtype
  set i : {c : Cube A // c ∈ D} := ⟨cubeAt M φ D ρ s, hmem⟩ with hidef
  have hx : latticeEnum M φ ρ s ∈ region M i.val ∩ fineLattice n (latticeScale ρ) :=
    ⟨hreg, (latticeEnum_mem hle s).2⟩
  -- `0 < Nᵢ`: the intersection is finite and contains the enumerated point
  have hNpos : 0 < (region M i.val ∩ fineLattice n (latticeScale ρ)).ncard :=
    (Set.ncard_pos (hfinLat i)).2 ⟨_, hx⟩
  have hNR : (0 : ℝ) < ((region M i.val ∩ fineLattice n (latticeScale ρ)).ncard : ℝ) := by
    exact_mod_cast hNpos
  have hR : (0 : ℝ) < (latticeScale ρ) ^ n := pow_pos (latticeScale_pos ρ) n
  have h := theta_lower_bound hNR hR hep1 hη1 (hvolLo i) ((hAU i).lower hx) (hlat i)
  simpa only [rates, hidef] using h

/-! ## The sum

`Finset.sum_le_sum` over `Finset.univ : Finset (Fin (latticeCount M φ ρ))`, then
`Finset.sum_const`. The resulting constant `N · ((1 − ε')²(1 − η)/10^(ρ·n))` is
`(1 − ε')²(1 − η) · Ttc.normalisedCount M φ ρ` after unfolding
`Ttc.normalisedCount`, which is `N/10^(ρ·n)` *by definition*
(`Model/Prelude`).
-/

/-- **`Λ ≥ (1 − ε')²(1 − η)·L`** — the general lower bound on the total level-`0`
rate mass, `L = Ttc.normalisedCount M φ ρ` being the paper's normalised lattice
count `|Sol(F) ∩ 𝕃ⁿ|/10^(ρ·n)`.

This is `alg:ttc`'s `big` guard in the form `sections/analysis.tex:295` uses it,
with no hypothesis whatsoever on how the enumerated points are distributed among
the cubes of `D`: by `Ttc.rate_ge_pointwise` the bound holds summand by summand.

No sign conditions on `ep`/`η` are needed: `ep ≤ 1` and `η ≤ 1` carry the whole
argument (the sum step is a `ring` identity, `normalisedCount` being `latticeCount /
(latticeScale ρ)^n` by definition).  An earlier draft carried `0 ≤ ep` and `0 ≤ η`;
they were never used and are dropped rather than left as dead weight. -/
theorem sum_rates_ge_of_pointwise {M : A → Set (Space n)}
    {φ : BForm A} {D : DNF A} {ρ : ℤ}
    (hDNF : IsDNFOf D φ) (hle : HasLatticeEnum M φ ρ)
    (sampD : Cube A → Space n → ℝ) (vol : Cube A → ℝ) {ep η : ℝ}
    (hep1 : ep ≤ 1) (hη1 : η ≤ 1)
    (hfinLat : ∀ i : {c : Cube A // c ∈ D},
      (region M i.val ∩ fineLattice n (latticeScale ρ)).Finite)
    (hAU : ∀ i : {c : Cube A // c ∈ D},
      AlmostUniform (sampD i.val) (region M i.val ∩ fineLattice n (latticeScale ρ)) ep)
    (hvolLo : ∀ i : {c : Cube A // c ∈ D},
      (1 - ep) * (volume (region M i.val)).toReal ≤ vol i.val)
    (hlat : ∀ i : {c : Cube A // c ∈ D},
      (1 - η) * (((region M i.val ∩ fineLattice n (latticeScale ρ)).ncard : ℝ)
          / (latticeScale ρ) ^ n)
        ≤ (volume (region M i.val)).toReal) :
    (1 - ep) ^ 2 * (1 - η) * normalisedCount M φ ρ
      ≤ ∑ s, rates M φ D ρ sampD vol s := by
  have key : ∀ s : Fin (latticeCount M φ ρ),
      (1 - ep) ^ 2 * (1 - η) / (latticeScale ρ) ^ n ≤ rates M φ D ρ sampD vol s :=
    fun s => rate_ge_pointwise hDNF hle sampD vol hep1 hη1 hfinLat hAU hvolLo hlat s
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum (fun s _ => key s))
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, normalisedCount]
  ring

/-! ## Axiom profile (`CLAUDE.md` §4) -/

#print axioms rate_ge_pointwise
#print axioms sum_rates_ge_of_pointwise

end Ttc
