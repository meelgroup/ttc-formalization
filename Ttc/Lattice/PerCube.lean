/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Sampler.Contract

/-!
# `lem:lattice`, **per polytope**

`sections/analysis.tex:271` states `lem:lattice` for each polytope `P^i` of the
decomposition separately,

```
Vol(P^i) ∈ [ (1−η)/10^(ρn) · |P^i ∩ 𝕃ⁿ| , (1+η)/10^(ρn) · |P^i ∩ 𝕃ⁿ| ],
```

but `Ttc.lattice_of_dnf` (`Lattice/Assembled`) was only ever instantiated at the
**whole** formula, giving `Ttc.TtcProb.lattice_lo`/`lattice_hi` about `Sol(F)`.
Because of that, `Ttc.TtcProb.theta_window_cube_of_almostUniform`
(`Sampler/Contract`) had to take the per-cube halves as *hypotheses*
`hlatLo`/`hlatHi`.

This file discharges them. The route is to instantiate `Ttc.lattice_of_dnf` at
the **singleton DNF `[i]`** for a cube `i` of the decomposition:

* `Ttc.cubeForm` turns a cube into the formula it denotes (the conjunction of its
  atoms), `Ttc.singleton_isDNFOf` says `[i]` is a DNF of that formula, and
  `Ttc.sol_cubeForm` identifies its solution set with `Ttc.region M i` — so the
  conclusion really is about the cube's own polytope. This mirrors what
  `Ttc/Witness/Box.lean` does for the box witness (`Ttc.boxForm`,
  `Ttc.boxDNF_isDNFOf`);
* `Ttc.card_facetIndex_singleton_le` transfers the facet bound: the facets of
  `[i]` inject into those of the full DNF, so `Ttc.TtcProb.facets_le` still
  applies;
* every remaining side condition of `Ttc.lattice_of_dnf` — positivity, `1 ≤ m`,
  the inscribed ball, finite volume, nonzero normals — is the corresponding
  `Ttc.TtcProb` field restricted to the one cube.

**No hypothesis had to be added.** `Ttc.TtcProb.lattice_cube_lo`/`lattice_cube_hi`
have exactly the shape of `hlatLo`/`hlatHi`, and
`Ttc.TtcProb.theta_window_cube` is `theta_window_cube_of_almostUniform` with
them discharged, so it assumes only `eq:almostuniform` and non-emptiness.
-/

namespace Ttc

open MeasureTheory Set

variable {A : Type*} {n : ℕ}

/-! ## A cube, as a formula

A cube is a list of literals; on a **positive** cube each literal is just its
atom, so the formula it denotes is `Ttc.conj` of the atom list. Positivity is
genuinely needed: a negated literal denotes the complement, and `Ttc.conj` has no
way to say that.
-/

/-! ### The positive-cube helper layer

This is the **single** cube-formula layer in the repo.
`Ttc/Findings/CubeLattice.lean` once carried a parallel `Ttc.cubeForm` (with
`Ttc.sol_cubeForm`, `Ttc.isDNFOf_singleton`, …) doing the same job; those eight
declarations have been deleted and `Ttc.lattice_of_cube` re-based onto the
lemmas below.

The duplicate threaded an extra atom `a : A` through every statement, to seed
the conjunction with the tautology `a ∨ ¬a`, justified as "`Ttc.BForm` has no
`true` constructor" — which was false: `Ttc.BForm.tt` exists
(`Model/Prelude.lean`). The seed was not merely cosmetic, since it made the
lemmas inapplicable when `A` is empty and forced callers to invent an atom they
may not have. Dropping it strictly strengthened `lattice_of_cube`.

This layer uses `BForm.tt` and needs no seed. It lives in namespace
`Ttc.PosCube`.

**Positivity costs nothing here.** These lemmas require `Cube.IsPositive`, where
the deleted `litForm` was polarity-blind. That extra generality was unusable:
`Ttc.lattice_of_dnf` (`Ttc/Lattice/Assembled.lean`) takes `DNF.IsPositive`
unconditionally, which at the singleton `[c]` *is* `Cube.IsPositive c`. So no
consumer could ever have exercised the negated-literal case.
-/

namespace PosCube

/-- **The formula a cube denotes**: the conjunction of its atoms. On a positive
cube (`Ttc.Cube.IsPositive`) this is faithful — see `Ttc.holds_cubeForm`. -/
def cubeForm (c : Cube A) : BForm A := conj (c.map Lit.atom)

/-- **The cube's formula is negation-free**, so it is a legitimate input formula
in the sense of `Ttc.BForm.IsPositive`. -/
theorem cubeForm_isPositive (c : Cube A) : (cubeForm c).IsPositive :=
  isPositive_conj _

/-- **The formula says exactly what the cube says**, on a positive cube. -/
theorem holds_cubeForm {c : Cube A} (hc : Cube.IsPositive c) (v : A → Prop) :
    (cubeForm c).holds v ↔ c.holds v := by
  rw [cubeForm, holds_conj]
  constructor
  · intro h l hl
    have hp : l.pos = true := hc l hl
    simp only [Lit.holds, hp, cond_true]
    exact h l.atom (List.mem_map_of_mem hl)
  · intro h a ha
    rw [List.mem_map] at ha
    obtain ⟨l, hl, rfl⟩ := ha
    have hp : l.pos = true := hc l hl
    have hlv := h l hl
    simpa only [Lit.holds, hp, cond_true] using hlv

/-- A one-cube DNF holds exactly when its cube does. -/
theorem dnf_holds_singleton (v : A → Prop) (c : Cube A) :
    DNF.holds v [c] ↔ c.holds v := by
  constructor
  · rintro ⟨d, hd, hdv⟩
    rw [List.mem_singleton] at hd
    exact hd ▸ hdv
  · intro h
    exact ⟨c, List.mem_singleton_self c, h⟩

/-- **The one-cube DNF `[c]` really is a DNF of `Ttc.cubeForm c`** — the
`Ttc.IsDNFOf` hypothesis `Ttc.lattice_of_dnf` needs, at the singleton. -/
theorem singleton_isDNFOf {c : Cube A} (hc : Cube.IsPositive c) :
    IsDNFOf [c] (cubeForm c) := fun v =>
  (dnf_holds_singleton v c).trans (holds_cubeForm hc v).symm

/-- **A one-cube DNF of a positive cube is positive** — the `Ttc.DNF.IsPositive`
hypothesis, at the singleton. -/
theorem singleton_isPositive {c : Cube A} (hc : Cube.IsPositive c) :
    DNF.IsPositive [c] := by
  intro d hd
  rw [List.mem_singleton] at hd
  exact hd ▸ hc

/-- **The solution set of a cube's formula is the cube's own region.** This is
what makes `Ttc.lattice_of_dnf`'s conclusion at `[c]` a statement about `P(c)`
rather than about a formula. -/
theorem sol_cubeForm {X : Type*} (M : A → Set X) {c : Cube A} (hc : Cube.IsPositive c) :
    sol M (cubeForm c) = region M c := by
  ext x
  exact holds_cubeForm hc (induced M x)

/-! ## The two counting side conditions

`Ttc.lattice_of_dnf` bounds the singleton DNF's cube count by `P.m` and its facet
count by `P.r`. The first is `1 ≤ m` (`Ttc.Params.hm`); the second needs the
singleton's facets to inject into the full DNF's.
-/

/-- **A one-cube DNF has one cube.** -/
theorem card_cubes_singleton (c : Cube A) :
    Nat.card {d : Cube A // d ∈ ([c] : DNF A)} = 1 := by
  haveI : Unique {d : Cube A // d ∈ ([c] : DNF A)} :=
    { default := ⟨c, List.mem_singleton_self c⟩
      uniq := by rintro ⟨d, hd⟩; exact Subtype.ext (List.mem_singleton.1 hd) }
  exact Nat.card_unique

/-- **The facets of a one-cube DNF inject into those of any DNF containing the
cube.** A facet of `[c]` is a literal of `c`; since `c ∈ D`, that same literal is
a facet of `D`. -/
theorem card_facetIndex_singleton_le {D : DNF A} {c : Cube A} (hc : c ∈ D) :
    Nat.card (FacetIndex ([c] : DNF A)) ≤ Nat.card (FacetIndex D) := by
  classical
  haveI : Finite {d : Cube A // d ∈ D} := D.finite_toSet.to_subtype
  haveI : ∀ d : {d : Cube A // d ∈ D}, Finite {l : Lit A // l ∈ d.val} :=
    fun d => d.val.finite_toSet.to_subtype
  haveI : Finite (FacetIndex D) := inferInstance
  have hmem : ∀ d : {d : Cube A // d ∈ ([c] : DNF A)}, d.val ∈ D := by
    rintro ⟨d, hd⟩
    rw [List.mem_singleton] at hd
    exact hd ▸ hc
  refine Nat.card_le_card_of_injective
    (fun j : FacetIndex ([c] : DNF A) => (⟨⟨j.1.val, hmem j.1⟩, j.2⟩ : FacetIndex D)) ?_
  rintro ⟨⟨d₁, hd₁⟩, ⟨l₁, hl₁⟩⟩ ⟨⟨d₂, hd₂⟩, ⟨l₂, hl₂⟩⟩ h
  rw [List.mem_singleton] at hd₁ hd₂
  subst hd₁
  subst hd₂
  simpa using h

/-! ## `lem:lattice`, per cube -/

end PosCube

open PosCube

namespace TtcProb

variable {A : Type*} {n : ℕ} (T : TtcProb A n)

/-- **`lem:lattice` for a single polytope** (`sections/analysis.tex:271`).

`Ttc.lattice_of_dnf` instantiated at the singleton DNF `[i]` and the formula
`Ttc.cubeForm i`. Every hypothesis it wants is a `Ttc.TtcProb` field restricted
to the one cube: positivity from `isPositive`, the ball from `ball_subset`,
finiteness from `volume_ne_top`, the normals from `normal_ne_zero`, the cube
count from `Ttc.Params.hm`, and the facet count from `facets_le` via
`Ttc.card_facetIndex_singleton_le`. Nothing extra is assumed. -/
theorem lattice_cube_two_sided {i : Cube A} (hi : i ∈ T.toDNF T.φ) :
    (1 - T.P.eta) * (((region T.M i ∩ fineLattice n (latticeScale T.ρ)).ncard : ℝ)
          / (latticeScale T.ρ) ^ n) ≤ (volume (region T.M i)).toReal ∧
      (volume (region T.M i)).toReal ≤ (1 + T.P.eta) *
        (((region T.M i ∩ fineLattice n (latticeScale T.ρ)).ncard : ℝ)
          / (latticeScale T.ρ) ^ n) := by
  have hcpos : Cube.IsPositive i := T.isPositive i hi
  have hm : (Nat.card {c : Cube A // c ∈ ([i] : DNF A)} : ℝ) ≤ T.P.m := by
    rw [card_cubes_singleton]
    exact_mod_cast T.P.hm
  have hr : (Nat.card (FacetIndex ([i] : DNF A)) : ℝ) ≤ T.P.r := by
    refine le_trans ?_ T.facets_le
    exact_mod_cast card_facetIndex_singleton_le hi
  have hAnz : ∀ j : FacetIndex ([i] : DNF A),
      0 < ∑ k, (T.atoms j.2.val.atom).coeff k ^ 2 := by
    rintro ⟨⟨d, hd⟩, ⟨l, hl⟩⟩
    rw [List.mem_singleton] at hd
    subst hd
    exact T.normal_ne_zero ⟨⟨_, hi⟩, ⟨l, hl⟩⟩
  have hball : ∀ j : {c : Cube A // c ∈ ([i] : DNF A)},
      Metric.ball (T.cen ⟨i, hi⟩) T.gammaHat
        ⊆ region (fun a => (T.atoms a).halfspace) j.val := by
    intro j
    rw [List.mem_singleton.1 j.property, ← T.M_eq]
    exact T.ball_subset ⟨i, hi⟩
  have hfin : ∀ j : {c : Cube A // c ∈ ([i] : DNF A)},
      volume (region (fun a => (T.atoms a).halfspace) j.val) ≠ ⊤ := by
    intro j
    rw [List.mem_singleton.1 j.property, ← T.M_eq]
    exact T.volume_ne_top ⟨i, hi⟩
  have h := lattice_of_dnf T.atoms (singleton_isDNFOf hcpos) (singleton_isPositive hcpos)
    T.P T.dim_eq hm hr hAnz (fun _ => T.cen ⟨i, hi⟩) T.hgammaHat hball hfin T.rho_eq
  obtain ⟨hlo, hhi⟩ := h.1
  rw [← T.M_eq, volSol, normalisedCount, latticeCount, sol_cubeForm T.M hcpos] at hlo hhi
  exact ⟨hlo, hhi⟩

/-- **`lem:lattice` for a single polytope, lower half** — exactly the shape of
`Ttc.TtcProb.theta_window_cube_of_almostUniform`'s `hlatLo`. -/
theorem lattice_cube_lo {i : Cube A} (hi : i ∈ T.toDNF T.φ) :
    (1 - T.P.eta) * (((region T.M i ∩ fineLattice n (latticeScale T.ρ)).ncard : ℝ)
        / (latticeScale T.ρ) ^ n) ≤ (volume (region T.M i)).toReal :=
  (T.lattice_cube_two_sided hi).1

/-- **`lem:lattice` for a single polytope, upper half** — exactly the shape of
`Ttc.TtcProb.theta_window_cube_of_almostUniform`'s `hlatHi`. -/
theorem lattice_cube_hi {i : Cube A} (hi : i ∈ T.toDNF T.φ) :
    (volume (region T.M i)).toReal ≤ (1 + T.P.eta) *
      (((region T.M i ∩ fineLattice n (latticeScale T.ρ)).ncard : ℝ)
        / (latticeScale T.ρ) ^ n) :=
  (T.lattice_cube_two_sided hi).2

/-- **The Invariant for a single polytope, with no lattice hypothesis left.**

`Ttc.TtcProb.theta_window_cube_of_almostUniform` with its `hlatLo`/`hlatHi`
discharged by `Ttc.TtcProb.lattice_cube_lo`/`lattice_cube_hi`. What remains
assumed is only `eq:almostuniform` for this cube's sampler and that the cube is
not lattice-empty; `Vol_ED`'s accuracy and `lem:lattice` are both theorems. -/
theorem theta_window_cube {i : Cube A} (hi : i ∈ T.toDNF T.φ)
    {D : Space n → ℝ} {x : Space n}
    (hN : 0 < (region T.M i ∩ fineLattice n (latticeScale T.ρ)).ncard)
    (hunif : AlmostUniform D (region T.M i ∩ fineLattice n (latticeScale T.ρ))
      T.P.epsPrime)
    (hx : x ∈ region T.M i ∩ fineLattice n (latticeScale T.ρ)) :
    (1 - T.P.epsPrime) ^ 2 * (1 - T.P.eta) / (latticeScale T.ρ) ^ n ≤ D x * T.vol i ∧
      D x * T.vol i
        ≤ (1 + T.P.epsPrime) ^ 2 * (1 + T.P.eta) / (latticeScale T.ρ) ^ n :=
  T.theta_window_cube_of_almostUniform hi hN hunif
    (T.lattice_cube_lo hi) (T.lattice_cube_hi hi) hx

end TtcProb

/-! ## Axiom profile (`CLAUDE.md` §4) -/

#print axioms TtcProb.lattice_cube_lo
#print axioms TtcProb.lattice_cube_hi
#print axioms TtcProb.theta_window_cube

end Ttc
