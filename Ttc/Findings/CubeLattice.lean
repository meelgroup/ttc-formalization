/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Lattice.Assembled

/-!
# `lem:lattice` for a single polytope

The paper applies `lem:lattice` (`sections/analysis.tex:269`) to **one** polytope
`P^i` at a time, whereas `Ttc.lattice_of_dnf` (`Lattice/Assembled`) is
stated globally, over `Sol(F)` for a whole DNF. This file recovers the paper's
per-polytope form by instantiating the global theorem at the **singleton DNF**
`[c]`, whose solution set is exactly the cube's region `P(c)`.

`Ttc.lattice_of_dnf` is phrased against a Boolean formula `φ` together with a
proof that the DNF represents it, so the singleton instance needs a formula whose
solution set is `P(c)`. That formula is `Ttc.cubeForm`, the conjunction of the
cube's literals. **`Ttc.BForm` has no `true` constructor**, so — exactly as for
`Ttc.boxForm` in `Witness/Box`, which is the template this file generalises
— the conjunction is seeded with the tautology `a ∨ ¬a` at an arbitrary atom `a`,
which the caller supplies.

The resulting `Ttc.lattice_of_cube` is stated directly about `Ttc.region` and its
lattice-point count, with no `Ttc.sol`/`Ttc.volSol` wrapper left in sight: the
two-sided `(1 ± η)` bound between the polytope's **volume** and its **normalised
lattice-point count** `|P(c) ∩ 𝕃ⁿ| / 10^(ρn)`.
-/

namespace Ttc

open MeasureTheory Set

variable {A : Type*} {n : ℕ}

/-! ## The formula of a cube -/

/-- The formula a single literal denotes: the bare atom when the literal is
positive, its negation otherwise — matching `Ttc.Lit.holds`. -/
def litForm (l : Lit A) : BForm A :=
  if l.pos then .atom l.atom else .neg (.atom l.atom)

/-- **A literal's formula says exactly what the literal says.** -/
theorem litForm_holds (l : Lit A) (v : A → Prop) : (litForm l).holds v ↔ l.holds v := by
  cases hb : l.pos <;> simp [litForm, Lit.holds, hb, BForm.holds]

/-- Folding `BForm.and` over a list of literals conjoins them onto the seed. The
polarity-blind analogue of `Ttc.holds_foldr_and` (`Witness/Box`). -/
theorem holds_foldr_litForm (L : List (Lit A)) (ψ : BForm A) (v : A → Prop) :
    (L.foldr (fun l φ => BForm.and (litForm l) φ) ψ).holds v
      ↔ (∀ l ∈ L, l.holds v) ∧ ψ.holds v := by
  induction L with
  | nil => simp
  | cons l L ih =>
      simp only [List.foldr_cons, BForm.holds, ih, List.mem_cons, litForm_holds]
      constructor
      · rintro ⟨hl, hL, hψ⟩
        exact ⟨fun j hj => hj.elim (fun h => h ▸ hl) (hL j), hψ⟩
      · rintro ⟨hall, hψ⟩
        exact ⟨hall l (Or.inl rfl), fun j hj => hall j (Or.inr hj), hψ⟩

/-- **The formula of a cube**: the conjunction of its literals. Needs a seed atom
`a`, because `Ttc.BForm` has no `true` constructor and the cube may be empty; the
seed contributes the tautology `a ∨ ¬a`, so it does not change the semantics.
Generalises `Ttc.boxForm` (`Witness/Box`) from the box's cube to any cube. -/
def cubeForm (c : Cube A) (a : A) : BForm A :=
  c.foldr (fun l φ => .and (litForm l) φ) (.or (.atom a) (.neg (.atom a)))

/-- **The formula says exactly what the cube says**, on every Boolean
assignment — the seed tautology is discharged by excluded middle. -/
theorem cubeForm_holds (c : Cube A) (a : A) (v : A → Prop) :
    (cubeForm c a).holds v ↔ c.holds v := by
  rw [cubeForm, holds_foldr_litForm]
  constructor
  · rintro ⟨h, -⟩
    exact h
  · intro h
    exact ⟨h, Classical.em (v a)⟩

/-- **The singleton DNF `[c]` represents `Ttc.cubeForm c a`** — the hypothesis
`Ttc.lattice_of_dnf` takes as `IsDNFOf`. -/
theorem isDNFOf_singleton (c : Cube A) (a : A) : IsDNFOf [c] (cubeForm c a) := by
  intro v
  rw [cubeForm_holds]
  constructor
  · rintro ⟨c', hc', hcv⟩
    rwa [List.mem_singleton.1 hc'] at hcv
  · intro h
    exact ⟨c, List.mem_singleton_self c, h⟩

/-- **`Sol` of a cube's formula is the cube's region** `P(c)`. -/
theorem sol_cubeForm (M : A → Set (Space n)) (c : Cube A) (a : A) :
    sol M (cubeForm c a) = region M c := by
  ext x
  exact cubeForm_holds c a (induced M x)

/-! ## The singleton DNF is one cube, and one cube only -/

/-- The cubes of the singleton DNF `[c]` number exactly one — what
`Ttc.lattice_of_dnf`'s `m`-bound is applied to. -/
theorem card_singleton_cubes (c : Cube A) :
    Nat.card {c' : Cube A // c' ∈ ([c] : DNF A)} = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun x y => ?_⟩, ⟨⟨c, List.mem_singleton_self c⟩⟩⟩
  exact Subtype.ext ((List.mem_singleton.1 x.2).trans (List.mem_singleton.1 y.2).symm)

/-! ## `lem:lattice`, per polytope -/

/-- **`lem:lattice` for a single polytope** (`sections/analysis.tex:269`).

For one positive cube `c`, the Lebesgue volume of its region `P(c)` is within
`(1 ± η)` of the normalised lattice count `|P(c) ∩ 𝕃ⁿ| / 10^(ρn)`, at `η = ε/8`
and the precision `ρ = ⌈log₁₀(γ/γ̂)⌉` that `alg:prec` computes — under exactly the
paper's per-polytope hypotheses: the atoms are linear, no literal of the cube is
negated, the polytope contains an `ℓ₂`-ball of radius `γ̂` about `cen` and has
finite volume, every facet has a nonzero normal, and `r` bounds the facet count.
That the intersection is finite (so the count is a genuine natural number) comes
out of the same theorem rather than being assumed.

This is `Ttc.lattice_of_dnf` instantiated at the singleton DNF `[c]`; the bound
`Nat.card {c' // c' ∈ [c]} ≤ m` it needs is `Ttc.card_singleton_cubes` together
with `Ttc.Params.hm`, so no extra hypothesis on `m` is required. -/
theorem lattice_of_cube (atoms : A → LinAtom n) (c : Cube A) (a : A)
    (hpos : Cube.IsPositive c) (P : Params) (hn : P.n = n)
    (hr : (Nat.card (FacetIndex ([c] : DNF A)) : ℝ) ≤ P.r)
    (hAnz : ∀ j : FacetIndex ([c] : DNF A), 0 < ∑ k, (atoms j.2.val.atom).coeff k ^ 2)
    (cen : Space n) {gammaHat : ℝ} (hg : 0 < gammaHat)
    (hball : Metric.ball cen gammaHat ⊆ region (fun b => (atoms b).halfspace) c)
    (hfin : volume (region (fun b => (atoms b).halfspace) c) ≠ ⊤)
    {ρ : ℤ} (hρ : ρ = P.precision gammaHat) :
    ((1 - P.eta) * (((region (fun b => (atoms b).halfspace) c
            ∩ fineLattice n (latticeScale ρ)).ncard : ℝ) / (latticeScale ρ) ^ n)
          ≤ (volume (region (fun b => (atoms b).halfspace) c)).toReal ∧
        (volume (region (fun b => (atoms b).halfspace) c)).toReal
          ≤ (1 + P.eta) * (((region (fun b => (atoms b).halfspace) c
            ∩ fineLattice n (latticeScale ρ)).ncard : ℝ) / (latticeScale ρ) ^ n)) ∧
      (region (fun b => (atoms b).halfspace) c ∩ fineLattice n (latticeScale ρ)).Finite := by
  have hDNFpos : DNF.IsPositive ([c] : DNF A) := by
    intro c' hc'
    rwa [List.mem_singleton.1 hc']
  have hm : (Nat.card {c' : Cube A // c' ∈ ([c] : DNF A)} : ℝ) ≤ P.m := by
    rw [card_singleton_cubes]
    exact_mod_cast P.hm
  have h := lattice_of_dnf atoms (isDNFOf_singleton c a) hDNFpos P hn hm hr hAnz
    (fun _ => cen) hg
    (fun i => by rw [List.mem_singleton.1 i.2]; exact hball)
    (fun i => by rw [List.mem_singleton.1 i.2]; exact hfin) hρ
  rw [volSol, normalisedCount, latticeCount, sol_cubeForm] at h
  exact h

end Ttc
