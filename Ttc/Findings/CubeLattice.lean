/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Lattice.PerCube

/-!
# `lem:lattice` for a single polytope

The paper applies `lem:lattice` (`sections/analysis.tex:269`) to **one** polytope
`P^i` at a time, whereas `Ttc.lattice_of_dnf` (`Lattice/Assembled`) is stated
globally, over `Sol(F)` for a whole DNF. This file is the `Findings/`
presentation of the per-polytope form: `Ttc.lattice_of_cube` states the paper's
inequality directly about a cube's region `P(c)` and its lattice-point count,
with no `Ttc.sol`/`Ttc.volSol` wrapper left in sight.

**The machinery lives in `Ttc/Lattice/PerCube.lean`**, namespace `Ttc.PosCube`:
`PosCube.cubeForm` is the formula a cube denotes, `PosCube.singleton_isDNFOf` and
`PosCube.singleton_isPositive` supply `Ttc.lattice_of_dnf`'s two hypotheses at the
singleton DNF `[c]`, `PosCube.sol_cubeForm` identifies its solution set with
`Ttc.region M c`, and `PosCube.card_cubes_singleton` gives the cube count. All
this file adds is the assembly, and a statement phrased the way the paper phrases
it. `Ttc.TtcProb.lattice_cube_lo`/`lattice_cube_hi` (also in `PerCube`) are the
same result specialised to a `Ttc.TtcProb`; those are the ones on the headline's
dependency path, and this file is not.

## The seed atom is gone

Earlier versions of this file carried their own `cubeForm`, seeded with the
tautology `a ∨ ¬a` at a caller-supplied atom `a : A`, on the stated grounds that
"`Ttc.BForm` has no `true` constructor". That was false: `Ttc.BForm.tt` exists
(`Model/Prelude.lean`) and is exactly the empty conjunction, which is what
`Ttc.conj` — and hence `PosCube.cubeForm` — folds onto. The seed was therefore
spurious, and not merely cosmetic: it made every lemma here inapplicable when the
atom type `A` is empty, and forced callers to invent an atom they may not have.
Dropping it strictly strengthens `Ttc.lattice_of_cube`.

## Positivity costs nothing here

`PosCube.cubeForm` is `Ttc.conj` of the cube's *atoms*, so it is faithful only on
a positive cube; the deleted local version used a polarity-aware `litForm` and so
was faithful on any cube. That extra generality was unusable at this level:
`Ttc.lattice_of_dnf` demands `Ttc.DNF.IsPositive` of its DNF regardless, which at
the singleton `[c]` is exactly `Ttc.Cube.IsPositive c`. `Ttc.lattice_of_cube`
always had to assume it, so re-basing onto `PosCube` loses nothing.
-/

namespace Ttc

open MeasureTheory Set PosCube

variable {A : Type*} {n : ℕ}

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

This is `Ttc.lattice_of_dnf` instantiated at the singleton DNF `[c]` and the
formula `Ttc.PosCube.cubeForm c`; the bound `Nat.card {c' // c' ∈ [c]} ≤ m` it
needs is `Ttc.PosCube.card_cubes_singleton` together with `Ttc.Params.hm`, so no
extra hypothesis on `m` is required. -/
theorem lattice_of_cube (atoms : A → LinAtom n) (c : Cube A)
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
  have hm : (Nat.card {c' : Cube A // c' ∈ ([c] : DNF A)} : ℝ) ≤ P.m := by
    rw [card_cubes_singleton]
    exact_mod_cast P.hm
  have h := lattice_of_dnf atoms (singleton_isDNFOf hpos) (singleton_isPositive hpos)
    P hn hm hr hAnz (fun _ => cen) hg
    (fun i => by rw [List.mem_singleton.1 i.2]; exact hball)
    (fun i => by rw [List.mem_singleton.1 i.2]; exact hfin) hρ
  rw [volSol, normalisedCount, latticeCount,
    sol_cubeForm (fun b => (atoms b).halfspace) hpos] at h
  exact h

/-! ## Axiom profile (`CLAUDE.md` §4) -/

#print axioms lattice_of_cube

end Ttc
