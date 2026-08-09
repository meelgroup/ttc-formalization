/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Lattice.PerCube

/-!
# `lem:lattice` **per cube**, over plain data

`sections/analysis.tex:271` states `lem:lattice` for each polytope `P^i` of the
decomposition separately. `Ttc/Lattice/PerCube.lean` already proves it — but only
in the form `Ttc.TtcProb.lattice_cube_lo`/`lattice_cube_hi`, i.e. **over a
`Ttc.TtcProb` bundle**, reading the atoms, the parameter block, the centres and
the precision off the bundle's fields.

The regime analysis in `Ttc/Exec/` has no such bundle: it works with the raw
`atoms`, `D`, `P`, `cen`, `γ̂`, `ρ` that the executable statement quantifies over.
This file restates the per-cube lemma over exactly that plain data:

* `Ttc.lattice_cube_of_dnf` — the lower half,
  `(1 − η) · |P(c) ∩ 𝕃ⁿ| / 10^(ρn) ≤ Vol(P(c))`;
* `Ttc.finite_region_lattice_of_dnf` — the companion finiteness fact
  `(P(c) ∩ 𝕃ⁿ).Finite`, which comes out of the same application.

**What it is for.** `Ttc.rates` (`Ttc/Sampler/Rates.lean`) is built from
per-cube normalised lattice counts; the lower half above is the pointwise bound
that turns the `big` regime condition of `Ttc/Exec/Regime.lean` into a
*theorem* once a volume hypothesis on the input body is supplied. Without it,
`big` can only be assumed.

**Nothing new is assumed.** The proof is the plain-data transcription of
`Ttc.TtcProb.lattice_cube_two_sided`: instantiate the already-proved general
`Ttc.lattice_of_dnf` (`Ttc/Lattice/Assembled.lean`) at the **singleton DNF**
`[c]` with formula `Ttc.PosCube.cubeForm c`, then rewrite
`sol M (cubeForm c) = region M c` by `Ttc.PosCube.sol_cubeForm`. The two
counting side conditions are `Ttc.PosCube.card_cubes_singleton` (one cube, so
`1 ≤ m` suffices) and `Ttc.PosCube.card_facetIndex_singleton_le` (the singleton's
facets inject into the full DNF's).
-/

namespace Ttc

open MeasureTheory Set
open PosCube

variable {A : Type*} {n : ℕ}

/-! ## Transporting the side conditions to the singleton DNF

`Ttc.lattice_of_dnf` applied at `[c]` wants its hypotheses indexed by the
singleton's cubes and facets. Each of the three lemmas below is the restriction
of the corresponding hypothesis of the full DNF, using that the singleton's
unique cube is `c` and `c ∈ D`.
-/

/-- **The nonzero-normal hypothesis, restricted to a singleton DNF.** A facet of
`[c]` is a literal of `c`; since `c ∈ D`, that literal is a facet of `D`, so the
full DNF's hypothesis applies verbatim. -/
theorem normal_pos_singleton (atoms : A → LinAtom n) {D : DNF A}
    (hAnz : ∀ j : FacetIndex D, 0 < ∑ k, (atoms j.2.val.atom).coeff k ^ 2)
    {c : Cube A} (hc : c ∈ D) :
    ∀ j : FacetIndex ([c] : DNF A), 0 < ∑ k, (atoms j.2.val.atom).coeff k ^ 2 := by
  rintro ⟨⟨d, hd⟩, ⟨l, hl⟩⟩
  rw [List.mem_singleton] at hd
  subst hd
  exact hAnz ⟨⟨_, hc⟩, ⟨l, hl⟩⟩

/-- **The cube-count bound, at a singleton DNF, is just `1 ≤ m`.** By
`Ttc.PosCube.card_cubes_singleton` the singleton has exactly one cube. -/
theorem card_cubes_singleton_le {P : Params} (c : Cube A) (hm : (1 : ℝ) ≤ P.m) :
    (Nat.card {d : Cube A // d ∈ ([c] : DNF A)} : ℝ) ≤ P.m := by
  rw [card_cubes_singleton]
  exact_mod_cast hm

/-- **The facet-count bound, restricted to a singleton DNF**, via
`Ttc.PosCube.card_facetIndex_singleton_le`. -/
theorem card_facetIndex_singleton_le_param {P : Params} {D : DNF A} {c : Cube A} (hc : c ∈ D)
    (hr : (Nat.card (FacetIndex D) : ℝ) ≤ P.r) :
    (Nat.card (FacetIndex ([c] : DNF A)) : ℝ) ≤ P.r :=
  le_trans (by exact_mod_cast card_facetIndex_singleton_le hc) hr

/-! ## `lem:lattice`, per cube, over plain data -/

/-- **`lem:lattice` for a single polytope of a positive DNF, both halves, plus
finiteness** — the plain-data form of `Ttc.TtcProb.lattice_cube_two_sided`.

`Ttc.lattice_of_dnf` instantiated at the singleton DNF `[i.val]` and the formula
`Ttc.PosCube.cubeForm i.val`, with every side condition restricted to the one
cube. The two target theorems below are its two projections; landing the
application once avoids doing the plumbing twice. -/
theorem lattice_cube_two_sided_of_dnf (atoms : A → LinAtom n) {D : DNF A}
    (hpos : DNF.IsPositive D)
    (P : Params) (hn : P.n = n)
    (hm : (1 : ℝ) ≤ P.m)
    (hr : (Nat.card (FacetIndex D) : ℝ) ≤ P.r)
    (hAnz : ∀ j : FacetIndex D, 0 < ∑ k, (atoms j.2.val.atom).coeff k ^ 2)
    (cen : {c : Cube A // c ∈ D} → Space n) {gammaHat : ℝ} (hg : 0 < gammaHat)
    (hball : ∀ i, Metric.ball (cen i) gammaHat
      ⊆ region (fun a => (atoms a).halfspace) i.val)
    (hfin : ∀ i : {c : Cube A // c ∈ D},
      volume (region (fun a => (atoms a).halfspace) i.val) ≠ ⊤)
    {ρ : ℤ} (hρ : ρ = P.precision gammaHat)
    (i : {c : Cube A // c ∈ D}) :
    ((1 - P.eta) * (((region (fun a => (atoms a).halfspace) i.val
            ∩ fineLattice n (latticeScale ρ)).ncard : ℝ) / (latticeScale ρ) ^ n)
        ≤ (volume (region (fun a => (atoms a).halfspace) i.val)).toReal ∧
      (volume (region (fun a => (atoms a).halfspace) i.val)).toReal
        ≤ (1 + P.eta) * (((region (fun a => (atoms a).halfspace) i.val
            ∩ fineLattice n (latticeScale ρ)).ncard : ℝ) / (latticeScale ρ) ^ n)) ∧
      (region (fun a => (atoms a).halfspace) i.val
        ∩ fineLattice n (latticeScale ρ)).Finite := by
  have hcpos : Cube.IsPositive i.val := hpos i.val i.property
  have hm' : (Nat.card {d : Cube A // d ∈ ([i.val] : DNF A)} : ℝ) ≤ P.m :=
    card_cubes_singleton_le i.val hm
  have hr' : (Nat.card (FacetIndex ([i.val] : DNF A)) : ℝ) ≤ P.r :=
    card_facetIndex_singleton_le_param i.property hr
  have hAnz' := normal_pos_singleton atoms hAnz i.property
  have hball' : ∀ j : {d : Cube A // d ∈ ([i.val] : DNF A)},
      Metric.ball (cen i) gammaHat ⊆ region (fun a => (atoms a).halfspace) j.val := by
    intro j
    rw [List.mem_singleton.1 j.property]
    exact hball i
  have hfin' : ∀ j : {d : Cube A // d ∈ ([i.val] : DNF A)},
      volume (region (fun a => (atoms a).halfspace) j.val) ≠ ⊤ := by
    intro j
    rw [List.mem_singleton.1 j.property]
    exact hfin i
  have h := lattice_of_dnf atoms (singleton_isDNFOf hcpos) (singleton_isPositive hcpos)
    P hn hm' hr' hAnz' (fun _ => cen i) hg hball' hfin' hρ
  obtain ⟨⟨hlo, hhi⟩, hfinite⟩ := h
  rw [volSol, normalisedCount, latticeCount,
    sol_cubeForm (fun a => (atoms a).halfspace) hcpos] at hlo hhi
  rw [sol_cubeForm (fun a => (atoms a).halfspace) hcpos] at hfinite
  exact ⟨⟨hlo, hhi⟩, hfinite⟩

/-- **`lem:lattice` for a single polytope, lower half, over plain data.**

`(1 − η) · |P(cᵢ) ∩ 𝕃ⁿ| / 10^(ρn) ≤ Vol(P(cᵢ))` for each cube `cᵢ` of a positive
DNF, under the paper's hypotheses: `1 ≤ m`, the facet family is bounded by `r`,
every facet has a nonzero normal, every polytope contains an `ℓ₂`-ball of radius
`γ̂ > 0` about its own centre and has finite volume, and `ρ = ⌈log₁₀(γ/γ̂)⌉`.

The bundle version is `Ttc.TtcProb.lattice_cube_lo`. -/
theorem lattice_cube_of_dnf (atoms : A → LinAtom n) {D : DNF A} (hpos : DNF.IsPositive D)
    (P : Params) (hn : P.n = n)
    (hm : (1 : ℝ) ≤ P.m)
    (hr : (Nat.card (FacetIndex D) : ℝ) ≤ P.r)
    (hAnz : ∀ j : FacetIndex D, 0 < ∑ k, (atoms j.2.val.atom).coeff k ^ 2)
    (cen : {c : Cube A // c ∈ D} → Space n) {gammaHat : ℝ} (hg : 0 < gammaHat)
    (hball : ∀ i, Metric.ball (cen i) gammaHat
      ⊆ region (fun a => (atoms a).halfspace) i.val)
    (hfin : ∀ i : {c : Cube A // c ∈ D},
      volume (region (fun a => (atoms a).halfspace) i.val) ≠ ⊤)
    {ρ : ℤ} (hρ : ρ = P.precision gammaHat)
    (i : {c : Cube A // c ∈ D}) :
    (1 - P.eta) * (((region (fun a => (atoms a).halfspace) i.val
          ∩ fineLattice n (latticeScale ρ)).ncard : ℝ) / (latticeScale ρ) ^ n)
      ≤ (volume (region (fun a => (atoms a).halfspace) i.val)).toReal :=
  (lattice_cube_two_sided_of_dnf atoms hpos P hn hm hr hAnz cen hg hball hfin hρ i).1.1

/-- **`lem:lattice` for a single polytope, upper half, over plain data** — the
companion of `Ttc.lattice_cube_of_dnf`, from the same application.

The bundle version is `Ttc.TtcProb.lattice_cube_hi`. -/
theorem lattice_cube_hi_of_dnf (atoms : A → LinAtom n) {D : DNF A} (hpos : DNF.IsPositive D)
    (P : Params) (hn : P.n = n)
    (hm : (1 : ℝ) ≤ P.m)
    (hr : (Nat.card (FacetIndex D) : ℝ) ≤ P.r)
    (hAnz : ∀ j : FacetIndex D, 0 < ∑ k, (atoms j.2.val.atom).coeff k ^ 2)
    (cen : {c : Cube A // c ∈ D} → Space n) {gammaHat : ℝ} (hg : 0 < gammaHat)
    (hball : ∀ i, Metric.ball (cen i) gammaHat
      ⊆ region (fun a => (atoms a).halfspace) i.val)
    (hfin : ∀ i : {c : Cube A // c ∈ D},
      volume (region (fun a => (atoms a).halfspace) i.val) ≠ ⊤)
    {ρ : ℤ} (hρ : ρ = P.precision gammaHat)
    (i : {c : Cube A // c ∈ D}) :
    (volume (region (fun a => (atoms a).halfspace) i.val)).toReal
      ≤ (1 + P.eta) * (((region (fun a => (atoms a).halfspace) i.val
          ∩ fineLattice n (latticeScale ρ)).ncard : ℝ) / (latticeScale ρ) ^ n) :=
  (lattice_cube_two_sided_of_dnf atoms hpos P hn hm hr hAnz cen hg hball hfin hρ i).1.2

/-- **A single polytope meets the fine lattice in a finite set.**

Not an assumption but a consequence of the same shell bound that proves
`Ttc.lattice_cube_of_dnf` (`Ttc.FacetSystem.finite_lattice_points`, via
`Ttc.lattice_of_dnf`). This is what makes the per-cube normalised count
`|P(cᵢ) ∩ 𝕃ⁿ| / 10^(ρn)` a count over a *finite* set, as `Ttc.rates` needs. -/
theorem finite_region_lattice_of_dnf (atoms : A → LinAtom n) {D : DNF A}
    (hpos : DNF.IsPositive D)
    (P : Params) (hn : P.n = n)
    (hm : (1 : ℝ) ≤ P.m)
    (hr : (Nat.card (FacetIndex D) : ℝ) ≤ P.r)
    (hAnz : ∀ j : FacetIndex D, 0 < ∑ k, (atoms j.2.val.atom).coeff k ^ 2)
    (cen : {c : Cube A // c ∈ D} → Space n) {gammaHat : ℝ} (hg : 0 < gammaHat)
    (hball : ∀ i, Metric.ball (cen i) gammaHat
      ⊆ region (fun a => (atoms a).halfspace) i.val)
    (hfin : ∀ i : {c : Cube A // c ∈ D},
      volume (region (fun a => (atoms a).halfspace) i.val) ≠ ⊤)
    {ρ : ℤ} (hρ : ρ = P.precision gammaHat)
    (i : {c : Cube A // c ∈ D}) :
    (region (fun a => (atoms a).halfspace) i.val
      ∩ fineLattice n (latticeScale ρ)).Finite :=
  (lattice_cube_two_sided_of_dnf atoms hpos P hn hm hr hAnz cen hg hball hfin hρ i).2

/-! ## Axiom profile (`CLAUDE.md` §4) -/

#print axioms normal_pos_singleton
#print axioms card_cubes_singleton_le
#print axioms card_facetIndex_singleton_le_param
#print axioms lattice_cube_two_sided_of_dnf
#print axioms lattice_cube_of_dnf
#print axioms lattice_cube_hi_of_dnf
#print axioms finite_region_lattice_of_dnf

end Ttc
