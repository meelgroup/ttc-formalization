/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.Endgoal
import Ttc.Findings.CubeLattice
import Ttc.Witness.BoxSharp

/-!
# `Sampler/Rates`: the level-`0` rates `θ`, constructed

`Ttc.ttc_volume` (`Model/Endgoal`) carries four binders for the sampling oracle,

```lean
(θ : Fin (latticeCount M φ ρ) → ℝ) (sampD : Cube A → Space n → ℝ)
(sampler : KV97Sampler A n M (toDNF φ) ρ P.epsPrime sampD)
(theta_eq : ∀ s, ∃ i, i ∈ toDNF φ ∧ latticeEnum M φ ρ s ∈ region M i ∧
                 θ s = sampD i (latticeEnum M φ ρ s) * vol i)
```

plus `gen_mem`.  This file removes **three** of them — `θ`, `theta_eq` and
`gen_mem` — leaving `sampD` and `sampler` (the sampler's own construction,
`Ttc/Sampler/Construct.lean`) as the only sampling-oracle inputs.
`Ttc.ttc_volume_rates` is the packaged statement: `Ttc.ttc_volume` applied
verbatim, with those three binders discharged and `big` now a condition on the
*constructed* `θ`.

## `θ`, from `sampD` and `vol`

`theta_eq` is not a constraint that has to be *assumed*: it is the *definition* of
the rates, read backwards.  Every enumerated point lies in `Sol(F)`
(`Ttc.latticeEnum_mem`), and `thm:decomposition` covers `Sol(F)` by the regions of
the DNF's cubes (`Ttc.sol_subset_iUnion_region`), so **some** cube of the
decomposition contains it.  `Ttc.cubeOf` picks one — classically, which is fine,
since `θ` is data and only its existence is asserted — and

```lean
Ttc.rates M φ D ρ sampD vol s = sampD (cubeAt … s) (latticeEnum M φ ρ s) * vol (cubeAt … s)
```

satisfies `theta_eq` with `i := cubeAt … s`, the last conjunct by `rfl`
(`Ttc.theta_eq_rates`).

`Ttc.Box.thC`/`Ttc.Box.thOf` — the box witnesses' hand-written rates — are the
special case where the DNF has one cube; `Ttc.Box.rates_eq_thOf` below proves the
general construction reproduces `Ttc.Box.thOf` on the box, so the sharp witness of
`Ttc/Witness/BoxSharp.lean` runs unchanged at the constructed `θ`
(`Ttc.Box.ttc_volume_box_rates`).

## Non-vacuity: `θ` is not the zero function

A `θ` that is identically `0` satisfies `theta_eq` vacuously and then *fails* the
capstone's `big`, `(1 − ε')·Thresh/8 ≤ ∑ s θ s`; a "construction" that collapsed
the rates would silently make every instance unusable.  So the construction is
accompanied by

* `Ttc.rates_pos` — `0 < θ s` at every index, from `vol_pos` and positivity of the
  sampler's mass at the enumerated points; `Ttc.rates_pos_of_almostUniform` gets
  that positivity out of `eq:almostuniform` itself (`Ttc.AlmostUniform`, the shape
  `Ttc.TtcProb.samp_unif` delivers), so it is not a new demand on the sampler;
* `Ttc.sum_rates_pos` — `0 < ∑ s θ s` whenever the lattice is nonempty; and
* `Ttc.Box.ttc_volume_box_rates` — the capstone itself, at the constructed `θ`, at
  **every** `(ε, δ) ∈ (0,1]²`, in particular strictly inside the square where the
  accuracy conclusion `1 − δ ≤ …` is a genuine bound on a probability.

## `gen_mem`, discharged from the geometry

`Ttc.gen_mem_trajOracles` (`Coupling/Run`) reduces `gen_mem` to *"cube `i` is met
by some enumerated lattice point"* — the guard that makes `Ttc.trajOracles`' filler
branch (`Ttc.padPoint`, which is `0` at a cube no enumerated point meets) safe.
That guard is **not** an extra assumption: `Ttc.lattice_of_cube`
(`Findings/CubeLattice`) bounds `Vol(P(cᵢ))` above by `(1+η)·|P(cᵢ) ∩ 𝕃ⁿ|/10^(ρn)`,
and `P(cᵢ)` contains a ball of radius `γ̂ > 0` — so the count cannot be `0`.
`Ttc.exists_lattice_point_region` is that argument, and
`Ttc.gen_mem_of_geometry` is `gen_mem` with only hypotheses `Ttc.ttc_volume`
already has (`isDNF`, `isPositive`, `hcoeff`, `ball_subset`, `hbdd`, `hr`, and
`ρ = P.precision γ̂`).
-/

namespace Ttc

open MeasureTheory Set

variable {A : Type*} {n : ℕ}

/-! ## Part 1.  A cube of the decomposition containing a given point -/

/-- Every point of `Sol(F)` is covered by a cube of any DNF abstraction — the
existence hypothesis of `Ttc.cubeOf_spec`, from `thm:decomposition`. -/
theorem exists_cube_mem_of_mem_sol {M : A → Set (Space n)} {D : DNF A} {φ : BForm A}
    (hDNF : IsDNFOf D φ) {x : Space n} (hx : x ∈ sol M φ) :
    ∃ c : Cube A, c ∈ D ∧ x ∈ region M c := by
  obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 (sol_subset_iUnion_region hDNF hx)
  exact ⟨c, hc, hxc⟩

/-- `Ttc.cubeAt` is a cube of the decomposition, and it contains the enumerated
point. -/
theorem cubeAt_spec {M : A → Set (Space n)} {φ : BForm A} {D : DNF A} {ρ : ℤ}
    (hDNF : IsDNFOf D φ) (hle : HasLatticeEnum M φ ρ) (s : Fin (latticeCount M φ ρ)) :
    cubeAt M φ D ρ s ∈ D ∧ latticeEnum M φ ρ s ∈ region M (cubeAt M φ D ρ s) :=
  cubeOf_spec (exists_cube_mem_of_mem_sol hDNF (latticeEnum_mem hle s).1)

/-! ## Part 2.  The rates `θ`, and `theta_eq` -/

/-- **`Ttc.ttc_volume`'s `theta_eq`, for the constructed rates.**  The witness is
`Ttc.cubeAt`, and the equation is `rfl`. -/
theorem theta_eq_rates {M : A → Set (Space n)} {φ : BForm A} {D : DNF A} {ρ : ℤ}
    (hDNF : IsDNFOf D φ) (hle : HasLatticeEnum M φ ρ)
    (sampD : Cube A → Space n → ℝ) (vol : Cube A → ℝ) (s : Fin (latticeCount M φ ρ)) :
    ∃ i, i ∈ D ∧ latticeEnum M φ ρ s ∈ region M i ∧
      rates M φ D ρ sampD vol s = sampD i (latticeEnum M φ ρ s) * vol i :=
  ⟨cubeAt M φ D ρ s, (cubeAt_spec hDNF hle s).1, (cubeAt_spec hDNF hle s).2, rfl⟩

/-! ### The rates are not degenerate -/

/-- **`0 < θ s`.**  Under `vol_pos` and positivity of the sampler's mass at the
enumerated lattice points, every rate is strictly positive — so the construction
cannot satisfy `theta_eq` by collapsing `θ` to `0`. -/
theorem rates_pos {M : A → Set (Space n)} {φ : BForm A} {D : DNF A} {ρ : ℤ}
    (hDNF : IsDNFOf D φ) (hle : HasLatticeEnum M φ ρ)
    {sampD : Cube A → Space n → ℝ} {vol : Cube A → ℝ}
    (hvol : ∀ i ∈ D, 0 < vol i)
    (hsamp : ∀ i ∈ D, ∀ x ∈ region M i ∩ fineLattice n (latticeScale ρ), 0 < sampD i x)
    (s : Fin (latticeCount M φ ρ)) : 0 < rates M φ D ρ sampD vol s := by
  obtain ⟨hmem, hreg⟩ := cubeAt_spec hDNF hle s
  exact mul_pos
    (hsamp _ hmem _ ⟨hreg, (latticeEnum_mem hle s).2⟩)
    (hvol _ hmem)

/-- **`0 < ∑ s θ s`.**  With the lattice nonempty — `Ttc.ttc_volume`'s `hm`/`hr`
guard it, and `Ttc.exists_lattice_point_region` below shows it is nonempty as soon
as one cube of the decomposition has an inscribed ball — the total rate is
positive, which is what `big` needs. -/
theorem sum_rates_pos {M : A → Set (Space n)} {φ : BForm A} {D : DNF A} {ρ : ℤ}
    (hDNF : IsDNFOf D φ) (hle : HasLatticeEnum M φ ρ)
    {sampD : Cube A → Space n → ℝ} {vol : Cube A → ℝ}
    (hvol : ∀ i ∈ D, 0 < vol i)
    (hsamp : ∀ i ∈ D, ∀ x ∈ region M i ∩ fineLattice n (latticeScale ρ), 0 < sampD i x)
    (hpos : 0 < latticeCount M φ ρ) : 0 < ∑ s, rates M φ D ρ sampD vol s := by
  haveI : Nonempty (Fin (latticeCount M φ ρ)) := Fin.pos_iff_nonempty.1 hpos
  exact Finset.sum_pos (fun s _ => rates_pos hDNF hle hvol hsamp s) Finset.univ_nonempty

/-! ### `hsamp` from `eq:almostuniform`

The positivity of the sampler's mass that `Ttc.rates_pos` asks for is not an extra
demand on the sampler: `Ttc.AlmostUniform` — what `Ttc.TtcProb.samp_unif` delivers
— gives it, since `(1 − ε')/N > 0` for `ε' < 1` and a nonempty finite `N`. -/

/-- An almost-uniform mass is positive on a finite set. -/
theorem pos_of_almostUniform {α : Type*} {D : α → ℝ} {S : Set α} {eps : ℝ}
    (h : AlmostUniform D S eps) (heps : eps < 1) (hfin : S.Finite) {x : α} (hx : x ∈ S) :
    0 < D x := by
  have hcard : 0 < S.ncard := (Set.ncard_pos hfin).2 ⟨x, hx⟩
  have hpos : 0 < (1 - eps) / (S.ncard : ℝ) := by
    have : (0 : ℝ) < (S.ncard : ℝ) := by exact_mod_cast hcard
    exact div_pos (by linarith) this
  exact lt_of_lt_of_le hpos (h.lower hx)

/-- `Sol(F) ∩ 𝕃ⁿ` is finite once it is enumerated — it is contained in the range of
the enumeration, whose domain is a `Fin`. -/
theorem finite_sol_lattice_of_hasLatticeEnum {M : A → Set (Space n)} {φ : BForm A} {ρ : ℤ}
    (hle : HasLatticeEnum M φ ρ) : (sol M φ ∩ fineLattice n (latticeScale ρ)).Finite := by
  refine (Set.finite_range (latticeEnum M φ ρ)).subset ?_
  intro x hx
  obtain ⟨s, hs⟩ := latticeEnum_onto hle x hx
  exact ⟨s, hs⟩

/-- Each cube's lattice points are finite, by `thm:decomposition` soundness. -/
theorem finite_region_lattice {M : A → Set (Space n)} {φ : BForm A} {D : DNF A} {ρ : ℤ}
    (hDNF : IsDNFOf D φ) (hle : HasLatticeEnum M φ ρ) {i : Cube A} (hi : i ∈ D) :
    (region M i ∩ fineLattice n (latticeScale ρ)).Finite :=
  (finite_sol_lattice_of_hasLatticeEnum hle).subset
    (Set.inter_subset_inter_left _ (region_subset_sol hDNF hi))

/-- **`0 < θ s`, from `eq:almostuniform`.**  `Ttc.rates_pos` with its positivity
hypothesis discharged from the sampler's own guarantee — the shape
`Ttc.TtcProb.samp_unif` has. -/
theorem rates_pos_of_almostUniform {M : A → Set (Space n)} {φ : BForm A} {D : DNF A} {ρ : ℤ}
    (hDNF : IsDNFOf D φ) (hle : HasLatticeEnum M φ ρ)
    {sampD : Cube A → Space n → ℝ} {vol : Cube A → ℝ} {eps : ℝ}
    (hvol : ∀ i ∈ D, 0 < vol i) (heps : eps < 1)
    (hunif : ∀ i ∈ D, AlmostUniform (sampD i)
      (region M i ∩ fineLattice n (latticeScale ρ)) eps)
    (s : Fin (latticeCount M φ ρ)) : 0 < rates M φ D ρ sampD vol s :=
  rates_pos hDNF hle hvol
    (fun i hi _ hx => pos_of_almostUniform (hunif i hi) heps
      (finite_region_lattice hDNF hle hi) hx) s

/-! ## Part 3.  `gen_mem`, discharged from the geometry

`Ttc.gen_mem_trajOracles` needs, for the cube it is asked about, *one* enumerated
lattice point in that cube — the guard on `Ttc.padPoint`.  `Ttc.lattice_of_cube`
supplies it: a cube's region has an inscribed ball, hence positive volume, hence a
nonzero lattice count.
-/

/-- **A cube's region contains a lattice point.**  From `lem:lattice` per polytope
(`Ttc.lattice_of_cube`): `Vol(P(c)) ≤ (1+η)·|P(c) ∩ 𝕃ⁿ|/10^(ρn)`, and the left side
is positive because `P(c)` contains a ball of radius `γ̂ > 0`.  So the count is not
`0`. -/
theorem exists_lattice_point_region (atoms : A → LinAtom n) {c : Cube A}
    (hpos : Cube.IsPositive c) (P : Params) (hn : P.n = n)
    (hr : (Nat.card (FacetIndex ([c] : DNF A)) : ℝ) ≤ P.r)
    (hAnz : ∀ j : FacetIndex ([c] : DNF A), 0 < ∑ k, (atoms j.2.val.atom).coeff k ^ 2)
    (cen : Space n) {gammaHat : ℝ} (hg : 0 < gammaHat)
    (hball : Metric.ball cen gammaHat ⊆ region (fun b => (atoms b).halfspace) c)
    (hfin : volume (region (fun b => (atoms b).halfspace) c) ≠ ⊤)
    {ρ : ℤ} (hρ : ρ = P.precision gammaHat) :
    (region (fun b => (atoms b).halfspace) c ∩ fineLattice n (latticeScale ρ)).Nonempty := by
  have hhi := (lattice_of_cube atoms c hpos P hn hr hAnz cen hg hball hfin hρ).1.2
  have hvolpos : 0 < (volume (region (fun b => (atoms b).halfspace) c)).toReal := by
    have hbpos : 0 < volume (Metric.ball cen gammaHat) := Metric.measure_ball_pos _ _ hg
    exact ENNReal.toReal_pos (lt_of_lt_of_le hbpos (measure_mono hball)).ne' hfin
  rcases Set.eq_empty_or_nonempty
    (region (fun b => (atoms b).halfspace) c ∩ fineLattice n (latticeScale ρ)) with h | h
  · rw [h] at hhi
    simp only [Set.ncard_empty, Nat.cast_zero, zero_div, mul_zero] at hhi
    linarith
  · exact h

/-- **The enumeration meets every cube of the decomposition that has a lattice
point.**  `Ttc.latticeEnum_onto` transports a lattice point of `P(cᵢ) ⊆ Sol(F)` to
an index. -/
theorem exists_enum_mem_region {M : A → Set (Space n)} {φ : BForm A} {D : DNF A} {ρ : ℤ}
    (hDNF : IsDNFOf D φ) (hle : HasLatticeEnum M φ ρ) {i : Cube A} (hi : i ∈ D)
    (hx : (region M i ∩ fineLattice n (latticeScale ρ)).Nonempty) :
    ∃ s, latticeEnum M φ ρ s ∈ region M i := by
  obtain ⟨x, hxr, hxl⟩ := hx
  obtain ⟨s, hs⟩ := latticeEnum_onto hle x ⟨region_subset_sol hDNF hi hxr, hxl⟩
  exact ⟨s, hs ▸ hxr⟩

/-- **`Ttc.ttc_volume`'s `gen_mem`, given the non-emptiness guard.**
`Ttc.gen_mem_trajOracles` at the constructed oracle bundle, with the sets
`T i := P(cᵢ) ∩ 𝕃ⁿ`. -/
theorem gen_mem_of_enum {M : A → Set (Space n)} {φ : BForm A} {ρ : ℤ}
    (hle : HasLatticeEnum M φ ρ) (vol : Cube A → ℝ)
    (t : ℕ → Fin (latticeCount M φ ρ) → ℕ) {i : Cube A}
    (hne : ∃ s, latticeEnum M φ ρ s ∈ region M i) (j N : ℕ) :
    ∀ s ∈ (coveredOracles M φ ρ vol t).gen i j N ρ,
      s ∈ region M i ∩ fineLattice n (latticeScale ρ) := by
  have hmem : ∀ (c : Cube A) (s : Fin (latticeCount M φ ρ)),
      memPtOfRegion M (latticeEnum M φ ρ) c s = true →
      latticeEnum M φ ρ s ∈ region M c ∩ fineLattice n (latticeScale ρ) :=
    fun c s h => ⟨(memPtOfRegion_eq_true _ _ _ _).1 h, (latticeEnum_mem hle s).2⟩
  have hne' : ∃ s, memPtOfRegion M (latticeEnum M φ ρ) i s = true := by
    obtain ⟨s, hs⟩ := hne
    exact ⟨s, (memPtOfRegion_eq_true _ _ _ _).2 hs⟩
  exact gen_mem_trajOracles (T := fun c => region M c ∩ fineLattice n (latticeScale ρ))
    (latticeEnum_injective M φ ρ) t hmem hne' j N ρ

/-- **`Ttc.ttc_volume`'s `gen_mem`, with no new hypothesis.**

Every hypothesis below is one `Ttc.ttc_volume` already carries — `isDNF`,
`isPositive`, `hbdd`, `hcoeff`, the facet bound (`Ttc.ttcParams_facets_le`), the
inscribed ball, and `ρ = P.precision γ̂` — so this discharges the binder outright
rather than trading it for another. -/
theorem gen_mem_of_geometry (atoms : A → LinAtom n) {D : DNF A} {φ : BForm A}
    (hDNF : IsDNFOf D φ) (hpos : DNF.IsPositive D)
    (hbdd : Bornology.IsBounded (sol (fun a => (atoms a).halfspace) φ))
    (hcoeff : ∀ j : FacetIndex D, (atoms j.2.val.atom).coeff ≠ 0)
    (P : Params) (hn : P.n = n) (hrD : (Nat.card (FacetIndex D) : ℝ) ≤ P.r)
    (cen : {c : Cube A // c ∈ D} → Space n) {gammaHat : ℝ} (hg : 0 < gammaHat)
    (hball : ∀ i, Metric.ball (cen i) gammaHat
      ⊆ region (fun a => (atoms a).halfspace) i.val)
    {ρ : ℤ} (hρ : ρ = P.precision gammaHat) (vol : Cube A → ℝ)
    (t : ℕ → Fin (latticeCount (fun a => (atoms a).halfspace) φ ρ) → ℕ)
    (i : Cube A) (j N : ℕ) (hi : i ∈ D) :
    ∀ s ∈ (coveredOracles (fun a => (atoms a).halfspace) φ ρ vol t).gen i j N ρ,
      s ∈ region (fun a => (atoms a).halfspace) i ∩ fineLattice n (latticeScale ρ) := by
  have hAnzD := normal_ne_zero_of_coeff_ne_zero hcoeff
  have hAnz : ∀ j : FacetIndex ([i] : DNF A), 0 < ∑ k, (atoms j.2.val.atom).coeff k ^ 2 := by
    rintro ⟨⟨d, hd⟩, ⟨l, hl⟩⟩
    rw [List.mem_singleton] at hd
    subst hd
    exact hAnzD ⟨⟨_, hi⟩, ⟨l, hl⟩⟩
  have hr : (Nat.card (FacetIndex ([i] : DNF A)) : ℝ) ≤ P.r :=
    le_trans (by exact_mod_cast PosCube.card_facetIndex_singleton_le hi) hrD
  have hfin := volume_region_ne_top_of_isBounded hDNF hbdd ⟨i, hi⟩
  have hlat := exists_lattice_point_region atoms (hpos i hi) P hn hr hAnz (cen ⟨i, hi⟩) hg
    (hball ⟨i, hi⟩) hfin hρ
  exact gen_mem_of_enum (hasLatticeEnum_of_isBounded _ _ _ hbdd) vol t
    (exists_enum_mem_region hDNF (hasLatticeEnum_of_isBounded _ _ _ hbdd) hi hlat) j N

/-! ## Part 4.  `Ttc.ttc_volume` with `θ`, `theta_eq` and `gen_mem` removed -/

/-- **The capstone, at the constructed rates and with `gen_mem` discharged.**

`Ttc.ttc_volume` applied verbatim — it is neither restated nor weakened — with

* `θ` **constructed**: `Ttc.rates M φ (toDNF φ) ρ sampD vol`, so the binder is gone;
* `theta_eq` **proved**: `Ttc.theta_eq_rates`, so that binder is gone;
* `gen_mem` **proved**: `Ttc.gen_mem_of_geometry`, from `isDNF`, `isPositive`,
  `hbdd`, `hcoeff`, `ball_subset` and the computed `P` — all of which the statement
  already carries — so that binder is gone too.

Three of `Ttc.ttc_volume`'s 28 residual binders, removed at no cost: the remaining
sampling-oracle inputs are `sampD` and `sampler`, i.e. the sampler itself.  `big`
is now a statement about the *constructed* `θ`, which is the honest form: it can no
longer be satisfied by collapsing the rates (`Ttc.rates_pos`). -/
theorem ttc_volume_rates
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (M : A → Set (Space n)) (M_eq : M = fun a => (atoms a).halfspace)
    (toDNF : BForm A → DNF A)
    (isDNF : IsDNFOf (toDNF φ) φ) (isPositive : DNF.IsPositive (toDNF φ))
    (hm : 1 ≤ Nat.card {c : Cube A // c ∈ toDNF φ})
    (hr : 1 ≤ Nat.card (FacetIndex (toDNF φ)))
    (P : Params) (hP : P = ttcParams (toDNF φ) n ε δ hε0 hε1 hn hm hr)
    (hbdd : Bornology.IsBounded (sol M φ))
    (hcoeff : ∀ j : FacetIndex (toDNF φ), (atoms j.2.val.atom).coeff ≠ 0)
    (cen : {c : Cube A // c ∈ toDNF φ} → Space n) (gammaHat : ℝ) (hgammaHat : 0 < gammaHat)
    (ball_subset : ∀ i, Metric.ball (cen i) gammaHat ⊆ region M i.val)
    (vol : Cube A → ℝ) (volAlg : VolumeAlgorithm n) (volCoins : volAlg.Ω)
    (volED_eq : ∀ (i : Cube A) (hi : i ∈ toDNF φ), vol i =
      gammaHat ^ n * volAlg.est (roundBody (cen ⟨i, hi⟩) gammaHat (region M i))
        P.epsPrime P.deltaPrime volCoins)
    (volCoins_good : ∀ i ∈ toDNF φ, vol i ∈ relErr P.epsPrime (volume (region M i)).toReal)
    (vol_pos : ∀ i ∈ toDNF φ, 0 < vol i)
    (sampD : Cube A → Space n → ℝ)
    (sampler : KV97Sampler A n M (toDNF φ) (P.precision gammaHat) P.epsPrime sampD)
    (big : (1 - P.epsPrime) * P.thresh / 8
      ≤ ∑ s, rates M φ (toDNF φ) (P.precision gammaHat) sampD vol s) :
    (1 - δ ≤ (trajLaw (rates M φ (toDNF φ) (P.precision gammaHat) sampD vol)
        {t : ℕ → Fin (latticeCount M φ (P.precision gammaHat)) → ℕ |
          ttcOutput P (coveredOracles M φ (P.precision gammaHat) vol) toDNF
              (P.precision gammaHat) φ t
            ∈ relErr ε (volSol M φ)}).toReal)
    ∧
    (∀ (t : ℕ → Fin (latticeCount M φ (P.precision gammaHat)) → ℕ) (cVol cSample thr : ℕ),
      (thr : ℝ) = P.thresh →
      Terminates P (coveredOracles M φ (P.precision gammaHat) vol t) (toDNF φ) →
      runCost P (coveredOracles M φ (P.precision gammaHat) vol t) cVol cSample
          (P.precision gammaHat) (toDNF φ)
        ≤ (toDNF φ).length * (cVol + cSample * thr)) := by
  subst M_eq
  subst hP
  have hle := hasLatticeEnum_of_isBounded (fun a => (atoms a).halfspace) φ
    ((ttcParams (toDNF φ) n ε δ hε0 hε1 hn hm hr).precision gammaHat) hbdd
  exact ttc_volume_explicit atoms φ ε δ hε0 hε1 hδ0 hδ1 hn _ rfl toDNF isDNF isPositive hm hr _ rfl
    hbdd hcoeff cen gammaHat hgammaHat ball_subset vol volAlg volCoins volED_eq
    volCoins_good vol_pos _ sampD sampler
    (fun s => theta_eq_rates isDNF hle sampD vol s)
    (fun t i j N hi => gen_mem_of_geometry atoms isDNF isPositive hbdd hcoeff
      (ttcParams (toDNF φ) n ε δ hε0 hε1 hn hm hr) rfl
      (ttcParams_facets_le (D := toDNF φ) (n := n) (ε := ε) (δ := δ)
        (hε0 := hε0) (hε1 := hε1) (hn := hn) (hm := hm) (hr := hr))
      cen hgammaHat ball_subset rfl vol t i j N hi)
    big

/-! ## Part 5.  Non-vacuity: the capstone at the constructed rates

`Ttc/Witness/BoxSharp.lean` instantiates `Ttc.ttc_volume` at every
`(ε, δ) ∈ (0,1]²` with the hand-written rates `Ttc.Box.thOf`.  Those rates are the
one-cube case of `Ttc.rates`, so the same witness runs at the *constructed* `θ` —
and in particular meets `big`, the hypothesis a collapsed `θ` would fail.
-/

namespace Box

open MeasureTheory Set

variable {n : ℕ} {ε δ : ℝ}

/-- **The general construction reproduces the box's rates.**  The box's DNF has one
cube, so `Ttc.cubeAt` can only pick it; both `Ttc.Box.smpOf` and `Ttc.Box.vlOf` then
read the box. -/
theorem rates_eq_thOf (n : ℕ) (c : ℝ) (hn : 1 ≤ n) (ρ : ℤ) :
    rates (fun a => (boxAtoms n c a).halfspace) (boxForm n hn)
        (Ttc.toDNF (boxForm n hn)) ρ (smpOf n c ρ) (vlOf n c)
      = thOf n c hn ρ := by
  funext s
  have hspec := cubeAt_spec (toDNF_isDNFOf (boxForm n hn)) (hasLatticeEnum_bxOf n c hn ρ) s
  simp only [rates, thOf, smpOf, vlOf, region_eq_bxOf n c hn hspec.1]

/-- **The box's sampler mass is positive** at every point — it is `1/N` for the
box's lattice-point count `N > 0`. -/
theorem smpOf_pos (n : ℕ) {c : ℝ} (hc : 0 < c) (hn : 1 ≤ n) (ρ : ℤ)
    {i : Cube (Fin n ⊕ Fin n)} (hi : i ∈ Ttc.toDNF (boxForm n hn)) (x : Space n) :
    0 < smpOf n c ρ i x := by
  have h : (0 : ℝ) < ((bxOf n c ∩ fineLattice n (latticeScale ρ)).ncard : ℝ) := by
    exact_mod_cast ncard_lat_pos n hc.le ρ
  simpa only [smpOf, region_eq_bxOf n c hn hi] using one_div_pos.2 h

/-- **The constructed rates are strictly positive on the box** — `Ttc.rates_pos` at
the box's data, so the witness below is not a collapsed one. -/
theorem rates_pos_box (n : ℕ) {c : ℝ} (hc : 0 < c) (hn : 1 ≤ n) (ρ : ℤ)
    (s : Fin (latticeCount (fun a => (boxAtoms n c a).halfspace) (boxForm n hn) ρ)) :
    0 < rates (fun a => (boxAtoms n c a).halfspace) (boxForm n hn)
      (Ttc.toDNF (boxForm n hn)) ρ (smpOf n c ρ) (vlOf n c) s :=
  rates_pos (toDNF_isDNFOf (boxForm n hn)) (hasLatticeEnum_bxOf n c hn ρ)
    (fun _ _ => volume_bxOf_pos n hc) (fun _ hi x _ => smpOf_pos n hc hn ρ hi x) s

/-- **The constructed rates sum to the box's volume.** -/
theorem sum_rates_box (n : ℕ) {c : ℝ} (hc : 0 < c) (hn : 1 ≤ n) (ρ : ℤ) :
    ∑ s, rates (fun a => (boxAtoms n c a).halfspace) (boxForm n hn)
        (Ttc.toDNF (boxForm n hn)) ρ (smpOf n c ρ) (vlOf n c) s
      = (volume (bxOf n c)).toReal := by
  rw [rates_eq_thOf n c hn ρ]
  exact sum_thOf n hc hn ρ

/-- **`big`, for the constructed rates** — the paper's regime condition, at every
`(ε, δ) ∈ (0,1]²`.  This is the hypothesis a degenerate `θ ≡ 0` would fail. -/
theorem big_rates_box (n : ℕ) (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (1 - (parS n hn ε δ hε0 hε1).epsPrime) * (parS n hn ε δ hε0 hε1).thresh / 8
      ≤ ∑ s, rates (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
          (boxForm n hn) (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε δ hε0 hε1)
          (smpOf n (sideS n hn ε δ hε0 hε1) (rhoS n hn ε δ hε0 hε1))
          (vlOf n (sideS n hn ε δ hε0 hε1)) s :=
  (epsPrime_thresh_le_volumeS hn hε0 hε1 hδ0 hδ1).trans
    (sum_rates_box n (sideS_pos hn hε0 hε1) hn (rhoS n hn ε δ hε0 hε1)).ge

/-- **`Ttc.ttc_volume` at the constructed rates, at every `(ε, δ) ∈ (0,1]²`.**

`Ttc.Box.ttc_volume_box_at` with its hand-written `Ttc.Box.thOf` replaced by
`Ttc.rates` — so the capstone's `θ` binder is met by the construction of this file,
not by an ad-hoc function, and at every accuracy pair.  Taking `(ε, δ)` strictly
inside `(0,1)` — e.g. `(1/2, 1/2)`, `Ttc.Box.ttc_volume_box_rates_sharp` — makes
the accuracy conclusion `1 − δ ≤ …` a genuine lower bound on a probability. -/
theorem ttc_volume_box_rates (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (1 - δ ≤ (trajLaw
        (rates (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace) (boxForm n hn)
          (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε δ hε0 hε1)
          (smpOf n (sideS n hn ε δ hε0 hε1) (rhoS n hn ε δ hε0 hε1))
          (vlOf n (sideS n hn ε δ hε0 hε1)))
        {t : ℕ → Fin (latticeCount
            (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
            (boxForm n hn) (rhoS n hn ε δ hε0 hε1)) → ℕ |
          ttcOutput (parS n hn ε δ hε0 hε1)
              (coveredOracles (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
                (boxForm n hn) (rhoS n hn ε δ hε0 hε1) (vlOf n (sideS n hn ε δ hε0 hε1)))
              Ttc.toDNF (rhoS n hn ε δ hε0 hε1) (boxForm n hn) t
            ∈ relErr ε (volSol (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
                (boxForm n hn))}).toReal)
    ∧
    (∀ (t : ℕ → Fin (latticeCount
        (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
        (boxForm n hn) (rhoS n hn ε δ hε0 hε1)) → ℕ) (cVol cSample thr : ℕ),
      (thr : ℝ) = (parS n hn ε δ hε0 hε1).thresh →
      Terminates (parS n hn ε δ hε0 hε1)
          (coveredOracles (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
            (boxForm n hn) (rhoS n hn ε δ hε0 hε1) (vlOf n (sideS n hn ε δ hε0 hε1)) t)
          (Ttc.toDNF (boxForm n hn)) →
      runCost (parS n hn ε δ hε0 hε1)
          (coveredOracles (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
            (boxForm n hn) (rhoS n hn ε δ hε0 hε1) (vlOf n (sideS n hn ε δ hε0 hε1)) t)
          cVol cSample (rhoS n hn ε δ hε0 hε1) (Ttc.toDNF (boxForm n hn))
        ≤ (Ttc.toDNF (boxForm n hn)).length * (cVol + cSample * thr)) := by
  have hcpos : 0 < sideS n hn ε δ hε0 hε1 := sideS_pos hn hε0 hε1
  exact ttc_volume_rates (boxAtoms n (sideS n hn ε δ hε0 hε1)) (boxForm n hn) ε δ
    hε0 hε1 hδ0 hδ1 hn
    (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace) rfl Ttc.toDNF
    (toDNF_isDNFOf _) (toDNF_isPositive (boxForm_isPositive hn))
    (one_le_card_cubes_box n hn) (one_le_card_facets_box n hn)
    (parS n hn ε δ hε0 hε1) rfl
    (isBounded_sol_bxOf n (sideS n hn ε δ hε0 hε1) hn)
    (coeff_ne_zero_bxOf n (sideS n hn ε δ hε0 hε1) hn)
    (fun _ => boxCentre n (sideS n hn ε δ hε0 hε1)) (gamS n hn ε δ hε0 hε1)
    (gamS_pos hn hε0 hε1) (ball_subset_bxOf n (sideS n hn ε δ hε0 hε1) hn)
    (vlOf n (sideS n hn ε δ hε0 hε1)) (VolumeAlgorithm.exact n) ()
    (by
      intro i hi
      show (volume (bxOf n (sideS n hn ε δ hε0 hε1))).toReal
          = gamS n hn ε δ hε0 hε1 ^ n
            * (volume (roundBody (boxCentre n (sideS n hn ε δ hε0 hε1))
                (gamS n hn ε δ hε0 hε1)
                (region (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace) i))).toReal
      rw [region_eq_bxOf n (sideS n hn ε δ hε0 hε1) hn hi]
      exact toReal_volume_eq (gamS_pos hn hε0 hε1))
    (by
      intro i hi
      rw [region_eq_bxOf n (sideS n hn ε δ hε0 hε1) hn hi]
      have h0 : (0 : ℝ) ≤ (volume (bxOf n (sideS n hn ε δ hε0 hε1))).toReal :=
        ENNReal.toReal_nonneg
      have he := parS_epsPrime_pos (δ := δ) hn hε0 hε1
      show (volume (bxOf n (sideS n hn ε δ hε0 hε1))).toReal ∈ Set.Icc _ _
      constructor <;> nlinarith)
    (fun _ _ => volume_bxOf_pos n hcpos)
    (smpOf n (sideS n hn ε δ hε0 hε1) (rhoS n hn ε δ hε0 hε1))
    (samplerOf n hn hcpos (rhoS n hn ε δ hε0 hε1) (parS_epsPrime_pos (δ := δ) hn hε0 hε1)
      (parS_epsPrime_le (δ := δ) hn hε0 hε1))
    (big_rates_box n hn hε0 hε1 hδ0 hδ1)

/-- **The sharp instance at the constructed rates**, `ε = δ = 1/2`.  Packaged
through `Ttc.Box.AtParams`, whose `θ` is existential — here witnessed by
`Ttc.rates` — so that the accuracy conclusion `1/2 ≤ (trajLaw …).toReal` is a real
bound, not the `0 ≤ …` of the `ε = δ = 1` witness. -/
theorem atParams_rates (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) : AtParams n ε δ := by
  obtain ⟨hacc, hrun⟩ := ttc_volume_box_rates n hn ε δ hε0 hε1 hδ0 hδ1
  exact ⟨boxAtoms n (sideS n hn ε δ hε0 hε1), boxForm n hn, parS n hn ε δ hε0 hε1,
    gamS n hn ε δ hε0 hε1, vlOf n (sideS n hn ε δ hε0 hε1),
    rates (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace) (boxForm n hn)
      (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε δ hε0 hε1)
      (smpOf n (sideS n hn ε δ hε0 hε1) (rhoS n hn ε δ hε0 hε1))
      (vlOf n (sideS n hn ε δ hε0 hε1)),
    hε0, hε1, hδ0, hδ1, rfl, rfl, rfl,
    isBounded_sol_bxOf n (sideS n hn ε δ hε0 hε1) hn,
    fun _ _ => volume_bxOf_pos n (sideS_pos hn hε0 hε1),
    big_rates_box n hn hε0 hε1 hδ0 hδ1, hacc, hrun⟩

/-- **The sharp witness at the constructed rates**, `ε = δ = 1/2`. -/
theorem atParams_rates_sharp (n : ℕ) (hn : 1 ≤ n) : AtParams n (1/2) (1/2) :=
  atParams_rates n hn (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Box

/-! ## Axiom profile

Every declaration of this file, checked transitively (`CLAUDE.md` §4).  Expect
`[propext, Classical.choice, Quot.sound]` throughout. -/

-- the construction
#print axioms cubeOf
#print axioms cubeOf_spec
#print axioms exists_cube_mem_of_mem_sol
#print axioms cubeAt
#print axioms cubeAt_spec
#print axioms rates

-- `theta_eq`, and non-degeneracy
#print axioms theta_eq_rates
#print axioms rates_pos
#print axioms sum_rates_pos
#print axioms pos_of_almostUniform
#print axioms finite_sol_lattice_of_hasLatticeEnum
#print axioms finite_region_lattice
#print axioms rates_pos_of_almostUniform

-- `gen_mem`
#print axioms exists_lattice_point_region
#print axioms exists_enum_mem_region
#print axioms gen_mem_of_enum
#print axioms gen_mem_of_geometry

-- the capstone with the three binders removed
#print axioms ttc_volume_rates

-- the witness
#print axioms Box.rates_eq_thOf
#print axioms Box.smpOf_pos
#print axioms Box.rates_pos_box
#print axioms Box.sum_rates_box
#print axioms Box.big_rates_box
#print axioms Box.ttc_volume_box_rates
#print axioms Box.atParams_rates
#print axioms Box.atParams_rates_sharp

end Ttc
