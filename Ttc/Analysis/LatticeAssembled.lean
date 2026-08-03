/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Analysis.NonconvAssembled
import Ttc.Analysis.Lattice
import Ttc.Analysis.FacetOfDNF
import Ttc.Model.ProblemSetting
import Ttc.Analysis.Invariants

/-!
# `lem:lattice` for the solution set of a positive DNF

`Ttc.FacetSystem.nonconv_of_ball` proves `lem:nonconv` for a facet system against
its **integer**-point count. The algorithm counts points of `𝕃ⁿ = 10^(−ρ)·ℤⁿ`
instead, and its `Q` is `Sol(F)`. This file closes both gaps:

* `Ttc.facetSystem` (`Analysis/FacetOfDNF`) makes `Sol(F)` a facet system's body,
  for a DNF with no negated literal;
* `Ttc.FacetSystem.scale` dilates it by `10^ρ`, and `Ttc.lattice_bounds`
  (`Analysis/Lattice`) transports the conclusion back.

**Where `GetPrecision` becomes load-bearing.** The dilated system must contain a
ball of radius `γ` — that is exactly what `ρ = ⌈log₁₀(γ/γ̂)⌉` buys, since it makes
`10^ρ·γ̂ ≥ γ` (`Ttc.gamma_le_latticeScale_mul`). So `alg:prec` is not decoration:
without it the shell bound has nothing to stand on.
-/

namespace Ttc

open MeasureTheory Set Pointwise

variable {A : Type*} {n : ℕ}

/-! ## The DNF facet system, presented by coefficient vectors -/

/-- The coefficient vector of each facet of a DNF — the paper's `A_ij`. -/
noncomputable def dnfCoeff (atoms : A → LinAtom n) (D : DNF A) :
    FacetIndex D → Fin n → ℝ := fun j => (atoms j.2.val.atom).coeff

theorem facetSystem_f (atoms : A → LinAtom n) (D : DNF A) (j : FacetIndex D) (x : Space n) :
    (facetSystem atoms D).f j x = ∑ k, dnfCoeff atoms D j k * x k := rfl

theorem facetSystem_w (atoms : A → LinAtom n) (D : DNF A) (j : FacetIndex D) :
    (facetSystem atoms D).w j = coeffNorm (dnfCoeff atoms D j) := rfl

/-! ## Dilating a facet system -/

variable {ι F : Type*}

/-- Dilating a facet system dilates its inscribed balls. -/
theorem ball_subset_scale_piece (S : FacetSystem n ι F) {c γ : ℝ} (hc : 0 < c)
    {cen : Space n} {i : ι} (h : Metric.ball cen γ ⊆ S.piece 0 i) :
    Metric.ball (c • cen) (c * γ) ⊆ (S.scale c).piece 0 i := by
  rw [S.scale_piece_zero hc]
  exact ball_radius_scales hc _ _ h

/-- Dilation keeps a piece's volume finite. -/
theorem volume_scale_piece_ne_top (S : FacetSystem n ι F) {c : ℝ} (hc : 0 < c) (i : ι)
    (h : volume (S.piece 0 i) ≠ ⊤) : volume ((S.scale c).piece 0 i) ≠ ⊤ := by
  rw [S.scale_piece_zero hc, volume_smul_body hc.le]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top h

/-! ## What `GetPrecision` buys -/

/-- **`10^ρ · γ̂ ≥ γ` for `ρ = ⌈log₁₀(γ/γ̂)⌉`** (`alg:prec` line 91). This is the
one place the precision enters the accuracy proof: it is what makes the dilated
polytopes contain a ball of the radius `lem:nonconv` needs. -/
theorem gamma_le_latticeScale_mul (P : Params) {gammaHat : ℝ} (hg : 0 < gammaHat) :
    P.gamma ≤ latticeScale (P.precision gammaHat) * gammaHat := by
  have hx : 0 < P.gamma / gammaHat := div_pos P.gamma_pos hg
  have h1 : P.gamma / gammaHat ≤ (10 : ℝ) ^ (⌈Real.logb 10 (P.gamma / gammaHat)⌉ : ℤ) := by
    rw [← Real.rpow_intCast]
    calc P.gamma / gammaHat = (10 : ℝ) ^ (Real.logb 10 (P.gamma / gammaHat)) :=
          (Real.rpow_logb (by norm_num) (by norm_num) hx).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Int.le_ceil _)
  rw [div_le_iff₀ hg] at h1
  rw [latticeScale, Params.precision]
  linarith

/-! ## `lem:lattice`, assembled -/

set_option maxHeartbeats 1000000 in
/-- **`lem:lattice` for the actual solution set.**

`Vol(F)` is within `(1 ± η)` of the normalised lattice count `|Sol(F) ∩ 𝕃ⁿ|/10^(ρn)`
at `η = ε/8`, under exactly the paper's hypotheses: the atoms are linear, no
literal is negated, every polytope contains an `ℓ₂`-ball of radius `γ̂` about its
own centre and has finite volume, every facet has a nonzero normal, and `m`, `r`
bound the family. -/
theorem lattice_of_dnf (atoms : A → LinAtom n) {D : DNF A} {φ : BForm A}
    (hDNF : IsDNFOf D φ) (hpos : DNF.IsPositive D)
    (P : Params) (hn : P.n = n)
    (hm : (Nat.card {c : Cube A // c ∈ D} : ℝ) ≤ P.m)
    (hr : (Nat.card (FacetIndex D) : ℝ) ≤ P.r)
    (hAnz : ∀ j : FacetIndex D, 0 < ∑ k, (atoms j.2.val.atom).coeff k ^ 2)
    (cen : {c : Cube A // c ∈ D} → Space n) {gammaHat : ℝ} (hg : 0 < gammaHat)
    (hball : ∀ i, Metric.ball (cen i) gammaHat
      ⊆ region (fun a => (atoms a).halfspace) i.val)
    (hfin : ∀ i : {c : Cube A // c ∈ D},
      volume (region (fun a => (atoms a).halfspace) i.val) ≠ ⊤)
    {ρ : ℤ} (hρ : ρ = P.precision gammaHat) :
    ((1 - P.eta) * normalisedCount (fun a => (atoms a).halfspace) φ ρ
        ≤ volSol (fun a => (atoms a).halfspace) φ ∧
      volSol (fun a => (atoms a).halfspace) φ
        ≤ (1 + P.eta) * normalisedCount (fun a => (atoms a).halfspace) φ ρ) ∧
      (sol (fun a => (atoms a).halfspace) φ ∩ fineLattice n (latticeScale ρ)).Finite := by
  classical
  haveI hfc : Finite {c : Cube A // c ∈ D} := D.finite_toSet.to_subtype
  haveI hfl : ∀ c : {c : Cube A // c ∈ D}, Finite {l : Lit A // l ∈ c.val} :=
    fun c => c.val.finite_toSet.to_subtype
  haveI : Finite (FacetIndex D) := inferInstance
  haveI : Fintype {c : Cube A // c ∈ D} := Fintype.ofFinite _
  haveI : Fintype (FacetIndex D) := Fintype.ofFinite _
  have hc0 : 0 < latticeScale ρ := latticeScale_pos ρ
  have hpiece : ∀ i, (facetSystem atoms D).piece 0 i
      = region (fun a => (atoms a).halfspace) i.val :=
    fun i => (region_eq_piece atoms hpos i).symm
  -- the dilated system inherits an inscribed ball of radius `γ`
  have hballS : ∀ i, Metric.ball (latticeScale ρ • cen i) P.gamma
      ⊆ ((facetSystem atoms D).scale (latticeScale ρ)).piece 0 i := by
    intro i
    refine subset_trans (Metric.ball_subset_ball ?_)
      (ball_subset_scale_piece _ hc0 (by rw [hpiece i]; exact hball i))
    rw [hρ]
    exact gamma_le_latticeScale_mul P hg
  have hfinS : ∀ i, volume (((facetSystem atoms D).scale (latticeScale ρ)).piece 0 i) ≠ ⊤ :=
    fun i => volume_scale_piece_ne_top _ hc0 i (by rw [hpiece i]; exact hfin i)
  -- `lem:nonconv` for the dilate
  have hmain := ((facetSystem atoms D).scale (latticeScale ρ)).nonconv_of_ball
    (dnfCoeff atoms D) (fun j x => facetSystem_f atoms D j x)
    (fun j => facetSystem_w atoms D j) hAnz P hn
    (by rw [← Nat.card_eq_fintype_card]; exact hm)
    (by rw [← Nat.card_eq_fintype_card]; exact hr)
    (fun i => latticeScale ρ • cen i) hballS hfinS
  -- the dilate is `10^ρ · Sol(F)`
  have hbody : ((facetSystem atoms D).scale (latticeScale ρ)).body 0
      = latticeScale ρ • sol (fun a => (atoms a).halfspace) φ := by
    rw [FacetSystem.scale_body_zero _ hc0, body_eq_sol atoms hpos hDNF]
  obtain ⟨hlow, hupp, hEfin⟩ := hmain
  rw [hbody] at hlow hupp hEfin
  refine ⟨lattice_bounds _ φ ρ hlow hupp, ?_⟩
  -- transport finiteness back through the dilation
  have himg : ((latticeScale ρ • sol (fun a => (atoms a).halfspace) φ)
      ∩ intLattice n).Finite := by
    rw [← image_latPt_eq]
    exact hEfin.image _
  refine Set.Finite.of_finite_image (f := fun x => latticeScale ρ • x) ?_ ?_
  · rw [Set.image_smul, smul_inter_fineLattice (latticeScale_ne_zero ρ)]
    exact himg
  · exact (smul_right_injective (Space n) (latticeScale_ne_zero ρ)).injOn

/-! ## `lem:lattice` for a `Ttc.TtcProb`

The two fields `lattice_lo`/`lattice_hi` that `Ttc.TtcProb` used to carry are now
these two theorems. Nothing downstream changes: `Ttc.TtcProb.toAnalysis`
(`Analysis/Capstone`) reads them by the same names.
-/

namespace TtcProb

variable {A : Type*} {n : ℕ} (T : TtcProb A n)

/-- A count is nonnegative — formerly a field. -/
theorem hL : 0 ≤ T.L := by
  rw [T.L_eq, normalisedCount]
  have h : (0:ℝ) < latticeScale T.ρ ^ n := pow_pos (latticeScale_pos T.ρ) n
  positivity

/-- **`lem:lattice` for the problem instance**, at the parameter block's `η`. -/
theorem lattice_two_sided :
    (1 - T.P.eta) * T.L ≤ volSol T.M T.φ ∧ volSol T.M T.φ ≤ (1 + T.P.eta) * T.L := by
  have hball : ∀ i, Metric.ball (T.cen i) T.gammaHat
      ⊆ region (fun a => (T.atoms a).halfspace) i.val := by
    intro i; rw [← T.M_eq]; exact T.ball_subset i
  have hfin : ∀ i : {c : Cube A // c ∈ T.D},
      volume (region (fun a => (T.atoms a).halfspace) i.val) ≠ ⊤ := by
    intro i; rw [← T.M_eq]; exact T.volume_ne_top i
  have h := lattice_of_dnf T.atoms T.isDNF T.isPositive T.P T.dim_eq T.cubes_le T.facets_le
    T.normal_ne_zero T.cen T.hgammaHat hball hfin T.rho_eq
  rw [T.L_eq, T.M_eq]
  exact h.1

/-- **`Sol(F) ∩ 𝕃ⁿ` is finite** — not assumed, but a consequence of `claim:cl`(a)
(see `Ttc.FacetSystem.finite_lattice_points`). This is what lets the run's sample
multiset be read as a count vector over a *finite* index, which the invariant of
`lem:numlattice` needs. -/
theorem sol_lattice_finite :
    (sol T.M T.φ ∩ fineLattice n (latticeScale T.ρ)).Finite := by
  have hball : ∀ i, Metric.ball (T.cen i) T.gammaHat
      ⊆ region (fun a => (T.atoms a).halfspace) i.val := by
    intro i; rw [← T.M_eq]; exact T.ball_subset i
  have hfin : ∀ i : {c : Cube A // c ∈ T.D},
      volume (region (fun a => (T.atoms a).halfspace) i.val) ≠ ⊤ := by
    intro i; rw [← T.M_eq]; exact T.volume_ne_top i
  have h := lattice_of_dnf T.atoms T.isDNF T.isPositive T.P T.dim_eq T.cubes_le T.facets_le
    T.normal_ne_zero T.cen T.hgammaHat hball hfin T.rho_eq
  rw [T.M_eq]
  exact h.2

/-- **The run only ever holds genuine solution lattice points.**

`𝒳` starts empty, the coverage filter and the thinning only remove
(`Oracles.halve_le`), and the only insertion is `GenerateSamples`, whose output
lies in `P(cᵢ) ∩ 𝕃ⁿ` by the `gen_mem` field. Since each `P(cᵢ) ⊆ Sol(F)`
(`thm:decomposition`), the whole run stays inside `Sol(F) ∩ 𝕃ⁿ`.

This is what makes the run's state a count vector over the **fixed finite** set
`Sol(F) ∩ 𝕃ⁿ` — the first structural step of the coupling that `lem:numlattice`
needs. -/
theorem run_state_mem (ω : T.Ω) :
    ∀ s ∈ (T.D.foldl (step T.P (T.O ω) T.fuel T.ρ) ⟨0, 1, 0, 0⟩).X,
      s ∈ sol T.M T.φ ∩ fineLattice n (latticeScale T.ρ) := by
  refine mem_run_state T.P (T.O ω) T.fuel T.ρ T.D ?_
  intro c i j N hi s hs
  obtain ⟨hreg, hlat⟩ := T.gen_mem ω c i j N hi s hs
  refine ⟨?_, hlat⟩
  have hsub : region T.M i ⊆ sol T.M T.φ := region_subset_sol T.isDNF hi
  exact hsub hreg

/-- **`lem:lattice`, lower half**, at `η = ε/8` — formerly a field. -/
theorem lattice_lo : (1 - T.ε / 8) * T.L ≤ volSol T.M T.φ := by
  have h := T.lattice_two_sided.1
  rwa [Params.eta, T.eps_eq] at h

/-- **`lem:lattice`, upper half**, at `η = ε/8` — formerly a field. -/
theorem lattice_hi : volSol T.M T.φ ≤ (1 + T.ε / 8) * T.L := by
  have h := T.lattice_two_sided.2
  rwa [Params.eta, T.eps_eq] at h

end TtcProb

end Ttc
