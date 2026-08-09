/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.CanonPolytope

/-!
# `Exec/RegimeInputs`: the two per-cube inputs to the pointwise rate bound

`Ttc.ttc_volume_final` (and `Ttc.ttc_volume_endToEnd_canon` before it) carries the
regime binder

```
big : ∀ c ∈ mcGood …, (1 − ε')·Thresh/8 ≤ ∑ s, rates … (e2eSampD …) (mcVol … c) s
```

which is the paper's `Λ ≥ (1−ε')·Thresh/8` (`sections/analysis.tex:295`).  Turning
that binder into a *consequence* of a hypothesis on `Vol(Sol F)` needs a pointwise
lower bound on each summand `θ_s = sampD(x_s)·Vol_ED(cube of s)`, and that bound has
exactly two inputs, one per factor:

* **the sampler factor** — `eq:almostuniform` for the capstone's *own* constructed
  law `Ttc.e2eSampD` at the canonical description, at **every** cube of an arbitrary
  positive DNF: `Ttc.e2eSampD_almostUniform`;
* **the volume factor** — the lower half of the constructed Monte-Carlo oracle's
  two-sided estimate at a good coin: `Ttc.mcVol_ge`.

Both are about the data the capstone constructs, not about an assumed oracle: the
first is `Ttc.almostUniform_of_kv97Sampler` at `Ttc.e2eSampler`, the second is
`Ttc.mcVol_mem_relErr`.  `Ttc.Box.canonSampD_box_almostUniform` (`Exec/Regime`) is
the one-cube box special case of the first; nothing here is box-specific.

## What had to be proved along the way

`Ttc.almostUniform_of_kv97Sampler` asks for two side conditions on each cube's
dilated lattice: finiteness and **nonemptiness** of
`(10^ρ · P(cᵢ)) ∩ ℤⁿ`.  For the box both come from `Ttc.Box.dilFiniteOf` /
`Ttc.Box.latNonemptyOf`, which compute with the box.  In general:

* finiteness is `Arlib.Lattice.finite_inter_intLattice` at the dilate of a bounded
  region;
* nonemptiness is `Ttc.exists_intLattice_mem_ball` — every open ball of radius
  greater than `√n/2` contains an integer point, namely the coordinatewise rounding
  of its centre — applied to the ball of radius `γ` that
  `Ttc.gamma_le_latticeScale_mul` puts inside `10^ρ · P(cᵢ)`.  The radius test is
  met with enormous room by `Ttc.sqrt_dim_half_lt_gamma`: `γ ≥ 64n > √n/2`.

So **no extra hypothesis** beyond the capstone's own is needed; in particular `hne`
is *not* a hypothesis of `Ttc.e2eSampD_almostUniform`.
-/

namespace Ttc

open MeasureTheory Set Pointwise

variable {A : Type*} {n : ℕ}

/-! ## 1. The volume factor -/

/-- **The Monte-Carlo volume estimate is at least `(1 − ε')·Vol(P(cᵢ))` at a good
coin.**  The lower half of `Ttc.mcVol_mem_relErr`, whose conclusion is membership in
`Ttc.relErr ε' (volume (region M i)).toReal = Set.Icc ((1−ε')·b) ((1+ε')·b)`.

This is the `Vol_ED` factor of each rate `θ_s`; no hypothesis about the oracle is
used, only that the coin lies in the constructed oracle's own good event. -/
theorem mcVol_ge (M : A → Set (Space n)) (D : DNF A)
    (cen : {c : Cube A // c ∈ D} → Space n) (γ ε' δ' : ℝ) {c : ℕ → Space n}
    (hc : c ∈ mcGood M D cen γ ε' δ') (i : {c : Cube A // c ∈ D}) :
    (1 - ε') * (volume (region M i.val)).toReal ≤ mcVol M D cen γ ε' δ' c i.val :=
  (mcVol_mem_relErr M D cen γ ε' δ' hc i.val i.property).1

/-! ## 2. A lattice point in a large enough ball

The only genuinely new geometry below.  `Ttc.almostUniform_of_kv97Sampler` needs the
dilated region to contain an integer point; the dilated region contains a ball of
radius `γ` (that is what `alg:prec`'s `ρ = ⌈log₁₀(γ/γ̂)⌉` buys), and a ball of radius
more than `√n/2` always contains one.
-/

/-- **Coordinatewise rounding lands within `√n/2`.**  For any `z : ℝⁿ` the integer
point `(round (z k))ₖ` is at Euclidean distance at most `√n/2` from `z`, because each
coordinate moves by at most `1/2`. -/
theorem dist_round_le (z : Space n) :
    dist (WithLp.toLp 2 (fun k => (round (z k) : ℝ)) : Space n) z ≤ Real.sqrt n / 2 := by
  classical
  rw [EuclideanSpace.dist_eq]
  have hsum : ∑ k : Fin n, dist ((round (z k) : ℝ)) (z k) ^ 2 ≤ (n : ℝ) * (1 / 2) ^ 2 := by
    calc ∑ k : Fin n, dist ((round (z k) : ℝ)) (z k) ^ 2
        ≤ ∑ _k : Fin n, ((1 : ℝ) / 2) ^ 2 := by
          refine Finset.sum_le_sum fun k _ => ?_
          have h : dist ((round (z k) : ℝ)) (z k) ≤ 1 / 2 := by
            rw [Real.dist_eq, abs_sub_comm]
            exact abs_sub_round (z k)
          have h0 : (0 : ℝ) ≤ dist ((round (z k) : ℝ)) (z k) := dist_nonneg
          nlinarith
      _ = (n : ℝ) * (1 / 2) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc Real.sqrt (∑ k : Fin n, dist ((WithLp.toLp 2 (fun k => (round (z k) : ℝ)) : Space n) k)
          (z k) ^ 2)
      = Real.sqrt (∑ k : Fin n, dist ((round (z k) : ℝ)) (z k) ^ 2) := rfl
    _ ≤ Real.sqrt ((n : ℝ) * (1 / 2) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt n / 2 := by
        rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1 / 2)]
        ring

/-- **Every open ball of radius more than `√n/2` contains an integer point.**
The witness is the coordinatewise rounding of the centre (`Ttc.dist_round_le`). -/
theorem exists_intLattice_mem_ball (z : Space n) {r : ℝ} (hr : Real.sqrt n / 2 < r) :
    (Metric.ball z r ∩ intLattice n).Nonempty := by
  classical
  refine ⟨(WithLp.toLp 2 (fun k => (round (z k) : ℝ)) : Space n), ?_, ?_⟩
  · exact Metric.mem_ball.2 (lt_of_le_of_lt (dist_round_le z) hr)
  · intro k
    exact ⟨round (z k), rfl⟩

/-! ## 3. `γ` clears `√n/2` by a mile -/

/-- **`1 ≤ log(8r/η)`.**  Sharper than `Ttc.Params.log_pos`, and all that is needed
below: `η ≤ 1` forces `8/η ≥ 8`, and `log 8 > 1` because `e < 8`. -/
theorem Params.one_le_log (P : Params) : 1 ≤ Real.log (8 * P.r / P.eta) := by
  have h8 : (1 : ℝ) ≤ Real.log 8 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have hle : Real.log 8 ≤ Real.log (8 / P.eta) := by
    refine Real.log_le_log (by norm_num) ?_
    rw [le_div_iff₀ P.eta_pos]
    nlinarith [P.eta_le_one, P.eta_pos]
  rw [P.log_split]
  linarith [P.log_r_nonneg]

/-- **`64n ≤ γ`.**  Every factor of `γ = (64mn/η)·√(log(8r/η))` is at least `1`
except the `64n`: `m ≥ 1`, `η ≤ 1`, and `√(log(8r/η)) ≥ 1` by
`Ttc.Params.one_le_log`. -/
theorem Params.mul_dim_le_gamma (P : Params) : 64 * (P.n : ℝ) ≤ P.gamma := by
  have hn1 : (1 : ℝ) ≤ (P.n : ℝ) := by exact_mod_cast P.hn
  have hm1 : (1 : ℝ) ≤ (P.m : ℝ) := by exact_mod_cast P.hm
  have hs : (1 : ℝ) ≤ Real.sqrt (Real.log (8 * P.r / P.eta)) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt P.one_le_log
  have hfac : 64 * (P.n : ℝ) ≤ 64 * (P.m : ℝ) * P.n / P.eta := by
    rw [le_div_iff₀ P.eta_pos]
    nlinarith [P.eta_le_one, P.eta_pos]
  have hfac0 : (0 : ℝ) ≤ 64 * (P.m : ℝ) * P.n / P.eta :=
    div_nonneg (by positivity) P.eta_pos.le
  rw [Params.gamma]
  nlinarith

/-- **`√n/2 < γ`** — the radius test of `Ttc.exists_intLattice_mem_ball`, met by the
inscribed radius `alg:prec` targets.  Uses only `√n ≤ n` (valid since `n ≥ 1`) and
`Ttc.Params.mul_dim_le_gamma`. -/
theorem sqrt_dim_half_lt_gamma (P : Params) {n : ℕ} (hn : P.n = n) :
    Real.sqrt n / 2 < P.gamma := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have := P.hn; rw [hn] at this; exact_mod_cast this
  have hs0 : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hsq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hs1 : (1 : ℝ) ≤ Real.sqrt n := by nlinarith
  have hle : Real.sqrt n ≤ (n : ℝ) := by nlinarith
  have hg := P.mul_dim_le_gamma
  rw [hn] at hg
  linarith

/-! ## 4. `eq:almostuniform` for the capstone's own sampler, at every cube

`Ttc.Box.canonSampD_box_almostUniform` (`Exec/Regime`) is this statement for the
one-cube box; the generalisation goes through because every ingredient of the
canonical description — `Ttc.canonAm`, `Ttc.canonBv`, `Ttc.canonDm`,
`Ttc.canonRfac`, `Ttc.e2eSampler` — is already stated for an arbitrary positive DNF.
-/

/-- **`eq:almostuniform` for `Ttc.e2eSampD` at the canonical description, at every
cube of an arbitrary positive DNF.**

The law is *the* term the capstone's `big` binder is stated about
(`Ttc.ttc_volume_endToEnd_canon`, `Ttc.ttc_volume_final`), spelled out; it is also
`Ttc.canonSampD atoms D P cen gammaHat i.val` by `rfl` once `ρ = P.precision γ̂`.

Nothing about the sampler is assumed: `Ttc.e2eSampler` builds a `Ttc.KV97Sampler`
for it out of facts about the *input polytope* only, and
`Ttc.almostUniform_of_kv97Sampler` reads `eq:almostuniform` off that.  The
hypotheses are the capstone's own:

* `hpos`  — no negated literal, so each cube's region is a half-space system;
* `hn`    — the block's dimension is the ambient one;
* `hr`    — at least one facet (`Params`' own `1 ≤ r`, as a cardinality);
* `hbdd`  — each region is bounded (the capstone's `hbdd` on `Sol(F)` gives this
  through `Ttc.isBounded_region_of_isBounded_sol`), which makes `Ttc.canonDm` a
  genuine diameter and the dilated lattice finite;
* `hg`, `hball` — the inscribed ball of radius `γ̂`;
* `hρ`    — the precision `alg:prec` computes.

`0 < ε'` and `ε' ≤ 1/2` are *not* hypotheses: they are `Ttc.Params.epsPrime_pos` and
a consequence of `ε ≤ 1`. -/
theorem e2eSampD_almostUniform (atoms : A → LinAtom n) {D : DNF A}
    (hpos : DNF.IsPositive D) (P : Params) (hn : P.n = n)
    (hr : 1 ≤ Nat.card (FacetIndex D))
    (hbdd : ∀ i : {c : Cube A // c ∈ D},
      Bornology.IsBounded (region (fun a => (atoms a).halfspace) i.val))
    (cen : {c : Cube A // c ∈ D} → Space n) {gammaHat : ℝ} (hg : 0 < gammaHat)
    (hball : ∀ i, Metric.ball (cen i) gammaHat
      ⊆ region (fun a => (atoms a).halfspace) i.val)
    {ρ : ℤ} (hρ : ρ = P.precision gammaHat) (i : {c : Cube A // c ∈ D}) :
    AlmostUniform
      (e2eSampD (fun a => (atoms a).halfspace) D ρ P.epsPrime (canonRfac D)
        (Jt := Fin (Nat.card (FacetIndex D))) (canonAm atoms D)
        (canonBv atoms D (latticeScale ρ)) cen gammaHat
        (canonDm (fun a => (atoms a).halfspace) D ρ) i.val)
      (region (fun a => (atoms a).halfspace) i.val ∩ fineLattice n (latticeScale ρ))
      P.epsPrime := by
  classical
  have hn1 : 1 ≤ n := by have := P.hn; rwa [hn] at this
  have hep0 : 0 < P.epsPrime := P.epsPrime_pos
  have hep : P.epsPrime ≤ 1 / 2 := by
    rw [Params.epsPrime]; linarith [P.hε1, P.hε0]
  have hs : (0 : ℝ) < latticeScale ρ := latticeScale_pos ρ
  -- the `KV97Sampler` for the canonical description
  have S : KV97Sampler A n (fun a => (atoms a).halfspace) D ρ P.epsPrime
      (e2eSampD (fun a => (atoms a).halfspace) D ρ P.epsPrime (canonRfac D)
        (Jt := Fin (Nat.card (FacetIndex D))) (canonAm atoms D)
        (canonBv atoms D (latticeScale ρ)) cen gammaHat
        (canonDm (fun a => (atoms a).halfspace) D ρ)) :=
    e2eSampler hn1 hep0 (Fin (Nat.card (FacetIndex D))) (canonAm atoms D)
      (canonBv atoms D (latticeScale ρ))
      (fun j => canon_smul_region_subset_body atoms hpos hs j)
      (canonRfac D) (by rw [canonRfac]; exact_mod_cast hr)
      (by rw [canonRfac, Fintype.card_fin])
      cen gammaHat hg hball
      (canonDm (fun a => (atoms a).halfspace) D ρ)
      (by
        intro j x hx y hy
        rw [canon_body_eq_smul_region atoms hpos hs j] at hx hy
        exact Metric.dist_le_diam_of_mem ((hbdd j).smul₀ _) hx hy)
  -- finiteness of the dilated lattice
  have hfin : ((latticeScale ρ • region (fun a => (atoms a).halfspace) i.val)
      ∩ intLattice n : Set (Space n)).Finite :=
    Arlib.Lattice.finite_inter_intLattice ((hbdd i).smul₀ _)
  -- nonemptiness, from the inscribed ball of radius `γ` the precision buys
  have hne : ((latticeScale ρ • region (fun a => (atoms a).halfspace) i.val)
      ∩ intLattice n : Set (Space n)).Nonempty := by
    have hsub : Metric.ball (latticeScale ρ • cen i) (latticeScale ρ * gammaHat)
        ⊆ latticeScale ρ • region (fun a => (atoms a).halfspace) i.val :=
      ball_radius_scales hs _ _ (hball i)
    have hgam : P.gamma ≤ latticeScale ρ * gammaHat := by
      rw [hρ]; exact gamma_le_latticeScale_mul P hg
    obtain ⟨y, hy1, hy2⟩ :=
      exists_intLattice_mem_ball (latticeScale ρ • cen i) (sqrt_dim_half_lt_gamma P hn)
    exact ⟨y, hsub (Metric.ball_subset_ball hgam hy1), hy2⟩
  exact almostUniform_of_kv97Sampler S hep0 hep i hfin hne

/-- **The same, in the capstone's own shape.**  `Ttc.ttc_volume_endToEnd_canon`
carries `isDNF` and `hbdd : Bornology.IsBounded (sol M φ)` rather than per-cube
boundedness; `Ttc.isBounded_region_of_isBounded_sol` converts. -/
theorem e2eSampD_almostUniform_of_isBounded_sol (atoms : A → LinAtom n)
    {D : DNF A} {φ : BForm A} (hD : IsDNFOf D φ) (hpos : DNF.IsPositive D)
    (P : Params) (hn : P.n = n) (hr : 1 ≤ Nat.card (FacetIndex D))
    (hbdd : Bornology.IsBounded (sol (fun a => (atoms a).halfspace) φ))
    (cen : {c : Cube A // c ∈ D} → Space n) {gammaHat : ℝ} (hg : 0 < gammaHat)
    (hball : ∀ i, Metric.ball (cen i) gammaHat
      ⊆ region (fun a => (atoms a).halfspace) i.val)
    {ρ : ℤ} (hρ : ρ = P.precision gammaHat) (i : {c : Cube A // c ∈ D}) :
    AlmostUniform
      (e2eSampD (fun a => (atoms a).halfspace) D ρ P.epsPrime (canonRfac D)
        (Jt := Fin (Nat.card (FacetIndex D))) (canonAm atoms D)
        (canonBv atoms D (latticeScale ρ)) cen gammaHat
        (canonDm (fun a => (atoms a).halfspace) D ρ) i.val)
      (region (fun a => (atoms a).halfspace) i.val ∩ fineLattice n (latticeScale ρ))
      P.epsPrime :=
  e2eSampD_almostUniform atoms hpos P hn hr
    (fun j => isBounded_region_of_isBounded_sol hD hbdd j.property) cen hg hball hρ i

/-- **`Ttc.canonSampD` is the term above**, by `rfl` — so the abbreviation cannot
have drifted from the law the capstone's `big` binder mentions. -/
theorem canonSampD_almostUniform (atoms : A → LinAtom n) {D : DNF A}
    (hpos : DNF.IsPositive D) (P : Params) (hn : P.n = n)
    (hr : 1 ≤ Nat.card (FacetIndex D))
    (hbdd : ∀ i : {c : Cube A // c ∈ D},
      Bornology.IsBounded (region (fun a => (atoms a).halfspace) i.val))
    (cen : {c : Cube A // c ∈ D} → Space n) {gammaHat : ℝ} (hg : 0 < gammaHat)
    (hball : ∀ i, Metric.ball (cen i) gammaHat
      ⊆ region (fun a => (atoms a).halfspace) i.val)
    (i : {c : Cube A // c ∈ D}) :
    AlmostUniform (canonSampD atoms D P cen gammaHat i.val)
      (region (fun a => (atoms a).halfspace) i.val
        ∩ fineLattice n (latticeScale (P.precision gammaHat))) P.epsPrime :=
  e2eSampD_almostUniform atoms hpos P hn hr hbdd cen hg hball rfl i

end Ttc

#print axioms Ttc.mcVol_ge
#print axioms Ttc.exists_intLattice_mem_ball
#print axioms Ttc.sqrt_dim_half_lt_gamma
#print axioms Ttc.e2eSampD_almostUniform
#print axioms Ttc.e2eSampD_almostUniform_of_isBounded_sol
#print axioms Ttc.canonSampD_almostUniform
