/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.Endgoal

/-!
# `Witness/BoxSharp`: the capstone at accuracy `ε < 1` and confidence `δ < 1`

## The defect this file closes

`Ttc.Box.ttc_volume_box` (`Ttc/Model/Endgoal.lean`) is the development's only
non-vacuity witness for the capstone `Ttc.ttc_volume`, and it instantiates it at
**`ε = 1` and `δ = 1`**.  At those values the accuracy conclusion reads

```
(1 : ℝ) - 1 ≤ (trajLaw …).toReal      i.e.      0 ≤ (…).toReal
```

which is true of *every* measure of *every* set — see `Ttc.Box.toReal_nonneg_any`
and `Ttc.Box.ttc_volume_box_accuracy_is_trivial` below, which prove exactly that
conjunct with no reference to the algorithm at all.  So the old witness certifies
that **the hypothesis bundle is inhabited** — a real and necessary check — and
certifies **nothing whatsoever about the conclusion**.

That is a known failure mode, and `#print axioms` is blind to it: nothing is ever
assumed, so the axiom profile is clean; the degeneracy lives in *which objects*
satisfy the hypotheses.  A bundle can be non-vacuous and yet *forced*, i.e. only
satisfiable by collapsing the very quantity the theorem is about.  One witness
cannot tell "the hypotheses are satisfiable" apart from "the hypotheses force
`ε = δ = 1`".

## What is here

A second, structurally different witness at `ε < 1` and `δ < 1`, and — the point —
the *pair*, landed as a theorem rather than as prose.

* `Ttc.Box.ttc_volume_box_sharp` — `Ttc.ttc_volume`, applied as it stands, at
  `ε = 1/2` and `δ = 1/2`.  Its accuracy conclusion is `1/2 ≤ (trajLaw …).toReal`,
  a genuine constraint on a probability.
* `Ttc.Box.ttc_volume_box_at` — the same, at **every** `(ε, δ) ∈ (0,1]²`.  This is
  what the arithmetic actually supports; `ttc_volume_box_sharp` is one line of it.
* `Ttc.Box.exists_two_ttc_volume_instances` — explicit witnesses at two *different*
  accuracy parameters, so `ε` and `δ` are provably not forced.

## Why the geometry survives shrinking `ε` and `δ`

The binding hypothesis is `big`, `(1 − ε')·Thresh/8 ≤ ∑ s, θ s`, and `Thresh` grows
without bound as `ε` and `δ` shrink.  The box's side is *chosen from* `Thresh`
(`Ttc.Box.sideS := max 1 Thresh`, following `Ttc.Box.side`), so the instance grows
with the threshold and the inequality is met with room to spare at every `(ε, δ)`:
`∑ θ = Vol(box) ≥ (1 − η)·L ≥ (7/8)·Thresh`, against a requirement of at most
`Thresh/8`.  Nothing in the construction was ever specific to `ε = δ = 1`; that the
old witness looked pinned there was an accident of `Ttc.Box.par`.

Everything geometric is re-derived here at a general side length `c` and precision
`ρ`, reusing `Ttc/Witness/Box.lean` (which is already parametric in `c` and `ρ`)
and `Ttc/Witness/BoxProb.lean`'s `ε`-agnostic pieces (`Ttc.Box.bxNormal`,
`Ttc.Box.bfac`, `Ttc.Box.eq_boxCube`, …).  `Ttc.ttc_volume` is applied verbatim; it
is not restated, weakened, or specialised.

## What this file does *not* claim

It does not improve any constant, and it does not make the accuracy conclusion
sharp in the sense of small `ε`.  `ε = δ = 1/2` is a *representative* interior
point; `Ttc.Box.ttc_volume_box_at` shows the whole open square works, so no
judgement call about "which coefficients matter" is being made.
-/

namespace Ttc

namespace Box

open MeasureTheory Set Pointwise

/-! ## Part 0.  The `ε = δ = 1` accuracy conclusion, shown to be empty

Before building anything, record precisely what the old witness's first conjunct
says.  It is `0 ≤ (μ S).toReal`, which `ENNReal.toReal` satisfies unconditionally.
-/

/-- **At `δ = 1` the accuracy half is vacuous.**  `1 − 1 = 0`, and the `toReal` of
any `ℝ≥0∞` — in particular of any measure of any set — is nonnegative. -/
theorem toReal_nonneg_any {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (S : Set Ω) :
    (1 : ℝ) - 1 ≤ (μ S).toReal := by
  simp

/-- **`Ttc.Box.ttc_volume_box`'s accuracy conjunct, proved without the algorithm.**

This is, verbatim, the first component of `Ttc.Box.ttc_volume_box`'s conclusion,
and the proof below never mentions `Ttc.ttc_volume`, `Ttc.ttcOutput`, or any
hypothesis of either: it is `Ttc.Box.toReal_nonneg_any`.  So the old witness's
accuracy statement carries no information about the algorithm — its content is
entirely in the fact that the 36 hypotheses could be met at all. -/
theorem ttc_volume_box_accuracy_is_trivial (n : ℕ) (hn : 1 ≤ n) :
    ((1 : ℝ) - 1 ≤ (trajLaw (thC n hn)
        {t : ℕ → Fin (latticeCount (fun a => (atm n hn a).halfspace)
            (boxForm n hn) (rho n hn)) → ℕ |
          ttcOutput (par n hn)
              (coveredOracles (fun a => (atm n hn a).halfspace) (boxForm n hn) (rho n hn)
                (vl n hn))
              Ttc.toDNF (rho n hn) (boxForm n hn) t
            ∈ relErr 1 (volSol (fun a => (atm n hn a).halfspace) (boxForm n hn))}).toReal) :=
  toReal_nonneg_any _ _

/-! ## Part 1.  The box at a general side length

`Ttc/Witness/Box.lean` is already parametric in the side `c` and the precision `ρ`.
What `Ttc/Witness/BoxProb.lean` adds is pinned to `Ttc.Box.par`, i.e. to
`ε = δ = 1`; the definitions below are its `(c, ρ)`-parametric form.  Nothing here
mentions accuracy or confidence.
-/

/-- The box `[0,c]ⁿ`, at a side length that is not yet fixed. -/
def bxOf (n : ℕ) (c : ℝ) : Set (Space n) := {x : Space n | ∀ k, 0 ≤ x k ∧ x k ≤ c}

/-- `Sol(F)` for the box's formula is the box. -/
theorem sol_eq_bxOf (n : ℕ) (c : ℝ) (hn : 1 ≤ n) :
    sol (fun a => (boxAtoms n c a).halfspace) (boxForm n hn) = bxOf n c :=
  sol_boxForm n c hn

/-- Every cube of the box's DNF has the box as its region — there is only one. -/
theorem region_eq_bxOf (n : ℕ) (c : ℝ) (hn : 1 ≤ n) {i : Cube (Fin n ⊕ Fin n)}
    (hi : i ∈ Ttc.toDNF (boxForm n hn)) :
    region (fun a => (boxAtoms n c a).halfspace) i = bxOf n c := by
  have hi' : i ∈ boxDNF n := by rwa [toDNF_boxForm hn] at hi
  rw [eq_boxCube hi']
  exact region_boxCube n c

/-- **`Ttc.ttc_volume`'s `hbdd`, at a general side.** -/
theorem isBounded_sol_bxOf (n : ℕ) (c : ℝ) (hn : 1 ≤ n) :
    Bornology.IsBounded (sol (fun a => (boxAtoms n c a).halfspace) (boxForm n hn)) := by
  rw [sol_eq_bxOf n c hn]
  exact isBounded_box n c

/-- **`Ttc.ttc_volume`'s `hcoeff`, at a general side** — every one of the `2n`
facet normals is a `±1` coordinate vector. -/
theorem coeff_ne_zero_bxOf (n : ℕ) (c : ℝ) (hn : 1 ≤ n) :
    ∀ j : FacetIndex (Ttc.toDNF (boxForm n hn)), (boxAtoms n c j.2.val.atom).coeff ≠ 0 := by
  refine coeff_ne_zero_of_normal_ne_zero ?_
  rw [toDNF_boxForm hn]
  exact boxAtoms_normal_ne_zero n c

/-- **`Ttc.ttc_volume`'s `ball_subset`, at a general side** — the inscribed ball of
radius `c/2` about the box's centre. -/
theorem ball_subset_bxOf (n : ℕ) (c : ℝ) (hn : 1 ≤ n) :
    ∀ i : {cu : Cube (Fin n ⊕ Fin n) // cu ∈ Ttc.toDNF (boxForm n hn)},
      Metric.ball (boxCentre n c) (c / 2)
        ⊆ region (fun a => (boxAtoms n c a).halfspace) i.val := by
  intro i
  rw [region_eq_bxOf n c hn i.property]
  exact ball_subset_box n c

/-- The box's lattice points at precision `ρ` are finite. -/
theorem latFiniteOf (n : ℕ) (c : ℝ) (ρ : ℤ) :
    (bxOf n c ∩ fineLattice n (latticeScale ρ)).Finite :=
  box_lattice_finite n c (latticeScale_pos ρ)

/-- …and nonempty: the origin is one. -/
theorem latNonemptyOf (n : ℕ) {c : ℝ} (hc : 0 ≤ c) (ρ : ℤ) :
    (bxOf n c ∩ fineLattice n (latticeScale ρ)).Nonempty :=
  box_lattice_nonempty n hc _

theorem ncard_lat_pos (n : ℕ) {c : ℝ} (hc : 0 ≤ c) (ρ : ℤ) :
    0 < (bxOf n c ∩ fineLattice n (latticeScale ρ)).ncard :=
  (Set.ncard_pos (latFiniteOf n c ρ)).2 (latNonemptyOf n hc ρ)

/-- The paper's `N = |Sol(F) ∩ 𝕃ⁿ|`, for the box. -/
theorem latticeCount_eq_ncard (n : ℕ) (c : ℝ) (hn : 1 ≤ n) (ρ : ℤ) :
    latticeCount (fun a => (boxAtoms n c a).halfspace) (boxForm n hn) ρ
      = (bxOf n c ∩ fineLattice n (latticeScale ρ)).ncard := by
  rw [latticeCount, sol_eq_bxOf n c hn]

theorem latticeCount_pos_bxOf (n : ℕ) {c : ℝ} (hc : 0 ≤ c) (hn : 1 ≤ n) (ρ : ℤ) :
    0 < latticeCount (fun a => (boxAtoms n c a).halfspace) (boxForm n hn) ρ := by
  rw [latticeCount_eq_ncard n c hn ρ]
  exact ncard_lat_pos n hc ρ

theorem volume_bxOf_ne_top (n : ℕ) (c : ℝ) : volume (bxOf n c) ≠ ⊤ := volume_box_ne_top n c

/-- The box has positive volume: it contains a ball of radius `c/2`. -/
theorem volume_bxOf_pos (n : ℕ) {c : ℝ} (hc : 0 < c) : 0 < (volume (bxOf n c)).toReal := by
  have hbpos : 0 < volume (Metric.ball (boxCentre n c) (c / 2)) :=
    Metric.measure_ball_pos _ _ (by positivity)
  have hle : volume (Metric.ball (boxCentre n c) (c / 2)) ≤ volume (bxOf n c) :=
    measure_mono (ball_subset_box n c)
  exact ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le hbpos hle)) (volume_bxOf_ne_top n c)

/-! ## Part 2.  The Kannan–Vempala sampler, at a general side and precision

A copy of `Ttc/Witness/BoxProb.lean`'s construction with `Ttc.Box.side` and
`Ttc.Box.rho` replaced by parameters, and the tuned constant `ε' = 1/12` replaced
by the hypothesis `ε' ≤ 1/12` (which `ε' = ε/12` satisfies for every `ε ≤ 1`).
`Ttc.Box.bxNormal`, `Ttc.Box.bfac` and their lemmas already carry no accuracy
parameter, so they are reused unchanged.
-/

/-- The offsets of the dilated box `10^ρ·[0,c]ⁿ`: `x k ≤ 10^ρ·c` and `−x k ≤ 0`. -/
noncomputable def bxOffsetOf (n : ℕ) (c : ℝ) (ρ : ℤ) : (Fin n ⊕ Fin n) → ℝ
  | .inl _ => latticeScale ρ * c
  | .inr _ => 0

/-- **The dilate of the box is the box of side `10^ρ·c`.** -/
theorem smul_bxOf (n : ℕ) (c : ℝ) (ρ : ℤ) :
    latticeScale ρ • bxOf n c = bxOf n (latticeScale ρ * c) := by
  have hc : 0 < latticeScale ρ := latticeScale_pos _
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ k
    have happ : (latticeScale ρ • y) k = latticeScale ρ * y k := rfl
    rw [happ]
    exact ⟨mul_nonneg hc.le (hy k).1, by nlinarith [(hy k).2]⟩
  · intro hx
    refine ⟨(latticeScale ρ)⁻¹ • x, fun k => ?_, ?_⟩
    · have happ : ((latticeScale ρ)⁻¹ • x) k = (latticeScale ρ)⁻¹ * x k := rfl
      rw [happ]
      refine ⟨mul_nonneg (by positivity) (hx k).1, ?_⟩
      calc (latticeScale ρ)⁻¹ * x k
          ≤ (latticeScale ρ)⁻¹ * (latticeScale ρ * c) := by
            have := (hx k).2
            have hinv : (0:ℝ) < (latticeScale ρ)⁻¹ := by positivity
            nlinarith
        _ = c := by field_simp
    · show latticeScale ρ • (latticeScale ρ)⁻¹ • x = x
      rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]

/-- **`dilate_eq` at a general side**: the linear system `±x k ≤ (10^ρ·c, 0)` cuts
out the dilated box. -/
theorem bxBodyOf_eq (n : ℕ) (c : ℝ) (ρ : ℤ) :
    Arlib.Polytope.body (bxNormal n) (bxOffsetOf n c ρ) = bxOf n (latticeScale ρ * c) := by
  ext x
  simp only [Arlib.Polytope.body, Set.mem_setOf_eq, bxOf, inner_bxNormal]
  constructor
  · intro h k
    have h1 := h (Sum.inl k)
    have h2 := h (Sum.inr k)
    simp only [boxAtoms_inl_coeff, boxAtoms_inr_coeff, bxOffsetOf, sum_single_mul] at h1 h2
    constructor <;> linarith
  · rintro h (k | k) <;>
      simp only [boxAtoms_inl_coeff, boxAtoms_inr_coeff, bxOffsetOf, sum_single_mul]
    · linarith [(h k).2]
    · linarith [(h k).1]

/-- **`c = √(2 log(4/ε')) ≥ 1` for every `ε' ≤ 1/12`.**  `Ttc.Box.one_le_cOf_epsPrime`
without the pin to `ε' = 1/12`; it is the fact that makes the inflation wider than
the rounding radius, hence the rejection step lossless. -/
theorem one_le_cOf_of_le {ep : ℝ} (hep0 : 0 < ep) (hep : ep ≤ 1 / 12) :
    1 ≤ Arlib.KV97.cOf ep := by
  have h48 : (48 : ℝ) ≤ 4 / ep := by
    rw [le_div_iff₀ hep0]; linarith
  have hexp : Real.exp (1 / 2 : ℝ) ≤ 48 := by
    have h1 : Real.exp (1 / 2 : ℝ) ≤ Real.exp 1 := Real.exp_le_exp.2 (by norm_num)
    have h2 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  have hlog48 : (1 / 2 : ℝ) ≤ Real.log 48 := (Real.le_log_iff_exp_le (by norm_num)).2 hexp
  have hmono : Real.log 48 ≤ Real.log (4 / ep) := Real.log_le_log (by norm_num) h48
  rw [Arlib.KV97.cOf, Real.one_le_sqrt]
  linarith

/-- **The facet displacement exceeds the rounding radius**, `κ ≥ 1`. -/
theorem one_le_kappaOf {ep : ℝ} (hep0 : 0 < ep) (hep : ep ≤ 1 / 12) (n : ℕ) :
    1 ≤ Arlib.KV97.kappaOf (Arlib.KV97.cOf ep) (bfac n) := by
  have h1 := one_le_cOf_of_le hep0 hep
  have h2 : (0 : ℝ) ≤ Real.sqrt (2 * Real.log (bfac n)) := Real.sqrt_nonneg _
  rw [Arlib.KV97.kappaOf]
  linarith

/-- The inflated dilated box `P'`, the body the continuous sampler draws from. -/
noncomputable def bxInflatedOf (n : ℕ) (c : ℝ) (ρ : ℤ) (ep : ℝ) : Set (Space n) :=
  Arlib.KV97.inflated (bxNormal n) (bxOffsetOf n c ρ) (Arlib.KV97.cOf ep) (bfac n)

/-- **The rounding kernel of a point of the dilated box stays inside `P'`.** -/
theorem roundBox_subset_bxInflatedOf (n : ℕ) (c : ℝ) (ρ : ℤ) {ep : ℝ}
    (hep0 : 0 < ep) (hep : ep ≤ 1 / 12) {z : Space n}
    (hz : z ∈ bxOf n (latticeScale ρ * c)) :
    Arlib.Lattice.Rounding.roundBox z ⊆ bxInflatedOf n c ρ ep := by
  intro p hp
  have hk := one_le_kappaOf hep0 hep n
  refine Arlib.KV97.mem_inflated.2 fun j => ?_
  rw [inner_bxNormal, norm_bxNormal, mul_one]
  cases j with
  | inl k =>
      have habs := abs_le.1 (hp k : |p k - z k| ≤ 1)
      have hzk := (hz k).2
      simp only [boxAtoms_inl_coeff, bxOffsetOf, sum_single_mul]
      linarith [habs.2]
  | inr k =>
      have habs := abs_le.1 (hp k : |p k - z k| ≤ 1)
      have hzk := (hz k).1
      simp only [boxAtoms_inr_coeff, bxOffsetOf, sum_single_mul]
      linarith [habs.1]

/-- **The rejection step is lossless.**  The whole rounding kernel of a point of
the dilated box lies in `P'`, so its unnormalised weight is exactly `1`. -/
theorem setIntegral_prodTent_bxInflatedOf (n : ℕ) (c : ℝ) (ρ : ℤ) {ep : ℝ}
    (hep0 : 0 < ep) (hep : ep ≤ 1 / 12) {z : Space n}
    (hz : z ∈ bxOf n (latticeScale ρ * c)) :
    ∫ p in bxInflatedOf n c ρ ep, Arlib.Lattice.Rounding.prodTent z p = 1 := by
  have hmeas : MeasurableSet (bxInflatedOf n c ρ ep) :=
    Arlib.KV97.measurableSet_inflated _ _ _ _
  have hzero : Set.EqOn (Arlib.Lattice.Rounding.prodTent z) (fun _ => (0 : ℝ))
      (bxInflatedOf n c ρ ep)ᶜ := fun p hp =>
    Arlib.Lattice.Rounding.prodTent_eq_zero_of_notMem
      fun hbox => hp (roundBox_subset_bxInflatedOf n c ρ hep0 hep hz hbox)
  have h0 : ∫ p in (bxInflatedOf n c ρ ep)ᶜ, Arlib.Lattice.Rounding.prodTent z p = 0 := by
    rw [MeasureTheory.setIntegral_congr_fun hmeas.compl hzero]
    simp
  rw [Arlib.Lattice.Rounding.setIntegral_prodTent_compl z hmeas, h0, sub_zero]

theorem dbx_sideOf_pos {c : ℝ} (hc : 0 < c) (ρ : ℤ) : 0 < latticeScale ρ * c :=
  mul_pos (latticeScale_pos _) hc

/-- The dilated box contains an `ℓ₂`-ball of radius `10^ρ·c/2`. -/
theorem ball_subset_dbxOf (n : ℕ) (c : ℝ) (ρ : ℤ) :
    Metric.ball (boxCentre n (latticeScale ρ * c)) ((latticeScale ρ * c) / 2)
      ⊆ Arlib.Polytope.body (bxNormal n) (bxOffsetOf n c ρ) := by
  rw [bxBodyOf_eq]
  exact ball_subset_box n _

theorem volume_bxInflatedOf_ne_zero (n : ℕ) {c : ℝ} (hc : 0 < c) (ρ : ℤ) (ep : ℝ) :
    volume (bxInflatedOf n c ρ ep) ≠ 0 :=
  Arlib.KV97.volume_inflated_ne_zero (half_pos (dbx_sideOf_pos hc ρ)) Arlib.KV97.cOf_nonneg
    (ball_subset_dbxOf n c ρ)

theorem volume_bxInflatedOf_ne_top (n : ℕ) {c : ℝ} (hc : 0 < c) (ρ : ℤ) (ep : ℝ) :
    volume (bxInflatedOf n c ρ ep) ≠ ⊤ :=
  Arlib.KV97.volume_inflated_ne_top (half_pos (dbx_sideOf_pos hc ρ)) Arlib.KV97.cOf_nonneg
    (ball_subset_dbxOf n c ρ) (by rw [bxBodyOf_eq]; exact volume_bxOf_ne_top n _)

theorem volume_bxInflatedOf_toReal_pos (n : ℕ) {c : ℝ} (hc : 0 < c) (ρ : ℤ) (ep : ℝ) :
    0 < (volume (bxInflatedOf n c ρ ep)).toReal :=
  ENNReal.toReal_pos (volume_bxInflatedOf_ne_zero n hc ρ ep)
    (volume_bxInflatedOf_ne_top n hc ρ ep)

theorem bxLawOf_isProb (n : ℕ) {c : ℝ} (hc : 0 < c) (ρ : ℤ) (ep : ℝ) :
    IsProbabilityMeasure (Arlib.uniformOn volume (bxInflatedOf n c ρ ep)) :=
  Arlib.isProbabilityMeasure_uniformOn _ (volume_bxInflatedOf_ne_zero n hc ρ ep)
    (volume_bxInflatedOf_ne_top n hc ρ ep)

/-- **Every enumerated point's unnormalised weight is exactly `1/Vol(P')`.** -/
theorem integral_prodTent_bxUniformOf (n : ℕ) (c : ℝ) (ρ : ℤ) {ep : ℝ}
    (hep0 : 0 < ep) (hep : ep ≤ 1 / 12) {z : Space n}
    (hz : z ∈ bxOf n (latticeScale ρ * c)) :
    ∫ p, Arlib.Lattice.Rounding.prodTent z p
        ∂(Arlib.uniformOn volume (bxInflatedOf n c ρ ep))
      = (volume (bxInflatedOf n c ρ ep)).toReal⁻¹ := by
  rw [Arlib.integral_uniformOn_real, setIntegral_prodTent_bxInflatedOf n c ρ hep0 hep hz,
    mul_one]

/-- **The dilated box has finitely many integer points.** -/
theorem dilFiniteOf (n : ℕ) (c : ℝ) (ρ : ℤ) :
    ((latticeScale ρ • bxOf n c) ∩ intLattice n : Set (Space n)).Finite := by
  have h : (latticeScale ρ • bxOf n c ∩ intLattice n : Set (Space n))
      = (fun x => latticeScale ρ • x) '' (bxOf n c ∩ fineLattice n (latticeScale ρ)) :=
    (Arlib.Lattice.image_smul_inter_fineLattice (latticeScale_pos _) (bxOf n c)).symm
  rw [h]
  exact (latFiniteOf n c ρ).image _

/-- **The sampler's output law**: exactly uniform on each cube's lattice points. -/
noncomputable def smpOf (n : ℕ) (c : ℝ) (ρ : ℤ) : Cube (Fin n ⊕ Fin n) → Space n → ℝ :=
  fun i _ => 1 / ((region (fun a => (boxAtoms n c a).halfspace) i
    ∩ fineLattice n (latticeScale ρ)).ncard : ℝ)

/-- **The Kannan–Vempala sampler for the box, at a general side and precision.**

`Ttc/Witness/BoxProb.lean`'s `sampler` field, with `Ttc.Box.side`/`Ttc.Box.rho`
replaced by parameters and `ε' = 1/12` replaced by `ε' ≤ 1/12`.  The
total-variation field holds at distance `0`, because the continuous draw *is* the
uniform law on `P'`; `sampD_eq` is exact because
`Ttc.Box.setIntegral_prodTent_bxInflatedOf` gives every enumerated point the same
weight. -/
noncomputable def samplerOf (n : ℕ) (hn : 1 ≤ n) {c : ℝ} (hc : 0 < c) (ρ : ℤ) {ep : ℝ}
    (hep0 : 0 < ep) (hep : ep ≤ 1 / 12) :
    KV97Sampler (Fin n ⊕ Fin n) n (fun a => (boxAtoms n c a).halfspace)
      (Ttc.toDNF (boxForm n hn)) ρ ep (smpOf n c ρ) where
  J := Fin n ⊕ Fin n
  Amat := fun _ => bxNormal n
  bvec := fun _ => bxOffsetOf n c ρ
  dilate_eq := fun i => by
    have h : latticeScale ρ • region (fun a => (boxAtoms n c a).halfspace) i.val
        = Arlib.Polytope.body (bxNormal n) (bxOffsetOf n c ρ) := by
      rw [region_eq_bxOf n c hn i.property, smul_bxOf, bxBodyOf_eq]
    exact h.le
  facetBound := bfac n
  one_le_facetBound := one_le_bfac
  card_le_facetBound := card_le_bfac
  contLaw := fun _ => Arlib.uniformOn volume (bxInflatedOf n c ρ ep)
  isProbContLaw := fun _ => bxLawOf_isProb n hc ρ ep
  contVol := fun _ => (volume (bxInflatedOf n c ρ ep)).toReal
  contVol_pos := fun _ => volume_bxInflatedOf_toReal_pos n hc ρ ep
  contVol_eq := fun _ => rfl
  law_tv := fun _ => (Arlib.TVLe.refl _).mono (by simp)
  sampD_eq := by
    intro i x hx
    have hfin : ((latticeScale ρ • region (fun a => (boxAtoms n c a).halfspace) i.val)
        ∩ intLattice n : Set (Space n)).Finite := by
      rw [region_eq_bxOf n c hn i.property]
      exact dilFiniteOf n c ρ
    letI : Fintype ((latticeScale ρ • region (fun a => (boxAtoms n c a).halfspace) i.val)
        ∩ intLattice n : Set (Space n)) := hfin.fintype
    have hVne : (volume (bxInflatedOf n c ρ ep)).toReal⁻¹ ≠ 0 :=
      inv_ne_zero (volume_bxInflatedOf_toReal_pos n hc ρ ep).ne'
    have hdb : ∀ z ∈ latticeScale ρ • region (fun a => (boxAtoms n c a).halfspace) i.val,
        (∫ p, Arlib.Lattice.Rounding.prodTent z p
            ∂(Arlib.uniformOn volume (bxInflatedOf n c ρ ep)))
          = (volume (bxInflatedOf n c ρ ep)).toReal⁻¹ := by
      intro z hz
      have hz' : z ∈ bxOf n (latticeScale ρ * c) := by
        rw [← smul_bxOf, ← region_eq_bxOf n c hn i.property]; exact hz
      exact integral_prodTent_bxUniformOf n c ρ hep0 hep hz'
    have hxmem : latticeScale ρ • x
        ∈ latticeScale ρ • region (fun a => (boxAtoms n c a).halfspace) i.val :=
      ⟨x, hx.1, rfl⟩
    have hsum : ∀ k : ((latticeScale ρ • region (fun a => (boxAtoms n c a).halfspace) i.val)
        ∩ intLattice n : Set (Space n)),
        (∫ p, Arlib.Lattice.Rounding.prodTent (k : Space n) p
            ∂(Arlib.uniformOn volume (bxInflatedOf n c ρ ep)))
          = (volume (bxInflatedOf n c ρ ep)).toReal⁻¹ :=
      fun k => hdb k.1 k.2.1
    rw [finsum_eq_sum_of_fintype, hdb _ hxmem,
      Finset.sum_congr rfl (fun k _ => hsum k)]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    rw [← Ttc.ncard_inter_fineLattice (latticeScale_pos _), mul_comm, ← div_div,
      div_self hVne]
    rfl

/-! ## Part 3.  The parameter block, at a general `(ε, δ)`

`Ttc.Box.par` stores `max 1 (…)` in `m` and `r`, so `Ttc.Box.par_eq_ttcParams` is
needed to identify it with the computed block.  Taking `Ttc.ttcParams` itself as
the parameter block makes `Ttc.ttc_volume`'s `hP` a `rfl` and removes that step.
-/

/-- **The computed parameter block of `TTC(boxForm, ε, δ)`.**  Literally
`Ttc.ttcParams` at the box's DNF, so `Ttc.ttc_volume`'s `hP` holds by `rfl`. -/
noncomputable def parS (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) : Params :=
  ttcParams (Ttc.toDNF (boxForm n hn)) n ε δ hε0 hε1 hn
    (one_le_card_cubes_box n hn) (one_le_card_facets_box n hn)

variable {n : ℕ} {ε δ : ℝ}

@[simp] theorem parS_eps (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (parS n hn ε δ hε0 hε1).ε = ε := rfl

@[simp] theorem parS_delta (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (parS n hn ε δ hε0 hε1).δ = δ := rfl

theorem parS_epsPrime (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (parS n hn ε δ hε0 hε1).epsPrime = ε / 12 := rfl

theorem parS_eta (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (parS n hn ε δ hε0 hε1).eta = ε / 8 := rfl

theorem parS_m (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (parS n hn ε δ hε0 hε1).m
      = Nat.card {cu : Cube (Fin n ⊕ Fin n) // cu ∈ Ttc.toDNF (boxForm n hn)} := rfl

theorem parS_r (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (parS n hn ε δ hε0 hε1).r
      = (Nat.card (FacetIndex (Ttc.toDNF (boxForm n hn))) : ℝ) := rfl

theorem parS_epsPrime_pos (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    0 < (parS n hn ε δ hε0 hε1).epsPrime := by
  rw [parS_epsPrime]; linarith

theorem parS_epsPrime_le (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (parS n hn ε δ hε0 hε1).epsPrime ≤ 1 / 12 := by
  rw [parS_epsPrime]; linarith

/-- **`Thresh > 0` at every `(ε, δ)` in range.**  The second branch of the `max` is
`15·(log(6/δ) + log m)`, and `δ ≤ 1` makes `log(6/δ) ≥ log 6 > 0`. -/
theorem parS_thresh_pos (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) : 0 < (parS n hn ε δ hε0 hε1).thresh := by
  refine lt_of_lt_of_le ?_ (le_max_right _ _)
  have hdiv : (1 : ℝ) < 6 / δ := (one_lt_div hδ0).2 (by linarith)
  have h6 : (0 : ℝ) < Real.log (6 / δ) := Real.log_pos hdiv
  have hm : (0 : ℝ) ≤ Real.log ((parS n hn ε δ hε0 hε1).m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (parS n hn ε δ hε0 hε1).hm)
  have hd : (parS n hn ε δ hε0 hε1).δ = δ := rfl
  rw [hd]
  linarith

/-- The box side at accuracy `ε` and confidence `δ`: at least `1`, and at least
`Thresh`, exactly as `Ttc.Box.side` chooses it at `ε = δ = 1`.  This is what makes
the instance grow as the accuracy parameters shrink. -/
noncomputable def sideS (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) : ℝ :=
  max 1 (parS n hn ε δ hε0 hε1).thresh

theorem one_le_sideS (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    1 ≤ sideS n hn ε δ hε0 hε1 := le_max_left _ _

theorem sideS_pos (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    0 < sideS n hn ε δ hε0 hε1 := lt_of_lt_of_le one_pos (one_le_sideS hn hε0 hε1)

theorem thresh_le_sideS (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (parS n hn ε δ hε0 hε1).thresh ≤ sideS n hn ε δ hε0 hε1 := le_max_right _ _

/-- `γ̂`, the inscribed radius: half the side. -/
noncomputable def gamS (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) : ℝ :=
  sideS n hn ε δ hε0 hε1 / 2

theorem gamS_pos (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    0 < gamS n hn ε δ hε0 hε1 := half_pos (sideS_pos hn hε0 hε1)

/-- The precision `GetPrecision` returns for this `γ̂`. -/
noncomputable def rhoS (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) : ℤ :=
  (parS n hn ε δ hε0 hε1).precision (gamS n hn ε δ hε0 hε1)

/-- The normalised lattice count of the instance. -/
noncomputable def LvalS (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) : ℝ :=
  normalisedCount (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
    (boxForm n hn) (rhoS n hn ε δ hε0 hε1)

/-- **The instance is big enough**: `Thresh ≤ c ≤ cⁿ ≤ L`. -/
theorem sideS_le_LvalS (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    sideS n hn ε δ hε0 hε1 ≤ LvalS n hn ε δ hε0 hε1 := by
  refine le_trans ?_ (normalisedCount_box_ge n (sideS_pos hn hε0 hε1) hn (rhoS n hn ε δ hε0 hε1))
  calc sideS n hn ε δ hε0 hε1 = sideS n hn ε δ hε0 hε1 ^ 1 := (pow_one _).symm
    _ ≤ sideS n hn ε δ hε0 hε1 ^ n := pow_le_pow_right₀ (one_le_sideS hn hε0 hε1) hn

/-- **`lem:lattice` for the sharp witness, lower half.**  `Ttc.lattice_of_dnf` at the
box's own DNF, which bounds the total rate `∑θ = Vol(box)` from below by
`(1 − η)·L`.  Nothing new is assumed. -/
theorem lattice_lo_bxS (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (1 - (parS n hn ε δ hε0 hε1).eta) * LvalS n hn ε δ hε0 hε1
      ≤ (volume (bxOf n (sideS n hn ε δ hε0 hε1))).toReal := by
  have hb : ∀ i : {cu : Cube (Fin n ⊕ Fin n) // cu ∈ boxDNF n}, i.val = boxCube n :=
    fun i => by simpa [boxDNF] using i.property
  have hmle : (Nat.card {cu : Cube (Fin n ⊕ Fin n) // cu ∈ boxDNF n} : ℝ)
      ≤ ((parS n hn ε δ hε0 hε1).m : ℝ) := by
    have h : (parS n hn ε δ hε0 hε1).m
        = Nat.card {cu : Cube (Fin n ⊕ Fin n) // cu ∈ boxDNF n} := by
      rw [parS_m, toDNF_boxForm hn]
    rw [h]
  have hrle : (Nat.card (FacetIndex (boxDNF n)) : ℝ) ≤ (parS n hn ε δ hε0 hε1).r := by
    have h : (parS n hn ε δ hε0 hε1).r = (Nat.card (FacetIndex (boxDNF n)) : ℝ) := by
      rw [parS_r, toDNF_boxForm hn]
    rw [h]
  have h := lattice_of_dnf (boxAtoms n (sideS n hn ε δ hε0 hε1)) (boxDNF_isDNFOf hn)
    boxDNF_isPositive (parS n hn ε δ hε0 hε1) rfl hmle hrle
    (boxAtoms_normal_ne_zero n (sideS n hn ε δ hε0 hε1))
    (fun _ => boxCentre n (sideS n hn ε δ hε0 hε1)) (gamS_pos hn hε0 hε1)
    (fun i => by
      rw [hb i]
      exact ball_subset_region_boxCube n (sideS n hn ε δ hε0 hε1))
    (fun i => by
      rw [hb i]
      exact volume_region_boxCube_ne_top n (sideS n hn ε δ hε0 hε1))
    (rfl : rhoS n hn ε δ hε0 hε1
      = (parS n hn ε δ hε0 hε1).precision (gamS n hn ε δ hε0 hε1))
  have hlo := h.1.1
  rwa [volSol, sol_eq_bxOf n (sideS n hn ε δ hε0 hε1) hn] at hlo

/-- **The binding hypothesis `big`, met at every `(ε, δ)`.**

`Thresh` grows as `ε` and `δ` shrink; the side is `max 1 Thresh`, so the box grows
with it, and `Vol(box) ≥ (1 − η)·L ≥ (7/8)·Thresh` against a requirement of at most
`Thresh/8`.  This is the inequality that was expected to bind, and it does not:
there is a factor of `7` in hand, uniformly in `(ε, δ)`. -/
theorem epsPrime_thresh_le_volumeS (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (1 - (parS n hn ε δ hε0 hε1).epsPrime) * (parS n hn ε δ hε0 hε1).thresh / 8
      ≤ (volume (bxOf n (sideS n hn ε δ hε0 hε1))).toReal := by
  have hlat := lattice_lo_bxS (δ := δ) hn hε0 hε1
  have hs := sideS_le_LvalS (δ := δ) hn hε0 hε1
  have hts := thresh_le_sideS (δ := δ) hn hε0 hε1
  have hT := parS_thresh_pos hn hε0 hε1 hδ0 hδ1
  rw [parS_eta] at hlat
  rw [parS_epsPrime]
  nlinarith [hlat, hs, hts, hT, hε0, hε1]

/-! ## Part 4.  The remaining hypotheses of `Ttc.ttc_volume`, at a general `(ε, δ)` -/

/-- The exact volume oracle: `Vol_ED` returns the truth. -/
noncomputable def vlOf (n : ℕ) (c : ℝ) : Cube (Fin n ⊕ Fin n) → ℝ :=
  fun _ => (volume (bxOf n c)).toReal

/-- The level-`0` rate at the canonical enumeration: the sampler's uniform mass
times the exact volume. -/
noncomputable def thOf (n : ℕ) (c : ℝ) (hn : 1 ≤ n) (ρ : ℤ) :
    Fin (latticeCount (fun a => (boxAtoms n c a).halfspace) (boxForm n hn) ρ) → ℝ :=
  fun _ => 1 / ((bxOf n c ∩ fineLattice n (latticeScale ρ)).ncard : ℝ)
    * (volume (bxOf n c)).toReal

/-- **The rates sum to the volume.**  Every point carries `Vol(box)/N` and there
are `N` of them. -/
theorem sum_thOf (n : ℕ) {c : ℝ} (hc : 0 < c) (hn : 1 ≤ n) (ρ : ℤ) :
    ∑ s, thOf n c hn ρ s = (volume (bxOf n c)).toReal := by
  have hN : ((bxOf n c ∩ fineLattice n (latticeScale ρ)).ncard : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (ncard_lat_pos n hc.le ρ).ne'
  simp only [thOf, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    latticeCount_eq_ncard n c hn ρ]
  field_simp

theorem hasLatticeEnum_bxOf (n : ℕ) (c : ℝ) (hn : 1 ≤ n) (ρ : ℤ) :
    HasLatticeEnum (fun a => (boxAtoms n c a).halfspace) (boxForm n hn) ρ :=
  hasLatticeEnum_of_isBounded _ _ _ (isBounded_sol_bxOf n c hn)

/-- The canonical enumeration lands in the box, at every index. -/
theorem latticeEnum_mem_bxOf (n : ℕ) (c : ℝ) (hn : 1 ≤ n) (ρ : ℤ)
    (s : Fin (latticeCount (fun a => (boxAtoms n c a).halfspace) (boxForm n hn) ρ)) :
    latticeEnum (fun a => (boxAtoms n c a).halfspace) (boxForm n hn) ρ s ∈ bxOf n c := by
  have h := (latticeEnum_mem (hasLatticeEnum_bxOf n c hn ρ) s).1
  rwa [sol_eq_bxOf n c hn] at h

/-- **`Ttc.ttc_volume`'s `theta_eq`, at a general side** — the box's sampler mass
is constant in the point, so nothing depends on which enumeration is used. -/
theorem theta_eq_bxOf (n : ℕ) (c : ℝ) (hn : 1 ≤ n) (ρ : ℤ)
    (s : Fin (latticeCount (fun a => (boxAtoms n c a).halfspace) (boxForm n hn) ρ)) :
    ∃ i, i ∈ Ttc.toDNF (boxForm n hn) ∧
      latticeEnum (fun a => (boxAtoms n c a).halfspace) (boxForm n hn) ρ s
        ∈ region (fun a => (boxAtoms n c a).halfspace) i ∧
      thOf n c hn ρ s = smpOf n c ρ i
        (latticeEnum (fun a => (boxAtoms n c a).halfspace) (boxForm n hn) ρ s)
        * vlOf n c i := by
  have hmem : boxCube n ∈ Ttc.toDNF (boxForm n hn) := by
    rw [toDNF_boxForm hn]; exact List.mem_singleton_self _
  refine ⟨boxCube n, hmem, ?_, ?_⟩
  · rw [region_eq_bxOf n c hn hmem]
    exact latticeEnum_mem_bxOf n c hn ρ s
  · simp only [thOf, smpOf, vlOf, region_eq_bxOf n c hn hmem]

/-- **`Ttc.ttc_volume`'s `gen_mem`, at a general side.** -/
theorem gen_mem_bxOf (n : ℕ) {c : ℝ} (hc : 0 ≤ c) (hn : 1 ≤ n) (ρ : ℤ)
    (t : ℕ → Fin (latticeCount (fun a => (boxAtoms n c a).halfspace) (boxForm n hn) ρ) → ℕ)
    (i : Cube (Fin n ⊕ Fin n)) (j N : ℕ) (hi : i ∈ Ttc.toDNF (boxForm n hn)) :
    ∀ s ∈ (coveredOracles (fun a => (boxAtoms n c a).halfspace) (boxForm n hn) ρ
        (vlOf n c) t).gen i j N ρ,
      s ∈ region (fun a => (boxAtoms n c a).halfspace) i
        ∩ fineLattice n (latticeScale ρ) := by
  have hmem : ∀ (cu : Cube (Fin n ⊕ Fin n))
      (s : Fin (latticeCount (fun a => (boxAtoms n c a).halfspace) (boxForm n hn) ρ)),
      memPtOfRegion (fun a => (boxAtoms n c a).halfspace)
          (latticeEnum (fun a => (boxAtoms n c a).halfspace) (boxForm n hn) ρ) cu s = true →
      latticeEnum (fun a => (boxAtoms n c a).halfspace) (boxForm n hn) ρ s
        ∈ bxOf n c ∩ fineLattice n (latticeScale ρ) :=
    fun _ s _ => ⟨latticeEnum_mem_bxOf n c hn ρ s,
      (latticeEnum_mem (hasLatticeEnum_bxOf n c hn ρ) s).2⟩
  have hne : ∃ s, memPtOfRegion (fun a => (boxAtoms n c a).halfspace)
      (latticeEnum (fun a => (boxAtoms n c a).halfspace) (boxForm n hn) ρ) i s = true :=
    ⟨⟨0, latticeCount_pos_bxOf n hc hn ρ⟩,
      (memPtOfRegion_eq_true _ _ _ _).2
        (by rw [region_eq_bxOf n c hn hi]; exact latticeEnum_mem_bxOf n c hn ρ _)⟩
  intro x hx
  rw [region_eq_bxOf n c hn hi]
  exact gen_mem_trajOracles
    (T := fun _ => bxOf n c ∩ fineLattice n (latticeScale ρ))
    (latticeEnum_injective _ _ _) t hmem hne j N ρ x hx

/-! ## Part 5.  The witness

`Ttc.ttc_volume` applied to the data above, at an arbitrary `(ε, δ) ∈ (0,1]²`.
-/

/-- **`Ttc.ttc_volume` is instantiable at every `(ε, δ) ∈ (0,1]²`.**

The box `[0,c]ⁿ` with `c = max 1 Thresh(ε, δ)`, its one-cube DNF, the exact volume
oracle, and the Kannan–Vempala sampler of `Ttc.Box.samplerOf`.  The proof is the
40-argument application of `Ttc.ttc_volume`, unweakened; the conclusion is recorded
so a reader can see *which* instance was checked.

Unlike `Ttc.Box.ttc_volume_box`, this is **not** vacuous whenever `δ < 1`: the
accuracy half then asserts a genuine lower bound `1 − δ > 0` on a probability. -/
theorem ttc_volume_box_at (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (1 - δ ≤ (trajLaw (thOf n (sideS n hn ε δ hε0 hε1) hn (rhoS n hn ε δ hε0 hε1))
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
  exact ttc_volume (boxAtoms n (sideS n hn ε δ hε0 hε1)) (boxForm n hn) ε δ
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
    (thOf n (sideS n hn ε δ hε0 hε1) hn (rhoS n hn ε δ hε0 hε1))
    (smpOf n (sideS n hn ε δ hε0 hε1) (rhoS n hn ε δ hε0 hε1))
    (samplerOf n hn hcpos (rhoS n hn ε δ hε0 hε1) (parS_epsPrime_pos (δ := δ) hn hε0 hε1)
      (parS_epsPrime_le (δ := δ) hn hε0 hε1))
    (theta_eq_bxOf n (sideS n hn ε δ hε0 hε1) hn (rhoS n hn ε δ hε0 hε1))
    (fun t i j N hi => gen_mem_bxOf n hcpos.le hn (rhoS n hn ε δ hε0 hε1) t i j N hi)
    ((epsPrime_thresh_le_volumeS hn hε0 hε1 hδ0 hδ1).trans
      (sum_thOf n hcpos hn (rhoS n hn ε δ hε0 hε1)).ge)

/-- **The sharp witness: `Ttc.ttc_volume` at `ε = 1/2` and `δ = 1/2`.**

The accuracy half now reads `1/2 ≤ (trajLaw …).toReal` — a genuine lower bound on a
probability, not the `0 ≤ …` of `Ttc.Box.ttc_volume_box`.  Together with that
theorem it shows `ε` and `δ` are free parameters of the hypothesis bundle, not
values the bundle forces; see `Ttc.Box.exists_two_ttc_volume_instances`. -/
theorem ttc_volume_box_sharp (n : ℕ) (hn : 1 ≤ n) :
    ((1 : ℝ) - 1 / 2 ≤ (trajLaw
        (thOf n (sideS n hn (1/2) (1/2) (by norm_num) (by norm_num)) hn
          (rhoS n hn (1/2) (1/2) (by norm_num) (by norm_num)))
        {t : ℕ → Fin (latticeCount
            (fun a => (boxAtoms n (sideS n hn (1/2) (1/2) (by norm_num) (by norm_num))
              a).halfspace)
            (boxForm n hn) (rhoS n hn (1/2) (1/2) (by norm_num) (by norm_num))) → ℕ |
          ttcOutput (parS n hn (1/2) (1/2) (by norm_num) (by norm_num))
              (coveredOracles
                (fun a => (boxAtoms n (sideS n hn (1/2) (1/2) (by norm_num) (by norm_num))
                  a).halfspace)
                (boxForm n hn) (rhoS n hn (1/2) (1/2) (by norm_num) (by norm_num))
                (vlOf n (sideS n hn (1/2) (1/2) (by norm_num) (by norm_num))))
              Ttc.toDNF (rhoS n hn (1/2) (1/2) (by norm_num) (by norm_num)) (boxForm n hn) t
            ∈ relErr (1/2) (volSol
                (fun a => (boxAtoms n (sideS n hn (1/2) (1/2) (by norm_num) (by norm_num))
                  a).halfspace)
                (boxForm n hn))}).toReal)
    ∧
    (∀ (t : ℕ → Fin (latticeCount
        (fun a => (boxAtoms n (sideS n hn (1/2) (1/2) (by norm_num) (by norm_num))
          a).halfspace)
        (boxForm n hn) (rhoS n hn (1/2) (1/2) (by norm_num) (by norm_num))) → ℕ)
        (cVol cSample thr : ℕ),
      (thr : ℝ) = (parS n hn (1/2) (1/2) (by norm_num) (by norm_num)).thresh →
      Terminates (parS n hn (1/2) (1/2) (by norm_num) (by norm_num))
          (coveredOracles
            (fun a => (boxAtoms n (sideS n hn (1/2) (1/2) (by norm_num) (by norm_num))
              a).halfspace)
            (boxForm n hn) (rhoS n hn (1/2) (1/2) (by norm_num) (by norm_num))
            (vlOf n (sideS n hn (1/2) (1/2) (by norm_num) (by norm_num))) t)
          (Ttc.toDNF (boxForm n hn)) →
      runCost (parS n hn (1/2) (1/2) (by norm_num) (by norm_num))
          (coveredOracles
            (fun a => (boxAtoms n (sideS n hn (1/2) (1/2) (by norm_num) (by norm_num))
              a).halfspace)
            (boxForm n hn) (rhoS n hn (1/2) (1/2) (by norm_num) (by norm_num))
            (vlOf n (sideS n hn (1/2) (1/2) (by norm_num) (by norm_num))) t)
          cVol cSample (rhoS n hn (1/2) (1/2) (by norm_num) (by norm_num))
          (Ttc.toDNF (boxForm n hn))
        ≤ (Ttc.toDNF (boxForm n hn)).length * (cVol + cSample * thr)) :=
  ttc_volume_box_at n hn (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ## Part 6.  The pair

The deliverable is not either witness but their *difference*.  `Ttc.Box.AtParams`
packages `Ttc.ttc_volume`'s conclusion — both halves — over the data it is stated
about, with the accuracy parameters exposed.  It asserts nothing that is not proved
below at every `(ε, δ) ∈ (0,1]²`.
-/

/-- **`Ttc.ttc_volume`'s conclusion, with `(ε, δ)` exposed.**

`Ttc.ttc_volume` returns a conjunction over data it constructs; to compare two
instances the data has to be existentially quantified and the accuracy parameters
left visible.

**The conclusion alone would be too weak a package**, so three of
`Ttc.ttc_volume`'s own hypotheses travel with it and rule out a degenerate
instance sneaking in: `P.ε = ε`, `P.δ = δ` and `P.n = n` pin the parameter block to
the stated accuracy, `hbdd` says the solution set is a bounded set, `vol_pos` says
every volume estimate is strictly positive, and `big` — the paper's regime
condition, which forces `∑ θ > 0` and hence a nonempty lattice — is the hypothesis
that killed the development's original empty-DNF witness.  Both instances below
supply all of them. -/
def AtParams (n : ℕ) (ε δ : ℝ) : Prop :=
  ∃ (atoms : (Fin n ⊕ Fin n) → LinAtom n) (φ : BForm (Fin n ⊕ Fin n)) (P : Params)
      (gammaHat : ℝ) (vol : Cube (Fin n ⊕ Fin n) → ℝ)
      (θ : Fin (latticeCount (fun a => (atoms a).halfspace) φ (P.precision gammaHat)) → ℝ),
    0 < ε ∧ ε ≤ 1 ∧ 0 < δ ∧ δ ≤ 1 ∧ P.ε = ε ∧ P.δ = δ ∧ P.n = n ∧
    Bornology.IsBounded (sol (fun a => (atoms a).halfspace) φ) ∧
    (∀ i ∈ Ttc.toDNF φ, 0 < vol i) ∧
    ((1 - P.epsPrime) * P.thresh / 8 ≤ ∑ s, θ s) ∧
    (1 - δ ≤ (trajLaw θ
        {t : ℕ → Fin (latticeCount (fun a => (atoms a).halfspace) φ
            (P.precision gammaHat)) → ℕ |
          ttcOutput P (coveredOracles (fun a => (atoms a).halfspace) φ
              (P.precision gammaHat) vol) Ttc.toDNF (P.precision gammaHat) φ t
            ∈ relErr ε (volSol (fun a => (atoms a).halfspace) φ)}).toReal)
    ∧
    (∀ (t : ℕ → Fin (latticeCount (fun a => (atoms a).halfspace) φ
        (P.precision gammaHat)) → ℕ) (cVol cSample thr : ℕ),
      (thr : ℝ) = P.thresh →
      Terminates P (coveredOracles (fun a => (atoms a).halfspace) φ
          (P.precision gammaHat) vol t) (Ttc.toDNF φ) →
      runCost P (coveredOracles (fun a => (atoms a).halfspace) φ
          (P.precision gammaHat) vol t) cVol cSample (P.precision gammaHat) (Ttc.toDNF φ)
        ≤ (Ttc.toDNF φ).length * (cVol + cSample * thr))

/-- **The capstone is instantiable at every accuracy pair in `(0,1]²`.** -/
theorem atParams_of (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) : AtParams n ε δ := by
  obtain ⟨hacc, hrun⟩ := ttc_volume_box_at n hn ε δ hε0 hε1 hδ0 hδ1
  have hcpos : 0 < sideS n hn ε δ hε0 hε1 := sideS_pos hn hε0 hε1
  exact ⟨boxAtoms n (sideS n hn ε δ hε0 hε1), boxForm n hn, parS n hn ε δ hε0 hε1,
    gamS n hn ε δ hε0 hε1, vlOf n (sideS n hn ε δ hε0 hε1),
    thOf n (sideS n hn ε δ hε0 hε1) hn (rhoS n hn ε δ hε0 hε1),
    hε0, hε1, hδ0, hδ1, rfl, rfl, rfl,
    isBounded_sol_bxOf n (sideS n hn ε δ hε0 hε1) hn,
    fun _ _ => volume_bxOf_pos n hcpos,
    (epsPrime_thresh_le_volumeS hn hε0 hε1 hδ0 hδ1).trans
      (sum_thOf n hcpos hn (rhoS n hn ε δ hε0 hε1)).ge,
    hacc, hrun⟩

/-- **The old witness, in the same shape.**  `Ttc.Box.ttc_volume_box` repackaged, so
that the two instances are literally comparable. -/
theorem atParams_one (n : ℕ) (hn : 1 ≤ n) : AtParams n 1 1 := by
  obtain ⟨hacc, hrun⟩ := ttc_volume_box n hn
  exact ⟨atm n hn, boxForm n hn, par n hn, gam n hn, vl n hn, thC n hn,
    one_pos, le_rfl, one_pos, le_rfl, rfl, rfl, rfl,
    isBounded_sol_box n hn, fun _ _ => volume_bx_pos hn,
    (epsPrime_thresh_le_volume hn).trans (sum_thC n hn).ge,
    hacc, hrun⟩

/-- **`ε` and `δ` are not forced.**

Two instances of `Ttc.ttc_volume`, at *different* accuracy parameters — `(1, 1)`,
which is `Ttc.Box.ttc_volume_box`, and `(1/2, 1/2)`, which is
`Ttc.Box.ttc_volume_box_sharp`.  Since the second lies strictly inside `(0,1)²`,
its accuracy conclusion `1 − δ₂ = 1/2 > 0` is a real bound on a probability,
whereas the first's is `1 − δ₁ = 0` and is satisfied by every measure
(`Ttc.Box.toReal_nonneg_any`).

This is the theorem the file exists for: a single witness cannot distinguish "the
36 hypotheses are satisfiable" from "the 36 hypotheses force `ε = δ = 1`", and the
pair does. -/
theorem exists_two_ttc_volume_instances (n : ℕ) (hn : 1 ≤ n) :
    ∃ ε₁ δ₁ ε₂ δ₂ : ℝ,
      AtParams n ε₁ δ₁ ∧ AtParams n ε₂ δ₂ ∧
      ε₁ ≠ ε₂ ∧ δ₁ ≠ δ₂ ∧
      (0 < ε₂ ∧ ε₂ < 1) ∧ (0 < δ₂ ∧ δ₂ < 1) ∧
      1 - δ₁ = 0 ∧ 0 < 1 - δ₂ :=
  ⟨1, 1, 1/2, 1/2, atParams_one n hn,
    atParams_of n hn (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    by norm_num, by norm_num, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    by norm_num, by norm_num⟩

/-- **The whole open square is available**, not just one interior point: for every
`(ε, δ)` with `0 < ε < 1` and `0 < δ < 1` there is an instance, and it is distinct
from the `(1, 1)` one in both parameters. -/
theorem exists_two_ttc_volume_instances_at (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    AtParams n 1 1 ∧ AtParams n ε δ ∧ (1 : ℝ) ≠ ε ∧ (1 : ℝ) ≠ δ ∧ 0 < 1 - δ :=
  ⟨atParams_one n hn, atParams_of n hn ε δ hε0 hε1.le hδ0 hδ1.le,
    fun h => absurd h.symm hε1.ne, fun h => absurd h.symm hδ1.ne, by linarith⟩

end Box

/-! ## Axiom profile

Every theorem of this file, checked as `CLAUDE.md` §4 requires. Expect
`[propext, Classical.choice, Quot.sound]` throughout. -/

#print axioms Box.toReal_nonneg_any
#print axioms Box.ttc_volume_box_accuracy_is_trivial
#print axioms Box.bxOf
#print axioms Box.sol_eq_bxOf
#print axioms Box.region_eq_bxOf
#print axioms Box.isBounded_sol_bxOf
#print axioms Box.coeff_ne_zero_bxOf
#print axioms Box.ball_subset_bxOf
#print axioms Box.latFiniteOf
#print axioms Box.latNonemptyOf
#print axioms Box.ncard_lat_pos
#print axioms Box.latticeCount_eq_ncard
#print axioms Box.latticeCount_pos_bxOf
#print axioms Box.volume_bxOf_ne_top
#print axioms Box.volume_bxOf_pos
#print axioms Box.bxOffsetOf
#print axioms Box.smul_bxOf
#print axioms Box.bxBodyOf_eq
#print axioms Box.one_le_cOf_of_le
#print axioms Box.one_le_kappaOf
#print axioms Box.bxInflatedOf
#print axioms Box.roundBox_subset_bxInflatedOf
#print axioms Box.setIntegral_prodTent_bxInflatedOf
#print axioms Box.dbx_sideOf_pos
#print axioms Box.ball_subset_dbxOf
#print axioms Box.volume_bxInflatedOf_ne_zero
#print axioms Box.volume_bxInflatedOf_ne_top
#print axioms Box.volume_bxInflatedOf_toReal_pos
#print axioms Box.bxLawOf_isProb
#print axioms Box.integral_prodTent_bxUniformOf
#print axioms Box.dilFiniteOf
#print axioms Box.smpOf
#print axioms Box.samplerOf
#print axioms Box.parS
#print axioms Box.parS_eps
#print axioms Box.parS_delta
#print axioms Box.parS_epsPrime
#print axioms Box.parS_eta
#print axioms Box.parS_m
#print axioms Box.parS_r
#print axioms Box.parS_epsPrime_pos
#print axioms Box.parS_epsPrime_le
#print axioms Box.parS_thresh_pos
#print axioms Box.sideS
#print axioms Box.one_le_sideS
#print axioms Box.sideS_pos
#print axioms Box.thresh_le_sideS
#print axioms Box.gamS
#print axioms Box.gamS_pos
#print axioms Box.rhoS
#print axioms Box.LvalS
#print axioms Box.sideS_le_LvalS
#print axioms Box.lattice_lo_bxS
#print axioms Box.epsPrime_thresh_le_volumeS
#print axioms Box.vlOf
#print axioms Box.thOf
#print axioms Box.sum_thOf
#print axioms Box.hasLatticeEnum_bxOf
#print axioms Box.latticeEnum_mem_bxOf
#print axioms Box.theta_eq_bxOf
#print axioms Box.gen_mem_bxOf
#print axioms Box.ttc_volume_box_at
#print axioms Box.ttc_volume_box_sharp
#print axioms Box.AtParams
#print axioms Box.atParams_of
#print axioms Box.atParams_one
#print axioms Box.exists_two_ttc_volume_instances
#print axioms Box.exists_two_ttc_volume_instances_at

end Ttc
