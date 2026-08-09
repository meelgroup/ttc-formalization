/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.Final

/-!
# `Exec/Regime`: `big` is **not** derivable — it is an independent regime condition

**Conclusion, stated up front.**  The binder

```lean
(big : ∀ c ∈ mcGood M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime,
    (1 - P.epsPrime) * P.thresh / 8
      ≤ ∑ s, rates M φ (toDNF φ) (P.precision gammaHat) (e2eSampD …) (mcVol … c) s)
```

carried by `Ttc.ttc_volume_final`, `Ttc.ttc_volume_stmt` and `Ttc.ttc_volume_estimate`
is **independent** of that theorem's other hypotheses.  This file proves it, by a
counterexample: `Ttc.Box.big_not_derivable` exhibits, for every
`(ε, δ) ∈ (0,1] × (0,1]` and every dimension `n ≥ 1`, a box `[0,a]ⁿ` that satisfies
every other hypothesis of `Ttc.ttc_volume_final` — the hypotheses are produced, one
per conjunct — and on which `big` fails.  So those hypotheses do not entail `big`.

`Ttc.Box.ttc_volume_final_at_box` is the guard against refuting a lookalike: it
applies `Ttc.ttc_volume_final` at that very instance with the refuted proposition,
written out verbatim, as its only hypothesis.  It elaborates, so the proposition
`Ttc.Box.big_not_derivable` refutes is the capstone's binder and not a paraphrase.

## What `big` actually says

`Ttc.rates M φ D ρ sampD vol s = sampD (cubeAt … s) (latticeEnum … s) * vol (cubeAt … s)`,
summed over **all** `latticeCount M φ ρ = |Sol(F) ∩ 𝕃ⁿ|` enumerated lattice points of
the solution set.  For a single-cube DNF the assigned cube is always that one cube, so

```
∑ θ = (∑ over the N lattice points of Sol(F)) sampD(x) · Vol_ED
```

and `eq:almostuniform` — `Ttc.AlmostUniform`, the *only* quantitative fact the
construction gives about `Ttc.e2eSampD` — pins `sampD(x)` to `(1 ± ε')/N`.  The `N`
cancels against the `N` summands:

* `Ttc.Box.sum_rates_box_ge` : `(1 − ε')·Vol_ED ≤ ∑ θ`
* `Ttc.Box.sum_rates_box_le` : `∑ θ ≤ (1 + ε')·Vol_ED`

and on a good coin `Vol_ED ∈ (1 ± ε')·Vol(Sol F)` (`Ttc.mcVol_mem_relErr`).  Hence

```
(1 − ε')² · Vol(Sol F)  ≤  ∑ θ  ≤  (1 + ε')² · Vol(Sol F).
```

With `ε' = ε/12 ≤ 1/12` those two factors are within `[0.84, 1.18]` of `1`, so **`∑ θ`
*is* the volume of the solution set**, up to a constant that cannot be tuned.  The
lattice refinement `ρ = ⌈log₁₀(γ/γ̂)⌉` does *not* enter: making the lattice finer
multiplies the number of summands by `10^(ρn)` and divides each summand by the same
`10^(ρn)`, because the sampler's mass is normalised by the lattice-point count.  That
is the crux, and it is why no choice of `γ̂` can rescue `big`.

Meanwhile `P.thresh = max(24 log(24/δ)/((1−ε')ε'²), 15(log(6/δ) + log m))` is a fixed
function of `ε`, `δ` and `m` alone — it does **not** shrink with the body.  So `big`
reads, up to the `(1 ± ε')²`,

> **`Vol(Sol F) ≳ Thresh/8`** — the input body must have volume at least a fixed
> constant depending only on the accuracy parameters.

That is a genuine constraint on the *instance*, not a consequence of the input
conditions, all of which (`isDNF`, `isPositive`, `hm`, `hr`, `hlen`, `hbdd`,
`hcoeff`, `hgammaHat`, `ball_subset`) are invariant under shrinking the body and
`γ̂` together.  Scaling `[0,a]ⁿ` down to `a → 0` preserves every one of them and
drives `∑ θ → 0`.

## Both directions, proved

* **Necessary** (`Ttc.Box.thresh_le_volume_of_big`): if `big` holds at a box instance,
  then `(1 − ε')·Thresh/8 ≤ (1 + ε')²·Vol(Sol F)`.
* **Sufficient** (`Ttc.Box.big_of_thresh_le_volume`): if `Thresh/8 ≤ (1 − ε')²·Vol(Sol F)`
  then `big` holds at that box instance.

Together these pin `big` to the volume condition, with a gap of only `(1 ± ε')²`.
Nothing here is a repackaging of `big`: both are proved from
`Ttc.almostUniform_of_kv97Sampler` (the sampler's own mixing bound) and
`Ttc.mcVol_mem_relErr` (the Monte-Carlo oracle's own guarantee), and the
counterexample computes `Vol([0,a]ⁿ) = aⁿ·Vol([0,1]ⁿ)` outright.

## What an instance must satisfy for `big` to hold — for the audit surface

> `big` holds as soon as the input body is large: it suffices that
> `Thresh/8 ≤ (1 − ε')² · Vol(Sol F)`, i.e. that `Vol(Sol F)` exceeds
> `max(24 log(24/δ)/((1−ε')ε'²), 15(log(6/δ) + log m)) / 8` by the factor
> `(1 − ε')⁻² ≤ 1.19`.  It **fails** as soon as `Vol(Sol F) < (1 − ε')·Thresh/(8(1 + ε')²)`.
> The condition is a lower bound on the *volume of the solution set* measured against a
> threshold fixed by `(ε, δ, m)`; it is not implied by, and does not follow from, any of
> the boundedness, positivity, inscribed-ball or DNF-shape hypotheses.  Since the
> algorithm may legitimately be run on a small body, `big` must remain a binder —
> or the statement must be restricted to instances with `Vol(Sol F) ≳ Thresh`.

The paper's own witness makes exactly this choice: `Ttc.Box.sideS = max 1 Thresh`
(`Witness/BoxSharp`) picks the side length *so that* the volume clears the threshold,
which is what `Ttc.Box.thresh_div_eight_le_epsPrime_volumeS` proves.  This file shows
that choice was necessary.
-/

namespace Ttc

open MeasureTheory Set Pointwise

namespace Box

variable {n : ℕ}

/-! ## 1.  `Vol([0,a]ⁿ) = aⁿ · Vol([0,1]ⁿ)`

The box is a dilate of the unit box, so Haar scaling gives its volume outright.  This
is the only place the *size* of the body enters; everything else in the file is
scale-free.
-/

/-- **The box of side `r·c` is the `r`-dilate of the box of side `c`**, for `r > 0`.
`Ttc.Box.smul_bxOf` is the special case `r = 10^ρ`. -/
theorem smul_bxOf_of_pos (n : ℕ) {r : ℝ} (hr : 0 < r) (c : ℝ) :
    r • bxOf n c = bxOf n (r * c) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ k
    have happ : (r • y) k = r * y k := rfl
    rw [happ]
    exact ⟨mul_nonneg hr.le (hy k).1, by nlinarith [(hy k).2]⟩
  · intro hx
    refine ⟨r⁻¹ • x, fun k => ?_, ?_⟩
    · have happ : (r⁻¹ • x) k = r⁻¹ * x k := rfl
      rw [happ]
      refine ⟨mul_nonneg (inv_pos.2 hr).le (hx k).1, ?_⟩
      have h2 := (hx k).2
      rw [inv_mul_le_iff₀ hr]
      linarith
    · show r • r⁻¹ • x = x
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]

/-- **The box's volume scales as the `n`-th power of its side.** -/
theorem volume_bxOf_eq (n : ℕ) {a : ℝ} (ha : 0 < a) :
    (volume (bxOf n a)).toReal = a ^ n * (volume (bxOf n 1)).toReal := by
  have hset : bxOf n a = a • bxOf n 1 := by
    rw [smul_bxOf_of_pos n ha 1, mul_one]
  rw [hset, Measure.addHaar_smul, finrank_euclideanSpace_fin,
    abs_of_pos (pow_pos ha n), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]

/-! ## 2.  `∑ θ` is the volume estimate, two-sidedly

The crux.  On a single-cube DNF every enumerated point is assigned the one cube, so
each rate is `sampD(x)·Vol_ED`; `eq:almostuniform` says `sampD(x) ∈ (1 ± ε')/N`, and
there are exactly `N = |Sol(F) ∩ 𝕃ⁿ|` summands.  The `N` cancels — which is why
refining the lattice (increasing `ρ`) cannot make `∑ θ` grow.

`Ttc.Box.sum_rates_ge_of_almostUniform` (`Exec/CanonPolytope`) is the lower half at
the *fixed* side `Ttc.Box.sideS`; these are both halves at an arbitrary side, an
arbitrary precision and an arbitrary volume estimate.
-/

/-- The one cube of the box's DNF is the cube every enumerated point is assigned to. -/
theorem cubeAt_box (n : ℕ) (hn : 1 ≤ n) (a : ℝ) (ρ : ℤ)
    (s : Fin (latticeCount (fun x => (boxAtoms n a x).halfspace) (boxForm n hn) ρ)) :
    cubeAt (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
        (Ttc.toDNF (boxForm n hn)) ρ s = boxCube n := by
  have hspec := cubeAt_spec (toDNF_isDNFOf (boxForm n hn))
    (hasLatticeEnum_bxOf n a hn ρ) s
  simpa only [toDNF_boxForm hn, boxDNF, List.mem_singleton] using hspec.1

/-- Every enumerated point is a lattice point of the box's one region. -/
theorem latticeEnum_mem_region_box (n : ℕ) (hn : 1 ≤ n) (a : ℝ) (ρ : ℤ)
    (s : Fin (latticeCount (fun x => (boxAtoms n a x).halfspace) (boxForm n hn) ρ)) :
    latticeEnum (fun x => (boxAtoms n a x).halfspace) (boxForm n hn) ρ s
      ∈ region (fun x => (boxAtoms n a x).halfspace) (boxCube n)
        ∩ fineLattice n (latticeScale ρ) := by
  have hspec := cubeAt_spec (toDNF_isDNFOf (boxForm n hn))
    (hasLatticeEnum_bxOf n a hn ρ) s
  exact ⟨cubeAt_box n hn a ρ s ▸ hspec.2,
    (latticeEnum_mem (hasLatticeEnum_bxOf n a hn ρ) s).2⟩

/-- **`∑ θ ≥ (1 − ε')·Vol_ED` on the box**, for *any* almost-uniform sampling law and
*any* nonnegative volume estimate.  No hypothesis about the sampler beyond
`eq:almostuniform`, and none about the estimate beyond its sign. -/
theorem sum_rates_box_ge (n : ℕ) (hn : 1 ≤ n) {a : ℝ} (ha : 0 ≤ a) (ρ : ℤ) {ep : ℝ}
    (sampD : Cube (Fin n ⊕ Fin n) → Space n → ℝ) (vol : Cube (Fin n ⊕ Fin n) → ℝ)
    (hvol : 0 ≤ vol (boxCube n))
    (hAU : AlmostUniform (sampD (boxCube n))
      (region (fun x => (boxAtoms n a x).halfspace) (boxCube n)
        ∩ fineLattice n (latticeScale ρ)) ep) :
    (1 - ep) * vol (boxCube n)
      ≤ ∑ s, rates (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
          (Ttc.toDNF (boxForm n hn)) ρ sampD vol s := by
  set N := (region (fun x => (boxAtoms n a x).halfspace) (boxCube n)
    ∩ fineLattice n (latticeScale ρ)).ncard with hNdef
  have hL : latticeCount (fun x => (boxAtoms n a x).halfspace) (boxForm n hn) ρ = N := by
    rw [hNdef, region_eq_bxOf n a hn (mem_toDNF_boxCube n hn), latticeCount_eq_ncard n a hn ρ]
  have hNpos : 0 < N := by
    rw [hNdef, region_eq_bxOf n a hn (mem_toDNF_boxCube n hn)]
    exact ncard_lat_pos n ha ρ
  have key : ∀ s, (1 - ep) / (N : ℝ) * vol (boxCube n)
      ≤ rates (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
          (Ttc.toDNF (boxForm n hn)) ρ sampD vol s := by
    intro s
    simp only [rates, cubeAt_box n hn a ρ s]
    exact mul_le_mul_of_nonneg_right
      (hAU.lower (latticeEnum_mem_region_box n hn a ρ s)) hvol
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum (fun s _ => key s))
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hL]
  have hNne : ((N : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 hNpos.ne'
  field_simp

/-- **`∑ θ ≤ (1 + ε')·Vol_ED` on the box** — the other half of
`Ttc.Box.sum_rates_box_ge`, and the half `big` cannot be met without.  Together they
say the total rate *is* the volume estimate, to within `(1 ± ε')`; in particular the
lattice precision `ρ` has cancelled out entirely. -/
theorem sum_rates_box_le (n : ℕ) (hn : 1 ≤ n) {a : ℝ} (ha : 0 ≤ a) (ρ : ℤ) {ep : ℝ}
    (sampD : Cube (Fin n ⊕ Fin n) → Space n → ℝ) (vol : Cube (Fin n ⊕ Fin n) → ℝ)
    (hvol : 0 ≤ vol (boxCube n))
    (hAU : AlmostUniform (sampD (boxCube n))
      (region (fun x => (boxAtoms n a x).halfspace) (boxCube n)
        ∩ fineLattice n (latticeScale ρ)) ep) :
    ∑ s, rates (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
        (Ttc.toDNF (boxForm n hn)) ρ sampD vol s
      ≤ (1 + ep) * vol (boxCube n) := by
  set N := (region (fun x => (boxAtoms n a x).halfspace) (boxCube n)
    ∩ fineLattice n (latticeScale ρ)).ncard with hNdef
  have hL : latticeCount (fun x => (boxAtoms n a x).halfspace) (boxForm n hn) ρ = N := by
    rw [hNdef, region_eq_bxOf n a hn (mem_toDNF_boxCube n hn), latticeCount_eq_ncard n a hn ρ]
  have hNpos : 0 < N := by
    rw [hNdef, region_eq_bxOf n a hn (mem_toDNF_boxCube n hn)]
    exact ncard_lat_pos n ha ρ
  have key : ∀ s, rates (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
        (Ttc.toDNF (boxForm n hn)) ρ sampD vol s
      ≤ (1 + ep) / (N : ℝ) * vol (boxCube n) := by
    intro s
    simp only [rates, cubeAt_box n hn a ρ s]
    exact mul_le_mul_of_nonneg_right
      (hAU.upper (latticeEnum_mem_region_box n hn a ρ s)) hvol
  refine le_trans (Finset.sum_le_sum (fun s _ => key s)) (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hL]
  have hNne : ((N : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 hNpos.ne'
  field_simp

/-! ## 3.  `eq:almostuniform` for the capstone's own sampler, at an arbitrary box

`Ttc.Box.bxCanonSampD_almostUniform` (`Exec/CanonPolytope`) is this at the *fixed*
side `Ttc.Box.sideS` and the fixed parameter block `Ttc.Box.parS`.  Both halves of §2
need it at an arbitrary side and an arbitrary block, so it is redone here — with the
same one-line proof, `Ttc.almostUniform_of_kv97Sampler` at `Ttc.e2eSampler`.  Nothing
is assumed about the sampler: `Ttc.e2eSampler`'s only quantitative field is a theorem.
-/

/-- **The capstone's sampling law is almost uniform on the box's lattice points.**
`Ttc.canonSampD` is definitionally the `Ttc.e2eSampD …` term that
`Ttc.ttc_volume_final`'s `big` is stated about (`Ttc.Box.canonSampD_eq_e2eSampD`
below re-checks that by `rfl`). -/
theorem canonSampD_box_almostUniform (n : ℕ) (hn : 1 ≤ n) {a : ℝ} (ha : 0 < a) (P : Params)
    (hep0 : 0 < P.epsPrime) (hep : P.epsPrime ≤ 1 / 2) :
    AlmostUniform
      (canonSampD (boxAtoms n a) (Ttc.toDNF (boxForm n hn)) P (fun _ => boxCentre n a) (a / 2)
        (boxCube n))
      (region (fun x => (boxAtoms n a x).halfspace) (boxCube n)
        ∩ fineLattice n (latticeScale (P.precision (a / 2)))) P.epsPrime := by
  set ρ := P.precision (a / 2) with hρ
  have S : KV97Sampler (Fin n ⊕ Fin n) n (fun x => (boxAtoms n a x).halfspace)
      (Ttc.toDNF (boxForm n hn)) ρ P.epsPrime
      (canonSampD (boxAtoms n a) (Ttc.toDNF (boxForm n hn)) P
        (fun _ => boxCentre n a) (a / 2)) :=
    e2eSampler hn hep0 (Fin (Nat.card (FacetIndex (Ttc.toDNF (boxForm n hn)))))
      (canonAm (boxAtoms n a) (Ttc.toDNF (boxForm n hn)))
      (canonBv (boxAtoms n a) (Ttc.toDNF (boxForm n hn)) (latticeScale ρ))
      (fun i => canon_smul_region_subset_body (boxAtoms n a)
        (toDNF_isPositive (boxForm_isPositive hn)) (latticeScale_pos ρ) i)
      (canonRfac (Ttc.toDNF (boxForm n hn)))
      (by rw [canonRfac]; exact_mod_cast one_le_card_facets_box n hn)
      (by rw [canonRfac, Fintype.card_fin])
      (fun _ => boxCentre n a) (a / 2) (by positivity)
      (ball_subset_bxOf n a hn)
      (canonDm (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn)) ρ)
      (canon_dist_le_canonDm (boxAtoms n a) (toDNF_isPositive (boxForm_isPositive hn))
        (toDNF_isDNFOf (boxForm n hn)) (isBounded_sol_bxOf n a hn) ρ)
  have hreg : region (fun x => (boxAtoms n a x).halfspace) (boxCube n) = bxOf n a :=
    region_eq_bxOf n a hn (mem_toDNF_boxCube n hn)
  have hfin : ((latticeScale ρ • region (fun x => (boxAtoms n a x).halfspace) (boxCube n))
      ∩ intLattice n : Set (Space n)).Finite := by
    rw [hreg]; exact dilFiniteOf n a ρ
  have hne : ((latticeScale ρ • region (fun x => (boxAtoms n a x).halfspace) (boxCube n))
      ∩ intLattice n : Set (Space n)).Nonempty := by
    rw [hreg]
    have h : (latticeScale ρ • bxOf n a ∩ intLattice n : Set (Space n))
        = (fun x => latticeScale ρ • x) '' (bxOf n a ∩ fineLattice n (latticeScale ρ)) :=
      (Arlib.Lattice.image_smul_inter_fineLattice (latticeScale_pos _) (bxOf n a)).symm
    rw [h]
    exact (latNonemptyOf n ha.le ρ).image _
  exact almostUniform_of_kv97Sampler S hep0 hep ⟨boxCube n, mem_toDNF_boxCube n hn⟩ hfin hne

/-- **`Ttc.canonSampD` at the box is literally the `Ttc.e2eSampD …` term
`Ttc.ttc_volume_final`'s `big` is stated about.**  By `rfl`, so the abbreviation used
throughout this file cannot have drifted from the capstone's binder. -/
theorem canonSampD_eq_e2eSampD (n : ℕ) (hn : 1 ≤ n) (a : ℝ) (P : Params) :
    canonSampD (boxAtoms n a) (Ttc.toDNF (boxForm n hn)) P (fun _ => boxCentre n a) (a / 2)
      = e2eSampD (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
          (P.precision (a / 2)) P.epsPrime (canonRfac (Ttc.toDNF (boxForm n hn)))
          (Jt := Fin (Nat.card (FacetIndex (Ttc.toDNF (boxForm n hn)))))
          (canonAm (boxAtoms n a) (Ttc.toDNF (boxForm n hn)))
          (canonBv (boxAtoms n a) (Ttc.toDNF (boxForm n hn))
            (latticeScale (P.precision (a / 2))))
          (fun _ => boxCentre n a) (a / 2)
          (canonDm (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
            (P.precision (a / 2))) := rfl

/-! ## 4.  `big` **is** a volume condition

Composing §2 with the Monte-Carlo oracle's own two-sided guarantee
(`Ttc.mcVol_mem_relErr`) evaluates the total rate against the *true* volume:

```
(1 − ε')² · Vol(Sol F)  ≤  ∑ θ  ≤  (1 + ε')² · Vol(Sol F).
```

The two corollaries then bracket `big` between two volume conditions differing only
by the factor `((1+ε')/(1−ε'))² ≤ 1.41` at `ε' ≤ 1/12`.
-/

/-- **The total rate is the volume of the solution set, to within `(1 ± ε')²`.**
The lower half is `eq:almostuniform` plus the oracle's lower estimate; the upper half
is the same two facts on the other side. -/
theorem sum_rates_box_window (n : ℕ) (hn : 1 ≤ n) {a : ℝ} (ha : 0 < a) (P : Params)
    (hep0 : 0 < P.epsPrime) (hep : P.epsPrime ≤ 1 / 2) {c : ℕ → Space n}
    (hc : c ∈ mcGood (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
      (fun _ => boxCentre n a) (a / 2) P.epsPrime P.deltaPrime) :
    (1 - P.epsPrime) ^ 2 * (volume (bxOf n a)).toReal
        ≤ ∑ s, rates (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
            (Ttc.toDNF (boxForm n hn)) (P.precision (a / 2))
            (canonSampD (boxAtoms n a) (Ttc.toDNF (boxForm n hn)) P
              (fun _ => boxCentre n a) (a / 2))
            (mcVol (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
              (fun _ => boxCentre n a) (a / 2) P.epsPrime P.deltaPrime c) s
      ∧ ∑ s, rates (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
            (Ttc.toDNF (boxForm n hn)) (P.precision (a / 2))
            (canonSampD (boxAtoms n a) (Ttc.toDNF (boxForm n hn)) P
              (fun _ => boxCentre n a) (a / 2))
            (mcVol (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
              (fun _ => boxCentre n a) (a / 2) P.epsPrime P.deltaPrime c) s
          ≤ (1 + P.epsPrime) ^ 2 * (volume (bxOf n a)).toReal := by
  have hreg : region (fun x => (boxAtoms n a x).halfspace) (boxCube n) = bxOf n a :=
    region_eq_bxOf n a hn (mem_toDNF_boxCube n hn)
  have hrel := mcVol_mem_relErr (fun x => (boxAtoms n a x).halfspace)
    (Ttc.toDNF (boxForm n hn)) (fun _ => boxCentre n a) (a / 2) P.epsPrime P.deltaPrime hc
    (boxCube n) (mem_toDNF_boxCube n hn)
  rw [hreg] at hrel
  have hV : 0 ≤ (volume (bxOf n a)).toReal := ENNReal.toReal_nonneg
  have hlo : (1 - P.epsPrime) * (volume (bxOf n a)).toReal
      ≤ mcVol (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
          (fun _ => boxCentre n a) (a / 2) P.epsPrime P.deltaPrime c (boxCube n) := hrel.1
  have hhi : mcVol (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
        (fun _ => boxCentre n a) (a / 2) P.epsPrime P.deltaPrime c (boxCube n)
      ≤ (1 + P.epsPrime) * (volume (bxOf n a)).toReal := hrel.2
  have hvol0 : 0 ≤ mcVol (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
      (fun _ => boxCentre n a) (a / 2) P.epsPrime P.deltaPrime c (boxCube n) := by
    refine le_trans ?_ hlo
    have : (0 : ℝ) ≤ 1 - P.epsPrime := by linarith
    exact mul_nonneg this hV
  have hAU := canonSampD_box_almostUniform n hn ha P hep0 hep
  refine ⟨?_, ?_⟩
  · refine le_trans ?_ (sum_rates_box_ge n hn ha.le (P.precision (a / 2)) _ _ hvol0 hAU)
    have h1 : (0 : ℝ) ≤ 1 - P.epsPrime := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hlo h1]
  · refine le_trans (sum_rates_box_le n hn ha.le (P.precision (a / 2)) _ _ hvol0 hAU) ?_
    have h1 : (0 : ℝ) ≤ 1 + P.epsPrime := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hhi h1]

/-- **`big` forces the body to be big** — the necessary direction.  If the regime
condition holds at *one* good coin, then `Thresh` is bounded by the volume of the
solution set, up to `(1 + ε')²`.  Nothing about the algorithm's run is used; this is
purely the evaluation of `∑ θ`. -/
theorem thresh_le_volume_of_big (n : ℕ) (hn : 1 ≤ n) {a : ℝ} (ha : 0 < a) (P : Params)
    (hep0 : 0 < P.epsPrime) (hep : P.epsPrime ≤ 1 / 2) {c : ℕ → Space n}
    (hc : c ∈ mcGood (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
      (fun _ => boxCentre n a) (a / 2) P.epsPrime P.deltaPrime)
    (hbig : (1 - P.epsPrime) * P.thresh / 8
      ≤ ∑ s, rates (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
          (Ttc.toDNF (boxForm n hn)) (P.precision (a / 2))
          (canonSampD (boxAtoms n a) (Ttc.toDNF (boxForm n hn)) P
            (fun _ => boxCentre n a) (a / 2))
          (mcVol (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
            (fun _ => boxCentre n a) (a / 2) P.epsPrime P.deltaPrime c) s) :
    (1 - P.epsPrime) * P.thresh / 8
      ≤ (1 + P.epsPrime) ^ 2 * (volume (bxOf n a)).toReal :=
  le_trans hbig (sum_rates_box_window n hn ha P hep0 hep hc).2

/-- **A big enough body gives `big`** — the sufficient direction.  So `big` is not
some subtle joint condition on the sampler, the oracle and the lattice: it is exactly
"the solution set has volume at least about `Thresh/8`". -/
theorem big_of_thresh_le_volume (n : ℕ) (hn : 1 ≤ n) {a : ℝ} (ha : 0 < a) (P : Params)
    (hep0 : 0 < P.epsPrime) (hep : P.epsPrime ≤ 1 / 2) (hT : 0 ≤ P.thresh)
    (hth : P.thresh / 8 ≤ (1 - P.epsPrime) ^ 2 * (volume (bxOf n a)).toReal) :
    ∀ c ∈ mcGood (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
        (fun _ => boxCentre n a) (a / 2) P.epsPrime P.deltaPrime,
      (1 - P.epsPrime) * P.thresh / 8
        ≤ ∑ s, rates (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
            (Ttc.toDNF (boxForm n hn)) (P.precision (a / 2))
            (canonSampD (boxAtoms n a) (Ttc.toDNF (boxForm n hn)) P
              (fun _ => boxCentre n a) (a / 2))
            (mcVol (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
              (fun _ => boxCentre n a) (a / 2) P.epsPrime P.deltaPrime c) s := by
  intro c hc
  refine le_trans ?_ (sum_rates_box_window n hn ha P hep0 hep hc).1
  nlinarith [hth, hT, hep0]

/-! ## 5.  The counterexample

`big` is a `∀ c ∈ mcGood …`, so refuting it needs a coin in `mcGood`.  There is one:
the constructed oracle's own failure bound (`Ttc.measure_mcGood_ge`, Chebyshev plus a
union bound — no hypothesis about `Vol_ED`) puts at least `1 − δ/4 ≥ 3/4` of the coin
measure inside the good event.
-/

/-- **The good event of the volume oracle is inhabited on the box.**  Its measure is
at least `1 − δ/4 ≥ 3/4 > 0`. -/
theorem mcGood_box_nonempty (n : ℕ) (hn : 1 ≤ n) {a : ℝ} (ha : 0 < a) (P : Params)
    {δ₀ : ℝ} (hδeq : P.δ = δ₀) (hδ0 : 0 < δ₀) (hδ1 : δ₀ ≤ 1) :
    (mcGood (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
      (fun _ => boxCentre n a) (a / 2) P.epsPrime P.deltaPrime).Nonempty := by
  have hlen : ((Ttc.toDNF (boxForm n hn)).length : ℝ) ≤ (P.m : ℝ) := by
    rw [length_toDNF_boxForm n hn]
    exact_mod_cast P.hm
  have hmeas := measure_mcGood_ge (fun x => (boxAtoms n a x).halfspace)
    (Ttc.toDNF (boxForm n hn)) P hδeq hδ0 hδ1 (by positivity : (0 : ℝ) < a / 2)
    (fun _ => boxCentre n a) (ball_subset_bxOf n a hn)
    (fun i => convex_region (boxAtoms n a) i.val)
    (volume_region_ne_top_of_isBounded (toDNF_isDNFOf (boxForm n hn))
      (isBounded_sol_bxOf n a hn)) hlen
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  rw [hemp, measure_empty] at hmeas
  simp only [ENNReal.toReal_zero] at hmeas
  linarith

/-- **`big` is not derivable from `Ttc.ttc_volume_final`'s other hypotheses.**

For every dimension `n ≥ 1` and every `(ε, δ) ∈ (0,1] × (0,1]` there is a side length
`a > 0` at which the box `[0,a]ⁿ` — with its own atoms, its own one-cube DNF, the
inscribed ball of radius `a/2` about its centre, and the parameter block
`Ttc.ttcParams` computes — satisfies **every** other hypothesis of
`Ttc.ttc_volume_final` and **fails** `big`.

The conjuncts are, in order: the DNF condition `isDNF`; positivity `isPositive`; the
cube count `hm`; the facet count `hr`; the parameter tie `hP`; the loop-length bound
`hlen`; boundedness `hbdd`; the nondegenerate-facet condition `hcoeff`;
`hgammaHat`; `ball_subset`; and finally `¬ big`, stated with the capstone's own
`Ttc.e2eSampD`/`Ttc.mcVol` terms.  (`M_eq` is `rfl` by the choice of `M`, and
`hε0 hε1 hδ0 hδ1 hn` are the arguments.)

The mechanism is §4: `∑ θ ≤ (1+ε')²·Vol([0,a]ⁿ) = (1+ε')²·aⁿ·Vol([0,1]ⁿ)`, which
`a → 0` drives below the fixed `(1−ε')·Thresh/8`, while every other hypothesis is
scale-free. -/
theorem big_not_derivable (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ a : ℝ, 0 < a ∧
      IsDNFOf (Ttc.toDNF (boxForm n hn)) (boxForm n hn) ∧
      DNF.IsPositive (Ttc.toDNF (boxForm n hn)) ∧
      1 ≤ Nat.card {cu : Cube (Fin n ⊕ Fin n) // cu ∈ Ttc.toDNF (boxForm n hn)} ∧
      1 ≤ Nat.card (FacetIndex (Ttc.toDNF (boxForm n hn))) ∧
      parS n hn ε (4 * δ / 5) hε0 hε1
        = ttcParams (Ttc.toDNF (boxForm n hn)) n ε (4 * δ / 5) hε0 hε1 hn
            (one_le_card_cubes_box n hn) (one_le_card_facets_box n hn) ∧
      ((Ttc.toDNF (boxForm n hn)).length : ℝ) ≤ ((parS n hn ε (4 * δ / 5) hε0 hε1).m : ℝ) ∧
      Bornology.IsBounded
        (sol (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)) ∧
      (∀ j : FacetIndex (Ttc.toDNF (boxForm n hn)),
        (boxAtoms n a j.2.val.atom).coeff ≠ 0) ∧
      0 < a / 2 ∧
      (∀ i : {cu : Cube (Fin n ⊕ Fin n) // cu ∈ Ttc.toDNF (boxForm n hn)},
        Metric.ball (boxCentre n a) (a / 2)
          ⊆ region (fun x => (boxAtoms n a x).halfspace) i.val) ∧
      ¬ (∀ c ∈ mcGood (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
            (fun _ => boxCentre n a) (a / 2)
            (parS n hn ε (4 * δ / 5) hε0 hε1).epsPrime
            (parS n hn ε (4 * δ / 5) hε0 hε1).deltaPrime,
          (1 - (parS n hn ε (4 * δ / 5) hε0 hε1).epsPrime)
              * (parS n hn ε (4 * δ / 5) hε0 hε1).thresh / 8
            ≤ ∑ s, rates (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
                (Ttc.toDNF (boxForm n hn))
                ((parS n hn ε (4 * δ / 5) hε0 hε1).precision (a / 2))
                (e2eSampD (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
                  ((parS n hn ε (4 * δ / 5) hε0 hε1).precision (a / 2))
                  (parS n hn ε (4 * δ / 5) hε0 hε1).epsPrime
                  (canonRfac (Ttc.toDNF (boxForm n hn)))
                  (Jt := Fin (Nat.card (FacetIndex (Ttc.toDNF (boxForm n hn)))))
                  (canonAm (boxAtoms n a) (Ttc.toDNF (boxForm n hn)))
                  (canonBv (boxAtoms n a) (Ttc.toDNF (boxForm n hn))
                    (latticeScale ((parS n hn ε (4 * δ / 5) hε0 hε1).precision (a / 2))))
                  (fun _ => boxCentre n a) (a / 2)
                  (canonDm (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
                    ((parS n hn ε (4 * δ / 5) hε0 hε1).precision (a / 2))))
                (mcVol (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
                  (fun _ => boxCentre n a) (a / 2)
                  (parS n hn ε (4 * δ / 5) hε0 hε1).epsPrime
                  (parS n hn ε (4 * δ / 5) hε0 hε1).deltaPrime c) s) := by
  have hd0 : (0 : ℝ) < 4 * δ / 5 := by linarith
  have hd1 : (4 : ℝ) * δ / 5 ≤ 1 := by linarith
  set P := parS n hn ε (4 * δ / 5) hε0 hε1 with hPdef
  have hep0 : 0 < P.epsPrime := parS_epsPrime_pos (n := n) (δ := 4 * δ / 5) hn hε0 hε1
  have hep12 : P.epsPrime ≤ 1 / 12 := parS_epsPrime_le (n := n) (δ := 4 * δ / 5) hn hε0 hε1
  have hT0 : 0 < P.thresh := parS_thresh_pos (n := n) hn hε0 hε1 hd0 hd1
  have hV1pos : 0 < (volume (bxOf n 1)).toReal := volume_bxOf_pos n one_pos
  have hepl : (0 : ℝ) < 1 - P.epsPrime := by linarith
  set T := (1 - P.epsPrime) * P.thresh / 8 with hTdef
  have hTpos : 0 < T := by
    rw [hTdef]; exact div_pos (mul_pos hepl hT0) (by norm_num)
  set K := (1 + P.epsPrime) ^ 2 * (volume (bxOf n 1)).toReal with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]; exact mul_pos (by positivity) hV1pos
  set a := min 1 (T / (2 * K)) with hadef
  have ha1 : a ≤ 1 := min_le_left _ _
  have haT : a ≤ T / (2 * K) := min_le_right _ _
  have ha0 : 0 < a := lt_min one_pos (div_pos hTpos (by linarith))
  refine ⟨a, ha0, toDNF_isDNFOf (boxForm n hn),
    toDNF_isPositive (boxForm_isPositive hn), one_le_card_cubes_box n hn,
    one_le_card_facets_box n hn, by rw [hPdef]; rfl, ?_,
    isBounded_sol_bxOf n a hn, coeff_ne_zero_bxOf n a hn, by linarith,
    ball_subset_bxOf n a hn, ?_⟩
  · rw [length_toDNF_boxForm n hn]
    exact_mod_cast P.hm
  · intro hbig
    obtain ⟨c0, hc0⟩ := mcGood_box_nonempty n hn ha0 P rfl hd0 hd1
    have hwin := (sum_rates_box_window n hn ha0 P hep0 (by linarith) hc0).2
    have hvol : (volume (bxOf n a)).toReal = a ^ n * (volume (bxOf n 1)).toReal :=
      volume_bxOf_eq n ha0
    have han : a ^ n ≤ a := by
      calc a ^ n ≤ a ^ 1 := pow_le_pow_of_le_one ha0.le ha1 hn
        _ = a := pow_one a
    have hKa : (1 + P.epsPrime) ^ 2 * (volume (bxOf n a)).toReal ≤ T / 2 := by
      rw [hvol]
      calc (1 + P.epsPrime) ^ 2 * (a ^ n * (volume (bxOf n 1)).toReal)
          = K * a ^ n := by rw [hKdef]; ring
        _ ≤ K * a := mul_le_mul_of_nonneg_left han hKpos.le
        _ ≤ K * (T / (2 * K)) := mul_le_mul_of_nonneg_left haT hKpos.le
        _ = T / 2 := by field_simp
    have hlt := lt_of_le_of_lt (le_trans hwin hKa) (by linarith : T / 2 < T)
    exact absurd (hbig c0 hc0) (not_le.2 hlt)

/-- **`big` is exactly a lower bound on the volume of the solution set.**  The two
directions of §4, side by side at the box, so the gap between the sufficient and the
necessary condition is visible: it is the factor `((1+ε')/(1−ε'))²`, and nothing else.
There is no third quantity — no lattice count, no precision `ρ`, no sampler
parameter — that could be tuned to make `big` hold on a body of small volume. -/
theorem big_iff_volume_window (n : ℕ) (hn : 1 ≤ n) {a : ℝ} (ha : 0 < a) (P : Params)
    (hep0 : 0 < P.epsPrime) (hep : P.epsPrime ≤ 1 / 2) (hT : 0 ≤ P.thresh)
    (hgood : (mcGood (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
      (fun _ => boxCentre n a) (a / 2) P.epsPrime P.deltaPrime).Nonempty) :
    (P.thresh / 8 ≤ (1 - P.epsPrime) ^ 2 * (volume (bxOf n a)).toReal →
        ∀ c ∈ mcGood (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
            (fun _ => boxCentre n a) (a / 2) P.epsPrime P.deltaPrime,
          (1 - P.epsPrime) * P.thresh / 8
            ≤ ∑ s, rates (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
                (Ttc.toDNF (boxForm n hn)) (P.precision (a / 2))
                (canonSampD (boxAtoms n a) (Ttc.toDNF (boxForm n hn)) P
                  (fun _ => boxCentre n a) (a / 2))
                (mcVol (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
                  (fun _ => boxCentre n a) (a / 2) P.epsPrime P.deltaPrime c) s)
      ∧ ((∀ c ∈ mcGood (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
              (fun _ => boxCentre n a) (a / 2) P.epsPrime P.deltaPrime,
            (1 - P.epsPrime) * P.thresh / 8
              ≤ ∑ s, rates (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
                  (Ttc.toDNF (boxForm n hn)) (P.precision (a / 2))
                  (canonSampD (boxAtoms n a) (Ttc.toDNF (boxForm n hn)) P
                    (fun _ => boxCentre n a) (a / 2))
                  (mcVol (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
                    (fun _ => boxCentre n a) (a / 2) P.epsPrime P.deltaPrime c) s) →
          (1 - P.epsPrime) * P.thresh / 8
            ≤ (1 + P.epsPrime) ^ 2 * (volume (bxOf n a)).toReal) := by
  obtain ⟨c0, hc0⟩ := hgood
  exact ⟨fun hth => big_of_thresh_le_volume n hn ha P hep0 hep hT hth,
    fun hbig => thresh_le_volume_of_big n hn ha P hep0 hep hc0 (hbig c0 hc0)⟩

/-! ## 6.  The refuted proposition really is the capstone's binder

`Ttc.Box.big_not_derivable` refutes a proposition; this section checks that the
proposition is not a lookalike.  `Ttc.Box.ttc_volume_final_at_box` applies
`Ttc.ttc_volume_final` at the counterexample's instance, discharging **every** binder
from the same terms `Ttc.Box.big_not_derivable` produces, and taking as its only
hypothesis the refuted proposition written out character for character.  It
elaborates, so that proposition *is* the binder, at the same `M`, `P`, `cen`, `γ̂`
and precision.  (`Ttc.Box.canonSampD_eq_e2eSampD` records, by `rfl`, that the
shorter `Ttc.canonSampD` spelling used in §3–§4 is the same law.)
-/

/-- **`Ttc.ttc_volume_final`, at the box of side `a`, with `big` as its only
hypothesis.**  A shape check, not a new result: every other binder is discharged from
the same terms `Ttc.Box.big_not_derivable` exhibits, so the `big` this file refutes is
the capstone's own. -/
theorem ttc_volume_final_at_box (n : ℕ) (hn : 1 ≤ n) (ε δ a : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 < a)
    (big : ∀ c ∈ mcGood (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
        (fun _ => boxCentre n a) (a / 2) (parS n hn ε (4 * δ / 5) hε0 hε1).epsPrime
        (parS n hn ε (4 * δ / 5) hε0 hε1).deltaPrime,
      (1 - (parS n hn ε (4 * δ / 5) hε0 hε1).epsPrime)
          * (parS n hn ε (4 * δ / 5) hε0 hε1).thresh / 8
        ≤ ∑ s, rates (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
            (Ttc.toDNF (boxForm n hn))
            ((parS n hn ε (4 * δ / 5) hε0 hε1).precision (a / 2))
            (e2eSampD (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
              ((parS n hn ε (4 * δ / 5) hε0 hε1).precision (a / 2))
              (parS n hn ε (4 * δ / 5) hε0 hε1).epsPrime
              (canonRfac (Ttc.toDNF (boxForm n hn)))
              (Jt := Fin (Nat.card (FacetIndex (Ttc.toDNF (boxForm n hn)))))
              (canonAm (boxAtoms n a) (Ttc.toDNF (boxForm n hn)))
              (canonBv (boxAtoms n a) (Ttc.toDNF (boxForm n hn))
                (latticeScale ((parS n hn ε (4 * δ / 5) hε0 hε1).precision (a / 2))))
              (fun _ => boxCentre n a) (a / 2)
              (canonDm (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
                ((parS n hn ε (4 * δ / 5) hε0 hε1).precision (a / 2))))
            (mcVol (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
              (fun _ => boxCentre n a) (a / 2)
              (parS n hn ε (4 * δ / 5) hε0 hε1).epsPrime
              (parS n hn ε (4 * δ / 5) hε0 hε1).deltaPrime c) s) :
    (1 - δ ≤
      (∫⁻ c, trajLaw (rates (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
            (Ttc.toDNF (boxForm n hn))
            ((parS n hn ε (4 * δ / 5) hε0 hε1).precision (a / 2))
            (canonSampD (boxAtoms n a) (Ttc.toDNF (boxForm n hn))
              (parS n hn ε (4 * δ / 5) hε0 hε1) (fun _ => boxCentre n a) (a / 2))
            (mcVol (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
              (fun _ => boxCentre n a) (a / 2)
              (parS n hn ε (4 * δ / 5) hε0 hε1).epsPrime
              (parS n hn ε (4 * δ / 5) hε0 hε1).deltaPrime c))
          {t : ℕ → Fin (latticeCount (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
              ((parS n hn ε (4 * δ / 5) hε0 hε1).precision (a / 2))) → ℕ |
            ttcOutput (parS n hn ε (4 * δ / 5) hε0 hε1)
                (coveredOracles (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
                  ((parS n hn ε (4 * δ / 5) hε0 hε1).precision (a / 2))
                  (mcVol (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
                    (fun _ => boxCentre n a) (a / 2)
                    (parS n hn ε (4 * δ / 5) hε0 hε1).epsPrime
                    (parS n hn ε (4 * δ / 5) hε0 hε1).deltaPrime c))
                Ttc.toDNF ((parS n hn ε (4 * δ / 5) hε0 hε1).precision (a / 2))
                (boxForm n hn) t
              ∈ relErr ε (volSol (fun x => (boxAtoms n a x).halfspace) (boxForm n hn))}
        ∂(MonteCarlo.coins n)).toReal)
    ∧
    (∀ (c : ℕ → Space n)
        (t : ℕ → Fin (latticeCount (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
          ((parS n hn ε (4 * δ / 5) hε0 hε1).precision (a / 2))) → ℕ)
        (cVol cSample thr : ℕ),
      (thr : ℝ) = (parS n hn ε (4 * δ / 5) hε0 hε1).thresh →
      Terminates (parS n hn ε (4 * δ / 5) hε0 hε1)
          (coveredOracles (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
            ((parS n hn ε (4 * δ / 5) hε0 hε1).precision (a / 2))
            (mcVol (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
              (fun _ => boxCentre n a) (a / 2)
              (parS n hn ε (4 * δ / 5) hε0 hε1).epsPrime
              (parS n hn ε (4 * δ / 5) hε0 hε1).deltaPrime c) t)
          (Ttc.toDNF (boxForm n hn)) →
      runCost (parS n hn ε (4 * δ / 5) hε0 hε1)
          (coveredOracles (fun x => (boxAtoms n a x).halfspace) (boxForm n hn)
            ((parS n hn ε (4 * δ / 5) hε0 hε1).precision (a / 2))
            (mcVol (fun x => (boxAtoms n a x).halfspace) (Ttc.toDNF (boxForm n hn))
              (fun _ => boxCentre n a) (a / 2)
              (parS n hn ε (4 * δ / 5) hε0 hε1).epsPrime
              (parS n hn ε (4 * δ / 5) hε0 hε1).deltaPrime c) t)
          cVol cSample ((parS n hn ε (4 * δ / 5) hε0 hε1).precision (a / 2))
          (Ttc.toDNF (boxForm n hn))
        ≤ (Ttc.toDNF (boxForm n hn)).length * (cVol + cSample * thr)) :=
  ttc_volume_final (boxAtoms n a) (boxForm n hn) ε δ hε0 hε1 hδ0 hδ1 hn
    (fun x => (boxAtoms n a x).halfspace) rfl Ttc.toDNF
    (toDNF_isDNFOf (boxForm n hn)) (toDNF_isPositive (boxForm_isPositive hn))
    (one_le_card_cubes_box n hn) (one_le_card_facets_box n hn)
    (parS n hn ε (4 * δ / 5) hε0 hε1) rfl
    (by rw [length_toDNF_boxForm n hn]
        exact_mod_cast (parS n hn ε (4 * δ / 5) hε0 hε1).hm)
    (isBounded_sol_bxOf n a hn) (coeff_ne_zero_bxOf n a hn)
    (fun _ => boxCentre n a) (a / 2) (by linarith) (ball_subset_bxOf n a hn) big

/-! ## 7.  Verification -/

#print axioms Ttc.Box.smul_bxOf_of_pos
#print axioms Ttc.Box.volume_bxOf_eq
#print axioms Ttc.Box.cubeAt_box
#print axioms Ttc.Box.latticeEnum_mem_region_box
#print axioms Ttc.Box.sum_rates_box_ge
#print axioms Ttc.Box.sum_rates_box_le
#print axioms Ttc.Box.canonSampD_box_almostUniform
#print axioms Ttc.Box.canonSampD_eq_e2eSampD
#print axioms Ttc.Box.sum_rates_box_window
#print axioms Ttc.Box.thresh_le_volume_of_big
#print axioms Ttc.Box.big_of_thresh_le_volume
#print axioms Ttc.Box.mcGood_box_nonempty
#print axioms Ttc.Box.big_not_derivable
#print axioms Ttc.Box.big_iff_volume_window
#print axioms Ttc.Box.ttc_volume_final_at_box

end Box

end Ttc
