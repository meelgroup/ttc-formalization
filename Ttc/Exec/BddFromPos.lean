/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Ttc.Exec.Prune

/-!
# `Exec/BddFromPos`: after the pruning round, `hbdd` is **derivable** from `hpos`

**Verdict: proved, not refuted.**  `Ttc.isBounded_sol_pruneForm_of_volSol_pos` derives

```
Bornology.IsBounded (sol (atomSet atoms) (pruneForm atoms φ))
```

from `hφ : φ.IsPositive` and `hpos : 0 < volSol (atomSet atoms) φ` alone — no
boundedness hypothesis anywhere in its statement or its proof.  So the `hbdd` binder
of `Ttc.ttc_volume_estimate` is redundant *for the formula the algorithm is actually
handed*, and every consumer of `Ttc.pruneBdd` can be fed this instead.

## The four steps

1. **`hpos` forces finite volume.**  `Ttc.volSol M φ = (volume (sol M φ)).toReal` and
   `ENNReal.toReal ⊤ = 0`, so `0 < volSol` gives `volume (sol M φ) ≠ ⊤`
   (`Ttc.volume_sol_ne_top_of_volSol_pos`).
2. **Each cube inherits it.**  `region (atomSet atoms) c ⊆ sol (atomSet atoms) φ` for
   every `c ∈ toDNFd φ` (`Ttc.region_subset_sol`), so each region has finite volume too.
3. **Each region is convex** — `Ttc.convex_region`, unconditional.
4. **The crux** (`Ttc.isBounded_of_convex_of_interior_of_volume_ne_top`): *a convex
   subset of `Space n` with an interior point and finite volume is bounded.*

Step 4 is the mathematical content; Mathlib has no such lemma (`Analysis/Convex/Measure`
only offers `Convex.addHaar_frontier`, and `Analysis/Convex/GaugeRescale` takes
boundedness as a hypothesis rather than concluding it).  It is proved here from scratch,
contrapositively: if `Metric.ball a r ⊆ S`, `S` is convex and `S` is *un*bounded, then
for every `N` one can find `x ∈ S` with `dist x a > 4r(N+1)` and slide `N` balls of
radius `r/2` along the segment `[a, x]` inside `S`
(`Ttc.ball_combo_subset_of_convex`), spaced `2r` apart, hence pairwise disjoint
(`Metric.ball_disjoint_ball`).  That gives
`N · volume (ball 0 (r/2)) ≤ volume S` for **every** `N`
(`Ttc.nsmul_volume_ball_le_of_convex_of_not_isBounded`), and a ball has positive finite
volume, so `volume S = ⊤`.

Finally `sol (atomSet atoms) (pruneForm atoms φ)` is the union of the surviving regions
(`Ttc.sol_pruneForm`), a *finite* union of bounded sets, hence bounded
(`Bornology.isBounded_biUnion`).

## Why this only became available after the pruning round

Before `Exec/Prune` this argument was **unavailable**: step 4 needs an interior point,
and an unpruned cube can be a *line* — convex, unbounded, and of volume `0`, so step 4
simply does not apply to it.  `Ttc.degForm` (`Exec/Degenerate`) is the machine-checked
witness that `hpos` does not imply per-cube full-dimensionality
(`Ttc.hint_not_derivable`), which is exactly the gap.  `Ttc.pruneForm` deletes those
cubes, and `Ttc.interior_nonempty_pruneForm` supplies the interior point step 4
requires — by construction, for every surviving cube.  Only then does "positive volume"
imply "bounded".

The original `hbdd` at the *unpruned* formula is a different statement, and this file
does **not** claim `0 < volSol (atomSet atoms) φ → IsBounded (sol (atomSet atoms) φ)`.
That implication is in fact false — in dimension `2`, `(box) ∨ (x₁ ≤ 0 ∧ −x₁ ≤ 0)` is
negation-free, has positive volume, and has unbounded `Sol` — though no witness for it
is formalised here, since nothing needs one.  What is claimed and proved is the pruned
statement, and that is the only one the run consumes: `Ttc.ttc_volume_prune` and
`Ttc.ttcInput_bdd` (`Exec/Api`) spend `hbdd` on nothing but `Ttc.pruneBdd`, whose
conclusion is exactly `Ttc.isBounded_sol_pruneForm_of_volSol_pos`'s
(`Ttc.pruneBdd_eq_isBounded_sol_pruneForm_of_volSol_pos`).
-/

namespace Ttc

open MeasureTheory Set

open scoped ENNReal

section ConvexBounded

variable {n : ℕ}

/-! ## Step 4: the crux

A convex set containing a ball around `a` and a point `x` contains a whole family of
balls interpolating between them — the "ice-cream cone" on `ball a r` with apex `x`.
Only the balls' centres and radii are needed, never the cone's volume.
-/

/-- **Convexity slides a ball along a segment.**  If `S` is convex, contains
`Metric.ball a r`, and contains `x`, then for every `t ∈ [0, 1)` it contains the ball of
radius `(1 - t)·r` around the point `a + t·(x - a)` of the segment `[a, x]`.

This is the cone `conv (ball a r ∪ {x})` described one slice at a time. -/
theorem ball_combo_subset_of_convex {S : Set (Space n)} (hS : Convex ℝ S)
    {a x : Space n} {r t : ℝ} (hball : Metric.ball a r ⊆ S) (hx : x ∈ S)
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Metric.ball (a + t • (x - a)) ((1 - t) * r) ⊆ S := by
  intro y hy
  have h1t : (0 : ℝ) < 1 - t := by linarith
  set c : Space n := a + t • (x - a) with hcdef
  set z : Space n := a + (1 - t)⁻¹ • (y - c) with hzdef
  have hza : z - a = (1 - t)⁻¹ • (y - c) := by rw [hzdef]; abel
  have hzball : z ∈ Metric.ball a r := by
    rw [Metric.mem_ball, dist_eq_norm, hza, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 h1t)]
    rw [Metric.mem_ball, dist_eq_norm] at hy
    calc (1 - t)⁻¹ * ‖y - c‖ < (1 - t)⁻¹ * ((1 - t) * r) :=
          mul_lt_mul_of_pos_left hy (inv_pos.2 h1t)
      _ = r := by field_simp
  have key : (1 - t) • (z - a) = y - c := by
    rw [hza, smul_smul, mul_inv_cancel₀ h1t.ne', one_smul]
  have hy' : (1 - t) • z + t • x = y := by
    have hsplit : (1 - t) • z = (1 - t) • (z - a) + (1 - t) • a := by
      rw [smul_sub]; abel
    rw [hsplit, key, hcdef]
    module
  have hmem := hS (hball hzball) hx h1t.le ht0 (by ring)
  rwa [hy'] at hmem

/-- **An unbounded convex set with an interior point has volume `≥ N · vol(ball)` for
every `N`.**

The cone of `Ttc.ball_combo_subset_of_convex` is sampled at `N` parameters
`t_j = j·(2r)/D`, `j < N`, where `D = dist x a` is chosen larger than `4r(N + 1)`.  Then
every `t_j < 1/2`, so each slice has radius `≥ r/2`; and consecutive centres are exactly
`2r` apart, so the `N` balls of radius `r/2` are pairwise disjoint. -/
theorem nsmul_volume_ball_le_of_convex_of_not_isBounded {S : Set (Space n)}
    (hS : Convex ℝ S) {a : Space n} {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball a r ⊆ S) (hub : ¬ Bornology.IsBounded S) (N : ℕ) :
    (N : ℝ≥0∞) * volume (Metric.ball (0 : Space n) (r / 2)) ≤ volume S := by
  -- a point of `S` far enough from `a`
  obtain ⟨x, hxS, hxfar⟩ : ∃ x ∈ S, 4 * r * ((N : ℝ) + 1) < dist x a := by
    by_contra hcon
    push Not at hcon
    exact hub ((Metric.isBounded_iff_subset_closedBall a).2
      ⟨4 * r * ((N : ℝ) + 1), fun y hy => Metric.mem_closedBall.2 (hcon y hy)⟩)
  set D : ℝ := dist x a with hDdef
  have hDpos : 0 < D := lt_trans (by positivity) hxfar
  have hxa : ‖x - a‖ = D := by rw [hDdef, dist_eq_norm]
  -- every sampled parameter is in `[0, 1/2)`
  have hpar : ∀ j : ℕ, j < N → 0 ≤ (j : ℝ) * (2 * r) / D ∧ (j : ℝ) * (2 * r) / D < 1 / 2 := by
    intro j hj
    refine ⟨by positivity, ?_⟩
    rw [div_lt_iff₀ hDpos]
    have hjN : (j : ℝ) < (N : ℝ) + 1 := by
      have : j < N + 1 := Nat.lt_succ_of_lt hj
      exact_mod_cast this
    nlinarith [mul_pos hr (sub_pos.2 hjN)]
  -- each sampled ball of radius `r/2` sits inside `S`
  have hballsub : ∀ j : ℕ, j < N →
      Metric.ball (a + ((j : ℝ) * (2 * r) / D) • (x - a)) (r / 2) ⊆ S := by
    intro j hj
    obtain ⟨h0, h1⟩ := hpar j hj
    refine subset_trans (Metric.ball_subset_ball ?_)
      (ball_combo_subset_of_convex hS hball hxS h0 (by linarith))
    nlinarith [mul_pos hr (sub_pos.2 h1)]
  -- distinct sampled centres are `≥ 2r` apart
  have hdist : ∀ j k : ℕ, j ≠ k →
      2 * r ≤ dist (a + ((j : ℝ) * (2 * r) / D) • (x - a))
                   (a + ((k : ℝ) * (2 * r) / D) • (x - a)) := by
    intro j k hjk
    rw [dist_eq_norm]
    have e : (a + ((j : ℝ) * (2 * r) / D) • (x - a)) - (a + ((k : ℝ) * (2 * r) / D) • (x - a))
        = (((j : ℝ) - (k : ℝ)) * (2 * r) / D) • (x - a) := by module
    rw [e, norm_smul, Real.norm_eq_abs, hxa]
    have habs : |((j : ℝ) - (k : ℝ)) * (2 * r) / D| = |(j : ℝ) - (k : ℝ)| * (2 * r) / D := by
      rw [abs_div, abs_mul, abs_of_pos hDpos, abs_of_pos (by linarith : (0 : ℝ) < 2 * r)]
    have hge1 : (1 : ℝ) ≤ |(j : ℝ) - (k : ℝ)| := by
      have hne : ((j : ℤ) - (k : ℤ)) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hjk)
      have h := Int.one_le_abs hne
      have hcast : ((|(j : ℤ) - (k : ℤ)| : ℤ) : ℝ) = |(j : ℝ) - (k : ℝ)| := by push_cast; ring
      rw [← hcast]
      exact_mod_cast h
    rw [habs, div_mul_cancel₀ _ hDpos.ne']
    nlinarith
  -- so they are pairwise disjoint
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range N) : Set ℕ)
      (fun j : ℕ => Metric.ball (a + ((j : ℝ) * (2 * r) / D) • (x - a)) (r / 2)) := by
    intro j _ k _ hjk
    exact Metric.ball_disjoint_ball (by linarith [hdist j k hjk])
  have hsub : (⋃ j ∈ Finset.range N,
      Metric.ball (a + ((j : ℝ) * (2 * r) / D) • (x - a)) (r / 2)) ⊆ S :=
    Set.iUnion₂_subset fun j hj => hballsub j (Finset.mem_range.1 hj)
  calc (N : ℝ≥0∞) * volume (Metric.ball (0 : Space n) (r / 2))
      = ∑ _j ∈ Finset.range N, volume (Metric.ball (0 : Space n) (r / 2)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = ∑ j ∈ Finset.range N,
          volume (Metric.ball (a + ((j : ℝ) * (2 * r) / D) • (x - a)) (r / 2)) :=
        Finset.sum_congr rfl fun j _ => (Measure.addHaar_ball_center volume _ _).symm
    _ = volume (⋃ j ∈ Finset.range N,
          Metric.ball (a + ((j : ℝ) * (2 * r) / D) • (x - a)) (r / 2)) :=
        (measure_biUnion_finset hdisj fun _ _ => measurableSet_ball).symm
    _ ≤ volume S := measure_mono hsub

/-- **A convex set with an interior point and finite volume is bounded.**

The crux of this module, and the step Mathlib does not provide.  Contrapositive of
`Ttc.nsmul_volume_ball_le_of_convex_of_not_isBounded`: an unbounded such set contains
`N` disjoint balls of a *fixed* positive radius for every `N`, so its volume dominates
every multiple of a fixed positive finite quantity and is therefore `⊤`. -/
theorem isBounded_of_convex_of_interior_of_volume_ne_top {S : Set (Space n)}
    (hc : Convex ℝ S) (hi : (interior S).Nonempty) (hv : volume S ≠ ⊤) :
    Bornology.IsBounded S := by
  by_contra hub
  obtain ⟨a, ha⟩ := hi
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 isOpen_interior a ha
  have hball : Metric.ball a r ⊆ S := hsub.trans interior_subset
  have hvpos : 0 < volume (Metric.ball (0 : Space n) (r / 2)) :=
    Metric.measure_ball_pos _ _ (by linarith)
  have hvtop : volume (Metric.ball (0 : Space n) (r / 2)) ≠ ⊤ := measure_ball_lt_top.ne
  have hvr : 0 < (volume (Metric.ball (0 : Space n) (r / 2))).toReal :=
    ENNReal.toReal_pos hvpos.ne' hvtop
  have key : ∀ N : ℕ,
      (N : ℝ) * (volume (Metric.ball (0 : Space n) (r / 2))).toReal ≤ (volume S).toReal := by
    intro N
    have h := ENNReal.toReal_mono hv
      (nsmul_volume_ball_le_of_convex_of_not_isBounded hc hr hball hub N)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h
  obtain ⟨N, hN⟩ :=
    exists_nat_gt ((volume S).toReal / (volume (Metric.ball (0 : Space n) (r / 2))).toReal)
  rw [div_lt_iff₀ hvr] at hN
  linarith [key N]

end ConvexBounded

section Payoff

variable {A : Type*} {n : ℕ}

/-! ## Steps 1–3, and the payoff -/

/-- **Step 1.**  `Ttc.volSol` is an `ENNReal.toReal` and `ENNReal.toReal ⊤ = 0`, so
positive volume already rules out infinite volume. -/
theorem volume_sol_ne_top_of_volSol_pos {M : A → Set (Space n)} {φ : BForm A}
    (hpos : 0 < volSol M φ) : volume (sol M φ) ≠ ⊤ :=
  (ENNReal.toReal_pos_iff.1 hpos).2.ne

/-- **Steps 2–4 for one cube.**  A cube of the DNF of a formula with positive volume,
whose region has an interior point, has bounded region: the region is convex
(`Ttc.convex_region`), of finite volume (it is a subset of `Sol(F)`, step 1), and has an
interior point by hypothesis — so the crux applies.

The interior hypothesis is what `Ttc.pruneForm` supplies by construction; it is *not*
derivable from `hpos` (`Ttc.hint_not_derivable`). -/
theorem isBounded_region_of_volSol_pos (atoms : A → LinAtom n) {φ : BForm A}
    {c : Cube A} (hc : c ∈ toDNFd φ)
    (hint : (interior (region (atomSet atoms) c)).Nonempty)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    Bornology.IsBounded (region (atomSet atoms) c) := by
  refine isBounded_of_convex_of_interior_of_volume_ne_top (convex_region atoms c) hint ?_
  exact ne_top_of_le_ne_top (volume_sol_ne_top_of_volSol_pos hpos)
    (measure_mono (region_subset_sol (toDNFd_isDNFOf φ) hc))

/-- **The payoff: `Sol` of the pruned formula is bounded, from `hpos` alone.**

No `hbdd` anywhere.  Every surviving cube has nonempty interior by construction
(`Ttc.mem_nondegenCubes`) and finite volume by `hpos`, hence bounded region; the pruned
solution set is the *finite* union of those regions (`Ttc.sol_pruneForm`), hence
bounded.

This makes `Ttc.ttc_volume_estimate`'s `hbdd` binder redundant: every consumer of
`Ttc.pruneBdd` can be handed this term instead. -/
theorem isBounded_sol_pruneForm_of_volSol_pos (atoms : A → LinAtom n) {φ : BForm A}
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ) :
    Bornology.IsBounded (sol (atomSet atoms) (pruneForm atoms φ)) := by
  rw [sol_pruneForm atoms hφ (pruneNeNil atoms hpos)]
  have hfin : {c : Cube A | c ∈ nondegenCubes (atomSet atoms) (toDNFd φ)}.Finite :=
    List.finite_toSet _
  refine (Bornology.isBounded_biUnion (f := fun c => region (atomSet atoms) c) hfin).2 ?_
  intro c hc
  exact isBounded_region_of_volSol_pos atoms (nondegenCubes_subset hc)
    (mem_nondegenCubes.1 hc).2 hpos

/-- **The drop-in check.**  `Ttc.pruneBdd` and `Ttc.isBounded_sol_pruneForm_of_volSol_pos`
prove the *same* proposition, the second without `hbdd`.  The `rfl` is proof
irrelevance, but the statement only elaborates if the two types agree — which is the
mechanical content: every occurrence of `pruneBdd atoms hφ hbdd hpos` (in
`Ttc.ttc_volume_prune` and in `Ttc.ttcInput_bdd`, the only two consumers of `hbdd` in
the whole chain) may be replaced by `isBounded_sol_pruneForm_of_volSol_pos atoms hφ
hpos`, after which `hbdd` occurs nowhere. -/
theorem pruneBdd_eq_isBounded_sol_pruneForm_of_volSol_pos (atoms : A → LinAtom n)
    {φ : BForm A} (hφ : φ.IsPositive)
    (hbdd : Bornology.IsBounded (sol (atomSet atoms) φ))
    (hpos : 0 < volSol (atomSet atoms) φ) :
    pruneBdd atoms hφ hbdd hpos = isBounded_sol_pruneForm_of_volSol_pos atoms hφ hpos :=
  rfl

end Payoff

end Ttc

/-! ## Axiom profile -/

#print axioms Ttc.ball_combo_subset_of_convex
#print axioms Ttc.nsmul_volume_ball_le_of_convex_of_not_isBounded
#print axioms Ttc.isBounded_of_convex_of_interior_of_volume_ne_top
#print axioms Ttc.volume_sol_ne_top_of_volSol_pos
#print axioms Ttc.isBounded_region_of_volSol_pos
#print axioms Ttc.isBounded_sol_pruneForm_of_volSol_pos
#print axioms Ttc.pruneBdd_eq_isBounded_sol_pruneForm_of_volSol_pos
