/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.Bridge
import Ttc.Volume.MonteCarlo

/-!
# `Volume/RadBound`: a closed form for the constructed `Vol_ED`'s sample count

`Ttc.mcVolCoins` — the number of coins the constructed volume oracle reads on one
cube — is `Ttc.MonteCarlo.nSamp` of the cube's **normalised** region, and `nSamp`
is `⌈(ε²·p·q)⁻¹⌉₊ + 1` with `q = Ttc.MonteCarlo.hitData K = (rad K)⁻ⁿ·Vol K / Vol(B₁)`.
So a closed form for the coin count needs an **upper bound on `Ttc.MonteCarlo.rad`**,
and that is what this file supplies — **unconditionally**, now that
`Ttc.MonteCarlo.rad` (`Model/Pseudocode`) is the *infimum* of the valid radii rather
than an `Exists.choose` of one.

## What is proved here, unconditionally

* `Ttc.roundRad γ K = γ⁻¹·diam K + 1` and
  `Ttc.roundBody_subset_ball : roundBody c γ K ⊆ Metric.ball 0 (roundRad γ K)` —
  the normalised body the run actually calls `Vol_ED` on **is** enclosed by an
  explicit ball, computed from the run's own data: the inscribed radius `γ`
  (`Ttc.autoGamma`, dilated by `Ttc.runScale`) and the metric diameter of the
  region, the same quantity `Ttc.canonDm` already names for the sampler.
  Hypotheses: `0 < γ` (`Ttc.TtcProb.hgammaHat`), `Metric.ball c γ ⊆ K` (the inscribed
  ball — the field `Ttc.TtcProb.ball_subset`, `Ttc/TtcProb.lean:155`), and
  `Bornology.IsBounded K` (`Ttc.isBounded_region_of_isBounded_sol`,
  `Ttc/Exec/Geometry.lean:114`, from the input condition
  `Bornology.IsBounded (sol M φ)`).  Convexity and finiteness of the volume are *not*
  needed for the containment; finiteness reappears only in §2.
* `Ttc.MonteCarlo.hitData_ge_of_rad_le` and `Ttc.MonteCarlo.nSamp_le_of_rad_le` — from
  *any* upper bound `rad K ≤ R` the sample count is at most `⌈Rⁿ/(ε²·p)⌉₊ + 1`.
* `Ttc.MonteCarlo.rad_le_of_subset_closedBall` — **the upper bound `Exists.choose` could
  not give**: any enclosing *closed* ball of radius `D` gives `rad K ≤ D + 1`.  It is a
  three-line consequence of `rad`'s `sInf`, and it is what makes everything below
  hypothesis-free.
* `Ttc.MonteCarlo.rad_roundBody_le` — that bound at the normalised body:
  `rad (roundBody c γ K) ≤ roundRad γ K`.
* `Ttc.MonteCarlo.nSamp_roundBody_le` — all of it combined, at `R = roundRad γ K`, with
  **no hypothesis about `rad`**.

**The bound is exponential in the dimension `n`, and that is the honest answer.**
`hitData` carries the factor `(rad K)⁻ⁿ`: hit-and-miss Monte Carlo needs `Θ(Rⁿ)`
samples to hit a body of inradius `1` inside a ball of radius `R`, and no rearrangement
of the argument avoids it. The closed form is

    nSamp (roundBody c γ K) ε p  ≤  ⌈(γ⁻¹·diam K + 1)ⁿ / (ε²·p)⌉₊ + 1 ,

i.e. `Θ((diam K / γ)ⁿ / (ε²·p))`. There is no polynomial bound to be had here; this
file makes the exponential one explicit, it does not make it smaller. Nothing in it
bounds a *running time* — see `Ttc/Exec/Complexity.lean` §4.

## What used to be the obstruction, and how it was removed

`Ttc.MonteCarlo.rad` used to be `if h : ∃ R, 0 < R ∧ K ⊆ Metric.ball 0 R then h.choose
else 1`. The **only** facts `Exists.choose_spec` supplies about `h.choose` are
`0 < h.choose` and `K ⊆ Metric.ball 0 h.choose`, and both are *lower*-bound information:
the set of reals satisfying them is upward closed, hence unbounded above, so **no
inequality `rad K ≤ R` was derivable for any `R`**. Producing an explicit ball around
`roundBody` did not help — it only exhibited one more valid radius, and `choose` is under
no obligation to have picked it or anything near it. `Ttc.MonteCarlo.nSamp_roundBody_le`
therefore carried `rad (roundBody c γ K) ≤ roundRad γ K` as an explicit hypothesis.

`rad` is now the **infimum** of the valid radii, plus one (`Model/Pseudocode`):

```lean
noncomputable def rad (K : Set (Space n)) : ℝ :=
  if ∃ R : ℝ, 0 < R ∧ K ⊆ Metric.ball (0 : Space n) R
  then sInf {R : ℝ | 0 < R ∧ K ⊆ Metric.ball (0 : Space n) R} + 1 else 1
```

The `+ 1` is not cosmetic: `sInf` of the valid radii need not itself be valid (take `K` a
closed ball), and it reopens the ball, so `Ttc.MonteCarlo.subset_ball_rad` survives
verbatim. `Ttc.MonteCarlo.rad_le_of_subset_closedBall` below is the inequality the old
definition withheld, and `Ttc.MonteCarlo.rad_roundBody_le` is it at the run's own body,
so **`Ttc.MonteCarlo.nSamp_roundBody_le` now carries no hypothesis about `rad` at all**.

`Ttc.mcVolCoins` and `Ttc.ttcCoinAndStepCharge_le_sum` carried a note saying that no
closed form for the coin count existed. That note is superseded by this file, and
`Ttc/Exec/PriceList.lean` is where the closed form is carried to the run's own price
list, uniformly over the DNF's cubes.
-/

namespace Ttc

open MeasureTheory Metric Set Pointwise

variable {n : ℕ} {c : Space n} {γ : ℝ} {K : Set (Space n)}

/-! ## §1. An explicit ball enclosing the normalised body

`Ttc.roundBody c γ K = γ⁻¹ • ((−c) +ᵥ K)` is `K` recentred at its inscribed ball's
centre and shrunk by the inradius. Its points are `γ⁻¹·(y − c)` for `y ∈ K`, and
`c ∈ K`, so their norms are at most `γ⁻¹·diam K`. -/

/-- **The centre of an inscribed ball lies in the body.** -/
theorem mem_of_ball_subset (hγ : 0 < γ) (hball : Metric.ball c γ ⊆ K) : c ∈ K :=
  hball (Metric.mem_ball_self hγ)

/-- **Every point of the normalised body has norm at most `γ⁻¹·diam K`.** -/
theorem norm_le_of_mem_roundBody (hγ : 0 < γ) (hc : c ∈ K)
    (hbdd : Bornology.IsBounded K) {x : Space n} (hx : x ∈ roundBody c γ K) :
    ‖x‖ ≤ γ⁻¹ * Metric.diam K := by
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨z, hz, rfl⟩ := hy
  have hdist : dist z c ≤ Metric.diam K := Metric.dist_le_diam_of_mem hbdd hz hc
  have hnorm : ‖(-c) +ᵥ z‖ = dist z c := by
    rw [vadd_eq_add, dist_eq_norm, neg_add_eq_sub]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hγ), hnorm]
  exact mul_le_mul_of_nonneg_left hdist (inv_pos.mpr hγ).le

/-- **The explicit enclosing radius of the normalised body**, `γ⁻¹·diam K + 1`.

Every ingredient is data the run already has: `γ` is the dilated inscribed radius
`Ttc.ttcScaledRadius` (`Ttc.runScale · Ttc.autoGamma`) and `Metric.diam K` is the
region's diameter, the quantity `Ttc.canonDm` names for the sampler. The `+ 1` opens
the ball: the sharp containment is in a *closed* ball of radius `γ⁻¹·diam K`
(`Ttc.roundBody_subset_closedBall`).

The name is discharged by `Ttc.roundBody_subset_ball`; it does not stand in for an
unproved identification. -/
noncomputable def roundRad (γ : ℝ) (K : Set (Space n)) : ℝ :=
  γ⁻¹ * Metric.diam K + 1

theorem roundRad_def (γ : ℝ) (K : Set (Space n)) :
    roundRad γ K = γ⁻¹ * Metric.diam K + 1 := rfl

theorem roundRad_pos (hγ : 0 < γ) : 0 < roundRad γ K := by
  have h : 0 ≤ γ⁻¹ * Metric.diam K :=
    mul_nonneg (inv_pos.mpr hγ).le Metric.diam_nonneg
  rw [roundRad]; linarith

/-- **Deliverable 1, sharp form.** -/
theorem roundBody_subset_closedBall (hγ : 0 < γ) (hball : Metric.ball c γ ⊆ K)
    (hbdd : Bornology.IsBounded K) :
    roundBody c γ K ⊆ Metric.closedBall (0 : Space n) (γ⁻¹ * Metric.diam K) := by
  intro x hx
  rw [mem_closedBall_zero_iff]
  exact norm_le_of_mem_roundBody hγ (mem_of_ball_subset hγ hball) hbdd hx

/-- **Deliverable 1.** The body the run calls `Vol_ED` on is enclosed by an explicit
ball, computed from the inscribed radius and the region's diameter. -/
theorem roundBody_subset_ball (hγ : 0 < γ) (hball : Metric.ball c γ ⊆ K)
    (hbdd : Bornology.IsBounded K) :
    roundBody c γ K ⊆ Metric.ball (0 : Space n) (roundRad γ K) := by
  refine (roundBody_subset_closedBall hγ hball hbdd).trans ?_
  exact Metric.closedBall_subset_ball (by rw [roundRad]; linarith)

/-- The enclosing radius exists for the normalised body — the hypothesis
`Ttc.MonteCarlo.subset_ball_rad` consumes, now witnessed *explicitly* rather than
through `Arlib.Convexity.exists_closedBall_superset_of_convex`. Convexity and
finiteness of the volume are not needed. -/
theorem exists_ball_superset_roundBody (hγ : 0 < γ) (hball : Metric.ball c γ ⊆ K)
    (hbdd : Bornology.IsBounded K) :
    ∃ R : ℝ, 0 < R ∧ roundBody c γ K ⊆ Metric.ball (0 : Space n) R :=
  ⟨roundRad γ K, roundRad_pos hγ, roundBody_subset_ball hγ hball hbdd⟩

end Ttc

namespace Ttc.MonteCarlo

open MeasureTheory Metric Set

variable {n : ℕ}

/-! ## §2. From an upper bound on the radius to a closed form for the sample count

Both steps are pure arithmetic once `rad K ≤ R` is available. The lower bound on the
hitting probability needs the unit ball inside `K` — which is what `roundBody` is built
to provide (`Ttc.ball_subset_roundBody`) — and finiteness of `Vol K`. -/

/-- **Deliverable 3.** An explicit positive lower bound on the hitting probability:
a body containing the unit ball and enclosed by a ball of radius `R` is hit with
probability at least `R⁻ⁿ`. -/
theorem hitData_ge_of_rad_le {K : Set (Space n)} {R : ℝ} (hR : 0 < R)
    (hrad : rad K ≤ R) (hball : Metric.ball (0 : Space n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) : (R ^ n)⁻¹ ≤ hitData K := by
  have hrpos : 0 < rad K := rad_pos K
  have hupos : 0 < (volume (Metric.ball (0 : Space n) 1)).toReal :=
    volume_unitBall_toReal_pos
  have hvol : (volume (Metric.ball (0 : Space n) 1)).toReal ≤ (volume K).toReal :=
    ENNReal.toReal_mono hfin (measure_mono hball)
  have hpow : rad K ^ n ≤ R ^ n := pow_le_pow_left₀ hrpos.le hrad n
  have hpowpos : (0 : ℝ) < rad K ^ n := rad_pow_pos K n
  have hRpow : (0 : ℝ) < R ^ n := pow_pos hR n
  have hinv : (R ^ n)⁻¹ ≤ (rad K ^ n)⁻¹ := by
    exact one_div (R ^ n) ▸ one_div (rad K ^ n) ▸ one_div_le_one_div_of_le hpowpos hpow
  rw [hitData, le_div_iff₀ hupos]
  calc (R ^ n)⁻¹ * (volume (Metric.ball (0 : Space n) 1)).toReal
      ≤ (rad K ^ n)⁻¹ * (volume (Metric.ball (0 : Space n) 1)).toReal := by
        exact mul_le_mul_of_nonneg_right hinv hupos.le
    _ ≤ (rad K ^ n)⁻¹ * (volume K).toReal := by
        exact mul_le_mul_of_nonneg_left hvol (inv_pos.mpr hpowpos).le

/-- **Deliverable 4.** The closed form for the sample count: `⌈Rⁿ/(ε²·p)⌉₊ + 1`.

**Exponential in `n`** — see the module docstring. -/
theorem nSamp_le_of_rad_le {K : Set (Space n)} {R ε pf : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (hpf : 0 < pf) (hrad : rad K ≤ R) (hball : Metric.ball (0 : Space n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) :
    nSamp K ε pf ≤ ⌈R ^ n / (ε ^ 2 * pf)⌉₊ + 1 := by
  have hRpow : (0 : ℝ) < R ^ n := pow_pos hR n
  have hq : (R ^ n)⁻¹ ≤ hitData K := hitData_ge_of_rad_le hR hrad hball hfin
  have hq0 : (0 : ℝ) < (R ^ n)⁻¹ := inv_pos.mpr hRpow
  have hcoef : (0 : ℝ) < ε ^ 2 * pf := by positivity
  have hmul : ε ^ 2 * pf * (R ^ n)⁻¹ ≤ ε ^ 2 * pf * hitData K :=
    mul_le_mul_of_nonneg_left hq hcoef.le
  have hlt : (0 : ℝ) < ε ^ 2 * pf * (R ^ n)⁻¹ := by positivity
  have hinv : (ε ^ 2 * pf * hitData K)⁻¹ ≤ (ε ^ 2 * pf * (R ^ n)⁻¹)⁻¹ :=
    one_div (ε ^ 2 * pf * hitData K) ▸ one_div (ε ^ 2 * pf * (R ^ n)⁻¹) ▸
      one_div_le_one_div_of_le hlt hmul
  have heq : (ε ^ 2 * pf * (R ^ n)⁻¹)⁻¹ = R ^ n / (ε ^ 2 * pf) := by
    field_simp
  rw [nSamp]
  exact Nat.add_le_add_right (Nat.ceil_le_ceil (heq ▸ hinv)) 1

/-! ## §3. The upper bound on `rad` that the `sInf` definition supplies

Three lines, and they are the whole of what changed: `rad K` is `sInf` of the valid radii
plus one, `sInf` is bounded above by every element of a set bounded below, and an
enclosing *closed* ball of radius `D` puts `D + t` in that set for every `t > 0`. -/

/-- The valid radii are bounded below by `0`. -/
theorem bddBelow_radSet (K : Set (Space n)) :
    BddBelow {R : ℝ | 0 < R ∧ K ⊆ Metric.ball (0 : Space n) R} :=
  ⟨0, fun _ hR => hR.1.le⟩

theorem sInf_radSet_nonneg (K : Set (Space n))
    (h : ∃ R : ℝ, 0 < R ∧ K ⊆ Metric.ball (0 : Space n) R) :
    0 ≤ sInf {R : ℝ | 0 < R ∧ K ⊆ Metric.ball (0 : Space n) R} :=
  le_csInf h fun _ hR => hR.1.le

/-- **The bound `Exists.choose` could not give.** Any closed ball enclosing `K` bounds
`Ttc.MonteCarlo.rad`. -/
theorem rad_le_of_subset_closedBall {K : Set (Space n)} {D : ℝ} (hD : 0 ≤ D)
    (hsub : K ⊆ Metric.closedBall (0 : Space n) D) : rad K ≤ D + 1 := by
  classical
  have hex : ∃ R : ℝ, 0 < R ∧ K ⊆ Metric.ball (0 : Space n) R :=
    ⟨D + 1, by linarith, hsub.trans (Metric.closedBall_subset_ball (by linarith))⟩
  have hkey : sInf {R : ℝ | 0 < R ∧ K ⊆ Metric.ball (0 : Space n) R} ≤ D := by
    refine le_of_forall_pos_le_add fun t ht => ?_
    refine csInf_le (bddBelow_radSet K) ?_
    exact ⟨by linarith, hsub.trans (Metric.closedBall_subset_ball (by linarith))⟩
  rw [rad, if_pos hex]
  linarith

/-- **The bound at the run's own body**: the normalised body's least enclosing radius is
at most the explicit `Ttc.roundRad`.  This is what discharges the hypothesis
`Ttc.MonteCarlo.nSamp_roundBody_le` used to carry. -/
theorem rad_roundBody_le {c : Space n} {γ : ℝ} {K : Set (Space n)} (hγ : 0 < γ)
    (hball : Metric.ball c γ ⊆ K) (hbdd : Bornology.IsBounded K) :
    rad (roundBody c γ K) ≤ roundRad γ K :=
  rad_le_of_subset_closedBall
    (mul_nonneg (inv_pos.mpr hγ).le Metric.diam_nonneg)
    (roundBody_subset_closedBall hγ hball hbdd)

/-! ## §4. The two halves joined, at the run's own body

No hypothesis about `Ttc.MonteCarlo.rad` remains: the geometry (`hγ`, `hball`, `hbdd`)
and the parameter range (`hε`, `hpf`) are all of it. -/

/-- **The closed form at the body the run actually calls `Vol_ED` on.**

    nSamp (roundBody c γ K) ε p ≤ ⌈(γ⁻¹·diam K + 1)ⁿ / (ε²·p)⌉₊ + 1

**Unconditional in `rad`** — `Ttc.MonteCarlo.rad_roundBody_le` supplies the enclosing
radius from `rad`'s own `sInf`.  **Exponential in `n`** — see the module docstring. -/
theorem nSamp_roundBody_le {c : Space n} {γ ε pf : ℝ} {K : Set (Space n)}
    (hγ : 0 < γ) (hε : 0 < ε) (hpf : 0 < pf) (hball : Metric.ball c γ ⊆ K)
    (hbdd : Bornology.IsBounded K) (hfin : volume K ≠ ⊤) :
    nSamp (roundBody c γ K) ε pf ≤ ⌈roundRad γ K ^ n / (ε ^ 2 * pf)⌉₊ + 1 :=
  nSamp_le_of_rad_le (roundRad_pos hγ) hε hpf (rad_roundBody_le hγ hball hbdd)
    (ball_subset_roundBody hγ hball) (volume_roundBody_ne_top hγ hfin)

end Ttc.MonteCarlo

/-! ## Axiom profile

Every declaration in this file is `sorry`-free and depends only on Lean's three
standard axioms. Re-check with `lake build Ttc.Volume.RadBound`. -/

#print axioms Ttc.mem_of_ball_subset
#print axioms Ttc.norm_le_of_mem_roundBody
#print axioms Ttc.roundRad
#print axioms Ttc.roundRad_def
#print axioms Ttc.roundRad_pos
#print axioms Ttc.roundBody_subset_closedBall
#print axioms Ttc.roundBody_subset_ball
#print axioms Ttc.exists_ball_superset_roundBody
#print axioms Ttc.MonteCarlo.hitData_ge_of_rad_le
#print axioms Ttc.MonteCarlo.nSamp_le_of_rad_le
#print axioms Ttc.MonteCarlo.bddBelow_radSet
#print axioms Ttc.MonteCarlo.sInf_radSet_nonneg
#print axioms Ttc.MonteCarlo.rad_le_of_subset_closedBall
#print axioms Ttc.MonteCarlo.rad_roundBody_le
#print axioms Ttc.MonteCarlo.nSamp_roundBody_le
