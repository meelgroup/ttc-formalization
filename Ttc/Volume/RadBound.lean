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
and that is what this file supplies — up to one step which the present definition of
`rad` makes unprovable, and which is isolated below as a hypothesis so that the
obstruction is visible rather than hidden.

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
* `Ttc.MonteCarlo.nSamp_roundBody_le` — the two combined, at `R = roundRad γ K`.

**The bound is exponential in the dimension `n`, and that is the honest answer.**
`hitData` carries the factor `(rad K)⁻ⁿ`: hit-and-miss Monte Carlo needs `Θ(Rⁿ)`
samples to hit a body of inradius `1` inside a ball of radius `R`, and no rearrangement
of the argument avoids it. The closed form is

    nSamp (roundBody c γ K) ε p  ≤  ⌈(γ⁻¹·diam K + 1)ⁿ / (ε²·p)⌉₊ + 1 ,

i.e. `Θ((diam K / γ)ⁿ / (ε²·p))`. There is no polynomial bound to be had here; this
file makes the exponential one explicit, it does not make it smaller. Nothing in it
bounds a *running time* — see `Ttc/Exec/Complexity.lean` §4.

## The obstruction: `rad` is a `Classical.choose`

`Ttc.MonteCarlo.rad K = if h : ∃ R, 0 < R ∧ K ⊆ Metric.ball 0 R then h.choose else 1`
(`Model/Pseudocode.lean`). The **only** facts about `h.choose` that `Exists.choose_spec`
supplies are `0 < h.choose` and `K ⊆ Metric.ball 0 h.choose`. Both are *lower*-bound
information: the set of reals satisfying them is upward closed, so it is unbounded
above, and therefore **no inequality `rad K ≤ R` is derivable for any `R`**. Producing an
explicit ball around `roundBody` (which this file does) does not help: it only exhibits
one more valid radius, and `choose` is under no obligation to have picked it or anything
near it. This is exactly the note already carried by `Ttc.mcVolCoins` and
`Ttc.ttcCoinAndStepCharge_le_sum`.

Hence `Ttc.MonteCarlo.nSamp_roundBody_le` takes `rad (roundBody c γ K) ≤ roundRad γ K`
as an explicit hypothesis. **It is not an assumption of the development** — nothing
imports this file to discharge it, and no `def`, `structure` or `axiom` here asserts
it. It is the precise statement of what the current definition of `rad` withholds.

## The fix, and why it is not applied here

Replace the `Classical.choose` by the **infimum** of the valid radii:

```lean
noncomputable def rad (K : Set (Space n)) : ℝ :=
  if ∃ R : ℝ, 0 < R ∧ K ⊆ Metric.ball (0 : Space n) R
  then sInf {R : ℝ | 0 < R ∧ K ⊆ Metric.ball (0 : Space n) R} + 1 else 1
```

`Ttc.MonteCarlo.radMin` below **is** that definition, and the three theorems
`Ttc.MonteCarlo.radMin_pos`, `Ttc.MonteCarlo.subset_ball_radMin`,
`Ttc.MonteCarlo.radMin_le_of_subset_closedBall` show it keeps both properties the
present `rad` has, verbatim, and adds the missing upper bound. The `+ 1` is not
cosmetic: `sInf` of the valid radii need not itself be valid (take `K` a closed ball),
and it opens the ball again.

Adopting it touches exactly two files, neither of which this file owns:

1. `Ttc/Model/Pseudocode.lean:848–851` — the body of `Ttc.MonteCarlo.rad`, replaced by
   the block above. Its *type* is unchanged, so no downstream statement moves.
2. `Ttc/Volume/MonteCarlo.lean:144–159` — the proofs of `Ttc.MonteCarlo.rad_pos` and
   `Ttc.MonteCarlo.subset_ball_rad`, whose current one-liners go through
   `Exists.choose_spec`. Their *statements* are unchanged; the replacement proofs are
   `Ttc.MonteCarlo.radMin_pos` and `Ttc.MonteCarlo.subset_ball_radMin` verbatim. A
   third theorem, `Ttc.MonteCarlo.radMin_le_of_subset_closedBall`, is added there.

Nothing else in the development sees `rad`'s body: outside those two files only
`rad_pos`, `rad_ne_zero`, `rad_pow_pos` and `subset_ball_rad` are ever used, and every
one of them survives. `Ttc.MonteCarlo.radMin_roundBody_le` is the payoff waiting for it
— with the swap made, it discharges `Ttc.MonteCarlo.nSamp_roundBody_le`'s `hrad` and the
closed form becomes unconditional.
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

/-! ## §3. The two halves joined, at the run's own body

`hrad` is the step the present `Ttc.MonteCarlo.rad` cannot supply — see the module
docstring. Everything else is discharged. -/

/-- **The closed form at the body the run actually calls `Vol_ED` on.**

    nSamp (roundBody c γ K) ε p ≤ ⌈(γ⁻¹·diam K + 1)ⁿ / (ε²·p)⌉₊ + 1

`hrad` is **not** an assumption of the development: it is the inequality
`Ttc.MonteCarlo.rad`'s `Classical.choose` withholds, isolated so that it is visible.
`Ttc.MonteCarlo.radMin_roundBody_le` below proves the corresponding statement for the
proposed replacement `Ttc.MonteCarlo.radMin`. -/
theorem nSamp_roundBody_le {c : Space n} {γ ε pf : ℝ} {K : Set (Space n)}
    (hγ : 0 < γ) (hε : 0 < ε) (hpf : 0 < pf) (hball : Metric.ball c γ ⊆ K)
    (hfin : volume K ≠ ⊤)
    (hrad : rad (roundBody c γ K) ≤ roundRad γ K) :
    nSamp (roundBody c γ K) ε pf ≤ ⌈roundRad γ K ^ n / (ε ^ 2 * pf)⌉₊ + 1 :=
  nSamp_le_of_rad_le (roundRad_pos hγ) hε hpf hrad
    (ball_subset_roundBody hγ hball) (volume_roundBody_ne_top hγ hfin)

/-! ## §4. `radMin`: the definition `rad` would have to become

Everything below is about `Ttc.MonteCarlo.radMin`, a *new* definition local to this
file. It is not used anywhere: it exists to show that the replacement proposed in the
module docstring keeps the two properties the development consumes and gains the one it
needs. Substituting it for `Ttc.MonteCarlo.rad` in `Ttc/Model/Pseudocode.lean` — a file
this agent does not own — turns `Ttc.MonteCarlo.nSamp_roundBody_le`'s hypothesis into a
theorem. -/

open scoped Classical in
/-- **The least enclosing radius, plus one.** The `Classical.choose`-free replacement
for `Ttc.MonteCarlo.rad`: same shape, same default `1` when no radius exists, but
`sInf` in place of `Exists.choose`, so an upper bound is derivable. -/
noncomputable def radMin (K : Set (Space n)) : ℝ :=
  if ∃ R : ℝ, 0 < R ∧ K ⊆ Metric.ball (0 : Space n) R
  then sInf {R : ℝ | 0 < R ∧ K ⊆ Metric.ball (0 : Space n) R} + 1 else 1

/-- The valid radii are bounded below by `0`. -/
theorem bddBelow_radSet (K : Set (Space n)) :
    BddBelow {R : ℝ | 0 < R ∧ K ⊆ Metric.ball (0 : Space n) R} :=
  ⟨0, fun _ hR => hR.1.le⟩

theorem sInf_radSet_nonneg (K : Set (Space n))
    (h : ∃ R : ℝ, 0 < R ∧ K ⊆ Metric.ball (0 : Space n) R) :
    0 ≤ sInf {R : ℝ | 0 < R ∧ K ⊆ Metric.ball (0 : Space n) R} :=
  le_csInf h fun _ hR => hR.1.le

/-- **`radMin` is positive** — `Ttc.MonteCarlo.rad_pos`, verbatim. -/
theorem radMin_pos (K : Set (Space n)) : 0 < radMin K := by
  classical
  rw [radMin]
  split_ifs with h
  · have := sInf_radSet_nonneg K h; linarith
  · exact one_pos

/-- **`radMin` encloses `K`** — `Ttc.MonteCarlo.subset_ball_rad`, verbatim. -/
theorem subset_ball_radMin {K : Set (Space n)}
    (h : ∃ R : ℝ, 0 < R ∧ K ⊆ Metric.ball (0 : Space n) R) :
    K ⊆ Metric.ball (0 : Space n) (radMin K) := by
  classical
  intro x hx
  rw [radMin, if_pos h, mem_ball_zero_iff]
  have hle : ‖x‖ ≤ sInf {R : ℝ | 0 < R ∧ K ⊆ Metric.ball (0 : Space n) R} :=
    le_csInf h fun R hR => (mem_ball_zero_iff.mp (hR.2 hx)).le
  linarith

/-- **The bound `rad` cannot give.** Any closed ball enclosing `K` bounds `radMin`. -/
theorem radMin_le_of_subset_closedBall {K : Set (Space n)} {D : ℝ} (hD : 0 ≤ D)
    (hsub : K ⊆ Metric.closedBall (0 : Space n) D) : radMin K ≤ D + 1 := by
  classical
  have hex : ∃ R : ℝ, 0 < R ∧ K ⊆ Metric.ball (0 : Space n) R :=
    ⟨D + 1, by linarith, hsub.trans (Metric.closedBall_subset_ball (by linarith))⟩
  have hkey : sInf {R : ℝ | 0 < R ∧ K ⊆ Metric.ball (0 : Space n) R} ≤ D := by
    refine le_of_forall_pos_le_add fun t ht => ?_
    refine csInf_le (bddBelow_radSet K) ?_
    exact ⟨by linarith, hsub.trans (Metric.closedBall_subset_ball (by linarith))⟩
  rw [radMin, if_pos hex]
  linarith

/-- **The payoff.** With `radMin` in place of `rad`, the hypothesis of
`Ttc.MonteCarlo.nSamp_roundBody_le` is a theorem: the normalised body's least enclosing
radius is at most the explicit `Ttc.roundRad`. -/
theorem radMin_roundBody_le {c : Space n} {γ : ℝ} {K : Set (Space n)} (hγ : 0 < γ)
    (hball : Metric.ball c γ ⊆ K) (hbdd : Bornology.IsBounded K) :
    radMin (roundBody c γ K) ≤ roundRad γ K :=
  radMin_le_of_subset_closedBall
    (mul_nonneg (inv_pos.mpr hγ).le Metric.diam_nonneg)
    (roundBody_subset_closedBall hγ hball hbdd)

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
#print axioms Ttc.MonteCarlo.nSamp_roundBody_le
#print axioms Ttc.MonteCarlo.radMin
#print axioms Ttc.MonteCarlo.bddBelow_radSet
#print axioms Ttc.MonteCarlo.sInf_radSet_nonneg
#print axioms Ttc.MonteCarlo.radMin_pos
#print axioms Ttc.MonteCarlo.subset_ball_radMin
#print axioms Ttc.MonteCarlo.radMin_le_of_subset_closedBall
#print axioms Ttc.MonteCarlo.radMin_roundBody_le
