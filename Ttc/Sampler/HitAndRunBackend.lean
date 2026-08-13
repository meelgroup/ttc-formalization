/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.MarkovChains.Continuous.ConductanceToTV
import Arlib.MarkovChains.Continuous.SpeedyAffine
import Ttc.Sampler.HitAndRunTheorem11

/-!
# A hit-and-run backend: closing every seam between the proved theorem and the contract

`Ttc.HitAndRunTheorem11Input` (`Ttc/Sampler/HitAndRunTheorem11.lean:94`) is a `structure`
whose single field `mixing` **assumes** Lovász–Vempala Theorem 1.1 in a very specific shape.
`Arlib.MarkovChains.tvLe_iterate_hitAndRun_unitBall`
(`Arlib/MarkovChains/Continuous/HitAndRunMixing.lean:944`) **proves** something close to that
shape, but not that shape: it is at inradius `r = 1`, its `hdom` hypothesis is written against
`uniformOn volume K A` rather than `uniformOn volume K (A \ S)`, and its deadline is spelt
`Arlib.MarkovChains.lvThreshold` rather than `Ttc.hitAndRunTheorem11Threshold`.

This file closes **all three** of those gaps, plus the transport of the start law, and then
applies the constructor.  Every declaration below is a `theorem`; there is no `def`, no
`structure`, no `class`, no `axiom`, no `sorry`, no `admit` and no `native_decide`.

## Main results

* `Ttc.lvThreshold_le_hitAndRunTheorem11Threshold` (§1) — **seam 3.**  The two thresholds are
  the *same function*: `lvThreshold n r R M eps` and `hitAndRunTheorem11Threshold n r R M eps`
  have byte-identical bodies, so `Ttc.lvThreshold_eq_hitAndRunTheorem11Threshold` is `rfl`.
  The inequality runs the right way — **nothing is lost at this seam** — and
  `Ttc.lvThreshold_unit_div_eq` records the version actually consumed after rescaling,
  `lvThreshold n 1 (R/r) M eps = hitAndRunTheorem11Threshold n r R M eps`.
* `Ttc.hdom_of_contract` (§2) — **seam 2.**  Since `A \ S ⊆ A`, the contract's
  `sigma (A \ S) ≤ M · π(A \ S)` is the **stronger** statement, so it implies the theorem's
  `sigma (A \ S) ≤ M · π(A)`.  The implication runs the right way; nothing is lost.
* §§3–5 — **seam 1, the `r → 1` rescaling.**  The chart is `z ↦ r • z + zin`, exactly the one
  `Arlib/MarkovChains/Continuous/SpeedyAffine.lean` uses for the speedy walk, so all of that
  file's generic transport (`tvLe_map`, `map_iterate_of_map_kernel`, `map_lazy_of_map_kernel`,
  `map_uniformOn_affineChart`, `volume_preimage_affineChart`, `dist_affineChart`) is reused
  rather than reproved.  The hit-and-run-specific content is:
  * `Ttc.map_hitAndRun_chart` — **the crux**:
    `Measure.map (fun z => r • z + zin) (hitAndRun ((fun z => r • z + zin) ⁻¹' K) y)
     = hitAndRun K (r • y + zin)`, for every `y`, with no membership hypothesis;
  * `Ttc.chordSet_chartPreimage`, `Ttc.setOf_chartPreimage`,
    `Ttc.uniformOn_preimage_mul_right`, `Ttc.hitAndRunProposal_chartPreimage` — its
    ingredients;
  * `Ttc.closedBall_one_subset_chartPreimage`, `Ttc.chartPreimage_subset_closedBall`,
    `Ttc.convex_chartPreimage`, `Ttc.isClosed_chartPreimage`,
    `Ttc.inradius_le_circumradius` — the geometry;
  * `Ttc.map_chart_map_invChart`, `Ttc.uniformOn_chartPreimage_apply`,
    `Ttc.hdom_chartPreimage`, `Ttc.tvLe_of_tvLe_chart` — the transport of the start law, the
    target and the exceptional-set hypothesis.
* `Ttc.tvLe_iterate_hitAndRun_at_contract_shape` (§6) — **seam 4.**  The conclusion of
  `Ttc.HitAndRunTheorem11Input.mixing`, byte for byte, proved, with only `hLem41`, `hIso` and
  `hLS` left as binders.
* `Ttc.hitAndRunTheorem11Input_of_binders` (§7) — **an actual
  `Ttc.HitAndRunTheorem11Input`**, given those three binders universally quantified over
  bodies.  This is the constructor application the audit looks for; it is conditional, and
  §"What this does NOT do" says exactly how conditional.
* `Ttc.tvLe_iterate_lazy_hitAndRun_at_contract_shape` (§8) — the same assembly over
  `Arlib.MarkovChains.lazy (Arlib.MarkovChains.hitAndRun K)`, where
  `Arlib/MarkovChains/Continuous/ConductanceToTV.lean` **discharges `hLS`**.  One fewer
  binder; a different kernel and a factor `4` in the deadline.
* `Ttc.tvLe_iterate_hitAndRun_ballTwo_dim2` (§9) — a witness that every hypothesis *other
  than* the three binders is simultaneously satisfiable, at `n = 2`, `K = B̄(0,2)`,
  `r = 1/2` (a genuinely non-trivial chart), `R = 2`, `M = 1`, `eps = 1/2`.

## Hit-and-run is equivariant under **similarities**, and that is what is used

The brief flagged a real risk: hit-and-run picks its direction from
`Arlib.MarkovChains.unifSphere n`, the uniform measure on the *Euclidean* unit sphere, so the
walk is **not** equivariant under a general affine map — an anisotropic linear map changes
which directions are likely.  It is equivariant under maps that preserve the sphere up to
scale, i.e. **similarities**.  `z ↦ r • z + zin` (a uniform scaling composed with a
translation) is one, and the proof of `Ttc.hitAndRunProposal_chartPreimage` makes the point
mechanically rather than by assertion: the direction `θ` is *literally the same variable on
both sides* of the identity, the `unifSphere n` factor is never touched, and the only thing
that moves is the chord parameter, `t ↦ t · r`.  `Ttc.uniformOn_preimage_mul_right` then shows
the uniform law on the chord does not notice that rescaling, because the Jacobian `|r⁻¹|`
appears in both the numerator and the denominator of `Arlib.uniformOn` and cancels.

This settles the item `Arlib/MarkovChains/Continuous/HitAndRunMixing.lean:168-180` flags as
"finite bookkeeping, not an open problem" — it is now finished bookkeeping.  Note the
docstring there still says the equivariance "is **not** proved in this repository"; that
sentence is stale as of this file, and the fix belongs in that file, not here.

## What this does NOT do

Read this before quoting anything above.

* **`Ttc.ttc` and `Ttc.ttcPoly` are not rewired.**  No existing file is edited by this one.
  No caller of `Ttc.HitAndRunTheorem11Input` is changed to use anything here, and the
  headline theorems keep whatever sampler they already had.
* **`Ttc.ttcSampPrice` is unchanged, and still exponential.**  Nothing here touches it.
* **This file makes nothing polynomial-time.**  Every theorem below is a Markov-chain
  *mixing* statement: after `m` applications of a kernel, the law is within total variation
  `eps` of `Arlib.uniformOn volume K`.  `m` counts abstract kernel applications.  Nothing
  bounds the cost of **one** step (which needs a membership oracle for `K`, a sample from the
  sphere, and a chord endpoint), nor bit complexity, nor oracle calls, and the deadline itself
  is `2⁵⁶ n² (R²/r²) log(8M/eps²)` — polynomial in `n` and the aspect ratio, but that is a
  *step count*, not a running time, and it is not a claim about TTC.
* **The three binders are unproved, here and elsewhere.**  `hLem41` (Lemma 4.1), `hIso`
  (Theorem 2.1, corrected) and `hLS` (Lovász–Simonovits Corollary 1.5 for the plain kernel)
  are carried verbatim.  §9 documents exactly why none of them is dischargeable today, and
  `hLS` for the plain kernel is a genuine gap **in the paper**
  (`Arlib/MarkovChains/Continuous/HitAndRunMixing.lean:204-210`), refuted for general
  reversible chains by a two-line counterexample on `Bool`.  So
  `Ttc.hitAndRunTheorem11Input_of_binders` is **not** a proof that
  `Ttc.HitAndRunTheorem11Input` is inhabited; it is a reduction of that question to three
  named statements.
* **The binders are consumed at the normalised body**
  `(fun z => r • z + zin) ⁻¹' K`, not at `K`.  Transporting `hLem41` and `hIso` back along the
  chart would need equivariance of `Arlib.crossRatioDist` and `Arlib.medianStep`, which is not
  proved here.  A caller holding the binders for *every* convex body (as
  `Ttc.hitAndRunTheorem11Input_of_binders` requires) loses nothing; a caller holding them only
  at `K` does not get the theorem.
* **The lazy route does not inhabit the contract.**  `Arlib/…/ConductanceToTV.lean` proves
  Theorem 1.1 with `hLS` discharged, but for `Arlib.MarkovChains.lazy
  (Arlib.MarkovChains.hitAndRun K)` at deadline `4 · lvThreshold`.  The contract asks for the
  **plain** kernel `Arlib.MarkovChains.hitAndRun K` at deadline `lvThreshold`.  These are
  different Markov chains and the conclusion does not transfer for free, so
  `Ttc.tvLe_iterate_lazy_hitAndRun_at_contract_shape` is stated separately and is **not** used
  to build the structure.  The honest options, both of which are interface decisions for a
  human and neither of which is taken here:
  1. amend `Ttc.HitAndRunTheorem11Input.mixing` to the lazy kernel and multiply the deadline
     by `4` — then `Ttc.tvLe_iterate_lazy_hitAndRun_at_contract_shape` inhabits it with only
     `hLem41` and `hIso` outstanding; or
  2. prove `hLS` for the plain hit-and-run kernel — which needs a hit-and-run-specific
     spectral fact, since the binder is *false* for general reversible chains.
  This file deliberately does **not** redefine, shadow or weaken the contract.
* **No non-vacuity claim.**  `Ttc.HitAndRunTheorem11Input` still has no unconditional witness,
  and §9 says why one is not available today.  `Ttc.tvLe_iterate_hitAndRun_ballTwo_dim2`
  certifies only that the *geometric* hypothesis bundle is satisfiable.
-/

namespace Ttc

open MeasureTheory Metric ProbabilityTheory
open scoped ENNReal

/-! ## 1. Seam: the threshold comparison -/

/-- The two thresholds are the **same function**. -/
theorem lvThreshold_eq_hitAndRunTheorem11Threshold (n : ℕ) (r R M eps : ℝ) :
    Arlib.MarkovChains.lvThreshold n r R M eps = hitAndRunTheorem11Threshold n r R M eps :=
  rfl

/-- Seam 3, in the direction a caller needs it. -/
theorem lvThreshold_le_hitAndRunTheorem11Threshold (n : ℕ) (r R M eps : ℝ) :
    Arlib.MarkovChains.lvThreshold n r R M eps ≤ hitAndRunTheorem11Threshold n r R M eps :=
  le_of_eq (lvThreshold_eq_hitAndRunTheorem11Threshold n r R M eps)

/-- The rescaled threshold. -/
theorem lvThreshold_unit_div_eq {n : ℕ} {r R M eps : ℝ} (hr : 0 < r) :
    Arlib.MarkovChains.lvThreshold n 1 (R / r) M eps
      = hitAndRunTheorem11Threshold n r R M eps := by
  unfold Arlib.MarkovChains.lvThreshold hitAndRunTheorem11Threshold
  rw [div_pow]
  field_simp

/-! ## 2. Seam: the `hdom` shape reconciliation -/

/-- Seam 2. -/
theorem hdom_of_contract {n : ℕ} {sigma : Measure (EuclideanSpace ℝ (Fin n))}
    {K S : Set (EuclideanSpace ℝ (Fin n))} {M : ℝ}
    (hdom : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      sigma (A \ S) ≤ ENNReal.ofReal M * Arlib.uniformOn volume K (A \ S)) :
    ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      sigma (A \ S) ≤ ENNReal.ofReal M * Arlib.uniformOn volume K A := by
  intro A hA
  exact (hdom A hA).trans (by gcongr; exact Set.sdiff_subset)

/-! ## 3. Seam: the `r → 1` chart, geometry -/

/-- The inverse chart `x ↦ (x − zin)/r` is measurable. -/
theorem measurable_invChart {n : ℕ} (r : ℝ) (zin : EuclideanSpace ℝ (Fin n)) :
    Measurable (fun x : EuclideanSpace ℝ (Fin n) => r⁻¹ • (x - zin)) := by
  fun_prop

/-- The chart and its inverse compose to the identity. -/
theorem chart_comp_invChart {n : ℕ} {r : ℝ} (hr : r ≠ 0) (zin : EuclideanSpace ℝ (Fin n)) :
    ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ∘
      fun x : EuclideanSpace ℝ (Fin n) => r⁻¹ • (x - zin)) = id := by
  funext x
  simp only [Function.comp_apply, id_eq, smul_smul, mul_inv_cancel₀ hr, one_smul]
  abel

/-- The inverse chart and the chart compose to the identity. -/
theorem invChart_comp_chart {n : ℕ} {r : ℝ} (hr : r ≠ 0) (zin : EuclideanSpace ℝ (Fin n)) :
    ((fun x : EuclideanSpace ℝ (Fin n) => r⁻¹ • (x - zin)) ∘
      fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) = id := by
  funext z
  simp only [Function.comp_apply, id_eq, add_sub_cancel_right, smul_smul,
    inv_mul_cancel₀ hr, one_smul]

/-- **The unit ball sits inside the normalised body.** -/
theorem closedBall_one_subset_chartPreimage {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {zin : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hin : closedBall zin r ⊆ K) :
    closedBall (0 : EuclideanSpace ℝ (Fin n)) 1
      ⊆ (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K := by
  intro y hy
  have hyn : ‖y‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hy
  refine hin ?_
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos hr]
  nlinarith [norm_nonneg y]

/-- **The normalised body sits inside a ball of radius `R/r`.** -/
theorem chartPreimage_subset_closedBall {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {zin zout : EuclideanSpace ℝ (Fin n)} {r R : ℝ} (hr : 0 < r)
    (hout : K ⊆ closedBall zout R) :
    (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K
      ⊆ closedBall (r⁻¹ • (zout - zin)) (R / r) := by
  intro y hy
  have h := mem_closedBall.1 (hout hy)
  rw [mem_closedBall, le_div_iff₀ hr]
  have hd : dist (r • y + zin) (r • (r⁻¹ • (zout - zin)) + zin) = r * dist y (r⁻¹ • (zout - zin)) :=
    Arlib.MarkovChains.dist_affineChart hr zin y (r⁻¹ • (zout - zin))
  rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, sub_add_cancel] at hd
  rw [mul_comm, ← hd]
  exact h

/-- **The normalised body is convex.** -/
theorem convex_chartPreimage {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (r : ℝ) (zin : EuclideanSpace ℝ (Fin n)) (hKc : Convex ℝ K) :
    Convex ℝ ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K) := by
  intro x hx y hy a b ha hb hab
  have hid : r • (a • x + b • y) + zin
      = a • (r • x + zin) + b • (r • y + zin) := by
    have h1 : a • (r • x + zin) + b • (r • y + zin)
        = (a + b) • zin + r • (a • x + b • y) := by module
    rw [h1, hab, one_smul]
    abel
  show r • (a • x + b • y) + zin ∈ K
  rw [hid]
  exact hKc hx hy ha hb hab

/-- **The normalised body is closed.** -/
theorem isClosed_chartPreimage {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (r : ℝ) (zin : EuclideanSpace ℝ (Fin n)) (hKcl : IsClosed K) :
    IsClosed ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K) :=
  hKcl.preimage (by fun_prop)

/-- **An inball radius never exceeds a circumball radius**, in dimension at least one.

Needed to feed `1 ≤ R/r` to the unit-inball theorems.  The two antipodal points
`zin ± r • e` (with `e` a coordinate unit vector) both lie in `closedBall zin r ⊆ K`, hence in
`closedBall zout R`, and they are `2r` apart. -/
theorem inradius_le_circumradius {n : ℕ} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {zin zout : EuclideanSpace ℝ (Fin n)} {r R : ℝ}
    (hr : 0 < r) (hin : closedBall zin r ⊆ K) (hout : K ⊆ closedBall zout R) : r ≤ R := by
  have hn0 : (0 : ℕ) < n := hn
  set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, hn0⟩ (1 : ℝ) with he
  have hne : ‖e‖ = 1 := by rw [he, PiLp.norm_single]; simp
  have hmem : ∀ s : ℝ, |s| ≤ 1 → zin + (r * s) • e ∈ closedBall zin r := by
    intro s hs
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hne,
      mul_one, abs_mul, abs_of_pos hr]
    nlinarith [abs_nonneg s]
  have h1 := mem_closedBall.1 (hout (hin (hmem 1 (by norm_num))))
  have h2 := mem_closedBall.1 (hout (hin (hmem (-1) (by norm_num))))
  have hdd : dist (zin + (r * 1) • e) (zin + (r * (-1)) • e) = 2 * r := by
    rw [dist_eq_norm, show zin + (r * 1) • e - (zin + (r * (-1)) • e) = (2 * r) • e by module,
      norm_smul, Real.norm_eq_abs, hne, mul_one, abs_of_pos (by linarith : (0:ℝ) < 2 * r)]
  have htri : dist (zin + (r * 1) • e) (zin + (r * (-1)) • e)
      ≤ dist (zin + (r * 1) • e) zout + dist zout (zin + (r * (-1)) • e) :=
    dist_triangle _ _ _
  rw [dist_comm zout] at htri
  rw [hdd] at htri
  linarith

/-! ## 4. Seam: the `r → 1` chart, equivariance of the kernel -/

/-- **The chord parameter set is equivariant.** -/
theorem chordSet_chartPreimage {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (r : ℝ) (zin y θ : EuclideanSpace ℝ (Fin n)) :
    Arlib.MarkovChains.chordSet
        ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K) y θ
      = (fun t : ℝ => t * r) ⁻¹'
          Arlib.MarkovChains.chordSet K (r • y + zin) θ := by
  ext t
  simp only [Arlib.MarkovChains.chordSet, Set.mem_setOf_eq, Set.mem_preimage]
  congr! 1
  module

/-- **The hitting set of a target, in chord parameters, is equivariant.** -/
theorem setOf_chartPreimage {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (r : ℝ) (zin y θ : EuclideanSpace ℝ (Fin n)) :
    {t : ℝ | y + t • θ ∈ (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' A}
      = (fun t : ℝ => t * r) ⁻¹' {s : ℝ | (r • y + zin) + s • θ ∈ A} := by
  ext t
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  congr! 1
  module

/-- **The uniform law on a line is invariant under rescaling the parameter.**  Both the
numerator and the denominator of `uniformOn` pick up the same Jacobian `|r⁻¹|`, so it
cancels — the one-dimensional shadow of `Arlib.MarkovChains.map_uniformOn_affineChart`. -/
theorem uniformOn_preimage_mul_right {r : ℝ} (hr : r ≠ 0) {C D : Set ℝ}
    (hC : MeasurableSet C) (hD : MeasurableSet D) :
    Arlib.uniformOn (volume : Measure ℝ) ((fun t : ℝ => t * r) ⁻¹' C)
        ((fun t : ℝ => t * r) ⁻¹' D)
      = Arlib.uniformOn (volume : Measure ℝ) C D := by
  have hmeas : Measurable (fun t : ℝ => t * r) := by fun_prop
  rw [Arlib.uniformOn_apply _ (hC.preimage hmeas) (hD.preimage hmeas),
    Arlib.uniformOn_apply _ hC hD, ← Set.preimage_inter,
    Real.volume_preimage_mul_right hr, Real.volume_preimage_mul_right hr]
  exact ENNReal.mul_div_mul_left _ _
    (ENNReal.ofReal_pos.2 (abs_pos.2 (inv_ne_zero hr))).ne' ENNReal.ofReal_ne_top

/-- **The hit-and-run proposal is equivariant under the chart**, in preimage form.

This is where the geometric content of the `r → 1` rescaling sits.  The chart
`z ↦ r • z + zin` is a **similarity**: it multiplies every distance by `r`
(`Arlib.MarkovChains.dist_affineChart`), so it maps lines to lines and does **not** move the
direction `θ`.  Consequently the direction measure `Arlib.MarkovChains.unifSphere n` is
untouched on both sides of this identity — only the chord parameter is rescaled, `t ↦ t·r`,
and `Ttc.uniformOn_preimage_mul_right` shows the uniform law on the chord does not notice.

This is exactly the verification the brief demanded: hit-and-run's direction distribution
*is* Euclidean-metric-dependent, so hit-and-run is equivariant only under similarities — and
a uniform scaling composed with a translation is one. -/
theorem hitAndRunProposal_chartPreimage {n : ℕ} {K A : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hA : MeasurableSet A) {r : ℝ} (hr : 0 < r)
    (zin y : EuclideanSpace ℝ (Fin n)) :
    Arlib.MarkovChains.hitAndRunProposal
        ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K) y
        ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' A)
      = Arlib.MarkovChains.hitAndRunProposal K (r • y + zin) A := by
  have hS : Measurable (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) :=
    Arlib.MarkovChains.measurable_affineChart r zin
  rw [Arlib.MarkovChains.hitAndRunProposal_apply_uniformOn (hK.preimage hS) y (hA.preimage hS),
    Arlib.MarkovChains.hitAndRunProposal_apply_uniformOn hK (r • y + zin) hA]
  refine lintegral_congr fun θ => ?_
  rw [chordSet_chartPreimage K r zin y _, setOf_chartPreimage A r zin y _]
  exact uniformOn_preimage_mul_right hr.ne'
    (Arlib.MarkovChains.measurableSet_chordSet hK _ _) (hA.preimage (by fun_prop))

/-- The proposal's total mass is a chart invariant. -/
theorem hitAndRunProposal_univ_chartPreimage {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) {r : ℝ} (hr : 0 < r)
    (zin y : EuclideanSpace ℝ (Fin n)) :
    Arlib.MarkovChains.hitAndRunProposal
        ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K) y Set.univ
      = Arlib.MarkovChains.hitAndRunProposal K (r • y + zin) Set.univ := by
  have h := hitAndRunProposal_chartPreimage hK MeasurableSet.univ hr zin y
  rwa [Set.preimage_univ] at h

/-- **The crux: the hit-and-run kernel is equivariant under the affine chart.**

    Measure.map (fun z => r • z + zin) (hitAndRun ((fun z => r • z + zin) ⁻¹' K) y)
      = hitAndRun K (r • y + zin).

The analogue, for hit-and-run, of `Arlib.MarkovChains.map_speedyWalk_affineChart`.  Holds for
**every** `y`, with no membership hypothesis — which is what
`Arlib.MarkovChains.map_iterate_of_map_kernel` needs. -/
theorem map_hitAndRun_chart {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) {r : ℝ} (hr : 0 < r) (zin y : EuclideanSpace ℝ (Fin n)) :
    Measure.map (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin)
        (Arlib.MarkovChains.hitAndRun
          ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K) y)
      = Arlib.MarkovChains.hitAndRun K (r • y + zin) := by
  have hS : Measurable (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) :=
    Arlib.MarkovChains.measurable_affineChart r zin
  ext t ht
  have hind : ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' t).indicator
        (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) y
      = t.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (r • y + zin) := by
    by_cases hmem : r • y + zin ∈ t
    · have hy : y ∈ (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' t := hmem
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hmem, Pi.one_apply, Pi.one_apply]
    · have hy : y ∉ (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' t := hmem
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hmem]
  rw [Measure.map_apply hS ht,
    Arlib.MarkovChains.hitAndRun_apply_set (hK.preimage hS) y (ht.preimage hS),
    Arlib.MarkovChains.hitAndRun_apply_set hK (r • y + zin) ht,
    hitAndRunProposal_chartPreimage hK ht hr zin y,
    hitAndRunProposal_univ_chartPreimage hK hr zin y, hind]

/-! ## 5. Seam: the `r → 1` chart, transport of the measures -/

/-- Preimage under the chart undoes preimage under the inverse chart. -/
theorem preimage_chart_preimage_invChart {n : ℕ} {r : ℝ} (hr : r ≠ 0)
    (zin : EuclideanSpace ℝ (Fin n)) (B : Set (EuclideanSpace ℝ (Fin n))) :
    (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹'
        ((fun x : EuclideanSpace ℝ (Fin n) => r⁻¹ • (x - zin)) ⁻¹' B) = B := by
  rw [← Set.preimage_comp, invChart_comp_chart hr zin, Set.preimage_id]

/-- Preimage under the inverse chart undoes preimage under the chart. -/
theorem preimage_invChart_preimage_chart {n : ℕ} {r : ℝ} (hr : r ≠ 0)
    (zin : EuclideanSpace ℝ (Fin n)) (B : Set (EuclideanSpace ℝ (Fin n))) :
    (fun x : EuclideanSpace ℝ (Fin n) => r⁻¹ • (x - zin)) ⁻¹'
        ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' B) = B := by
  rw [← Set.preimage_comp, chart_comp_invChart hr zin, Set.preimage_id]

/-- Pushing a law down the inverse chart and back up the chart is the identity. -/
theorem map_chart_map_invChart {n : ℕ} {r : ℝ} (hr : r ≠ 0)
    (zin : EuclideanSpace ℝ (Fin n)) (sigma : Measure (EuclideanSpace ℝ (Fin n))) :
    Measure.map (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin)
        (Measure.map (fun x : EuclideanSpace ℝ (Fin n) => r⁻¹ • (x - zin)) sigma) = sigma := by
  rw [Measure.map_map (Arlib.MarkovChains.measurable_affineChart r zin)
      (measurable_invChart r zin), chart_comp_invChart hr zin, Measure.map_id]

/-- **The normalised uniform target, evaluated through the chart.** -/
theorem uniformOn_chartPreimage_apply {n : ℕ} {K A : Set (EuclideanSpace ℝ (Fin n))}
    (hKm : MeasurableSet K) (hA : MeasurableSet A) {r : ℝ} (hr : 0 < r)
    (zin : EuclideanSpace ℝ (Fin n)) :
    Arlib.uniformOn volume ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K) A
      = Arlib.uniformOn volume K
          ((fun x : EuclideanSpace ℝ (Fin n) => r⁻¹ • (x - zin)) ⁻¹' A) := by
  have hS : Measurable (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) :=
    Arlib.MarkovChains.measurable_affineChart r zin
  have hT : Measurable (fun x : EuclideanSpace ℝ (Fin n) => r⁻¹ • (x - zin)) :=
    measurable_invChart r zin
  rw [← Arlib.MarkovChains.map_uniformOn_affineChart hr zin hKm,
    Measure.map_apply hS (hA.preimage hT), preimage_chart_preimage_invChart hr.ne' zin]

/-- **The normalised exceptional-set hypothesis.** -/
theorem hdom_chartPreimage {n : ℕ} {K Sx : Set (EuclideanSpace ℝ (Fin n))}
    {sigma : Measure (EuclideanSpace ℝ (Fin n))} {M : ℝ}
    (hKm : MeasurableSet K) (hSm : MeasurableSet Sx) {r : ℝ} (hr : 0 < r)
    (zin : EuclideanSpace ℝ (Fin n))
    (hdom : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      sigma (A \ Sx) ≤ ENNReal.ofReal M * Arlib.uniformOn volume K (A \ Sx)) :
    ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      Measure.map (fun x : EuclideanSpace ℝ (Fin n) => r⁻¹ • (x - zin)) sigma
          (A \ (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' Sx)
        ≤ ENNReal.ofReal M *
          Arlib.uniformOn volume
            ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K) A := by
  have hS : Measurable (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) :=
    Arlib.MarkovChains.measurable_affineChart r zin
  have hT : Measurable (fun x : EuclideanSpace ℝ (Fin n) => r⁻¹ • (x - zin)) :=
    measurable_invChart r zin
  intro A hA
  rw [Measure.map_apply hT (hA.diff (hSm.preimage hS)), Set.preimage_sdiff,
    preimage_invChart_preimage_chart hr.ne' zin,
    uniformOn_chartPreimage_apply hKm hA hr zin]
  exact hdom_of_contract hdom _ (hA.preimage hT)

/-- **The transport step**: a mixing bound for the normalised body, started from the
normalised law, is a mixing bound for the original body started from the original law.  The
accuracy `eps` is unchanged.

Everything generic here is borrowed from `Arlib/MarkovChains/Continuous/SpeedyAffine.lean`
(`tvLe_map`, `map_iterate_of_map_kernel`, `map_uniformOn_affineChart`); the only
hit-and-run-specific input is `hmap`, discharged by `Ttc.map_hitAndRun_chart`. -/
theorem tvLe_of_tvLe_chart {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKm : MeasurableSet K) {r : ℝ} (hr : 0 < r) (zin : EuclideanSpace ℝ (Fin n))
    {P' P : Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))}
    (hmap : ∀ y : EuclideanSpace ℝ (Fin n),
      Measure.map (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) (P' y) = P (r • y + zin))
    {sigma : Measure (EuclideanSpace ℝ (Fin n))} {m : ℕ} {eps : ℝ≥0∞}
    (h : Arlib.TVLe
      (Arlib.MarkovChains.iterate P'
        (Measure.map (fun x : EuclideanSpace ℝ (Fin n) => r⁻¹ • (x - zin)) sigma) m)
      (Arlib.uniformOn volume
        ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K)) eps) :
    Arlib.TVLe (Arlib.MarkovChains.iterate P sigma m) (Arlib.uniformOn volume K) eps := by
  have hS : Measurable (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) :=
    Arlib.MarkovChains.measurable_affineChart r zin
  have h2 := Arlib.MarkovChains.tvLe_map hS h
  rw [Arlib.MarkovChains.map_iterate_of_map_kernel hS hmap, map_chart_map_invChart hr.ne' zin,
    Arlib.MarkovChains.map_uniformOn_affineChart hr zin hKm] at h2
  exact h2

/-! ## 6. The assembled backend theorem, plain kernel -/

/-- **The conclusion of `Ttc.HitAndRunTheorem11Input.mixing`, byte for byte, proved** — with
only the paper's Lemma 4.1 (`hLem41`), the paper's corrected Theorem 2.1 (`hIso`) and
Lovász–Simonovits Corollary 1.5 (`hLS`) remaining as binders.

Every other seam is closed here: the general inradius `r` (via the chart
`z ↦ r • z + zin`, `Ttc.map_hitAndRun_chart`), the `hdom` shape mismatch
(`Ttc.hdom_of_contract`), and the threshold (`Ttc.lvThreshold_unit_div_eq`).  Note there is
no factor lost anywhere: the deadline is exactly `Ttc.hitAndRunTheorem11Threshold`.

**The three binders are consumed at the normalised body**
`(fun z => r • z + zin) ⁻¹' K`, not at `K`.  That is not a weakening for a caller who holds
them for every convex body — which is how they are used in
`Ttc.hitAndRunTheorem11Input_of_binders` — but it is not the same statement as holding them
at `K` alone: transporting `hLem41` and `hIso` back along the chart would need equivariance
of `Arlib.crossRatioDist` and `Arlib.medianStep`, which is **not**
proved here. -/
theorem tvLe_iterate_hitAndRun_at_contract_shape {n : ℕ} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKm : MeasurableSet K) (hKc : Convex ℝ K) (hKcl : IsClosed K)
    {zin zout : EuclideanSpace ℝ (Fin n)} {r R : ℝ}
    (hr : 0 < r) (hR : 0 ≤ R)
    (hin : closedBall zin r ⊆ K) (hout : K ⊆ closedBall zout R)
    {sigma : Measure (EuclideanSpace ℝ (Fin n))}
    [IsProbabilityMeasure sigma]
    {M eps : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {Sx : Set (EuclideanSpace ℝ (Fin n))} (hSm : MeasurableSet Sx)
    (hS : sigma Sx ≤ ENNReal.ofReal (eps / 2))
    (hdom : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      sigma (A \ Sx) ≤ ENNReal.ofReal M * Arlib.uniformOn volume K (A \ Sx))
    (hLem41 : ∀ u ∈ (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K,
      ∀ v ∈ (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K,
      Arlib.crossRatioDist
          ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K) u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n *
          max (Arlib.medianStep
              ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K) u)
            (Arlib.medianStep
              ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K) v) →
      Arlib.TVLe
        (Arlib.MarkovChains.hitAndRun
          ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K) u)
        (Arlib.MarkovChains.hitAndRun
          ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K) v)
        (ENNReal.ofReal (1 - 1 / 500)))
    (hIso : ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), (∀ x, 0 ≤ h x) →
      (∀ x ∈ (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ →
      T₁ ⊆ (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K →
      T₂ ⊆ (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂,
        ∀ x ∈ (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (Arlib.crossRatioDist
          ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K) u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(Arlib.uniformOn volume
            ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K))) *
          min (Arlib.uniformOn volume
              ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K) T₁)
            (Arlib.uniformOn volume
              ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K) T₂)
        ≤ Arlib.uniformOn volume ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K)
            (((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K \ T₁) \ T₂))
    (hLS : ∀ ph W : ℝ, 0 < ph → ph ≤ 1 → 1 ≤ W →
      ENNReal.ofReal ph ≤ Arlib.MarkovChains.conductance
        (Arlib.MarkovChains.hitAndRun
          ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K))
        (Arlib.uniformOn volume
          ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K)) →
      ∀ mu : Measure (EuclideanSpace ℝ (Fin n)), IsProbabilityMeasure mu →
        Arlib.IsWarm (ENNReal.ofReal W) mu (Arlib.uniformOn volume
          ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K)) →
        ∀ t : ℕ, Arlib.TVLe
          (Arlib.MarkovChains.iterate (Arlib.MarkovChains.hitAndRun
            ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K)) mu t)
          (Arlib.uniformOn volume
            ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K))
          (ENNReal.ofReal (Real.sqrt W * (1 - ph ^ 2 / 2) ^ t)))
    {m : ℕ} (hm : hitAndRunTheorem11Threshold n r R M eps < (m : ℝ)) :
    Arlib.TVLe
      (Arlib.MarkovChains.iterate (Arlib.MarkovChains.hitAndRun K) sigma m)
      (Arlib.uniformOn volume K) (ENNReal.ofReal eps) := by
  have hchart : Measurable (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) :=
    Arlib.MarkovChains.measurable_affineChart r zin
  have hT : Measurable (fun x : EuclideanSpace ℝ (Fin n) => r⁻¹ • (x - zin)) :=
    measurable_invChart r zin
  haveI : IsProbabilityMeasure
      (Measure.map (fun x : EuclideanSpace ℝ (Fin n) => r⁻¹ • (x - zin)) sigma) :=
    Measure.isProbabilityMeasure_map hT.aemeasurable
  have hR1 : (1 : ℝ) ≤ R / r := (one_le_div hr).2 (inradius_le_circumradius hn hr hin hout)
  refine tvLe_of_tvLe_chart hKm hr zin (fun y => map_hitAndRun_chart hKm hr zin y) ?_
  refine Arlib.MarkovChains.tvLe_iterate_hitAndRun_unitBall hn
    (convex_chartPreimage r zin hKc) (isClosed_chartPreimage r zin hKcl) (hKm.preimage hchart)
    (closedBall_one_subset_chartPreimage hr hin) hR1
    (chartPreimage_subset_closedBall hr hout) hM heps0 heps1 (hSm.preimage hchart) ?_
    (hdom_chartPreimage hKm hSm hr zin hdom) hLem41 hIso hLS ?_
  · rw [Measure.map_apply hT (hSm.preimage hchart),
      preimage_invChart_preimage_chart hr.ne' zin]
    exact hS
  · rw [lvThreshold_unit_div_eq hr]
    exact hm.le

/-! ## 7. The contract, inhabited from the three binders -/

/-- **A `Ttc.HitAndRunTheorem11Input`, constructed** — conditionally on the three
mathematical binders, stated here for *every* convex body rather than for one.

This is the constructor application that `Ttc/Sampler/SpeedyBackend.lean:18-20` observes is
missing from the repository: `HitAndRunTheorem11Input` is inhabited **nowhere**.  It is
inhabited here, modulo `HLem41` (Lovász–Vempala Lemma 4.1), `HIso` (their Theorem 2.1, in the
corrected form carrying `∀ x ∈ K, h x ≤ 1/3`) and `HLS` (Lovász–Simonovits Corollary 1.5 for
the **plain** hit-and-run kernel).

Read the module docstring before quoting this: `HLS` for the plain kernel is a genuine gap in
the paper (`Arlib/MarkovChains/Continuous/HitAndRunMixing.lean:204-210`), not a bookkeeping
loss, and it is **not** discharged anywhere in this repository.  So this term is an
implication with an antecedent nobody has exhibited; it is not a witness for
`Nonempty HitAndRunTheorem11Input`. -/
theorem hitAndRunTheorem11Input_of_binders
    (HLem41 : ∀ (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))),
      ∀ u ∈ K, ∀ v ∈ K, Arlib.crossRatioDist K u v < 1 / 8 →
        dist u v < 2 / Real.sqrt n * max (Arlib.medianStep K u) (Arlib.medianStep K v) →
        Arlib.TVLe (Arlib.MarkovChains.hitAndRun K u) (Arlib.MarkovChains.hitAndRun K v)
          (ENNReal.ofReal (1 - 1 / 500)))
    (HIso : ∀ (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n)))
        (h : EuclideanSpace ℝ (Fin n) → ℝ) (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))),
      (∀ x, 0 ≤ h x) → (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (Arlib.crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(Arlib.uniformOn volume K)) *
          min (Arlib.uniformOn volume K T₁) (Arlib.uniformOn volume K T₂)
        ≤ Arlib.uniformOn volume K ((K \ T₁) \ T₂))
    (HLS : ∀ (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) (ph W : ℝ),
      0 < ph → ph ≤ 1 → 1 ≤ W →
      ENNReal.ofReal ph ≤ Arlib.MarkovChains.conductance
        (Arlib.MarkovChains.hitAndRun K) (Arlib.uniformOn volume K) →
      ∀ mu : Measure (EuclideanSpace ℝ (Fin n)), IsProbabilityMeasure mu →
        Arlib.IsWarm (ENNReal.ofReal W) mu (Arlib.uniformOn volume K) →
        ∀ t : ℕ, Arlib.TVLe
          (Arlib.MarkovChains.iterate (Arlib.MarkovChains.hitAndRun K) mu t)
          (Arlib.uniformOn volume K)
          (ENNReal.ofReal (Real.sqrt W * (1 - ph ^ 2 / 2) ^ t))) :
    HitAndRunTheorem11Input := by
  refine ⟨?_⟩
  intro n hn K hKm hKc hKcl zin zout r R hr hR hin hout sigma _ M eps hM heps0 heps1 Sx hSm
    hS hdom m hm
  exact tvLe_iterate_hitAndRun_at_contract_shape hn hKm hKc hKcl hr hR hin hout hM heps0 heps1
    hSm hS hdom (HLem41 n _) (HIso n _) (HLS n _) hm

/-! ## 8. The same assembly over the **lazy** kernel, where `hLS` is a theorem -/

/-- **The contract's conclusion for the lazy hit-and-run kernel**, at a deadline four times
as long — with only `hLem41` and `hIso` remaining as binders.

`Arlib.MarkovChains.tvLe_iterate_lazy_hitAndRun_unitBall`
(`Arlib/MarkovChains/Continuous/ConductanceToTV.lean:414`) discharges `hLS` from laziness
(`hasNonnegSpectrum_lazy`) plus reversibility of hit-and-run, so this route carries **one
fewer** unproved input than `Ttc.tvLe_iterate_hitAndRun_at_contract_shape`.  The price is
paid in two places, both visible in the statement:

* the kernel is `Arlib.MarkovChains.lazy (Arlib.MarkovChains.hitAndRun K)`, **not**
  `Arlib.MarkovChains.hitAndRun K`.  These are different Markov chains and this theorem does
  **not** inhabit `Ttc.HitAndRunTheorem11Input`, which asks for the plain one;
* the deadline is `4 · Ttc.hitAndRunTheorem11Threshold`, the exact factor by which laziness
  halves the conductance.

The `r → 1` chart, the `hdom` reconciliation and the threshold identity are the same seams as
in the plain-kernel theorem; the extra step is
`Arlib.MarkovChains.map_lazy_of_map_kernel`, which lifts `Ttc.map_hitAndRun_chart` through
`lazy`. -/
theorem tvLe_iterate_lazy_hitAndRun_at_contract_shape {n : ℕ} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKm : MeasurableSet K) (hKc : Convex ℝ K) (hKcl : IsClosed K)
    {zin zout : EuclideanSpace ℝ (Fin n)} {r R : ℝ}
    (hr : 0 < r) (hR : 0 ≤ R)
    (hin : closedBall zin r ⊆ K) (hout : K ⊆ closedBall zout R)
    {sigma : Measure (EuclideanSpace ℝ (Fin n))}
    [IsProbabilityMeasure sigma]
    {M eps : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {Sx : Set (EuclideanSpace ℝ (Fin n))} (hSm : MeasurableSet Sx)
    (hS : sigma Sx ≤ ENNReal.ofReal (eps / 2))
    (hdom : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      sigma (A \ Sx) ≤ ENNReal.ofReal M * Arlib.uniformOn volume K (A \ Sx))
    (hLem41 : ∀ u ∈ (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K,
      ∀ v ∈ (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K,
      Arlib.crossRatioDist
          ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K) u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n *
          max (Arlib.medianStep
              ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K) u)
            (Arlib.medianStep
              ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K) v) →
      Arlib.TVLe
        (Arlib.MarkovChains.hitAndRun
          ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K) u)
        (Arlib.MarkovChains.hitAndRun
          ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K) v)
        (ENNReal.ofReal (1 - 1 / 500)))
    (hIso : ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), (∀ x, 0 ≤ h x) →
      (∀ x ∈ (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ →
      T₁ ⊆ (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K →
      T₂ ⊆ (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂,
        ∀ x ∈ (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (Arlib.crossRatioDist
          ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K) u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(Arlib.uniformOn volume
            ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K))) *
          min (Arlib.uniformOn volume
              ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K) T₁)
            (Arlib.uniformOn volume
              ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K) T₂)
        ≤ Arlib.uniformOn volume ((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K)
            (((fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) ⁻¹' K \ T₁) \ T₂))
    {m : ℕ} (hm : 4 * hitAndRunTheorem11Threshold n r R M eps ≤ (m : ℝ)) :
    Arlib.TVLe
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy (Arlib.MarkovChains.hitAndRun K)) sigma m)
      (Arlib.uniformOn volume K) (ENNReal.ofReal eps) := by
  have hchart : Measurable (fun z : EuclideanSpace ℝ (Fin n) => r • z + zin) :=
    Arlib.MarkovChains.measurable_affineChart r zin
  have hT : Measurable (fun x : EuclideanSpace ℝ (Fin n) => r⁻¹ • (x - zin)) :=
    measurable_invChart r zin
  haveI : IsProbabilityMeasure
      (Measure.map (fun x : EuclideanSpace ℝ (Fin n) => r⁻¹ • (x - zin)) sigma) :=
    Measure.isProbabilityMeasure_map hT.aemeasurable
  have hR1 : (1 : ℝ) ≤ R / r := (one_le_div hr).2 (inradius_le_circumradius hn hr hin hout)
  refine tvLe_of_tvLe_chart hKm hr zin
    (fun y => Arlib.MarkovChains.map_lazy_of_map_kernel hchart
      (fun w => map_hitAndRun_chart hKm hr zin w) y) ?_
  refine Arlib.MarkovChains.tvLe_iterate_lazy_hitAndRun_unitBall hn
    (convex_chartPreimage r zin hKc) (isClosed_chartPreimage r zin hKcl) (hKm.preimage hchart)
    (closedBall_one_subset_chartPreimage hr hin) hR1
    (chartPreimage_subset_closedBall hr hout) hM heps0 heps1 (hSm.preimage hchart) ?_
    (hdom_chartPreimage hKm hSm hr zin hdom) hLem41 hIso ?_
  · rw [Measure.map_apply hT (hSm.preimage hchart),
      preimage_invChart_preimage_chart hr.ne' zin]
    exact hS
  · rw [lvThreshold_unit_div_eq hr]
    exact hm

/-! ## 9. Non-vacuity (`CLAUDE.md` §11)

**There is no zero-hypothesis instance, and this section does not pretend otherwise.**
`Ttc/Sampler/SpeedyBackend.lean:600` has one (`..._ballTwo_dim2`); nothing of that kind is
reachable here, and the reason is upstream, not in this file.

The three binders are **not** in the same state, and the difference matters:

| binder | plain kernel (§§6–7) | lazy kernel (§8) |
| --- | --- | --- |
| `hLS` | **open, and a gap in the paper** | **proved** — `Arlib.MarkovChains.ls_lazy`, via `ConductanceToTV.lean:414`; not a binder there at all |
| `hLem41` | open | open |
| `hIso` | open | open |

So §8 carries **two** binders and §§6–7 carry **three**; the extra one is `hLS` for the plain
kernel, and it is the paper's own gap, not a formalisation shortfall.  Neither route is
hypothesis-free, because `hLem41` and `hIso` are open for both.  In detail:

* `hIso` — Lovász–Vempala Theorem 2.1 — is not proved for any body.  `Arlib.needle_iso`
  (`Arlib/Convexity/LovaszVempalaIso.lean:421`) is the one-dimensional core, and
  `Arlib.needle_iso_of_chord` (`:629`) lifts it to a needle, but the localisation step that
  would turn needles into a statement about `K` is classified as open in
  `Arlib/Convexity/LocalizationAssembly.lean` (lower semicontinuity for indicator
  integrands; the measure-preserving transport `EuclideanSpace ℝ (Fin n) ≃ (Fin (m+1) → ℝ)`).
* `hLem41` — Lovász–Vempala Lemma 4.1 — is proved only in the shape
  `Arlib.MarkovChains.tvLe_hitAndRun_lemma41_unconditional`
  (`Arlib/MarkovChains/Continuous/HitAndRunOverlap.lean:751`), whose conclusion carries the
  *dimension-dependent* constant `1 − 1/(2(1+4/n)ⁿ)·(…)` rather than the `1 − 1/500` the
  conductance theorem consumes, and which additionally assumes `u ≠ v`,
  `hitAndRunProposal K u univ = 1`, `chordLow K u v < 0` and `1 < chordHigh K u v`.
* `hLS` for the **plain** `hitAndRun K` is not merely unproved — it is the paper's own gap
  (`Arlib/MarkovChains/Continuous/HitAndRunMixing.lean:204-210`), refuted for general
  reversible chains by the swap kernel on `Bool`.  For `lazy (hitAndRun K)` it is a
  **theorem** (`Arlib/MarkovChains/Continuous/ConductanceToTV.lean`), which is exactly why §8
  exists and why it carries one binder fewer.  That does not rescue §§6–7: the contract asks
  for the plain kernel.

Neither binder can be made vacuous by a choice of body either: `hIso`'s conclusion is a real
inequality about a body of positive finite volume (forced by the inball and the circumball),
and `hLem41` quantifies over genuinely distinct pairs `u ≠ v` in a body with nonempty
interior.

What *can* be certified with no hypotheses at all is that **every seam this file closes is
closed unconditionally**: `Ttc.map_hitAndRun_chart`, `Ttc.hdom_of_contract`,
`Ttc.lvThreshold_unit_div_eq`, `Ttc.inradius_le_circumradius` and the rest of §§1–5 are
theorems with no binder beyond measurability and positivity.  And the witness below shows
that **every** hypothesis of the assembled theorem *except* the three binders is
simultaneously satisfiable, at a concrete body, dimension, start and step count. -/

/-- The chart at `r = 1`, `zin = 0` is the identity.  (Not used by the witness below, which
deliberately takes `r = 1/2` so that the chart is non-trivial; recorded because a caller
checking the `r = 1` case by hand will want it.) -/
theorem preimage_chart_id {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) :
    (fun z : EuclideanSpace ℝ (Fin n) =>
      (1 : ℝ) • z + (0 : EuclideanSpace ℝ (Fin n))) ⁻¹' S = S := by
  ext z; simp

/-- **Non-vacuity witness for everything except the three binders.**

At `n = 2`, `K = closedBall 0 2`, inball radius `r = 1/2` (so the chart `z ↦ (1/2) • z` is
**not** the identity and the `r → 1` rescaling is genuinely exercised), circumball radius
`R = 2`, warmness `M = 1`, accuracy `eps = 1/2`, empty exceptional set, and start law
`Arlib.uniformOn volume K` — every hypothesis of `Ttc.hitAndRunTheorem11Input_of_binders`
other than `HLem41`, `HIso`, `HLS` is discharged here, and the conclusion is obtained
*through* the constructed `Ttc.HitAndRunTheorem11Input`, not directly.

The tolerance `1/2` is non-trivial (`ENNReal.ofReal 1` would be the vacuous total-variation
bound).  What is **not** claimed is that the `m`-step law actually differs from the target. -/
theorem tvLe_iterate_hitAndRun_ballTwo_dim2
    (HLem41 : ∀ (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))),
      ∀ u ∈ K, ∀ v ∈ K, Arlib.crossRatioDist K u v < 1 / 8 →
        dist u v < 2 / Real.sqrt n * max (Arlib.medianStep K u) (Arlib.medianStep K v) →
        Arlib.TVLe (Arlib.MarkovChains.hitAndRun K u) (Arlib.MarkovChains.hitAndRun K v)
          (ENNReal.ofReal (1 - 1 / 500)))
    (HIso : ∀ (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n)))
        (h : EuclideanSpace ℝ (Fin n) → ℝ) (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))),
      (∀ x, 0 ≤ h x) → (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (Arlib.crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(Arlib.uniformOn volume K)) *
          min (Arlib.uniformOn volume K T₁) (Arlib.uniformOn volume K T₂)
        ≤ Arlib.uniformOn volume K ((K \ T₁) \ T₂))
    (HLS : ∀ (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) (ph W : ℝ),
      0 < ph → ph ≤ 1 → 1 ≤ W →
      ENNReal.ofReal ph ≤ Arlib.MarkovChains.conductance
        (Arlib.MarkovChains.hitAndRun K) (Arlib.uniformOn volume K) →
      ∀ mu : Measure (EuclideanSpace ℝ (Fin n)), IsProbabilityMeasure mu →
        Arlib.IsWarm (ENNReal.ofReal W) mu (Arlib.uniformOn volume K) →
        ∀ t : ℕ, Arlib.TVLe
          (Arlib.MarkovChains.iterate (Arlib.MarkovChains.hitAndRun K) mu t)
          (Arlib.uniformOn volume K)
          (ENNReal.ofReal (Real.sqrt W * (1 - ph ^ 2 / 2) ^ t))) :
    Arlib.TVLe
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.hitAndRun (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 2))
        (Arlib.uniformOn volume (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 2))
        (hitAndRunTheorem11Steps 2 (1 / 2) 2 1 (1 / 2)))
      (Arlib.uniformOn volume (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 2))
      (ENNReal.ofReal (1 / 2)) := by
  haveI : IsProbabilityMeasure
      (Arlib.uniformOn volume (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 2)) :=
    Arlib.isProbabilityMeasure_uniformOn volume
      (measure_closedBall_pos volume (0 : EuclideanSpace ℝ (Fin 2)) (by norm_num)).ne'
      measure_closedBall_lt_top.ne
  refine (hitAndRunTheorem11Input_of_binders HLem41 HIso HLS).at_steps (n := 2) (by norm_num)
    measurableSet_closedBall (convex_closedBall _ _) isClosed_closedBall
    (r := 1 / 2) (R := 2) (zin := 0) (zout := 0) (by norm_num) (by norm_num)
    (closedBall_subset_closedBall (by norm_num)) Set.Subset.rfl
    (M := 1) le_rfl (by norm_num) (by norm_num)
    (S := (∅ : Set (EuclideanSpace ℝ (Fin 2)))) MeasurableSet.empty (by simp) ?_
  intro A _
  simp

/-! ### Axiom audit (`CLAUDE.md` §4)

Every declaration in this file must report exactly
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms lvThreshold_eq_hitAndRunTheorem11Threshold
#print axioms lvThreshold_le_hitAndRunTheorem11Threshold
#print axioms lvThreshold_unit_div_eq
#print axioms hdom_of_contract
#print axioms measurable_invChart
#print axioms chart_comp_invChart
#print axioms invChart_comp_chart
#print axioms closedBall_one_subset_chartPreimage
#print axioms chartPreimage_subset_closedBall
#print axioms convex_chartPreimage
#print axioms isClosed_chartPreimage
#print axioms inradius_le_circumradius
#print axioms chordSet_chartPreimage
#print axioms setOf_chartPreimage
#print axioms uniformOn_preimage_mul_right
#print axioms hitAndRunProposal_chartPreimage
#print axioms hitAndRunProposal_univ_chartPreimage
#print axioms map_hitAndRun_chart
#print axioms preimage_chart_preimage_invChart
#print axioms preimage_invChart_preimage_chart
#print axioms map_chart_map_invChart
#print axioms uniformOn_chartPreimage_apply
#print axioms hdom_chartPreimage
#print axioms tvLe_of_tvLe_chart
#print axioms tvLe_iterate_hitAndRun_at_contract_shape
#print axioms hitAndRunTheorem11Input_of_binders
#print axioms tvLe_iterate_lazy_hitAndRun_at_contract_shape
#print axioms preimage_chart_id
#print axioms tvLe_iterate_hitAndRun_ballTwo_dim2

end Ttc
