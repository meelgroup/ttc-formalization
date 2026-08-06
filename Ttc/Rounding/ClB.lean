/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Rounding.RoundMoments
import Ttc.Nonconv.FacetOfDNF

/-!
# `claim:cl`(b) for the actual rounding

Parts (a) and (c) fix a lattice point `x` and integrate over `p`; part (b) fixes
`p` and sums over **lattice points**, so it needs the law of `rnd p` on `ℤⁿ`
(`Ttc.roundLaw`) rather than the displacement law on `ℝⁿ`. The moments of that law
are `Rounding/RoundMoments`; what this file adds is the geometry and the averaging.

Two things differ from (a):

* **The crossing goes the other way.** In (a), `x ∈ Q` and `p ∉ Q'` force
  `A_j·(p − x) ≥ κ‖A_j‖`. Here `p ∈ Q''` and `rnd p ∉ Q` force
  `A_j·(rnd p − p) ≥ κ‖A_j‖`, i.e. the tail bound is applied to the coefficient
  vector `−A_j` (`Ttc.cover_of_notMem_body_deflated`). The bound is unchanged,
  since `‖−A‖ = ‖A‖`.
* **The averaging is over `p`, not over `x`.** Once every `p ∈ Q''` rounds into
  `Q` with probability `≥ 1 − η/4`, a uniform draw from `Q''` does too — that is
  `Ttc.claim_cl_b`, which needs nothing from the kernel.
-/

namespace Ttc

open MeasureTheory ProbabilityTheory Set

variable {n : ℕ} {ι F : Type*}

/-! ## The covering, in the `Q''` direction -/

/-- **The facet-crossing, deflated.** If `p` lies in the *deflated* body and `x`
outside the body, some facet `j` has `κ·w j ≤ f j x − f j p`.

This is the mirror of `Ttc.cover_of_notMem_body`: there the moving point escapes
an inflation, here it escapes the body while the fixed point sits inside a
deflation. Both give one facet crossed by `κ‖A_j‖`, but with opposite signs. -/
theorem cover_of_notMem_body_deflated (S : FacetSystem n ι F) {κ : ℝ}
    {p x : Space n} (hp : p ∈ S.body (-κ)) (hx : x ∉ S.body 0) :
    ∃ j, κ * S.w j ≤ S.f j x - S.f j p := by
  obtain ⟨i, hi⟩ := S.mem_body.1 hp
  have hxi : x ∉ S.piece 0 i := fun h => hx (S.mem_body.2 ⟨i, h⟩)
  simp only [FacetSystem.mem_piece, not_forall] at hxi
  obtain ⟨j, hpart, hlt⟩ := hxi
  have hpj : S.f j p ≤ S.b j + (-κ) * S.w j := hi j hpart
  have hneg : S.b j + (-κ) * S.w j = S.b j - κ * S.w j := by ring
  rw [hneg] at hpj
  push Not at hlt
  exact ⟨j, by linarith⟩

/-- Negating a coefficient vector does not change its norm. -/
theorem coeffNorm_neg (A : Fin n → ℝ) : coeffNorm (fun k => -(A k)) = coeffNorm A := by
  unfold coeffNorm
  exact congrArg Real.sqrt (Finset.sum_congr rfl fun k _ => by ring)

theorem sum_sq_neg (A : Fin n → ℝ) : ∑ k, (-(A k)) ^ 2 = ∑ k, A k ^ 2 :=
  Finset.sum_congr rfl fun k _ => by ring

/-! ## The escape bound at a fixed `p` -/

/-- **The escape bound of `claim:cl`(b).** For `p` in the deflated body, the
probability that `rnd p` lands outside the body is at most `η/4`: each escape
crosses some facet, the tail bound gives each facet `η/(4r)`, and the union bound
over the `r` facets does the rest. -/
theorem roundLaw_escape_bound [Fintype F] (S : FacetSystem n ι F) (Aof : F → Fin n → ℝ)
    (hf : ∀ (j : F) (x : Space n), S.f j x = ∑ k, Aof j k * x k)
    (hw : ∀ j, S.w j = coeffNorm (Aof j))
    (hA : ∀ j, 0 < ∑ k, Aof j k ^ 2)
    {η r κ : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hr : 1 ≤ r)
    (hcard : (Fintype.card F : ℝ) ≤ r)
    (hκ : κ = Real.sqrt (2 * Real.log (4 / η)) + Real.sqrt (2 * Real.log r))
    {p : Space n} (hp : p ∈ S.body (-κ)) :
    (roundLaw p).real {z : Fin n → ℤ | latPt z ∉ S.body 0} ≤ η / 4 := by
  classical
  have hcover : {z : Fin n → ℤ | latPt z ∉ S.body 0}
      ⊆ ⋃ j ∈ (Finset.univ : Finset F),
          {z : Fin n → ℤ | κ * coeffNorm (fun k => -(Aof j k))
            ≤ ∑ k, (-(Aof j k)) * (p k - (z k : ℝ))} := by
    intro z hz
    obtain ⟨j, hj⟩ := cover_of_notMem_body_deflated S hp hz
    refine Set.mem_biUnion (Finset.mem_univ j) ?_
    have hsum : S.f j (latPt z) - S.f j p = ∑ k, (-(Aof j k)) * (p k - (z k : ℝ)) := by
      rw [hf, hf, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [latPt_apply]; ring
    show κ * coeffNorm (fun k => -(Aof j k)) ≤ _
    rw [coeffNorm_neg, ← hw, ← hsum]
    exact hj
  calc (roundLaw p).real {z : Fin n → ℤ | latPt z ∉ S.body 0}
      ≤ (roundLaw p).real (⋃ j ∈ (Finset.univ : Finset F),
          {z : Fin n → ℤ | κ * coeffNorm (fun k => -(Aof j k))
            ≤ ∑ k, (-(Aof j k)) * (p k - (z k : ℝ))}) :=
        measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ ∑ j, (roundLaw p).real
          {z : Fin n → ℤ | κ * coeffNorm (fun k => -(Aof j k))
            ≤ ∑ k, (-(Aof j k)) * (p k - (z k : ℝ))} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ η / 4 := by
        refine rounding_union_bound (η := η) (r := r) Finset.univ _ (by linarith)
          (by simpa using hcard) ?_ hη.le
        intro j _
        subst hκ
        exact roundLaw_tail_bound_kappa p (fun k => -(Aof j k)) hη hη1 hr
          (by rw [sum_sq_neg]; exact hA j)

/-- **`claim:cl`(b), pointwise.** For `p` in the deflated body, `rnd p` lands in
the body with probability at least `1 − η/4`. -/
theorem roundLaw_hit_bound [Fintype F] (S : FacetSystem n ι F) (Aof : F → Fin n → ℝ)
    (hf : ∀ (j : F) (x : Space n), S.f j x = ∑ k, Aof j k * x k)
    (hw : ∀ j, S.w j = coeffNorm (Aof j))
    (hA : ∀ j, 0 < ∑ k, Aof j k ^ 2)
    {η r κ : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hr : 1 ≤ r)
    (hcard : (Fintype.card F : ℝ) ≤ r)
    (hκ : κ = Real.sqrt (2 * Real.log (4 / η)) + Real.sqrt (2 * Real.log r))
    {p : Space n} (hp : p ∈ S.body (-κ)) :
    1 - η / 4 ≤ (roundLaw p).real {z : Fin n → ℤ | latPt z ∈ S.body 0} := by
  have hesc := roundLaw_escape_bound S Aof hf hw hA hη hη1 hr hcard hκ hp
  have hcompl : {z : Fin n → ℤ | latPt z ∉ S.body 0}
      = {z : Fin n → ℤ | latPt z ∈ S.body 0}ᶜ := rfl
  rw [hcompl, measureReal_compl MeasurableSet.of_discrete, probReal_univ] at hesc
  linarith

/-! ## From the law to the kernel sum

`Ttc.sum_upper_of_claim_bc` consumes `1 − η/2 ≤ ∑_{x ∈ T} Pr[rnd p = x]` with the
sum over a *finite set of lattice points*. That sum is the law's mass on `T`.
-/

/-- The law's mass on a finite set of lattice points is the sum of the kernel's
values there — the same numbers, read as a measure. -/
theorem roundLaw_real_finset (p : Space n) (T : Finset (Fin n → ℤ)) :
    (roundLaw p).real (↑T : Set (Fin n → ℤ)) = ∑ z ∈ T, ∏ i, tent (p i - z i) := by
  have hsum : (roundLaw p) (↑T : Set (Fin n → ℤ))
      = ENNReal.ofReal (∑ z ∈ T, ∏ i, tent (p i - z i)) := by
    rw [← sum_measure_singleton (μ := roundLaw p) (s := T),
      ENNReal.ofReal_sum_of_nonneg fun z _ => Finset.prod_nonneg fun i _ => tent_nonneg _]
    exact Finset.sum_congr rfl fun z _ => roundLaw_singleton p z
  rw [Measure.real, hsum,
    ENNReal.toReal_ofReal (Finset.sum_nonneg fun z _ => Finset.prod_nonneg fun i _ =>
      tent_nonneg _)]

/-- **`claim:cl`(b), pointwise, as a kernel sum.** If `T` contains every lattice
point of the body, then at every `p` of the deflated body the rounding kernel puts
mass at least `1 − η/4` on `T`. -/
theorem prodKernel_sum_ge [Fintype F] (S : FacetSystem n ι F) (Aof : F → Fin n → ℝ)
    (hf : ∀ (j : F) (x : Space n), S.f j x = ∑ k, Aof j k * x k)
    (hw : ∀ j, S.w j = coeffNorm (Aof j))
    (hA : ∀ j, 0 < ∑ k, Aof j k ^ 2)
    {η r κ : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hr : 1 ≤ r)
    (hcard : (Fintype.card F : ℝ) ≤ r)
    (hκ : κ = Real.sqrt (2 * Real.log (4 / η)) + Real.sqrt (2 * Real.log r))
    (T : Finset (Fin n → ℤ)) (hT : ∀ z, latPt z ∈ S.body 0 → z ∈ T)
    {p : Space n} (hp : p ∈ S.body (-κ)) :
    1 - η / 4 ≤ ∑ z ∈ T, (prodKernel n).k p (latPt z) := by
  have hmono : (roundLaw p).real {z : Fin n → ℤ | latPt z ∈ S.body 0}
      ≤ (roundLaw p).real (↑T : Set (Fin n → ℤ)) :=
    measureReal_mono (fun z hz => hT z hz) (measure_ne_top _ _)
  have hhit := roundLaw_hit_bound S Aof hf hw hA hη hη1 hr hcard hκ hp
  rw [roundLaw_real_finset] at hmono
  have hker : ∑ z ∈ T, (prodKernel n).k p (latPt z) = ∑ z ∈ T, ∏ i, tent (p i - (z i : ℝ)) :=
    Finset.sum_congr rfl fun z _ => rfl
  rw [hker]
  linarith

/-! ## The averaging step

`Ttc.claim_cl_b` turns the pointwise bound into the bound for a uniform draw. The
only bookkeeping is that the integral of the finite sum is the sum of the
integrals, so the conclusion is a sum of `Ttc.roundProb`s — exactly what
`Ttc.sum_upper_of_claim_bc` consumes.
-/

/-- **`claim:cl`(b) for the actual rounding, with no residual hypothesis.**

For `p` uniform on the deflated body `Q''`, the total probability that `rnd p`
hits a lattice point of `T ⊇ Q ∩ ℤⁿ` is at least `1 − η/4`. -/
theorem prodKernel_claim_cl_b [Fintype F] (S : FacetSystem n ι F) (Aof : F → Fin n → ℝ)
    (hf : ∀ (j : F) (x : Space n), S.f j x = ∑ k, Aof j k * x k)
    (hw : ∀ j, S.w j = coeffNorm (Aof j))
    (hA : ∀ j, 0 < ∑ k, Aof j k ^ 2)
    {η r κ : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hr : 1 ≤ r)
    (hcard : (Fintype.card F : ℝ) ≤ r)
    (hκ : κ = Real.sqrt (2 * Real.log (4 / η)) + Real.sqrt (2 * Real.log r))
    (T : Finset (Fin n → ℤ)) (hT : ∀ z, latPt z ∈ S.body 0 → z ∈ T)
    (hmeas : MeasurableSet (S.body (-κ)))
    (hpos : 0 < (volume (S.body (-κ))).toReal) (hfin : volume (S.body (-κ)) ≠ ⊤) :
    1 - η / 4 ≤ ∑ z ∈ T, roundProb (prodKernel n) (S.body (-κ)) (latPt z) := by
  have hint : ∀ z : Fin n → ℤ,
      IntegrableOn (fun p => (prodKernel n).k p (latPt z)) (S.body (-κ)) :=
    fun z => ((prodKernel n).integrable (latPt z)).integrableOn
  have hg : IntegrableOn (fun p => ∑ z ∈ T, (prodKernel n).k p (latPt z)) (S.body (-κ)) :=
    integrable_finsetSum _ fun z _ => hint z
  have havg := claim_cl_b (S := S.body (-κ))
    (g := fun p => ∑ z ∈ T, (prodKernel n).k p (latPt z)) (e := η / 4)
    hmeas hg
    (fun p hp => prodKernel_sum_ge S Aof hf hw hA hη hη1 hr hcard hκ T hT hp)
    hpos hfin
  have hswap : ∑ z ∈ T, roundProb (prodKernel n) (S.body (-κ)) (latPt z)
      = (∫ p in S.body (-κ), ∑ z ∈ T, (prodKernel n).k p (latPt z))
          / (volume (S.body (-κ))).toReal := by
    simp only [roundProb]
    rw [← Finset.sum_div, integral_finsetSum _ fun z _ => hint z]
  rw [hswap]
  exact havg

end Ttc
