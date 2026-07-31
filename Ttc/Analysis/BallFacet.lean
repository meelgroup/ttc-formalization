/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Analysis.ClB
import Ttc.Analysis.Lattice

/-!
# The inscribed ball, the facet form, and counting lattice points

Three pieces of bookkeeping that the assembly of `lem:lattice` needs and that have
no counterpart in the paper, because the paper leaves them implicit.

* **Ball ↔ facet.** The paper's hypothesis is *"each `Pᵢ` contains an `ℓ₂`-ball of
  radius `γ`"*; every step of the proof uses the equivalent per-facet inequality
  `γ‖A_ij‖ ≤ b_ij − A_ij·cᵢ`. The two are equivalent — by Cauchy–Schwarz one way
  (`Ttc.FacetSystem.ball_subset_piece`) and by evaluating at
  `cᵢ + (t/‖A‖)·A` the other (`Ttc.FacetSystem.facet_of_ball_subset`) — and both
  directions are used: the assembly *assumes* the ball form (so the audit surface
  states the paper's hypothesis) and *uses* the facet form, but it also needs the
  ball back to know a piece has positive volume.

* **Finiteness from a uniform bound.** `Q ∩ ℤⁿ` must be a `Finset` before it can
  be summed over. Rather than proving `Q` bounded, we get it from `claim:cl`(a)
  itself: that step bounds `|T|` for *every* finite `T ⊆ Q ∩ ℤⁿ` by
  `vol Q'/(1−θ/2)`, and a set all of whose finite subsets have bounded cardinality
  is finite (`Ttc.finite_of_forall_finset_card_le`).

* **Lattice points as `ℤⁿ`.** `Ttc.latPt` embeds `ℤⁿ` in `ℝⁿ`; the counting side
  of `lem:nonconv` sums over `Fin n → ℤ`, while `lem:lattice` counts
  `Q ∩ Ttc.intLattice n`. `Ttc.ncard_inter_intLattice` says these agree.
-/

namespace Ttc

open MeasureTheory Set

variable {n : ℕ} {ι F : Type*}

/-! ## The linear form of a coefficient vector -/

/-- A coefficient vector, as a point of `ℝⁿ`. -/
noncomputable def coeffPt (A : Fin n → ℝ) : Space n := (WithLp.toLp 2 A : Space n)

@[simp] theorem coeffPt_apply (A : Fin n → ℝ) (k : Fin n) : (coeffPt A) k = A k := rfl

/-- The paper's `A·x`, as an inner product. -/
theorem sum_mul_eq_inner (A : Fin n → ℝ) (y : Space n) :
    ∑ k, A k * y k = inner ℝ (coeffPt A) y := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun k _ => by simp [RCLike.inner_apply, mul_comm]

/-- `Ttc.coeffNorm` is the norm of the coefficient vector. -/
theorem norm_coeffPt (A : Fin n → ℝ) : ‖coeffPt A‖ = coeffNorm A := by
  rw [EuclideanSpace.norm_eq, coeffNorm]
  exact congrArg Real.sqrt (Finset.sum_congr rfl fun k _ => by simp [Real.norm_eq_abs, sq_abs])

/-- **Cauchy–Schwarz**, in the form the ball argument uses. -/
theorem sum_mul_le_coeffNorm_mul (A : Fin n → ℝ) (y : Space n) :
    ∑ k, A k * y k ≤ coeffNorm A * ‖y‖ := by
  rw [sum_mul_eq_inner, ← norm_coeffPt]
  exact le_trans (real_inner_le_norm _ _) le_rfl

namespace FacetSystem

/-! ## Ball ↔ facet -/

/-- **Facet form ⟹ inscribed ball.** If every facet of piece `i` satisfies
`γ·w j ≤ b j + t·w j − f j c`, then `B(c, γ) ⊆ P(t)ᵢ`. Cauchy–Schwarz. -/
theorem ball_subset_piece (S : FacetSystem n ι F) (Aof : F → Fin n → ℝ)
    (hf : ∀ (j : F) (x : Space n), S.f j x = ∑ k, Aof j k * x k)
    (hw : ∀ j, S.w j = coeffNorm (Aof j))
    {γ t : ℝ} {c : Space n} {i : ι}
    (hball : ∀ j, S.part j = i → γ * S.w j ≤ S.b j + t * S.w j - S.f j c) :
    Metric.ball c γ ⊆ S.piece t i := by
  intro x hx j hj
  have hd : ‖x - c‖ < γ := by rwa [Metric.mem_ball, dist_eq_norm] at hx
  have hlin : S.f j x - S.f j c = S.f j (x - c) := by rw [map_sub]
  have hcs : S.f j (x - c) ≤ S.w j * ‖x - c‖ := by
    rw [hf, hw]
    exact sum_mul_le_coeffNorm_mul _ _
  have hmul : S.w j * ‖x - c‖ ≤ S.w j * γ :=
    mul_le_mul_of_nonneg_left hd.le (S.w_nonneg j)
  have := hball j hj
  linarith

/-- **Inscribed ball ⟹ facet form.** The converse, by evaluating at
`c + (t/‖A‖)·A`: this is why the paper's hypothesis and the per-facet inequality
its proof uses are the same hypothesis. -/
theorem facet_of_ball_subset (S : FacetSystem n ι F) (Aof : F → Fin n → ℝ)
    (hf : ∀ (j : F) (x : Space n), S.f j x = ∑ k, Aof j k * x k)
    (hw : ∀ j, S.w j = coeffNorm (Aof j))
    {γ : ℝ} (hγ : 0 < γ) {c : Space n} {i : ι}
    (h : Metric.ball c γ ⊆ S.piece 0 i) (j : F) (hj : S.part j = i) :
    γ * S.w j ≤ S.b j - S.f j c := by
  have hc : S.f j c ≤ S.b j := by
    have := h (Metric.mem_ball_self hγ) j hj
    simpa using this
  rcases eq_or_lt_of_le (S.w_nonneg j) with hw0 | hwpos
  · rw [← hw0]; linarith
  by_contra hcon
  push Not at hcon
  set s : ℝ := (S.b j - S.f j c) / S.w j with hs
  have hs0 : 0 ≤ s := div_nonneg (by linarith) (S.w_nonneg j)
  have hsγ : s < γ := by rw [hs, div_lt_iff₀ hwpos]; linarith
  set t : ℝ := (s + γ) / 2 with ht
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  have htγ : t < γ := by rw [ht]; linarith
  have hst : s < t := by rw [ht]; linarith
  -- the witness point `c + (t/w) • A`
  set x : Space n := c + (t / S.w j) • coeffPt (Aof j) with hx
  have hnorm : ‖x - c‖ = t := by
    rw [hx, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg ht0 (S.w_nonneg j)), norm_coeffPt, ← hw]
    field_simp
  have hmem : x ∈ Metric.ball c γ := by
    rw [Metric.mem_ball, dist_eq_norm, hnorm]; exact htγ
  have hfA : S.f j (coeffPt (Aof j)) = S.w j ^ 2 := by
    rw [hf, hw, coeffNorm_sq]
    exact Finset.sum_congr rfl fun k _ => by rw [coeffPt_apply]; ring
  have hval : S.f j x = S.f j c + t * S.w j := by
    rw [hx, map_add, map_smul, smul_eq_mul, hfA]
    field_simp
  have hle : S.f j x ≤ S.b j := by simpa using h hmem j hj
  rw [hval] at hle
  have : s * S.w j = S.b j - S.f j c := by rw [hs]; field_simp
  nlinarith

end FacetSystem

/-! ## Finiteness from a uniform cardinality bound -/

/-- A set all of whose finite subsets have cardinality at most `C` is finite. This
is how `Q ∩ ℤⁿ` is known to be finite: `claim:cl`(a) bounds every finite subset. -/
theorem finite_of_forall_finset_card_le {α : Type*} {s : Set α} {C : ℝ}
    (h : ∀ T : Finset α, (↑T : Set α) ⊆ s → (T.card : ℝ) ≤ C) : s.Finite := by
  by_contra hinf
  obtain ⟨T, hTs, hTcard⟩ := Set.Infinite.exists_subset_card_eq hinf (⌈C⌉₊ + 1)
  have h1 := h T hTs
  rw [hTcard] at h1
  have h2 : C ≤ (⌈C⌉₊ : ℝ) := Nat.le_ceil C
  push_cast at h1
  linarith

/-! ## Lattice points as `ℤⁿ` -/

/-- `Ttc.latPt` is injective. -/
theorem latPt_injective : Function.Injective (latPt (n := n)) := by
  intro z w h
  funext k
  have hk : ((z k : ℝ)) = ((w k : ℝ)) := congrFun (congrArg WithLp.ofLp h) k
  exact_mod_cast hk

/-- The image of `ℤⁿ` under `Ttc.latPt` is the integer lattice. -/
theorem image_latPt_eq (X : Set (Space n)) :
    latPt '' {z : Fin n → ℤ | latPt z ∈ X} = X ∩ intLattice n := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨hz, fun k => ⟨z k, rfl⟩⟩
  · rintro ⟨hy, hlat⟩
    choose z hz using hlat
    have hzy : latPt z = y := by
      have hfun : (fun k => ((z k : ℝ))) = WithLp.ofLp y := funext fun k => (hz k).symm
      show (WithLp.toLp 2 (fun k => ((z k : ℝ))) : Space n) = y
      rw [hfun]
    exact ⟨z, by show latPt z ∈ X; rw [hzy]; exact hy, hzy⟩

/-- **Counting on `ℤⁿ` is counting lattice points.** -/
theorem ncard_inter_intLattice (X : Set (Space n)) :
    (X ∩ intLattice n).ncard = {z : Fin n → ℤ | latPt z ∈ X}.ncard := by
  rw [← image_latPt_eq X, Set.ncard_image_of_injective _ latPt_injective]

end Ttc
