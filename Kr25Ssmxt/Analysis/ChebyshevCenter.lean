import Kr25Ssmxt.Model.Run

/-!
# `MaxInscribedBall` attains its optimum

A component's `inradius` `γ` and `incenter` `z` are the optimum value and a chosen optimal
centre of the Chebyshev-centre LP (`Model/Prelude.lean`). The LP's feasible pairs `(c, t)`
with `t ≥ 0` are the `ℓ₂` balls inside the component; they form a compact nonempty set, since
`c` lies in the bounded component and `t` is at most the outer radius. So the optimum is
attained, and `B₂(z, γ)` is a largest ball inside the component: `inradius_pos`, `inball`
and `inradius_max`.
-/

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Kr25Ssmxt

/-- An `ℓ₂` ball of radius `t ≥ 0` lies in the carrier exactly when `(c, t)` is LP-feasible. -/
theorem euclideanBall_subset_iff_chebyshevFeasible {n : Nat} (H : HalfspacePresentation n)
    (c : Point n) {t : Real} (ht : 0 ≤ t) :
    euclideanBall c t ⊆ H.carrier ↔ H.chebyshevFeasible c t := by
  constructor
  · intro hsub j
    by_cases ha : toEuclidean (H.normal j) = 0
    · have hc : c ∈ euclideanBall c t := by simpa [euclideanBall] using ht
      have := hsub hc j
      rw [ha, norm_zero, mul_zero, add_zero]
      exact this
    · set a := toEuclidean (H.normal j)
      have hpos : 0 < ‖a‖ := norm_pos_iff.mpr ha
      let x : Point n := c + (t / ‖a‖) • H.normal j
      have hx : x ∈ euclideanBall c t := by
        change ‖(WithLp.toLp 2 (x - c) : EuclideanSpace Real (Fin n))‖ ≤ t
        have hxc : x - c = (t / ‖a‖) • H.normal j := by simp [x]
        rw [hxc, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg ht hpos.le)]
        change t / ‖a‖ * ‖a‖ ≤ t
        rw [div_mul_cancel₀ _ hpos.ne']
      have hdot := hsub hx j
      have hself : dotProduct (H.normal j) (H.normal j) = ‖a‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq]
        change dotProduct (H.normal j) (H.normal j) =
          dotProduct (H.normal j) (H.normal j)
        rfl
      have hexp : dotProduct (H.normal j) x =
          dotProduct (H.normal j) c + t * ‖a‖ := by
        simp only [x, dotProduct_add, dotProduct_smul, smul_eq_mul, hself]
        field_simp
      change dotProduct (H.normal j) x ≤ H.offset j at hdot
      linarith
  · intro hfeas x hx j
    change dotProduct (H.normal j) x ≤ H.offset j
    have hx' : ‖(WithLp.toLp 2 (x - c) : EuclideanSpace Real (Fin n))‖ ≤ t := hx
    have hcs : dotProduct (H.normal j) (x - c) ≤
        ‖toEuclidean (H.normal j)‖ * ‖(WithLp.toLp 2 (x - c) : EuclideanSpace Real (Fin n))‖ := by
      have := real_inner_le_norm (toEuclidean (H.normal j))
        (WithLp.toLp 2 (x - c) : EuclideanSpace Real (Fin n))
      have heq : ⟪toEuclidean (H.normal j),
          (WithLp.toLp 2 (x - c) : EuclideanSpace Real (Fin n))⟫_Real =
          dotProduct (H.normal j) (x - c) := by
        change dotProduct (x - c) (H.normal j) = _
        exact dotProduct_comm _ _
      linarith
    have hsplit : dotProduct (H.normal j) x =
        dotProduct (H.normal j) c + dotProduct (H.normal j) (x - c) := by
      rw [dotProduct_sub]; ring
    have hnorm := norm_nonneg (toEuclidean (H.normal j))
    have := hfeas j
    nlinarith

/-- A ball of radius `r ≥ 0` inside the component has `r ≤ R`. -/
theorem PolytopeData.le_outerRadius_of_ball {n : Nat} (P : PolytopeData n)
    {c : Point n} {r : Real} (hr : 0 ≤ r)
    (hsub : euclideanBall c r ⊆ P.presentation.carrier) : r ≤ P.outerRadius := by
  rcases hr.eq_or_lt with hz | hpos
  · rw [← hz]; exact P.outerRadius_nonneg
  let e : Point n := Pi.single ⟨0, P.dim_pos⟩ (1 : Real)
  have heE : ‖toEuclidean e‖ = 1 := by
    simp [toEuclidean, e]
  let x : Point n := c + r • e
  let y : Point n := c - r • e
  have hx : x ∈ P.presentation.carrier := by
    apply hsub
    change ‖(WithLp.toLp 2 (x - c) : EuclideanSpace Real (Fin n))‖ ≤ r
    have hxc : x - c = r • e := by simp [x]
    rw [hxc, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
    change r * ‖toEuclidean e‖ ≤ _
    rw [heE, mul_one]
  have hy : y ∈ P.presentation.carrier := by
    apply hsub
    change ‖(WithLp.toLp 2 (y - c) : EuclideanSpace Real (Fin n))‖ ≤ r
    have hyc : y - c = -(r • e) := by simp [y]
    rw [hyc, WithLp.toLp_neg, norm_neg, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos hpos]
    change r * ‖toEuclidean e‖ ≤ _
    rw [heE, mul_one]
  have hxR := P.outer_bound x hx
  have hyR := P.outer_bound y hy
  have hxy : dist (toEuclidean x) (toEuclidean y) = 2 * r := by
    have heq : toEuclidean x - toEuclidean y = (2 * r) • toEuclidean e := by
      ext i
      simp [x, y, toEuclidean, PiLp.smul_apply, PiLp.add_apply]
      ring
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < 2 * r), heE]
    ring
  have hsplit : toEuclidean x - toEuclidean y =
      toEuclidean (x - P.outerCenter) - toEuclidean (y - P.outerCenter) := by
    simp only [toEuclidean, WithLp.toLp_sub]
    abel
  have htri : dist (toEuclidean x) (toEuclidean y) ≤
      ‖toEuclidean (x - P.outerCenter)‖ + ‖toEuclidean (y - P.outerCenter)‖ := by
    rw [dist_eq_norm, hsplit]
    exact norm_sub_le _ _
  change ‖toEuclidean (x - P.outerCenter)‖ ≤ P.outerRadius at hxR
  change ‖toEuclidean (y - P.outerCenter)‖ ≤ P.outerRadius at hyR
  linarith

/-- The LP's nonnegative feasible pairs. -/
private def chebyshevFeasibleSet {n : Nat} (H : HalfspacePresentation n) :
    Set (Point n × Real) :=
  {p | 0 ≤ p.2 ∧ H.chebyshevFeasible p.1 p.2}

private theorem isClosed_chebyshevFeasibleSet {n : Nat} (H : HalfspacePresentation n) :
    IsClosed (chebyshevFeasibleSet H) := by
  have hset : chebyshevFeasibleSet H = {p : Point n × Real | 0 ≤ p.2} ∩
      ⋂ j, {p : Point n × Real |
        dotProduct (H.normal j) p.1 + p.2 * ‖toEuclidean (H.normal j)‖ ≤ H.offset j} := by
    ext p
    simp [chebyshevFeasibleSet, HalfspacePresentation.chebyshevFeasible]
  rw [hset]
  refine (isClosed_le continuous_const continuous_snd).inter (isClosed_iInter fun j => ?_)
  apply isClosed_le _ continuous_const
  have hdot : Continuous fun p : Point n × Real => dotProduct (H.normal j) p.1 := by
    unfold dotProduct
    exact continuous_finset_sum _ fun i _ =>
      continuous_const.mul ((continuous_apply i).comp continuous_fst)
  exact hdot.add (continuous_snd.mul continuous_const)

/-- A nonnegative feasible centre lies in the component. -/
private theorem mem_carrier_of_feasible {n : Nat} (H : HalfspacePresentation n)
    {c : Point n} {t : Real} (ht : 0 ≤ t) (hf : H.chebyshevFeasible c t) :
    c ∈ H.carrier := by
  have hsub := (euclideanBall_subset_iff_chebyshevFeasible H c ht).2 hf
  apply hsub
  change ‖(WithLp.toLp 2 (c - c) : EuclideanSpace Real (Fin n))‖ ≤ t
  simpa using ht

/-- The Chebyshev-centre LP attains its optimum: some feasible `(c, t)` has the largest `t`. -/
theorem PolytopeData.exists_chebyshev_optimum {n : Nat} (P : PolytopeData n) :
    ∃ c t, P.presentation.chebyshevFeasible c t ∧ 0 < t ∧
      IsGreatest {t | ∃ c, P.presentation.chebyshevFeasible c t} t := by
  let H := P.presentation
  let K := chebyshevFeasibleSet H
  have hclosed : IsClosed K := isClosed_chebyshevFeasibleSet H
  have hbdd : Bornology.IsBounded K := by
    refine (P.bounded.prod (Metric.isBounded_Icc (0 : Real) P.outerRadius)).subset ?_
    rintro ⟨c, t⟩ ⟨ht, hf⟩
    refine ⟨mem_carrier_of_feasible H ht hf, ht, ?_⟩
    exact P.le_outerRadius_of_ball ht ((euclideanBall_subset_iff_chebyshevFeasible H c ht).2 hf)
  have hcompact : IsCompact K := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  obtain ⟨c₀, r₀, hr₀, hball₀⟩ := P.fullDimensional
  have hmem₀ : (c₀, r₀) ∈ K :=
    ⟨hr₀.le, (euclideanBall_subset_iff_chebyshevFeasible H c₀ hr₀.le).1 hball₀⟩
  obtain ⟨⟨c, t⟩, hmem, hmax⟩ :=
    hcompact.exists_isMaxOn ⟨_, hmem₀⟩ continuous_snd.continuousOn
  have ht₀ : r₀ ≤ t := hmax hmem₀
  refine ⟨c, t, hmem.2, lt_of_lt_of_le hr₀ ht₀, ⟨c, hmem.2⟩, ?_⟩
  rintro s ⟨c', hs⟩
  rcases le_or_gt 0 s with hs0 | hs0
  · exact hmax (show (c', s) ∈ K from ⟨hs0, hs⟩)
  · linarith [hmem.1]

/-- `γ` is the LP's largest feasible value. -/
theorem PolytopeData.isGreatest_inradius {n : Nat} (P : PolytopeData n) :
    IsGreatest {t | ∃ c, P.presentation.chebyshevFeasible c t} P.inradius := by
  obtain ⟨c, t, -, -, hg⟩ := P.exists_chebyshev_optimum
  have : P.inradius = t := hg.csSup_eq
  rw [this]
  exact hg

theorem PolytopeData.inradius_pos {n : Nat} (P : PolytopeData n) : 0 < P.inradius := by
  obtain ⟨c, t, -, ht, hg⟩ := P.exists_chebyshev_optimum
  have : P.inradius = t := hg.csSup_eq
  rw [this]
  exact ht

/-- `(z, γ)` is an optimal point of the LP. -/
theorem PolytopeData.chebyshevFeasible_incenter {n : Nat} (P : PolytopeData n) :
    P.presentation.chebyshevFeasible P.incenter P.inradius := by
  obtain ⟨c, hc⟩ := P.isGreatest_inradius.1
  exact Classical.epsilon_spec (p := fun c => P.presentation.chebyshevFeasible c
    P.presentation.MaxInscribedBall) ⟨c, hc⟩

/-- `B₂(z, γ) ⊆ P`. -/
theorem PolytopeData.inball {n : Nat} (P : PolytopeData n) :
    euclideanBall P.incenter P.inradius ⊆ P.presentation.carrier :=
  (euclideanBall_subset_iff_chebyshevFeasible P.presentation P.incenter
    P.inradius_pos.le).2 P.chebyshevFeasible_incenter

/-- No `ℓ₂` ball larger than `γ` fits inside the component. -/
theorem PolytopeData.inradius_max {n : Nat} (P : PolytopeData n) (c : Point n) (r : Real)
    (hsub : euclideanBall c r ⊆ P.presentation.carrier) : r ≤ P.inradius := by
  rcases le_or_gt 0 r with hr | hr
  · exact P.isGreatest_inradius.2
      ⟨c, (euclideanBall_subset_iff_chebyshevFeasible P.presentation c hr).1 hsub⟩
  · linarith [P.inradius_pos]

end Kr25Ssmxt
