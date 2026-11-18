import Kr25Ssmxt.Analysis.EuclideanInball

/-!
# `BoundingRadius` against the true outer radius

`P ⊆ B₂(z, R₀)`, `γ ≤ R₀`, and Proposition `prop:bounding-radius`: the coordinate-LP radius
`R₀` about the inscribed ball's centre is at most `2√n R`.
-/

noncomputable section

namespace Kr25Ssmxt

theorem PolytopeData.coordinate_abs_le_outerRadius {n : Nat} (P : PolytopeData n)
    {x : Point n} (hx : x ∈ P.carrier) (j : Fin n) : |x j| ≤ P.outerRadius := by
  have h := PiLp.norm_apply_le (WithLp.toLp 2 x : EuclideanSpace Real (Fin n)) j
  have hR := P.outer_bound x hx
  simpa [Real.norm_eq_abs] using h.trans hR

theorem PolytopeData.coordinate_bddBelow {n : Nat} (P : PolytopeData n) (j : Fin n) :
    BddBelow ((fun x : Point n => x j) '' P.presentation.carrier) := by
  refine ⟨-P.outerRadius, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact (abs_le.mp (P.coordinate_abs_le_outerRadius hy j)).1

theorem PolytopeData.coordinate_bddAbove {n : Nat} (P : PolytopeData n) (j : Fin n) :
    BddAbove ((fun x : Point n => x j) '' P.presentation.carrier) := by
  refine ⟨P.outerRadius, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact (abs_le.mp (P.coordinate_abs_le_outerRadius hy j)).2

/-- Every point of the component lies between the coordinate LP optima. -/
theorem PolytopeData.coordinate_bounds {n : Nat} (P : PolytopeData n)
    {x : Point n} (hx : x ∈ P.carrier) (j : Fin n) :
    P.presentation.coordinateMin j ≤ x j ∧ x j ≤ P.presentation.coordinateMax j :=
  ⟨csInf_le (P.coordinate_bddBelow j) ⟨x, hx, rfl⟩,
    le_csSup (P.coordinate_bddAbove j) ⟨x, hx, rfl⟩⟩

/-- `P ⊆ B₂(z, BoundingRadius P)`. -/
theorem PolytopeData.norm_sub_incenter_le_boundingRadius {n : Nat} (P : PolytopeData n)
    {x : Point n} (hx : x ∈ P.carrier) :
    ‖toEuclidean (x - P.incenter)‖ ≤ P.BoundingRadius := by
  rw [EuclideanSpace.norm_eq]
  unfold PolytopeData.BoundingRadius
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro j _
  obtain ⟨hl, hu⟩ := P.coordinate_bounds hx j
  have hmax : |x j - P.incenter j| ≤
      max |P.presentation.coordinateMin j - P.incenter j|
        |P.presentation.coordinateMax j - P.incenter j| := by
    apply abs_le.mpr
    constructor
    · have h1 := neg_abs_le (P.presentation.coordinateMin j - P.incenter j)
      have h2 := le_max_left |P.presentation.coordinateMin j - P.incenter j|
        |P.presentation.coordinateMax j - P.incenter j|
      linarith
    · have h1 := le_abs_self (P.presentation.coordinateMax j - P.incenter j)
      have h2 := le_max_right |P.presentation.coordinateMin j - P.incenter j|
        |P.presentation.coordinateMax j - P.incenter j|
      linarith
  calc ‖(toEuclidean (x - P.incenter)) j‖ ^ 2 = |x j - P.incenter j| ^ 2 := by
        simp [toEuclidean, Real.norm_eq_abs]
    _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) hmax 2

theorem PolytopeData.boundingRadius_nonneg {n : Nat} (P : PolytopeData n) :
    0 ≤ P.BoundingRadius := Real.sqrt_nonneg _

/-- `γ ≤ R₀`: the inscribed ball lies in `B₂(z, R₀)`. -/
theorem PolytopeData.inradius_le_boundingRadius {n : Nat}
    (P : PolytopeData n) (hn : 0 < n) : P.inradius ≤ P.BoundingRadius := by
  let e : Point n := Pi.single ⟨0, hn⟩ (1 : Real)
  have heE : ‖toEuclidean e‖ = 1 := by
    simp [toEuclidean, e]
  let x : Point n := P.incenter + P.inradius • e
  have hxc : x - P.incenter = P.inradius • e := by simp [x]
  have hnorm : ‖toEuclidean (x - P.incenter)‖ = P.inradius := by
    rw [hxc]
    change ‖(WithLp.toLp 2 (P.inradius • e) : EuclideanSpace Real (Fin n))‖ = _
    rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos P.inradius_pos]
    change P.inradius * ‖toEuclidean e‖ = _
    rw [heE, mul_one]
  have hx : x ∈ P.carrier := by
    apply P.inball
    change ‖toEuclidean (x - P.incenter)‖ ≤ P.inradius
    rw [hnorm]
  have h := P.norm_sub_incenter_le_boundingRadius hx
  rwa [hnorm] at h

/-- The coordinate LP optima lie within the outer radius. -/
theorem PolytopeData.coordinate_optima_abs_le {n : Nat} (P : PolytopeData n) (j : Fin n) :
    |P.presentation.coordinateMin j| ≤ P.outerRadius ∧
      |P.presentation.coordinateMax j| ≤ P.outerRadius := by
  have hne : ((fun x : Point n => x j) '' P.presentation.carrier).Nonempty :=
    ⟨_, P.incenter, P.incenter_mem_carrier, rfl⟩
  have hlow : -P.outerRadius ≤ P.presentation.coordinateMin j :=
    le_csInf hne (by
      rintro _ ⟨y, hy, rfl⟩
      exact (abs_le.mp (P.coordinate_abs_le_outerRadius hy j)).1)
  have hup : P.presentation.coordinateMax j ≤ P.outerRadius :=
    csSup_le hne (by
      rintro _ ⟨y, hy, rfl⟩
      exact (abs_le.mp (P.coordinate_abs_le_outerRadius hy j)).2)
  obtain ⟨hl, hu⟩ := P.coordinate_bounds P.incenter_mem_carrier j
  have hz := abs_le.mp (P.coordinate_abs_le_outerRadius P.incenter_mem_carrier j)
  exact ⟨abs_le.mpr ⟨hlow, by linarith⟩, abs_le.mpr ⟨by linarith, hup⟩⟩

/-- Proposition `prop:bounding-radius`: `R₀ ≤ 2√n R` for any enclosing radius `R`. -/
theorem PolytopeData.boundingRadius_le {n : Nat} (P : PolytopeData n) :
    P.BoundingRadius ≤ 2 * Real.sqrt n * P.outerRadius := by
  have hR := P.outerRadius_nonneg
  have hterm : ∀ j : Fin n,
      (max |P.presentation.coordinateMin j - P.incenter j|
        |P.presentation.coordinateMax j - P.incenter j|) ^ 2 ≤ (2 * P.outerRadius) ^ 2 := by
    intro j
    obtain ⟨hl, hu⟩ := P.coordinate_optima_abs_le j
    have hz := P.coordinate_abs_le_outerRadius P.incenter_mem_carrier j
    have h1 : |P.presentation.coordinateMin j - P.incenter j| ≤ 2 * P.outerRadius :=
      (abs_sub _ _).trans (by linarith)
    have h2 : |P.presentation.coordinateMax j - P.incenter j| ≤ 2 * P.outerRadius :=
      (abs_sub _ _).trans (by linarith)
    exact pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) (max_le h1 h2) 2
  unfold PolytopeData.BoundingRadius
  calc Real.sqrt (∑ j : Fin n, _) ≤ Real.sqrt (∑ _j : Fin n, (2 * P.outerRadius) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => hterm j)
    _ = 2 * Real.sqrt n * P.outerRadius := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
        ring

end Kr25Ssmxt
