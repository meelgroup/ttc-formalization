import Kr25Ssmxt.Analysis.ArlibPolytopeBridge
import ArlibCommunity.Algorithms.HitAndRun.Model.Theorem
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Lattice.KV97.Inflate

/-!
# Finite-step Hit-and-Run on a TTC scaled polytope

This is the first algorithmic specialization of the TTC/Arlib geometry bridge.  It turns
the certified decimal-scaled inball and boundedness data into an actual finite-step
Hit-and-Run law with a total-variation guarantee.
-/

noncomputable section

namespace Kr25Ssmxt

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

private theorem dist_homothety_apply (c : EuclideanSpace Real (Fin n)) (k : Real)
    (p q : EuclideanSpace Real (Fin n)) :
    dist (AffineMap.homothety c k p) (AffineMap.homothety c k q) = |k| * dist p q := by
  simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, dist_eq_norm]
  rw [show (k • (p - c) + c) - (k • (q - c) + c) = k • (p - q) by module,
    norm_smul, Real.norm_eq_abs]

theorem dist_le_of_mem_inflated {n : Nat} {ι : Type*}
    {A : ι → EuclideanSpace Real (Fin n)} {b : ι → Real}
    {c : EuclideanSpace Real (Fin n)} {gamma D cp r : Real}
    (hgamma : 0 < gamma) (hcp : 0 ≤ cp)
    (hball : Metric.ball c gamma ⊆ Arlib.Polytope.body A b)
    (hD : ∀ x ∈ Arlib.Polytope.body A b, ∀ y ∈ Arlib.Polytope.body A b,
      dist x y ≤ D) :
    ∀ x ∈ Arlib.KV97.inflated A b cp r, ∀ y ∈ Arlib.KV97.inflated A b cp r,
      dist x y ≤ (1 + Arlib.KV97.kappaOf cp r / gamma) * D := by
  have hkappa : 0 ≤ Arlib.KV97.kappaOf cp r := Arlib.KV97.kappaOf_nonneg hcp
  have hk : 0 < 1 + Arlib.KV97.kappaOf cp r / gamma := by positivity
  intro x hx y hy
  obtain ⟨x', hx', rfl⟩ :=
    Arlib.Polytope.inflate_subset_homothety hgamma hkappa hball hx
  obtain ⟨y', hy', rfl⟩ :=
    Arlib.Polytope.inflate_subset_homothety hgamma hkappa hball hy
  rw [dist_homothety_apply, abs_of_nonneg hk.le]
  exact mul_le_mul_of_nonneg_left (hD x' hx' y' hy') hk.le

/-- Compatibility wrapper for the former `HitAndRunFromInball` API.  It proves that
the uniform law on an included unit ball is a warm start, then invokes the public
arlib-community Hit-and-Run headline theorem `HitAndRun.hitAndRun_mixes`. -/
theorem tvLe_iterate_lazy_hitAndRun_from_unit_inball {n : Nat} (hn : 21 ≤ n)
    {K : Set (EuclideanSpace Real (Fin n))}
    (hKc : Convex Real K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K) {z : EuclideanSpace Real (Fin n)}
    (hball : Metric.closedBall z 1 ⊆ K) {D : Real}
    (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    {eps : Real} (heps0 : 0 < eps) (heps1 : eps ≤ 1) {m : Nat}
    (hm : Arlib.MarkovChains.hrDeadlineUncond n D
      (volume K / volume (Metric.ball z 1)).toReal eps ≤ (m : Real)) :
    Arlib.TVLe
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy (Arlib.MarkovChains.hitAndRun K))
        (Arlib.uniformOn volume (Metric.ball z 1)) m)
      (Arlib.uniformOn volume K) (ENNReal.ofReal eps) := by
  let B : Set (EuclideanSpace Real (Fin n)) := Metric.ball z 1
  let M : Real := (volume K / volume B).toReal
  have hBsub : B ⊆ K := Metric.ball_subset_closedBall.trans hball
  have hB0 : volume B ≠ 0 := (Metric.measure_ball_pos volume z one_pos).ne'
  have hBtop : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hK0 : volume K ≠ 0 := (lt_of_lt_of_le
    (Metric.measure_ball_pos volume z one_pos) (measure_mono hBsub)).ne'
  have hKtop : volume K ≠ ⊤ := hKb.measure_lt_top.ne
  letI : IsProbabilityMeasure (Arlib.uniformOn volume B) :=
    Arlib.isProbabilityMeasure_uniformOn volume hB0 hBtop
  have hratioTop : volume K / volume B ≠ ⊤ := ENNReal.div_ne_top hKtop hB0
  have hM : 1 ≤ M := by
    change 1 ≤ (volume K / volume B).toReal
    rw [show (1 : Real) = (1 : ENNReal).toReal by simp]
    apply ENNReal.toReal_mono hratioTop
    rw [ENNReal.div_eq_inv_mul, ← ENNReal.inv_mul_cancel hB0 hBtop]
    simpa [mul_comm] using mul_le_mul_left (measure_mono hBsub) (volume B)⁻¹
  have hdiam : Metric.diam K ≤ D := by
    have hD0 : 0 ≤ D := by
      have hz : z ∈ K := hball (Metric.mem_closedBall_self zero_le_one)
      simpa using hD z hz z hz
    exact Metric.diam_le_of_forall_dist_le hD0 hD
  let problem : ArlibCommunity.Algorithms.HitAndRun.Problem n :=
    { body := K
      center := z
      diameter := D
      convex_body := hKc
      closed_body := hKcl
      measurable_body := hKm
      bounded_body := hKb
      unitBall_subset := hball
      diam_le := hdiam }
  have hdom : ∀ A : Set (EuclideanSpace Real (Fin n)), MeasurableSet A →
      Arlib.uniformOn volume B (A \ ∅) ≤
        ENNReal.ofReal M * Arlib.uniformOn volume K A := by
    intro A hA
    rw [Set.diff_empty, Arlib.uniformOn_apply volume measurableSet_ball hA,
      Arlib.uniformOn_apply volume hKm hA]
    have hinter : volume (A ∩ B) ≤ volume (A ∩ K) :=
      measure_mono (Set.inter_subset_inter_right _ hBsub)
    have hMenn : ENNReal.ofReal M = volume K / volume B := by
      change ENNReal.ofReal (volume K / volume B).toReal = volume K / volume B
      exact ENNReal.ofReal_toReal hratioTop
    rw [hMenn]
    calc
      volume (A ∩ B) / volume B ≤ volume (A ∩ K) / volume B :=
        ENNReal.div_le_div_right hinter (volume B)
      _ = (volume K / volume B) * (volume (A ∩ K) / volume K) := by
        simp only [ENNReal.div_eq_inv_mul]
        calc
          (volume B)⁻¹ * volume (A ∩ K) =
              (volume B)⁻¹ * (1 * volume (A ∩ K)) := by rw [one_mul]
          _ = (volume B)⁻¹ * ((volume K * (volume K)⁻¹) *
              volume (A ∩ K)) := by
                rw [ENNReal.mul_inv_cancel hK0 hKtop]
          _ = ((volume B)⁻¹ * volume K) *
              ((volume K)⁻¹ * volume (A ∩ K)) := by ac_rfl

  have hwarm : ArlibCommunity.Algorithms.HitAndRun.WarmStart problem.body
      (Arlib.uniformOn volume B) M eps ∅ :=
    ⟨MeasurableSet.empty, by simp, hdom⟩
  -- The public arlib-community Hit-and-Run headline theorem.
  have hmix := ArlibCommunity.Algorithms.HitAndRun.hitAndRun_mixes hn problem
    hM heps0 heps1 hwarm
    (by simpa [ArlibCommunity.Algorithms.HitAndRun.deadline,
      Arlib.MarkovChains.hrDeadlineUncond, problem, M, B] using hm)
  simpa [ArlibCommunity.Algorithms.HitAndRun.run,
    ArlibCommunity.Algorithms.HitAndRun.lazyStep,
    ArlibCommunity.Algorithms.HitAndRun.step,
    ArlibCommunity.Algorithms.HitAndRun.target, problem, B] using hmix

/-- In dimensions covered by Arlib's unconditional Hit-and-Run theorem, every TTC polytope
whose decimal-scaled inradius is at least one admits an explicit finite-step walk law.
The existential `D` is a genuine pairwise-distance bound extracted from certified
boundedness; `m` is chosen past Arlib's displayed deadline. -/
theorem PolytopeData.exists_hitAndRun_scaled_tvLe {n : Nat} (hn : 21 ≤ n)
    (P : PolytopeData n) (b : Nat)
    (hunit : 1 ≤ decimalScale b * P.inradius)
    {eps : Real} (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ (D : Real) (m : Nat),
      (∀ x ∈ P.scaledBody b, ∀ y ∈ P.scaledBody b, dist x y ≤ D) ∧
      Arlib.TVLe
        (Arlib.MarkovChains.iterate
          (Arlib.MarkovChains.lazy (Arlib.MarkovChains.hitAndRun (P.scaledBody b)))
          (Arlib.uniformOn volume
            (Metric.ball (decimalScale b • toEuclidean P.incenter) 1)) m)
        (Arlib.uniformOn volume (P.scaledBody b)) (ENNReal.ofReal eps) := by
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.mp (P.scaledBody_bounded b)
  let M : Real :=
    (volume (P.scaledBody b) /
      volume (Metric.ball (decimalScale b • toEuclidean P.incenter) 1)).toReal
  obtain ⟨m, hm⟩ := exists_nat_ge (Arlib.MarkovChains.hrDeadlineUncond n D M eps)
  refine ⟨D, m, hD, ?_⟩
  have hball : Metric.closedBall (decimalScale b • toEuclidean P.incenter) 1 ⊆
      P.scaledBody b := by
    intro x hx
    apply P.scaledBody_inball b
    exact Metric.mem_closedBall.2 ((Metric.mem_closedBall.1 hx).trans hunit)
  apply tvLe_iterate_lazy_hitAndRun_from_unit_inball
    hn (Arlib.Polytope.convex_body P.arlibNormal (P.scaledOffset b))
    (Arlib.Polytope.isClosed_body P.arlibNormal (P.scaledOffset b))
    (Arlib.Polytope.measurableSet_body P.arlibNormal (P.scaledOffset b))
    (P.scaledBody_bounded b) hball hD heps0 heps1
  exact hm

/-- The same finite-step construction on the Kannan--Vempala inflated body used by
randomized rounding.  In particular, the walk target here is the actual `P'` occurring in
KV97, not the uninflated TTC component. -/
theorem PolytopeData.exists_hitAndRun_inflated_tvLe {n : Nat} (hn : 21 ≤ n)
    (P : PolytopeData n) (b : Nat)
    (hunit : 1 ≤ decimalScale b * P.inradius)
    {cp r eps : Real} (hcp : 0 ≤ cp) (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ (D : Real) (m : Nat),
      (∀ x ∈ Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b) cp r,
        ∀ y ∈ Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b) cp r,
          dist x y ≤ D) ∧
      Arlib.MarkovChains.hrDeadlineUncond n D
          (volume (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b) cp r) /
            volume (Metric.ball (decimalScale b • toEuclidean P.incenter) 1)).toReal eps ≤
        (m : Real) ∧
      m = Nat.ceil (Arlib.MarkovChains.hrDeadlineUncond n D
          (volume (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b) cp r) /
            volume (Metric.ball (decimalScale b • toEuclidean P.incenter) 1)).toReal eps) ∧
      Arlib.TVLe
        (Arlib.MarkovChains.iterate
          (Arlib.MarkovChains.lazy (Arlib.MarkovChains.hitAndRun
            (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b) cp r)))
          (Arlib.uniformOn volume
            (Metric.ball (decimalScale b • toEuclidean P.incenter) 1)) m)
        (Arlib.uniformOn volume
          (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b) cp r))
        (ENNReal.ofReal eps) := by
  let gamma : Real := decimalScale b * P.inradius
  have hgamma : 0 < gamma := mul_pos (decimalScale_pos b) P.inradius_pos
  have hbaseball : Metric.ball (decimalScale b • toEuclidean P.incenter) gamma ⊆
      P.scaledBody b :=
    Metric.ball_subset_closedBall.trans (P.scaledBody_inball b)
  obtain ⟨D₀, hD₀⟩ := Metric.isBounded_iff.mp (P.scaledBody_bounded b)
  let D : Real := (1 + Arlib.KV97.kappaOf cp r / gamma) * D₀
  have hD : ∀ x ∈ Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b) cp r,
      ∀ y ∈ Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b) cp r,
        dist x y ≤ D := by
    simpa [D] using dist_le_of_mem_inflated hgamma hcp hbaseball hD₀
  have hbounded : Bornology.IsBounded
      (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b) cp r) :=
    Metric.isBounded_iff.mpr ⟨D, hD⟩
  have hball : Metric.closedBall (decimalScale b • toEuclidean P.incenter) 1 ⊆
      Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b) cp r := by
    intro x hx
    apply Arlib.KV97.body_subset_inflated P.arlibNormal (P.scaledOffset b) r hcp
    apply P.scaledBody_inball b
    exact Metric.mem_closedBall.2 ((Metric.mem_closedBall.1 hx).trans hunit)
  let M : Real :=
    (volume (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b) cp r) /
      volume (Metric.ball (decimalScale b • toEuclidean P.incenter) 1)).toReal
  let deadline := Arlib.MarkovChains.hrDeadlineUncond n D M eps
  let m := Nat.ceil deadline
  have hm : deadline ≤ (m : Real) := by
    exact Nat.le_ceil deadline
  refine ⟨D, m, hD, ?_, ?_, ?_⟩
  · simpa only [M] using hm
  · simp [m, deadline, M]
  · apply tvLe_iterate_lazy_hitAndRun_from_unit_inball
      hn (Arlib.KV97.convex_inflated P.arlibNormal (P.scaledOffset b) cp r)
      (Arlib.KV97.isClosed_inflated P.arlibNormal (P.scaledOffset b) cp r)
      (Arlib.KV97.measurableSet_inflated P.arlibNormal (P.scaledOffset b) cp r)
      hbounded hball hD heps0 heps1
    exact hm

/-- Hit-and-Run can be run at the inverse-volume tolerance required by the KV97
TV-to-pointwise transfer.  If that requested tolerance exceeds one, the walk is run to
tolerance one and monotonicity supplies the displayed (weaker) bound. -/
theorem PolytopeData.exists_hitAndRun_inflated_tvLe_inv_volume {n : Nat} (hn : 21 ≤ n)
    (P : PolytopeData n) (b : Nat)
    (hunit : 1 ≤ decimalScale b * P.inradius)
    {cp r theta : Real} (hcp : 0 ≤ cp) (htheta : 0 < theta) :
    ∃ (D : Real) (m : Nat),
      (∀ x ∈ Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b) cp r,
        ∀ y ∈ Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b) cp r,
          dist x y ≤ D) ∧
      Arlib.MarkovChains.hrDeadlineUncond n D
          (volume (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b) cp r) /
            volume (Metric.ball (decimalScale b • toEuclidean P.incenter) 1)).toReal
          (min 1 (theta /
            (volume (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b) cp r)).toReal)) ≤
        (m : Real) ∧
      m = Nat.ceil (Arlib.MarkovChains.hrDeadlineUncond n D
          (volume (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b) cp r) /
            volume (Metric.ball (decimalScale b • toEuclidean P.incenter) 1)).toReal
          (min 1 (theta /
            (volume (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b) cp r)).toReal))) ∧
      Arlib.TVLe
        (Arlib.MarkovChains.iterate
          (Arlib.MarkovChains.lazy (Arlib.MarkovChains.hitAndRun
            (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b) cp r)))
          (Arlib.uniformOn volume
            (Metric.ball (decimalScale b • toEuclidean P.incenter) 1)) m)
        (Arlib.uniformOn volume
          (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b) cp r))
        (ENNReal.ofReal (theta /
          (volume (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b) cp r)).toReal)) := by
  let gamma : Real := decimalScale b * P.inradius
  have hgamma : 0 < gamma := mul_pos (decimalScale_pos b) P.inradius_pos
  have hbaseball : Metric.ball (decimalScale b • toEuclidean P.incenter) gamma ⊆
      P.scaledBody b :=
    Metric.ball_subset_closedBall.trans (P.scaledBody_inball b)
  have hfin : volume (P.scaledBody b) ≠ ⊤ :=
    (P.scaledBody_bounded b).measure_lt_top.ne
  have hV : 0 <
      (volume (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b) cp r)).toReal :=
    Arlib.KV97.toReal_volume_inflated_pos hgamma hcp hbaseball hfin
  let eps : Real := min 1 (theta /
    (volume (Arlib.KV97.inflated P.arlibNormal (P.scaledOffset b) cp r)).toReal)
  have heps0 : 0 < eps := (lt_min_iff).2 ⟨one_pos, div_pos htheta hV⟩
  have heps1 : eps ≤ 1 := min_le_left _ _
  obtain ⟨D, m, hD, hdeadline, hmceil, htv⟩ :=
    P.exists_hitAndRun_inflated_tvLe hn b hunit hcp heps0 heps1
  refine ⟨D, m, hD, ?_, ?_, htv.mono ?_⟩
  · simpa only [eps] using hdeadline
  · simpa only [eps] using hmceil
  · exact ENNReal.ofReal_mono (min_le_right _ _)

/-- Boundedness of the exact inflated body named on the model surface. -/
theorem PolytopeData.hitAndRunBody_bounded {n : Nat} (P : PolytopeData n)
    (b : Nat) (eta : Real) : Bornology.IsBounded (hitAndRunBody P b eta) := by
  let gamma : Real := decimalScale b * P.inradius
  have hgamma : 0 < gamma := mul_pos (decimalScale_pos b) P.inradius_pos
  have hbaseball : Metric.ball (decimalScale b • toEuclidean P.incenter) gamma ⊆
      P.scaledBody b :=
    Metric.ball_subset_closedBall.trans (P.scaledBody_inball b)
  obtain ⟨D₀, hD₀⟩ := Metric.isBounded_iff.mp (P.scaledBody_bounded b)
  let D : Real :=
    (1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf eta)
      (P.presentation.facetCount : Real) / gamma) * D₀
  apply Metric.isBounded_iff.mpr
  refine ⟨D, ?_⟩
  simpa [hitAndRunBody, D] using
    (dist_le_of_mem_inflated hgamma Arlib.KV97.cOf_nonneg hbaseball hD₀)

end Kr25Ssmxt
