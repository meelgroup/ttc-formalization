import ttc.Analysis.ScaledBody
import ttc.Analysis.BoundingRadius
import ttc.Analysis.ArlibPolytopeBridge
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Normalising a TTC component for the CV18 Gaussian-cooling development

The Gaussian-cooling theorems in Arlib are stated for a convex body containing the unit ball
at the origin.  TTC stores an arbitrary certified incenter and positive inradius.  This file
records the exact affine chart, its geometry, and its Jacobian.  It is the geometry adapter
needed before the remaining CV18 estimator assembly can be applied.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal InnerProductSpace

namespace ttc

private lemma measurable_cv18Chart {n : Nat} (gamma : Real)
    (center : EuclideanSpace Real (Fin n)) :
    Measurable (fun y : EuclideanSpace Real (Fin n) => gamma • y + center) := by
  fun_prop

private lemma volume_preimage_cv18Chart {n : Nat} {gamma : Real} (hgamma : 0 < gamma)
    (center : EuclideanSpace Real (Fin n)) (A : Set (EuclideanSpace Real (Fin n))) :
    volume ((fun y : EuclideanSpace Real (Fin n) => gamma • y + center) ⁻¹' A) =
      ENNReal.ofReal ((gamma ^ n)⁻¹) * volume A := by
  have hpre : (fun y : EuclideanSpace Real (Fin n) => gamma • y + center) ⁻¹' A =
      (fun y : EuclideanSpace Real (Fin n) => gamma • y) ⁻¹'
        ((fun y : EuclideanSpace Real (Fin n) => y + center) ⁻¹' A) := rfl
  rw [hpre, Measure.addHaar_preimage_smul volume hgamma.ne', measure_preimage_add_right,
    finrank_euclideanSpace_fin, abs_of_pos (by positivity : (0 : Real) < (gamma ^ n)⁻¹)]

private lemma preimage_cv18Chart_ball {n : Nat} {gamma : Real} (hgamma : 0 < gamma)
    (center y : EuclideanSpace Real (Fin n)) (delta : Real) :
    (fun z : EuclideanSpace Real (Fin n) => gamma • z + center) ⁻¹'
        ball (gamma • y + center) delta = ball y (delta / gamma) := by
  ext z
  simp only [mem_preimage, mem_ball, dist_eq_norm]
  rw [show gamma • z + center - (gamma • y + center) = gamma • (z - y) by module,
    norm_smul, Real.norm_eq_abs, abs_of_pos hgamma, lt_div_iff₀ hgamma]
  simp [mul_comm]

/-- The Arlib presentation of the unscaled TTC component. -/
def PolytopeData.arlibBody {n : Nat} (P : PolytopeData n) :
    Set (EuclideanSpace Real (Fin n)) :=
  ArlibCommunity.Foundations.Convex.Polytope.body P.arlibNormal P.presentation.offset

/-- Facet normals after translating by the certified incenter and scaling the inball to
unit radius. -/
def PolytopeData.cv18Normal {n : Nat} (P : PolytopeData n) :
    Fin P.presentation.facetCount → EuclideanSpace Real (Fin n) :=
  fun i => P.inradius • P.arlibNormal i

/-- Facet offsets in the same normalized coordinates. -/
def PolytopeData.cv18Offset {n : Nat} (P : PolytopeData n) :
  Fin P.presentation.facetCount → Real :=
  fun i => P.presentation.offset i -
    inner Real (P.arlibNormal i) (toEuclidean P.incenter)

/-- The affine-preimage definition of the CV18 body is definitionally represented by the
finite normalized halfspace family.  This exposes the executable chord scan to Arlib. -/
lemma PolytopeData.cv18Body_eq_polytopeBody {n : Nat} (P : PolytopeData n) :
    P.cv18Body = ArlibCommunity.Foundations.Convex.Polytope.body P.cv18Normal P.cv18Offset := by
  ext y
  simp only [PolytopeData.cv18Body, PolytopeData.arlibBody,
    ArlibCommunity.Foundations.Convex.Polytope.mem_body, Set.mem_preimage]
  constructor <;> intro h i
  · have hi := h i
    simp only [PolytopeData.cv18Normal, PolytopeData.cv18Offset,
      inner_add_right, real_inner_smul_right, real_inner_smul_left] at hi ⊢
    linarith
  · have hi := h i
    simp only [PolytopeData.cv18Normal, PolytopeData.cv18Offset,
      inner_add_right, real_inner_smul_right, real_inner_smul_left] at hi ⊢
    linarith

lemma PolytopeData.arlibBody_eq_scaledBody_zero {n : Nat} (P : PolytopeData n) :
    P.arlibBody = P.scaledBody 0 := by
  unfold PolytopeData.arlibBody PolytopeData.scaledBody
  congr 1
  funext i
  simp [PolytopeData.scaledOffset, decimalScale]

lemma PolytopeData.arlibBody_inball {n : Nat} (P : PolytopeData n) :
    closedBall (toEuclidean P.incenter) P.inradius ⊆ P.arlibBody := by
  rw [P.arlibBody_eq_scaledBody_zero]
  simpa [decimalScale] using P.scaledBody_inball 0

lemma PolytopeData.cv18Body_measurable {n : Nat} (P : PolytopeData n) :
    MeasurableSet P.cv18Body :=
  (ArlibCommunity.Foundations.Convex.Polytope.measurableSet_body P.arlibNormal P.presentation.offset).preimage
    (measurable_cv18Chart P.inradius (toEuclidean P.incenter))

lemma PolytopeData.cv18Body_closed {n : Nat} (P : PolytopeData n) :
    IsClosed P.cv18Body := by
  exact (ArlibCommunity.Foundations.Convex.Polytope.isClosed_body P.arlibNormal P.presentation.offset).preimage
    (by fun_prop)

lemma PolytopeData.cv18Body_convex {n : Nat} (P : PolytopeData n) :
    Convex Real P.cv18Body := by
  intro x hx y hy a b ha hb hab
  change P.inradius • x + toEuclidean P.incenter ∈
    ArlibCommunity.Foundations.Convex.Polytope.body P.arlibNormal P.presentation.offset at hx
  change P.inradius • y + toEuclidean P.incenter ∈
    ArlibCommunity.Foundations.Convex.Polytope.body P.arlibNormal P.presentation.offset at hy
  change P.inradius • (a • x + b • y) + toEuclidean P.incenter ∈
    ArlibCommunity.Foundations.Convex.Polytope.body P.arlibNormal P.presentation.offset
  have h := (ArlibCommunity.Foundations.Convex.Polytope.convex_body P.arlibNormal P.presentation.offset)
    hx hy ha hb hab
  have heq : P.inradius • (a • x + b • y) + toEuclidean P.incenter =
      a • (P.inradius • x + toEuclidean P.incenter) +
        b • (P.inradius • y + toEuclidean P.incenter) := by
    calc
      P.inradius • (a • x + b • y) + toEuclidean P.incenter =
          P.inradius • (a • x + b • y) +
            (a + b) • toEuclidean P.incenter := by rw [hab, one_smul]
      _ = a • (P.inradius • x + toEuclidean P.incenter) +
          b • (P.inradius • y + toEuclidean P.incenter) := by module
  rw [heq]
  exact h

/-- The certified component inball becomes the unit ball required by CV18. -/
lemma PolytopeData.unitBall_subset_cv18Body {n : Nat} (P : PolytopeData n) :
    ball (0 : EuclideanSpace Real (Fin n)) 1 ⊆ P.cv18Body := by
  have hpre := preimage_cv18Chart_ball P.inradius_pos
    (toEuclidean P.incenter) (0 : EuclideanSpace Real (Fin n)) P.inradius
  have hball : ball (toEuclidean P.incenter) P.inradius ⊆ P.arlibBody :=
    ball_subset_closedBall.trans P.arlibBody_inball
  rw [show P.inradius • (0 : EuclideanSpace Real (Fin n)) + toEuclidean P.incenter =
      toEuclidean P.incenter by simp,
    div_self P.inradius_pos.ne'] at hpre
  rw [← hpre]
  exact preimage_mono hball

/-- Closed-unit-ball form needed by arlib-community's `VolumeInput`. -/
lemma PolytopeData.closedUnitBall_subset_cv18Body {n : Nat} (P : PolytopeData n) :
    closedBall (0 : EuclideanSpace Real (Fin n)) 1 ⊆ P.cv18Body := by
  rw [← closure_ball (0 : EuclideanSpace Real (Fin n)) one_ne_zero]
  exact closure_minimal P.unitBall_subset_cv18Body P.cv18Body_closed

/-- Exact Jacobian for the CV18 normalization. -/
lemma PolytopeData.volume_cv18Body {n : Nat} (P : PolytopeData n) :
    volume P.cv18Body = ENNReal.ofReal ((P.inradius ^ n)⁻¹) * volume P.arlibBody := by
  exact volume_preimage_cv18Chart P.inradius_pos
    (toEuclidean P.incenter) P.arlibBody

/-- The same Jacobian identity with TTC's actual volume target on the right. -/
lemma PolytopeData.volume_cv18Body_eq_ttc {n : Nat} (P : PolytopeData n) :
    volume P.cv18Body = ENNReal.ofReal ((P.inradius ^ n)⁻¹) * volume P.carrier := by
  rw [P.volume_cv18Body, PolytopeData.arlibBody,
    P.volume_arlib_body_eq_carrier]

/-- Rescaling a normalized-body volume by the chart determinant recovers TTC's target. -/
lemma PolytopeData.inradiusPow_mul_volume_cv18Body {n : Nat} (P : PolytopeData n) :
    ENNReal.ofReal (P.inradius ^ n) * volume P.cv18Body = volume P.carrier := by
  rw [P.volume_cv18Body_eq_ttc, ← mul_assoc]
  have hpow : 0 < P.inradius ^ n := pow_pos P.inradius_pos n
  rw [← ENNReal.ofReal_mul hpow.le]
  have hinv : P.inradius ^ n * (P.inradius ^ n)⁻¹ = 1 :=
    mul_inv_cancel₀ hpow.ne'
  rw [hinv, ENNReal.ofReal_one, one_mul]

lemma PolytopeData.inradiusPow_mul_volume_cv18Body_toReal {n : Nat} (P : PolytopeData n) :
    P.inradius ^ n * (volume P.cv18Body).toReal = (volume P.carrier).toReal := by
  have h := congrArg ENNReal.toReal P.inradiusPow_mul_volume_cv18Body
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg P.inradius_pos.le n)] using h

lemma PolytopeData.arlibBody_bounded {n : Nat} (P : PolytopeData n) :
    Bornology.IsBounded P.arlibBody := by
  rw [P.arlibBody_eq_scaledBody_zero]
  exact P.scaledBody_bounded 0

/-- Corollary `cor:vol`'s ball: `P* = (P − z)/γ ⊆ B₂(0, R₀/γ)`. -/
lemma PolytopeData.cv18Body_subset_boundingBall {n : Nat} (P : PolytopeData n) :
    P.cv18Body ⊆ closedBall (0 : EuclideanSpace Real (Fin n))
      (P.BoundingRadius / P.inradius) := by
  intro x hx
  have hy : P.inradius • x + toEuclidean P.incenter ∈ P.arlibBody := hx
  unfold PolytopeData.arlibBody at hy
  rw [← P.image_toEuclidean_carrier] at hy
  obtain ⟨x', hx', hxeq⟩ := hy
  have hnorm := P.norm_sub_incenter_le_boundingRadius hx'
  have heq : toEuclidean (x' - P.incenter) = P.inradius • x := by
    have h1 : toEuclidean (x' - P.incenter) = toEuclidean x' - toEuclidean P.incenter := by
      simp [toEuclidean, WithLp.toLp_sub]
    rw [h1, hxeq]
    abel
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos P.inradius_pos] at hnorm
  rw [mem_closedBall, dist_zero_right, le_div_iff₀ P.inradius_pos]
  linarith

/-- The radius used by CV18 after translating by the incenter and scaling the inball to unit
radius: `max 1 (R₀/γ)`. The `max 1` records the unit ball already inside the body. -/
def PolytopeData.cv18OuterRadius {n : Nat} (P : PolytopeData n) : Real :=
  max 1 (P.BoundingRadius / P.inradius)

lemma PolytopeData.cv18OuterRadius_nonneg {n : Nat} (P : PolytopeData n) :
    0 <= P.cv18OuterRadius := by
  exact le_trans zero_le_one (le_max_left _ _)

lemma PolytopeData.one_le_cv18OuterRadius {n : Nat} (P : PolytopeData n)
    (_hn : 1 <= n) :
    1 <= P.cv18OuterRadius := by
  exact le_max_left _ _

lemma PolytopeData.cv18Body_subset_outerBall {n : Nat} (P : PolytopeData n) :
    P.cv18Body ⊆ closedBall (0 : EuclideanSpace Real (Fin n)) P.cv18OuterRadius :=
  P.cv18Body_subset_boundingBall.trans (Metric.closedBall_subset_closedBall (le_max_right _ _))

/-- The normalized body has a finite, explicit outer-radius certificate, as required by
the Gaussian-cooling schedule. -/
lemma PolytopeData.exists_cv18_outerRadius {n : Nat} (P : PolytopeData n) :
    ∃ R : Real, 0 ≤ R ∧ ∀ x ∈ P.cv18Body, ‖x‖ ≤ R := by
  refine ⟨P.cv18OuterRadius, P.cv18OuterRadius_nonneg, ?_⟩
  intro x hx
  have h := P.cv18Body_subset_outerBall hx
  simpa [mem_closedBall, dist_zero_right] using h

lemma PolytopeData.exists_cv18_subset_closedBall {n : Nat} (P : PolytopeData n) :
    ∃ R : Real, 0 ≤ R ∧
      P.cv18Body ⊆ closedBall (0 : EuclideanSpace Real (Fin n)) R := by
  exact ⟨P.cv18OuterRadius, P.cv18OuterRadius_nonneg,
    P.cv18Body_subset_outerBall⟩

lemma PolytopeData.exp_one_le_dim_mul_cv18OuterRadius_sq {n : Nat}
    (P : PolytopeData n) (hn : 3 <= n) :
    Real.exp 1 <= (n : Real) * P.cv18OuterRadius ^ 2 := by
  have hnR : (3 : Real) <= (n : Real) := by exact_mod_cast hn
  have hR2 : (1 : Real) <= P.cv18OuterRadius ^ 2 := by
    nlinarith [P.one_le_cv18OuterRadius (by omega : 1 <= n)]
  calc
    Real.exp 1 <= 3 := by linarith [Real.exp_one_lt_d9]
    _ = 3 * 1 := by ring
    _ <= (n : Real) * P.cv18OuterRadius ^ 2 :=
      mul_le_mul hnR hR2 (by norm_num) (by positivity)

lemma PolytopeData.cv18Body_bounded {n : Nat} (P : PolytopeData n) :
    Bornology.IsBounded P.cv18Body := by
  obtain ⟨R, -, hR⟩ := P.exists_cv18_subset_closedBall
  exact Metric.isBounded_closedBall.subset hR

lemma PolytopeData.volume_cv18Body_ne_top {n : Nat} (P : PolytopeData n) :
    volume P.cv18Body ≠ ⊤ :=
  P.cv18Body_bounded.measure_lt_top.ne

/-- A canonical positive diameter parameter for the normalized body. -/
def PolytopeData.cv18Diameter {n : Nat} (P : PolytopeData n) : Real :=
  max 1 (Metric.diam P.cv18Body)

lemma PolytopeData.cv18Diameter_pos {n : Nat} (P : PolytopeData n) :
    0 < P.cv18Diameter :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

lemma PolytopeData.one_le_cv18Diameter {n : Nat} (P : PolytopeData n) :
    1 ≤ P.cv18Diameter :=
  le_max_left _ _

lemma PolytopeData.diam_cv18Body_le {n : Nat} (P : PolytopeData n) :
    Metric.diam P.cv18Body ≤ P.cv18Diameter :=
  le_max_right _ _

/-- The auxiliary diameter used by the mixing theorem is controlled by the same explicit
preprocessing radius as the cooling schedule. -/
lemma PolytopeData.cv18Diameter_le_two_mul_outerRadius {n : Nat} (P : PolytopeData n) :
    P.cv18Diameter ≤ 2 * P.cv18OuterRadius := by
  have hdiam : Metric.diam P.cv18Body ≤ 2 * P.cv18OuterRadius :=
    (Metric.diam_mono P.cv18Body_subset_outerBall Metric.isBounded_closedBall).trans
      (Metric.diam_closedBall P.cv18OuterRadius_nonneg)
  unfold PolytopeData.cv18Diameter
  apply max_le
  · have hR : 1 ≤ P.cv18OuterRadius := by
      unfold PolytopeData.cv18OuterRadius
      exact le_max_left _ _
    linarith
  · exact hdiam

#print axioms PolytopeData.cv18Body_subset_outerBall
#print axioms PolytopeData.cv18Diameter_le_two_mul_outerRadius

end ttc
