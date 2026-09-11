import Kr25Ssmxt.Analysis.ScaledPolytopeInball
import Kr25Ssmxt.Model.Run
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.Polytope

/-!
# The TTC/Arlib polytope representation bridge

`PolytopeData` stores normals as ordinary coordinate functions.  Arlib's convex-body and
random-walk developments use the definitionally equivalent `EuclideanSpace` presentation.
This file packages the conversion, proves that it preserves the carrier, and records the
positive decimal dilation used before randomized rounding to the integer lattice.
-/

noncomputable section

open scoped InnerProductSpace

namespace Kr25Ssmxt

/-- The inverse coordinate identity, used only in bridge proofs. -/
def fromEuclidean {n : Nat} (x : EuclideanSpace Real (Fin n)) : Point n :=
  WithLp.ofLp x

@[simp] lemma toEuclidean_apply {n : Nat} (x : Point n) (i : Fin n) :
    toEuclidean x i = x i := rfl

@[simp] lemma fromEuclidean_apply {n : Nat} (x : EuclideanSpace Real (Fin n)) (i : Fin n) :
    fromEuclidean x i = x i := rfl

@[simp] lemma toEuclidean_fromEuclidean {n : Nat} (x : EuclideanSpace Real (Fin n)) :
    toEuclidean (fromEuclidean x) = x := rfl

@[simp] lemma fromEuclidean_toEuclidean {n : Nat} (x : Point n) :
    fromEuclidean (toEuclidean x) = x := rfl

/-- TTC's halfspace carrier is exactly Arlib's polytope body. -/
theorem PolytopeData.image_toEuclidean_carrier {n : Nat} (P : PolytopeData n) :
    toEuclidean '' P.carrier =
      Arlib.Polytope.body P.arlibNormal P.presentation.offset := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    intro i
    change dotProduct x (P.presentation.normal i) ≤ P.presentation.offset i
    simpa [dotProduct_comm] using hx i
  · intro hy
    refine ⟨fromEuclidean y, ?_, by simp⟩
    intro i
    have hi := hy i
    change dotProduct (fromEuclidean y) (P.presentation.normal i) ≤
      P.presentation.offset i at hi
    simpa [dotProduct_comm] using hi

/-- The coordinate identification used by Arlib preserves the component's Lebesgue volume. -/
theorem PolytopeData.volume_arlib_body_eq_carrier {n : Nat} (P : PolytopeData n) :
    MeasureTheory.volume (Arlib.Polytope.body P.arlibNormal P.presentation.offset) =
      MeasureTheory.volume P.carrier := by
  have hpre :
      (toEuclidean : Point n → EuclideanSpace Real (Fin n)) ⁻¹'
          Arlib.Polytope.body P.arlibNormal P.presentation.offset = P.carrier := by
    ext x
    constructor
    · intro hx
      rw [← P.image_toEuclidean_carrier] at hx
      rcases hx with ⟨y, hy, hxy⟩
      have : y = x := by
        apply congrArg fromEuclidean at hxy
        simpa using hxy
      simpa [this] using hy
    · intro hx
      rw [← P.image_toEuclidean_carrier]
      exact ⟨x, hx, rfl⟩
  rw [← (PiLp.volume_preserving_toLp (Fin n)).measure_preimage
    (Arlib.Polytope.measurableSet_body P.arlibNormal P.presentation.offset).nullMeasurableSet]
  change MeasureTheory.volume
      ((toEuclidean : Point n → EuclideanSpace Real (Fin n)) ⁻¹'
        Arlib.Polytope.body P.arlibNormal P.presentation.offset) =
    MeasureTheory.volume P.carrier
  rw [hpre]

lemma decimalScale_pos (b : Nat) : 0 < decimalScale b := by
  unfold decimalScale
  positivity

lemma decimalScale_ne_zero (b : Nat) : decimalScale b ≠ 0 :=
  (decimalScale_pos b).ne'

/-- Scaling the carrier by `10^b` gives exactly `scaledBody`. -/
theorem PolytopeData.image_decimalScale_eq_scaledBody {n : Nat} (P : PolytopeData n)
    (b : Nat) :
    (fun x : Point n => decimalScale b • toEuclidean x) '' P.carrier = P.scaledBody b := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    intro i
    change ⟪P.arlibNormal i, decimalScale b • toEuclidean x⟫_Real ≤
      P.scaledOffset b i
    rw [inner_smul_right]
    change decimalScale b * dotProduct x (P.presentation.normal i) ≤
      decimalScale b * P.presentation.offset i
    simpa [dotProduct_comm] using
      mul_le_mul_of_nonneg_left (hx i) (decimalScale_pos b).le
  · intro hy
    let x : Point n := fun i => (decimalScale b)⁻¹ * y i
    have hxy : decimalScale b • toEuclidean x = y := by
      ext i
      simp [x, toEuclidean, decimalScale_ne_zero]
    refine ⟨x, ?_, hxy⟩
    · intro i
      have hi := hy i
      change ⟪toEuclidean (P.presentation.normal i), y⟫_Real ≤
        decimalScale b * P.presentation.offset i at hi
      rw [← hxy] at hi
      change dotProduct (P.presentation.normal i) x ≤ P.presentation.offset i
      have hi' : decimalScale b * dotProduct x (P.presentation.normal i) ≤
          decimalScale b * P.presentation.offset i := by
        rw [inner_smul_right] at hi
        change decimalScale b * dotProduct x (P.presentation.normal i) ≤
          decimalScale b * P.presentation.offset i at hi
        exact hi
      exact (mul_le_mul_iff_of_pos_left (decimalScale_pos b)).mp <|
        by simpa [dotProduct_comm] using hi'

/-- The scaled body contains the correspondingly scaled certified inball. -/
theorem PolytopeData.scaledBody_inball {n : Nat} (P : PolytopeData n) (b : Nat) :
    Metric.closedBall (decimalScale b • toEuclidean P.incenter)
        (decimalScale b * P.inradius) ⊆ P.scaledBody b := by
  intro y hy
  rw [← P.image_decimalScale_eq_scaledBody b]
  let x : Point n := fromEuclidean ((decimalScale b)⁻¹ • y)
  refine ⟨x, P.inball ?_, ?_⟩
  · rw [Metric.mem_closedBall] at hy ⊢
    rw [dist_eq_norm] at hy ⊢
    have hspos := decimalScale_pos b
    have hnorm : ‖(decimalScale b)⁻¹ •
        (y - decimalScale b • toEuclidean P.incenter)‖ ≤ P.inradius := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hspos)]
      calc
        (decimalScale b)⁻¹ * ‖y - decimalScale b • toEuclidean P.incenter‖
            ≤ (decimalScale b)⁻¹ * (decimalScale b * P.inradius) :=
          mul_le_mul_of_nonneg_left hy (inv_pos.mpr hspos).le
        _ = P.inradius := by field_simp
    apply (pi_norm_le_iff_of_nonneg P.inradius_pos.le).2
    intro i
    have hi := PiLp.norm_apply_le
      ((decimalScale b)⁻¹ • (y - decimalScale b • toEuclidean P.incenter)) i
    calc
      ‖(x - P.incenter) i‖ =
          ‖((decimalScale b)⁻¹ •
            (y - decimalScale b • toEuclidean P.incenter)) i‖ := by
              congr 1
              simp [x, fromEuclidean, sub_apply, smul_eq_mul, mul_sub,
                decimalScale_ne_zero]
      _ ≤ ‖(decimalScale b)⁻¹ •
          (y - decimalScale b • toEuclidean P.incenter)‖ := hi
      _ ≤ P.inradius := hnorm
  · ext i
    simp [x, toEuclidean, fromEuclidean, smul_eq_mul, decimalScale_ne_zero]

/-- The scaled body is bounded. -/
theorem PolytopeData.scaledBody_bounded {n : Nat} (P : PolytopeData n) (b : Nat) :
    Bornology.IsBounded (P.scaledBody b) := by
  rw [← P.image_decimalScale_eq_scaledBody b]
  let e : (Fin n → Real) ≃L[Real] EuclideanSpace Real (Fin n) :=
    (PiLp.continuousLinearEquiv 2 Real (fun _ : Fin n => Real)).symm
  let f : (Fin n → Real) →L[Real] EuclideanSpace Real (Fin n) :=
    decimalScale b • e.toContinuousLinearMap
  have himage : Bornology.IsBounded (f '' P.carrier) := P.bounded.image f
  simpa [f, e, toEuclidean] using himage

end Kr25Ssmxt
