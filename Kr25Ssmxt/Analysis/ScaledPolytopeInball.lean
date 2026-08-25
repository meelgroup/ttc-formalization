import Kr25Ssmxt.Model.Prelude
import Mathlib.Topology.Instances.Matrix

/-!
# Geometry of a scaled polytope

Positive scalar dilation preserves the convexity, boundedness, and measurability of a
halfspace polytope and sends its certified inball to the correspondingly scaled inball.
-/

namespace Kr25Ssmxt

/--
A positive dilation of a certified polytope has the expected scaled inball and regularity.

INTERNAL: scaling bookkeeping for the component cubulation estimate
-/
lemma scaled_polytope_inball {n : Nat} (P : PolytopeData n) (s : Real) (hs : 0 < s) :
    let A := (fun x : Point n => s • x) '' P.carrier
    Convex Real A ∧
      Bornology.IsBounded A ∧
      MeasureTheory.NullMeasurableSet A MeasureTheory.volume ∧
      Metric.closedBall (s • P.incenter) (s * P.inradius) ⊆ A := by
  dsimp only
  have hcarrierConvex : Convex Real P.carrier := by
    intro x hx y hy a b ha hb hab i
    simp only [HalfspacePresentation.carrier, Set.mem_setOf_eq] at hx hy ⊢
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
    calc
      a * dotProduct (P.presentation.normal i) x +
          b * dotProduct (P.presentation.normal i) y ≤
          a * P.presentation.offset i + b * P.presentation.offset i :=
        add_le_add (mul_le_mul_of_nonneg_left (hx i) ha)
          (mul_le_mul_of_nonneg_left (hy i) hb)
      _ = P.presentation.offset i := by rw [← add_mul, hab, one_mul]
  have hcarrierClosed : IsClosed P.carrier := by
    have hcarrier :
        P.carrier = ⋂ i, {x : Point n |
          dotProduct (P.presentation.normal i) x ≤ P.presentation.offset i} := by
      ext x
      simp [HalfspacePresentation.carrier]
    rw [hcarrier]
    apply isClosed_iInter
    intro i
    exact isClosed_le
      (show Continuous (fun x : Point n => dotProduct (P.presentation.normal i) x) from
        continuous_const.dotProduct
          (show Continuous (fun x : Point n => x) from continuous_id))
      continuous_const
  have hcarrierCompact : IsCompact P.carrier :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨hcarrierClosed, P.bounded⟩
  have hscaledCompact : IsCompact ((fun x : Point n => s • x) '' P.carrier) :=
    hcarrierCompact.image (continuous_const_smul s)
  refine ⟨?_, hscaledCompact.isBounded, hscaledCompact.nullMeasurableSet, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
    refine ⟨a • x + b • y, hcarrierConvex hx hy ha hb hab, ?_⟩
    simp only [smul_add, smul_smul]
    congr 1 <;> rw [mul_comm s]
  · intro y hy
    refine ⟨s⁻¹ • y, P.inball ?_, ?_⟩
    · rw [Metric.mem_closedBall] at hy ⊢
      have hc : s⁻¹ • (s • P.incenter) = P.incenter := by
        simp [smul_smul, hs.ne']
      calc
        dist (s⁻¹ • y) P.incenter =
            dist (s⁻¹ • y) (s⁻¹ • (s • P.incenter)) := by rw [hc]
        _ = ‖s⁻¹‖ * dist y (s • P.incenter) := by
          rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul]
        _ = s⁻¹ * dist y (s • P.incenter) := by
          rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
        _ ≤ s⁻¹ * (s * P.inradius) :=
          mul_le_mul_of_nonneg_left hy (le_of_lt (inv_pos.mpr hs))
        _ = P.inradius := by
          rw [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
    · simp [smul_smul, hs.ne']

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r3 · proved · derived scaled regularity from compactness and mapped the certified inball
* r2 · reduced · isolated positive-dilation regularity and the centered scaled inball
-/

end Kr25Ssmxt
