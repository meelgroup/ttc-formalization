import Kr25Ssmxt.Model.Run

/-! Basic facts about a component's maximal inscribed `ℓ₂` ball. -/

namespace Kr25Ssmxt

open MeasureTheory

/-- The `ℓ₂` ball of `Point n` is the preimage of the Euclidean closed ball. -/
theorem euclideanBall_eq_preimage {n : Nat} (c : Point n) (r : Real) :
    euclideanBall c r = toEuclidean ⁻¹' Metric.closedBall (toEuclidean c) r := by
  ext x
  simp [euclideanBall, Metric.mem_closedBall, dist_eq_norm, toEuclidean, WithLp.toLp_sub]

/-- The centre of the inscribed ball lies in the component. -/
theorem PolytopeData.incenter_mem_carrier {n : Nat} (P : PolytopeData n) :
    P.incenter ∈ P.carrier :=
  P.inball (by simp [euclideanBall, P.inradius_pos.le])

/-- The inscribed `ℓ₂` ball has positive volume. -/
theorem PolytopeData.volume_euclideanBall_pos {n : Nat} (P : PolytopeData n) :
    0 < volume (euclideanBall P.incenter P.inradius) := by
  rw [euclideanBall_eq_preimage]
  have h := (PiLp.volume_preserving_toLp (Fin n)).measure_preimage
    (s := Metric.closedBall (toEuclidean P.incenter) P.inradius)
    measurableSet_closedBall.nullMeasurableSet
  change 0 < volume ((WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) ⁻¹'
    Metric.closedBall (toEuclidean P.incenter) P.inradius)
  rw [h]
  exact Metric.measure_closedBall_pos volume _ P.inradius_pos

/-- A component has positive volume. -/
theorem PolytopeData.volume_carrier_pos {n : Nat} (P : PolytopeData n) :
    0 < volume P.carrier :=
  P.volume_euclideanBall_pos.trans_le (measure_mono P.inball)

end Kr25Ssmxt
