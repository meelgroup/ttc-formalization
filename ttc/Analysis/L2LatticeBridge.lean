import ttc.Analysis.ScaledBody
import ttc.Analysis.L2LatticeUnion
import ttc.Analysis.ArlibPolytopeBridge

/-! # `lem:nonconv` for TTC components

Transfers `l2_union_lattice_comparison` from arlib's Euclidean bodies to TTC's
`PolytopeData`: for a finite family of components whose `10ᵇ`-scaled maximal
inscribed `ℓ₂` balls have radius at least `(64 m n / η) √(log (4 r / η))`, the
`10ᵇ`-scaled union has volume within relative error `η` of its number of integer
points. -/

namespace ttc

open MeasureTheory Set

/-- The integer points of a set of `Point n`, counted through `ℤⁿ`. -/
theorem integerPoints_eq_image {n : ℕ} (S : Set (Point n)) :
    S ∩ {x : Point n | ∀ j, ∃ z : Int, x j = (z : Real)} =
      (fun z : Fin n → ℤ => fun j => (z j : Real)) ''
        {z | intPoint z ∈ (fromEuclidean ⁻¹' S)} := by
  ext x
  constructor
  · rintro ⟨hx, hz⟩
    choose z hz using hz
    refine ⟨z, ?_, funext fun j => (hz j).symm⟩
    have : (fun j => (z j : Real)) = x := funext fun j => (hz j).symm
    change fromEuclidean (intPoint z) ∈ S
    simpa [fromEuclidean, intPoint, this] using hx
  · rintro ⟨z, hz, rfl⟩
    exact ⟨hz, fun j => ⟨z j, rfl⟩⟩

set_option maxHeartbeats 1000000 in
/-- **`lem:nonconv` for a finite family of TTC components.** -/
theorem scaled_family_lattice_comparison {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (P : Fin m → PolytopeData n) (b : ℕ) {η r : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hr1 : 1 ≤ r) (hf : ∀ i, ((P i).presentation.facetCount : ℝ) ≤ r)
    (hγ : ∀ i, (64 * m * n / η) * Real.sqrt (Real.log (4 * r / η)) ≤
      (10 : ℝ) ^ b * (P i).inradius) :
    (volume ((fun x : Point n => (10 : ℝ) ^ b • x) '' ⋃ i, (P i).carrier)).toReal ∈
      Arlib.relErr η
        (((((fun x : Point n => (10 : ℝ) ^ b • x) '' ⋃ i, (P i).carrier) ∩
          {x : Point n | ∀ j, ∃ z : Int, x j = (z : Real)}).ncard : ℝ)) := by
  classical
  set S := (fun x : Point n => (10 : ℝ) ^ b • x) '' ⋃ i, (P i).carrier with hSdef
  set γ := (64 * m * n / η) * Real.sqrt (Real.log (4 * r / η)) with hγdef
  have hmain := l2_union_lattice_comparison (f := fun i => (P i).presentation.facetCount)
    (fun i => (P i).arlibNormal) (fun i => (P i).scaledOffset b) hm hn hη0 hη1 hr1 hf
    le_rfl (fun i => decimalScale b • toEuclidean (P i).incenter)
    (fun i => by
      refine Metric.ball_subset_closedBall.trans
        ((Metric.closedBall_subset_closedBall ?_).trans ((P i).scaledBody_inball b))
      simpa [decimalScale] using hγ i)
    (fun i => (P i).scaledBody_bounded b)
  -- the Euclidean union is the image of `S`
  have hQ : (⋃ i, ArlibCommunity.Foundations.Convex.Polytope.body ((fun i => (P i).arlibNormal) i)
      ((fun i => (P i).scaledOffset b) i)) = fromEuclidean ⁻¹' S := by
    ext y
    simp only [mem_iUnion, mem_preimage, hSdef, mem_image]
    constructor
    · rintro ⟨i, hi⟩
      change y ∈ (P i).scaledBody b at hi
      rw [← (P i).image_decimalScale_eq_scaledBody b] at hi
      obtain ⟨x, hx, rfl⟩ := hi
      refine ⟨x, ⟨i, hx⟩, ?_⟩
      ext j; simp [fromEuclidean, toEuclidean, decimalScale]
    · rintro ⟨x, ⟨i, hx⟩, hxy⟩
      refine ⟨i, ?_⟩
      change y ∈ (P i).scaledBody b
      rw [← (P i).image_decimalScale_eq_scaledBody b]
      refine ⟨x, hx, ?_⟩
      ext j
      have := congrFun hxy j
      simp [fromEuclidean, toEuclidean, decimalScale] at this ⊢
      exact this
  rw [hQ] at hmain
  -- volumes agree through the volume-preserving coordinate identity
  have hvol : volume (fromEuclidean ⁻¹' S) = volume S := by
    have hmp := (PiLp.volume_preserving_toLp (Fin n))
    have hpre : (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) ⁻¹'
        (fromEuclidean ⁻¹' S) = S := by
      ext x; simp [fromEuclidean]
    have hSm : NullMeasurableSet (fromEuclidean ⁻¹' S) volume := by
      rw [← hQ]
      exact (MeasurableSet.iUnion fun i =>
        ArlibCommunity.Foundations.Convex.Polytope.measurableSet_body _ _).nullMeasurableSet
    rw [← hmp.measure_preimage hSm, hpre]
  have hcount : ((S ∩ {x : Point n | ∀ j, ∃ z : Int, x j = (z : Real)}).ncard : ℝ) =
      ({z : Fin n → ℤ | intPoint z ∈ fromEuclidean ⁻¹' S}.ncard : ℝ) := by
    rw [integerPoints_eq_image, Set.ncard_image_of_injective]
    intro z w h
    funext j
    have := congrFun h j
    simp only at this
    exact_mod_cast this
  rw [measureReal_def, hvol] at hmain
  rw [hcount]
  exact ⟨hmain.1, hmain.2⟩

end ttc
