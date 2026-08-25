import Kr25Ssmxt.Analysis.IntegerCubulation

/-!
# Volume of integer cubulation

For a bounded set, only finitely many integer anchors occur.  The corresponding
half-open unit cubes are pairwise disjoint and each has Lebesgue volume one.
-/

namespace Kr25Ssmxt

open scoped ENNReal

/--
The integer cubulation of a bounded set is null-measurable, has finite volume, and its
volume is the number of integer lattice points of the set.

INTERNAL: cubulation volume/count identity used in the finite-union lattice comparison
-/
lemma integer_cubulation_volume
    {n : Nat} (hn : 0 < n) (S : Set (Point n))
    (hbounded : Bornology.IsBounded S) :
    MeasureTheory.NullMeasurableSet (integerCubulation S) MeasureTheory.volume ∧
      MeasureTheory.volume (integerCubulation S) ≠ ∞ ∧
      (MeasureTheory.volume (integerCubulation S)).toReal =
        (((S ∩ {x : Point n | ∀ i, ∃ z : Int, x i = (z : Real)}).ncard : Real)) := by
  let L : Set (Point n) := {x | ∀ i, ∃ z : Int, x i = (z : Real)}
  let T : Set (Point n) := S ∩ L
  let C : Point n → Set (Point n) :=
    fun p => Set.univ.pi (fun i => Set.Ico (p i) (p i + 1))

  have hT : T.Finite := by
    let castPi : (Fin n → Int) → Point n :=
      Pi.map (fun _ : Fin n => ((↑) : Int → Real))
    have hcastClosed : Topology.IsClosedEmbedding castPi := by
      exact Topology.IsClosedEmbedding.piMap
        (fun _ : Fin n => Int.isClosedEmbedding_coe_real)
    have hrange : Set.range castPi = L := by
      ext x
      constructor
      · rintro ⟨z, rfl⟩ i
        exact ⟨z i, rfl⟩
      · intro hx
        choose z hz using hx
        refine ⟨z, ?_⟩
        funext i
        exact (hz i).symm
    have hLclosed : IsClosed L := by
      rw [← hrange]
      exact hcastClosed.isClosed_range
    have hLdiscrete : IsDiscrete L := by
      rw [← hrange]
      exact hcastClosed.isInducing.isDiscrete_range
    exact Metric.finite_isBounded_inter_isClosed hLdiscrete hbounded hLclosed

  have hC : ∀ p, MeasurableSet (C p) ∧ MeasureTheory.volume (C p) = 1 := by
    intro p
    constructor
    · exact MeasurableSet.univ_pi fun _ => measurableSet_Ico
    · rw [Real.volume_pi_Ico]
      simp

  have hdisjoint : L.PairwiseDisjoint C := by
    intro p hp q hq hpq
    dsimp only [Function.onFun, C]
    rw [Set.disjoint_left]
    intro x hxp hxq
    have hcoord : ∃ i, p i ≠ q i := by
      by_contra h
      push Not at h
      exact hpq (funext h)
    obtain ⟨i, hi⟩ := hcoord
    obtain ⟨z, hz⟩ := hp i
    obtain ⟨w, hw⟩ := hq i
    have hzw : z ≠ w := by
      intro h
      apply hi
      rw [hz, hw, h]
    have hxp_i := hxp i (Set.mem_univ i)
    have hxq_i := hxq i (Set.mem_univ i)
    change p i ≤ x i ∧ x i < p i + 1 at hxp_i
    change q i ≤ x i ∧ x i < q i + 1 at hxq_i
    rcases lt_or_gt_of_ne hzw with hlt | hgt
    · have hgap : (z : Real) + 1 ≤ (w : Real) := by
        exact_mod_cast (Int.add_one_le_iff.mpr hlt)
      rw [hz] at hxp_i
      rw [hw] at hxq_i
      linarith [hxp_i.2, hxq_i.1]
    · have hgap : (w : Real) + 1 ≤ (z : Real) := by
        exact_mod_cast (Int.add_one_le_iff.mpr hgt)
      rw [hz] at hxp_i
      rw [hw] at hxq_i
      linarith [hxq_i.2, hxp_i.1]

  have hunion : integerCubulation S = ⋃ p ∈ T, C p := by
    ext x
    constructor
    · rintro ⟨z, hzS, hbounds⟩
      let p : Point n := fun i => (z i : Real)
      have hpL : ∀ i, ∃ w : Int, p i = (w : Real) := fun i => ⟨z i, rfl⟩
      refine Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨⟨hzS, hpL⟩, ?_⟩⟩
      intro i hi
      exact hbounds i
    · intro hx
      obtain ⟨p, hpT, hxp⟩ := Set.mem_iUnion₂.1 hx
      rcases hpT with ⟨hpS, hpL⟩
      choose z hz using hpL
      refine ⟨z, ?_, ?_⟩
      · have hpcast : (fun j => (z j : Real)) = p := by
          funext j
          exact (hz j).symm
        rw [hpcast]
        exact hpS
      · intro j
        have hcoord := hxp j (Set.mem_univ j)
        change p j ≤ x j ∧ x j < p j + 1 at hcoord
        simpa [hz j] using hcoord

  have hTdisjoint : T.PairwiseDisjoint C :=
    Set.Pairwise.mono Set.inter_subset_right hdisjoint
  have hmeas : MeasurableSet (integerCubulation S) := by
    rw [hunion]
    exact hT.measurableSet_biUnion fun p _ => (hC p).1
  have hvolume : MeasureTheory.volume (integerCubulation S) = (T.ncard : ENNReal) := by
    rw [hunion]
    have hindex : (⋃ p ∈ T, C p) = ⋃ p ∈ hT.toFinset, C p := by
      simp only [hT.mem_toFinset]
    rw [hindex]
    rw [MeasureTheory.measure_biUnion_finset]
    · simp only [(hC _).2, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [Set.ncard_eq_toFinset_card T hT]
    · simpa only [hT.coe_toFinset] using hTdisjoint
    · intro p hp
      exact (hC p).1
  refine ⟨hmeas.nullMeasurableSet, ?_, ?_⟩
  · rw [hvolume]
    exact ENNReal.natCast_ne_top T.ncard
  · rw [hvolume, ENNReal.toReal_natCast]

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · finite disjoint union of measurable half-open unit cubes
-/

end Kr25Ssmxt
