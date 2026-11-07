import Kr25Ssmxt.Analysis.GeometricOracleDischarge

/-! Adequate precision and a nonempty decomposition give at least one lattice
point in the union. This supplies the positive lattice count for the dyadic
stopping-level argument. -/

namespace Kr25Ssmxt

theorem manuscript_union_lattice_nonempty
    {n k : Nat} (hn : 0 < n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (hcomponents : 0 < D.componentCount) :
    (D.latticePoints b).Nonempty := by
  let i : Fin D.componentCount := ⟨0, hcomponents⟩
  obtain ⟨x, hx⟩ :=
    (coded_lattice_points_finite_nonempty hn D p b hprecision i).2
  refine ⟨x.toPoint, ?_⟩
  rcases hx with ⟨hprecisionX, hcarrier⟩
  constructor
  · exact Set.mem_iUnion.2 ⟨i, hcarrier⟩
  · intro j
    refine ⟨x.2 j, ?_⟩
    simp [LatticePoint.toPoint, hprecisionX]

theorem manuscript_component_lattice_finite
    {n : Nat} (P : PolytopeData n) (b : Nat)
    (hcode : (codedLatticePoints P b).Finite) :
    (P.carrier ∩ decimalLattice b n).Finite := by
  have himage : (fun x : LatticePoint n => x.toPoint) ''
      codedLatticePoints P b = P.carrier ∩ decimalLattice b n := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨hx.2, ?_⟩
      intro i
      exact ⟨x.2 i, by simp [LatticePoint.toPoint, hx.1]⟩
    · intro hy
      choose z hz using hy.2
      let x : LatticePoint n := (b, z)
      have hxpoint : x.toPoint = y := by
        funext i
        simpa [x, LatticePoint.toPoint] using (hz i).symm
      exact ⟨x, ⟨rfl, hxpoint.symm ▸ hy.1⟩, hxpoint⟩
  rw [← himage]
  exact hcode.image _

theorem manuscript_union_lattice_finite
    {n k : Nat} (hn : 0 < n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta) :
    (D.latticePoints b).Finite := by
  have hcomponent : ∀ i : Fin D.componentCount,
      ((D.component i).carrier ∩ decimalLattice b n).Finite := by
    intro i
    exact manuscript_component_lattice_finite (D.component i) b
      (coded_lattice_points_finite_nonempty hn D p b hprecision i).1
  change ((⋃ i : Fin D.componentCount, (D.component i).carrier) ∩
    decimalLattice b n).Finite
  rw [Set.iUnion_inter]
  exact Set.finite_iUnion hcomponent

theorem manuscript_union_lattice_ncard_pos
    {n k : Nat} (hn : 0 < n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (hcomponents : 0 < D.componentCount) :
    0 < (D.latticePoints b).ncard := by
  have hfinite := manuscript_union_lattice_finite hn D p b hprecision
  have hnonempty := manuscript_union_lattice_nonempty hn D p b hprecision hcomponents
  exact (Set.ncard_pos hfinite).mpr hnonempty

theorem manuscript_component_lattice_ncard_le_union
    {n k : Nat} (hn : 0 < n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (i : Fin D.componentCount) :
    ((D.component i).carrier ∩ decimalLattice b n).ncard ≤
      (D.latticePoints b).ncard := by
  apply Set.ncard_le_ncard _
    (manuscript_union_lattice_finite hn D p b hprecision)
  intro x hx
  exact ⟨Set.mem_iUnion.mpr ⟨i, hx.1⟩, hx.2⟩

end Kr25Ssmxt
