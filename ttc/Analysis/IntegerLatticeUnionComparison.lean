import ttc.Analysis.PrecisionRequirements
import ttc.Analysis.L2LatticeBridge
import ttc.Analysis.PrecisionAdequateSplit

/-!
# Integer-lattice comparison for a finite polytope union

The paper's Lemma `lem:nonconv`: components may overlap and may have different incenters.
The proof is `scaled_family_lattice_comparison`, the `ℓ₂` argument of
`Analysis/L2LatticeUnion.lean`.
-/

namespace ttc

/--
The scaled finite union satisfying the paper radius bound has volume within relative error
`η` of its number of standard integer-lattice points.

PAPER: sections/analysis.tex:124-246
-/
lemma integer_lattice_union_comparison
    {n k : Nat}
    (hn : 0 < n)
    {F : LRAFormula n k}
    (D : Decomposition F)
    (b : Nat)
    (η : Real)
    (hηpos : 0 < η)
    (hηle : η ≤ 1)
    (hradius : ∀ i,
      latticeRadiusRequirement D η ≤
        (10 : Real) ^ b * (D.component i).inradius) :
    (MeasureTheory.volume
      ((fun x : Point n => (10 : Real) ^ b • x) '' D.union)).toReal ∈
      Arlib.relErr η
        (((((fun x : Point n => (10 : Real) ^ b • x) '' D.union) ∩
          {x : Point n | ∀ i, ∃ z : Int, x i = (z : Real)}).ncard : Real)) := by
  classical
  by_cases hmzero : D.componentCount = 0
  · have hunion : D.union = ∅ := by
      rw [Decomposition.union]
      apply Set.iUnion_eq_empty.2
      intro i
      exact (Nat.not_lt_zero i (hmzero ▸ i.isLt)).elim
    simp [hunion, Arlib.relErr]
  · have hm : 0 < D.componentCount := Nat.pos_of_ne_zero hmzero
    have hr1 : (1 : Real) ≤ D.totalFacets := by
      have h1 := D.facetCount_le_totalFacets ⟨0, hm⟩
      have h2 := (D.component ⟨0, hm⟩).facets_pos
      exact_mod_cast (by omega : 1 ≤ D.totalFacets)
    exact scaled_family_lattice_comparison hn hm D.component b hηpos hηle hr1
      (fun i => by exact_mod_cast D.facetCount_le_totalFacets i) hradius

end ttc
