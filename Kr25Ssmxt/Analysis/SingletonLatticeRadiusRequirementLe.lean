import Kr25Ssmxt.Analysis.SingletonDecomposition

/-!
# Radius comparison for a singleton decomposition

The paper's global radius requirement for a finite decomposition dominates the same
requirement for any one of its components viewed as a singleton decomposition.
-/

namespace Kr25Ssmxt

/--
Passing from a nonempty decomposition to the singleton decomposition at `i` can only
decrease the lattice radius requirement.

INTERNAL: transfers the global radius hypothesis to the singleton union theorem.
-/
lemma singleton_latticeRadiusRequirement_le
    {n k : Nat}
    {F : LRAFormula n k}
    (D : Decomposition F)
    (i : Fin D.componentCount)
    (η : Real)
    (hηpos : 0 < η)
    (_hηle : η ≤ 1) :
    latticeRadiusRequirement (singletonDecomposition (D.component i)) η ≤
      latticeRadiusRequirement D η := by
  have htotal :
      (singletonDecomposition (D.component i)).totalFacets =
        (D.component i).presentation.facetCount := by
    unfold Decomposition.totalFacets
    change (∑ _ : Fin 1, (D.component i).presentation.facetCount) =
      (D.component i).presentation.facetCount
    exact Fin.sum_univ_one
      (fun _ : Fin 1 => (D.component i).presentation.facetCount)
  have hcountNat : 1 ≤ D.componentCount := by
    exact Nat.one_le_iff_ne_zero.mpr (by
      intro hzero
      exact Fin.elim0 (hzero ▸ i))
  have hcount : (1 : Real) ≤ D.componentCount := by
    exact_mod_cast hcountNat
  have hfacetsNat :
      (D.component i).presentation.facetCount ≤ D.totalFacets := by
    rw [Decomposition.totalFacets]
    exact Finset.single_le_sum
      (fun j _ => Nat.zero_le (D.component j).presentation.facetCount)
      (Finset.mem_univ i)
  have hfacets :
      ((D.component i).presentation.facetCount : Real) ≤ D.totalFacets := by
    exact_mod_cast hfacetsNat
  have hfacetpos :
      (0 : Real) < (D.component i).presentation.facetCount := by
    exact_mod_cast (D.component i).facets_pos
  rw [latticeRadiusRequirement, latticeRadiusRequirement, htotal]
  simp only [singletonDecomposition]
  gcongr

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r3 · proved · bounded singleton count and facet factors by their global counterparts
-/

end Kr25Ssmxt
