import Kr25Ssmxt.Analysis.PrecisionRequirements
import Kr25Ssmxt.Analysis.L2LatticeBridge
import Kr25Ssmxt.Analysis.PrecisionAdequateSplit

/-!
# Integer-lattice comparison for scaled components

The single-component case of Lemma `lem:nonconv`, from the `ℓ₂` union lemma with one
component.
-/

namespace Kr25Ssmxt

/--
Every scaled component satisfying the global paper radius bound has volume within relative
error `η` of its number of standard integer-lattice points.

PAPER: sections/analysis.tex:117-133
-/
lemma integer_lattice_polytope_comparison
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
    ∀ i,
      (MeasureTheory.volume
        ((fun x : Point n => (10 : Real) ^ b • x) ''
          (D.component i).carrier)).toReal ∈
        Arlib.relErr η
          (((((fun x : Point n => (10 : Real) ^ b • x) ''
              (D.component i).carrier) ∩
            {x : Point n | ∀ j, ∃ z : Int, x j = (z : Real)}).ncard : Real)) := by
  classical
  intro i
  have hm : (1 : Real) ≤ D.componentCount := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Fin.pos i).ne'
  have hr1 : (1 : Real) ≤ D.totalFacets := by
    have h1 := D.facetCount_le_totalFacets i
    have h2 := (D.component i).facets_pos
    exact_mod_cast (by omega : 1 ≤ D.totalFacets)
  have h := scaled_family_lattice_comparison (m := 1) hn one_pos (fun _ => D.component i) b
    hηpos hηle hr1 (fun _ => by exact_mod_cast D.facetCount_le_totalFacets i) (fun _ => by
      refine le_trans ?_ (hradius i)
      unfold latticeRadiusRequirement
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      apply div_le_div_of_nonneg_right _ hηpos.le
      have hn0 : (0 : Real) ≤ n := Nat.cast_nonneg n
      push_cast
      nlinarith)
  rwa [Set.iUnion_const] at h

end Kr25Ssmxt
