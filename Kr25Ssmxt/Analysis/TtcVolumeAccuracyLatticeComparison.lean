import Kr25Ssmxt.Analysis.PrecisionRequirements
import Kr25Ssmxt.Analysis.PrecisionAdequateSplit
import Kr25Ssmxt.Analysis.ReferenceProgram
import Kr25Ssmxt.Analysis.DecimalLatticeComponentComparison
import Kr25Ssmxt.Analysis.DecimalLatticeUnionComparison
import Kr25Ssmxt.Analysis.DecompositionLatticePointsEq

namespace Kr25Ssmxt

/-- An adequate decimal precision compares lattice counts with both every component volume
and the volume of their union.  The component bounds feed the sampling invariant, while the
union bound is the deterministic final conversion to geometric volume.

PAPER: main-arxiv.tex:1181-1187
-/
lemma ttc_volume_accuracy_lattice_comparison
    {n k : Nat}
    (hn : 0 < n)
    {F : LRAFormula n k}
    (D : Decomposition F)
    (params : ApproxParams)
    (b : Nat)
    (hprecision : PrecisionAdequate D b params.precisionEta) :
    (forall i,
      (MeasureTheory.volume (D.component i).carrier).toReal ∈
        Arlib.relErr params.latticeEta
          (((D.component i).carrier ∩ decimalLattice b n).ncard /
            (10 : Real) ^ (b * n))) ∧
      (MeasureTheory.volume D.union).toReal ∈
        Arlib.relErr params.latticeEta
          ((D.latticePoints b).ncard / (10 : Real) ^ (b * n)) := by
  have hηpos : 0 < params.latticeEta := by
    simpa only [ApproxParams.latticeEta] using
      div_pos params.epsilon_pos (by norm_num : (0 : Real) < 8)
  have hηle : params.latticeEta ≤ 1 := by
    simp only [ApproxParams.latticeEta]
    linarith [params.epsilon_le_one]
  have hradius : ∀ i,
      latticeRadiusRequirement D params.latticeEta ≤
        (10 : Real) ^ b * (D.component i).inradius := by
    intro i
    exact le_trans (le_max_left _ _) (hprecision.split i)
  constructor
  · exact decimal_lattice_component_comparison hn D b params.latticeEta
      hηpos hηle hradius
  · rw [decomposition_latticePoints_eq]
    exact decimal_lattice_union_comparison hn D b params.latticeEta
      hηpos hηle hradius

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · reduced · split scaling, integer component geometry, and integer union geometry
* r1 · reduced · headline closed via the explicit finite-union decimal-lattice comparison
-/

end Kr25Ssmxt
