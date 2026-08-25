import Kr25Ssmxt.Analysis.DecimalLatticeUnionComparison
import Kr25Ssmxt.Analysis.SingletonLatticeRadiusRequirementLe

/-!
# Decimal-lattice comparison for decomposition components

This module derives the componentwise decimal-lattice estimate from the finite-union
comparison by viewing each component as a singleton decomposition.
-/

namespace Kr25Ssmxt

/--
The global precision radius is sufficient for the decimal-lattice comparison of every
individual component.

PAPER: main-arxiv.tex:1181-1187
-/
lemma decimal_lattice_component_comparison
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
      (MeasureTheory.volume (D.component i).carrier).toReal ∈
        Arlib.relErr η
          (((D.component i).carrier ∩ decimalLattice b n).ncard /
            (10 : Real) ^ (b * n)) := by
  intro i
  let Di := singletonDecomposition (D.component i)
  have hradius_i : ∀ j,
      latticeRadiusRequirement Di η ≤
        (10 : Real) ^ b * (Di.component j).inradius := by
    intro j
    calc
      latticeRadiusRequirement Di η ≤ latticeRadiusRequirement D η := by
        exact singleton_latticeRadiusRequirement_le D i η hηpos hηle
      _ ≤ (10 : Real) ^ b * (D.component i).inradius := hradius i
      _ = (10 : Real) ^ b * (Di.component j).inradius := by
        rfl
  have hcomparison :=
    decimal_lattice_union_comparison hn Di b η hηpos hηle hradius_i
  simpa [Di, singletonDecomposition_union] using hcomparison

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r3 · proved · derived the component estimate from the union theorem via a singleton decomposition
* r2 · proved · transferred the scaled integer component estimate through decimal scaling
* r1 · reduced · isolated componentwise decimal scaling from the nonconvex union estimate
-/

end Kr25Ssmxt
