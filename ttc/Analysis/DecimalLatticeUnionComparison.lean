import ttc.Analysis.DecimalLatticeScaling
import ttc.Analysis.IntegerLatticeUnionComparison

/-!
# Decimal-lattice comparison for a finite polytope union

This module isolates the geometric content of paper Lemma 7.  Its proof must combine the
integer-lattice estimate for a nonconvex finite union with scaling by `10 ^ b`.  In
particular, the components have separate incenters; no common-center dilation is assumed.
-/

namespace ttc

/--
If every component has the scaled inradius required by the paper's finite-union lattice
estimate, decimal-lattice counts approximate the volume of their union.

PAPER: main-arxiv.tex:1181-1187
-/
lemma decimal_lattice_union_comparison
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
    (MeasureTheory.volume D.union).toReal ∈
      Arlib.relErr η
        ((D.union ∩ decimalLattice b n).ncard /
          (10 : Real) ^ (b * n)) := by
  apply decimal_lattice_scaling hn D.union b η
  exact integer_lattice_union_comparison hn D b η hηpos hηle hradius

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · proved · transferred the scaled integer union estimate through decimal scaling
* r1 · reduced · isolated the finite-union geometric comparison with explicit radius bounds
-/

end ttc
