import ttc.Model.Prelude

/-!
# Final decomposition lattice points

The model's final lattice-point set is definitionally the intersection of the component
union with the decimal lattice.
-/

namespace ttc

/--
The lattice points retained after all components are precisely the decimal-lattice points
in the decomposition union.

INTERNAL: Exposes `Decomposition.latticePoints` in the set-theoretic form used by geometry.
-/
lemma decomposition_latticePoints_eq
    {n k : Nat} {F : LRAFormula n k} (D : Decomposition F) (b : Nat) :
    D.latticePoints b = D.union ∩ decimalLattice b n := by
  rfl

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · the equality is definitional in the current model
-/

end ttc
