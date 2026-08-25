import Kr25Ssmxt.Model.Prelude

/-!
# Half-open cubulation at integer lattice points

This module defines the measurable cubulation used to compare a bounded set with its
standard integer-lattice points.  Half-open cubes make distinct lattice cells disjoint.
-/

namespace Kr25Ssmxt

/--
The union of the half-open unit cubes anchored at the integer lattice points of `S`.

INTERNAL: set-level device for turning an integer-lattice count into a Lebesgue volume
-/
def integerCubulation {n : Nat} (S : Set (Point n)) : Set (Point n) :=
  {x | ∃ z : Fin n → Int,
    (fun j => (z j : Real)) ∈ S ∧
      ∀ j, (z j : Real) ≤ x j ∧ x j < (z j : Real) + 1}

end Kr25Ssmxt
