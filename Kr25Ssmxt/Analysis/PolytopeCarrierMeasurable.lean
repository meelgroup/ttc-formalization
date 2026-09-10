import Kr25Ssmxt.Model.Prelude

/-!
# Measurability of normalized-polytope carriers

Every normalized component is presented by finitely many closed affine halfspaces, hence its
carrier is Borel measurable.  The boundedness and inball fields are irrelevant here.
-/

namespace Kr25Ssmxt

open MeasureTheory

/--
The carrier of every normalized polytope is measurable.

INTERNAL: measurable source events for removal and future-component membership profiles.
-/
lemma polytope_carrier_measurable {n : Nat} (P : PolytopeData n) :
    MeasurableSet P.carrier := by
  rw [show P.carrier =
      ⋂ i, {x | dotProduct (P.presentation.normal i) x ≤ P.presentation.offset i} by
    ext x
    simp [HalfspacePresentation.carrier]]
  exact MeasurableSet.iInter fun _ => measurableSet_le (by fun_prop) measurable_const

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · expressed the carrier as a finite intersection of measurable affine
  halfspaces
-/
