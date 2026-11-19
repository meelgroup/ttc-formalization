import ttc.Model.Prelude

/-!
# A QF-LRA formula for a halfspace presentation

This module encodes the finite conjunction of a presentation's closed halfspaces and
proves that its QF-LRA semantics is exactly the presented carrier.
-/

namespace ttc

/--
The conjunction of the inequalities at the supplied facet indices.

INTERNAL: recursive syntax used to encode a halfspace presentation as QF-LRA.
-/
def halfspaceConjunction {n : Nat} (H : HalfspacePresentation n) :
    List (Fin H.facetCount) → LRAFormula n 0
  | [] => .truth
  | i :: is =>
      .and
        (.atom {
          coefficients := H.normal i
          relation := .le
          constant := H.offset i })
        (halfspaceConjunction H is)

/--
Satisfaction of the recursive conjunction is equivalent to all indexed inequalities.

INTERNAL: induction principle for the halfspace formula encoding.
-/
lemma halfspaceConjunction_satisfies
    {n : Nat}
    (H : HalfspacePresentation n)
    (is : List (Fin H.facetCount))
    (β : Fin 0 → Bool)
    (x : Point n) :
    (halfspaceConjunction H is).Satisfies β x ↔
      ∀ i ∈ is, dotProduct (H.normal i) x ≤ H.offset i := by
  induction is with
  | nil => simp [halfspaceConjunction, LRAFormula.Satisfies]
  | cons i is ih =>
      simp [halfspaceConjunction, LRAFormula.Satisfies, LinearAtom.Holds, ih]

/--
The QF-LRA formula consisting of all inequalities in a halfspace presentation.

INTERNAL: syntax realizing a polytope carrier as a formula with no Boolean variables.
-/
def halfspaceFormula {n : Nat} (H : HalfspacePresentation n) : LRAFormula n 0 :=
  halfspaceConjunction H (List.ofFn id)

/--
The halfspace formula is satisfied exactly at points of the presented carrier.

INTERNAL: semantic bridge used to construct a singleton decomposition.
-/
lemma halfspaceFormula_satisfies
    {n : Nat}
    (H : HalfspacePresentation n)
    (β : Fin 0 → Bool)
    (x : Point n) :
    (halfspaceFormula H).Satisfies β x ↔ x ∈ H.carrier := by
  rw [halfspaceFormula, halfspaceConjunction_satisfies]
  simp [HalfspacePresentation.carrier]

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r3 · proved · encoded all closed halfspaces and proved exact carrier semantics
-/

end ttc
