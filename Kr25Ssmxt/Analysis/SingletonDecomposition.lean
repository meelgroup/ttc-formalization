import Kr25Ssmxt.Analysis.HalfspaceFormulaSatisfies

/-!
# Singleton decompositions

Every certified polytope can be packaged as a one-component decomposition of the QF-LRA
formula expressing its halfspace presentation.  Its decomposition union is definitionally
the same geometric carrier up to the elementary singleton-indexed union identity proved
below.
-/

namespace Kr25Ssmxt

/--
The formula represented by a single certified polytope.

INTERNAL: formula used as the index of the singleton decomposition.
-/
def singletonFormula {n : Nat} (P : PolytopeData n) : LRAFormula n 0 :=
  halfspaceFormula P.presentation

/--
A certified polytope regarded as a decomposition with one component.

INTERNAL: reduces a component comparison to the finite-union comparison.
-/
def singletonDecomposition {n : Nat} (P : PolytopeData n) :
    Decomposition (singletonFormula P) where
  componentCount := 1
  component := fun _ => P
  solution_ae := by
    filter_upwards [] with x
    simp only [singletonFormula, solutionSet, Set.mem_iUnion]
    constructor
    · rintro ⟨j, hx⟩
      refine ⟨fun q => Fin.elim0 q, ?_⟩
      simpa using (halfspaceFormula_satisfies P.presentation (fun q => Fin.elim0 q) x).2 hx
    · rintro ⟨β, hx⟩
      refine ⟨0, ?_⟩
      simpa using (halfspaceFormula_satisfies P.presentation β x).1 hx

/--
The union of a singleton decomposition is the carrier of its sole polytope.

INTERNAL: rewrite used after applying the finite-union lattice comparison.
-/
lemma singletonDecomposition_union {n : Nat} (P : PolytopeData n) :
    (singletonDecomposition P).union = P.carrier := by
  ext x
  simp [Decomposition.union, singletonDecomposition]

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r3 · proved · packaged one polytope as a decomposition and identified its union
-/

end Kr25Ssmxt
