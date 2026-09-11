import Kr25Ssmxt.Model.Program

/-!
# Indexing decomposition components

Membership in the component list processed by TTC is equivalent to occurrence at one of
the decomposition's finite indices.
-/

namespace Kr25Ssmxt

/--
Every member of `List.ofFn D.component` is supplied by a `Fin D.componentCount` index.

INTERNAL: bridge from list induction to the contracts' finite indexing.
-/
lemma component_mem_has_index {n k : Nat} {F : LRAFormula n k} (D : Decomposition F)
    {P : PolytopeData n} (hP : P ∈ List.ofFn D.component) :
    ∃ i : Fin D.componentCount, D.component i = P := by
  exact List.mem_ofFn.mp hP

end Kr25Ssmxt
