import Kr25Ssmxt.Model.Prelude

/-!
# Scaling a finite component union

The image of a decomposition union under scalar multiplication is the union of the
images of its components.
-/

namespace Kr25Ssmxt

/--
Scaling commutes with the finite union represented by a decomposition.

INTERNAL: set identity exposing the scaled target as a component-indexed union
-/
lemma scaled_union_eq_iUnion
    {n k : Nat} {F : LRAFormula n k} (D : Decomposition F) (b : Nat) :
    (fun x : Point n => (10 : Real) ^ b • x) '' D.union =
      ⋃ i, (fun x : Point n => (10 : Real) ^ b • x) '' (D.component i).carrier := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Decomposition.union] at hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, ⟨x, hi, rfl⟩⟩
  · intro hy
    rcases Set.mem_iUnion.mp hy with ⟨i, x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    rw [Decomposition.union]
    exact Set.mem_iUnion.mpr ⟨i, hx⟩

end Kr25Ssmxt
