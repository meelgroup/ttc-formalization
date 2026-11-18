import Kr25Ssmxt.Analysis.ReferenceProgram

/-!
# Cardinality of the coded decimal lattice

The sampling oracle is stated on countable lattice codes, whereas the accuracy target is
stated on geometric points.  At a fixed precision these are two presentations of the same
finite set.
-/

noncomputable section

namespace Kr25Ssmxt

/-- Fixed-precision lattice codes in a component have the same cardinality as the
component's geometric decimal-lattice intersection.

INTERNAL: representation bridge in the component-prefix counting invariant for
`process_components_lattice_count_accuracy`.
-/
lemma process_components_lattice_count_accuracy_coded_card
    {n : Nat} (P : PolytopeData n) (b : Nat) :
    (codedLatticePoints P b).ncard =
      (P.carrier ∩ decimalLattice b n).ncard := by
  refine Set.ncard_congr (fun x _ => x.toPoint) ?_ ?_ ?_
  · intro x hx
    constructor
    · exact hx.2
    · intro i
      exact ⟨x.2 i, by simp [LatticePoint.toPoint, hx.1]⟩
  · intro x y hx hy hxy
    apply Prod.ext
    · exact hx.1.trans hy.1.symm
    · funext i
      have hcoord := congrFun hxy i
      change (x.2 i : Real) / (10 : Real) ^ x.1 =
          (y.2 i : Real) / (10 : Real) ^ y.1 at hcoord
      rw [hx.1, hy.1] at hcoord
      have hcast : (x.2 i : Real) = (y.2 i : Real) :=
        (div_left_inj' (pow_ne_zero b (by norm_num))).mp hcoord
      exact Int.cast_injective hcast
  · intro y hy
    choose z hz using hy.2
    let x : LatticePoint n := (b, z)
    have hxpoint : x.toPoint = y := by
      funext i
      simpa [x, LatticePoint.toPoint] using (hz i).symm
    refine ⟨x, ?_, hxpoint⟩
    exact ⟨rfl, hxpoint.symm ▸ hy.1⟩

end Kr25Ssmxt
