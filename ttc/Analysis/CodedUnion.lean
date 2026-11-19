import ttc.Analysis.PrecisionRequirements
import ttc.Analysis.UnionLatticeNonempty
import ttc.Analysis.ProcessComponentsLatticeCountAccuracyCodedCard

/-! Finite fixed-precision codes for the entire union, used as the coordinate
type of the Poisson point-count process. -/

namespace ttc

def Decomposition.codedUnionLatticePoints
    {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (b : Nat) : Set (LatticePoint n) :=
  {x | x.1 = b ∧ x.toPoint ∈ D.union}

theorem Decomposition.codedUnion_eq_iUnion
    {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (b : Nat) :
    D.codedUnionLatticePoints b =
      ⋃ i : Fin D.componentCount, codedLatticePoints (D.component i) b := by
  ext x
  simp [Decomposition.codedUnionLatticePoints,
    Decomposition.union, codedLatticePoints, and_comm,
    exists_and_left, exists_and_right]

theorem Decomposition.codedUnion_finite
    {n k : Nat} (hn : 0 < n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta) :
    (D.codedUnionLatticePoints b).Finite := by
  rw [D.codedUnion_eq_iUnion b]
  exact Set.finite_iUnion fun i =>
    (coded_lattice_points_finite_nonempty hn D p b hprecision i).1

theorem Decomposition.codedUnion_ncard_eq_latticePoints
    {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (b : Nat) :
    (D.codedUnionLatticePoints b).ncard =
      (D.latticePoints b).ncard := by
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

theorem Decomposition.codedUnion_nonempty
    {n k : Nat} (hn : 0 < n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (hcomponents : 0 < D.componentCount) :
    (D.codedUnionLatticePoints b).Nonempty := by
  let i : Fin D.componentCount := ⟨0, hcomponents⟩
  obtain ⟨x, hx⟩ :=
    (coded_lattice_points_finite_nonempty hn D p b hprecision i).2
  refine ⟨x, ?_⟩
  exact ⟨hx.1, Set.mem_iUnion.mpr ⟨i, hx.2⟩⟩

end ttc
