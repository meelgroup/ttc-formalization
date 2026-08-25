import Kr25Ssmxt.Analysis.CubulationUnionError
import Kr25Ssmxt.Analysis.IntegerCubulationVolume
import Kr25Ssmxt.Analysis.IntegerLatticePolytopeComparison
import Kr25Ssmxt.Analysis.ScaledComponentCubulationError
import Kr25Ssmxt.Analysis.ScaledUnionEqIUnion
import Kr25Ssmxt.Analysis.ScaledUnionRegular

/-!
# Integer-lattice comparison for a finite polytope union

This module is the substantive nonconvex geometric step.  Components may overlap and may
have different incenters; its statement deliberately assumes no common-center dilation.
-/

namespace Kr25Ssmxt

open scoped ENNReal symmDiff

/--
The scaled finite union satisfying the paper radius bound has volume within relative error
`η` of its number of standard integer-lattice points.

PAPER: sections/analysis.tex:124-246
-/
lemma integer_lattice_union_comparison
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
    (MeasureTheory.volume
      ((fun x : Point n => (10 : Real) ^ b • x) '' D.union)).toReal ∈
      Arlib.relErr η
        (((((fun x : Point n => (10 : Real) ^ b • x) '' D.union) ∩
          {x : Point n | ∀ i, ∃ z : Int, x i = (z : Real)}).ncard : Real)) := by
  classical
  by_cases hmzero : D.componentCount = 0
  · have hunion : D.union = ∅ := by
      rw [Decomposition.union]
      apply Set.iUnion_eq_empty.2
      intro i
      exact (Nat.not_lt_zero i (hmzero ▸ i.isLt)).elim
    simp [hunion, Arlib.relErr]
  · have hm : 0 < D.componentCount := Nat.pos_of_ne_zero hmzero
    let S : Fin D.componentCount → Set (Point n) := fun i ↦
      (fun x : Point n => (10 : Real) ^ b • x) '' (D.component i).carrier
    let A : Set (Point n) :=
      (fun x : Point n => (10 : Real) ^ b • x) '' D.union
    let q : Real :=
      (((A ∩ {x : Point n | ∀ i, ∃ z : Int, x i = (z : Real)}).ncard : Real))
    have hA : A = ⋃ i, S i := by
      simpa [A, S] using scaled_union_eq_iUnion D b
    rcases scaled_union_regular D b with ⟨hAnull, hAfin, hAbounded⟩
    change MeasureTheory.NullMeasurableSet A MeasureTheory.volume at hAnull
    change MeasureTheory.volume A ≠ ∞ at hAfin
    change Bornology.IsBounded A at hAbounded
    rcases integer_cubulation_volume hn A hAbounded with
      ⟨hCnull, hCfin, hCcount⟩
    have hCcount' :
        (MeasureTheory.volume (integerCubulation A)).toReal = q := by
      simpa [q] using hCcount
    have hcomponent : ∀ i,
        MeasureTheory.volume (S i ∆ integerCubulation (S i)) ≠ ∞ ∧
          (MeasureTheory.volume (S i ∆ integerCubulation (S i))).toReal ≤
            (η / (D.componentCount : Real)) *
              (MeasureTheory.volume (integerCubulation (S i))).toReal := by
      simpa [S] using
        scaled_component_cubulation_error hn D b η hηpos hηle hm hradius
    have hCUnionFin :
        MeasureTheory.volume (integerCubulation (⋃ i, S i)) ≠ ∞ := by
      simpa only [← hA] using hCfin
    have hunionError :
        (MeasureTheory.volume (A ∆ integerCubulation A)).toReal ≤
          η * (MeasureTheory.volume (integerCubulation A)).toReal := by
      simpa only [← hA] using
        cubulation_union_error hm S η hηpos.le hcomponent hCUnionFin
    have habsMeasure :
        |(MeasureTheory.volume A).toReal -
            (MeasureTheory.volume (integerCubulation A)).toReal| ≤
          (MeasureTheory.volume (A ∆ integerCubulation A)).toReal :=
      MeasureTheory.abs_measureReal_sub_le_measureReal_symmDiff'
        hAnull hCnull hAfin hCfin
    have habs : |(MeasureTheory.volume A).toReal - q| ≤ η * q := by
      calc
        |(MeasureTheory.volume A).toReal - q| =
            |(MeasureTheory.volume A).toReal -
              (MeasureTheory.volume (integerCubulation A)).toReal| := by rw [hCcount']
        _ ≤ (MeasureTheory.volume (A ∆ integerCubulation A)).toReal := habsMeasure
        _ ≤ η * (MeasureTheory.volume (integerCubulation A)).toReal := hunionError
        _ = η * q := by rw [hCcount']
    change (MeasureTheory.volume A).toReal ∈ Arlib.relErr η q
    rw [Arlib.mem_relErr]
    constructor
    · have := neg_le_of_abs_le habs
      nlinarith
    · have := le_of_abs_le habs
      nlinarith

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · reduced · closed the headline from integer cubulation volume and component boundary-layer budgets
* r1 · reduced · isolated the nonconvex integer-lattice theorem without a common center
-/

end Kr25Ssmxt
