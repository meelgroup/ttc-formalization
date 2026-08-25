import Kr25Ssmxt.Analysis.FinitePolytopeFamilyCubulationError
import Kr25Ssmxt.Analysis.IntegerCubulationVolume
import Kr25Ssmxt.Analysis.ScaledUnionRegular
import Kr25Ssmxt.Analysis.SingletonDecomposition

/-!
# Integer-lattice comparison for scaled components

This is the single-component geometric estimate after scaling a decomposition by
`10 ^ b`.  It is separated from the finite-union estimate because it does not require
controlling overlaps between distinct components.
-/

namespace Kr25Ssmxt

open scoped ENNReal symmDiff

/--
Every scaled component satisfying the global paper radius bound has volume within relative
error `η` of its number of standard integer-lattice points.

PAPER: sections/analysis.tex:117-133
-/
lemma integer_lattice_polytope_comparison
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
    ∀ i,
      (MeasureTheory.volume
        ((fun x : Point n => (10 : Real) ^ b • x) ''
          (D.component i).carrier)).toReal ∈
        Arlib.relErr η
          (((((fun x : Point n => (10 : Real) ^ b • x) ''
              (D.component i).carrier) ∩
            {x : Point n | ∀ j, ∃ z : Int, x j = (z : Real)}).ncard : Real)) := by
  classical
  intro i
  have hm : 0 < D.componentCount := Nat.pos_of_ne_zero (by
    intro hmzero
    exact Nat.not_lt_zero i (hmzero ▸ i.isLt))
  let A : Set (Point n) :=
    (fun x : Point n => (10 : Real) ^ b • x) '' (D.component i).carrier
  let q : Real :=
    (((A ∩ {x : Point n | ∀ j, ∃ z : Int, x j = (z : Real)}).ncard : Real))
  let Di := singletonDecomposition (D.component i)
  have hAregular := scaled_union_regular Di b
  have hAeq :
      (fun x : Point n => (10 : Real) ^ b • x) '' Di.union = A := by
    simp [A, Di, singletonDecomposition_union]
  rw [hAeq] at hAregular
  rcases hAregular with ⟨hAnull, hAfin, hAbounded⟩
  rcases integer_cubulation_volume hn A hAbounded with
    ⟨hCnull, hCfin, hCcount⟩
  have hCcount' :
      (MeasureTheory.volume (integerCubulation A)).toReal = q := by
    simpa [q] using hCcount
  have hcomponent :=
    finite_polytope_family_cubulation_error
      hn hm D.component b η hηpos hηle (by
        simpa only [latticeRadiusRequirement, Decomposition.totalFacets] using hradius) i
  dsimp only at hcomponent
  change MeasureTheory.volume (A ∆ integerCubulation A) ≠ ∞ ∧
      (MeasureTheory.volume (A ∆ integerCubulation A)).toReal ≤
        (η / (D.componentCount : Real)) *
          (MeasureTheory.volume (integerCubulation A)).toReal at hcomponent
  have hbudget : η / (D.componentCount : Real) ≤ η :=
    div_le_self hηpos.le (by exact_mod_cast hm)
  have hunionError :
      (MeasureTheory.volume (A ∆ integerCubulation A)).toReal ≤
        η * (MeasureTheory.volume (integerCubulation A)).toReal := by
    calc
      (MeasureTheory.volume (A ∆ integerCubulation A)).toReal ≤
          (η / (D.componentCount : Real)) *
            (MeasureTheory.volume (integerCubulation A)).toReal := hcomponent.2
      _ ≤ η * (MeasureTheory.volume (integerCubulation A)).toReal :=
        mul_le_mul_of_nonneg_right hbudget ENNReal.toReal_nonneg
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

* r2 · proved · derived the component estimate from cubulation error and exact cubulation volume
* r1 · reduced · stated the scaled single-component integer-lattice estimate
-/

end Kr25Ssmxt
