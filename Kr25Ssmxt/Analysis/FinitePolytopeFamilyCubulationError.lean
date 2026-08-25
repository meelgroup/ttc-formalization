import Kr25Ssmxt.Analysis.IntegerCubulation
import Kr25Ssmxt.Analysis.IntegerCubulationCellControl
import Kr25Ssmxt.Analysis.ScaledPolytopeInball
import Kr25Ssmxt.Analysis.CubulationHomothetySandwich
import Kr25Ssmxt.Analysis.CubulationErrorOfInball
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Cubulation error for a finite family of polytopes

This module isolates the geometric boundary-layer estimate required to pass from
componentwise inradius bounds to a comparison between a scaled polytope and the union of
unit cubes based at its integer lattice points.
-/

open scoped ENNReal symmDiff

namespace Kr25Ssmxt

/--
Under the paper's global radius bound for a finite family, each scaled component spends at
most its `η / m` share of the relative cubulation-error budget.

INTERNAL: geometric boundary-layer estimate needed to implement the finite-union lattice argument
-/
lemma finite_polytope_family_cubulation_error
    {n m : Nat}
    (hn : 0 < n)
    (hm : 0 < m)
    (P : Fin m → PolytopeData n)
    (b : Nat)
    (η : Real)
    (hηpos : 0 < η)
    (hηle : η ≤ 1)
    (hradius : ∀ i,
      ((64 * m * n / η) *
          Real.sqrt (Real.log (4 * (∑ j, (P j).presentation.facetCount) / η))) ≤
        (10 : Real) ^ b * (P i).inradius) :
    ∀ i,
      let A := (fun x : Point n => (10 : Real) ^ b • x) '' (P i).carrier
      MeasureTheory.volume (A ∆ integerCubulation A) ≠ ∞ ∧
        (MeasureTheory.volume (A ∆ integerCubulation A)).toReal ≤
          (η / (m : Real)) *
            (MeasureTheory.volume (integerCubulation A)).toReal := by
  classical
  intro i
  dsimp only
  let s : Real := (10 : Real) ^ b
  let A : Set (Point n) := (fun x : Point n => s • x) '' (P i).carrier
  let c : Point n := s • (P i).incenter
  let R : Real := s * (P i).inradius
  change MeasureTheory.volume (A ∆ integerCubulation A) ≠ ∞ ∧
    (MeasureTheory.volume (A ∆ integerCubulation A)).toReal ≤
      (η / (m : Real)) *
        (MeasureTheory.volume (integerCubulation A)).toReal
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hgeometry := scaled_polytope_inball (P i) s hs
  dsimp only at hgeometry
  change Convex Real A ∧
      Bornology.IsBounded A ∧
      MeasureTheory.NullMeasurableSet A MeasureTheory.volume ∧
      Metric.closedBall c R ⊆ A at hgeometry
  rcases hgeometry with ⟨hconvex, hbounded, hnull, hinball⟩
  have hfacets : 0 < ∑ j, (P j).presentation.facetCount := by
    apply Finset.sum_pos
    · intro j hj
      exact (P j).facets_pos
    · exact ⟨i, Finset.mem_univ i⟩
  have hfacets_one :
      (1 : Real) ≤ ((∑ j, (P j).presentation.facetCount : Nat) : Real) := by
    exact_mod_cast hfacets
  have hratio :
      (4 : Real) ≤ 4 * (∑ j, (P j).presentation.facetCount) / η := by
    rw [le_div_iff₀ hηpos]
    nlinarith
  have hsqrt :
      (1 : Real) ≤
        Real.sqrt (Real.log (4 * (∑ j, (P j).presentation.facetCount) / η)) := by
    rw [Real.one_le_sqrt]
    have hlog4 : (1 : Real) ≤ Real.log 4 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      exact Real.exp_one_lt_three.le.trans (by norm_num)
    exact hlog4.trans (Real.log_le_log (by norm_num) hratio)
  have hbase_nonneg :
      0 ≤ 64 * (m : Real) * (n : Real) / η := by
    positivity
  have hscaledRadius :
      64 * (m : Real) * (n : Real) / η ≤ R := by
    calc
      64 * (m : Real) * (n : Real) / η ≤
          (64 * (m : Real) * (n : Real) / η) *
            Real.sqrt
              (Real.log (4 * (∑ j, (P j).presentation.facetCount) / η)) := by
        exact le_mul_of_one_le_right hbase_nonneg hsqrt
      _ ≤ R := by
        simpa only [R, s] using hradius i
  have hm_one : (1 : Real) ≤ (m : Real) := by
    exact_mod_cast hm
  have hn_one : (1 : Real) ≤ (n : Real) := by
    exact_mod_cast hn
  have hbase_ge :
      (64 : Real) ≤ 64 * (m : Real) * (n : Real) / η := by
    rw [le_div_iff₀ hηpos]
    nlinarith [mul_nonneg (sub_nonneg.mpr hm_one) (sub_nonneg.mpr hn_one)]
  have hR : 1 < R :=
    lt_of_lt_of_le (by norm_num) (hbase_ge.trans hscaledRadius)
  have hcell := integerCubulation_cell_control A
  have hsandwich :=
    cubulation_homothety_sandwich A c R hR hconvex hinball hcell
  exact cubulation_error_of_inball hn hm A c R η hηpos hηle hscaledRadius
    hconvex hbounded hnull hinball hsandwich

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · reduced · closed the family theorem from four isolated geometric dependencies
* r1 · reduced · isolated the missing component boundary-layer theorem for a finite family
-/

end Kr25Ssmxt
