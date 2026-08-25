import Kr25Ssmxt.Model.Prelude
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Scaling the decimal lattice to the integer lattice

Multiplication by `10 ^ b` sends the decimal lattice bijectively to the standard integer
lattice, preserves lattice-point cardinality, and scales `n`-dimensional volume by
`10 ^ (b * n)`.
-/

namespace Kr25Ssmxt

open scoped Pointwise

/--
An integer-lattice relative-error comparison for the scaled image of a set transfers to
the corresponding decimal-lattice comparison for the original set.

PAPER: sections/analysis.tex:247-263
-/
lemma decimal_lattice_scaling
    {n : Nat}
    (hn : 0 < n)
    (S : Set (Point n))
    (b : Nat)
    (η : Real)
    (hinteger :
      (MeasureTheory.volume
        ((fun x : Point n => (10 : Real) ^ b • x) '' S)).toReal ∈
        Arlib.relErr η
          ((((fun x : Point n => (10 : Real) ^ b • x) '' S) ∩
            {x : Point n | ∀ i, ∃ z : Int, x i = (z : Real)}).ncard : Real)) :
    (MeasureTheory.volume S).toReal ∈
      Arlib.relErr η
        ((S ∩ decimalLattice b n).ncard / (10 : Real) ^ (b * n)) := by
  let a : Real := (10 : Real) ^ b
  let d : Real := (10 : Real) ^ (b * n)
  let T : Point n → Point n := fun x ↦ a • x
  let Z : Set (Point n) := {x | ∀ i, ∃ z : Int, x i = (z : Real)}
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have had : a ^ n = d := by
    dsimp [a, d]
    rw [pow_mul]
  have hvolume :
      (MeasureTheory.volume (T '' S)).toReal =
        d * (MeasureTheory.volume S).toReal := by
    calc
      (MeasureTheory.volume (T '' S)).toReal =
          (MeasureTheory.volume (a • S)).toReal := by
            rw [← Set.image_smul]
      _ = (ENNReal.ofReal
            |a ^ Module.finrank Real (Point n)| * MeasureTheory.volume S).toReal := by
            rw [MeasureTheory.volume.addHaar_smul]
      _ = d * (MeasureTheory.volume S).toReal := by
            rw [ENNReal.toReal_ofReal_mul _ _ (abs_nonneg _)]
            rw [Module.finrank_fin_fun, abs_of_pos (pow_pos ha n), had]
  have hset :
      T '' (S ∩ decimalLattice b n) = (T '' S) ∩ Z := by
    ext y
    constructor
    · rintro ⟨x, ⟨hxS, hxL⟩, rfl⟩
      refine ⟨⟨x, hxS, rfl⟩, ?_⟩
      intro i
      rcases hxL i with ⟨z, hz⟩
      refine ⟨z, ?_⟩
      change a * x i = (z : Real)
      change x i = (z : Real) / a at hz
      rw [hz]
      field_simp [ha.ne']
    · rintro ⟨⟨x, hxS, rfl⟩, hxZ⟩
      refine ⟨x, ⟨hxS, ?_⟩, rfl⟩
      intro i
      rcases hxZ i with ⟨z, hz⟩
      refine ⟨z, ?_⟩
      change a * x i = (z : Real) at hz
      change x i = (z : Real) / a
      exact (eq_div_iff ha.ne').2 (by simpa [mul_comm] using hz)
  have hTinj : Function.Injective T := by
    intro x y hxy
    funext i
    have hi := congrFun hxy i
    change a * x i = a * y i at hi
    exact (mul_left_cancel₀ ha.ne') hi
  have hcount :
      (((T '' S) ∩ Z).ncard : Real) =
        ((S ∩ decimalLattice b n).ncard : Real) := by
    norm_cast
    calc
      ((T '' S) ∩ Z).ncard = (T '' (S ∩ decimalLattice b n)).ncard := by
        rw [hset]
      _ = (S ∩ decimalLattice b n).ncard :=
        Set.ncard_image_of_injective _ hTinj
  change (MeasureTheory.volume (T '' S)).toReal ∈
    Arlib.relErr η (((T '' S) ∩ Z).ncard : Real) at hinteger
  rw [hvolume, hcount, Arlib.mem_relErr] at hinteger
  change (MeasureTheory.volume S).toReal ∈
    Arlib.relErr η (((S ∩ decimalLattice b n).ncard : Real) / d)
  rw [Arlib.mem_relErr]
  constructor
  · rw [← mul_div_assoc]
    exact (div_le_iff₀ hd).2 (by simpa [mul_comm] using hinteger.1)
  · rw [← mul_div_assoc]
    exact (le_div_iff₀ hd).2 (by simpa [mul_comm] using hinteger.2)

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · proved · exact Haar scaling and the decimal/integer lattice bijection close the transfer
* r1 · reduced · isolated the decimal-to-integer lattice bijection and volume scaling
-/

end Kr25Ssmxt
