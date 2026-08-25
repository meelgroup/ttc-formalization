import Kr25Ssmxt.Analysis.IntegerCubulation

/-!
# Cubulation error for a finite union

Integer cubulation commutes with unions.  The symmetric difference of two finite unions
is contained in the union of the component symmetric differences, so component error
budgets add without assuming disjoint components.
-/

open scoped ENNReal symmDiff

namespace Kr25Ssmxt

/--
Per-component `η / m` cubulation errors give an `η` cubulation error for the union.

INTERNAL: finite-union bookkeeping for overlapping component carriers
-/
lemma cubulation_union_error
    {n m : Nat}
    (hm : 0 < m)
    (S : Fin m → Set (Point n))
    (η : Real)
    (hηnonneg : 0 ≤ η)
    (hcomponent : ∀ i,
      MeasureTheory.volume (S i ∆ integerCubulation (S i)) ≠ ∞ ∧
        (MeasureTheory.volume (S i ∆ integerCubulation (S i))).toReal ≤
          (η / (m : Real)) *
            (MeasureTheory.volume (integerCubulation (S i))).toReal)
    (hcubFinite : MeasureTheory.volume (integerCubulation (⋃ i, S i)) ≠ ∞) :
    (MeasureTheory.volume ((⋃ i, S i) ∆ integerCubulation (⋃ i, S i))).toReal ≤
      η * (MeasureTheory.volume (integerCubulation (⋃ i, S i))).toReal := by
  have hcubUnion :
      integerCubulation (⋃ i, S i) = ⋃ i, integerCubulation (S i) := by
    ext x
    constructor
    · rintro ⟨z, hz, hbox⟩
      rw [Set.mem_iUnion] at hz
      rcases hz with ⟨i, hi⟩
      rw [Set.mem_iUnion]
      exact ⟨i, z, hi, hbox⟩
    · intro hx
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨i, z, hz, hbox⟩
      exact ⟨z, Set.mem_iUnion.mpr ⟨i, hz⟩, hbox⟩
  have herrorSubset :
      (⋃ i, S i) ∆ integerCubulation (⋃ i, S i) ⊆
        ⋃ i, S i ∆ integerCubulation (S i) := by
    intro x hx
    rw [Set.symmDiff_def] at hx
    rcases hx with hx | hx
    · rcases Set.mem_iUnion.mp hx.1 with ⟨i, hSi⟩
      have hnotCi : x ∉ integerCubulation (S i) := by
        intro hCi
        apply hx.2
        rw [hcubUnion, Set.mem_iUnion]
        exact ⟨i, hCi⟩
      rw [Set.mem_iUnion]
      exact ⟨i, Or.inl ⟨hSi, hnotCi⟩⟩
    · have hxUnion : x ∈ ⋃ i, integerCubulation (S i) := by
        rw [← hcubUnion]
        exact hx.1
      rcases Set.mem_iUnion.mp hxUnion with ⟨i, hCi⟩
      have hnotSi : x ∉ S i := by
        intro hSi
        exact hx.2 (Set.mem_iUnion.mpr ⟨i, hSi⟩)
      rw [Set.mem_iUnion]
      exact ⟨i, Or.inr ⟨hCi, hnotSi⟩⟩
  have hcubSubset (i : Fin m) :
      integerCubulation (S i) ⊆ integerCubulation (⋃ i, S i) := by
    intro x hx
    rw [hcubUnion, Set.mem_iUnion]
    exact ⟨i, hx⟩
  have hcubToReal (i : Fin m) :
      (MeasureTheory.volume (integerCubulation (S i))).toReal ≤
        (MeasureTheory.volume (integerCubulation (⋃ i, S i))).toReal :=
    ENNReal.toReal_mono hcubFinite
      (MeasureTheory.measure_mono (hcubSubset i))
  have hfactorNonneg : 0 ≤ η / (m : Real) :=
    div_nonneg hηnonneg (Nat.cast_nonneg m)
  have hcomponentUnion (i : Fin m) :
      (MeasureTheory.volume (S i ∆ integerCubulation (S i))).toReal ≤
        (η / (m : Real)) *
          (MeasureTheory.volume (integerCubulation (⋃ i, S i))).toReal := by
    calc
      (MeasureTheory.volume (S i ∆ integerCubulation (S i))).toReal ≤
          (η / (m : Real)) *
            (MeasureTheory.volume (integerCubulation (S i))).toReal :=
        (hcomponent i).2
      _ ≤ (η / (m : Real)) *
            (MeasureTheory.volume (integerCubulation (⋃ i, S i))).toReal :=
        mul_le_mul_of_nonneg_left (hcubToReal i) hfactorNonneg
  have hmeasure :
      MeasureTheory.volume ((⋃ i, S i) ∆ integerCubulation (⋃ i, S i)) ≤
        ∑ i, MeasureTheory.volume (S i ∆ integerCubulation (S i)) := by
    calc
      MeasureTheory.volume ((⋃ i, S i) ∆ integerCubulation (⋃ i, S i)) ≤
          MeasureTheory.volume (⋃ i, S i ∆ integerCubulation (S i)) :=
        MeasureTheory.measure_mono herrorSubset
      _ ≤ ∑ i, MeasureTheory.volume (S i ∆ integerCubulation (S i)) :=
        MeasureTheory.measure_iUnion_fintype_le MeasureTheory.volume _
  have hsumFinite :
      (∑ i, MeasureTheory.volume (S i ∆ integerCubulation (S i))) ≠ ∞ := by
    rw [ENNReal.sum_ne_top]
    intro i hi
    exact (hcomponent i).1
  calc
    (MeasureTheory.volume ((⋃ i, S i) ∆ integerCubulation (⋃ i, S i))).toReal ≤
        (∑ i, MeasureTheory.volume (S i ∆ integerCubulation (S i))).toReal :=
      ENNReal.toReal_mono hsumFinite hmeasure
    _ = ∑ i, (MeasureTheory.volume
          (S i ∆ integerCubulation (S i))).toReal := by
      rw [ENNReal.toReal_sum]
      intro i hi
      exact (hcomponent i).1
    _ ≤ ∑ _i : Fin m, (η / (m : Real)) *
          (MeasureTheory.volume (integerCubulation (⋃ i, S i))).toReal :=
      Finset.sum_le_sum fun i _hi ↦ hcomponentUnion i
    _ = (m : Real) * ((η / (m : Real)) *
          (MeasureTheory.volume (integerCubulation (⋃ i, S i))).toReal) := by
      simp
    _ = η * (MeasureTheory.volume
          (integerCubulation (⋃ i, S i))).toReal := by
      have hmR : (m : Real) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
      field_simp [hmR]

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* current · proved · finite-union subadditivity and component-to-union cubulation monotonicity
-/
