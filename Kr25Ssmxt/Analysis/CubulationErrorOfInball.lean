import Kr25Ssmxt.Analysis.CubulationHomothetySandwich
import Kr25Ssmxt.Analysis.CubulationHomothetyPowerBound
import Kr25Ssmxt.Analysis.HomothetyImageNullMeasurable

/-!
# Cubulation error from a large inball

This module packages the homothety sandwich, volume scaling, finiteness, and elementary
power bounds into the relative error estimate used for each polytope component.
-/

open scoped ENNReal symmDiff

namespace Kr25Ssmxt

/--
If a bounded measurable convex set has inradius at least `64 * m * n / η`, its
cubulation error consumes at most an `η / m` fraction of cubulation volume.

INTERNAL: boundary-layer volume consequence of the centered homothety sandwich
-/
lemma cubulation_error_of_inball {n m : Nat}
    (hn : 0 < n)
    (hm : 0 < m)
    (S : Set (Point n))
    (c : Point n)
    (R η : Real)
    (hηpos : 0 < η)
    (hηle : η ≤ 1)
    (hradius : 64 * (m : Real) * (n : Real) / η ≤ R)
    (hconvex : Convex Real S)
    (hbounded : Bornology.IsBounded S)
    (hnull : MeasureTheory.NullMeasurableSet S MeasureTheory.volume)
    (hinball : Metric.closedBall c R ⊆ S)
    (hsandwich :
      (fun x : Point n => c + (1 - 1 / R) • (x - c)) '' S ⊆
          S ∩ integerCubulation S ∧
        S ∪ integerCubulation S ⊆
          (fun x : Point n => c + (1 + 1 / R) • (x - c)) '' S) :
    MeasureTheory.volume (S ∆ integerCubulation S) ≠ ∞ ∧
      (MeasureTheory.volume (S ∆ integerCubulation S)).toReal ≤
        (η / (m : Real)) *
          (MeasureTheory.volume (integerCubulation S)).toReal := by
  let a : Real := 1 - 1 / R
  let b : Real := 1 + 1 / R
  let H : Real → Set (Point n) := fun r =>
    (fun x : Point n => c + r • (x - c)) '' S
  let C : Set (Point n) := integerCubulation S
  have hpower := cubulation_homothety_power_bound hn hm R η hηpos hηle hradius
  have ha : 0 < a := by simpa [a] using hpower.1
  have hb : 0 < b := by
    dsimp [b]
    have hR : 0 < R := by
      have hmR : 0 < (m : Real) := by exact_mod_cast hm
      have hnR : 0 < (n : Real) := by exact_mod_cast hn
      have : 0 < 64 * (m : Real) * (n : Real) / η :=
        div_pos (mul_pos (mul_pos (by norm_num) hmR) hnR) hηpos
      exact this.trans_le hradius
    positivity
  have hpow : b ^ n - a ^ n ≤ (η / (m : Real)) * a ^ n := by
    simpa [a, b] using hpower.2
  have hAfin : MeasureTheory.volume (H a) ≠ ∞ := by
    rw [show H a = AffineMap.homothety c a '' S by
      apply Set.image_congr
      intro x hx
      rw [AffineMap.homothety_apply]
      ext i
      dsimp
      ring]
    rw [MeasureTheory.Measure.addHaar_image_homothety]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbounded.measure_lt_top.ne
  have hBfin : MeasureTheory.volume (H b) ≠ ∞ := by
    rw [show H b = AffineMap.homothety c b '' S by
      apply Set.image_congr
      intro x hx
      rw [AffineMap.homothety_apply]
      ext i
      dsimp
      ring]
    rw [MeasureTheory.Measure.addHaar_image_homothety]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbounded.measure_lt_top.ne
  have hAmeas : MeasureTheory.NullMeasurableSet (H a) MeasureTheory.volume := by
    apply homothety_image_nullMeasurable S c a hnull ha.ne'
  have hAinter : H a ⊆ S ∩ C := by simpa [H, a, C] using hsandwich.1
  have hunionB : S ∪ C ⊆ H b := by simpa [H, b, C] using hsandwich.2
  have hAB : H a ⊆ H b := hAinter.trans (Set.inter_subset_left.trans Set.subset_union_left) |>.trans hunionB
  have hsymm : S ∆ C ⊆ H b \ H a := by
    intro x hx
    rw [Set.mem_symmDiff] at hx
    rcases hx with ⟨hxS, hxC⟩ | ⟨hxC, hxS⟩
    constructor
    · exact hunionB (Set.mem_union_left C hxS)
    · exact fun hxA => hxC (hAinter hxA).2
    constructor
    · exact hunionB (Set.mem_union_right S hxC)
    · exact fun hxA => hxS (hAinter hxA).1
  have hCsub : C ⊆ H b := Set.subset_union_right.trans hunionB
  have hCfin : MeasureTheory.volume C ≠ ∞ :=
    ne_of_lt ((MeasureTheory.measure_mono hCsub).trans_lt (lt_top_iff_ne_top.2 hBfin))
  have hsymmfin : MeasureTheory.volume (S ∆ C) ≠ ∞ :=
    ne_of_lt ((MeasureTheory.measure_mono hsymm).trans_lt
      ((MeasureTheory.measure_mono Set.sdiff_subset).trans_lt (lt_top_iff_ne_top.2 hBfin)))
  refine ⟨by simpa [C] using hsymmfin, ?_⟩
  have hmeasure : MeasureTheory.volume (S ∆ C) ≤
      MeasureTheory.volume (H b) - MeasureTheory.volume (H a) := by
    calc
      MeasureTheory.volume (S ∆ C) ≤ MeasureTheory.volume (H b \ H a) :=
        MeasureTheory.measure_mono hsymm
      _ = MeasureTheory.volume (H b) - MeasureTheory.volume (H a) :=
        MeasureTheory.measure_sdiff hAB hAmeas hAfin
  have hvol (r : Real) (hr : 0 ≤ r) :
      (MeasureTheory.volume (H r)).toReal = r ^ n * (MeasureTheory.volume S).toReal := by
    rw [show H r = AffineMap.homothety c r '' S by
      apply Set.image_congr
      intro x hx
      rw [AffineMap.homothety_apply]
      ext i
      dsimp
      ring]
    rw [MeasureTheory.Measure.addHaar_image_homothety, ENNReal.toReal_mul]
    rw [ENNReal.toReal_ofReal (abs_nonneg _)]
    simp [abs_of_nonneg (pow_nonneg hr n)]
  have htoReal : (MeasureTheory.volume (S ∆ C)).toReal ≤
      (MeasureTheory.volume (H b)).toReal - (MeasureTheory.volume (H a)).toReal := by
    calc
      (MeasureTheory.volume (S ∆ C)).toReal ≤
          (MeasureTheory.volume (H b) - MeasureTheory.volume (H a)).toReal :=
        ENNReal.toReal_mono (ENNReal.sub_ne_top hBfin) hmeasure
      _ = (MeasureTheory.volume (H b)).toReal -
          (MeasureTheory.volume (H a)).toReal :=
        ENNReal.toReal_sub_of_le (MeasureTheory.measure_mono hAB) hBfin
  have hAtoC : (MeasureTheory.volume (H a)).toReal ≤
      (MeasureTheory.volume C).toReal :=
    ENNReal.toReal_mono hCfin
      (MeasureTheory.measure_mono (hAinter.trans Set.inter_subset_right))
  calc
    (MeasureTheory.volume (S ∆ integerCubulation S)).toReal =
        (MeasureTheory.volume (S ∆ C)).toReal := by rfl
    _ ≤ (MeasureTheory.volume (H b)).toReal -
        (MeasureTheory.volume (H a)).toReal := htoReal
    _ = (b ^ n - a ^ n) * (MeasureTheory.volume S).toReal := by
      rw [hvol b hb.le, hvol a ha.le]
      ring
    _ ≤ ((η / (m : Real)) * a ^ n) *
        (MeasureTheory.volume S).toReal := by
      gcongr
    _ = (η / (m : Real)) * (MeasureTheory.volume (H a)).toReal := by
      rw [hvol a ha.le]
      ring
    _ ≤ (η / (m : Real)) * (MeasureTheory.volume C).toReal := by
      gcongr
    _ = (η / (m : Real)) *
        (MeasureTheory.volume (integerCubulation S)).toReal := by rfl

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r4 · proved · completed both helper proofs and the homothetic-annulus measure estimate
* r3 · reduced · closed the measure calculation using scalar and null-measurability helpers
* r2 · reduced · packaged sandwich, scaling, finiteness, and the power estimate
-/

end Kr25Ssmxt
