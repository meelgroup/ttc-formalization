import Kr25Ssmxt.Model.Prelude
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Null measurability of homothetic images

This module records that a nondegenerate centered homothety preserves null measurability
for Lebesgue measure.
-/

namespace Kr25Ssmxt

/--
A nonzero centered homothety sends a null-measurable set to a null-measurable set.

INTERNAL: measurability transport needed by the homothetic-annulus difference formula
-/
lemma homothety_image_nullMeasurable {n : Nat} (S : Set (Point n))
    (c : Point n) (r : Real)
    (hs : MeasureTheory.NullMeasurableSet S MeasureTheory.volume)
    (hr : r ≠ 0) :
    MeasureTheory.NullMeasurableSet
      ((fun x : Point n => c + r • (x - c)) '' S) MeasureTheory.volume := by
  let g : Point n → Point n := fun x => r⁻¹ • (x + -c) + c
  have hg : MeasureTheory.Measure.QuasiMeasurePreserving g MeasureTheory.volume
      MeasureTheory.volume := by
    have hsub : MeasureTheory.Measure.QuasiMeasurePreserving
        (fun x : Point n => x + -c) MeasureTheory.volume MeasureTheory.volume :=
      MeasureTheory.quasiMeasurePreserving_add_right MeasureTheory.volume (-c)
    have hsmul : MeasureTheory.Measure.QuasiMeasurePreserving
        (fun x : Point n => r⁻¹ • x) MeasureTheory.volume MeasureTheory.volume :=
      MeasureTheory.Measure.quasiMeasurePreserving_smul
        MeasureTheory.volume (r := r⁻¹) (inv_ne_zero hr)
    have hadd : MeasureTheory.Measure.QuasiMeasurePreserving
        (fun x : Point n => x + c) MeasureTheory.volume MeasureTheory.volume :=
      MeasureTheory.quasiMeasurePreserving_add_right MeasureTheory.volume c
    simpa [g, Function.comp_def] using hadd.comp (hsmul.comp hsub)
  rw [show (fun x : Point n => c + r • (x - c)) '' S = g ⁻¹' S by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change g (c + r • (y - c)) ∈ S
      convert hy using 1
      ext i
      dsimp [g]
      field_simp [hr]
      ring
    · intro hx
      change g x ∈ S at hx
      refine ⟨g x, hx, ?_⟩
      ext i
      dsimp [g]
      field_simp [hr]
      ring]
  exact hs.preimage hg

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r4 · proved · represented the image as a preimage under the inverse homothety
-/

end Kr25Ssmxt
