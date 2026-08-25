import Kr25Ssmxt.Model.Prelude
import Mathlib.Topology.Instances.Matrix

/-!
# Regularity of a scaled decomposition union

Finite unions of scaled bounded closed polytopes are null-measurable, bounded, and have
finite Lebesgue measure.  This file records that routine geometric interface separately
from the lattice boundary estimate.
-/

namespace Kr25Ssmxt

open scoped ENNReal

/--
The scaled union of a decomposition is null-measurable, finite-volume, and bounded.

INTERNAL: regularity facts needed to apply the measure symmetric-difference inequality
-/
lemma scaled_union_regular
    {n k : Nat} {F : LRAFormula n k} (D : Decomposition F) (b : Nat) :
    let A := (fun x : Point n => (10 : Real) ^ b • x) '' D.union
    MeasureTheory.NullMeasurableSet A MeasureTheory.volume ∧
      MeasureTheory.volume A ≠ ∞ ∧ Bornology.IsBounded A := by
  dsimp only
  have hcomponentClosed : ∀ i, IsClosed (D.component i).carrier := by
    intro i
    have hcarrier :
        (D.component i).carrier = ⋂ j, {x : Point n |
          dotProduct ((D.component i).presentation.normal j) x ≤
            (D.component i).presentation.offset j} := by
      ext x
      simp [HalfspacePresentation.carrier]
    rw [hcarrier]
    apply isClosed_iInter
    intro j
    exact isClosed_le
      (show Continuous (fun x : Point n =>
        dotProduct ((D.component i).presentation.normal j) x) from
          continuous_const.dotProduct
            (show Continuous (fun x : Point n => x) from continuous_id))
      continuous_const
  have hcomponentCompact : ∀ i, IsCompact (D.component i).carrier := by
    intro i
    exact Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨hcomponentClosed i, (D.component i).bounded⟩
  have hunionCompact : IsCompact D.union := by
    rw [Decomposition.union]
    exact isCompact_iUnion hcomponentCompact
  have hscaledCompact :
      IsCompact ((fun x : Point n => (10 : Real) ^ b • x) '' D.union) :=
    hunionCompact.image (continuous_const_smul ((10 : Real) ^ b))
  exact ⟨hscaledCompact.nullMeasurableSet, hscaledCompact.measure_ne_top,
    hscaledCompact.isBounded⟩

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* current · proved · derived all three regularity facts from compactness of the scaled finite union
-/
