import Kr25Ssmxt.Analysis.ManuscriptLabelFreshness
import Kr25Ssmxt.Analysis.ManuscriptMarkingMeasure

/-! The count-vector projection of a labelled manuscript state. This is the
deterministic bridge from the executable state to the fixed-level Poisson
point-count process. -/

namespace Kr25Ssmxt

open Arlib.Probability
open Classical

def TTCState.pointCount {n : Nat} (s : TTCState n)
    (x : LatticePoint n) : Nat := by
  classical
  exact (s.X.filter fun copy => copy.2 = x).card

def TTCState.pointCounts {n : Nat} (s : TTCState n)
    (S : Finset (LatticePoint n)) : S → Nat :=
  fun x => s.pointCount x.1

theorem TTCState.pointCount_removeComponent {n : Nat}
    (s : TTCState n) (P : PolytopeData n) (x : LatticePoint n) :
    (s.removeComponent P).pointCount x =
      if x.toPoint ∈ P.carrier then 0 else s.pointCount x := by
  classical
  by_cases hx : x.toPoint ∈ P.carrier
  · have hfilter :
        ((s.X.filter fun copy => copy.2.toPoint ∉ P.carrier).filter
          fun copy => copy.2 = x) = ∅ := by
      ext copy
      by_cases hc : copy.2 = x <;> simp [hc, hx]
    change ((s.X.filter fun copy => copy.2.toPoint ∉ P.carrier).filter
        fun copy => copy.2 = x).card =
      if x.toPoint ∈ P.carrier then 0 else s.pointCount x
    rw [hfilter, if_pos hx]
    simp
  · have hfilter :
        ((s.X.filter fun copy => copy.2.toPoint ∉ P.carrier).filter
          fun copy => copy.2 = x) =
        (s.X.filter fun copy => copy.2 = x) := by
      ext copy
      by_cases hc : copy.2 = x <;> simp [hc, hx]
    change ((s.X.filter fun copy => copy.2.toPoint ∉ P.carrier).filter
        fun copy => copy.2 = x).card =
      if x.toPoint ∈ P.carrier then 0 else s.pointCount x
    rw [hfilter, if_neg hx]
    rfl

theorem TTCState.pointCount_addBatch {n count : Nat}
    (s : TTCState n) (batch : Fin count → LatticePoint n)
    (x : LatticePoint n) (h : s.LabelsFresh) :
    (s.addBatch batch).pointCount x =
      s.pointCount x + colourCount batch x := by
  classical
  let added : Finset (SampleCopy n) :=
    Finset.univ.image fun i : Fin count => (s.nextLabel + i.val, batch i)
  have hdisjoint : Disjoint s.X added := by
    apply Finset.disjoint_left.mpr
    intro copy hstored hadd
    obtain ⟨i, _, heq⟩ := Finset.mem_image.mp hadd
    have hlt := h.1 copy hstored
    have hlabel := congrArg Prod.fst heq
    dsimp at hlabel
    omega
  have hinj : Function.Injective
      (fun i : Fin count => (s.nextLabel + i.val, batch i)) := by
    intro i j hij
    have hlabel := congrArg Prod.fst hij
    dsimp at hlabel
    exact Fin.ext (Nat.add_left_cancel hlabel)
  have hadded : (added.filter fun copy => copy.2 = x).card =
      colourCount batch x := by
    rw [Finset.filter_image]
    rw [Finset.card_image_of_injective _ hinj]
    rfl
  change ((s.X ∪ added).filter fun copy => copy.2 = x).card =
    (s.X.filter fun copy => copy.2 = x).card + colourCount batch x
  rw [Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisjoint),
    hadded]

theorem TTCState.pointCounts_removeComponent {n : Nat}
    (s : TTCState n) (P : PolytopeData n)
    (S : Finset (LatticePoint n)) :
    (s.removeComponent P).pointCounts S =
      fun x : S => if x.1.toPoint ∈ P.carrier then 0 else s.pointCounts S x := by
  funext x
  exact s.pointCount_removeComponent P x.1

theorem TTCState.pointCounts_addBatch {n count : Nat}
    (s : TTCState n) (batch : Fin count → LatticePoint n)
    (S : Finset (LatticePoint n)) (h : s.LabelsFresh) :
    (s.addBatch batch).pointCounts S =
      fun x : S => s.pointCounts S x + colourCount batch x.1 := by
  funext x
  exact s.pointCount_addBatch batch x.1 h

end Kr25Ssmxt
