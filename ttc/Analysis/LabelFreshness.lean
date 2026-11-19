import ttc.Analysis.ThinningCosts

/-! Fresh labels make the fair thinning coins for distinct stored copies
independent. The invariant is deterministic and holds throughout the
paper program. -/

namespace ttc

open Classical

/-- All stored labels precede the next unused label, and no two stored copies
share a label. -/
def TTCState.LabelsFresh {n : Nat} (s : TTCState n) : Prop :=
  (∀ c ∈ s.X, c.1 < s.nextLabel) ∧
    (∀ c ∈ s.X, ∀ d ∈ s.X, c.1 = d.1 → c = d)

theorem TTCState.initial_labelsFresh (n : Nat) :
    (TTCState.unitInitial n).LabelsFresh := by
  simp [TTCState.LabelsFresh, TTCState.unitInitial]

theorem TTCState.labelsFresh_removeComponent {n : Nat}
    (s : TTCState n) (P : PolytopeData n) (h : s.LabelsFresh) :
    (s.removeComponent P).LabelsFresh := by
  classical
  unfold TTCState.LabelsFresh at h ⊢
  constructor
  · intro c hc
    exact h.1 c (Finset.mem_filter.mp hc).1
  · intro c hc d hd heq
    exact h.2 c (Finset.mem_filter.mp hc).1 d
      (Finset.mem_filter.mp hd).1 heq

theorem TTCState.labelsFresh_addBatch {n count : Nat}
    (s : TTCState n) (points : Fin count → LatticePoint n)
    (h : s.LabelsFresh) : (s.addBatch points).LabelsFresh := by
  classical
  let added : Finset (SampleCopy n) :=
    Finset.univ.image (fun i : Fin count => (s.nextLabel + i.val, points i))
  have hadded (c : SampleCopy n) (hc : c ∈ added) :
      ∃ i : Fin count, c = (s.nextLabel + i.val, points i) := by
    rcases Finset.mem_image.mp hc with ⟨i, _, rfl⟩
    exact ⟨i, rfl⟩
  change (∀ c ∈ s.X ∪ added, c.1 < s.nextLabel + count) ∧
    (∀ c ∈ s.X ∪ added, ∀ d ∈ s.X ∪ added,
      c.1 = d.1 → c = d)
  constructor
  · intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · exact (h.1 c hc).trans_le (Nat.le_add_right _ _)
    · obtain ⟨i, rfl⟩ := hadded c hc
      exact Nat.add_lt_add_left i.isLt _
  · intro c hc d hd heq
    rcases Finset.mem_union.mp hc with hc | hc <;>
      rcases Finset.mem_union.mp hd with hd | hd
    · exact h.2 c hc d hd heq
    · obtain ⟨j, rfl⟩ := hadded d hd
      have hlt := h.1 c hc
      omega
    · obtain ⟨i, rfl⟩ := hadded c hc
      have hlt := h.1 d hd
      omega
    · obtain ⟨i, rfl⟩ := hadded c hc
      obtain ⟨j, rfl⟩ := hadded d hd
      have hij : i = j := Fin.ext (Nat.add_left_cancel heq)
      subst hij
      rfl

theorem TTCState.labelsFresh_samplesAfter {n : Nat}
    (s : TTCState n) (coins : Nat × Nat → Bool) (rounds : Nat)
    (h : s.LabelsFresh) :
    ({s with X := samplesAfter coins rounds s.X}).LabelsFresh := by
  classical
  unfold TTCState.LabelsFresh at h ⊢
  constructor
  · intro c hc
    exact h.1 c (Finset.mem_filter.mp hc).1
  · intro c hc d hd heq
    exact h.2 c (Finset.mem_filter.mp hc).1 d
      (Finset.mem_filter.mp hd).1 heq

theorem rateThinningResult_labelsFresh {n : Nat}
    (s : TTCState n) (intensity : NNReal) (threshold : Real)
    (coins : Nat × Nat → Bool) (h : s.LabelsFresh) :
    (ttcReference.firstLoopResult s intensity threshold coins).LabelsFresh := by
  exact s.labelsFresh_samplesAfter coins
    (ttcReference.firstLoopExit s intensity threshold) h

theorem thinningResult_labelsFresh {n : Nat}
    (s : TTCState n) (pending : Nat) (threshold : Real)
    (coins : Nat × Nat → Bool) (h : s.LabelsFresh) :
    (ttcPseudocode.secondLoopResult s pending threshold coins).1.LabelsFresh := by
  exact s.labelsFresh_samplesAfter coins
    (ttcPseudocode.secondLoopExitRound s pending threshold coins) h

/-- Labels of stored and pending copies are disjoint; the union has exactly
the expected number of copies. -/
theorem TTCState.populationLabels_card {n : Nat} (s : TTCState n)
    (pending : Nat) (h : s.LabelsFresh) :
    ((s.X.image Prod.fst) ∪
      ((Finset.range pending).image (fun i => s.nextLabel + i))).card =
      s.X.card + pending := by
  classical
  have hstored : (s.X.image Prod.fst).card = s.X.card := by
    apply Finset.card_image_of_injOn
    intro c hc d hd heq
    exact h.2 c hc d hd heq
  have hpending : ((Finset.range pending).image
      (fun i => s.nextLabel + i)).card = pending := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro a b hab
      exact Nat.add_left_cancel hab
  have hdisjoint : Disjoint (s.X.image Prod.fst)
      ((Finset.range pending).image (fun i => s.nextLabel + i)) := by
    apply Finset.disjoint_left.mpr
    intro label hstoredLabel hpendingLabel
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hstoredLabel
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hpendingLabel
    have hlt := h.1 c hc
    omega
  rw [Finset.card_union_of_disjoint hdisjoint, hstored, hpending]

/-- The fixed-round second-loop population is the survivor count of one
finite set of distinct labels. -/
theorem TTCState.thinningPopulation_eq_filter_labels {n : Nat}
    (s : TTCState n) (pending rounds : Nat)
    (coins : Nat × Nat → Bool) (h : s.LabelsFresh) :
    (samplesAfter coins rounds s.X).card +
        pendingAfter coins rounds s.nextLabel pending =
      (((s.X.image Prod.fst) ∪
        ((Finset.range pending).image (fun i => s.nextLabel + i))).filter
          (fun label => survives coins rounds label)).card := by
  classical
  have hstored : ((s.X.image Prod.fst).filter
      (fun label => survives coins rounds label)).card =
      (samplesAfter coins rounds s.X).card := by
    have hset : (s.X.image Prod.fst).filter
        (fun label => survives coins rounds label) =
        (samplesAfter coins rounds s.X).image Prod.fst := by
      ext label
      simp [samplesAfter, and_comm]
    rw [hset]
    apply Finset.card_image_of_injOn
    intro c hc d hd heq
    exact h.2 c (Finset.mem_filter.mp hc).1 d
      (Finset.mem_filter.mp hd).1 heq
  have hpending : (((Finset.range pending).image
      (fun i => s.nextLabel + i)).filter
      (fun label => survives coins rounds label)).card =
      pendingAfter coins rounds s.nextLabel pending := by
    have hset : ((Finset.range pending).image
        (fun i => s.nextLabel + i)).filter
        (fun label => survives coins rounds label) =
        ((Finset.range pending).filter
          (fun i => survives coins rounds (s.nextLabel + i))).image
            (fun i => s.nextLabel + i) := by
      ext label
      simp [Finset.mem_filter, Finset.mem_image]
      aesop
    rw [hset]
    rw [Finset.card_image_of_injective]
    · rfl
    · intro a b hab
      exact Nat.add_left_cancel hab
  have hdisjoint : Disjoint (s.X.image Prod.fst)
      ((Finset.range pending).image (fun i => s.nextLabel + i)) := by
    apply Finset.disjoint_left.mpr
    intro label hstoredLabel hpendingLabel
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hstoredLabel
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hpendingLabel
    have hlt := h.1 c hc
    omega
  rw [Finset.filter_union,
    Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter hdisjoint), hstored, hpending]

end ttc
