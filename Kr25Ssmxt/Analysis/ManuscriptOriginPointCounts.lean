import Kr25Ssmxt.Analysis.ManuscriptOriginHistory

/-! The ghost source invariant identifies executable point counts with the
counts of eligible source copies surviving the current absolute level. -/

namespace Kr25Ssmxt

open Classical

noncomputable def manuscriptOriginSourcePointCounts {n : Nat}
    (valid : Finset (Nat × Nat))
    (marks : Nat × Nat → LatticePoint n)
    (sources : Nat → Nat × Nat → Bool)
    (level : Nat) (S : Finset (LatticePoint n)) : S → Nat :=
  fun x => (valid.filter fun tag =>
    survives (sources tag.1) level tag.2 ∧ marks tag = x.1).card

theorem manuscriptState_pointCounts_eq_originSource
    {n : Nat} (s : TTCState n)
    (origin : Nat → Nat × Nat)
    (valid : Finset (Nat × Nat))
    (marks : Nat × Nat → LatticePoint n)
    (sources : Nat → Nat × Nat → Bool)
    (level processed : Nat) (S : Finset (LatticePoint n))
    (hfresh : s.LabelsFresh)
    (hhistory : ManuscriptOriginHistory s.nextLabel processed origin)
    (hvalid : ManuscriptOriginValid s origin valid)
    (hmarked : ManuscriptOriginMarked s origin marks)
    (hsurvives : ManuscriptOriginSurvives s origin sources level)
    (hcomplete : ManuscriptOriginComplete s origin valid sources level) :
    s.pointCounts S =
      manuscriptOriginSourcePointCounts valid marks sources level S := by
  funext x
  let stateCopies := s.samples.filter fun copy => copy.2 = x.1
  let sourceTags := valid.filter fun tag =>
    survives (sources tag.1) level tag.2 ∧ marks tag = x.1
  have hsets : stateCopies.image (fun copy => origin copy.1) = sourceTags := by
    ext tag
    constructor
    · intro htag
      obtain ⟨copy, hcopy, horigin⟩ := Finset.mem_image.mp htag
      have hstored : copy ∈ s.samples := (Finset.mem_filter.mp hcopy).1
      have hpoint : copy.2 = x.1 := (Finset.mem_filter.mp hcopy).2
      apply Finset.mem_filter.mpr
      constructor
      · rw [← horigin]
        exact hvalid copy hstored
      · constructor
        · rw [← horigin]
          exact hsurvives copy hstored
        · rw [← horigin]
          rw [← hmarked copy hstored]
          exact hpoint
    · intro htag
      have htag' := Finset.mem_filter.mp htag
      obtain ⟨copy, hcopy, horigin⟩ :=
        hcomplete tag htag'.1 htag'.2.1
      apply Finset.mem_image.mpr
      refine ⟨copy, ?_, horigin⟩
      apply Finset.mem_filter.mpr
      refine ⟨hcopy, ?_⟩
      have hpoint := hmarked copy hcopy
      rw [horigin] at hpoint
      exact hpoint.trans htag'.2.2
  have hinj : Set.InjOn (fun copy : SampleCopy n => origin copy.1)
      (stateCopies : Set (SampleCopy n)) := by
    intro a ha b hb hab
    have ha' : a ∈ s.samples :=
      (Finset.mem_filter.mp (show a ∈ stateCopies from ha)).1
    have hb' : b ∈ s.samples :=
      (Finset.mem_filter.mp (show b ∈ stateCopies from hb)).1
    have hlabel : a.1 = b.1 :=
      hhistory.2 a.1 b.1 (hfresh.1 a ha') (hfresh.1 b hb') hab
    exact hfresh.2 a ha' b hb' hlabel
  change stateCopies.card = sourceTags.card
  calc
    stateCopies.card =
      (stateCopies.image fun copy => origin copy.1).card :=
        (Finset.card_image_iff.mpr hinj).symm
    _ = sourceTags.card := by rw [hsets]

end Kr25Ssmxt
