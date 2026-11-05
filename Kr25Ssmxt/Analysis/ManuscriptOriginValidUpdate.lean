import Kr25Ssmxt.Analysis.ManuscriptOriginPointCounts

/-! The ghost source's eligible tags follow the same delete-and-append
recurrence as the manuscript component list. -/

namespace Kr25Ssmxt

open Classical MeasureTheory

noncomputable def manuscriptValidUpdate {n : Nat}
    (valid : Finset (Nat × Nat))
    (marks : Nat × Nat → LatticePoint n) (P : PolytopeData n)
    (component firstLabel basePending : Nat) : Finset (Nat × Nat) :=
  (valid.filter fun tag => (marks tag).toPoint ∉ P.carrier) ∪
    manuscriptSourceTags component firstLabel basePending

theorem manuscriptSourceTags_component
    (component firstLabel basePending : Nat) (tag : Nat × Nat)
    (h : tag ∈ manuscriptSourceTags component firstLabel basePending) :
    tag.1 = component := by
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
  exact congrArg Prod.fst hi.symm

theorem manuscriptValidUpdate_disjoint {n : Nat}
    (valid : Finset (Nat × Nat))
    (marks : Nat × Nat → LatticePoint n) (P : PolytopeData n)
    (component firstLabel basePending : Nat)
    (hbound : ManuscriptValidBound valid component) :
    Disjoint
      (valid.filter fun tag => (marks tag).toPoint ∉ P.carrier)
      (manuscriptSourceTags component firstLabel basePending) := by
  apply Finset.disjoint_left.mpr
  intro tag hold hnew
  have hlt := hbound tag (Finset.mem_filter.mp hold).1
  have heq := manuscriptSourceTags_component component firstLabel
    basePending tag hnew
  omega

theorem manuscriptOriginSourcePointCounts_delete {n : Nat}
    (valid : Finset (Nat × Nat))
    (marks : Nat × Nat → LatticePoint n)
    (sources : Nat → Nat × Nat → Bool)
    (level : Nat) (S : Finset (LatticePoint n))
    (P : PolytopeData n) :
    manuscriptOriginSourcePointCounts
      (valid.filter fun tag => (marks tag).toPoint ∉ P.carrier)
      marks sources level S =
    fun x : S => if x.1.toPoint ∈ P.carrier then 0 else
      manuscriptOriginSourcePointCounts valid marks sources level S x := by
  funext x
  by_cases hx : x.1.toPoint ∈ P.carrier
  · simp only [if_pos hx, manuscriptOriginSourcePointCounts]
    have hempty :
        (valid.filter fun tag => (marks tag).toPoint ∉ P.carrier).filter
          (fun tag => survives (sources tag.1) level tag.2 ∧
            marks tag = x.1) = ∅ := by
      ext tag
      by_cases hmark : marks tag = x.1
      · simp [hmark, hx]
      · simp [hmark]
    rw [hempty]
    rfl
  · simp only [if_neg hx, manuscriptOriginSourcePointCounts]
    congr 1
    ext tag
    by_cases hmark : marks tag = x.1
    · simp [hmark, hx]
    · simp [hmark]

theorem manuscriptOriginSourcePointCounts_newSource {n : Nat}
    (S : Finset (LatticePoint n))
    (marks : Nat × Nat → LatticePoint n)
    (sources : Nat → Nat × Nat → Bool)
    (component firstLabel basePending level preRounds : Nat)
    (preCoins future : Nat × Nat → Bool)
    (tape : Nat → LatticePoint n) :
    manuscriptOriginSourcePointCounts
      (manuscriptSourceTags component firstLabel basePending)
      (manuscriptMarksAppend marks component tape)
      (manuscriptCoinsAppend sources component preCoins future preRounds)
      level S =
    manuscriptPoissonTapePointCounts S firstLabel level
      (basePending, spliceCoins preCoins future preRounds, tape) := by
  funext x
  unfold manuscriptOriginSourcePointCounts manuscriptSourceTags
    manuscriptPoissonTapePointCounts
  rw [Finset.filter_image]
  rw [Finset.card_image_of_injective]
  · congr 1
    ext i
    simp [manuscriptMarksAppend, manuscriptCoinsAppend]
  · intro a b h
    have hlabel := congrArg Prod.snd h
    exact Nat.add_left_cancel hlabel

theorem manuscriptOriginSourcePointCounts_oldSource_unchanged {n : Nat}
    (valid : Finset (Nat × Nat))
    (marks : Nat × Nat → LatticePoint n)
    (sources : Nat → Nat × Nat → Bool)
    (component firstLabel preRounds level : Nat)
    (preCoins future : Nat × Nat → Bool)
    (tape : Nat → LatticePoint n)
    (P : PolytopeData n) (S : Finset (LatticePoint n))
    (hbound : ManuscriptValidBound valid component) :
    manuscriptOriginSourcePointCounts
      (valid.filter fun tag => (marks tag).toPoint ∉ P.carrier)
      (manuscriptMarksAppend marks component tape)
      (manuscriptCoinsAppend sources component preCoins future preRounds)
      level S =
    manuscriptOriginSourcePointCounts
      (valid.filter fun tag => (marks tag).toPoint ∉ P.carrier)
      marks sources level S := by
  funext x
  unfold manuscriptOriginSourcePointCounts
  congr 1
  ext tag
  by_cases htag : tag ∈ valid.filter (fun tag =>
      (marks tag).toPoint ∉ P.carrier)
  · have hlt := hbound tag (Finset.mem_filter.mp htag).1
    simp only [Finset.mem_filter, htag, true_and]
    rw [manuscriptMarksAppend_old marks component tape tag hlt,
      manuscriptCoinsAppend_old sources component tag.1 preCoins future
        preRounds hlt]
  · simp [htag]

/-- Eligible source counts obey the manuscript's fixed-level
delete-and-append recurrence. -/
theorem manuscriptOriginSourcePointCounts_update {n : Nat}
    (valid : Finset (Nat × Nat))
    (marks : Nat × Nat → LatticePoint n)
    (sources : Nat → Nat × Nat → Bool)
    (component firstLabel basePending preRounds level : Nat)
    (preCoins future : Nat × Nat → Bool)
    (tape : Nat → LatticePoint n)
    (P : PolytopeData n) (S : Finset (LatticePoint n))
    (hbound : ManuscriptValidBound valid component) :
    manuscriptOriginSourcePointCounts
      (manuscriptValidUpdate valid marks P component firstLabel basePending)
      (manuscriptMarksAppend marks component tape)
      (manuscriptCoinsAppend sources component preCoins future preRounds)
      level S =
    fun x : S =>
      (if x.1.toPoint ∈ P.carrier then 0 else
        manuscriptOriginSourcePointCounts valid marks sources level S x) +
      manuscriptPoissonTapePointCounts S firstLabel level
        (basePending, spliceCoins preCoins future preRounds, tape) x := by
  funext x
  let oldTags := valid.filter fun tag => (marks tag).toPoint ∉ P.carrier
  let newTags := manuscriptSourceTags component firstLabel basePending
  let marksNew := manuscriptMarksAppend marks component tape
  let coinsNew := manuscriptCoinsAppend sources component preCoins future preRounds
  let pred : Nat × Nat → Prop := fun tag =>
    survives (coinsNew tag.1) level tag.2 ∧ marksNew tag = x.1
  have hdisj : Disjoint oldTags newTags :=
    manuscriptValidUpdate_disjoint valid marks P component firstLabel
      basePending hbound
  have hsplit : manuscriptOriginSourcePointCounts
      (oldTags ∪ newTags) marksNew coinsNew level S x =
      manuscriptOriginSourcePointCounts oldTags marksNew coinsNew level S x +
        manuscriptOriginSourcePointCounts newTags marksNew coinsNew level S x := by
    change ((oldTags ∪ newTags).filter pred).card =
      (oldTags.filter pred).card + (newTags.filter pred).card
    rw [Finset.filter_union]
    exact Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter hdisj)
  have hold := manuscriptOriginSourcePointCounts_oldSource_unchanged
    valid marks sources component firstLabel preRounds level preCoins future
    tape P S hbound
  have hdelete := manuscriptOriginSourcePointCounts_delete valid marks
    sources level S P
  have hnew := manuscriptOriginSourcePointCounts_newSource S marks sources
    component firstLabel basePending level preRounds preCoins future tape
  change manuscriptOriginSourcePointCounts (oldTags ∪ newTags)
    marksNew coinsNew level S x = _
  rw [hsplit]
  change manuscriptOriginSourcePointCounts oldTags marksNew coinsNew
      level S x + manuscriptOriginSourcePointCounts newTags marksNew coinsNew
      level S x = _
  rw [show manuscriptOriginSourcePointCounts oldTags marksNew coinsNew
      level S x = manuscriptOriginSourcePointCounts oldTags marks sources
      level S x from congrFun hold x]
  rw [show manuscriptOriginSourcePointCounts oldTags marks sources level S x =
      (if x.1.toPoint ∈ P.carrier then 0 else
        manuscriptOriginSourcePointCounts valid marks sources level S x) from
      congrFun hdelete x]
  exact congrArg (fun z =>
    (if x.1.toPoint ∈ P.carrier then 0 else
      manuscriptOriginSourcePointCounts valid marks sources level S x) + z)
    (congrFun hnew x)

end Kr25Ssmxt
