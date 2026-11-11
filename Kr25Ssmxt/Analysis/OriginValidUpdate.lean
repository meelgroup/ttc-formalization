import Kr25Ssmxt.Analysis.OriginPointCounts

/-! The ghost source's eligible tags follow the same delete-and-append
recurrence as the paper component list. -/

namespace Kr25Ssmxt

open Classical MeasureTheory

noncomputable def validUpdate {n : Nat}
    (valid : Finset (Nat × Nat))
    (marks : Nat × Nat → LatticePoint n) (P : PolytopeData n)
    (component firstLabel basePending : Nat) : Finset (Nat × Nat) :=
  (valid.filter fun tag => (marks tag).toPoint ∉ P.carrier) ∪
    originSourceTags component firstLabel basePending

theorem sourceTags_component
    (component firstLabel basePending : Nat) (tag : Nat × Nat)
    (h : tag ∈ originSourceTags component firstLabel basePending) :
    tag.1 = component := by
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
  exact congrArg Prod.fst hi.symm

theorem validUpdate_disjoint {n : Nat}
    (valid : Finset (Nat × Nat))
    (marks : Nat × Nat → LatticePoint n) (P : PolytopeData n)
    (component firstLabel basePending : Nat)
    (hbound : ValidBound valid component) :
    Disjoint
      (valid.filter fun tag => (marks tag).toPoint ∉ P.carrier)
      (originSourceTags component firstLabel basePending) := by
  apply Finset.disjoint_left.mpr
  intro tag hold hnew
  have hlt := hbound tag (Finset.mem_filter.mp hold).1
  have heq := sourceTags_component component firstLabel
    basePending tag hnew
  omega

theorem originSourcePointCounts_delete {n : Nat}
    (valid : Finset (Nat × Nat))
    (marks : Nat × Nat → LatticePoint n)
    (sources : Nat → Nat × Nat → Bool)
    (level : Nat) (S : Finset (LatticePoint n))
    (P : PolytopeData n) :
    originSourcePointCounts
      (valid.filter fun tag => (marks tag).toPoint ∉ P.carrier)
      marks sources level S =
    fun x : S => if x.1.toPoint ∈ P.carrier then 0 else
      originSourcePointCounts valid marks sources level S x := by
  funext x
  by_cases hx : x.1.toPoint ∈ P.carrier
  · simp only [if_pos hx, originSourcePointCounts]
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
  · simp only [if_neg hx, originSourcePointCounts]
    congr 1
    ext tag
    by_cases hmark : marks tag = x.1
    · simp [hmark, hx]
    · simp [hmark]

theorem originSourcePointCounts_newSource {n : Nat}
    (S : Finset (LatticePoint n))
    (marks : Nat × Nat → LatticePoint n)
    (sources : Nat → Nat × Nat → Bool)
    (component firstLabel basePending level preRounds : Nat)
    (preCoins future : Nat × Nat → Bool)
    (tape : Nat → LatticePoint n) :
    originSourcePointCounts
      (originSourceTags component firstLabel basePending)
      (marksAppend marks component tape)
      (coinsAppend sources component preCoins future preRounds)
      level S =
    poissonTapePointCounts S firstLabel level
      (basePending, spliceCoins preCoins future preRounds, tape) := by
  funext x
  unfold originSourcePointCounts originSourceTags
    poissonTapePointCounts
  rw [Finset.filter_image]
  rw [Finset.card_image_of_injective]
  · congr 1
    ext i
    simp [marksAppend, coinsAppend]
  · intro a b h
    have hlabel := congrArg Prod.snd h
    exact Nat.add_left_cancel hlabel

theorem originSourcePointCounts_oldSource_unchanged {n : Nat}
    (valid : Finset (Nat × Nat))
    (marks : Nat × Nat → LatticePoint n)
    (sources : Nat → Nat × Nat → Bool)
    (component firstLabel preRounds level : Nat)
    (preCoins future : Nat × Nat → Bool)
    (tape : Nat → LatticePoint n)
    (P : PolytopeData n) (S : Finset (LatticePoint n))
    (hbound : ValidBound valid component) :
    originSourcePointCounts
      (valid.filter fun tag => (marks tag).toPoint ∉ P.carrier)
      (marksAppend marks component tape)
      (coinsAppend sources component preCoins future preRounds)
      level S =
    originSourcePointCounts
      (valid.filter fun tag => (marks tag).toPoint ∉ P.carrier)
      marks sources level S := by
  funext x
  unfold originSourcePointCounts
  congr 1
  ext tag
  by_cases htag : tag ∈ valid.filter (fun tag =>
      (marks tag).toPoint ∉ P.carrier)
  · have hlt := hbound tag (Finset.mem_filter.mp htag).1
    simp only [Finset.mem_filter, htag, true_and]
    rw [marksAppend_old marks component tape tag hlt,
      coinsAppend_old sources component tag.1 preCoins future
        preRounds hlt]
  · simp [htag]

/-- Eligible source counts obey the paper's fixed-level
delete-and-append recurrence. -/
theorem originSourcePointCounts_update {n : Nat}
    (valid : Finset (Nat × Nat))
    (marks : Nat × Nat → LatticePoint n)
    (sources : Nat → Nat × Nat → Bool)
    (component firstLabel basePending preRounds level : Nat)
    (preCoins future : Nat × Nat → Bool)
    (tape : Nat → LatticePoint n)
    (P : PolytopeData n) (S : Finset (LatticePoint n))
    (hbound : ValidBound valid component) :
    originSourcePointCounts
      (validUpdate valid marks P component firstLabel basePending)
      (marksAppend marks component tape)
      (coinsAppend sources component preCoins future preRounds)
      level S =
    fun x : S =>
      (if x.1.toPoint ∈ P.carrier then 0 else
        originSourcePointCounts valid marks sources level S x) +
      poissonTapePointCounts S firstLabel level
        (basePending, spliceCoins preCoins future preRounds, tape) x := by
  funext x
  let oldTags := valid.filter fun tag => (marks tag).toPoint ∉ P.carrier
  let newTags := originSourceTags component firstLabel basePending
  let marksNew := marksAppend marks component tape
  let coinsNew := coinsAppend sources component preCoins future preRounds
  let pred : Nat × Nat → Prop := fun tag =>
    survives (coinsNew tag.1) level tag.2 ∧ marksNew tag = x.1
  have hdisj : Disjoint oldTags newTags :=
    validUpdate_disjoint valid marks P component firstLabel
      basePending hbound
  have hsplit : originSourcePointCounts
      (oldTags ∪ newTags) marksNew coinsNew level S x =
      originSourcePointCounts oldTags marksNew coinsNew level S x +
        originSourcePointCounts newTags marksNew coinsNew level S x := by
    change ((oldTags ∪ newTags).filter pred).card =
      (oldTags.filter pred).card + (newTags.filter pred).card
    rw [Finset.filter_union]
    exact Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter hdisj)
  have hold := originSourcePointCounts_oldSource_unchanged
    valid marks sources component firstLabel preRounds level preCoins future
    tape P S hbound
  have hdelete := originSourcePointCounts_delete valid marks
    sources level S P
  have hnew := originSourcePointCounts_newSource S marks sources
    component firstLabel basePending level preRounds preCoins future tape
  change originSourcePointCounts (oldTags ∪ newTags)
    marksNew coinsNew level S x = _
  rw [hsplit]
  change originSourcePointCounts oldTags marksNew coinsNew
      level S x + originSourcePointCounts newTags marksNew coinsNew
      level S x = _
  rw [show originSourcePointCounts oldTags marksNew coinsNew
      level S x = originSourcePointCounts oldTags marks sources
      level S x from congrFun hold x]
  rw [show originSourcePointCounts oldTags marks sources level S x =
      (if x.1.toPoint ∈ P.carrier then 0 else
        originSourcePointCounts valid marks sources level S x) from
      congrFun hdelete x]
  exact congrArg (fun z =>
    (if x.1.toPoint ∈ P.carrier then 0 else
      originSourcePointCounts valid marks sources level S x) + z)
    (congrFun hnew x)

end Kr25Ssmxt
