import Kr25Ssmxt.Analysis.MeasurableSetSurvives

/-!
# Measurability of finite survivor counts

The number of surviving elements of any fixed finite labelled family is a measurable
natural-valued function of the coin stream.
-/

namespace Kr25Ssmxt

/--
Filtering a fixed finite set by finite-round survival has measurable cardinality.

INTERNAL: Finite counting lemma used for retained and pending thinning copies.
-/
lemma measurable_survivorCount {α : Type*} [DecidableEq α] (I : Finset α)
    (label : α → Nat) (rounds : Nat) :
    Measurable (fun coins : Nat × Nat → Bool =>
      by classical exact (I.filter (fun i => survives coins rounds (label i))).card) := by
  classical
  refine Finset.induction_on I ?_ ?_
  · simpa using (measurable_const :
      Measurable (fun _ : Nat × Nat → Bool => (0 : Nat)))
  · intro a I ha ih
    have hsucc : Measurable (fun coins : Nat × Nat → Bool =>
        (I.filter (fun i => survives coins rounds (label i))).card + 1) :=
      ih.add (measurable_const :
        Measurable (fun _ : Nat × Nat → Bool => (1 : Nat)))
    have hpiece : Measurable (fun coins : Nat × Nat → Bool =>
        if survives coins rounds (label a) then
          (I.filter (fun i => survives coins rounds (label i))).card + 1
        else (I.filter (fun i => survives coins rounds (label i))).card) :=
      @Measurable.ite _ _ _ _ _ _ _ (Classical.decPred _)
        (measurableSet_survives rounds (label a)) hsucc ih
    convert hpiece using 1
    funext coins
    by_cases hsurvives : survives coins rounds (label a)
    · simp [Finset.filter_insert, ha, hsurvives]
    · simp [Finset.filter_insert, ha, hsurvives]

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · finite induction expresses the count as a measurable two-branch update
-/
