import Kr25Ssmxt.Model.Program

/-!
# Monotonicity of thinning exits

Survivor counts decrease with the number of rounds, so once the thinning guard has exited
it remains exited at every later round.
-/

namespace Kr25Ssmxt

/--
The fixed-stream thinning-exit predicate is upward closed in the round number.

INTERNAL: Order property needed to identify successor fibers of the least exit round.
-/
lemma thinningExit_mono_rounds {n : Nat} (s : TTCState n) (pending : Nat)
    (threshold : Real) (coins : Nat × Nat → Bool) {r₁ r₂ : Nat} (hr : r₁ ≤ r₂) :
    thinningExit s pending threshold coins r₁ →
      thinningExit s pending threshold coins r₂ := by
  classical
  intro hexit
  have hsurvives : ∀ label,
      survives coins r₂ label → survives coins r₁ label := by
    intro label hsurvives r hlt
    exact hsurvives r (lt_of_lt_of_le hlt hr)
  have hsamplesSubset :
      samplesAfter coins r₂ s.samples ⊆ samplesAfter coins r₁ s.samples := by
    intro copy hcopy
    simp only [samplesAfter, Finset.mem_filter] at hcopy ⊢
    exact ⟨hcopy.1, hsurvives copy.1 hcopy.2⟩
  have hpendingSubset :
      (Finset.range pending).filter
          (fun i => survives coins r₂ (s.nextLabel + i)) ⊆
        (Finset.range pending).filter
          (fun i => survives coins r₁ (s.nextLabel + i)) := by
    intro i hi
    simp only [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hsurvives (s.nextLabel + i) hi.2⟩
  have hsamplesCard :
      (samplesAfter coins r₂ s.samples).card ≤
        (samplesAfter coins r₁ s.samples).card :=
    Finset.card_le_card hsamplesSubset
  have hpendingCard :
      pendingAfter coins r₂ s.nextLabel pending ≤
        pendingAfter coins r₁ s.nextLabel pending := by
    simpa only [pendingAfter] using Finset.card_le_card hpendingSubset
  apply (add_le_add (Nat.cast_le.mpr hsamplesCard)
    (Nat.cast_le.mpr hpendingCard)).trans
  exact hexit

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · later-round survivor Finsets are subsets of their earlier-round counterparts
-/
