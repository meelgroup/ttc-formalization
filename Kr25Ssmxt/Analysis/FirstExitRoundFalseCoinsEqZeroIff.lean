import Kr25Ssmxt.Analysis.ThinningExitMonoRounds

/-!
# The false-coin first-exit counterexample

With zero pending copies and threshold zero, the everywhere-false stream makes an empty
sample set exit at round zero and every nonempty sample set exit at round one.  In particular,
the zero fiber of `firstExitRound` detects whether the state's sample finset is empty.
-/

namespace Kr25Ssmxt

/--
The zero fiber of `firstExitRound` along the everywhere-false stream is exactly sample
emptiness.

INTERNAL: elementary specialization computing the zero fiber.
-/
lemma firstExitRound_falseCoins_eq_zero_iff (s : TTCState 1) :
    firstExitRound s 0 0 (fun _ => false) = 0 ↔ s.samples = ∅ := by
  rw [firstExitRound, Nat.sInf_eq_zero]
  have hexitOne : thinningExit s 0 0 (fun _ => false) 1 := by
    simp [thinningExit, samplesAfter, pendingAfter, survives]
  simp only [Set.eq_empty_iff_forall_notMem, Set.mem_ofPred_eq]
  rw [or_iff_left]
  · simp [thinningExit, samplesAfter, pendingAfter, survives]
  · push Not
    exact ⟨1, hexitOne⟩

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · computed the zero fiber using exit at rounds zero and one
-/
