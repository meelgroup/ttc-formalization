import Kr25Ssmxt.Analysis.ThinningExitMonoRounds

/-!
# The false-coin first-exit counterexample

With zero pending copies and threshold zero, the everywhere-false stream makes an empty
sample set exit at round zero and every nonempty sample set exit at round one.  In particular,
the zero fiber of `ttcPseudocode.secondLoopExitRound` detects whether the state's sample finset is empty.
-/

namespace Kr25Ssmxt

/--
The zero fiber of `ttcPseudocode.secondLoopExitRound` along the everywhere-false stream is exactly sample
emptiness.

INTERNAL: elementary specialization computing the zero fiber.
-/
lemma firstExitRound_falseCoins_eq_zero_iff (s : TTCState 1) :
    ttcPseudocode.secondLoopExitRound s 0 0 (fun _ => false) = 0 ↔ s.X = ∅ := by
  rw [ttcPseudocode.secondLoopExitRound, Nat.sInf_eq_zero]
  have hexitOne : ttcPseudocode.secondLoopExit s 0 0 (fun _ => false) 1 := by
    simp [ttcPseudocode.secondLoopExit, samplesAfter, pendingAfter, survives]
  simp only [Set.eq_empty_iff_forall_notMem, Set.mem_ofPred_eq]
  rw [or_iff_left]
  · simp [ttcPseudocode.secondLoopExit, samplesAfter, pendingAfter, survives]
  · push Not
    exact ⟨1, hexitOne⟩

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · computed the zero fiber using exit at rounds zero and one
-/
