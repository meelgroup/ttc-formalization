import Kr25Ssmxt.Analysis.MeasurableFirstExitRound
import Kr25Ssmxt.Analysis.MeasurableFirstExitRoundJointFalse

/-!
# Joint measurability of the first TTC thinning-exit round

This statement is false under the current measurable-space instance on `TTCState`.  At
dimension one and threshold zero, restriction to the everywhere-false coin stream makes the
zero fiber of the claimed map equal to sample-finset emptiness.  That event is not measurable
for Mathlib's membership-generated measurable space on `Finset (SampleCopy 1)`.

The algorithm needs a redesigned state measurable space exposing countable label multiplicities,
or a reachable-state formulation under laws supported on countable sample sets.  Merely changing
this lemma's proof cannot repair the obstruction.
-/

namespace Kr25Ssmxt

/--
For a fixed threshold, the first thinning-exit round is jointly measurable in the state,
pending count, and coin stream.

INTERNAL: countable-control measurability for the unbounded thinning loop.
-/
lemma measurable_firstExitRound_joint {n : Nat} (threshold : Real) :
    Measurable (fun z : (TTCState n × Nat) × (Nat × Nat → Bool) =>
      firstExitRound z.1.1 z.1.2 threshold z.2) := by
  -- DISPROVED: not_measurable_firstExitRound_joint_zero
  -- REPAIR: (hexit : ∀ rounds, MeasurableSet {z : (TTCState n × Nat) × (Nat × Nat → Bool) | thinningExit z.1.1 z.1.2 threshold z.2 rounds})
  sorry

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · disproved · `not_measurable_firstExitRound_joint_zero`, false-coin zero fiber is sample emptiness
* this round · open · `Finset` label multiplicities lack a measurable map over uncountable sample points
-/
