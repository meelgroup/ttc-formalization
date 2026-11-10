import Kr25Ssmxt.Analysis.MeasurableFirstExitRound
import Kr25Ssmxt.Analysis.MeasurableSamplesAfterFixed
import Kr25Ssmxt.Analysis.MeasurableSurvivorCount

/-!
# Measurability of TTC thinning

The first-exit thinning result is measurable as a function of its infinite Boolean coin
stream.  The proof must expose the measurable fibers of the least exit round.
-/

namespace Kr25Ssmxt

/--
For fixed input state and loop parameters, the result of coupled thinning is measurable in
the coin stream.

INTERNAL: Giry-monad bookkeeping for the paper's unbounded thinning loop.
-/
lemma measurable_thinningResult {n : Nat} (s : TTCState n) (pending : Nat)
    (threshold : Real) : Measurable (thinningResult s pending threshold) := by
  let exitRound := firstExitRound s pending threshold
  have hexitRound : Measurable exitRound :=
    measurable_firstExitRound s pending threshold
  have hcoinsRound : Measurable (fun coins : Nat × Nat → Bool =>
      (coins, exitRound coins)) :=
    measurable_id.prodMk hexitRound
  have hsamplesJoint : Measurable (fun p : (Nat × Nat → Bool) × Nat =>
      samplesAfter p.1 p.2 s.X) :=
    measurable_from_prod_countable_left fun rounds =>
      measurable_samplesAfter_fixed rounds s.X
  have hsamples : Measurable (fun coins : Nat × Nat → Bool =>
      samplesAfter coins (exitRound coins) s.X) :=
    hsamplesJoint.comp hcoinsRound
  have hpendingFixed : ∀ rounds, Measurable (fun coins : Nat × Nat → Bool =>
      pendingAfter coins rounds s.nextLabel pending) := by
    intro rounds
    simpa [pendingAfter] using
      (measurable_survivorCount (Finset.range pending)
        (fun i => s.nextLabel + i) rounds)
  have hpendingJoint : Measurable (fun p : (Nat × Nat → Bool) × Nat =>
      pendingAfter p.1 p.2 s.nextLabel pending) :=
    measurable_from_prod_countable_left hpendingFixed
  have hpending : Measurable (fun coins : Nat × Nat → Bool =>
      pendingAfter coins (exitRound coins) s.nextLabel pending) :=
    hpendingJoint.comp hcoinsRound
  have hrate : Measurable (fun coins : Nat × Nat → Bool =>
      s.p / (2 : NNReal) ^ exitRound coins) :=
    (measurable_of_countable
      (fun rounds : Nat => s.p / (2 : NNReal) ^ rounds)).comp hexitRound
  have hstate : Measurable (fun coins : Nat × Nat → Bool =>
      { p := s.p / (2 : NNReal) ^ exitRound coins
        X := samplesAfter coins (exitRound coins) s.X
        nextLabel := s.nextLabel : TTCState n }) := by
    rw [measurable_comap_iff]
    exact hrate.prodMk (hsamples.prodMk measurable_const)
  change Measurable (fun coins : Nat × Nat → Bool =>
    ({ p := s.p / (2 : NNReal) ^ exitRound coins
       X := samplesAfter coins (exitRound coins) s.X
       nextLabel := s.nextLabel : TTCState n },
     pendingAfter coins (exitRound coins) s.nextLabel pending))
  exact hstate.prodMk hpending

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · assembled measurable variable-round state and pending coordinates
-/
