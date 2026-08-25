import Kr25Ssmxt.Analysis.MeasurableSurvivorCount

/-!
# Measurability of fixed-round thinning exits

At a fixed round, the loop guard is a comparison involving two measurable finite survivor
counts.
-/

namespace Kr25Ssmxt

/--
The event that thinning has exited at a fixed round is measurable.

INTERNAL: Measurable fixed-round pieces for the first-exit construction.
-/
lemma measurableSet_thinningExit {n : Nat} (s : TTCState n) (pending : Nat)
    (threshold : Real) (rounds : Nat) :
    MeasurableSet {coins : Nat × Nat → Bool |
      thinningExit s pending threshold coins rounds} := by
  have hsamples : Measurable (fun coins : Nat × Nat → Bool =>
      (samplesAfter coins rounds s.samples).card) := by
    simpa [samplesAfter] using
      (measurable_survivorCount s.samples (fun copy => copy.1) rounds)
  have hpending : Measurable (fun coins : Nat × Nat → Bool =>
      pendingAfter coins rounds s.nextLabel pending) := by
    simpa [pendingAfter] using
      (measurable_survivorCount (Finset.range pending)
        (fun i => s.nextLabel + i) rounds)
  have htotal : Measurable (fun coins : Nat × Nat → Bool =>
      (samplesAfter coins rounds s.samples).card +
        pendingAfter coins rounds s.nextLabel pending) :=
    hsamples.add hpending
  have hreal : Measurable ((fun coins : Nat × Nat → Bool =>
      ((samplesAfter coins rounds s.samples).card +
        pendingAfter coins rounds s.nextLabel pending : Nat)) :
      (Nat × Nat → Bool) → Real) :=
    (measurable_of_countable (fun q : Nat => (q : Real))).comp htotal
  convert hreal (measurableSet_Iic : MeasurableSet (Set.Iic threshold)) using 1
  ext coins
  simp [thinningExit]

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · combined measurable retained and pending counts with the real threshold guard
-/
