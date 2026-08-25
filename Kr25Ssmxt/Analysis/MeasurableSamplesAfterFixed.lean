import Kr25Ssmxt.Analysis.MeasurableSetSurvives

/-!
# Measurability of fixed-round retained samples

At a fixed thinning round, each membership coordinate of the retained finite set is a
finite survival event.
-/

namespace Kr25Ssmxt

/--
The retained sample Finset after a fixed number of rounds is measurable in the coin stream.

INTERNAL: Fixed-round state-coordinate measurability for thinning.
-/
lemma measurable_samplesAfter_fixed {n : Nat} (rounds : Nat)
    (samples : Finset (SampleCopy n)) :
    Measurable (fun coins : Nat × Nat → Bool => samplesAfter coins rounds samples) := by
  rw [measurable_finset_iff]
  intro a
  apply measurable_to_prop
  have hevent :
      (fun coins : Nat × Nat → Bool => a ∈ samplesAfter coins rounds samples) ⁻¹' {True} =
        {coins | a ∈ samplesAfter coins rounds samples} := by
    ext coins
    simp
  rw [hevent]
  by_cases ha : a ∈ samples
  · simpa [samplesAfter, ha] using measurableSet_survives rounds a.1
  · simp [samplesAfter, ha]

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · reduced Finset measurability to its measurable membership coordinates
-/
