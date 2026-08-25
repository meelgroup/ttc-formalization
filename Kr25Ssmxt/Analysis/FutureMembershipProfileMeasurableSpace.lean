import Kr25Ssmxt.Analysis.FutureMembershipProfile

/-!
# Discrete measurable structure for future-membership profiles

Future-membership profiles form a countable type.  We equip them with the discrete measurable
structure so that their fibers are measurable once a profile observable is known to be
almost-everywhere measurable.
-/

namespace Kr25Ssmxt

/--
The countable execution-profile type carries its discrete measurable structure.

INTERNAL: codomain measurable structure for stratifying state laws by discrete profiles.
-/
instance futureMembershipProfileMeasurableSpace :
    MeasurableSpace (Multiset (Nat × List Bool)) := ⊤

/-- Exact future-membership profiles are measurable for the coded lattice sample state. -/
lemma futureMembershipProfile_measurable {n : Nat} (Qs : List (PolytopeData n)) :
    Measurable (futureMembershipProfile Qs : TTCState n → Multiset (Nat × List Bool)) := by
  classical
  have hsamples : Measurable (fun s : TTCState n => s.samples) :=
    (measurable_fst.comp measurable_snd).comp
      (comap_measurable (fun s : TTCState n => (s.rate, s.samples, s.nextLabel)))
  change Measurable (fun s : TTCState n => s.samples.1.map fun copy =>
    (copy.1, Qs.map fun Q => decide (copy.2.toPoint ∈ Q.carrier)))
  exact (measurable_of_countable (fun samples : Finset (SampleCopy n) =>
    samples.1.map fun copy =>
      (copy.1, Qs.map fun Q => decide (copy.2.toPoint ∈ Q.carrier)))).comp hsamples

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · exact profiles are globally measurable for coded lattice samples
* previous round · defined · supplied the discrete measurable structure on the profile type
-/
