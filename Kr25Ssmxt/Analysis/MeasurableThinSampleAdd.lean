import Kr25Ssmxt.Analysis.MeasurableSampleAddByCount
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Thinning followed by the sampling tail

This module composes the first thinning kernel with the count-indexed final
sampling, insertion, and thinning kernel.
-/

namespace Kr25Ssmxt

/--
The two final stages following the Poisson draw form a measurable kernel in the
state and pending-count pair.

INTERNAL: ordinary Giry composition after count-indexed tail measurability.
-/
lemma measurable_thin_sample_add {n k : Nat} (O : TTCOracles n k) (b : Nat)
    (epsilonPrime deltaPrime threshold : Real) (P : PolytopeData n)
    (hadd : ∀ count, Measurable
      (fun z : TTCState n × (Fin count → LatticePoint n) => z.1.addBatch z.2))
    (hthin : Measurable
      (fun z : TTCState n × Nat => thinUntil z.1 z.2 threshold)) :
    Measurable (fun z : TTCState n × Nat =>
      (thinUntil z.1 z.2 threshold).bind fun thinned =>
        (O.generateSamples P thinned.2 b epsilonPrime deltaPrime).bind fun batch =>
          (thinUntil (thinned.1.addBatch batch.2) 0 threshold).map Prod.fst) := by
  have htail := measurable_sample_add_by_count O b epsilonPrime deltaPrime threshold P
    hadd hthin
  exact (MeasureTheory.Measure.measurable_bind' htail).comp hthin

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · composed the first thinning kernel with the count-indexed tail
-/
