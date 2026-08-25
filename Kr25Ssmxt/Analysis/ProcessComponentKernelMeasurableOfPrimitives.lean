import Kr25Ssmxt.Analysis.MeasurablePoissonMeasure
import Kr25Ssmxt.Analysis.MeasurableRemoveComponent
import Kr25Ssmxt.Analysis.MeasurableAddBatch
import Kr25Ssmxt.Analysis.ThinUntilKernelMeasurable
import Kr25Ssmxt.Analysis.MeasurableVolumeProcessTail

/-!
# Assembly of the TTC component kernel

This is the composition step after the primitive state transitions and
parameterized laws have been isolated.
-/

namespace Kr25Ssmxt

/--
The five stages of `processComponent` assemble into a measurable kernel once
the Poisson law, deterministic transitions, and thinning kernel have the
required parameter measurability.

INTERNAL: Giry-bind assembly, including the dependent split over sample counts.
-/
lemma processComponent_kernel_measurable_of_primitives {n k : Nat}
    (O : TTCOracles n k) (b : Nat) (epsilonPrime deltaPrime threshold : Real)
    (P : PolytopeData n)
    (hpoisson : Measurable
      (fun r : NNReal => ProbabilityTheory.poissonMeasure r))
    (hremove : Measurable (fun s : TTCState n => s.removeComponent P))
    (hadd : ∀ count, Measurable
      (fun z : TTCState n × (Fin count → Point n) => z.1.addBatch z.2))
    (hthin : Measurable
      (fun z : TTCState n × Nat => thinUntil z.1 z.2 threshold)) :
    Measurable (fun s =>
      processComponent O b epsilonPrime deltaPrime threshold P s) := by
  simpa only [processComponent] using
    measurable_volume_process_tail O b epsilonPrime deltaPrime threshold P
      hpoisson hremove hadd hthin

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · reduced · closed assembly via fixed-count, Poisson, and volume-bind helpers
* this round · reduced · isolated bind assembly and the dependent sample-count split
-/
