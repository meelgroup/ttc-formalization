import Kr25Ssmxt.Analysis.ProcessComponentKernelMeasurableOfPrimitives

/-!
# Measurability of one TTC component kernel

The adaptive composition of volume, Poisson, thinning, and sample laws is measurable in its
incoming state.
-/

namespace Kr25Ssmxt

/--
For fixed algorithm data, processing one component is a measurable measure-valued kernel in
the incoming TTC state.

INTERNAL: Giry-monad bookkeeping for sequential composition of TTC components.
-/
lemma processComponent_kernel_measurable {n k : Nat} (O : TTCOracles n k) (b : Nat)
    (epsilonPrime deltaPrime threshold : Real) (P : PolytopeData n) :
    Measurable (fun s => processComponent O b epsilonPrime deltaPrime threshold P s) := by
  exact processComponent_kernel_measurable_of_primitives O b epsilonPrime deltaPrime
    threshold P measurable_poissonMeasure (measurable_removeComponent P)
    (fun _ => measurable_addBatch) (thinUntil_kernel_measurable threshold)

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · reduced · closed the headline from six isolated primitive and assembly obligations
-/
