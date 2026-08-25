import Kr25Ssmxt.Analysis.BatchFutureProfileMeasurable
import Kr25Ssmxt.Analysis.FutureMembershipProfile
import Kr25Ssmxt.Analysis.FutureMembershipProfileMeasurableSpace

/-!
# Almost-measurability of the profile after one component

Exact suffix profiles are globally measurable for the countable coded-lattice sample state,
so they are almost measurable under every component output law.
-/

noncomputable section

namespace Kr25Ssmxt

open MeasureTheory

/--
Processing one component turns a fixed almost-sure input profile into an almost-measurable
observable of the output law for the remaining component suffix.

INTERNAL: removal, coupled thinning, generated-batch membership, and collision bookkeeping
needed before the generic countable-fiber decomposition can be applied.
-/
lemma processComponent_futureMembershipProfile_aemeasurable {n k : Nat}
    (O : TTCOracles n k) (b : Nat) (epsilonPrime deltaPrime threshold : Real)
    (P : PolytopeData n) (rest : List (PolytopeData n)) (μ : Measure (TTCState n))
    (profile : Multiset (Nat × List Bool))
    (hkernel : AEMeasurable
      (fun state => processComponent O b epsilonPrime deltaPrime threshold P state) μ)
    (hprofile : ∀ᵐ s ∂μ, futureMembershipProfile (P :: rest) s = profile) :
    AEMeasurable (futureMembershipProfile rest)
      (μ.bind (fun state =>
        processComponent O b epsilonPrime deltaPrime threshold P state)) := by
  exact (futureMembershipProfile_measurable rest).aemeasurable

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · global profile measurability makes the process-specific assumptions
  unnecessary for this conclusion
-/
