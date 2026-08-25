import Kr25Ssmxt.Analysis.BatchFutureProfileMeasurable
import Kr25Ssmxt.Analysis.FutureMembershipProfile
import Kr25Ssmxt.Analysis.MeasureSumByCountableAeFibers
import Kr25Ssmxt.Analysis.ProcessComponentFutureMembershipProfileAEMeasurable

/-!
# One-component transition of future-membership profiles

This derives the desired countable profile stratification from almost-measurability of the
suffix profile under the one-component output law.  The generic countable-fiber decomposition
is separated from the process-specific removal, thinning, finite-batch, and collision
bookkeeping.
-/

noncomputable section

namespace Kr25Ssmxt

open MeasureTheory

/--
A law supported almost everywhere on one fixed `(P :: rest)` profile becomes a countable sum
of laws supported on fixed `rest` profiles after processing `P`.

INTERNAL: one-component removal/thinning/sampling/collision transition used in the induction
for reachable sample-cardinality measurability.
-/
lemma processComponent_profile_step {n k : Nat} (O : TTCOracles n k) (b : Nat)
    (epsilonPrime deltaPrime threshold : Real) (P : PolytopeData n)
    (rest : List (PolytopeData n)) (μ : Measure (TTCState n))
    (profile : Multiset (Nat × List Bool))
    (hkernel : AEMeasurable
      (fun state => processComponent O b epsilonPrime deltaPrime threshold P state) μ)
    (hprofile : ∀ᵐ s ∂μ, futureMembershipProfile (P :: rest) s = profile) :
    ∃ ν : Multiset (Nat × List Bool) → Measure (TTCState n),
      μ.bind (fun state => processComponent O b epsilonPrime deltaPrime threshold P state) =
        Measure.sum ν ∧
      ∀ tailProfile, ∀ᵐ s ∂ν tailProfile,
        futureMembershipProfile rest s = tailProfile := by
  exact measure_sum_by_countable_ae_fibers _ _
    (processComponent_futureMembershipProfile_aemeasurable O b epsilonPrime deltaPrime
      threshold P rest μ profile hkernel hprofile)

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · reduced · proved the generic countable-fiber decomposition and isolated
  output-law profile AEMeasurability as the sole process-specific dependency
* this round · reduced · isolated one iteration's removal, coupled thinning, finite batch
  partition, and collision bookkeeping with the bind-measurability hypothesis explicit
-/
