import Kr25Ssmxt.Model.Pseudocode

/-!
# TTC runtime model

This module is the model-level vocabulary for Theorem 3.  It records only the
membership-query counts and algebraic bounds visible in the paper.  Concrete CV18 and
Hit-and-Run executions that populate these fields belong to `Analysis/`.
-/

noncomputable section

open scoped BigOperators

namespace Kr25Ssmxt
namespace TTCRuntime

/-- One polytope membership query scans every facet and costs `dimension * facets`
real-arithmetic operations in the paper's cost model. -/
def membershipQueryOperations (dimension facets queries : Nat) : Nat :=
  dimension * facets * queries

@[simp] theorem membershipQueryOperations_eq (dimension facets queries : Nat) :
    membershipQueryOperations dimension facets queries = dimension * facets * queries := rfl

/-- Integer charge used for the paper's expected rejection count of at most `3/2`. -/
def rejectionAttemptCharge : Nat := 2

/-- Cost of one accepted sample: the Hit-and-Run transitions and the final membership
test, multiplied by the rejection-attempt charge. -/
def acceptedSampleOperations (dimension facets steps : Nat) : Nat :=
  rejectionAttemptCharge * membershipQueryOperations dimension facets (steps + 1)

@[simp] theorem acceptedSampleOperations_eq (dimension facets steps : Nat) :
    acceptedSampleOperations dimension facets steps =
      2 * (dimension * facets * (steps + 1)) := rfl

/-- Model-level runtime trace for TTC's geometric calls.  Implementations supply one CV18
membership-query count and one Hit-and-Run step count for every decomposed component. -/
structure TTCMembershipRuntimeCertificate {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) where
  volumeQueryCount : Fin D.componentCount → Nat
  samplerStepCount : Fin D.componentCount → Nat

/-- Maximum number of accepted samples charged per component in the paper analysis. -/
def sampleCap (p : ApproxParams) (componentCount : Nat) : Nat :=
  Nat.ceil (p.threshold componentCount)

/-- Total geometric-oracle operations represented by a model-level runtime trace. -/
def TTCMembershipRuntimeCertificate.operations {n k : Nat} {F : LRAFormula n k}
    {D : Decomposition F} {p : ApproxParams}
    (cert : TTCMembershipRuntimeCertificate D p) : Nat :=
  ∑ i : Fin D.componentCount,
    (membershipQueryOperations n (D.component i).presentation.facetCount
        (cert.volumeQueryCount i) +
      sampleCap p D.componentCount *
        acceptedSampleOperations n (D.component i).presentation.facetCount
          (cert.samplerStepCount i))

/-- Volume kernel displayed in the proof of Theorem 3, before facets and suppressed
factors are included. -/
def theorem3VolumeKernel (n : Nat) (rho epsilon : Real) : Real :=
  max ((n : Real) ^ 3 * rho ^ 2) ((n : Real) ^ 4) / epsilon ^ 2

/-- Per-sample kernel displayed in the proof of Theorem 3. -/
def theorem3SamplingKernel (n : Nat) (rho : Real) : Real :=
  (n : Real) ^ 5 * rho ^ 2

/-- Unsimplified runtime display from the proof of Theorem 3. -/
def theorem3DetailedRuntime (componentCount n rMax : Nat) (rho epsilon threshold : Real)
    (volumeOverhead samplingOverhead : Real) : Real :=
  (componentCount : Real) * rMax *
    (volumeOverhead * theorem3VolumeKernel n rho epsilon +
      threshold * samplingOverhead * theorem3SamplingKernel n rho)

/-- Exact multiplier containing the factors suppressed by the paper's `O` notation. -/
def theorem3SuppressedFactor (epsilon threshold volumeOverhead samplingOverhead : Real) :
    Real :=
  volumeOverhead / epsilon ^ 2 + threshold * samplingOverhead

/-- Geometric monomial in the headline statement of Theorem 3. -/
def theorem3HeadlineCore (componentCount n rMax : Nat) (rho : Real) : Real :=
  (componentCount : Real) * (n : Real) ^ 5 * rho ^ 2 * rMax

/-- Model-level assumptions corresponding to the two oracle estimates cited by Theorem 3.
The implementation layer discharges these fields for concrete runtime traces. -/
structure Theorem3OracleBounds {n k : Nat} {F : LRAFormula n k}
    {D : Decomposition F} {p : ApproxParams}
    (cert : TTCMembershipRuntimeCertificate D p) (rho : Real) (rMax : Nat) where
  one_le_rho : 1 ≤ rho
  volumeOverhead : Real
  volumeOverhead_nonneg : 0 ≤ volumeOverhead
  samplingOverhead : Real
  samplingOverhead_nonneg : 0 ≤ samplingOverhead
  facets_le : ∀ i, (D.component i).presentation.facetCount ≤ rMax
  volume_operations_le : ∀ i,
    (membershipQueryOperations n (D.component i).presentation.facetCount
        (cert.volumeQueryCount i) : Real) ≤
      ((D.component i).presentation.facetCount : Real) * volumeOverhead *
        theorem3VolumeKernel n rho p.epsilon
  sample_operations_le : ∀ i,
    (acceptedSampleOperations n (D.component i).presentation.facetCount
        (cert.samplerStepCount i) : Real) ≤
      ((D.component i).presentation.facetCount : Real) * samplingOverhead *
        theorem3SamplingKernel n rho

end TTCRuntime
end Kr25Ssmxt
