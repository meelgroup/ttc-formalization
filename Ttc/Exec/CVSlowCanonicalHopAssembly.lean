import Ttc.Exec.CVSlowCanonicalStreamOperational
import Ttc.Exec.CVSlowCanonicalClippedFactorization

/-!
# Assembling the slow canonical `hop` at the literal clipped statistic

`Ttc.CVSlowCanonicalStreamOperational.exists_slowCanonicalStreamOperational` produces the
`hop` / `htau` / `hmixError` triple demanded by
`Ttc.CVSlowCanonicalRobustCertificate.exists_sourceReferenceTVOneRunCertificate_slowCanonical_of_weightedData`,
but leaves twelve pieces of finite-history factorization data as binders: a scalar
(single-path) quadruple `Vscalar` / `uscalar` / `vscalar` and a stream (`Fin k`-block)
quadruple `V` / `u` / `v`.

This file discharges all twelve, pinning `V` to the *literal* statistic run by the slow
canonical route, `Ttc.CVSlowCanonicalRobustCertificate.slowClippedPositiveEmpiricalFamily`
— which is exactly the frontier theorem's `hVliteral` right-hand side.  Consequently the
frontier's `hVliteral` may be taken to be `rfl`.

Two already-proved transports do all the work:

* the stream layer is
  `Ttc.CVSlowCanonicalClippedFactorization.slowClipped_streamOperational_statistics`,
  stated for an arbitrary Markov schedule `Q`, hence usable verbatim under the frontier's
  abstract `Q`-plus-equation form;
* the scalar layer is
  `Ttc.CVSlowCanonicalPositivePathFactorization.positiveScalarPhaseFamily_factorizations`
  at the unclipped positive-dummy phase family.  The scalar family is a genuinely free
  parameter here: `Vscalar` occurs only in the intermediate `SeedProjectedOperational`
  package and does not appear in the type of the resulting
  `IndependentStreamOperational`, whose statistic is the stream-level `V`.  We fill it
  with the canonical phase-score family rather than a throw-away constant so that the
  intermediate package remains the meaningful one.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Ttc.CVSlowCanonicalHopAssembly

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVCorrected
open Ttc.CVIndependentStreamDependence
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVGaussianScoreAwareParameters
open Ttc.CVRelativeMeanClippingAssembly
open Ttc.CVSlowFullBodySourceSchedule
open Ttc.CVSlowRadiusQCanonicalOperational
open Ttc.CVSlowSourceReferenceCertificate Ttc.CVSlowCanonicalRetainedReference
open Ttc.CVSlowCanonicalRobustCertificate
open Ttc.CVSlowCanonicalPositivePathFactorization
open Ttc.CVSlowCanonicalClippedFactorization
open Ttc.CVSlowCanonicalStreamOperational
open scoped ENNReal Classical

variable {n : Nat}

/-- The state space of one cooling stream. -/
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- One recorded pair (state, raw seed) of one cooling stream. -/
abbrev ScoreSeed (n : Nat) := State n × State n

/-! ## The scalar layer -/

/-- The scalar (single-path) finite-history statistic used to fill the `uscalar` binder:
the corrected prefix recursion of the state-projected phase score along one path. -/
noncomputable def slowScalarHistoryAccuracy (m : Nat) (eps : Real)
    (sigmaSq : Nat → Real) (K : Set (State n))
    (mu : Measure (Nat → ScoreSeed n)) :
    (i : Nat) → (Finset.Iic i → ScoreSeed n) → Real :=
  Ttc.CVCoordinateStatisticFactorization.pathHistoryAccuracy mu
    (fun i x ↦ phaseScore (m + 1) sigmaSq (interior K) i x.1) (correctedAlpha (m + 1) eps)

/-- Measurability of the scalar finite-history statistic. -/
theorem measurable_slowScalarHistoryAccuracy (m : Nat) (eps : Real)
    (sigmaSq : Nat → Real) {K : Set (State n)} (mu : Measure (Nat → ScoreSeed n)) (i : Nat) :
    Measurable (slowScalarHistoryAccuracy m eps sigmaSq K mu i) :=
  Ttc.CVCoordinateStatisticFactorization.measurable_pathHistoryAccuracy mu _
    (fun j ↦ (measurable_phaseScore isOpen_interior.measurableSet j).comp measurable_fst)
    (correctedAlpha (m + 1) eps) i

/-- The four scalar binders of
`Ttc.CVSlowCanonicalStreamOperational.exists_slowCanonicalStreamOperational`, at
`Vscalar := positiveScalarPhaseFamilyChainLength (m + 1) sigmaSq K`,
`vscalar := phaseScore (m + 1) sigmaSq (interior K)` and
`uscalar := slowScalarHistoryAccuracy …`. -/
theorem slowScalar_streamOperational_statistics (m : Nat) (eps : Real)
    (sigmaSq : Nat → Real) (K : Set (State n)) (mu : Measure (Nat → ScoreSeed n)) :
    (∀ i, Measurable (slowScalarHistoryAccuracy m eps sigmaSq K mu i)) ∧
    (∀ i, Measurable (phaseScore (m + 1) sigmaSq (interior K) i)) ∧
    (∀ i, accuracyU mu
        (positiveScalarPhaseFamilyChainLength (Seed := State n) (m + 1) sigmaSq K)
        (correctedAlpha (m + 1) eps) i =
      fun omega ↦ slowScalarHistoryAccuracy m eps sigmaSq K mu i
        (Preorder.frestrictLe (π := fun _ : Nat => ScoreSeed n) i omega)) ∧
    (∀ i, positiveScalarPhaseFamilyChainLength (Seed := State n) (m + 1) sigmaSq K (i + 1) =
      fun omega ↦ phaseScore (m + 1) sigmaSq (interior K) i (omega (i + 1)).1) := by
  refine ⟨measurable_slowScalarHistoryAccuracy m eps sigmaSq mu,
    fun i ↦ measurable_phaseScore isOpen_interior.measurableSet i, ?_, fun _ ↦ rfl⟩
  exact (positiveScalarPhaseFamily_factorizations (Seed := State n) (m + 1) sigmaSq K mu
    (correctedAlpha (m + 1) eps)).1

#print axioms slowScalarHistoryAccuracy
#print axioms measurable_slowScalarHistoryAccuracy
#print axioms slowScalar_streamOperational_statistics

/-! ## The assembled `hop` -/

/-- The `hop` / `htau` / `hmixError` triple of the slow canonical frontier theorem, at the
literal clipped statistic `slowClippedPositiveEmpiricalFamily` and with no factorization
data left as a binder. -/
theorem exists_slowCanonicalHop_literal
    (hn : 21 ≤ n) (m k : Nat) (hk : 1 ≤ k)
    {q eps : Real} (hq4 : 4 ≤ q) (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (scoreScale : Real) {slack boundSq : Nat → Real}
    (hslack : ∀ i, 0 < slack i) (hbound : ∀ i, 0 < boundSq i)
    [∀ j, IsProbabilityMeasure (slowStationaryTail n q (slowSourceInitialVariance n) K j)]
    [IsProbabilityMeasure (slowInitialPair n)]
    {Q : Nat → Kernel (State n) (ScoreSeed n)} [∀ i, IsMarkovKernel (Q i)]
    (hQ : Q = slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1) k
      (q := q) (eps := eps / 2) (s0 := slowSourceInitialVariance n)
      (lt_of_lt_of_le (by norm_num) hq4)
      (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
      slowReferenceWarm slack boundSq) :
    ∃ hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
        (slowInitialPair n)
        (slowClippedPositiveEmpiricalFamily m k eps Q (slowInitialPair n)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K) m eps,
      (∀ i, i < m → hop.tau i =
        slowLocalPairReference (m + 1) n q (slowSourceInitialVariance n) K i) ∧
      (∀ j, hop.mixError j = activeReferenceMixError (m + 1)
        (scoreAwareMixError (m + 1) k (eps / 2) slack boundSq) j) := by
  obtain ⟨hu, hv, hU, hV⟩ := slowClipped_streamOperational_statistics m k eps Q
    (slowInitialPair n) (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
  obtain ⟨huscalar, hvscalar, hUscalar, hVscalar⟩ :=
    slowScalar_streamOperational_statistics (n := n) m eps
      (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
      (inhomogeneousPathMeasure (stateScheduleFromSeed Q) (slowInitialPair n))
  exact exists_slowCanonicalStreamOperational hn m k hk hq4 heps heps1 hK hKc hball hfin
    scoreScale hslack hbound hQ
    (positiveScalarPhaseFamilyChainLength (Seed := State n) (m + 1)
      (slowSourceSigmaSq n (slowSourceInitialVariance n)) K)
    (slowScalarHistoryAccuracy m eps (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
      (inhomogeneousPathMeasure (stateScheduleFromSeed Q) (slowInitialPair n)))
    (phaseScore (m + 1) (slowSourceSigmaSq n (slowSourceInitialVariance n)) (interior K))
    huscalar hvscalar hUscalar hVscalar
    _ _ _ hu hv hU hV

#print axioms exists_slowCanonicalHop_literal

end Ttc.CVSlowCanonicalHopAssembly
