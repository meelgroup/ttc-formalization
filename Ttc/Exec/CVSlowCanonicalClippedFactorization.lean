import Ttc.Exec.CVSlowCanonicalPositivePathFactorization
import Ttc.Exec.CVSlowCanonicalRobustCertificate

/-!
# Finite-history factorization of the slow canonical *clipped* empirical statistic

`Ttc.CVSlowCanonicalRobustCertificate.slowClippedPositiveEmpiricalFamily` is the literal
statistic run by the slow canonical route: the `k`-stream average of the positive-dummy
phase family, clipped at `correctedAlpha m eps` times its own mean under the independent
path law.

`IndependentStreamOperational` requires this family to factor through a finite history:
a `V_eq` field exhibiting `V (i + 1)` as a function of the time-`(i+1)` block alone, and a
`U_eq` field exhibiting the corrected prefix `accuracyU` as a function of the history
through time `i`.

Both follow from the transport already proved in
`Ttc.Exec.CVSlowCanonicalPositivePathFactorization`, because neither
`Arlib.GaussianCooling.accuracyU` nor `Arlib.GaussianCooling.prefixMean` ever reads the
phase family at index zero (`accuracyU_congr_succ`, `prefixMean_congr_succ`).  So it
suffices to identify the clipped family at *successor* indices with the block statistic
`slowClippedCoordinateStatistic` defined below; the index-zero value of the clipped family
(itself a clipped constant `1`) is irrelevant and is never mentioned.

The clip threshold is a *constant* — an integral of the family against a fixed measure —
so it contributes nothing to the history dependence and passes through `min` untouched.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Ttc.CVSlowCanonicalClippedFactorization

open MeasureTheory ProbabilityTheory Set
open Arlib.GaussianCooling
open Ttc.CVCorrected
open Ttc.CVIndependentStreamMoments
open Ttc.CVIndependentStreamDependence
open Ttc.CVRelativeMeanClippingAssembly
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVSlowCanonicalRobustCertificate
open Ttc.CVSlowCanonicalPositivePathFactorization
open scoped Classical

variable {n : Nat}

/-- The state space of one cooling stream. -/
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- One recorded pair (state, raw seed) of one cooling stream. -/
abbrev ScoreSeed (n : Nat) := State n × State n

/-! ## Step 1: the block statistic, and the successor-index identification -/

/-- The finite-history (single time block) form of the slow canonical clipped statistic.

At paper index `i` it reads the `k`-stream block of `ScoreSeed n` values at time `i + 1`,
averages the phase-`i` score of the state components, and clips the result at
`correctedAlpha m eps` times the (constant) mean of the corresponding stream average under
the independent path law. -/
noncomputable def slowClippedCoordinateStatistic
    (m k : Nat) (eps : Real)
    (Q : Nat → Kernel (State n) (ScoreSeed n)) [∀ i, IsMarkovKernel (Q i)]
    (mu0 : Measure (ScoreSeed n)) (sigmaSq : Nat → Real) (K : Set (State n))
    (i : Nat) : (Fin k → ScoreSeed n) → Real :=
  fun x ↦
    min (streamAverage (k := k)
        (fun p : ScoreSeed n ↦ phaseScore m sigmaSq (interior K) i p.1) x)
      (correctedAlpha m eps *
        ∫ z, streamAverage (k := k)
            (positiveScalarPhaseFamilyChainLength (Seed := State n) m sigmaSq K (i + 1)) z
          ∂independentPathLaw k (stateScheduleFromSeed Q) mu0)

/-- The `V_eq` field: at every successor index the clipped empirical family reads only the
block of states at that time. -/
theorem slowClippedPositiveEmpiricalFamily_succ
    (m k : Nat) (eps : Real)
    (Q : Nat → Kernel (State n) (ScoreSeed n)) [∀ i, IsMarkovKernel (Q i)]
    (mu0 : Measure (ScoreSeed n)) (sigmaSq : Nat → Real) (K : Set (State n)) (i : Nat) :
    slowClippedPositiveEmpiricalFamily m k eps Q mu0 sigmaSq K (i + 1) =
      fun omega ↦ slowClippedCoordinateStatistic m k eps Q mu0 sigmaSq K i
        (fun l ↦ omega l (i + 1)) := by
  funext omega
  rfl

/-- The clipped empirical family agrees, at every successor index, with the positive-dummy
coordinatewise family built from `slowClippedCoordinateStatistic`.  This is all the
corrected accuracy recursion ever reads. -/
theorem slowClippedPositiveEmpiricalFamily_eq_positiveCoordinatePhases_succ
    (m k : Nat) (eps : Real)
    (Q : Nat → Kernel (State n) (ScoreSeed n)) [∀ i, IsMarkovKernel (Q i)]
    (mu0 : Measure (ScoreSeed n)) (sigmaSq : Nat → Real) (K : Set (State n)) (i : Nat) :
    slowClippedPositiveEmpiricalFamily m k eps Q mu0 sigmaSq K (i + 1) =
      positiveCoordinatePhases (X := ScoreSeed n)
        (slowClippedCoordinateStatistic m k eps Q mu0 sigmaSq K) (i + 1) :=
  slowClippedPositiveEmpiricalFamily_succ m k eps Q mu0 sigmaSq K i

/-! ## Step 2: measurability -/

/-- The block statistic is measurable: a stream average of measurable phase scores, clipped
at a constant. -/
theorem measurable_slowClippedCoordinateStatistic
    (m k : Nat) (eps : Real)
    (Q : Nat → Kernel (State n) (ScoreSeed n)) [∀ i, IsMarkovKernel (Q i)]
    (mu0 : Measure (ScoreSeed n)) (sigmaSq : Nat → Real) (K : Set (State n)) (i : Nat) :
    Measurable (slowClippedCoordinateStatistic m k eps Q mu0 sigmaSq K i) :=
  (measurable_streamAverage
    ((measurable_phaseScore isOpen_interior.measurableSet i).comp measurable_fst)).min
      measurable_const

/-- The corresponding finite-history accuracy statistic is measurable. -/
theorem measurable_slowClippedHistoryAccuracy
    (m k : Nat) (eps : Real)
    (Q : Nat → Kernel (State n) (ScoreSeed n)) [∀ i, IsMarkovKernel (Q i)]
    (mu0 : Measure (ScoreSeed n)) (sigmaSq : Nat → Real) (K : Set (State n))
    (mu : Measure (Fin k → Nat → ScoreSeed n)) (alpha : Real) (i : Nat) :
    Measurable (Ttc.CVCoordinateStatisticFactorization.historyAccuracy mu
      (slowClippedCoordinateStatistic m k eps Q mu0 sigmaSq K) alpha i) :=
  Ttc.CVCoordinateStatisticFactorization.measurable_historyAccuracy mu _
    (measurable_slowClippedCoordinateStatistic m k eps Q mu0 sigmaSq K) alpha i

/-! ## Step 3: both factorization fields -/

/-- Both factorization fields required by `IndependentStreamOperational`, for the slow
canonical clipped empirical statistic: the finite-history statistic is
`Ttc.CVCoordinateStatisticFactorization.historyAccuracy` of the block statistic
`slowClippedCoordinateStatistic`. -/
theorem slowClipped_factorizations
    (m k : Nat) (eps : Real)
    (Q : Nat → Kernel (State n) (ScoreSeed n)) [∀ i, IsMarkovKernel (Q i)]
    (mu0 : Measure (ScoreSeed n)) (sigmaSq : Nat → Real) (K : Set (State n))
    (mu : Measure (Fin k → Nat → ScoreSeed n)) (alpha : Real) :
    (∀ i, accuracyU mu (slowClippedPositiveEmpiricalFamily m k eps Q mu0 sigmaSq K)
        alpha i =
      fun omega ↦ Ttc.CVCoordinateStatisticFactorization.historyAccuracy mu
        (slowClippedCoordinateStatistic m k eps Q mu0 sigmaSq K) alpha i
        (fun l ↦ Preorder.frestrictLe (π := fun _ : Nat => ScoreSeed n) i (omega l))) ∧
    (∀ i, slowClippedPositiveEmpiricalFamily m k eps Q mu0 sigmaSq K (i + 1) =
      fun omega ↦ slowClippedCoordinateStatistic m k eps Q mu0 sigmaSq K i
        (fun l ↦ omega l (i + 1))) := by
  refine ⟨fun i ↦ ?_, slowClippedPositiveEmpiricalFamily_succ m k eps Q mu0 sigmaSq K⟩
  rw [accuracyU_congr_succ mu (slowClippedPositiveEmpiricalFamily m k eps Q mu0 sigmaSq K)
    (positiveCoordinatePhases (X := ScoreSeed n)
      (slowClippedCoordinateStatistic m k eps Q mu0 sigmaSq K)) alpha
    (slowClippedPositiveEmpiricalFamily_eq_positiveCoordinatePhases_succ
      m k eps Q mu0 sigmaSq K) i]
  exact (positiveCoordinate_factorizations (X := ScoreSeed n) mu
    (slowClippedCoordinateStatistic m k eps Q mu0 sigmaSq K) alpha).1 i

/-! ## Step 4: the consumer-shaped package -/

/-- Everything the block-level binders of
`Ttc.CVSlowCanonicalStreamOperational.slowCanonicalStreamOperational` require of the slow
canonical clipped statistic, at `V := slowClippedPositiveEmpiricalFamily …`,
`alpha := correctedAlpha m eps` and `mu := independentPathLaw k (stateScheduleFromSeed Q) mu0`.

The four conjuncts are, in order, the `hu`, `hv`, `hU` and `hV` binders, taken at
`u := historyAccuracy … (slowClippedCoordinateStatistic …) (correctedAlpha m eps)` and
`v := slowClippedCoordinateStatistic …`.

This module deliberately does not import `Ttc.Exec.CVSlowCanonicalStreamOperational` (no
import cycle exists, but the statement is strictly more general without it): `Q` here is an
arbitrary Markov schedule, so a caller instantiates it at the canonical active schedule. -/
theorem slowClipped_streamOperational_statistics
    (m k : Nat) (eps : Real)
    (Q : Nat → Kernel (State n) (ScoreSeed n)) [∀ i, IsMarkovKernel (Q i)]
    (mu0 : Measure (ScoreSeed n)) (sigmaSq : Nat → Real) (K : Set (State n)) :
    (∀ i, Measurable (Ttc.CVCoordinateStatisticFactorization.historyAccuracy
        (independentPathLaw k (stateScheduleFromSeed Q) mu0)
        (slowClippedCoordinateStatistic m k eps Q mu0 sigmaSq K)
        (correctedAlpha m eps) i)) ∧
    (∀ i, Measurable (slowClippedCoordinateStatistic m k eps Q mu0 sigmaSq K i)) ∧
    (∀ i, accuracyU (independentPathLaw k (stateScheduleFromSeed Q) mu0)
        (slowClippedPositiveEmpiricalFamily m k eps Q mu0 sigmaSq K)
        (correctedAlpha m eps) i =
      fun omega ↦ Ttc.CVCoordinateStatisticFactorization.historyAccuracy
        (independentPathLaw k (stateScheduleFromSeed Q) mu0)
        (slowClippedCoordinateStatistic m k eps Q mu0 sigmaSq K) (correctedAlpha m eps) i
        (fun l ↦ Preorder.frestrictLe (π := fun _ : Nat => ScoreSeed n) i (omega l))) ∧
    (∀ i, slowClippedPositiveEmpiricalFamily m k eps Q mu0 sigmaSq K (i + 1) =
      fun omega ↦ slowClippedCoordinateStatistic m k eps Q mu0 sigmaSq K i
        (fun l ↦ omega l (i + 1))) := by
  refine ⟨fun i ↦ measurable_slowClippedHistoryAccuracy m k eps Q mu0 sigmaSq K _ _ i,
    measurable_slowClippedCoordinateStatistic m k eps Q mu0 sigmaSq K, ?_, ?_⟩
  · exact (slowClipped_factorizations m k eps Q mu0 sigmaSq K
      (independentPathLaw k (stateScheduleFromSeed Q) mu0) (correctedAlpha m eps)).1
  · exact slowClippedPositiveEmpiricalFamily_succ m k eps Q mu0 sigmaSq K

#print axioms slowClippedCoordinateStatistic
#print axioms slowClippedPositiveEmpiricalFamily_succ
#print axioms slowClippedPositiveEmpiricalFamily_eq_positiveCoordinatePhases_succ
#print axioms measurable_slowClippedCoordinateStatistic
#print axioms measurable_slowClippedHistoryAccuracy
#print axioms slowClipped_factorizations
#print axioms slowClipped_streamOperational_statistics

end Ttc.CVSlowCanonicalClippedFactorization
