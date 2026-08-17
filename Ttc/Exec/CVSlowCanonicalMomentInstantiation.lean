import Ttc.Exec.CVSlowCanonicalStreamOperational
import Ttc.Exec.CVSlowCanonicalUniformParameters
import Ttc.Exec.CVSlowCanonicalPhaseMomentPackage
import Ttc.Exec.CVScoreAwareHalfMeanBudget

/-! # Analytic instantiation of the slow-canonical phase-moment package -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Ttc.CVSlowCanonicalMomentInstantiation

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVCorrected Ttc.CVCorrectedRuntime
open Ttc.CVIndependentStreamDependence Ttc.CVScoreSeedPhaseKernel
open Ttc.CVGaussianScoreAwareParameters Ttc.CVGaussianFactorSevenAssembly
open Ttc.CVGaussianScoreAwareMeanBudget Ttc.CVScoreAwareHalfMeanBudget
open Ttc.CVGaussianBlockRetryParameters
open Ttc.CVSlowFullBodySourceSchedule Ttc.CVSlowSourceReferenceCertificate
open Ttc.CVSlowSourceTargetTVAccuracy Ttc.CVRAwareGlobalRadius
open Ttc.CVSlowCanonicalShareBounds Ttc.CVMinimalScoreAwareWarmLogArithmetic
open Ttc.CVSlowCanonicalUniformParameters
open Ttc.CVSlowCanonicalPhaseMomentPackage
open Ttc.CVSlowCanonicalStreamOperational
open Ttc.CVSlowRadiusQReferencePhaseTV
open Ttc.CVSlowRadiusQCanonicalOperational
open Ttc.CVGlobalLogarithmicRadius
open Ttc.CVRelativeMeanClippingAssembly
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-! ## Step 1 — the target-TV binder at the uniform radius selection -/

/-- The `htargetTV` hypothesis of the phase-moment consumers, for any stream whose
phase targets are the canonical slow local pair references at the *active* chain
length `m + 1`.  The radius is the uniform selection
`slowUniformQ n m k eps R = rAwareGlobalRadiusQ n R s0 (slowUniformMeanTailFloor …)`. -/
theorem slowCanonical_htargetTV
    {k m : Nat} {Q : Nat → Kernel (State n) (ScoreSeed n)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (ScoreSeed n)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → ScoreSeed n) → Real} {estimatorEps eps R : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V m estimatorEps)
    (hn : 1 ≤ n)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (htau : ∀ i, i < m → hop.tau i =
      slowLocalPairReference (m + 1) n (slowUniformQ n m k eps R)
        (slowSourceInitialVariance n) K i) :
    ∀ j, TVLe (Measure.map Prod.fst (hop.tau j))
      (coolLaw m (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j)
      (slowTargetError n
        (rAwareGlobalRadiusQ n R (slowSourceInitialVariance n)
          (slowUniformMeanTailFloor n m k eps R)) m j) := by
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have hq4 : (4 : Real) ≤ slowUniformQ n m k eps R := four_le_slowUniformQ hn m k eps R
  have hq1 : (1 : Real) < slowUniformQ n m k eps R := by linarith
  have htau' : ∀ i, i < m → hop.tau i =
      slowLocalPairReference m n (slowUniformQ n m k eps R)
        (slowSourceInitialVariance n) K i := by
    intro i hi
    rw [htau i hi]
    exact slowLocalPairReference_succ_length_eq m n _ _ K hi
  exact tvLe_map_fst_tau_fullCoolLaw_slowTargetError hop hn hq1 hs0 hK hKc hball hfin
    (fun i _ ↦ slowUniformQ_rad hn m k eps R i) htau'

#print axioms slowCanonical_htargetTV

end Ttc.CVSlowCanonicalMomentInstantiation
