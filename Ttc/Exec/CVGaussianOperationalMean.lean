import Ttc.Exec.CVCoordinateStatisticFactorization
import Ttc.Exec.CVGaussianWarmFallbackScoreMoment
import Ttc.Exec.CVCorrectedClippingBias

/-!
# Approximate Gaussian telescope for the operational CV path

This file replaces the invalid exact sampled-mean telescope by the relative statement
delivered by total-variation mixing.  It is the mean-side companion to the operational
second-moment transport.
-/

namespace Ttc.CVGaussianOperationalMean

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVIndependentStreamMoments Ttc.CVIndependentStreamDependence
open Ttc.CVGaussianWarmFallbackScoreMoment Ttc.CVCorrectedClippingBias
open Ttc.CVScoreSeedPhaseKernel
open scoped ENNReal Classical BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- Phase `i` score read from time `i+1` of one scalar operational stream. -/
noncomputable def scalarPhaseScore {Seed : Type*}
    (m : Nat) (sigmaSq : Nat → Real) (K : Set (State n)) (i : Nat) :
    (Nat → State n × Seed) → Real :=
  fun omega => phaseScore m sigmaSq (interior K) i (omega (i + 1)).1

/-- Paper-indexed empirical phase family on `k` independent complete streams. -/
noncomputable def empiricalPhaseFamily {Seed : Type*} (k m : Nat)
    (sigmaSq : Nat → Real) (K : Set (State n)) :
    Nat → (Fin k → Nat → State n × Seed) → Real
  | 0 => fun _ => 0
  | i + 1 => streamAverage (k := k) (scalarPhaseScore m sigmaSq K i)

theorem measurable_scalarPhaseScore {Seed : Type*} [MeasurableSpace Seed]
    {m : Nat} {sigmaSq : Nat → Real} {K : Set (State n)}
    (hK : MeasurableSet K) (i : Nat) :
    Measurable (scalarPhaseScore (Seed := Seed) m sigmaSq K i) := by
  exact (measurable_phaseScore isOpen_interior.measurableSet i).comp
    (measurable_fst.comp (measurable_pi_apply (i + 1)))

theorem measurable_empiricalPhaseFamily {Seed : Type*} [MeasurableSpace Seed]
    {k m : Nat} {sigmaSq : Nat → Real} {K : Set (State n)}
    (hK : MeasurableSet K) :
    ∀ i, Measurable (empiricalPhaseFamily (Seed := Seed) k m sigmaSq K i)
  | 0 => measurable_const
  | i + 1 => measurable_streamAverage (measurable_scalarPhaseScore hK i)

/-- Each empirical operational phase mean has the same relative bias as one scalar
stream. -/
theorem integral_empiricalPhaseFamily_mem_relErr
    {Seed : Type*} [MeasurableSpace Seed]
    {k m : Nat} {Q : Nat → Kernel Seed (State n × Seed)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × Seed)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → State n × Seed) → Real} {eps : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V m eps)
    (hk : 0 < k) {sigmaSq : Nat → Real} (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R eta : Real} (hKR : K ⊆ closedBall (0 : State n) R)
    (htarget : ∀ i, Measure.map Prod.fst (hop.tau i) = coolLaw m sigmaSq K i)
    (herror : ∀ i : Fin m,
      Real.exp (R ^ 2 / (2 * sigmaSq (i : Nat))) *
          (hop.mixError (i : Nat)).toReal ≤
        eta * (chain m sigmaSq K ((i : Nat) + 1) /
          chain m sigmaSq K (i : Nat)))
    (i : Fin m) :
    ∫ omega, empiricalPhaseFamily (Seed := Seed) k m sigmaSq K ((i : Nat) + 1) omega
        ∂independentPathLaw k (stateScheduleFromSeed Q) mu0 ∈
      Ttc.relErr eta
        (chain m sigmaSq K ((i : Nat) + 1) / chain m sigmaSq K (i : Nat)) := by
  let scalarLaw : Measure (Nat → State n × Seed) :=
    inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
  let g := scalarPhaseScore (Seed := Seed) m sigmaSq K (i : Nat)
  have hg : Measurable g := measurable_scalarPhaseScore hK (i : Nat)
  have htv := tvLe_operational_score_eval_succ hop (i : Nat)
  rw [htarget (i : Nat)] at htv
  have hmean : ∫ omega, g omega ∂scalarLaw ∈
      Ttc.relErr eta
        (chain m sigmaSq K ((i : Nat) + 1) / chain m sigmaSq K (i : Nat)) := by
    apply integral_phaseScore_interior_mem_Icc_of_tvLe hsigma hKc hball hfin hKR
      (measurable_fst.comp (measurable_pi_apply ((i : Nat) + 1))) htv
      (hop.mixError_ne_top (i : Nat))
    exact herror i
  have hbound : ∀ omega, |g omega| ≤ Real.exp (R ^ 2 / (2 * sigmaSq (i : Nat))) := by
    intro omega
    dsimp only [g, scalarPhaseScore]
    rw [abs_of_nonneg (phaseScore_nonneg m sigmaSq (interior K) (i : Nat) _)]
    exact phaseScore_le hsigma (interior_subset.trans hKR) (i : Nat) _
  have hgInt : Integrable g scalarLaw := by
    exact Integrable.of_bound hg.aestronglyMeasurable _
      (Filter.Eventually.of_forall hbound)
  have havg := integral_streamAverage (k := k) hk scalarLaw hg hgInt
  simpa only [empiricalPhaseFamily, independentPathLaw, scalarLaw, g] using
    (havg ▸ hmean)

/-- The raw empirical prefix is within aggregate relative error `gamma` of the final
cooling normalizer. -/
theorem operational_rawPrefix_mem_relErr
    {Seed : Type*} [MeasurableSpace Seed]
    {k m : Nat} {Q : Nat → Kernel Seed (State n × Seed)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × Seed)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → State n × Seed) → Real} {eps : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V m eps)
    (hk : 0 < k) {sigmaSq : Nat → Real} (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R eta gamma : Real} (hKR : K ⊆ closedBall (0 : State n) R)
    (heta : 0 ≤ eta) (hgamma : gamma ≤ 1)
    (hbudget : 2 * (m : Real) * eta ≤ gamma)
    (htarget : ∀ i, Measure.map Prod.fst (hop.tau i) = coolLaw m sigmaSq K i)
    (herror : ∀ i : Fin m,
      Real.exp (R ^ 2 / (2 * sigmaSq (i : Nat))) *
          (hop.mixError (i : Nat)).toReal ≤
        eta * (chain m sigmaSq K ((i : Nat) + 1) /
          chain m sigmaSq K (i : Nat)))
    (hm : 0 < m) :
    chain m sigmaSq K 0 *
        prefixMean (independentPathLaw k (stateScheduleFromSeed Q) mu0)
          (empiricalPhaseFamily (Seed := Seed) k m sigmaSq K) m ∈
      Ttc.relErr gamma (chain m sigmaSq K m) := by
  apply prefixMean_mem_relErr_of_phaseMeans_budget
    (mu := independentPathLaw k (stateScheduleFromSeed Q) mu0)
    (Wbar := empiricalPhaseFamily (Seed := Seed) k m sigmaSq K)
    (A := fun i => chain m sigmaSq K i)
    hm heta hgamma hbudget (fun i => chain_pos hsigma hball hfin i)
  intro i
  exact integral_empiricalPhaseFamily_mem_relErr hop hk hsigma hK hKc hball hfin
    hKR htarget herror i

#print axioms integral_empiricalPhaseFamily_mem_relErr
#print axioms operational_rawPrefix_mem_relErr

end Ttc.CVGaussianOperationalMean
