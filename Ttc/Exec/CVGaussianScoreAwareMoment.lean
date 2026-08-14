import Ttc.Exec.CVGaussianScoreAwareOperational
import Ttc.Exec.CVGaussianWarmFallbackScoreMoment
import Ttc.Volume.AdaptivePhaseScoreVariance

/-! Concrete score slack used by the score-aware Gaussian operation. -/

namespace Ttc.CVGaussianScoreAwareMoment

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
  Arlib.GaussianCooling.Chunked
open Ttc.CVGaussianScoreAwareParameters
open Ttc.CVGaussianWarmFallbackScoreMoment
open Ttc.CVIndependentStreamDependence
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVSequentialPhaseSampler
open scoped ENNReal

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

noncomputable def phaseMomentSlack (chainLength : Nat) (sigmaSq : Nat → Real)
    (K : Set (State n)) (C : Nat → Real) (i : Nat) : Real :=
  (9 - C i) * (chain chainLength sigmaSq K (i + 1) /
    chain chainLength sigmaSq K i) ^ 2

noncomputable def phaseScoreTransportBoundSq (R : Real) (sigmaSq : Nat → Real)
    (i : Nat) : Real :=
  Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2 * (1 + 2 * 9)

theorem phaseScoreTransportBoundSq_pos {R : Real} {sigmaSq : Nat → Real}
    (i : Nat) : 0 < phaseScoreTransportBoundSq R sigmaSq i := by
  unfold phaseScoreTransportBoundSq
  positivity

theorem phaseMomentSlack_pos {chainLength : Nat} {sigmaSq : Nat → Real}
    {K : Set (State n)} {C : Nat → Real}
    (hsigma : ∀ j, 0 < sigmaSq j) (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (hC9 : ∀ i, C i < 9) (i : Nat) :
    0 < phaseMomentSlack chainLength sigmaSq K C i := by
  unfold phaseMomentSlack
  have hi := chain_pos (m := chainLength) hsigma hball hfin i
  have hi1 := chain_pos (m := chainLength) hsigma hball hfin (i + 1)
  exact mul_pos (sub_pos.2 (hC9 i)) (sq_pos_of_pos (div_pos hi1 hi))

/-- Before the end of an adaptive chunk the exact factor is at most two, hence has a
strict seven-unit gap below the operational target factor nine. -/
theorem adaptiveGlobalPhaseVarFactor_lt_nine {N s₀ : Real} (hN : 0 < N)
    {i : Nat} (hsigmaN : adaptiveSigmaSq N s₀ i ≤ N) :
    adaptiveGlobalPhaseVarFactor 1 N s₀ i < 9 := by
  have hdiv : adaptiveSigmaSq N s₀ i / N ≤ 1 := (div_le_one hN).2 hsigmaN
  unfold adaptiveGlobalPhaseVarFactor
  simp only [one_mul]
  linarith

/-- The score-aware error share proves the precise scalar inequality required by
`operational_path_phaseScore_scalarPremises`; no unproved TV-moment binder remains. -/
theorem scoreAware_phaseScore_slack
    {m k chainLength : Nat} {eps R : Real} {sigmaSq : Nat → Real}
    {K : Set (State n)} {C : Nat → Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hsigma : ∀ j, 0 < sigmaSq j) (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (hC9 : ∀ i, C i < 9) (i : Nat) :
    (scoreAwareMixError m k eps
        (phaseMomentSlack chainLength sigmaSq K C)
        (phaseScoreTransportBoundSq R sigmaSq) i).toReal *
      (Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2 * (1 + 2 * 9)) ≤
        (9 - C i) * (chain chainLength sigmaSq K (i + 1) /
          chain chainLength sigmaSq K i) ^ 2 := by
  exact scoreAwareMixError_mul_boundSq_le_slack heps heps1
    (phaseMomentSlack_pos hsigma hball hfin hC9)
    (phaseScoreTransportBoundSq_pos (R := R) (sigmaSq := sigmaSq)) i

/-- Active-phase raw score moment for a score-aware operational path.  This combines
the exact cool-law variance theorem with the operational TV transport; the old scalar
`hslack` premise is absent. -/
theorem operational_path_phaseScore_scoreAware_active
    {k mPhases chainLength : Nat}
    {Q : Nat → Kernel (State n) (State n × State n)}
    [hQ : ∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × State n)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → State n × State n) → Real} {eta : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V mPhases eta)
    {mParam kParam : Nat} {eps R : Real} {slack boundSq : Nat → Real}
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError mPhases
      (scoreAwareMixError mParam kParam eps slack boundSq) j)
    {sigmaSq : Nat → Real} {K : Set (State n)} {C : Nat → Real}
    (hslackDef : slack = phaseMomentSlack chainLength sigmaSq K C)
    (hboundDef : boundSq = phaseScoreTransportBoundSq R sigmaSq)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hsigma : ∀ j, 0 < sigmaSq j) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    (htarget : ∀ i, Measure.map Prod.fst (hop.tau i) = coolLaw chainLength sigmaSq K i)
    (hC0 : ∀ i, 0 ≤ C i) (hC9 : ∀ i, C i < 9)
    (hexact : ∀ i,
      ∫ x, phaseScore chainLength sigmaSq (interior K) i x ^ 2
          ∂(coolLaw chainLength sigmaSq K i) ≤
        C i * (∫ x, phaseScore chainLength sigmaSq (interior K) i x
          ∂(coolLaw chainLength sigmaSq K i)) ^ 2)
    {i : Nat} (hi : i + 1 < mPhases) :
    let pathLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
    let g := fun omega : Nat → State n × State n ↦
      phaseScore chainLength sigmaSq (interior K) i (omega (i + 1)).1
    MemLp g 2 pathLaw ∧ ∫ omega, (g omega) ^ 2 ∂pathLaw ≤
      9 * (∫ omega, g omega ∂pathLaw) ^ 2 := by
  apply operational_path_phaseScore_memLp_and_sq_moment_le_nine hop hsigma hKc
    hball hfin hKR (htarget i) (hC0 i) (hC9 i).le (hexact i)
  rw [hmixError i, activeReferenceMixError, if_pos hi, hslackDef, hboundDef]
  exact scoreAware_phaseScore_slack heps heps1 hsigma hball hfin hC9 i

#print axioms phaseMomentSlack_pos
#print axioms adaptiveGlobalPhaseVarFactor_lt_nine
#print axioms scoreAware_phaseScore_slack
#print axioms operational_path_phaseScore_scoreAware_active

end Ttc.CVGaussianScoreAwareMoment
