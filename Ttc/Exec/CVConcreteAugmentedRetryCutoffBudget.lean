import Ttc.Exec.CVContinuingRetryParameters
import Ttc.Exec.CVGaussianAugmentedCutoffReference
import Ttc.Exec.CVFiniteContinuingAugmentedCutoffSchedule
import Ttc.Exec.CVGaussianWarmFallbackPhaseKernel

/-!
# Concrete query cutoffs for the finite continuing-retry phase

This file turns the reference-law expected-query estimate into the exact deterministic
cutoff selected by `CVContinuingRetryParameters`.  It also sums a uniform phase cutoff.

The resulting expression is polynomial, but contains `1 / correctedNu`.  Consequently
the final adapter to `sourceOneRunQueryBudget` keeps the comparison with the paper's much
smaller displayed source envelope explicit rather than hiding it in a purported universal
constant.
-/

namespace Ttc.CVConcreteAugmentedRetryCutoffBudget

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains
open Ttc.CVContinuingRetryParameters
open Ttc.CVGaussianAugmentedSelectiveTV
open Ttc.CVGaussianAugmentedExpectedCost
open Ttc.CVGaussianAugmentedCutoffReference
open Ttc.FiniteContinuingRetryExpectedCost
open Ttc.FiniteContinuingRetryGaussianAugmentedPhase
open Ttc.CVSourcePolynomialCutoffCapstone
open Ttc.CVGaussianScoreSeedPhaseKernel
open scoped ENNReal Classical BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- Real envelope corresponding to the division-free `10 * steps * M` bound for
`L` continuing-retry attempts. -/
noncomputable def retryReferenceMeanEnvelope
    (M : Real) (steps : Nat → Nat) (L : Nat) : Real :=
  ∑ j ∈ Finset.range L, 10 * ((steps j : Real) * M)

theorem retryReferenceMeanEnvelope_nonneg {M : Real} (hM : 0 ≤ M)
    (steps : Nat → Nat) (L : Nat) :
    0 ≤ retryReferenceMeanEnvelope M steps L := by
  unfold retryReferenceMeanEnvelope
  positivity

theorem ofReal_retryReferenceMeanEnvelope {M : Real} (hM : 0 ≤ M)
    (steps : Nat → Nat) (L : Nat) :
    ENNReal.ofReal (retryReferenceMeanEnvelope M steps L) =
      ∑ j ∈ Finset.range L, 10 * ((steps j : ENNReal) * ENNReal.ofReal M) := by
  unfold retryReferenceMeanEnvelope
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [ENNReal.ofReal_mul (by positivity : (0 : Real) ≤ 10),
      ENNReal.ofReal_mul (by positivity : (0 : Real) ≤ (steps j : Real))]
    norm_num
  · intro j hj
    positivity

/-- The geometric stopped-query theorem, expressed with a real envelope ready for the
concrete Markov cutoff.  The independent random fallback adds no retry queries, so this
is also the reference mean used by the random-fallback postprocessor. -/
theorem augmentedPhaseQueryMean_le_referenceEnvelope
    (hn : 2 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    {q delta sigma R c : Real} (hq : 1 < q)
    (hdelta : 0 < delta) (hsigma : 0 < sigma) (hc : c ≠ 0)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    (hdeltaq : delta ≤ sigma / (max 8 (2 * q) * Real.sqrt n))
    (hR : 0 ≤ R) (hRsigma : R ≤ q * sigma * Real.sqrt n)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (steps : Nat → Nat) (nu : Measure (ScoreSeed n)) [IsProbabilityMeasure nu]
    (pi : Measure (State n)) [IsProbabilityMeasure pi]
    (hpi : pi = ellGaussianProb K delta (sigma ^ 2))
    {M : Real} (hM : 0 ≤ M) (L : Nat)
    (hwarm : ∀ j, j < L → IsWarm (ENNReal.ofReal M)
      (runningCurrent
        (augmentedMarginalOf K hK delta (sigma ^ 2) c hdelta hc steps nu j)) pi) :
    augmentedPhaseQueryMean K hK delta (sigma ^ 2) c hdelta hc steps L nu ≤
      ENNReal.ofReal (retryReferenceMeanEnvelope M steps L) := by
  rw [ofReal_retryReferenceMeanEnvelope hM]
  exact augmentedPhaseQueryMean_le_ten_sum hn hK hKc hball hq hdelta hsigma hc
    hdeltan hdeltaq hR hRsigma hKR steps nu pi hpi (ENNReal.ofReal M) L hwarm

/-- Actual membership-query mean of the retry part of the random-fallback phase.  The
fallback is an independently supplied law and performs no membership query; the finite
retry trace is therefore the complete charged part of this phase. -/
noncomputable def warmFallbackPhaseQueryMean
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat)
    (rho : Measure (State n)) : ENNReal :=
  augmentedPhaseQueryMean K hK delta s c hdelta hc steps L
    (Measure.map (seedEmbedding c) rho)

/-- Reference-mean theorem in the exact incoming-seed shape of
`gaussianWarmFallbackPhaseKernel`. -/
theorem warmFallbackPhaseQueryMean_le_referenceEnvelope
    (hn : 2 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    {q delta sigma R c : Real} (hq : 1 < q)
    (hdelta : 0 < delta) (hsigma : 0 < sigma) (hc : c ≠ 0)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    (hdeltaq : delta ≤ sigma / (max 8 (2 * q) * Real.sqrt n))
    (hR : 0 ≤ R) (hRsigma : R ≤ q * sigma * Real.sqrt n)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (steps : Nat → Nat) (rho : Measure (State n)) [IsProbabilityMeasure rho]
    (pi : Measure (State n)) [IsProbabilityMeasure pi]
    (hpi : pi = ellGaussianProb K delta (sigma ^ 2))
    {M : Real} (hM : 0 ≤ M) (L : Nat)
    (hwarm : ∀ j, j < L → IsWarm (ENNReal.ofReal M)
      (runningCurrent
        (augmentedMarginalOf K hK delta (sigma ^ 2) c hdelta hc steps
          (Measure.map (seedEmbedding c) rho) j)) pi) :
    warmFallbackPhaseQueryMean K hK delta (sigma ^ 2) c hdelta hc steps L rho ≤
      ENNReal.ofReal (retryReferenceMeanEnvelope M steps L) := by
  letI : IsProbabilityMeasure (Measure.map (seedEmbedding c) rho) :=
    Measure.isProbabilityMeasure_map (measurable_seedEmbedding c).aemeasurable
  exact augmentedPhaseQueryMean_le_referenceEnvelope hn hK hKc hball hq hdelta hsigma hc
    hdeltan hdeltaq hR hRsigma hKR steps (Measure.map (seedEmbedding c) rho) pi hpi hM L hwarm

/-- The concrete phase cutoff obtained from the exact retry mean envelope. -/
noncomputable def concreteRetryQueryCutoff
    (M : Real) (steps : Nat → Nat) (L m : Nat) (eps : Real) : ENNReal :=
  continuingQueryCutoff (retryReferenceMeanEnvelope M steps L) m eps

theorem concreteRetryQueryCutoff_pos {M eps : Real} (hM : 0 ≤ M)
    (steps : Nat → Nat) (L m : Nat) (heps : 0 < eps) :
    0 < concreteRetryQueryCutoff M steps L m eps := by
  exact continuingQueryCutoff_pos
    (retryReferenceMeanEnvelope_nonneg hM steps L) heps

/-- With the concrete retry count, Markov timeout spends precisely the continuing timeout
share selected by `CVContinuingRetryParameters`. -/
theorem referenceMean_div_concreteRetryQueryCutoff_le_timeout
    {M eps : Real} (hM : 0 ≤ M) (steps : Nat → Nat) (m : Nat) (heps : 0 < eps) :
    ENNReal.ofReal
        (retryReferenceMeanEnvelope M steps (explicitContinuingRetries m eps)) /
      concreteRetryQueryCutoff M steps (explicitContinuingRetries m eps) m eps ≤
        continuingTimeout m eps := by
  exact expectedCost_div_continuingQueryCutoff_le_timeout
    (retryReferenceMeanEnvelope_nonneg hM steps (explicitContinuingRetries m eps)) heps

/-- A single natural deadline dominating every retry attempt gives a fully scalar phase
mean bound. -/
theorem retryReferenceMeanEnvelope_le_uniform
    {M : Real} (hM : 0 ≤ M) {steps : Nat → Nat} {L T : Nat}
    (hsteps : ∀ j < L, steps j ≤ T) :
    retryReferenceMeanEnvelope M steps L ≤
      10 * (L : Real) * (T : Real) * M := by
  unfold retryReferenceMeanEnvelope
  calc
    _ ≤ ∑ _j ∈ Finset.range L, 10 * ((T : Real) * M) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' := hsteps j (Finset.mem_range.mp hj)
      have hjR : (steps j : Real) ≤ (T : Real) := by exact_mod_cast hj'
      gcongr
    _ = 10 * (L : Real) * (T : Real) * M := by
      simp
      ring

/-- Closed-form phase mean used below: logarithmically many retries, each with at most
`T` lazy-speedy steps and one noncompounding warm factor `M`. -/
noncomputable def explicitRetryPhaseMeanEnvelope
    (M : Real) (T m : Nat) (eps : Real) : Real :=
  10 * (explicitContinuingRetries m eps : Real) * (T : Real) * M

theorem retryReferenceMeanEnvelope_explicit_le
    {M : Real} (hM : 0 ≤ M) {steps : Nat → Nat} {T m : Nat} {eps : Real}
    (hsteps : ∀ j < explicitContinuingRetries m eps, steps j ≤ T) :
    retryReferenceMeanEnvelope M steps (explicitContinuingRetries m eps) ≤
      explicitRetryPhaseMeanEnvelope M T m eps := by
  exact retryReferenceMeanEnvelope_le_uniform hM hsteps

/-- Uniform real upper envelope for `phases` concrete phase cutoffs. -/
noncomputable def continuingOneRunQueryEnvelope
    (B : Real) (phases m : Nat) (eps : Real) : Real :=
  (phases : Real) * (8 * (B + 1) / Ttc.CVCorrected.correctedNu m eps)

/-- Fully expanded uniform schedule cutoff.  Its retry factor has the machine-checked
logarithmic bound `explicitContinuingRetries_lt_logb`; all other displayed operations are
polynomial/rational in the supplied phase, step, warmness, and accuracy parameters. -/
noncomputable def explicitContinuingOneRunQueryEnvelope
    (M : Real) (T phases m : Nat) (eps : Real) : Real :=
  continuingOneRunQueryEnvelope (explicitRetryPhaseMeanEnvelope M T m eps)
    phases m eps

theorem continuingOneRunQueryEnvelope_nonneg {B eps : Real} (hB : 0 ≤ B)
    {phases m : Nat} (heps : 0 < eps) :
    0 ≤ continuingOneRunQueryEnvelope B phases m eps := by
  unfold continuingOneRunQueryEnvelope
  positivity [correctedNu_pos (m := m) heps]

/-- Summing phase-dependent concrete cutoffs requires only a common real mean bound. -/
theorem sum_continuingQueryCutoff_le_envelope
    {B eps : Real} (hB : 0 ≤ B) {phases m : Nat} (heps : 0 < eps)
    (phaseMeanEnvelope : Nat → Real)
    (hphase0 : ∀ i < phases, 0 ≤ phaseMeanEnvelope i)
    (hphase : ∀ i < phases, phaseMeanEnvelope i ≤ B) :
    (∑ i ∈ Finset.range phases,
      continuingQueryCutoff (phaseMeanEnvelope i) m eps) ≤
        ENNReal.ofReal (continuingOneRunQueryEnvelope B phases m eps) := by
  have hnu : 0 < Ttc.CVCorrected.correctedNu m eps := correctedNu_pos heps
  calc
    _ ≤ ∑ _i ∈ Finset.range phases, continuingQueryCutoff B m eps := by
      apply Finset.sum_le_sum
      intro i hi
      unfold continuingQueryCutoff
      apply ENNReal.ofReal_le_ofReal
      apply div_le_div_of_nonneg_right _ hnu.le
      nlinarith [hphase i (Finset.mem_range.mp hi)]
    _ = (phases : ENNReal) * continuingQueryCutoff B m eps := by simp
    _ = ENNReal.ofReal (continuingOneRunQueryEnvelope B phases m eps) := by
      unfold continuingOneRunQueryEnvelope continuingQueryCutoff
      rw [ENNReal.ofReal_mul (by positivity : (0 : Real) ≤ (phases : Real))]
      norm_num

/-- Concrete summed cutoff for logarithmically many retries per phase. -/
theorem sum_explicitRetryQueryCutoff_le_explicitEnvelope
    {M eps : Real} (hM : 0 ≤ M) {T phases m : Nat} (heps : 0 < eps)
    (steps : Nat → Nat → Nat)
    (hsteps : ∀ i < phases, ∀ j < explicitContinuingRetries m eps,
      steps i j ≤ T) :
    (∑ i ∈ Finset.range phases,
      concreteRetryQueryCutoff M (steps i) (explicitContinuingRetries m eps) m eps) ≤
        ENNReal.ofReal (explicitContinuingOneRunQueryEnvelope M T phases m eps) := by
  unfold concreteRetryQueryCutoff explicitContinuingOneRunQueryEnvelope
  apply sum_continuingQueryCutoff_le_envelope
    (B := explicitRetryPhaseMeanEnvelope M T m eps) (eps := eps)
  · unfold explicitRetryPhaseMeanEnvelope
    positivity
  · exact heps
  · exact fun i hi ↦ retryReferenceMeanEnvelope_nonneg hM (steps i)
      (explicitContinuingRetries m eps)
  · exact fun i hi ↦ retryReferenceMeanEnvelope_explicit_le hM
      (hsteps i hi)

/-- Honest adapter to the existing public source budget.  The final real inequality is
kept explicit: with the present conservative `correctedNu`, it is not derivable for a
universal `runtimeConstant` from the paper's `eps^-2` source envelope. -/
theorem sum_continuingQueryCutoff_le_sourceOneRunQueryBudget
    {B eps runtimeConstant R : Real} (hB : 0 ≤ B) {phases m : Nat}
    (heps : 0 < eps) (phaseMeanEnvelope : Nat → Real)
    (hphase0 : ∀ i < phases, 0 ≤ phaseMeanEnvelope i)
    (hphase : ∀ i < phases, phaseMeanEnvelope i ≤ B)
    (hsource : continuingOneRunQueryEnvelope B phases m eps ≤
      sourceOneRunQueryEnvelope runtimeConstant n R eps) :
    (∑ i ∈ Finset.range phases,
      continuingQueryCutoff (phaseMeanEnvelope i) m eps) ≤
        sourceOneRunQueryBudget runtimeConstant n R eps := by
  exact (sum_continuingQueryCutoff_le_envelope hB heps phaseMeanEnvelope hphase0 hphase).trans
    (ENNReal.ofReal_le_ofReal hsource)

#print axioms augmentedPhaseQueryMean_le_referenceEnvelope
#print axioms warmFallbackPhaseQueryMean_le_referenceEnvelope
#print axioms referenceMean_div_concreteRetryQueryCutoff_le_timeout
#print axioms sum_continuingQueryCutoff_le_envelope
#print axioms sum_explicitRetryQueryCutoff_le_explicitEnvelope
#print axioms sum_continuingQueryCutoff_le_sourceOneRunQueryBudget

end Ttc.CVConcreteAugmentedRetryCutoffBudget
