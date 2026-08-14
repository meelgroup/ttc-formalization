import Ttc.Exec.CVGaussianScoreSeedPhaseKernel
import Arlib.Probability.TVKernelHeterogeneous
import Arlib.Probability.TVTensor

/-!
# Exceptional-path transfer for the Gaussian score/seed phase

The exact accepted reference is supported on the graph `y ↦ (y, c • y)`.  Its second
coordinate is a dimension-free warm start for the next speedy walk.  A finite operational
retry law is generally only close to this reference in total variation; that does **not**
make its seed marginal warm.  For cost accounting, however, every measurable bounded
timeout event transfers from the exact warm reference with only the finite-retry TV error.
-/

namespace Ttc.CVScoreSeedExceptionalCost

open MeasureTheory ProbabilityTheory Set
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler
open Ttc.CVGaussianScoreSeedPhaseKernel
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- Projecting an approximate score/seed pair onto its seed coordinate costs no TV. -/
theorem tvLe_seed_of_scoreSeedReference
    {rho : Measure (ScoreSeed n)} {mu : Measure (State n)}
    {c : Real} {eps : ENNReal}
    (h : TVLe rho (scoreSeedReference c mu) eps) :
    TVLe (Measure.map Prod.snd rho) (Measure.map (fun y ↦ c • y) mu) eps := by
  simpa only [map_snd_scoreSeedReference] using h.map measurable_snd

/-- Randomized post-processing of the retained seed also preserves the same finite-retry
error.  This is the form used by the next phase's cost/timeout experiment. -/
theorem tvLe_bind_seed_of_scoreSeedReference
    {F : Type*} [MeasurableSpace F]
    {rho : Measure (ScoreSeed n)} [IsProbabilityMeasure rho]
    {mu : Measure (State n)} [IsProbabilityMeasure mu]
    {c : Real} {eps : ENNReal}
    (h : TVLe rho (scoreSeedReference c mu) eps)
    (Q : Kernel (State n) F) [IsMarkovKernel Q] :
    TVLe
      (sampleFromKernel Q (Measure.map Prod.snd rho))
      (sampleFromKernel Q (Measure.map (fun y ↦ c • y) mu)) eps := by
  letI : IsProbabilityMeasure (Measure.map Prod.snd rho) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  letI : IsProbabilityMeasure (Measure.map (fun y ↦ c • y) mu) :=
    Measure.isProbabilityMeasure_map (by fun_prop : Measurable (fun y : State n ↦ c • y)).aemeasurable
  have hseed := tvLe_seed_of_scoreSeedReference h
  exact hseed.bind_kernel Q

/-- A next-phase timeout bound proved under the exact graph seed transfers to the actual
finite-retry output with one additive TV error. -/
theorem bind_seed_badEvent_le_add
    {F : Type*} [MeasurableSpace F]
    {rho : Measure (ScoreSeed n)} [IsProbabilityMeasure rho]
    {mu : Measure (State n)} [IsProbabilityMeasure mu]
    {c : Real} {eps p : ENNReal}
    (h : TVLe rho (scoreSeedReference c mu) eps)
    (Q : Kernel (State n) F) [IsMarkovKernel Q]
    {Bad : Set F} (hBad : MeasurableSet Bad)
    (href : sampleFromKernel Q (Measure.map (fun y ↦ c • y) mu) Bad ≤ p) :
    sampleFromKernel Q (Measure.map Prod.snd rho) Bad ≤ p + eps := by
  exact (tvLe_bind_seed_of_scoreSeedReference h Q).measure_le_add hBad href

/-- Independent `k`-coordinate replacement of actual augmented samples by their exact
graph references.  The finite-retry errors add, exactly as in the source union bound. -/
theorem tvLe_pi_scoreSeedReference
    {k : Nat} {rho : Fin k → Measure (ScoreSeed n)}
    [∀ j, IsProbabilityMeasure (rho j)]
    {mu : Measure (State n)} [IsProbabilityMeasure mu]
    {c : Real} {retryError : Fin k → ENNReal}
    (h : ∀ j, TVLe (rho j) (scoreSeedReference c mu) (retryError j)) :
    TVLe (Measure.pi rho)
      (Measure.pi (fun _ : Fin k ↦ scoreSeedReference c mu))
      (∑ j, retryError j) := by
  apply tvLe_pi_aux k rho (fun _ : Fin k ↦ scoreSeedReference c mu)
    (fun _ ↦ inferInstance) (fun _ ↦ ?_) retryError h
  exact Measure.isProbabilityMeasure_map (by fun_prop : Measurable
    (fun y : State n ↦ (y, c • y))).aemeasurable

/-- Constant-error specialization: `k` independently restarted augmented samples spend
exactly `k * retryError` of the global replacement budget. -/
theorem tvLe_pi_scoreSeedReference_const
    {k : Nat} {rho : Fin k → Measure (ScoreSeed n)}
    [∀ j, IsProbabilityMeasure (rho j)]
    {mu : Measure (State n)} [IsProbabilityMeasure mu]
    {c : Real} {retryError : ENNReal}
    (h : ∀ j, TVLe (rho j) (scoreSeedReference c mu) retryError) :
    TVLe (Measure.pi rho)
      (Measure.pi (fun _ : Fin k ↦ scoreSeedReference c mu))
      ((k : ENNReal) * retryError) := by
  have hpi := tvLe_pi_scoreSeedReference (retryError := fun _ : Fin k ↦ retryError) h
  simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hpi

/-- Concrete source-schedule adapter.  The deadline theorem is invoked only on the exact
`2e`-warm seed.  The actual finite-retry pair needs no multiplicative warmness premise;
its timeout probability is the exact-reference bound plus `retryError`.

This avoids multiplying a warm constant across phases.  The price is additive allocation
of the finite-retry errors in the global exceptional-path budget. -/
theorem standard_finiteRetry_nextPhase_badEvent_le
    (hn : 1 ≤ n) {m : Nat} {sigmaSq : Nat → Real}
    (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : Metric.ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m) {cc : Real} (hcc1 : 1 ≤ cc)
    (hcc : cc ≤ 1 + 2 / (n : Real))
    (hsched : sigmaSq (i + 1) = cc * sigmaSq i)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    {rho : Measure (ScoreSeed n)} [IsProbabilityMeasure rho]
    {retryError p : ENNReal}
    (hretry : TVLe rho
      (scoreSeedReference (1 - 1 / (2 * (n : Real)))
        (coolLaw m sigmaSq K i)) retryError)
    {F : Type*} [MeasurableSpace F]
    (Q : Kernel (State n) F) [IsMarkovKernel Q]
    {Bad : Set F} (hBad : MeasurableSet Bad)
    (hdeadline : ∀ nu : Measure (State n),
      IsWarm (ENNReal.ofReal (2 * Real.exp 1)) nu
        (ellGaussianProb K delta (sigmaSq (i + 1))) →
      IsProbabilityMeasure nu → sampleFromKernel Q nu Bad ≤ p) :
    sampleFromKernel Q (Measure.map Prod.snd rho) Bad ≤ p + retryError := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  let refSeed : Measure (State n) :=
    Measure.map Prod.snd (scoreSeedReference c (coolLaw m sigmaSq K i))
  have hrefWarm : IsWarm (ENNReal.ofReal (2 * Real.exp 1)) refSeed
      (ellGaussianProb K delta (sigmaSq (i + 1))) := by
    dsimp only [refSeed, c]
    exact isWarm_snd_scoreSeedReference_standard hn hsigma hK hKc hball hfin hi
      hcc1 hcc hsched hdelta hdeltan
  haveI : IsProbabilityMeasure (coolLaw m sigmaSq K i) :=
    coolLaw_isProbabilityMeasure hsigma hball hfin i
  haveI : IsProbabilityMeasure
      (scoreSeedReference c (coolLaw m sigmaSq K i)) :=
    Measure.isProbabilityMeasure_map (by fun_prop : Measurable
      (fun y : State n ↦ (y, c • y))).aemeasurable
  haveI : IsProbabilityMeasure refSeed :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  haveI : IsProbabilityMeasure (Measure.map Prod.snd rho) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have href : sampleFromKernel Q refSeed Bad ≤ p :=
    hdeadline refSeed hrefWarm inferInstance
  have hseed : TVLe (Measure.map Prod.snd rho) refSeed retryError := by
    exact hretry.map measurable_snd
  exact (hseed.bind_kernel Q).measure_le_add hBad href

theorem standardShrink_ne_zero (hn : 1 ≤ n) :
    1 - 1 / (2 * (n : Real)) ≠ 0 := by
  have hn0 : 0 < (n : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  have hden : 1 < 2 * (n : Real) := by nlinarith
  have hfrac : 1 / (2 * (n : Real)) < 1 := by
    rw [div_lt_one (by positivity)]
    exact hden
  exact ne_of_gt (sub_pos.2 hfrac)

/-- Direct operational-kernel specialization.  Once the finite-retry TV theorem supplies
`hretry` for `gaussianScoreSeedKernel`, the next phase's bounded timeout estimate follows
with no additional semantic adapter and no actual-seed warmness assertion. -/
theorem standard_gaussianScoreSeedKernel_nextPhase_badEvent_le
    (hn : 1 ≤ n) {m : Nat} {sigmaSq : Nat → Real}
    (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : Metric.ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m) {cc : Real} (hcc1 : 1 ≤ cc)
    (hcc : cc ≤ 1 + 2 / (n : Real))
    (hsched : sigmaSq (i + 1) = cc * sigmaSq i)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    {rhoSeed : Measure (State n)} [IsProbabilityMeasure rhoSeed]
    {s : Real} {steps : Nat → Nat} {L : Nat}
    {retryError p : ENNReal}
    (hretry : TVLe
      (sampleFromKernel
        (gaussianScoreSeedKernel K hK delta s
          (1 - 1 / (2 * (n : Real))) hdelta
          (standardShrink_ne_zero hn) steps L) rhoSeed)
      (scoreSeedReference (1 - 1 / (2 * (n : Real)))
        (coolLaw m sigmaSq K i)) retryError)
    {F : Type*} [MeasurableSpace F]
    (Q : Kernel (State n) F) [IsMarkovKernel Q]
    {Bad : Set F} (hBad : MeasurableSet Bad)
    (hdeadline : ∀ nu : Measure (State n),
      IsWarm (ENNReal.ofReal (2 * Real.exp 1)) nu
        (ellGaussianProb K delta (sigmaSq (i + 1))) →
      IsProbabilityMeasure nu → sampleFromKernel Q nu Bad ≤ p) :
    sampleFromKernel Q
        (Measure.map Prod.snd
          (sampleFromKernel
            (gaussianScoreSeedKernel K hK delta s
              (1 - 1 / (2 * (n : Real))) hdelta
              (standardShrink_ne_zero hn) steps L) rhoSeed)) Bad
      ≤ p + retryError := by
  apply standard_finiteRetry_nextPhase_badEvent_le hn hsigma hK hKc hball hfin hi
    hcc1 hcc hsched hdelta hdeltan hretry Q hBad hdeadline

#print axioms tvLe_seed_of_scoreSeedReference
#print axioms tvLe_bind_seed_of_scoreSeedReference
#print axioms bind_seed_badEvent_le_add
#print axioms tvLe_pi_scoreSeedReference
#print axioms tvLe_pi_scoreSeedReference_const
#print axioms standard_finiteRetry_nextPhase_badEvent_le
#print axioms standardShrink_ne_zero
#print axioms standard_gaussianScoreSeedKernel_nextPhase_badEvent_le

end Ttc.CVScoreSeedExceptionalCost
