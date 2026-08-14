import Ttc.Exec.CVGaussianWarmFallbackIndependentCertificate
import Ttc.Exec.CVScoreSeedReferenceSchedule

/-!
# Active Gaussian phases with an exact reference tail

Corrected dependence is stated for every natural phase although the estimator reads only
finitely many phases.  This file extends the active Gaussian warm-fallback family by an
input-forgetting exact reference kernel.  Consequently accepted-sublaw warmth and
selective Gaussian mixing are required only when `i + 1 < m`; tail warmth and mixing are
both exact.
-/

namespace Ttc.CVGaussianWarmFallbackCappedOperational

open MeasureTheory ProbabilityTheory Set
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVCorrected
open Ttc.CVSequentialPhaseSampler
open Ttc.CVSeedProjectedDependence
open Ttc.CVFiniteAugmentedSeedOperational
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVGaussianWarmFallbackOperational
open Ttc.CVIndependentStreamDependence
open scoped ENNReal Classical

variable {Score Seed : Type*} [MeasurableSpace Score] [MeasurableSpace Seed]

/-- Use the operational kernel on active phases and resample the next exact reference
law on the irrelevant infinite tail. -/
noncomputable def activeReferenceTailSchedule
    (m : Nat) (Q : Nat → Kernel Seed (Score × Seed))
    (tail : Nat → Measure (Score × Seed)) :
    Nat → Kernel Seed (Score × Seed) := fun i ↦
  if i + 1 < m then Q i else Kernel.const Seed (tail (i + 1))

instance activeReferenceTailSchedule.isMarkovKernel
    (m : Nat) (Q : Nat → Kernel Seed (Score × Seed))
    [∀ i, IsMarkovKernel (Q i)]
    (tail : Nat → Measure (Score × Seed))
    [∀ i, IsProbabilityMeasure (tail i)] (i : Nat) :
    IsMarkovKernel (activeReferenceTailSchedule m Q tail i) := by
  unfold activeReferenceTailSchedule
  split <;> infer_instance

/-- Output reference family: the Gaussian target on active phases and the exact tail law
after the active range. -/
noncomputable def activeReferenceTarget
    (m : Nat) (tau tail : Nat → Measure (Score × Seed)) :
    Nat → Measure (Score × Seed) := fun i ↦
  if i + 1 < m then tau i else tail (i + 1)

instance activeReferenceTarget.isProbabilityMeasure
    (m : Nat) (tau tail : Nat → Measure (Score × Seed))
    [∀ i, IsProbabilityMeasure (tau i)] [∀ i, IsProbabilityMeasure (tail i)] (i : Nat) :
    IsProbabilityMeasure (activeReferenceTarget m tau tail i) := by
  unfold activeReferenceTarget
  split <;> infer_instance

/-- Mixing error is identically zero on the reference tail. -/
def activeReferenceMixError (m : Nat) (eps : Nat → ENNReal) : Nat → ENNReal :=
  fun i ↦ if i + 1 < m then eps i else 0

theorem sampleFrom_activeReferenceTailSchedule_inactive
    (m : Nat) (Q : Nat → Kernel Seed (Score × Seed))
    (tail : Nat → Measure (Score × Seed)) (i : Nat)
    (hi : ¬ i + 1 < m) (rho : Measure Seed) [IsProbabilityMeasure rho] :
    sampleFromKernel (activeReferenceTailSchedule m Q tail i) rho = tail (i + 1) := by
  rw [activeReferenceTailSchedule, if_neg hi]
  unfold sampleFromKernel
  rw [Measure.const_comp]
  simp

/-- The all-natural operational package obtained from active-only warmth and mixing.

`htailSeed` identifies the seed marginal of each exact tail reference.  No warmness or
mixing premise is required on inactive phases. -/
noncomputable def seedProjectedOperational_activeReferenceTail
    (m : Nat) (Q : Nat → Kernel Seed (Score × Seed)) [∀ i, IsMarkovKernel (Q i)]
    (tail : Nat → Measure (Score × Seed)) [∀ i, IsProbabilityMeasure (tail i)]
    (mu0 : Measure (Score × Seed)) [IsProbabilityMeasure mu0]
    (V : Nat → (Nat → Score × Seed) → Real) (eta : Real)
    (pi : Nat → Measure Seed) (tau : Nat → Measure (Score × Seed))
    [∀ i, IsProbabilityMeasure (tau i)]
    (warmBudget mixError : Nat → ENNReal)
    (hwarmOne : ∀ i, 1 ≤ warmBudget i)
    (hstart : IsWarm (warmBudget 0) (Measure.map Prod.snd mu0) (pi 0))
    (hactiveStep : ∀ i, i + 1 < m → ∀ (rho : Measure Seed),
      IsProbabilityMeasure rho → IsWarm (warmBudget i) rho (pi i) →
        IsWarm (warmBudget (i + 1))
          (Measure.map Prod.snd (sampleFromKernel (Q i) rho)) (pi (i + 1)))
    (htailSeed : ∀ i, Measure.map Prod.snd (tail i) = pi i)
    (hactiveMixTop : ∀ i, i + 1 < m → mixError i ≠ ⊤)
    (hactiveMix : ∀ i, i + 1 < m → ∀ (rho : Measure Seed),
      IsWarm (2 * warmBudget i) rho (pi i) → IsProbabilityMeasure rho →
        TVLe (sampleFromKernel (Q i) rho) (tau i) (mixError i))
    (u : (i : Nat) → (Finset.Iic i → Score × Seed) → Real)
    (v : Nat → Score → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i,
      accuracyU
          (inhomogeneousPathMeasure
            (stateScheduleFromSeed (activeReferenceTailSchedule m Q tail)) mu0)
          V (correctedAlpha m eta) i =
        fun omega ↦ u i (Preorder.frestrictLe i omega))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (omega (i + 1)).1)
    (hbudget : ∀ i, i + 1 < m →
      2 * (mixError i).toReal ≤ correctedNu m eta) :
    SeedProjectedOperational
      (stateScheduleFromSeed (activeReferenceTailSchedule m Q tail))
      (activeReferenceTailSchedule m Q tail) Prod.snd Prod.fst mu0 V m eta := by
  apply seedProjectedOperational_of_recurrence
    (activeReferenceTailSchedule m Q tail) mu0 V m eta pi
    (activeReferenceTarget m tau tail) warmBudget
    (activeReferenceMixError m mixError) hstart
  · intro i rho hprob hwarm
    by_cases hi : i + 1 < m
    · simpa only [activeReferenceTailSchedule, if_pos hi] using
        hactiveStep i hi rho hprob hwarm
    · letI : IsProbabilityMeasure rho := hprob
      rw [sampleFrom_activeReferenceTailSchedule_inactive m Q tail i hi rho,
        htailSeed (i + 1)]
      exact (IsWarm.refl (pi (i + 1))).mono (hwarmOne (i + 1))
  · intro i
    unfold activeReferenceMixError
    by_cases hi : i + 1 < m
    · simpa only [if_pos hi] using hactiveMixTop i hi
    · simp [hi]
  · intro i rho hwarm hprob
    by_cases hi : i + 1 < m
    · simpa only [activeReferenceTailSchedule, activeReferenceTarget,
        activeReferenceMixError, if_pos hi] using hactiveMix i hi rho hwarm hprob
    · letI : IsProbabilityMeasure rho := hprob
      rw [sampleFrom_activeReferenceTailSchedule_inactive m Q tail i hi rho]
      simp only [activeReferenceTarget, activeReferenceMixError, if_neg hi]
      exact TVLe.refl _
  · exact hu
  · exact hv
  · exact hU
  · exact hV
  · intro i
    unfold activeReferenceMixError
    by_cases hi : i + 1 < m
    · simpa only [if_pos hi] using hbudget i hi
    · simp only [if_neg hi, ENNReal.toReal_zero, mul_zero]
      unfold correctedNu
      have halpha : 0 ≤ correctedAlpha m eta := by
        unfold correctedAlpha
        positivity
      exact div_nonneg (sq_nonneg eta)
        (mul_nonneg
          (mul_nonneg (by norm_num) (pow_nonneg halpha 4))
          (by positivity))

/-- Lift any scalar seed-projected operational proof to the block interface for `k`
independent complete paths.  Only the block statistic factorisations are additional. -/
noncomputable def independentStreamOperational_of_seedProjected
    {k m : Nat} {Q : Nat → Kernel Seed (Score × Seed)} [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (Score × Seed)} [IsProbabilityMeasure mu0]
    {Vscalar : Nat → (Nat → Score × Seed) → Real} {eta : Real}
    (hop : SeedProjectedOperational (stateScheduleFromSeed Q) Q Prod.snd Prod.fst
      mu0 Vscalar m eta)
    (V : Nat → (Fin k → Nat → Score × Seed) → Real)
    (u : (i : Nat) → (Fin k → Finset.Iic i → Score × Seed) → Real)
    (v : Nat → (Fin k → Score × Seed) → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i,
      accuracyU (independentPathLaw k (stateScheduleFromSeed Q) mu0) V
          (correctedAlpha m eta) i =
        fun omega ↦ u i (fun l ↦ Preorder.frestrictLe i (omega l)))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (fun l ↦ omega l (i + 1)))
    (hbudget : ∀ i,
      (k : Real) * (2 * (hop.mixError i).toReal) ≤ correctedNu m eta) :
    IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd mu0 V m eta where
  measurable_seed := measurable_snd
  factor := stateScheduleFromSeed_factor Q
  pi := hop.pi
  tau := hop.tau
  tau_prob := hop.tau_prob
  warmConst := hop.warmConst
  mixError := hop.mixError
  mixError_ne_top := hop.mixError_ne_top
  u := u
  v := v
  measurable_u := hu
  measurable_v := hv
  U_eq := hU
  V_eq := hV
  last_seed_warm := hop.last_seed_warm
  distributional_mixing := hop.distributional_mixing
  dependence_budget := hbudget

/-! Gaussian specialization. -/

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev GaussianScoreSeed (n : Nat) := State n × State n

/-- Source analytic accepted-sublaw warmth, now exposed in exactly the active-only shape
needed by the capped operational constructor. -/
theorem activeAcceptedWarm_gaussian
    (hn : 1 ≤ n) {m : Nat} {sigmaSq : Nat → Real}
    (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : Metric.ball (0 : State n) 1 ⊆ K) (hKvol : volume K ≠ ⊤)
    {cc : Real} (hcc1 : 1 ≤ cc) (hcc : cc ≤ 1 + 2 / (n : Real))
    (hsched : ∀ i, i + 1 < m → sigmaSq (i + 1) = cc * sigmaSq i)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    (warmBudget : Nat → ENNReal) (steps : Nat → Nat → Nat) (retries : Nat → Nat) :
    ∀ i, i + 1 < m → ∀ (rho : Measure (State n)), IsProbabilityMeasure rho →
      IsWarm (warmBudget i) rho (ellGaussianProb K delta (sigmaSq i)) →
        IsWarm
          ((retries i : ENNReal) *
            (((16 : ENNReal) * ENNReal.ofReal (2 * Real.exp 1)) * warmBudget i))
          (Measure.map Prod.snd
            (Ttc.FiniteContinuingRetryRandomFallback.acceptedOutputSubmeasure
              (Ttc.CVGaussianAugmentedSelectiveTV.augmentedMarginalOf K hK delta
                (sigmaSq i) (1 - 1 / (2 * (n : Real))) hdelta
                (by
                  have hnR : (0 : Real) < n := by
                    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
                  have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
                  have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
                    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
                    linarith
                  linarith)
                (steps i)
                (Measure.map
                  (Ttc.CVGaussianScoreSeedPhaseKernel.seedEmbedding
                    (1 - 1 / (2 * (n : Real)))) rho)
                (retries i))))
          (ellGaussianProb K delta (sigmaSq (i + 1))) := by
  intro i hi rho hprob hwarm
  letI : IsProbabilityMeasure rho := hprob
  exact Ttc.CVGaussianWarmFallbackAnalytic.isWarm_seed_acceptedOutputSubmeasure_gaussian
    hn hsigma hK hKc hball hKvol hi hcc1 hcc (hsched i hi) hdelta hdeltan hwarm
    (steps i) (retries i)

/-- Capped Gaussian warm-fallback operation.  The accepted-sublaw, fallback warmth, and
selective mixing premises are now restricted literally to active indices. -/
noncomputable def gaussianSeedProjectedOperational_activeReferenceTail
    (m : Nat) {K : Set (State n)} (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback tail : Nat → Measure (GaussianScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)]
    [∀ i, IsProbabilityMeasure (tail i)]
    (mu0 : Measure (GaussianScoreSeed n)) [IsProbabilityMeasure mu0]
    (V : Nat → (Nat → GaussianScoreSeed n) → Real) (eta : Real)
    (pi : Nat → Measure (State n)) (tau : Nat → Measure (GaussianScoreSeed n))
    [∀ i, IsProbabilityMeasure (tau i)]
    (warmBudget acceptedBudget fallbackBudget mixError : Nat → ENNReal)
    (hwarmOne : ∀ i, 1 ≤ warmBudget i)
    (hstart : IsWarm (warmBudget 0) (Measure.map Prod.snd mu0) (pi 0))
    (haccepted : ∀ i, i + 1 < m → ∀ (rho : Measure (State n)),
      IsProbabilityMeasure rho → IsWarm (warmBudget i) rho (pi i) →
        IsWarm (acceptedBudget i)
          (Measure.map Prod.snd
            (Ttc.FiniteContinuingRetryRandomFallback.acceptedOutputSubmeasure
              (Ttc.CVGaussianAugmentedSelectiveTV.augmentedMarginalOf K hK
                (delta i) (sigmaSq i) (shrink i) (hdelta i) (hshrink i)
                (retrySteps i) (Measure.map
                  (Ttc.CVGaussianScoreSeedPhaseKernel.seedEmbedding (shrink i))
                  rho) (retries i))))
          (pi (i + 1)))
    (hfallback : ∀ i, i + 1 < m →
      IsWarm (fallbackBudget i) (Measure.map Prod.snd (fallback i)) (pi (i + 1)))
    (hgrowth : ∀ i, i + 1 < m →
      acceptedBudget i + fallbackBudget i ≤ warmBudget (i + 1))
    (htailSeed : ∀ i, Measure.map Prod.snd (tail i) = pi i)
    (hactiveMixTop : ∀ i, i + 1 < m → mixError i ≠ ⊤)
    (hactiveMix : ∀ i, i + 1 < m → ∀ (rho : Measure (State n)),
      IsWarm (2 * warmBudget i) rho (pi i) → IsProbabilityMeasure rho →
        TVLe
          (sampleFromKernel
            (warmFallbackSchedule K hK delta sigmaSq shrink hdelta hshrink
              retrySteps retries fallback i) rho)
          (tau i) (mixError i))
    (u : (i : Nat) → (Finset.Iic i → GaussianScoreSeed n) → Real)
    (v : Nat → State n → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i,
      accuracyU
          (inhomogeneousPathMeasure
            (stateScheduleFromSeed
              (activeReferenceTailSchedule m
                (warmFallbackSchedule K hK delta sigmaSq shrink hdelta hshrink
                  retrySteps retries fallback) tail)) mu0)
          V (correctedAlpha m eta) i =
        fun omega ↦ u i (Preorder.frestrictLe i omega))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (omega (i + 1)).1)
    (hbudget : ∀ i, i + 1 < m →
      2 * (mixError i).toReal ≤ correctedNu m eta) :
    SeedProjectedOperational
      (stateScheduleFromSeed
        (activeReferenceTailSchedule m
          (warmFallbackSchedule K hK delta sigmaSq shrink hdelta hshrink
            retrySteps retries fallback) tail))
      (activeReferenceTailSchedule m
        (warmFallbackSchedule K hK delta sigmaSq shrink hdelta hshrink
          retrySteps retries fallback) tail)
      Prod.snd Prod.fst mu0 V m eta := by
  apply seedProjectedOperational_activeReferenceTail m
    (warmFallbackSchedule K hK delta sigmaSq shrink hdelta hshrink
      retrySteps retries fallback) tail mu0 V eta pi tau warmBudget mixError
    hwarmOne hstart
  · intro i hi rho hprob hrho
    letI : IsProbabilityMeasure rho := hprob
    exact
      (Ttc.CVGaussianWarmFallbackPhaseKernel.isWarm_seed_sampleFrom_gaussianWarmFallbackPhaseKernel
        hK (delta i) (sigmaSq i) (shrink i) (hdelta i) (hshrink i)
        (retrySteps i) (retries i) (fallback i) rho (pi (i + 1))
        (haccepted i hi rho hprob hrho) (hfallback i hi)).mono (hgrowth i hi)
  · exact htailSeed
  · exact hactiveMixTop
  · exact hactiveMix
  · exact hu
  · exact hv
  · exact hU
  · exact hV
  · exact hbudget

#print axioms sampleFrom_activeReferenceTailSchedule_inactive
#print axioms seedProjectedOperational_activeReferenceTail
#print axioms independentStreamOperational_of_seedProjected
#print axioms gaussianSeedProjectedOperational_activeReferenceTail
#print axioms activeAcceptedWarm_gaussian

end Ttc.CVGaussianWarmFallbackCappedOperational
