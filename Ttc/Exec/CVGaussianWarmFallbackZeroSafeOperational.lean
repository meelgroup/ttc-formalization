import Ttc.Exec.CVGaussianWarmFallbackZeroSafe
import Ttc.Exec.CVGaussianWarmFallbackOperational

/-! Explicit operational package for the zero-safe Gaussian warm-fallback phase. -/

namespace Ttc.CVGaussianWarmFallbackZeroSafeOperational

open MeasureTheory ProbabilityTheory Metric Set Pointwise
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryGaussian
open Ttc.FiniteContinuingRetryGaussianAugmentedPhase
open Ttc.FiniteContinuingRetryGaussianAugmentedPhase
open Ttc.FiniteContinuingRetryRandomFallback
open Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.CVGaussianWarmFallbackPhaseKernel
open Ttc.CVGaussianWarmFallbackOperational
open Ttc.CVGaussianWarmFallbackAnalytic
open Ttc.CVGaussianWarmFallbackZeroSafe
open Ttc.CVGaussianAugmentedSelectiveTV
open Ttc.CVCombinedContinuingAccept
open Ttc.CVIdealCombinedAccepted
open Ttc.CVContinuingRetryParameters
open Ttc.CVSeedProjectedDependence
open Ttc.CVScoreSeedPhaseKernel
open scoped ENNReal Classical BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

noncomputable def zeroSafeAcceptedBudget (L : Nat) (warmBudget : Nat → ENNReal)
    (i : Nat) : ENNReal :=
  (L : ENNReal) * (((16 : ENNReal) * ENNReal.ofReal (2 * Real.exp 1)) * warmBudget i)

noncomputable def zeroSafeMixError (m : Nat) (eps : Real) : ENNReal :=
  32 * continuingZeta m eps +
    (continuingEta m eps + continuingContraction ^ explicitContinuingRetries m eps)

theorem zeroSafeMixError_ne_top (m : Nat) (eps : Real) :
    zeroSafeMixError m eps ≠ ⊤ := by
  unfold zeroSafeMixError continuingZeta continuingEta continuingContraction
  finiteness

theorem zeroSafeMixError_budget {m : Nat} {eps : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    2 * (zeroSafeMixError m eps).toReal ≤ Ttc.CVCorrected.correctedNu m eps := by
  have htail := continuingContraction_pow_explicitRetries_le_eta
    (m := m) heps heps1
  have hfull := continuing_total_error_toReal_budget_of_tail heps htail
  let e := zeroSafeMixError m eps
  let full := continuingTimeout m eps + 32 * continuingZeta m eps +
    continuingEta m eps + continuingContraction ^ explicitContinuingRetries m eps
  have heTop : e ≠ ⊤ := zeroSafeMixError_ne_top m eps
  have hfullTop : full ≠ ⊤ := by
    dsimp only [full, continuingTimeout, continuingZeta, continuingEta,
      continuingContraction]
    finiteness
  have hle : e ≤ full := by
    calc
      e ≤ continuingTimeout m eps + e := le_add_left le_rfl
      _ = full := by dsimp only [e, full, zeroSafeMixError]; ac_rfl
  have hreal := ENNReal.toReal_mono hfullTop hle
  calc
    2 * e.toReal ≤ 2 * full.toReal := by gcongr
    _ ≤ Ttc.CVCorrected.correctedNu m eps := by
      simpa only [full, add_assoc] using hfull

/-- Fully packaged scalar seed-projected operation.  All finite-retry normalization,
acceptance, contraction, killed-current warmth, and error arithmetic are discharged.
`hmix` is the remaining ordinary distributional speedy mixing theorem at the displayed
deadline. -/
noncomputable def seedProjectedOperational_gaussianWarmFallback_zeroSafe
    (hn : 1 ≤ n) {sigmaSq : Nat → Real} (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : Metric.ball (0 : State n) 1 ⊆ K) (hKvol : volume K ≠ ⊤)
    {cc : Real} (hcc1 : 1 ≤ cc) (hcc : cc ≤ 1 + 2 / (n : Real))
    (hsched : ∀ i, sigmaSq (i + 1) = cc * sigmaSq i)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    (deadline : Nat → ENNReal → Nat)
    (V : Nat → (Nat → ScoreSeed n) → Real) (m : Nat) (eps : Real)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)]
    (fallbackBudget warmBudget : Nat → ENNReal)
    (hfallback : ∀ i, IsWarm (fallbackBudget i) (Measure.map Prod.snd (fallback i))
      (ellGaussianProb K delta (sigmaSq (i + 1))))
    (hgrowth : ∀ i,
      zeroSafeAcceptedBudget (explicitContinuingRetries m eps) warmBudget i +
          fallbackBudget i ≤ warmBudget (i + 1))
    (mu0 : Measure (ScoreSeed n)) [IsProbabilityMeasure mu0]
    (hstart : IsWarm (warmBudget 0) (Measure.map Prod.snd mu0)
      (ellGaussianProb K delta (sigmaSq 0)))
    (tau : Nat → Measure (ScoreSeed n)) [∀ i, IsProbabilityMeasure (tau i)]
    (htau : ∀ i, tau i = scoreSeedReference (1 - 1 / (2 * (n : Real)))
      (Measure.map (combinedOutput (1 - 1 / (2 * (n : Real))))
        (condOn (SpeedyRejection.proposal (ellGaussianProb K delta (sigmaSq i)))
          (combinedAccept K (1 - 1 / (2 * (n : Real))) (sigmaSq i)))))
    (hmix : ∀ i (nu : Measure (State n)),
      IsWarm ((2 * warmBudget i) / continuingEta m eps) nu
          (ellGaussianProb K delta (sigmaSq i)) → IsProbabilityMeasure nu →
        TVLe (sampleFromKernel
          (iteratedKernel (lazy (speedyMetropolisGaussian K delta (sigmaSq i)))
            (deadline i ((2 * warmBudget i) / continuingEta m eps))) nu)
          (ellGaussianProb K delta (sigmaSq i)) (continuingZeta m eps))
    (u : (i : Nat) → (Finset.Iic i → ScoreSeed n) → Real)
    (v : Nat → State n → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i,
      accuracyU
          (inhomogeneousPathMeasure
            (stateScheduleFromSeed
              (warmFallbackSchedule K hK (fun _ ↦ delta) sigmaSq
                (fun _ ↦ 1 - 1 / (2 * (n : Real))) (fun _ ↦ hdelta)
                (fun _ ↦ by
                  have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
                  have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
                    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
                    linarith
                  linarith)
                (fun i _ ↦ deadline i ((2 * warmBudget i) / continuingEta m eps))
                (fun _ ↦ explicitContinuingRetries m eps) fallback)) mu0)
          V (Ttc.CVCorrected.correctedAlpha m eps) i =
        fun omega ↦ u i (Preorder.frestrictLe i omega))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (omega (i + 1)).1) :
    SeedProjectedOperational
      (stateScheduleFromSeed
        (warmFallbackSchedule K hK (fun _ ↦ delta) sigmaSq
          (fun _ ↦ 1 - 1 / (2 * (n : Real))) (fun _ ↦ hdelta)
          (fun _ ↦ by
            have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
            have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
              rw [div_le_div_iff₀ (by positivity) (by norm_num)]
              linarith
            linarith)
          (fun i _ ↦ deadline i ((2 * warmBudget i) / continuingEta m eps))
          (fun _ ↦ explicitContinuingRetries m eps) fallback))
      (warmFallbackSchedule K hK (fun _ ↦ delta) sigmaSq
        (fun _ ↦ 1 - 1 / (2 * (n : Real))) (fun _ ↦ hdelta)
        (fun _ ↦ by
          have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
          have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]
            linarith
          linarith)
        (fun i _ ↦ deadline i ((2 * warmBudget i) / continuingEta m eps))
        (fun _ ↦ explicitContinuingRetries m eps) fallback)
      Prod.snd Prod.fst mu0 V m eps := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hc0 : 0 < c := by
    have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
    have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    dsimp [c]
    linarith
  let steps : Nat → Nat → Nat := fun i _ ↦
    deadline i ((2 * warmBudget i) / continuingEta m eps)
  let retries : Nat → Nat := fun _ ↦ explicitContinuingRetries m eps
  let acceptedBudget : Nat → ENNReal :=
    zeroSafeAcceptedBudget (explicitContinuingRetries m eps) warmBudget
  let mixError : Nat → ENNReal := fun _ ↦ zeroSafeMixError m eps
  apply seedProjectedOperational_of_warmFallback K hK (fun _ ↦ delta) sigmaSq
    (fun _ ↦ c) (fun _ ↦ hdelta) (fun _ ↦ hc0.ne') steps retries fallback mu0 V
    m eps (fun i ↦ ellGaussianProb K delta (sigmaSq i)) tau warmBudget acceptedBudget
    fallbackBudget mixError hstart
  · intro i rho hrho hwrho
    simpa only [acceptedBudget, zeroSafeAcceptedBudget, retries, steps, c] using
      isWarm_seed_acceptedOutputSubmeasure_gaussian hn hsigma hK hKc hball hKvol
        (m := i + 2) (i := i) (by omega) hcc1 hcc (hsched i) hdelta hdeltan
        hwrho (steps i) (retries i)
  · exact hfallback
  · intro i
    simpa only [acceptedBudget, retries] using hgrowth i
  · intro i
    exact zeroSafeMixError_ne_top m eps
  · intro i rho hrho hwrho
    letI : IsProbabilityMeasure rho := hwrho
    have hM0 : ellGaussianMeasure K delta (sigmaSq i) Set.univ ≠ 0 :=
      ellGaussianMeasure_univ_ne_zero_of_ball hK hKc hball hc0
        (by
          dsimp [c]
          have : 0 < 1 / (2 * (n : Real)) := by positivity
          linarith) hdelta (by simpa [c] using hdeltan) (hsigma i)
    have hMtop : ellGaussianMeasure K delta (sigmaSq i) Set.univ ≠ ⊤ :=
      ellGaussianMeasure_univ_ne_top (hsigma i) K delta hKvol
    letI : IsProbabilityMeasure (ellGaussianProb K delta (sigmaSq i)) :=
      isProbabilityMeasure_ellGaussianProb hM0 hMtop
    letI : IsProbabilityMeasure (Measure.map (seedEmbedding c) rho) :=
      Measure.isProbabilityMeasure_map (measurable_seedEmbedding c).aemeasurable
    change TVLe
      (sampleFromKernel
        (gaussianWarmFallbackPhaseKernel K hK delta (sigmaSq i) c hdelta hc0.ne'
          (steps i) (retries i) (fallback i)) rho)
      (tau i) (mixError i)
    rw [sampleFrom_gaussianWarmFallbackPhaseKernel hK delta (sigmaSq i) c hdelta hc0.ne'
      (steps i) (retries i) (fallback i) rho, htau i]
    apply tvLe_gaussianWarmFallbackPhase_selective_zeroSafe hK hdelta hc0.ne'
      (deadline i) (Measure.map (seedEmbedding c) rho) (fallback i) (retries i)
      (pi := ellGaussianProb K delta (sigmaSq i))
      (tau := ellGaussianProb K delta (sigmaSq i))
      (M := 2 * warmBudget i) (eta := continuingEta m eps)
      (zeta := continuingZeta m eps)
    · exact ENNReal.ofReal_ne_zero_iff.mpr (continuingShare_pos heps)
    · intro j
      simpa only [steps, c] using
        isWarm_runningCurrent_augmentedMarginalOf_gaussian hK hdelta hc0.ne'
          rho hrho (steps i) j
    · exact hmix i
    · exact eighth_le_ellGaussianProb_combinedAccept hn hK hKc hball hKvol hdelta
        hdeltan (hsigma i)
    · exact continuingZeta_le_sixteenth heps heps1
  · exact hu
  · exact hv
  · simpa only [steps, retries, c] using hU
  · exact hV
  · intro i
    exact zeroSafeMixError_budget heps heps1

#print axioms zeroSafeMixError_budget
#print axioms seedProjectedOperational_gaussianWarmFallback_zeroSafe

end Ttc.CVGaussianWarmFallbackZeroSafeOperational
