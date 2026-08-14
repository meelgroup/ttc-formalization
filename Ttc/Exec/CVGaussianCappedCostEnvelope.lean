import Ttc.Exec.CVGaussianCappedCostedSchedule
import Ttc.Exec.CVGaussianWarmFallbackAnalytic

/-! Active-phase expected cost for the capped Gaussian schedule. -/

namespace Ttc.CVGaussianCappedCostEnvelope

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVGaussianWarmFallbackCostedPhaseKernel
open Ttc.CVGaussianCappedCostedSchedule
open Ttc.CVGaussianWarmFallbackAnalytic
open Ttc.CVConcreteAugmentedRetryCutoffBudget
open Ttc.GenericCostedPhaseCertificate
open Ttc.CVGaussianWarmFallbackOperational
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVSeedProjectedDependence
open scoped ENNReal Classical

variable {E : Type*} [MeasurableSpace E]

/-- Every incoming state marginal of a costed execution is the corresponding marginal
of its cost-erased Markov path. -/
theorem stateMarginal_costed_eq_eval_uncosted
    (Q : Nat → Kernel E (ENNReal × E)) [∀ i, IsMarkovKernel (Q i)]
    (P : Nat → Kernel E E) [∀ i, IsMarkovKernel (P i)]
    (mu0 : Measure E) [IsProbabilityMeasure mu0]
    (hforget : ∀ i x, Measure.map Prod.snd (Q i x) = P i x) (i : Nat) :
    stateMarginal Q mu0 i =
      Measure.map (fun omega : Nat → E ↦ omega i)
        (inhomogeneousPathMeasure P mu0) := by
  have hpath := Ttc.SequentialCostedPathLumping.map_statePath_execution
    Q P mu0 hforget
  unfold stateMarginal oneRunLaw
  calc
    Measure.map (fun omega : Nat → ENNReal × E ↦ (omega i).2)
        (Ttc.SequentialCost.execution Q mu0) =
        Measure.map (fun omega : Nat → E ↦ omega i)
          (Measure.map (Ttc.SequentialCostedPathLumping.pathMap Prod.snd)
            (Ttc.SequentialCost.execution Q mu0)) := by
              rw [Measure.map_map (measurable_pi_apply i)
                (Ttc.SequentialCostedPathLumping.measurable_pathMap measurable_snd)]
              rfl
    _ = _ := by rw [hpath]

/-- The seed marginal seen by active cost accounting is literally the last-seed law
already controlled by `SeedProjectedOperational.last_seed_warm`. -/
theorem map_seed_stateMarginal_eq_historyLastSeed
    {Seed : Type*} [MeasurableSpace Seed]
    (Q : Nat → Kernel E (ENNReal × E)) [∀ i, IsMarkovKernel (Q i)]
    (P : Nat → Kernel E E) [∀ i, IsMarkovKernel (P i)]
    (mu0 : Measure E) [IsProbabilityMeasure mu0]
    (seed : E → Seed) (hseed : Measurable seed)
    (hforget : ∀ i x, Measure.map Prod.snd (Q i x) = P i x) (i : Nat) :
    Measure.map seed (stateMarginal Q mu0 i) =
      ((inhomogeneousPathMeasure P mu0).map (Preorder.frestrictLe i)).map
        (fun h ↦ seed (h ⟨i, Finset.mem_Iic.2 le_rfl⟩)) := by
  rw [stateMarginal_costed_eq_eval_uncosted Q P mu0 hforget i]
  rw [Measure.map_map hseed (measurable_pi_apply i)]
  rw [Measure.map_map
    (by fun_prop : Measurable
      (fun h : Finset.Iic i → E ↦ seed (h ⟨i, Finset.mem_Iic.2 le_rfl⟩)))
    (Preorder.measurable_frestrictLe i)]
  rfl

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- On an active phase, warmth of the incoming seed marginal is exactly the hypothesis
needed by the Gaussian retry-cost theorem.  The retry's killed current submeasure
preserves that same (noncompounding) warm constant. -/
theorem lintegral_stepMean_costedActive_gaussian_le_referenceEnvelope
    (hn : 2 ≤ n) (m i : Nat) (hi : i + 1 < m)
    {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    {q delta sigma R c : Real} (hq : 1 < q)
    (hdelta : 0 < delta) (hsigma : 0 < sigma) (hc : c ≠ 0)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    (hdeltaq : delta ≤ sigma / (max 8 (2 * q) * Real.sqrt n))
    (hR : 0 ≤ R) (hRsigma : R ≤ q * sigma * Real.sqrt n)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (steps : Nat → Nat) (L : Nat)
    (fallback : Measure (ScoreSeed n)) [IsProbabilityMeasure fallback]
    (tail : Nat → Measure (ScoreSeed n)) [∀ j, IsProbabilityMeasure (tail j)]
    (rho : Measure (ScoreSeed n)) [IsProbabilityMeasure rho]
    [IsProbabilityMeasure (ellGaussianProb K delta (sigma ^ 2))]
    {M : ENNReal} (hMtop : M ≠ ⊤)
    (hwarm : IsWarm M (Measure.map Prod.snd rho)
      (ellGaussianProb K delta (sigma ^ 2))) :
    (∫⁻ x, Ttc.SequentialCost.stepMean
      (costedStateScheduleFromSeed
        (costedActiveReferenceTailSchedule m
          (fun _ ↦ gaussianWarmFallbackCostedPhaseKernel K hK delta (sigma ^ 2) c
            hdelta hc steps L fallback) tail)) i x ∂rho) ≤
      ENNReal.ofReal (retryReferenceMeanEnvelope M.toReal steps L) := by
  letI : IsProbabilityMeasure (Measure.map Prod.snd rho) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  let pi : Measure (State n) := ellGaussianProb K delta (sigma ^ 2)
  letI : IsProbabilityMeasure pi := by
    dsimp only [pi]
    infer_instance
  have hwarm' : IsWarm (ENNReal.ofReal M.toReal) (Measure.map Prod.snd rho) pi := by
    rw [ENNReal.ofReal_toReal hMtop]
    exact hwarm
  have hkilled : ∀ j, j < L → IsWarm (ENNReal.ofReal M.toReal)
      (Ttc.FiniteContinuingRetryExpectedCost.runningCurrent
        (Ttc.CVGaussianAugmentedSelectiveTV.augmentedMarginalOf K hK delta
          (sigma ^ 2) c hdelta hc steps
          (Measure.map (Ttc.CVGaussianScoreSeedPhaseKernel.seedEmbedding c)
            (Measure.map Prod.snd rho)) j)) pi := by
    intro j _hj
    exact isWarm_runningCurrent_augmentedMarginalOf_gaussian hK hdelta hc
      (Measure.map Prod.snd rho) hwarm' steps j
  have hmain :=
    lintegral_stepMean_gaussianWarmFallbackCostedPhaseKernel_le_referenceEnvelope
      hn hK hKc hball hq hdelta hsigma hc hdeltan hdeltaq hR hRsigma hKR
      steps L fallback rho pi rfl (ENNReal.toReal_nonneg) hkilled
  simpa only [Ttc.SequentialCost.stepMean, costedStateScheduleFromSeed,
    costedActiveReferenceTailSchedule, if_pos hi] using hmain

/-- The operational last-seed warmth supplies the actual incoming-marginal premise of
the active Gaussian cost theorem.  Thus cost accounting does not require a second,
duplicated warmness hypothesis. -/
theorem phaseMean_costedActive_gaussian_le_of_operational
    (hn : 2 ≤ n) (m i : Nat) (hi : i + 1 < m)
    {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (q R : Real) (hq : 1 < q) (hR : 0 ≤ R)
    (delta sigma shrink : Nat → Real)
    (hdelta : ∀ j, 0 < delta j) (hsigma : ∀ j, 0 < sigma j)
    (hshrink : ∀ j, shrink j ≠ 0)
    (hdeltan : ∀ j, delta j ≤ 1 / (2 * (n : Real)))
    (hdeltaq : ∀ j, j + 1 < m →
      delta j ≤ sigma j / (max 8 (2 * q) * Real.sqrt n))
    (hRsigma : ∀ j, j + 1 < m → R ≤ q * sigma j * Real.sqrt n)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback tail : Nat → Measure (ScoreSeed n))
    [∀ j, IsProbabilityMeasure (fallback j)]
    [∀ j, IsProbabilityMeasure (tail j)]
    [∀ j, IsProbabilityMeasure
      (ellGaussianProb K (delta j) ((sigma j) ^ 2))]
    (mu0 : Measure (ScoreSeed n)) [IsProbabilityMeasure mu0]
    (V : Nat → (Nat → ScoreSeed n) → Real) (eta : Real)
    (hop : SeedProjectedOperational
      (stateScheduleFromSeed
        (activeReferenceTailSchedule m
          (warmFallbackSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
            hdelta hshrink steps retries fallback) tail))
      (activeReferenceTailSchedule m
        (warmFallbackSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
          hdelta hshrink steps retries fallback) tail)
      Prod.snd Prod.fst mu0 V m eta)
    (hpi : ∀ j, hop.pi j = ellGaussianProb K (delta j) ((sigma j) ^ 2))
    (hMtop : hop.warmConst i ≠ ⊤) :
    (∫⁻ x, Ttc.SequentialCost.stepMean
      (costedStateScheduleFromSeed
        (costedActiveReferenceTailSchedule m
          (warmFallbackCostedSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
            hdelta hshrink steps retries fallback) tail)) i x
      ∂stateMarginal
        (costedStateScheduleFromSeed
          (costedActiveReferenceTailSchedule m
            (warmFallbackCostedSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
              hdelta hshrink steps retries fallback) tail)) mu0 i) ≤
      ENNReal.ofReal
        (retryReferenceMeanEnvelope (hop.warmConst i).toReal (steps i) (retries i)) := by
  let P := stateScheduleFromSeed
    (activeReferenceTailSchedule m
      (warmFallbackSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
        hdelta hshrink steps retries fallback) tail)
  let QR := costedStateScheduleFromSeed
    (costedActiveReferenceTailSchedule m
      (warmFallbackCostedSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
        hdelta hshrink steps retries fallback) tail)
  have hforget : ∀ j z, Measure.map Prod.snd (QR j z) = P j z := by
    intro j z
    exact map_snd_costedStateActiveReferenceTailSchedule m
      (warmFallbackSchedule K hK delta (fun l ↦ (sigma l) ^ 2) shrink
        hdelta hshrink steps retries fallback)
      (warmFallbackCostedSchedule K hK delta (fun l ↦ (sigma l) ^ 2) shrink
        hdelta hshrink steps retries fallback)
      tail
      (fun l x ↦ map_snd_gaussianWarmFallbackCostedPhaseKernel hK
        (delta l) ((sigma l) ^ 2) (shrink l) (hdelta l) (hshrink l)
        (steps l) (retries l) (fallback l) x) j z
  have hwarm := hop.last_seed_warm i
  have hmarg := map_seed_stateMarginal_eq_historyLastSeed QR P mu0 Prod.snd
    measurable_snd hforget i
  rw [← hmarg] at hwarm
  rw [hpi i] at hwarm
  let rho := stateMarginal QR mu0 i
  letI : IsProbabilityMeasure rho := by
    dsimp only [rho, stateMarginal]
    letI : IsProbabilityMeasure (oneRunLaw QR mu0) := by
      unfold oneRunLaw
      infer_instance
    exact Measure.isProbabilityMeasure_map
      (measurable_snd.comp (measurable_pi_apply i)).aemeasurable
  have hlocal := lintegral_stepMean_costedActive_gaussian_le_referenceEnvelope
    hn m i hi hK hKc hball hq (hdelta i) (hsigma i) (hshrink i)
    (hdeltan i) (hdeltaq i hi) hR (hRsigma i hi) hKR (steps i) (retries i)
    (fallback i) tail rho hMtop hwarm
  simpa only [P, QR, rho, warmFallbackCostedSchedule,
    Ttc.SequentialCost.stepMean, costedStateScheduleFromSeed,
    costedActiveReferenceTailSchedule, if_pos hi] using hlocal

#print axioms stateMarginal_costed_eq_eval_uncosted
#print axioms map_seed_stateMarginal_eq_historyLastSeed
#print axioms lintegral_stepMean_costedActive_gaussian_le_referenceEnvelope
#print axioms phaseMean_costedActive_gaussian_le_of_operational

end Ttc.CVGaussianCappedCostEnvelope
