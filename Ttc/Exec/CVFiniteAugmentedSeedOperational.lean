import Ttc.Exec.CVGaussianScoreSeedPhaseKernel
import Ttc.Exec.CVScoreSeedPhaseKernel
import Ttc.Exec.CVGaussianAugmentedSelectiveTV
import Ttc.Exec.CVFiniteContinuingPhaseDistributional
import Ttc.Volume.CVDirectSequentialWarm

/-!
# Finite-retry augmented phases with a warm seed projection

This file supplies the operational part of the finite-retry `(score, seed)` construction.
Warmness is propagated only for the retained seed.  The estimator is free to read the
score, and no warmness assertion is made for the joint pair law.

The Gaussian specialization deliberately leaves one analytic premise visible: a finite
retry phase must send an incoming warm seed law to a warm outgoing raw-seed marginal.
For the concrete retry machine this is precisely the first-hit raw-seed domination seam;
it is not implied by total-variation closeness of the score law.
-/

namespace Ttc.CVFiniteAugmentedSeedOperational

open MeasureTheory ProbabilityTheory
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVSeedProjectedDependence
open Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.CVGaussianAugmentedSelectiveTV
open Ttc.FiniteContinuingRetryGaussianAugmentedPhase
open Ttc.CVCorrected
open scoped ENNReal Classical

variable {Score Seed : Type*} [MeasurableSpace Score] [MeasurableSpace Seed]

/-- The seed marginal at time `i + 1` is obtained by applying the seed-indexed phase
kernel to the seed marginal at time `i` and then forgetting the new score. -/
theorem map_seed_eval_succ
    (Q : Nat → Kernel Seed (Score × Seed)) [∀ i, IsMarkovKernel (Q i)]
    (mu0 : Measure (Score × Seed)) [IsProbabilityMeasure mu0] (i : Nat) :
    Measure.map Prod.snd
        (Measure.map (fun omega ↦ omega (i + 1))
          (inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0)) =
      Measure.map Prod.snd
        (sampleFromKernel (Q i)
          (Measure.map Prod.snd
            (Measure.map (fun omega ↦ omega i)
              (inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0))) ) := by
  rw [Ttc.CVDirectSequentialWarm.map_eval_inhomogeneousPathMeasure_succ]
  unfold sampleFromKernel stateScheduleFromSeed stateKernelFromSeed
  rw [Arlib.MarkovChains.bind_comap]

/-- Phase-by-phase warmth recurrence for the retained seed marginal.  This is the
projection-valued analogue of the usual inhomogeneous warmness induction. -/
theorem isWarm_seed_eval_of_recurrence
    (Q : Nat → Kernel Seed (Score × Seed)) [∀ i, IsMarkovKernel (Q i)]
    (mu0 : Measure (Score × Seed)) [IsProbabilityMeasure mu0]
    (pi : Nat → Measure Seed) (warmBudget : Nat → ENNReal)
    (hstart : IsWarm (warmBudget 0) (Measure.map Prod.snd mu0) (pi 0))
    (hstep : ∀ i (rho : Measure Seed), IsProbabilityMeasure rho →
      IsWarm (warmBudget i) rho (pi i) →
        IsWarm (warmBudget (i + 1))
          (Measure.map Prod.snd (sampleFromKernel (Q i) rho)) (pi (i + 1))) :
    ∀ i, IsWarm (warmBudget i)
      (Measure.map Prod.snd
        (Measure.map (fun omega ↦ omega i)
          (inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0))) (pi i) := by
  intro i
  induction i with
  | zero =>
      rw [Ttc.CVDirectSequentialWarm.map_eval_inhomogeneousPathMeasure_zero]
      exact hstart
  | succ i ih =>
      rw [map_seed_eval_succ Q mu0 i]
      let rho : Measure Seed :=
        Measure.map Prod.snd
          (Measure.map (fun omega ↦ omega i)
            (inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0))
      letI : IsProbabilityMeasure rho := by
        dsimp [rho]
        letI : IsProbabilityMeasure
            (Measure.map (fun omega ↦ omega i)
              (inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0)) :=
          Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable
        exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
      exact hstep i rho inferInstance ih

/-- Rewriting the seed marginal induction into the exact history-last form consumed by
the LV2 event-conditioned dependence theorem. -/
theorem isWarm_historyLastSeed_of_recurrence
    (Q : Nat → Kernel Seed (Score × Seed)) [∀ i, IsMarkovKernel (Q i)]
    (mu0 : Measure (Score × Seed)) [IsProbabilityMeasure mu0]
    (pi : Nat → Measure Seed) (warmBudget : Nat → ENNReal)
    (hstart : IsWarm (warmBudget 0) (Measure.map Prod.snd mu0) (pi 0))
    (hstep : ∀ i (rho : Measure Seed), IsProbabilityMeasure rho →
      IsWarm (warmBudget i) rho (pi i) →
        IsWarm (warmBudget (i + 1))
          (Measure.map Prod.snd (sampleFromKernel (Q i) rho)) (pi (i + 1)))
    (i : Nat) :
    IsWarm (warmBudget i)
      (((inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0).map
        (Preorder.frestrictLe i)).map
          (fun h ↦ (h ⟨i, Finset.mem_Iic.2 le_rfl⟩).2)) (pi i) := by
  have hw := isWarm_seed_eval_of_recurrence Q mu0 pi warmBudget hstart hstep i
  let lastSeed : (Finset.Iic i → Score × Seed) → Seed :=
    fun h ↦ (h ⟨i, Finset.mem_Iic.2 le_rfl⟩).2
  have hlastSeed : Measurable lastSeed :=
    measurable_snd.comp (measurable_pi_apply _)
  rw [Measure.map_map hlastSeed (Preorder.measurable_frestrictLe i)]
  change IsWarm (warmBudget i)
    (Measure.map (fun omega : Nat → Score × Seed ↦ (omega i).2)
      (inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0)) (pi i)
  have hsnd : Measurable (Prod.snd : Score × Seed → Seed) := measurable_snd
  rw [Measure.map_map hsnd (measurable_pi_apply i)] at hw
  exact hw

/-- Assemble the corrected-accuracy dependence package from a seed warmness recurrence
and distributional phase mixing.  The latter is required only for starts obtained by
conditioning a history event, hence the source-faithful factor `2 * warmBudget i`. -/
noncomputable def seedProjectedOperational_of_recurrence
    (Q : Nat → Kernel Seed (Score × Seed)) [∀ i, IsMarkovKernel (Q i)]
    (mu0 : Measure (Score × Seed)) [IsProbabilityMeasure mu0]
    (V : Nat → (Nat → Score × Seed) → Real) (m : Nat) (eta : Real)
    (pi : Nat → Measure Seed) (tau : Nat → Measure (Score × Seed))
    [∀ i, IsProbabilityMeasure (tau i)]
    (warmBudget mixError : Nat → ENNReal)
    (hstart : IsWarm (warmBudget 0) (Measure.map Prod.snd mu0) (pi 0))
    (hstep : ∀ i (rho : Measure Seed), IsProbabilityMeasure rho →
      IsWarm (warmBudget i) rho (pi i) →
        IsWarm (warmBudget (i + 1))
          (Measure.map Prod.snd (sampleFromKernel (Q i) rho)) (pi (i + 1)))
    (hmixTop : ∀ i, mixError i ≠ ⊤)
    (hmix : ∀ i (rho : Measure Seed),
      IsWarm (2 * warmBudget i) rho (pi i) → IsProbabilityMeasure rho →
        TVLe (sampleFromKernel (Q i) rho) (tau i) (mixError i))
    (u : (i : Nat) → (Finset.Iic i → Score × Seed) → Real)
    (v : Nat → Score → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i,
      accuracyU
          (inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) V
          (Ttc.CVCorrected.correctedAlpha m eta) i =
        fun omega ↦ u i (Preorder.frestrictLe i omega))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (omega (i + 1)).1)
    (hbudget : ∀ i,
      2 * (mixError i).toReal ≤ Ttc.CVCorrected.correctedNu m eta) :
    SeedProjectedOperational (stateScheduleFromSeed Q) Q Prod.snd Prod.fst
      mu0 V m eta where
  measurable_seed := measurable_snd
  measurable_score := measurable_fst
  factor := stateScheduleFromSeed_factor Q
  pi := pi
  tau := tau
  tau_prob := fun _ ↦ inferInstance
  warmConst := warmBudget
  mixError := mixError
  mixError_ne_top := hmixTop
  u := u
  v := v
  measurable_u := hu
  measurable_v := hv
  U_eq := hU
  V_eq := hV
  last_seed_warm := isWarm_historyLastSeed_of_recurrence Q mu0 pi warmBudget hstart hstep
  distributional_mixing := hmix
  dependence_budget := hbudget

variable {n : Nat}
abbrev GaussianState (n : Nat) := EuclideanSpace Real (Fin n)

/-- The concrete finite-retry, no-query-cutoff Gaussian phase schedule. -/
noncomputable def gaussianFiniteScoreSeedSchedule
    (K : Set (GaussianState n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat) :
    Nat → Kernel (GaussianState n) (GaussianState n × GaussianState n) := fun i ↦
  gaussianScoreSeedKernel K hK (delta i) (sigmaSq i) (shrink i)
    (hdelta i) (hshrink i) (retrySteps i) (retries i)

instance gaussianFiniteScoreSeedSchedule.isMarkovKernel
    (K : Set (GaussianState n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat) (i : Nat) :
    IsMarkovKernel (gaussianFiniteScoreSeedSchedule K hK delta sigmaSq shrink
      hdelta hshrink retrySteps retries i) := by
  unfold gaussianFiniteScoreSeedSchedule
  infer_instance

/-- Arbitrary incoming-law identification with the embedded augmented retry marginal.
This is the bridge that lets the selective Gaussian TV theorem discharge the
`distributional_mixing` field of the operational package. -/
theorem sampleFrom_gaussianFiniteScoreSeedSchedule
    (K : Set (GaussianState n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (rho : Measure (GaussianState n)) [IsProbabilityMeasure rho] (i : Nat) :
    sampleFromKernel
        (gaussianFiniteScoreSeedSchedule K hK delta sigmaSq shrink hdelta hshrink
          retrySteps retries i) rho =
      Measure.map Ttc.FiniteContinuingRetry.output
        (augmentedMarginalOf K hK (delta i) (sigmaSq i) (shrink i)
          (hdelta i) (hshrink i) (retrySteps i)
          (Measure.map (seedEmbedding (shrink i)) rho) (retries i)) := by
  let rhoPair := Measure.map (seedEmbedding (shrink i)) rho
  letI : IsProbabilityMeasure rhoPair :=
    Measure.isProbabilityMeasure_map
      (measurable_seedEmbedding (shrink i)).aemeasurable
  unfold gaussianFiniteScoreSeedSchedule gaussianScoreSeedKernel
  rw [Ttc.CVFiniteContinuingPhaseDistributional.sampleFromKernel_map _ Prod.snd
    measurable_snd rho]
  unfold gaussianScoreSeedCostedKernel
  unfold sampleFromKernel
  rw [Arlib.MarkovChains.bind_comap]
  change Measure.map Prod.snd
      (sampleFromKernel
        (augmentedGaussianFinitePhaseCostedKernel K hK (delta i) (sigmaSq i)
          (shrink i) (hdelta i) (hshrink i) (retrySteps i) (retries i)) rhoPair) = _
  unfold augmentedGaussianFinitePhaseCostedKernel
  rw [Ttc.CVFiniteContinuingPhaseDistributional.sampleFromKernel_map _
    augmentedPhaseCostOutput measurable_augmentedPhaseCostOutput rhoPair,
    Measure.map_map measurable_snd measurable_augmentedPhaseCostOutput]
  change Measure.map Ttc.FiniteContinuingRetry.output
      (sampleFromKernel
        (augmentedGaussianRetryStateKernel K hK (delta i) (sigmaSq i) (shrink i)
          (hdelta i) (hshrink i) (retrySteps i) (retries i)) rhoPair) = _
  rw [sampleFrom_augmentedRetryStateKernel_eq_marginalOf]

/-- Cost-recording companion of `gaussianFiniteScoreSeedSchedule`.  The retry count is
finite, but there is no inner query-time cutoff; a later global cutoff can therefore be
charged once without contaminating the warm seed law by an atom. -/
noncomputable def gaussianFiniteScoreSeedCostedSchedule
    (K : Set (GaussianState n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat) :
    Nat → Kernel (GaussianState n)
      (ENNReal × (GaussianState n × GaussianState n)) := fun i ↦
  gaussianScoreSeedCostedKernel K hK (delta i) (sigmaSq i) (shrink i)
    (hdelta i) (hshrink i) (retrySteps i) (retries i)

instance gaussianFiniteScoreSeedCostedSchedule.isMarkovKernel
    (K : Set (GaussianState n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat) (i : Nat) :
    IsMarkovKernel (gaussianFiniteScoreSeedCostedSchedule K hK delta sigmaSq shrink
      hdelta hshrink retrySteps retries i) := by
  unfold gaussianFiniteScoreSeedCostedSchedule
  infer_instance

/-- Exact pointwise erasure of the traced membership-query cost. -/
theorem map_snd_gaussianFiniteScoreSeedCostedSchedule
    (K : Set (GaussianState n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (i : Nat) (x : GaussianState n) :
    Measure.map Prod.snd
        (gaussianFiniteScoreSeedCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
          retrySteps retries i x) =
      gaussianFiniteScoreSeedSchedule K hK delta sigmaSq shrink hdelta hshrink
        retrySteps retries i x := by
  exact map_snd_gaussianScoreSeedCostedKernel hK (delta i) (sigmaSq i) (shrink i)
    (hdelta i) (hshrink i) (retrySteps i) (retries i) x

/-- Gaussian specialization of the operational constructor.  Its `hseedStep` premise is
the exact remaining raw-seed first-hit warmness obligation; all path/history dependence
and LV2 conditioning are discharged here. -/
noncomputable def gaussianFiniteSeedProjectedOperational
    (K : Set (GaussianState n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (mu0 : Measure (GaussianState n × GaussianState n)) [IsProbabilityMeasure mu0]
    (V : Nat → (Nat → GaussianState n × GaussianState n) → Real)
    (m : Nat) (eta : Real)
    (pi : Nat → Measure (GaussianState n))
    (tau : Nat → Measure (GaussianState n × GaussianState n))
    [∀ i, IsProbabilityMeasure (tau i)]
    (warmBudget mixError : Nat → ENNReal)
    (hstart : IsWarm (warmBudget 0) (Measure.map Prod.snd mu0) (pi 0))
    (hseedStep : ∀ i (rho : Measure (GaussianState n)), IsProbabilityMeasure rho →
      IsWarm (warmBudget i) rho (pi i) →
        IsWarm (warmBudget (i + 1))
          (Measure.map Prod.snd
            (sampleFromKernel
              (gaussianFiniteScoreSeedSchedule K hK delta sigmaSq shrink hdelta
                hshrink retrySteps retries i) rho)) (pi (i + 1)))
    (hmixTop : ∀ i, mixError i ≠ ⊤)
    (hmix : ∀ i (rho : Measure (GaussianState n)),
      IsWarm (2 * warmBudget i) rho (pi i) → IsProbabilityMeasure rho →
        TVLe
          (sampleFromKernel
            (gaussianFiniteScoreSeedSchedule K hK delta sigmaSq shrink hdelta
              hshrink retrySteps retries i) rho)
          (tau i) (mixError i))
    (u : (i : Nat) →
      (Finset.Iic i → GaussianState n × GaussianState n) → Real)
    (v : Nat → GaussianState n → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i,
      accuracyU
          (inhomogeneousPathMeasure
            (stateScheduleFromSeed
              (gaussianFiniteScoreSeedSchedule K hK delta sigmaSq shrink hdelta
                hshrink retrySteps retries)) mu0)
          V (Ttc.CVCorrected.correctedAlpha m eta) i =
        fun omega ↦ u i (Preorder.frestrictLe i omega))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (omega (i + 1)).1)
    (hbudget : ∀ i,
      2 * (mixError i).toReal ≤ Ttc.CVCorrected.correctedNu m eta) :
    SeedProjectedOperational
      (stateScheduleFromSeed
        (gaussianFiniteScoreSeedSchedule K hK delta sigmaSq shrink hdelta hshrink
          retrySteps retries))
      (gaussianFiniteScoreSeedSchedule K hK delta sigmaSq shrink hdelta hshrink
        retrySteps retries)
      Prod.snd Prod.fst mu0 V m eta :=
  seedProjectedOperational_of_recurrence
    (gaussianFiniteScoreSeedSchedule K hK delta sigmaSq shrink hdelta hshrink
      retrySteps retries)
    mu0 V m eta pi tau warmBudget mixError hstart hseedStep hmixTop hmix
    u v hu hv hU hV hbudget

#print axioms map_seed_eval_succ
#print axioms isWarm_seed_eval_of_recurrence
#print axioms isWarm_historyLastSeed_of_recurrence
#print axioms seedProjectedOperational_of_recurrence
#print axioms sampleFrom_gaussianFiniteScoreSeedSchedule
#print axioms map_snd_gaussianFiniteScoreSeedCostedSchedule
#print axioms gaussianFiniteSeedProjectedOperational

end Ttc.CVFiniteAugmentedSeedOperational
