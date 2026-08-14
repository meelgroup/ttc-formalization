import Ttc.Exec.CVGaussianAugmentedSelectiveTV
import Ttc.Exec.CVFiniteContinuingPhaseDistributional
import Ttc.Exec.CVScoreSeedPhaseKernel

/-!
# Finite Gaussian retry phases retaining the acceptance flag

The pair-only phase forgets whether the finite retry loop accepted or returned its
self-fallback.  That makes the successful branch unavailable as a measurable path event.
Here the flag is retained.  The resulting transition is an honest Markov kernel; its
`flag = true` conditional law is the distribution-level accepted first-hit mixture, while
the complement has exactly the retry survival mass.
-/

namespace Ttc.CVFiniteAugmentedAcceptedFlag

open MeasureTheory ProbabilityTheory Set
open Arlib Arlib.Probability Arlib.MarkovChains
open Ttc.CVSequentialPhaseSampler
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryGaussianAugmentedPhase
open Ttc.CVGaussianAugmentedSelectiveTV
open Ttc.CVGaussianScoreSeedPhaseKernel
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n
/-- `(accepted before L, estimator score, retained raw seed)`. -/
abbrev FlaggedState (n : Nat) := Bool × ScoreSeed n

def flaggedOutput (z : RetryState (State n) (ScoreSeed n)) : FlaggedState n :=
  (accepted z, output z)

theorem measurable_flaggedOutput :
    Measurable (flaggedOutput : RetryState (State n) (ScoreSeed n) → FlaggedState n) :=
  measurable_accepted.prodMk measurable_output

def acceptedFlagSet : Set (FlaggedState n) := {z | z.1 = true}

theorem measurableSet_acceptedFlagSet : MeasurableSet (acceptedFlagSet : Set (FlaggedState n)) := by
  change MeasurableSet
    ((Prod.fst : FlaggedState n → Bool) ⁻¹' ({true} : Set Bool))
  exact (MeasurableSet.singleton true).preimage measurable_fst

@[simp] theorem flaggedOutput_mem_acceptedFlagSet
    (z : RetryState (State n) (ScoreSeed n)) :
    flaggedOutput z ∈ acceptedFlagSet ↔ accepted z = true := Iff.rfl

/-- Seed-indexed finite retry phase with the terminal acceptance flag retained. -/
noncomputable def flaggedGaussianPhaseKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat) :
    Kernel (State n) (FlaggedState n) :=
  Kernel.map
    (Kernel.comap
      (augmentedGaussianRetryStateKernel K hK delta s c hdelta hc steps L)
      (seedEmbedding c) (measurable_seedEmbedding c))
    flaggedOutput

instance flaggedGaussianPhaseKernel.isMarkovKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat) :
    IsMarkovKernel (flaggedGaussianPhaseKernel K hK delta s c hdelta hc steps L) := by
  unfold flaggedGaussianPhaseKernel
  exact Kernel.IsMarkovKernel.map _ measurable_flaggedOutput

/-- The next transition reads only the raw seed and ignores the old flag and score. -/
noncomputable def flaggedStateKernelFromSeed
    (Q : Kernel (State n) (FlaggedState n)) [IsMarkovKernel Q] :
    Kernel (FlaggedState n) (FlaggedState n) :=
  Kernel.comap Q (fun z ↦ z.2.2) (measurable_snd.comp measurable_snd)

instance flaggedStateKernelFromSeed.isMarkovKernel
    (Q : Kernel (State n) (FlaggedState n)) [IsMarkovKernel Q] :
    IsMarkovKernel (flaggedStateKernelFromSeed Q) := by
  unfold flaggedStateKernelFromSeed
  infer_instance

theorem flaggedStateKernelFromSeed_apply
    (Q : Kernel (State n) (FlaggedState n)) [IsMarkovKernel Q]
    (z : FlaggedState n) :
    flaggedStateKernelFromSeed Q z = Q z.2.2 := by
  rw [flaggedStateKernelFromSeed, Kernel.comap_apply]

/-- Arbitrary incoming-law identification with the embedded retry marginal. -/
theorem sampleFrom_flaggedGaussianPhaseKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat)
    (rho : Measure (State n)) [IsProbabilityMeasure rho] :
    sampleFromKernel (flaggedGaussianPhaseKernel K hK delta s c hdelta hc steps L) rho =
      Measure.map flaggedOutput
        (augmentedMarginalOf K hK delta s c hdelta hc steps
          (Measure.map (seedEmbedding c) rho) L) := by
  let rhoPair := Measure.map (seedEmbedding c) rho
  letI : IsProbabilityMeasure rhoPair :=
    Measure.isProbabilityMeasure_map (measurable_seedEmbedding c).aemeasurable
  unfold flaggedGaussianPhaseKernel
  rw [Ttc.CVFiniteContinuingPhaseDistributional.sampleFromKernel_map _ flaggedOutput
    measurable_flaggedOutput rho]
  unfold sampleFromKernel
  rw [Arlib.MarkovChains.bind_comap]
  change Measure.map flaggedOutput
      (sampleFromKernel
        (augmentedGaussianRetryStateKernel K hK delta s c hdelta hc steps L) rhoPair) = _
  rw [sampleFrom_augmentedRetryStateKernel_eq_marginalOf]

/-- The failed flag has exactly the unresolved survival mass. -/
theorem flaggedGaussianPhaseKernel_failure
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat)
    (rho : Measure (State n)) [IsProbabilityMeasure rho] :
    sampleFromKernel (flaggedGaussianPhaseKernel K hK delta s c hdelta hc steps L) rho
        (acceptedFlagSetᶜ) =
      augmentedSurvivalOf K hK delta s c hdelta hc steps
        (Measure.map (seedEmbedding c) rho) L := by
  rw [sampleFrom_flaggedGaussianPhaseKernel hK delta s c hdelta hc steps L rho,
    Measure.map_apply measurable_flaggedOutput measurableSet_acceptedFlagSet.compl]
  change augmentedMarginalOf K hK delta s c hdelta hc steps
      (Measure.map (seedEmbedding c) rho) L
      (flaggedOutput ⁻¹' acceptedFlagSetᶜ) = _
  have hpre : flaggedOutput ⁻¹' (acceptedFlagSetᶜ : Set (FlaggedState n)) =
      Ttc.FiniteContinuingRetry.runningStates := by
    ext z
    simp [acceptedFlagSet, flaggedOutput, Ttc.FiniteContinuingRetry.runningStates,
      acceptedStates]
  rw [hpre]
  rfl

/-- Conditioning the flagged phase on success and then forgetting the flag is literally
the accepted first-hit mixture obtained by conditioning the law-level retry marginal. -/
theorem map_snd_condOn_flaggedGaussianPhaseKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat)
    (rho : Measure (State n)) [IsProbabilityMeasure rho]
    (hacc : sampleFromKernel
      (flaggedGaussianPhaseKernel K hK delta s c hdelta hc steps L) rho
        acceptedFlagSet ≠ 0) :
    Measure.map Prod.snd
        (condOn
          (sampleFromKernel
            (flaggedGaussianPhaseKernel K hK delta s c hdelta hc steps L) rho)
          acceptedFlagSet) =
      Measure.map output
        (condOn
          (augmentedMarginalOf K hK delta s c hdelta hc steps
            (Measure.map (seedEmbedding c) rho) L)
          acceptedStates) := by
  let mu := augmentedMarginalOf K hK delta s c hdelta hc steps
    (Measure.map (seedEmbedding c) rho) L
  have hmu : sampleFromKernel
      (flaggedGaussianPhaseKernel K hK delta s c hdelta hc steps L) rho =
      Measure.map flaggedOutput mu :=
    sampleFrom_flaggedGaussianPhaseKernel hK delta s c hdelta hc steps L rho
  rw [hmu] at hacc ⊢
  apply Measure.ext
  intro T hT
  rw [Measure.map_apply measurable_snd hT,
    condOn_apply _ measurableSet_acceptedFlagSet (hT.preimage measurable_snd),
    Measure.map_apply measurable_flaggedOutput
      ((hT.preimage measurable_snd).inter measurableSet_acceptedFlagSet),
    Measure.map_apply measurable_flaggedOutput measurableSet_acceptedFlagSet,
    Measure.map_apply measurable_output hT,
    condOn_apply _ measurableSet_acceptedStates (hT.preimage measurable_output)]
  congr 1 <;> ext z <;> simp [flaggedOutput, acceptedFlagSet, acceptedStates]

#print axioms sampleFrom_flaggedGaussianPhaseKernel
#print axioms flaggedGaussianPhaseKernel_failure
#print axioms map_snd_condOn_flaggedGaussianPhaseKernel

end Ttc.CVFiniteAugmentedAcceptedFlag
