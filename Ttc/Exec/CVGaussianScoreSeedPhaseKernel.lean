import Ttc.Exec.CVScoreSeedPhaseKernel
import Ttc.Exec.FiniteContinuingRetryGaussianAugmentedPhase
import Arlib.Convexity.GaussianCooling.ScaledRawWarm

/-!
# Concrete Gaussian `(score, seed)` phase kernel

The accepted retry output remembers both the rescaled estimator point and the raw
endpoint.  The input is only the raw seed; its estimator coordinate is used solely as
the unresolved self-fallback.
-/

namespace Ttc.CVGaussianScoreSeedPhaseKernel

open MeasureTheory ProbabilityTheory Set
open Arlib Arlib.MarkovChains
open Ttc.CVSequentialPhaseSampler
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryGaussianAugmentedPhase
open Arlib.GaussianCooling
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- Canonical unresolved pair associated to a raw seed. -/
noncomputable def seedEmbedding (c : Real) (x : State n) : ScoreSeed n :=
  (c⁻¹ • x, x)

theorem measurable_seedEmbedding (c : Real) :
    Measurable (seedEmbedding (n := n) c) := by
  unfold seedEmbedding
  fun_prop

/-- The exact reference pair associated with a full cooling draw: its first coordinate
is the estimator score and its second is the raw, scaled seed for the next walk. -/
noncomputable def scoreSeedReference (c : Real) (mu : Measure (State n)) :
    Measure (ScoreSeed n) :=
  Measure.map (fun y ↦ (y, c • y)) mu

theorem map_fst_scoreSeedReference (c : Real) (mu : Measure (State n)) :
    Measure.map Prod.fst (scoreSeedReference c mu) = mu := by
  rw [scoreSeedReference, Measure.map_map measurable_fst (by fun_prop)]
  have hfun : Prod.fst ∘ (fun y : State n ↦ (y, c • y)) = id := by
    funext y
    rfl
  rw [hfun, Measure.map_id]

theorem map_snd_scoreSeedReference (c : Real) (mu : Measure (State n)) :
    Measure.map Prod.snd (scoreSeedReference c mu) =
      Measure.map (fun y ↦ c • y) mu := by
  rw [scoreSeedReference, Measure.map_map measurable_snd (by fun_prop)]
  rfl

/-- The raw endpoint and rescaled score in a combined accepted proposal lie on the
same deterministic graph. -/
theorem combinedNext_eq_smul_combinedOutput (c : Real) (hc : c ≠ 0)
    (p : State n × Real) :
    Ttc.CVCombinedContinuingAccept.combinedNext p =
      c • Ttc.CVCombinedContinuingAccept.combinedOutput c p := by
  simp [Ttc.CVCombinedContinuingAccept.combinedNext,
    Ttc.CVCombinedContinuingAccept.combinedOutput, hc]

/-- Consequently, retaining both fields of any ideal accepted law is exactly the graph
lift of its score marginal. -/
theorem map_scoreSeed_eq_reference_of_combined
    (c : Real) (hc : c ≠ 0) (mu : Measure (State n × Real)) :
    Measure.map
        (fun p ↦ (Ttc.CVCombinedContinuingAccept.combinedOutput c p,
          Ttc.CVCombinedContinuingAccept.combinedNext p)) mu =
      scoreSeedReference c
        (Measure.map (Ttc.CVCombinedContinuingAccept.combinedOutput c) mu) := by
  rw [scoreSeedReference,
    Measure.map_map (by fun_prop : Measurable (fun y : State n ↦ (y, c • y)))
      (Ttc.CVCombinedContinuingAccept.measurable_combinedOutput c)]
  apply Measure.map_congr
  filter_upwards [] with p
  rw [combinedNext_eq_smul_combinedOutput c hc p]
  rfl

/-- Costed finite-retry phase, indexed only by the seed used to start the walk. -/
noncomputable def gaussianScoreSeedCostedKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat) :
    Kernel (State n) (ENNReal × ScoreSeed n) :=
  Kernel.comap
    (augmentedGaussianFinitePhaseCostedKernel K hK delta s c hdelta hc steps L)
    (seedEmbedding c) (measurable_seedEmbedding c)

instance gaussianScoreSeedCostedKernel.isMarkovKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat) :
    IsMarkovKernel
      (gaussianScoreSeedCostedKernel K hK delta s c hdelta hc steps L) := by
  unfold gaussianScoreSeedCostedKernel
  infer_instance

/-- Cost-erased augmented phase. -/
noncomputable def gaussianScoreSeedKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat) :
    Kernel (State n) (ScoreSeed n) :=
  Kernel.map
    (gaussianScoreSeedCostedKernel K hK delta s c hdelta hc steps L) Prod.snd

instance gaussianScoreSeedKernel.isMarkovKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat) :
    IsMarkovKernel (gaussianScoreSeedKernel K hK delta s c hdelta hc steps L) := by
  unfold gaussianScoreSeedKernel
  exact Kernel.IsMarkovKernel.map _ measurable_snd

/-- Exact cost erasure, in the interface expected by sequential cost refinements. -/
theorem map_snd_gaussianScoreSeedCostedKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat)
    (x : State n) :
    Measure.map Prod.snd
        (gaussianScoreSeedCostedKernel K hK delta s c hdelta hc steps L x) =
      gaussianScoreSeedKernel K hK delta s c hdelta hc steps L x := by
  rw [gaussianScoreSeedKernel, Kernel.map_apply _ measurable_snd]

/-- Pointwise law of the concrete costed phase. -/
theorem gaussianScoreSeedCostedKernel_apply
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat)
    (x : State n) :
    gaussianScoreSeedCostedKernel K hK delta s c hdelta hc steps L x =
      Measure.map augmentedPhaseCostOutput
        (Arlib.adaptiveMarginal
          (augmentedGaussianRetrySchedule K hK delta s c hdelta hc steps)
          (Measure.dirac (augmentedEmbedding (seedEmbedding c x))) L) := by
  rw [gaussianScoreSeedCostedKernel, Kernel.comap_apply,
    augmentedGaussianFinitePhaseCostedKernel,
    Kernel.map_apply _ measurable_augmentedPhaseCostOutput,
    augmentedGaussianRetryStateKernel_apply]

/-- Exact score marginal: accepted retries contribute the rescaled endpoint, while the
unresolved branch contributes the correspondingly rescaled incoming seed. -/
theorem map_fst_gaussianScoreSeedKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat)
    (x : State n) :
    Measure.map Prod.fst
        (gaussianScoreSeedKernel K hK delta s c hdelta hc steps L x) =
      Measure.map (fun z ↦ (output z).1)
        (Arlib.adaptiveMarginal
          (augmentedGaussianRetrySchedule K hK delta s c hdelta hc steps)
          (Measure.dirac (augmentedEmbedding (seedEmbedding c x))) L) := by
  rw [gaussianScoreSeedKernel, Kernel.map_apply _ measurable_snd,
    Measure.map_map measurable_fst measurable_snd,
    gaussianScoreSeedCostedKernel_apply hK delta s c hdelta hc steps L x,
    Measure.map_map (measurable_fst.comp measurable_snd)
      measurable_augmentedPhaseCostOutput]
  rfl

/-- Exact raw-seed marginal retained for the next phase. -/
theorem map_snd_gaussianScoreSeedKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat)
    (x : State n) :
    Measure.map Prod.snd
        (gaussianScoreSeedKernel K hK delta s c hdelta hc steps L x) =
      Measure.map (fun z ↦ (output z).2)
        (Arlib.adaptiveMarginal
          (augmentedGaussianRetrySchedule K hK delta s c hdelta hc steps)
          (Measure.dirac (augmentedEmbedding (seedEmbedding c x))) L) := by
  rw [gaussianScoreSeedKernel, Kernel.map_apply _ measurable_snd,
    Measure.map_map measurable_snd measurable_snd,
    gaussianScoreSeedCostedKernel_apply hK delta s c hdelta hc steps L x,
    Measure.map_map (measurable_snd.comp measurable_snd)
      measurable_augmentedPhaseCostOutput]
  rfl

/-- Any exact/approximate score-marginal theorem for the retry marginal transfers to
the concrete augmented kernel without loss. -/
theorem tvLe_scoreMarginal
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat)
    (x : State n) (tau : Measure (State n)) (eps : ENNReal)
    (hscore : TVLe
      (Measure.map (fun z ↦ (output z).1)
        (Arlib.adaptiveMarginal
          (augmentedGaussianRetrySchedule K hK delta s c hdelta hc steps)
          (Measure.dirac (augmentedEmbedding (seedEmbedding c x))) L)) tau eps) :
    TVLe
      (Measure.map Prod.fst
        (gaussianScoreSeedKernel K hK delta s c hdelta hc steps L x)) tau eps := by
  rw [map_fst_gaussianScoreSeedKernel hK delta s c hdelta hc steps L x]
  exact hscore

/-- The analytic scaled-seed estimate plugs into the augmented kernel through its exact
seed marginal formula; no warmth of the full pair law is requested. -/
theorem isWarm_seedMarginal
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat)
    (x : State n) (pi : Measure (State n)) (M : ENNReal)
    (hwarm : IsWarm M
      (Measure.map (fun z ↦ (output z).2)
        (Arlib.adaptiveMarginal
          (augmentedGaussianRetrySchedule K hK delta s c hdelta hc steps)
          (Measure.dirac (augmentedEmbedding (seedEmbedding c x))) L)) pi) :
    IsWarm M
      (Measure.map Prod.snd
        (gaussianScoreSeedKernel K hK delta s c hdelta hc steps L x)) pi := by
  rw [map_snd_gaussianScoreSeedKernel hK delta s c hdelta hc steps L x]
  exact hwarm

/-- The concrete reference seed for the standard source shrink is dimension-free
`2e`-warm for the next speedy Gaussian target. -/
theorem isWarm_snd_scoreSeedReference_standard
    (hn : 1 ≤ n) {m : Nat} {sigmaSq : Nat → Real} (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : Metric.ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m) {cc : Real} (hcc1 : 1 ≤ cc)
    (hcc : cc ≤ 1 + 2 / (n : Real))
    (hsched : sigmaSq (i + 1) = cc * sigmaSq i)
    {delta : Real} (hdelta : 0 < delta) (hdeltan : delta ≤ 1 / (2 * (n : Real))) :
    IsWarm (ENNReal.ofReal (2 * Real.exp 1))
      (Measure.map Prod.snd
        (scoreSeedReference (1 - 1 / (2 * (n : Real)))
          (coolLaw m sigmaSq K i)))
      (ellGaussianProb K delta (sigmaSq (i + 1))) := by
  rw [map_snd_scoreSeedReference]
  exact isWarm_standardScaledRaw_coolLaw_succ_ellGaussianProb hn hsigma hK hKc
    hball hfin hi hcc1 hcc hsched hdelta hdeltan

#print axioms map_snd_gaussianScoreSeedCostedKernel
#print axioms map_fst_scoreSeedReference
#print axioms map_snd_scoreSeedReference
#print axioms map_scoreSeed_eq_reference_of_combined
#print axioms gaussianScoreSeedCostedKernel_apply
#print axioms map_fst_gaussianScoreSeedKernel
#print axioms map_snd_gaussianScoreSeedKernel
#print axioms tvLe_scoreMarginal
#print axioms isWarm_seedMarginal
#print axioms isWarm_snd_scoreSeedReference_standard

end Ttc.CVGaussianScoreSeedPhaseKernel
