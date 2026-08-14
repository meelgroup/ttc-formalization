/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVFreshRestartKernel
import Ttc.Volume.CVCorrectedParameters

/-!
# Dependence from a fresh-regeneration phase sampler

This is the strongest law-level bridge justified by the distributional reading of
Cousins--Vempala's rejection routine.  After conditioning a history event, an external
regeneration resource supplies fresh iid draws from the entire proposal law produced by
that conditioned start.  `freshTwoStageSpeedyRestartKernel` then implements both rejection
stages.  The ordinary LV2 large-event argument gives history/next-phase `NuIndep`.

The resource is explicit in `FreshRegenerationResource`.  In particular, this file does
not identify fresh draws from a proposal *law* with repeated runs of a statewise kernel
from one realised previous point.
-/

namespace Ttc.CVFreshRestartDependence

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.GaussianCooling
open Ttc.CVFreshRestartKernel Ttc.CVSequentialDependence
open scoped ENNReal Pointwise

/-- The missing operational resource in the paper's distribution-level rejection step.

For every large measurable history event `S`, `proposalFor S` must be the full proposal
law obtained by running the phase generator from the conditioned last-state law.  The
second conjunct says that the algorithm's actual conditional next output is obtained by
fresh rejection from that law.  Supplying merely one realised last state does not prove
either conjunct. -/
def FreshRegenerationResource
    {Ω Hist E B : Type*} [MeasurableSpace Ω] [MeasurableSpace Hist]
    [MeasurableSpace E] [MeasurableSpace B]
    (μ : Measure Ω) (H : Ω → Hist) (Y : Ω → B)
    (last : Hist → E) (proposalLaw : Measure E → Measure E)
    (proposalFor : Set Hist → ProbabilityMeasure E)
    (outputFor : ProbabilityMeasure E → Measure B) : Prop :=
  ∀ S : Set Hist, MeasurableSet S → 1 / 2 ≤ μ.real (H ⁻¹' S) →
    ((proposalFor S : ProbabilityMeasure E) : Measure E) =
        proposalLaw ((Arlib.condOn (μ.map H) S).map last) ∧
      ∀ T : Set B, MeasurableSet T →
        μ.real (H ⁻¹' S ∩ Y ⁻¹' T) =
          μ.real (H ⁻¹' S) * (outputFor (proposalFor S)).real T

variable {n : Nat}

/-- Law-level LV2 `lem:delta-ind` for the complete two-stage fresh-restart routine.

The proposal-law identity in `hregen` documents the source of every regenerated draw.
The proof of independence uses its factorization conjunct and target TV.  Positivity of
the two rejection masses makes the total fallback branches unreachable. -/
theorem nuIndep_history_next_of_freshTwoStageRegeneration
    {Ω Hist E : Type*} [MeasurableSpace Ω] [MeasurableSpace Hist]
    [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {τ : Measure (Space n)} [IsProbabilityMeasure τ]
    {H : Ω → Hist} {Y : Ω → Space n} (hH : Measurable H) (hY : Measurable Y)
    (last : Hist → E) (proposalLaw : Measure E → Measure E)
    (proposalFor : Set Hist → ProbabilityMeasure E)
    {A : Set E} (hA : MeasurableSet A) {f : E → Space n} (hf : Measurable f)
    {c s : Real} (hs : 0 < s) (hc2 : c ^ 2 ≤ 1)
    {eps : ENNReal} (heps : eps ≠ ⊤)
    (hregen : FreshRegenerationResource μ H Y last proposalLaw proposalFor
      (fun q => freshTwoStageSpeedyRestartKernel hA f hf c s q))
    (hA0 : ∀ S : Set Hist, MeasurableSet S → 1 / 2 ≤ μ.real (H ⁻¹' S) →
      (proposalFor S : Measure E) A ≠ 0)
    (hmass : ∀ S : Set Hist, MeasurableSet S → 1 / 2 ≤ μ.real (H ⁻¹' S) →
      ((Measure.map f (Arlib.condOn (proposalFor S : Measure E) A)).withDensity
        fun x => ENNReal.ofReal (Arlib.MarkovChains.speedyAcceptReal c s x)) Set.univ ≠ 0)
    (hmix : ∀ S : Set Hist, MeasurableSet S → 1 / 2 ≤ μ.real (H ⁻¹' S) →
      TVLe
        (Arlib.condOn
          ((Measure.map f (Arlib.condOn (proposalFor S : Measure E) A)).withDensity
            fun x => ENNReal.ofReal (Arlib.MarkovChains.speedyAcceptReal c s x)) Set.univ)
        τ eps) :
    NuIndep μ H Y (2 * eps.toReal) := by
  apply nuIndep_of_largeEvent_conditionedSampler
    (μ := μ) (τ := τ) (H := H) (Y := Y) hH hY
    (fun S => freshTwoStageSpeedyRestartKernel hA f hf c s (proposalFor S)) heps
  · intro S hS hp
    infer_instance
  · intro S T hS hT hp
    exact (hregen S hS hp).2 T hT
  · intro S hS hp
    exact tvLe_freshTwoStageSpeedyRestartKernel_apply hA hf (proposalFor S)
      hs hc2 (hA0 S hS hp) (hmass S hS hp) (hmix S hS hp)

/-- Measurable history and next-point statistics, together with their squares, inherit
the same coefficient.  These are precisely the two dependence premises used by the
corrected first- and second-moment recursions. -/
theorem nuIndep_statistics_and_sq_of_freshTwoStageRegeneration
    {Ω Hist E : Type*} [MeasurableSpace Ω] [MeasurableSpace Hist]
    [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {τ : Measure (Space n)} [IsProbabilityMeasure τ]
    {H : Ω → Hist} {Y : Ω → Space n} (hH : Measurable H) (hY : Measurable Y)
    (last : Hist → E) (proposalLaw : Measure E → Measure E)
    (proposalFor : Set Hist → ProbabilityMeasure E)
    {A : Set E} (hA : MeasurableSet A) {f : E → Space n} (hf : Measurable f)
    {c s : Real} (hs : 0 < s) (hc2 : c ^ 2 ≤ 1)
    {eps : ENNReal} (heps : eps ≠ ⊤)
    (hregen : FreshRegenerationResource μ H Y last proposalLaw proposalFor
      (fun q => freshTwoStageSpeedyRestartKernel hA f hf c s q))
    (hA0 : ∀ S : Set Hist, MeasurableSet S → 1 / 2 ≤ μ.real (H ⁻¹' S) →
      (proposalFor S : Measure E) A ≠ 0)
    (hmass : ∀ S : Set Hist, MeasurableSet S → 1 / 2 ≤ μ.real (H ⁻¹' S) →
      ((Measure.map f (Arlib.condOn (proposalFor S : Measure E) A)).withDensity
        fun x => ENNReal.ofReal (Arlib.MarkovChains.speedyAcceptReal c s x)) Set.univ ≠ 0)
    (hmix : ∀ S : Set Hist, MeasurableSet S → 1 / 2 ≤ μ.real (H ⁻¹' S) →
      TVLe
        (Arlib.condOn
          ((Measure.map f (Arlib.condOn (proposalFor S : Measure E) A)).withDensity
            fun x => ENNReal.ofReal (Arlib.MarkovChains.speedyAcceptReal c s x)) Set.univ)
        τ eps)
    (u : Hist → Real) (v : Space n → Real) (hu : Measurable u) (hv : Measurable v) :
    NuIndep μ (fun ω => u (H ω)) (fun ω => v (Y ω)) (2 * eps.toReal) ∧
      NuIndep μ (fun ω => (u (H ω)) ^ 2) (fun ω => (v (Y ω)) ^ 2)
        (2 * eps.toReal) := by
  have hbase := nuIndep_history_next_of_freshTwoStageRegeneration hH hY last proposalLaw
    proposalFor hA hf hs hc2 heps hregen hA0 hmass hmix
  constructor
  · exact hbase.comp hu hv
  · have hstats := hbase.comp hu hv
    have hp : Measurable (fun x : Real => x ^ 2) := measurable_id.pow_const 2
    simpa only [Function.comp_apply] using hstats.comp hp hp

/-! ## Concrete Gaussian speedy-to-target specialization -/

/-- Source-level `lem:delta-ind` after the repository's fully justified
`lem:map-speedy-to-ball`.  Each large conditioned history event must provide a fresh
proposal law `proposalFor S` that is `eps`-close to the speedy stationary law.  The
normalized output is therefore `64 * eps`-close to the Gaussian target, and history/next
dependence is at most twice that quantity.

The two positive-mass premises expose termination of both rejection stages.  They are
facts about the supplied proposal laws, not consequences of having one realised point. -/
theorem nuIndep_history_next_freshGaussianPhase
    {Ω Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Hist]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → Hist} {Y : Ω → Space n} (hH : Measurable H) (hY : Measurable Y)
    (last : Hist → Space n) (proposalLaw : Measure (Space n) → Measure (Space n))
    (proposalFor : Set Hist → ProbabilityMeasure (Space n))
    {K : Set (Space n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : Metric.ball (0 : Space n) 1 ⊆ K) (hKvol : volume K ≠ ⊤)
    {c delta s : Real} (hc0 : 0 < c) (hc1 : c < 1)
    (hdelta : 0 < delta) (hdeltac : delta ≤ 1 - c) (hs : 0 < s)
    (hcn : (1 : Real) / 2 ≤ c ^ n) {eps : ENNReal}
    (hQhalf : ENNReal.ofReal (1 / 2) ≤
      Arlib.condOn
        (Arlib.MarkovChains.ellGaussianMeasure K delta s) Set.univ (c • K))
    (heps : eps ≤ ENNReal.ofReal (1 / 32))
    (hregen : FreshRegenerationResource μ H Y last proposalLaw proposalFor
      (fun q => freshTwoStageSpeedyRestartKernel
        (Arlib.MarkovChains.measurableSet_smul_set hK hc0.ne')
        (fun x : Space n => c⁻¹ • x) (continuous_const_smul _).measurable c s q))
    (hP : ∀ S : Set Hist, MeasurableSet S → 1 / 2 ≤ μ.real (H ⁻¹' S) →
      TVLe (proposalFor S : Measure (Space n))
        (Arlib.condOn (Arlib.MarkovChains.ellGaussianMeasure K delta s) Set.univ) eps)
    (hshrink : ∀ S : Set Hist, MeasurableSet S → 1 / 2 ≤ μ.real (H ⁻¹' S) →
      (proposalFor S : Measure (Space n)) (c • K) ≠ 0)
    (haccept : ∀ S : Set Hist, MeasurableSet S → 1 / 2 ≤ μ.real (H ⁻¹' S) →
      ((Measure.map (fun x : Space n => c⁻¹ • x)
          (Arlib.condOn (proposalFor S : Measure (Space n)) (c • K))).withDensity
        fun x => ENNReal.ofReal (Arlib.MarkovChains.speedyAcceptReal c s x)) Set.univ ≠ 0) :
    NuIndep μ H Y (2 * (64 * eps).toReal) := by
  have hepsTop : eps ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top heps
  have h64Top : 64 * eps ≠ ⊤ := ENNReal.mul_ne_top (by simp) hepsTop
  have htarget0 :
      ((volume.restrict K).withDensity
        (Arlib.MarkovChains.gaussianWeight s)) Set.univ ≠ 0 := by
    rw [Arlib.MarkovChains.gaussianRestrict_univ]
    exact (Arlib.MarkovChains.lintegral_gaussianWeight_pos hs one_pos hball).ne'
  have htargetTop :
      ((volume.restrict K).withDensity
        (Arlib.MarkovChains.gaussianWeight s)) Set.univ ≠ ⊤ := by
    rw [Arlib.MarkovChains.gaussianRestrict_univ]
    exact Arlib.MarkovChains.lintegral_gaussianWeight_ne_top hs hKvol
  letI : IsProbabilityMeasure (Arlib.condOn
      ((volume.restrict K).withDensity
        (Arlib.MarkovChains.gaussianWeight s)) Set.univ) :=
    Arlib.isProbabilityMeasure_condOn _ htarget0 htargetTop
  apply nuIndep_history_next_of_freshTwoStageRegeneration
    (μ := μ) (τ := Arlib.condOn
      ((volume.restrict K).withDensity (Arlib.MarkovChains.gaussianWeight s)) Set.univ)
    hH hY last proposalLaw proposalFor
    (Arlib.MarkovChains.measurableSet_smul_set hK hc0.ne')
    (continuous_const_smul _).measurable hs (by nlinarith) h64Top hregen
    hshrink haccept
  intro S hS hp
  exact Arlib.MarkovChains.tvLe_speedyRejection_target_of hK hKc hball hKvol
    hc0 hc1 hdelta hdeltac hs hcn hQhalf (hP S hS hp) heps

/-- Direct adapter to the dependence fields of `corrected_lem_accuracy_concrete`.

At phase `i`, `H i` contains the history and `Y i` is the regenerated next point.  The
equalities `hU` and `hV` identify the abstract statistics with the corrected recursion's
`U_i` and `V_(i+1)`.  All operational work is isolated in `hdep`; in applications it is
provided by `nuIndep_statistics_and_sq_of_freshTwoStageRegeneration` phase by phase.
-/
theorem correctedAccuracy_dependencePremises_of_freshRegeneration
    {Ω Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Hist]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (V : Nat → Ω → Real) {m : Nat} {eta : Real}
    (H : Nat → Ω → Hist) (Y : Nat → Ω → Space n)
    (u : Nat → Hist → Real) (v : Nat → Space n → Real)
    (hU : ∀ i, accuracyU μ V (Ttc.CVCorrected.correctedAlpha m eta) i =
      fun ω => u i (H i ω))
    (hV : ∀ i, V (i + 1) = fun ω => v i (Y i ω))
    (epsPhase : Nat → ENNReal)
    (hbudget : ∀ i, 2 * (epsPhase i).toReal ≤ Ttc.CVCorrected.correctedNu m eta)
    (hdep : ∀ i,
      NuIndep μ (fun ω => u i (H i ω)) (fun ω => v i (Y i ω))
        (2 * (epsPhase i).toReal) ∧
      NuIndep μ (fun ω => (u i (H i ω)) ^ 2) (fun ω => (v i (Y i ω)) ^ 2)
        (2 * (epsPhase i).toReal)) :
    (∀ i, NuIndep μ
      (accuracyU μ V (Ttc.CVCorrected.correctedAlpha m eta) i) (V (i + 1))
      (Ttc.CVCorrected.correctedNu m eta)) ∧
    (∀ i, NuIndep μ
      (fun ω => (accuracyU μ V (Ttc.CVCorrected.correctedAlpha m eta) i ω) ^ 2)
      (fun ω => (V (i + 1) ω) ^ 2)
      (Ttc.CVCorrected.correctedNu m eta)) := by
  constructor
  · intro i
    rw [hU i, hV i]
    exact (hdep i).1.mono (hbudget i)
  · intro i
    rw [hU i, hV i]
    exact (hdep i).2.mono (hbudget i)

/-! Axiom audit. -/

#print axioms nuIndep_history_next_of_freshTwoStageRegeneration
#print axioms nuIndep_statistics_and_sq_of_freshTwoStageRegeneration
#print axioms nuIndep_history_next_freshGaussianPhase
#print axioms correctedAccuracy_dependencePremises_of_freshRegeneration

end Ttc.CVFreshRestartDependence
