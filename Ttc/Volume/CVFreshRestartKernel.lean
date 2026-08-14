/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVPathwisePhaseKernel
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Fresh, distribution-level rejection restarts

The rejection operation in Cousins--Vempala's `lem:map-speedy-to-ball` is phrased in
terms of repeated *samples from a law* `P`: `P'` is the distribution of the first sample
from `P` which passes the rejection test.  This is different from rerunning a walk from
one fixed realised previous point.

This file makes the distribution-level reading operational.  A probability measure is an
explicit input state, `freshDrawKernel` draws from that state, and
`freshSpeedyRoundKernel` augments the draw by an independent uniform coin.  Conditioning
the round kernel on acceptance and projecting the point gives an honest Markov kernel.
The fallback on zero acceptance is only there to make the kernel total; all source uses
have positive acceptance.

Because every retry uses the same supplied law, the output is exactly independent of any
earlier history once that law has been fixed.  The final rectangle theorem records this
conditioned-history factorisation.  It does not claim that the supplied law can itself be
sampled afresh by continuing a single realised Markov trajectory.
-/

namespace Ttc.CVFreshRestartKernel

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.Probability
open Ttc.CVPathwisePhaseKernel Ttc.SpeedyRejection
open scoped ENNReal

/-- The Giry evaluation kernel: its input is a probability law and its output is one
fresh draw from that law. -/
noncomputable def freshDrawKernel {E : Type*} [MeasurableSpace E] :
    Kernel (ProbabilityMeasure E) E where
  toFun q := (q : Measure E)
  measurable' := measurable_subtype_coe

instance freshDrawKernel.isMarkovKernel {E : Type*} [MeasurableSpace E] :
    IsMarkovKernel (freshDrawKernel (E := E)) := by
  constructor
  intro q
  simpa [freshDrawKernel] using q.property

@[simp]
theorem freshDrawKernel_apply {E : Type*} [MeasurableSpace E]
    (q : ProbabilityMeasure E) :
    freshDrawKernel q = (q : Measure E) := rfl

/-! ## The first, distribution-level rejection stage -/

/-- Condition a fresh draw on `A`, then apply `f`.  This is total by falling back to an
unconditioned fresh draw when `A` has zero mass. -/
noncomputable def freshConditionMapKernel
    {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    {A : Set E} (hA : MeasurableSet A) (f : E → F) (_hf : Measurable f) :
    Kernel (ProbabilityMeasure E) F :=
  Kernel.map (conditionOr freshDrawKernel freshDrawKernel hA) f

instance freshConditionMapKernel.isMarkovKernel
    {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    {A : Set E} (hA : MeasurableSet A) (f : E → F) (hf : Measurable f) :
    IsMarkovKernel (freshConditionMapKernel hA f hf) := by
  unfold freshConditionMapKernel
  exact Kernel.IsMarkovKernel.map _ hf

/-- Package the first-stage output as the probability-law input for another fresh
restart.  This explicit law-valued state is what a distribution-level restart needs. -/
noncomputable def freshConditionMapLaw
    {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    {A : Set E} (hA : MeasurableSet A) (f : E → F) (hf : Measurable f)
    (q : ProbabilityMeasure E) : ProbabilityMeasure F :=
  ⟨freshConditionMapKernel hA f hf q, inferInstance⟩

theorem measurable_freshConditionMapLaw
    {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    {A : Set E} (hA : MeasurableSet A) {f : E → F} (hf : Measurable f) :
    Measurable (freshConditionMapLaw hA f hf) := by
  exact (freshConditionMapKernel hA f hf).measurable.subtype_mk

/-- On the source branch of positive acceptance, the law-valued state is literally the
pushforward of the conditioned input law. -/
theorem freshConditionMapLaw_toMeasure_of_ne_zero
    {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    {A : Set E} (hA : MeasurableSet A) {f : E → F} (hf : Measurable f)
    (q : ProbabilityMeasure E) (hA0 : (q : Measure E) A ≠ 0) :
    ((freshConditionMapLaw hA f hf q : ProbabilityMeasure F) : Measure F) =
      Measure.map f (Arlib.condOn (q : Measure E) A) := by
  change freshConditionMapKernel hA f hf q = _
  unfold freshConditionMapKernel
  rw [Kernel.map_apply _ hf,
    conditionOr_apply_of_ne_zero freshDrawKernel freshDrawKernel hA]
  rw [freshDrawKernel_apply]
  change (q : Measure E) A ≠ 0
  exact hA0

variable {n : Nat}

/-- The fixed uniform coin, packaged as a probability-measure state. -/
noncomputable def unitCoinProbabilityMeasure : ProbabilityMeasure Real :=
  ⟨unitCoin, inferInstance⟩

/-- One fresh source-level rejection round: independently draw a point from the supplied
law and a uniform coin.  The explicit probability-measure input is the augmentation that
makes “draw afresh from `P`” a genuine kernel operation. -/
noncomputable def freshSpeedyRoundKernel :
    Kernel (ProbabilityMeasure (Space n)) (Space n × Real) where
  toFun q := proposal (q : Measure (Space n))
  measurable' := by
    unfold proposal
    exact ProbabilityMeasure.measurable_fun_prod.comp
      (measurable_id.prodMk (measurable_const :
        Measurable fun _q : ProbabilityMeasure (Space n) => unitCoinProbabilityMeasure))

instance freshSpeedyRoundKernel.isMarkovKernel :
    IsMarkovKernel (freshSpeedyRoundKernel (n := n)) := by
  constructor
  intro q
  change IsProbabilityMeasure (proposal (q : Measure (Space n)))
  infer_instance

@[simp]
theorem freshSpeedyRoundKernel_apply (q : ProbabilityMeasure (Space n)) :
    freshSpeedyRoundKernel q = proposal (q : Measure (Space n)) := rfl

/-- Repeated fresh rounds, conditioned on speedy acceptance.  On a zero-acceptance input
the unconditioned round is returned, solely to keep this a total Markov kernel. -/
noncomputable def freshAcceptedRoundKernel (c s : Real) :
    Kernel (ProbabilityMeasure (Space n)) (Space n × Real) :=
  conditionOr freshSpeedyRoundKernel freshSpeedyRoundKernel
    (measurableSet_acceptRegion c s)

instance freshAcceptedRoundKernel.isMarkovKernel (c s : Real) :
    IsMarkovKernel (freshAcceptedRoundKernel (n := n) c s) := by
  unfold freshAcceptedRoundKernel
  infer_instance

/-- The point returned by the fresh-restart rejection transformer. -/
noncomputable def freshSpeedyRestartKernel (c s : Real) :
    Kernel (ProbabilityMeasure (Space n)) (Space n) :=
  Kernel.map (freshAcceptedRoundKernel (n := n) c s) Prod.fst

instance freshSpeedyRestartKernel.isMarkovKernel (c s : Real) :
    IsMarkovKernel (freshSpeedyRestartKernel (n := n) c s) := by
  unfold freshSpeedyRestartKernel
  exact Kernel.IsMarkovKernel.map _ measurable_fst

/-- Positive acceptance identifies the kernel application with the paper's normalized
distribution-level rejection law. -/
theorem freshSpeedyRestartKernel_apply_eq_condOn_withDensity
    (q : ProbabilityMeasure (Space n)) {c s : Real}
    (hs : 0 < s) (hc2 : c ^ 2 ≤ 1)
    (hmass : (((q : Measure (Space n)).withDensity fun x =>
      ENNReal.ofReal (speedyAcceptReal c s x)) Set.univ) ≠ 0) :
    freshSpeedyRestartKernel c s q =
      Arlib.condOn
        ((q : Measure (Space n)).withDensity fun x =>
          ENNReal.ofReal (speedyAcceptReal c s x)) Set.univ := by
  unfold freshSpeedyRestartKernel freshAcceptedRoundKernel
  rw [Kernel.map_apply _ measurable_fst,
    conditionOr_apply_of_ne_zero]
  · exact map_fst_condOn_proposal (q : Measure (Space n)) hs hc2
  · rw [freshSpeedyRoundKernel_apply,
      proposal_acceptRegion (q : Measure (Space n)) hs hc2]
    exact hmass

/-- The kernel is precisely the explicit iid first-accepted-point loop used in the
source-level distributional reading. -/
theorem freshSpeedyRestartKernel_apply_eq_firstAcceptedPoint
    (q : ProbabilityMeasure (Space n)) {c s : Real}
    (hs : 0 < s) (hc2 : c ^ 2 ≤ 1)
    (hmass : (((q : Measure (Space n)).withDensity fun x =>
      ENNReal.ofReal (speedyAcceptReal c s x)) Set.univ) ≠ 0) :
    freshSpeedyRestartKernel c s q =
      Measure.map (firstAcceptedPoint c s)
        (roundsMeasure (proposal (q : Measure (Space n)))) := by
  rw [freshSpeedyRestartKernel_apply_eq_condOn_withDensity q hs hc2 hmass]
  exact (map_firstAcceptedPoint_eq_condOn_withDensity
    (q : Measure (Space n)) hs hc2 hmass).symm

/-- Target-TV transport for the operational transformer.  There is no additional loss:
all loss is exactly the loss already paid by the normalized distribution-level theorem
(for the repository's speedy-to-target theorem, `64 * eps`). -/
theorem tvLe_freshSpeedyRestartKernel_apply
    (q : ProbabilityMeasure (Space n)) {c s : Real}
    (hs : 0 < s) (hc2 : c ^ 2 ≤ 1)
    (hmass : (((q : Measure (Space n)).withDensity fun x =>
      ENNReal.ofReal (speedyAcceptReal c s x)) Set.univ) ≠ 0)
    {tau : Measure (Space n)} {eps : ENNReal}
    (htv : TVLe
      (Arlib.condOn
        ((q : Measure (Space n)).withDensity fun x =>
          ENNReal.ofReal (speedyAcceptReal c s x)) Set.univ)
      tau eps) :
    TVLe (freshSpeedyRestartKernel c s q) tau eps := by
  rw [freshSpeedyRestartKernel_apply_eq_condOn_withDensity q hs hc2 hmass]
  exact htv

/-! ## Both rejection stages from `lem:map-speedy-to-ball` -/

/-- The full distribution-level reading of the source routine.  First draw afresh from
`q` until `A` occurs and apply `f`; then, on every final-filter rejection, draw afresh
from that whole first-stage output law. -/
noncomputable def freshTwoStageSpeedyRestartKernel
    {E : Type*} [MeasurableSpace E]
    {A : Set E} (hA : MeasurableSet A) (f : E → Space n) (hf : Measurable f)
    (c s : Real) : Kernel (ProbabilityMeasure E) (Space n) :=
  Kernel.comap (freshSpeedyRestartKernel c s)
    (freshConditionMapLaw hA f hf) (measurable_freshConditionMapLaw hA hf)

instance freshTwoStageSpeedyRestartKernel.isMarkovKernel
    {E : Type*} [MeasurableSpace E]
    {A : Set E} (hA : MeasurableSet A) (f : E → Space n) (hf : Measurable f)
    (c s : Real) :
    IsMarkovKernel (freshTwoStageSpeedyRestartKernel (n := n) hA f hf c s) := by
  unfold freshTwoStageSpeedyRestartKernel
  infer_instance

/-- The full operational kernel is exactly normalize-after-first-stage-mixing, which is
the nonlinear measure expression in the paper and in `CVSampler.phaseLaw`. -/
theorem freshTwoStageSpeedyRestartKernel_apply_eq
    {E : Type*} [MeasurableSpace E]
    {A : Set E} (hA : MeasurableSet A) {f : E → Space n} (hf : Measurable f)
    (q : ProbabilityMeasure E) {c s : Real}
    (hs : 0 < s) (hc2 : c ^ 2 ≤ 1)
    (hA0 : (q : Measure E) A ≠ 0)
    (hmass : ((Measure.map f (Arlib.condOn (q : Measure E) A)).withDensity
      fun x => ENNReal.ofReal (speedyAcceptReal c s x)) Set.univ ≠ 0) :
    freshTwoStageSpeedyRestartKernel hA f hf c s q =
      Arlib.condOn
        ((Measure.map f (Arlib.condOn (q : Measure E) A)).withDensity
          fun x => ENNReal.ofReal (speedyAcceptReal c s x)) Set.univ := by
  change freshSpeedyRestartKernel c s (freshConditionMapLaw hA f hf q) = _
  have hq := freshConditionMapLaw_toMeasure_of_ne_zero hA hf q hA0
  rw [freshSpeedyRestartKernel_apply_eq_condOn_withDensity]
  · rw [hq]
  · exact hs
  · exact hc2
  · simpa [hq] using hmass

/-- Target-TV transport for the complete two-stage source routine.  The operational
realization adds no TV loss to the normalized distributional analysis. -/
theorem tvLe_freshTwoStageSpeedyRestartKernel_apply
    {E : Type*} [MeasurableSpace E]
    {A : Set E} (hA : MeasurableSet A) {f : E → Space n} (hf : Measurable f)
    (q : ProbabilityMeasure E) {c s : Real}
    (hs : 0 < s) (hc2 : c ^ 2 ≤ 1)
    (hA0 : (q : Measure E) A ≠ 0)
    (hmass : ((Measure.map f (Arlib.condOn (q : Measure E) A)).withDensity
      fun x => ENNReal.ofReal (speedyAcceptReal c s x)) Set.univ ≠ 0)
    {tau : Measure (Space n)} {eps : ENNReal}
    (htv : TVLe
      (Arlib.condOn
        ((Measure.map f (Arlib.condOn (q : Measure E) A)).withDensity
          fun x => ENNReal.ofReal (speedyAcceptReal c s x)) Set.univ)
      tau eps) :
    TVLe (freshTwoStageSpeedyRestartKernel hA f hf c s q) tau eps := by
  rw [freshTwoStageSpeedyRestartKernel_apply_eq hA hf q hs hc2 hA0 hmass]
  exact htv

/-- Once the proposal law `q` has been selected (for example, as the previous marginal
conditioned on a history event), the fresh-restart output ignores the realised history.
This is the exact rectangle factorisation needed by the event-form dependence argument.

The theorem is deliberately parameterized by `q`: selecting a conditioned law for each
history event is an analysis-level family, not an event-oblivious statewise transition. -/
theorem freshRestart_conditionedHistory_factorization
    {H E F : Type*} [MeasurableSpace H] [MeasurableSpace E] [MeasurableSpace F]
    (rho : Measure H) [IsProbabilityMeasure rho]
    (q : ProbabilityMeasure E) (R : Kernel (ProbabilityMeasure E) F)
    [IsMarkovKernel R]
    {S : Set H} {T : Set F} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (rho ⊗ₘ Kernel.const H (R q)).real
        (Prod.fst ⁻¹' S ∩ Prod.snd ⁻¹' T) =
      rho.real S * (R q).real T := by
  have hrect : Prod.fst ⁻¹' S ∩ Prod.snd ⁻¹' T = S ×ˢ T := by
    ext z
    simp
  rw [hrect]
  change ((rho ⊗ₘ Kernel.const H (R q)) (S ×ˢ T)).toReal =
    (rho S).toReal * (R q T).toReal
  rw [Measure.compProd_apply_prod hS hT]
  simp_rw [Kernel.const_apply]
  rw [setLIntegral_const, ENNReal.toReal_mul]
  ring

/-- Specialization of the conditioned-history factorization to the fresh speedy
accept/restart transformer. -/
theorem freshSpeedyRestart_conditionedHistory_factorization
    {H : Type*} [MeasurableSpace H]
    (rho : Measure H) [IsProbabilityMeasure rho]
    (q : ProbabilityMeasure (Space n)) {c s : Real}
    {S : Set H} {T : Set (Space n)} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (rho ⊗ₘ Kernel.const H (freshSpeedyRestartKernel c s q)).real
        (Prod.fst ⁻¹' S ∩ Prod.snd ⁻¹' T) =
      rho.real S * (freshSpeedyRestartKernel c s q).real T :=
  freshRestart_conditionedHistory_factorization rho q
    (freshSpeedyRestartKernel c s) hS hT

/-- The same exact factorization for the complete source routine, including the first
condition-and-map stage.  In particular, after a history event has selected a proposal
law `q`, all rejection retries are fresh draws from the corresponding law-valued state. -/
theorem freshTwoStageSpeedyRestart_conditionedHistory_factorization
    {H E : Type*} [MeasurableSpace H] [MeasurableSpace E]
    (rho : Measure H) [IsProbabilityMeasure rho]
    (q : ProbabilityMeasure E) {A : Set E} (hA : MeasurableSet A)
    {f : E → Space n} (hf : Measurable f) {c s : Real}
    {S : Set H} {T : Set (Space n)} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (rho ⊗ₘ Kernel.const H
      (freshTwoStageSpeedyRestartKernel hA f hf c s q)).real
        (Prod.fst ⁻¹' S ∩ Prod.snd ⁻¹' T) =
      rho.real S *
        (freshTwoStageSpeedyRestartKernel hA f hf c s q).real T :=
  freshRestart_conditionedHistory_factorization rho q
    (freshTwoStageSpeedyRestartKernel hA f hf c s) hS hT

/-! Axiom audit. -/

#print axioms freshSpeedyRestartKernel_apply_eq_condOn_withDensity
#print axioms freshSpeedyRestartKernel_apply_eq_firstAcceptedPoint
#print axioms tvLe_freshSpeedyRestartKernel_apply
#print axioms freshConditionMapLaw_toMeasure_of_ne_zero
#print axioms freshTwoStageSpeedyRestartKernel_apply_eq
#print axioms tvLe_freshTwoStageSpeedyRestartKernel_apply
#print axioms freshRestart_conditionedHistory_factorization
#print axioms freshSpeedyRestart_conditionedHistory_factorization
#print axioms freshTwoStageSpeedyRestart_conditionedHistory_factorization

end Ttc.CVFreshRestartKernel
