import Ttc.Exec.TVMaximalCoupling
import Arlib.Probability.TVTensor

/-!
# Cost-preserving exact product references for refreshed CV phases

The independent seed refresh is most useful on the proof/reference side.  Once a phase's
score marginal is close to its exact target, tensoring with an exact fresh seed gives a
full `(score, seed)` product target with the same TV error.  A maximal coupling followed
by disintegration then changes only the reference state: the operational cost marginal is
preserved exactly.
-/

set_option autoImplicit false

namespace Ttc.CVProductStateCostReset

open MeasureTheory ProbabilityTheory
open Arlib
open scoped ENNReal Classical

variable {Cost Score Seed : Type*}
  [MeasurableSpace Cost] [MeasurableSpace Score] [MeasurableSpace Seed]

/-- Tensoring a score approximation with the same independent seed law spends no
additional TV error. -/
theorem tvLe_prod_exactSeed
    (scoreActual scoreTarget : Measure Score)
    [IsProbabilityMeasure scoreActual] [IsProbabilityMeasure scoreTarget]
    (seedTarget : Measure Seed) [IsProbabilityMeasure seedTarget]
    {eps : ENNReal} (hscore : TVLe scoreActual scoreTarget eps) :
    TVLe (scoreActual.prod seedTarget) (scoreTarget.prod seedTarget) eps := by
  simpa only [add_zero] using hscore.prod (TVLe.refl seedTarget)

/-- A costed operational phase whose state marginal is TV-close to an exact product has
a reference law with:

* exactly the same cost marginal;
* exactly the requested independent score/seed state law;
* no increase in TV error.

This is the reference to append to retained histories.  It does not sample the exact
target operationally and therefore introduces no circular oracle call. -/
theorem exists_costPreserving_productStateReference_of_tvLe
    [StandardBorelSpace Score] [StandardBorelSpace Seed]
    [Nonempty Score] [Nonempty Seed]
    (actual : Measure (Cost × (Score × Seed))) [IsProbabilityMeasure actual]
    (scoreTarget : Measure Score) [IsProbabilityMeasure scoreTarget]
    (seedTarget : Measure Seed) [IsProbabilityMeasure seedTarget]
    {eps : ENNReal}
    (hstate : TVLe (Measure.map Prod.snd actual)
      (scoreTarget.prod seedTarget) eps) :
    ∃ reference : Measure (Cost × (Score × Seed)),
      IsProbabilityMeasure reference ∧
      Measure.map Prod.fst reference = Measure.map Prod.fst actual ∧
      Measure.map Prod.snd reference = scoreTarget.prod seedTarget ∧
      Measure.map (fun z : Cost × (Score × Seed) ↦ z.2.1) reference = scoreTarget ∧
      Measure.map (fun z : Cost × (Score × Seed) ↦ z.2.2) reference = seedTarget ∧
      TVLe actual reference eps := by
  obtain ⟨reference, hrefProb, hcost, hpair, htv⟩ :=
    Ttc.TVMaximalCoupling.exists_costPreserving_reset_of_tvLe
      actual (scoreTarget.prod seedTarget) hstate
  refine ⟨reference, hrefProb, hcost, hpair, ?_, ?_, htv⟩
  · have h := congrArg (Measure.map Prod.fst) hpair
    rw [Measure.map_map measurable_fst measurable_snd] at h
    simpa [Function.comp_def] using h
  · have h := congrArg (Measure.map Prod.snd) hpair
    rw [Measure.map_map measurable_snd measurable_snd] at h
    simpa [Function.comp_def] using h

/-- Common phase-level capstone: a score TV theorem plus an exact independent refresh
law immediately yields a cost-preserving full product reference. -/
theorem exists_costPreserving_productStateReference_of_scoreTV
    [StandardBorelSpace Score] [StandardBorelSpace Seed]
    [Nonempty Score] [Nonempty Seed]
    (actual : Measure (Cost × (Score × Seed))) [IsProbabilityMeasure actual]
    (scoreActual scoreTarget : Measure Score)
    [IsProbabilityMeasure scoreActual] [IsProbabilityMeasure scoreTarget]
    (seedTarget : Measure Seed) [IsProbabilityMeasure seedTarget]
    (hstate : Measure.map Prod.snd actual = scoreActual.prod seedTarget)
    {eps : ENNReal} (hscore : TVLe scoreActual scoreTarget eps) :
    ∃ reference : Measure (Cost × (Score × Seed)),
      IsProbabilityMeasure reference ∧
      Measure.map Prod.fst reference = Measure.map Prod.fst actual ∧
      Measure.map Prod.snd reference = scoreTarget.prod seedTarget ∧
      Measure.map (fun z : Cost × (Score × Seed) ↦ z.2.1) reference = scoreTarget ∧
      Measure.map (fun z : Cost × (Score × Seed) ↦ z.2.2) reference = seedTarget ∧
      TVLe actual reference eps := by
  apply exists_costPreserving_productStateReference_of_tvLe actual scoreTarget seedTarget
  rw [hstate]
  exact tvLe_prod_exactSeed scoreActual scoreTarget seedTarget hscore

#print axioms tvLe_prod_exactSeed
#print axioms exists_costPreserving_productStateReference_of_tvLe
#print axioms exists_costPreserving_productStateReference_of_scoreTV

end Ttc.CVProductStateCostReset
