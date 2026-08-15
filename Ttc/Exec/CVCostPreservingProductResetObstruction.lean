import Ttc.Exec.CVProductStateCostReset

/-!
# TV obstruction to a denotational independent stationary reset

A maximal-coupling/disintegration reset preserves the cost marginal, but it cannot
replace an operational graph-valued `(score,nextSeed)` law by an unrelated independent
product at small TV error.  The event lemma below records the exact obstruction used by
the switched CV audit: if the operational state is supported on a graph event and the
desired product target gives that graph event zero mass, every joint cost-preserving
reference is at TV distance at least one.

The statement is deliberately independent of how the reference was constructed.  Thus
maximal coupling is already optimal here; disintegration cannot remove the missing
state-marginal TV estimate.
-/

set_option autoImplicit false

namespace Ttc.CVCostPreservingProductResetObstruction

open MeasureTheory ProbabilityTheory
open Arlib
open scoped ENNReal

variable {Cost Score Seed : Type*}
  [MeasurableSpace Cost] [MeasurableSpace Score] [MeasurableSpace Seed]

/-- A measurable event of mass one versus mass zero forces TV error at least one. -/
theorem one_le_tvError_of_event_one_zero
    {X : Type*} [MeasurableSpace X]
    {mu nu : Measure X} {eps : ENNReal} {G : Set X}
    (hG : MeasurableSet G) (hmu : mu G = 1) (hnu : nu G = 0)
    (htv : TVLe mu nu eps) : 1 ≤ eps := by
  have h := htv.left hG
  simpa only [hmu, hnu, zero_add] using h

/-- Any costed reference whose state is the requested exact product is distance at
least one from an operational law supported on a product-null graph event.  Equality of
cost marginals is included to match the cost-preserving reset API, although the
obstruction already occurs after forgetting cost. -/
theorem one_le_tvError_of_costPreserving_productReset_graph
    (actual reference : Measure (Cost × (Score × Seed)))
    (scoreTarget : Measure Score) (seedTarget : Measure Seed)
    {eps : ENNReal} {G : Set (Score × Seed)}
    (hG : MeasurableSet G)
    (hactualGraph : Measure.map Prod.snd actual G = 1)
    (hreferenceState :
      Measure.map Prod.snd reference = scoreTarget.prod seedTarget)
    (hproductGraph : (scoreTarget.prod seedTarget) G = 0)
    (_hcost : Measure.map Prod.fst reference = Measure.map Prod.fst actual)
    (htv : TVLe actual reference eps) : 1 ≤ eps := by
  have hstate : TVLe (Measure.map Prod.snd actual)
      (Measure.map Prod.snd reference) eps := htv.map measurable_snd
  rw [hreferenceState] at hstate
  exact one_le_tvError_of_event_one_zero hG hactualGraph hproductGraph hstate

/-- Consequently the small-error premise needed by the source retained-reference
certificate is impossible whenever its target independent product is null on the
operational graph event. -/
theorem not_costPreserving_productReset_graph_of_error_lt_one
    (actual reference : Measure (Cost × (Score × Seed)))
    (scoreTarget : Measure Score) (seedTarget : Measure Seed)
    {eps : ENNReal} (heps : eps < 1) {G : Set (Score × Seed)}
    (hG : MeasurableSet G)
    (hactualGraph : Measure.map Prod.snd actual G = 1)
    (hreferenceState :
      Measure.map Prod.snd reference = scoreTarget.prod seedTarget)
    (hproductGraph : (scoreTarget.prod seedTarget) G = 0)
    (hcost : Measure.map Prod.fst reference = Measure.map Prod.fst actual) :
    ¬ TVLe actual reference eps := by
  intro htv
  exact (not_le_of_gt heps)
    (one_le_tvError_of_costPreserving_productReset_graph actual reference
      scoreTarget seedTarget hG hactualGraph hreferenceState hproductGraph hcost htv)

#print axioms one_le_tvError_of_event_one_zero
#print axioms one_le_tvError_of_costPreserving_productReset_graph
#print axioms not_costPreserving_productReset_graph_of_error_lt_one

end Ttc.CVCostPreservingProductResetObstruction
