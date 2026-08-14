/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.MarkovChains.Continuous.PolytopeHitAndRunExecution
import Ttc.Exec.CostedLazyHitAndRunAdapter
import Ttc.Exec.LazyProperProposalCost

/-!
# Facet-inspection cost for finite-polytope hit-and-run

The finite-facet kernel scans every inequality once to form the lower maximum and upper
minimum.  We record `card ι` as the facet-inspection cost of a non-lazy proposal.  Exact
real inner products, comparisons, division, and sampling from a real interval remain
abstract mathematical operations; this file does not claim a bit-complexity bound for
them.

The fair lazy wrapper records zero cost on its hold branch.  Consequently its expected
facet-inspection count is `(card ι)/2`, and forgetting the cost is exactly the repository's
`lazy (hitAndRun (Polytope.body A b))` kernel.
-/

namespace Ttc.FiniteFacetHitAndRunCost

open MeasureTheory ProbabilityTheory Set
open Arlib Arlib.MarkovChains
open Arlib.MarkovChains.PolytopeHitAndRunExecution
open Ttc.CostedLazyHitAndRunAdapter Ttc.LazyProperCost
open scoped ENNReal Classical

variable {n : Nat} {ι : Type*} [Fintype ι]

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- The recorded number of inspected facet inequalities. -/
def facetScanCost (ι : Type*) [Fintype ι] : ENNReal :=
  Fintype.card ι

/-- One finite-facet hit-and-run step carrying the deterministic full-scan count. -/
noncomputable def costedFiniteFacetHitAndRun
    (A : ι → State n) (b : ι → Real) : Kernel (State n) (ENNReal × State n) :=
  Kernel.map (finiteFacetHitAndRun A b)
    (fun y => (facetScanCost ι, y))

instance (A : ι → State n) (b : ι → Real) :
    IsMarkovKernel (costedFiniteFacetHitAndRun A b) := by
  unfold costedFiniteFacetHitAndRun
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

theorem map_snd_costedFiniteFacetHitAndRun
    (A : ι → State n) (b : ι → Real) (x : State n) :
    Measure.map Prod.snd (costedFiniteFacetHitAndRun A b x) =
      finiteFacetHitAndRun A b x := by
  rw [costedFiniteFacetHitAndRun, Kernel.map_apply _ (by fun_prop),
    Measure.map_map measurable_snd (by fun_prop)]
  simpa [Function.comp_def]

theorem lintegral_fst_costedFiniteFacetHitAndRun
    (A : ι → State n) (b : ι → Real) (x : State n) :
    (∫⁻ z, z.1 ∂costedFiniteFacetHitAndRun A b x) = facetScanCost ι := by
  rw [costedFiniteFacetHitAndRun, Kernel.map_apply _ (by fun_prop),
    lintegral_map measurable_fst (by fun_prop)]
  simp [facetScanCost]

/-- Fair lazy finite-facet hit-and-run with its realized inspection count. -/
noncomputable def lazyCostedFiniteFacetHitAndRun
    (A : ι → State n) (b : ι → Real) : Kernel (State n) (ENNReal × State n) :=
  lazyCostedKernel (costedFiniteFacetHitAndRun A b)

instance (A : ι → State n) (b : ι → Real) :
    IsMarkovKernel (lazyCostedFiniteFacetHitAndRun A b) := by
  unfold lazyCostedFiniteFacetHitAndRun
  infer_instance

theorem map_snd_lazyCostedFiniteFacetHitAndRun
    (A : ι → State n) (b : ι → Real) (x : State n) :
    Measure.map Prod.snd (lazyCostedFiniteFacetHitAndRun A b x) =
      lazy (finiteFacetHitAndRun A b) x := by
  exact map_snd_lazyCostedKernel _ _
    (map_snd_costedFiniteFacetHitAndRun A b) x

theorem lintegral_fst_lazyCostedFiniteFacetHitAndRun
    (A : ι → State n) (b : ι → Real) (x : State n) :
    (∫⁻ z, z.1 ∂lazyCostedFiniteFacetHitAndRun A b x) =
      (2 : ENNReal)⁻¹ * facetScanCost ι := by
  rw [lazyCostedFiniteFacetHitAndRun, lintegral_fst_lazyCostedKernel,
    lintegral_fst_costedFiniteFacetHitAndRun]

/-- The promised operational realization.  Its sole recorded cost is one complete scan of
the finite facet family on the active half of the lazy step. -/
noncomputable def lazyHitAndRunRealization
    (A : ι → State n) (b : ι → Real)
    (hK : Bornology.IsBounded (Arlib.Polytope.body A b)) [NeZero n] :
    LazyHitAndRunRealization (Arlib.Polytope.body A b) where
  kernel := lazyCostedFiniteFacetHitAndRun A b
  isMarkov := inferInstance
  forget := fun x => by
    rw [map_snd_lazyCostedFiniteFacetHitAndRun,
      finiteFacetHitAndRun_eq_hitAndRun A b hK]
  stepBound := (2 : ENNReal)⁻¹ * facetScanCost ι
  mean_le := fun x => (lintegral_fst_lazyCostedFiniteFacetHitAndRun A b x).le

/-- The exact per-step mean bound exposed by the generic realization interface. -/
theorem lazyHitAndRunRealization_stepBound
    (A : ι → State n) (b : ι → Real)
    (hK : Bornology.IsBounded (Arlib.Polytope.body A b)) [NeZero n] :
    (lazyHitAndRunRealization A b hK).stepBound =
      (2 : ENNReal)⁻¹ * Fintype.card ι := rfl

/-- The specialization used by KV97: its inflated body is the same finite system with
offsets `b i + kappaOf c r * ‖A i‖`. -/
noncomputable def lazyHitAndRunInflatedRealization
    (A : ι → State n) (b : ι → Real) (c r : Real)
    (hK : Bornology.IsBounded (Arlib.KV97.inflated A b c r)) [NeZero n] :
    LazyHitAndRunRealization (Arlib.KV97.inflated A b c r) := by
  let b' : ι → Real := fun i => b i + Arlib.KV97.kappaOf c r * ‖A i‖
  have hbody : Arlib.Polytope.body A b' = Arlib.KV97.inflated A b c r := rfl
  rw [← hbody] at hK ⊢
  exact lazyHitAndRunRealization A b' hK

theorem lazyHitAndRunInflatedRealization_stepBound
    (A : ι → State n) (b : ι → Real) (c r : Real)
    (hK : Bornology.IsBounded (Arlib.KV97.inflated A b c r)) [NeZero n] :
    (lazyHitAndRunInflatedRealization A b c r hK).stepBound =
      (2 : ENNReal)⁻¹ * Fintype.card ι := rfl

#print axioms map_snd_lazyCostedFiniteFacetHitAndRun
#print axioms lintegral_fst_lazyCostedFiniteFacetHitAndRun
#print axioms lazyHitAndRunRealization
#print axioms lazyHitAndRunInflatedRealization

end Ttc.FiniteFacetHitAndRunCost
