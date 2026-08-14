/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.CostedAdaptiveIidCalls
import Ttc.Exec.KV97RoundedEndpointBridge
import Ttc.Process.PoissonLaws

/-!
# Honest cost accounting for finite marked call streams

This file supplies the execution layer that is independent of the remaining multinomial
identification.  A fresh iid stream of genuine costed calls is read up to a random count;
the output records both its actual prefix query cost and the empirical count vector of its
`Fin L` endpoints.

For a count bounded by `T`, the expected actual cost is at most `T` times the one-call
bound, directly via `CostedAdaptiveIidCalls`.  The count-vector marginal is exactly the
pushforward `markedCountLaw` below.  `MarkedPoissonIdentified` names the one remaining
measure theorem needed to rewrite that pushforward as `Ttc.countLaw` when the call count is
Poisson and the endpoint marginal is `q`.

An exact nondegenerate Poisson count is not bounded by any deterministic `T`; consequently
the bounded theorem is intended for TTC's accepted/cut-off branch.  An uncapped exact
Poisson execution instead needs the separate identity `E[N] = lambda` and has expected
cost `lambda * B`.
-/

namespace Ttc.CostedMarkedPoisson

open MeasureTheory ProbabilityTheory
open Ttc.CostedAdaptiveIidCalls
open scoped ENNReal BigOperators Classical

variable {L : Nat}

abbrev CostedMark (L : Nat) := ENNReal × Fin L
abbrev MarkStream (L : Nat) := Nat → CostedMark L

/-- Counts of each finite mark among the first `N` calls. -/
def prefixMarkCounts (N : Nat) (omega : MarkStream L) : Fin L → Nat :=
  fun a => ∑ j ∈ Finset.range N, if (omega j).2 = a then 1 else 0

theorem measurable_prefixMarkCounts (N : Nat) :
    Measurable (prefixMarkCounts (L := L) N) := by
  apply measurable_pi_lambda
  intro a
  unfold prefixMarkCounts
  apply Finset.measurable_sum
  intro j _hj
  exact Measurable.ite
    ((MeasurableSet.singleton a).preimage
      (measurable_snd.comp (measurable_pi_apply j)))
    measurable_const measurable_const

theorem measurable_randomPrefixMarkCounts :
    Measurable (fun p : Nat × MarkStream L => prefixMarkCounts p.1 p.2) := by
  apply measurable_from_prod_countable_right
  intro N
  exact measurable_prefixMarkCounts N

/-- The empirical-count law of a random number of genuine iid marked calls. -/
noncomputable def markedCountLaw
    (nu : Measure Nat) (xi : Measure (CostedMark L)) : Measure (Fin L → Nat) :=
  Measure.map (fun p : Nat × MarkStream L => prefixMarkCounts p.1 p.2)
    (adaptiveCallLaw nu xi)

/-- One narrow distributional binder remains: the empirical count pushforward of a
Poisson number of iid `q`-marked calls is the repository's point-mass definition of
`Ttc.countLaw`. -/
structure MarkedPoissonIdentified (lam : Real) (q : Fin L → Real)
    (xi : Measure (CostedMark L)) : Prop where
  count_eq : markedCountLaw (poissonMeasure lam.toNNReal) xi = Ttc.countLaw lam q

theorem measurable_randomPrefixQueryCost :
    Measurable (fun p : Nat × MarkStream L => prefixQueryCost p.1 p.2) := by
  apply measurable_from_prod_countable_right
  intro N
  exact measurable_prefixQueryCost N

/-- The uncapped honest execution: every reported mark contributes its recorded query cost. -/
noncomputable def actualCostedMarkedLaw
    (nu : Measure Nat) (xi : Measure (CostedMark L)) :
    Measure (ENNReal × (Fin L → Nat)) :=
  Measure.map
    (fun p : Nat × MarkStream L =>
      (prefixQueryCost p.1 p.2, prefixMarkCounts p.1 p.2))
    (adaptiveCallLaw nu xi)

theorem measurable_actualCostedMarkedMap :
    Measurable (fun p : Nat × MarkStream L =>
      (prefixQueryCost p.1 p.2, prefixMarkCounts p.1 p.2)) :=
  measurable_randomPrefixQueryCost.prodMk measurable_randomPrefixMarkCounts

instance isProbabilityMeasure_actualCostedMarkedLaw
    (nu : Measure Nat) [IsProbabilityMeasure nu]
    (xi : Measure (CostedMark L)) [IsProbabilityMeasure xi] :
    IsProbabilityMeasure (actualCostedMarkedLaw nu xi) := by
  unfold actualCostedMarkedLaw
  exact Measure.isProbabilityMeasure_map measurable_actualCostedMarkedMap.aemeasurable

theorem map_snd_actualCostedMarkedLaw
    (nu : Measure Nat) [IsProbabilityMeasure nu]
    (xi : Measure (CostedMark L)) [IsProbabilityMeasure xi] :
    Measure.map Prod.snd (actualCostedMarkedLaw nu xi) = markedCountLaw nu xi := by
  rw [actualCostedMarkedLaw, markedCountLaw,
    Measure.map_map measurable_snd measurable_actualCostedMarkedMap]
  rfl

/-- Exact random-prefix cost formula.  This is the honest uncapped replacement for a
nonexistent deterministic cap on a Poisson random variable. -/
theorem lintegral_fst_actualCostedMarkedLaw
    (nu : Measure Nat) [IsProbabilityMeasure nu]
    (xi : Measure (CostedMark L)) [IsProbabilityMeasure xi] :
    (∫⁻ z, z.1 ∂actualCostedMarkedLaw nu xi) =
      ∫⁻ N, (N : ENNReal) * (∫⁻ z, z.1 ∂xi) ∂nu := by
  rw [actualCostedMarkedLaw, lintegral_map measurable_fst measurable_actualCostedMarkedMap,
    adaptiveCallLaw, lintegral_prod _ measurable_randomPrefixQueryCost.aemeasurable]
  congr 1
  funext N
  exact lintegral_prefixQueryCost xi N

/-- If the random call count is genuinely supported below `T`, the actual summed cost has
the expected `T * B` bound. -/
theorem lintegral_fst_actualCostedMarkedLaw_le_of_ae_cap
    (nu : Measure Nat) [IsProbabilityMeasure nu]
    (xi : Measure (CostedMark L)) [IsProbabilityMeasure xi]
    (T : Nat) (hcap : ∀ᵐ N ∂nu, N ≤ T)
    {B : ENNReal} (hB : (∫⁻ z, z.1 ∂xi) ≤ B) :
    (∫⁻ z, z.1 ∂actualCostedMarkedLaw nu xi) ≤ (T : ENNReal) * B := by
  rw [lintegral_fst_actualCostedMarkedLaw]
  calc
    (∫⁻ N, (N : ENNReal) * (∫⁻ z, z.1 ∂xi) ∂nu) ≤
        ∫⁻ _N : Nat, (T : ENNReal) * B ∂nu := by
      apply lintegral_mono_ae
      filter_upwards [hcap] with N hN
      exact mul_le_mul (by exact_mod_cast hN) hB (by simp) (by simp)
    _ = (T : ENNReal) * B := by simp

/-- A bounded-call execution.  Its first coordinate is the actual sum of recorded call
costs whenever `N ≤ T`; the fixed-range presentation makes it measurable everywhere. -/
noncomputable def boundedCostedMarkedLaw
    (T : Nat) (nu : Measure Nat) (xi : Measure (CostedMark L)) :
    Measure (ENNReal × (Fin L → Nat)) :=
  Measure.map
    (fun p : Nat × MarkStream L =>
      (boundedAdaptiveQueryCost T id p, prefixMarkCounts p.1 p.2))
    (adaptiveCallLaw nu xi)

theorem measurable_boundedCostedMarkedMap (T : Nat) :
    Measurable (fun p : Nat × MarkStream L =>
      (boundedAdaptiveQueryCost T id p, prefixMarkCounts p.1 p.2)) := by
  apply Measurable.prodMk
  · exact measurable_boundedAdaptiveQueryCost T measurable_id
  · exact measurable_randomPrefixMarkCounts

instance isProbabilityMeasure_boundedCostedMarkedLaw
    (T : Nat) (nu : Measure Nat) [IsProbabilityMeasure nu]
    (xi : Measure (CostedMark L)) [IsProbabilityMeasure xi] :
    IsProbabilityMeasure (boundedCostedMarkedLaw T nu xi) := by
  unfold boundedCostedMarkedLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_boundedCostedMarkedMap (L := L) T).aemeasurable

/-- Forgetting costs gives exactly the empirical-count pushforward. -/
theorem map_snd_boundedCostedMarkedLaw
    (T : Nat) (nu : Measure Nat) [IsProbabilityMeasure nu]
    (xi : Measure (CostedMark L)) [IsProbabilityMeasure xi] :
    Measure.map Prod.snd (boundedCostedMarkedLaw T nu xi) = markedCountLaw nu xi := by
  rw [boundedCostedMarkedLaw, markedCountLaw,
    Measure.map_map measurable_snd (measurable_boundedCostedMarkedMap (L := L) T)]
  rfl

/-- Expected actual query cost for at most `T` genuine fresh calls. -/
theorem lintegral_fst_boundedCostedMarkedLaw_le
    (T : Nat) (nu : Measure Nat) [IsProbabilityMeasure nu]
    (xi : Measure (CostedMark L)) [IsProbabilityMeasure xi]
    {B : ENNReal} (hB : (∫⁻ z, z.1 ∂xi) ≤ B) :
    (∫⁻ z, z.1 ∂boundedCostedMarkedLaw T nu xi) ≤ (T : ENNReal) * B := by
  rw [boundedCostedMarkedLaw,
    lintegral_map measurable_fst (measurable_boundedCostedMarkedMap (L := L) T)]
  exact lintegral_boundedAdaptiveQueryCost_le nu xi T id measurable_id hB

/-- Under the explicit multinomial identification, the bounded costed execution has the
repository's `countLaw` marginal.  Notice that for a genuine Poisson `nu` this theorem is a
distributional statement; it does not assert the Poisson count is bounded by `T`. -/
theorem map_snd_boundedCostedMarkedLaw_eq_countLaw
    {lam : Real} {q : Fin L → Real}
    (xi : Measure (CostedMark L)) [IsProbabilityMeasure xi]
    (hident : MarkedPoissonIdentified lam q xi) (T : Nat) :
    Measure.map Prod.snd
        (boundedCostedMarkedLaw T (poissonMeasure lam.toNNReal) xi) =
      Ttc.countLaw lam q := by
  rw [map_snd_boundedCostedMarkedLaw]
  exact hident.count_eq

theorem map_snd_actualCostedMarkedLaw_eq_countLaw
    {lam : Real} {q : Fin L → Real}
    (xi : Measure (CostedMark L)) [IsProbabilityMeasure xi]
    (hident : MarkedPoissonIdentified lam q xi) :
    Measure.map Prod.snd
        (actualCostedMarkedLaw (poissonMeasure lam.toNNReal) xi) =
      Ttc.countLaw lam q := by
  rw [map_snd_actualCostedMarkedLaw]
  exact hident.count_eq

/-- Hence the operational count vector is a product of independent Poissons once the
usual nonnegative probability-vector hypotheses are supplied. -/
theorem map_snd_boundedCostedMarkedLaw_eq_pi
    {lam : Real} (hlam : 0 ≤ lam) {q : Fin L → Real}
    (hq0 : ∀ i, 0 ≤ q i) (hq : ∑ i, q i = 1)
    (xi : Measure (CostedMark L)) [IsProbabilityMeasure xi]
    (hident : MarkedPoissonIdentified lam q xi) (T : Nat) :
    Measure.map Prod.snd
        (boundedCostedMarkedLaw T (poissonMeasure lam.toNNReal) xi) =
      Measure.pi (fun i => poissonMeasure (lam * q i).toNNReal) := by
  rw [map_snd_boundedCostedMarkedLaw_eq_countLaw xi hident T,
    Ttc.countLaw_eq_pi hlam hq0 hq]

/-- Adapter from any genuine finite-endpoint cost package. -/
structure ExpectedQueryFiniteSampler (q : Fin L → Real) where
  law : Measure (CostedMark L)
  probability : IsProbabilityMeasure law
  stateMarginal : Measure.map Prod.snd law =
    Measure.sum (fun i : Fin L => ENNReal.ofReal (q i) • Measure.dirac i)
  expectedQueries : ENNReal
  expectedQueries_eq : (∫⁻ z, z.1 ∂law) = expectedQueries

/-- Cost theorem stated directly for a packaged genuine finite sampler. -/
theorem expectedQueries_boundedCostedMarkedLaw_le
    {q : Fin L → Real} (S : ExpectedQueryFiniteSampler q)
    (T : Nat) (nu : Measure Nat) [IsProbabilityMeasure nu] :
    letI : IsProbabilityMeasure S.law := S.probability
    (∫⁻ z, z.1 ∂boundedCostedMarkedLaw T nu S.law) ≤
      (T : ENNReal) * S.expectedQueries := by
  letI : IsProbabilityMeasure S.law := S.probability
  exact lintegral_fst_boundedCostedMarkedLaw_le T nu S.law S.expectedQueries_eq.le

#print axioms map_snd_boundedCostedMarkedLaw
#print axioms map_snd_actualCostedMarkedLaw
#print axioms lintegral_fst_actualCostedMarkedLaw
#print axioms lintegral_fst_actualCostedMarkedLaw_le_of_ae_cap
#print axioms lintegral_fst_boundedCostedMarkedLaw_le
#print axioms map_snd_boundedCostedMarkedLaw_eq_pi
#print axioms expectedQueries_boundedCostedMarkedLaw_le

end Ttc.CostedMarkedPoisson
