/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Probability.Independence.InfinitePi

/-!
# A bounded adaptive number of honest iid costed calls

TTC's `GenerateSamples` count is determined by the state of the main loop, but is
bounded by the deterministic `Thresh` appearing in the runtime proof.  This file
provides the measure-theoretic accounting primitive for that situation.  The cost
stream consists of iid copies of a genuine `(query count, endpoint)` law; the caller
may read any measurable number of its initial coordinates up to a fixed bound.

The main theorem charges at most `T * B` expected queries when one call has expected
cost at most `B`.  It does not replace the random cost by a modelling price, and it
does not require the adaptive call count to be independent of the preceding state:
independence is supplied by the product with the fresh iid stream.
-/

namespace Ttc.CostedAdaptiveIidCalls

open MeasureTheory
open scoped ENNReal BigOperators

variable {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]

abbrev CostedCall (E : Type*) := ENNReal × E
abbrev CostedStream (E : Type*) := Nat → CostedCall E

/-- A countable iid stream of costed oracle calls. -/
noncomputable def iidCostedStreamLaw (xi : Measure (CostedCall E)) :
    Measure (CostedStream E) :=
  Measure.infinitePi (fun _ : Nat ↦ xi)

instance iidCostedStreamLaw.isProbabilityMeasure
    (xi : Measure (CostedCall E)) [IsProbabilityMeasure xi] :
    IsProbabilityMeasure (iidCostedStreamLaw xi) := by
  unfold iidCostedStreamLaw
  infer_instance

/-- Total recorded query cost of the first `N` calls. -/
noncomputable def prefixQueryCost (N : Nat) (omega : CostedStream E) : ENNReal :=
  ∑ i ∈ Finset.range N, (omega i).1

theorem measurable_prefixQueryCost (N : Nat) :
    Measurable (prefixQueryCost (E := E) N) := by
  unfold prefixQueryCost
  apply Finset.measurable_sum
  intro i _hi
  exact measurable_fst.comp (measurable_pi_apply i)

/-- Every coordinate of the iid stream has the supplied one-call law. -/
theorem map_eval_iidCostedStreamLaw
    (xi : Measure (CostedCall E)) [IsProbabilityMeasure xi] (i : Nat) :
    Measure.map (fun omega : CostedStream E ↦ omega i) (iidCostedStreamLaw xi) = xi := by
  unfold iidCostedStreamLaw
  exact Measure.infinitePi_map_eval (fun _ : Nat ↦ xi) i

/-- Exact expected query count of a deterministic finite prefix. -/
theorem lintegral_prefixQueryCost
    (xi : Measure (CostedCall E)) [IsProbabilityMeasure xi] (N : Nat) :
    (∫⁻ omega, prefixQueryCost N omega ∂iidCostedStreamLaw xi) =
      (N : ENNReal) * ∫⁻ z, z.1 ∂xi := by
  unfold prefixQueryCost
  rw [lintegral_finsetSum]
  · calc
      ∑ i ∈ Finset.range N,
          ∫⁻ omega, (omega i).1 ∂iidCostedStreamLaw xi =
          ∑ _i ∈ Finset.range N, ∫⁻ z, z.1 ∂xi := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [← lintegral_map measurable_fst (measurable_pi_apply i),
              map_eval_iidCostedStreamLaw xi i]
      _ = (N : ENNReal) * ∫⁻ z, z.1 ∂xi := by
        simp [nsmul_eq_mul]
  · intro i _hi
    exact measurable_fst.comp (measurable_pi_apply i)

/-- Joint law of an arbitrary preceding state and a fresh iid costed-call stream. -/
noncomputable def adaptiveCallLaw
    (nu : Measure Omega) (xi : Measure (CostedCall E)) :
    Measure (Omega × CostedStream E) :=
  nu.prod (iidCostedStreamLaw xi)

instance adaptiveCallLaw.isProbabilityMeasure
    (nu : Measure Omega) [IsProbabilityMeasure nu]
    (xi : Measure (CostedCall E)) [IsProbabilityMeasure xi] :
    IsProbabilityMeasure (adaptiveCallLaw nu xi) := by
  unfold adaptiveCallLaw
  infer_instance

/-- Query count for an adaptive prefix, written over a fixed finite range `T`.

When `count state ≤ T`, this is literally the sum of the first `count state` recorded
costs.  The fixed-range presentation makes measurability transparent. -/
noncomputable def boundedAdaptiveQueryCost (T : Nat) (count : Omega → Nat)
    (p : Omega × CostedStream E) : ENNReal :=
  ∑ i ∈ Finset.range T, if i < count p.1 then (p.2 i).1 else 0

theorem measurable_boundedAdaptiveQueryCost (T : Nat) {count : Omega → Nat}
    (hcount : Measurable count) :
    Measurable (boundedAdaptiveQueryCost (E := E) T count) := by
  unfold boundedAdaptiveQueryCost
  apply Finset.measurable_sum
  intro i _hi
  apply Measurable.ite
  · exact measurableSet_lt measurable_const (hcount.comp measurable_fst)
  · exact measurable_fst.comp ((measurable_pi_apply i).comp measurable_snd)
  · exact measurable_const

theorem boundedAdaptiveQueryCost_eq_prefix
    (T : Nat) (count : Omega → Nat) (p : Omega × CostedStream E)
    (hcount : count p.1 ≤ T) :
    boundedAdaptiveQueryCost T count p = prefixQueryCost (count p.1) p.2 := by
  unfold boundedAdaptiveQueryCost prefixQueryCost
  rw [← Finset.sum_subset (Finset.range_mono hcount)]
  · apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [if_pos hi]
  · intro i hiT hiN
    simp only [Finset.mem_range] at hiT hiN ⊢
    rw [if_neg hiN]

/-- Honest expected-query bound for at most `T` fresh iid calls.

The adaptive count may depend arbitrarily on the preceding state.  Each summand is
bounded by the corresponding fresh call cost, and product integration then exposes
the one-call expectation. -/
theorem lintegral_boundedAdaptiveQueryCost_le
    (nu : Measure Omega) [IsProbabilityMeasure nu]
    (xi : Measure (CostedCall E)) [IsProbabilityMeasure xi]
    (T : Nat) (count : Omega → Nat) (hcount : Measurable count) {B : ENNReal}
    (hB : (∫⁻ z, z.1 ∂xi) ≤ B) :
    (∫⁻ p, boundedAdaptiveQueryCost T count p ∂adaptiveCallLaw nu xi) ≤
      (T : ENNReal) * B := by
  unfold boundedAdaptiveQueryCost adaptiveCallLaw
  rw [lintegral_finsetSum]
  · calc
      ∑ i ∈ Finset.range T,
          ∫⁻ p, (if i < count p.1 then (p.2 i).1 else 0) ∂nu.prod (iidCostedStreamLaw xi) ≤
          ∑ _i ∈ Finset.range T, ∫⁻ z, z.1 ∂xi := by
            apply Finset.sum_le_sum
            intro i _hi
            calc
              _ ≤ ∫⁻ p, (p.2 i).1 ∂nu.prod (iidCostedStreamLaw xi) :=
                lintegral_mono fun p ↦ by split_ifs <;> simp
              _ = ∫⁻ z, z.1 ∂xi := by
                have hcosti : Measurable
                    (fun y : CostedStream E ↦ (y i).1) :=
                  measurable_fst.comp (measurable_pi_apply i)
                rw [(measurePreserving_snd (μ := nu)
                  (ν := iidCostedStreamLaw xi)).lintegral_comp hcosti]
                rw [← lintegral_map measurable_fst (measurable_pi_apply i),
                  map_eval_iidCostedStreamLaw xi i]
      _ ≤ ∑ _i ∈ Finset.range T, B := Finset.sum_le_sum fun _i _hi ↦ hB
      _ = (T : ENNReal) * B := by simp [nsmul_eq_mul]
  · intro i _hi
    have hcosti : Measurable
        (fun p : Omega × CostedStream E ↦ (p.2 i).1) :=
      (show Measurable (fun z : CostedCall E ↦ z.1) from measurable_fst).comp
        ((show Measurable (fun y : CostedStream E ↦ y i) from
          measurable_pi_apply i).comp measurable_snd)
    exact (Measurable.ite
      (measurableSet_lt (measurable_const : Measurable fun _p : Omega × CostedStream E ↦ i)
        (hcount.comp measurable_fst))
      hcosti
      (measurable_const : Measurable fun _p : Omega × CostedStream E ↦ (0 : ENNReal)))

#print axioms lintegral_prefixQueryCost
#print axioms lintegral_boundedAdaptiveQueryCost_le

end Ttc.CostedAdaptiveIidCalls
