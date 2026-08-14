/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Exec.CostedHybridCoordinateSchedule
import Ttc.Exec.CVCostedRuntimeCutoff

/-!
# Joint state projection of a costed packed CV execution

Coordinate marginals alone are insufficient to transport the estimator accuracy event.
This file proves that forgetting every cost coordinate maps the *entire* independently
restarted product law to the packed product of the corresponding state marginals.
-/

namespace Ttc.CostedPackedJointLaw

open MeasureTheory
open Arlib.Probability Arlib.GaussianCooling
open Ttc.CostedPackedWarmSchedule
open Ttc.CVCostedRuntimeCutoff
open scoped ENNReal Classical

variable {n r m k : Nat}

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- Forget the query counter in every packed coordinate. -/
def stateProjection
    (omega : CostedPackedSpace n r m k) :
    Arlib.Probability.RunSpace (Fin k → State n) r m :=
  fun j i l ↦ (omega j i l).2

theorem measurable_stateProjection :
    Measurable (stateProjection (n := n) (r := r) (m := m) (k := k)) := by
  exact measurable_pi_lambda _ fun j ↦ measurable_pi_lambda _ fun i ↦
    measurable_pi_lambda _ fun l ↦ measurable_snd.comp
      ((measurable_pi_apply l).comp
        ((measurable_pi_apply i).comp (measurable_pi_apply j)))

/-- Full joint-law identity, not merely equality of the elementary marginals. -/
theorem map_costedPackedLaw_stateProjection
    (rho : Fin r → Fin m → Fin k → Measure (ENNReal × State n))
    [∀ j i l, IsProbabilityMeasure (rho j i l)] :
    Measure.map stateProjection (costedPackedLaw rho) =
      Arlib.Probability.runMeasure
        (packedPhaseLaw (fun j i l ↦ Measure.map Prod.snd (rho j i l))) := by
  letI (j : Fin r) (i : Fin m) (l : Fin k) :
      IsProbabilityMeasure
        (Measure.map (fun z : ENNReal × State n ↦ z.2) (rho j i l)) :=
    Measure.isProbabilityMeasure_map
      (measurable_snd : Measurable (fun z : ENNReal × State n ↦ z.2)).aemeasurable
  unfold costedPackedLaw Arlib.Probability.runMeasure packedPhaseLaw stateProjection
  let fOuter : ∀ j : Fin r,
      (Fin m → Fin k → ENNReal × State n) → (Fin m → Fin k → State n) :=
    fun _ eta i l ↦ (eta i l).2
  change Measure.map (fun x j ↦ fOuter j (x j))
      (Measure.pi fun j ↦ Measure.pi fun i ↦ Measure.pi (rho j i)) = _
  calc
    _ = Measure.pi (fun j ↦
        Measure.map (fOuter j) (Measure.pi fun i ↦ Measure.pi (rho j i))) :=
      Measure.pi_map_pi (f := fOuter) (fun j ↦
        (measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun l ↦
          measurable_snd.comp ((measurable_pi_apply l).comp
            (measurable_pi_apply i))).aemeasurable)
    _ = _ := by
      congr 1
      funext j
      let fMiddle : ∀ i : Fin m,
          (Fin k → ENNReal × State n) → (Fin k → State n) :=
        fun _ eta l ↦ (eta l).2
      change Measure.map (fun x i ↦ fMiddle i (x i))
          (Measure.pi fun i ↦ Measure.pi (rho j i)) = _
      calc
        _ = Measure.pi (fun i ↦
            Measure.map (fMiddle i) (Measure.pi (rho j i))) :=
          Measure.pi_map_pi (f := fMiddle) (fun i ↦
            (measurable_pi_lambda _ fun l ↦
              measurable_snd.comp (measurable_pi_apply l)).aemeasurable)
        _ = _ := by
          congr 1
          funext i
          change Measure.map (fun x l ↦ Prod.snd (x l))
              (Measure.pi (rho j i)) = _
          exact Measure.pi_map_pi (μ := rho j i)
            (f := fun _ : Fin k ↦ fun z : ENNReal × State n ↦ z.2)
            (fun _ ↦ measurable_snd.aemeasurable)

/-- Rewriting the elementary state marginals yields the declared packed sampler law. -/
theorem map_costedPackedLaw_stateProjection_eq
    (rho : Fin r → Fin m → Fin k → Measure (ENNReal × State n))
    [∀ j i l, IsProbabilityMeasure (rho j i l)]
    (nu : Fin r → Fin m → Fin k → Measure (State n))
    (hstate : ∀ j i l, Measure.map Prod.snd (rho j i l) = nu j i l) :
    Measure.map stateProjection (costedPackedLaw rho) =
      Arlib.Probability.runMeasure (packedPhaseLaw nu) := by
  rw [map_costedPackedLaw_stateProjection]
  congr 3
  funext j i l
  exact hstate j i l

/-- Any measurable estimator of the states has exactly the same output law on the costed
execution as on the pre-existing packed sampler law. -/
theorem map_estimator_costedPackedLaw
    (rho : Fin r → Fin m → Fin k → Measure (ENNReal × State n))
    [∀ j i l, IsProbabilityMeasure (rho j i l)]
    (nu : Fin r → Fin m → Fin k → Measure (State n))
    (hstate : ∀ j i l, Measure.map Prod.snd (rho j i l) = nu j i l)
    (est : Arlib.Probability.RunSpace (Fin k → State n) r m → Real)
    (hest : Measurable est) :
    Measure.map (est ∘ stateProjection) (costedPackedLaw rho) =
      Measure.map est (Arlib.Probability.runMeasure (packedPhaseLaw nu)) := by
  rw [← Measure.map_map hest measurable_stateProjection,
    map_costedPackedLaw_stateProjection_eq rho nu hstate]

/-- Accuracy events transport from the existing packed sampler law to the same joint law
that carries the operational query count. -/
theorem measureReal_estimator_event_costedPackedLaw
    (rho : Fin r → Fin m → Fin k → Measure (ENNReal × State n))
    [∀ j i l, IsProbabilityMeasure (rho j i l)]
    (nu : Fin r → Fin m → Fin k → Measure (State n))
    (hstate : ∀ j i l, Measure.map Prod.snd (rho j i l) = nu j i l)
    (est : Arlib.Probability.RunSpace (Fin k → State n) r m → Real)
    (hest : Measurable est) {S : Set Real} (hS : MeasurableSet S) :
    (costedPackedLaw rho).real
        {omega | est (stateProjection omega) ∈ S} =
      (Arlib.Probability.runMeasure (packedPhaseLaw nu)).real
        {omega | est omega ∈ S} := by
  have hmap := map_estimator_costedPackedLaw rho nu hstate est hest
  have hleft :
      Measure.map (est ∘ stateProjection) (costedPackedLaw rho) S =
        costedPackedLaw rho {omega | est (stateProjection omega) ∈ S} := by
    rw [Measure.map_apply (hest.comp measurable_stateProjection) hS]
    rfl
  have hright :
      Measure.map est (Arlib.Probability.runMeasure (packedPhaseLaw nu)) S =
        Arlib.Probability.runMeasure (packedPhaseLaw nu) {omega | est omega ∈ S} := by
    rw [Measure.map_apply hest hS]
    rfl
  change (costedPackedLaw rho
      {omega | est (stateProjection omega) ∈ S}).toReal =
    (Arlib.Probability.runMeasure (packedPhaseLaw nu)
      {omega | est omega ∈ S}).toReal
  rw [← hleft, hmap, hright]

/-- The paper's `4/5 - 1/20 = 3/4` cutoff argument on the actual costed packed execution. -/
theorem cutoff_success_costedPackedLaw
    (rho : Fin r → Fin m → Fin k → Measure (ENNReal × State n))
    [∀ j i l, IsProbabilityMeasure (rho j i l)]
    (nu : Fin r → Fin m → Fin k → Measure (State n))
    (hstate : ∀ j i l, Measure.map Prod.snd (rho j i l) = nu j i l)
    (est : Arlib.Probability.RunSpace (Fin k → State n) r m → Real)
    (hest : Measurable est) {B L : ENNReal} (hL0 : L ≠ 0) (hLtop : L ≠ ⊤)
    (hmean : (∫⁻ omega, totalMembershipQueries omega ∂(costedPackedLaw rho)) ≤ B)
    (hratio : B / L ≤ ENNReal.ofReal (1 / 20 : Real))
    {fallback lo hi : Real}
    (haccuracy : 4 / 5 ≤
      (Arlib.Probability.runMeasure (packedPhaseLaw nu)).real
        {omega | est omega ∈ Set.Icc lo hi}) :
    3 / 4 ≤ (costedPackedLaw rho).real
      {omega | cutoffValue L fallback totalMembershipQueries
        (est ∘ stateProjection) omega ∈ Set.Icc lo hi} := by
  apply Ttc.CVCostedRuntimeCutoff.cutoff_success_three_quarters
    measurable_totalMembershipQueries (hest.comp measurable_stateProjection)
    hL0 hLtop hmean hratio
  change 4 / 5 ≤ (costedPackedLaw rho).real
    {omega | est (stateProjection omega) ∈ Set.Icc lo hi}
  rw [measureReal_estimator_event_costedPackedLaw rho nu hstate est hest
    measurableSet_Icc]
  exact haccuracy

#print axioms map_costedPackedLaw_stateProjection
#print axioms map_estimator_costedPackedLaw
#print axioms cutoff_success_costedPackedLaw

end Ttc.CostedPackedJointLaw
