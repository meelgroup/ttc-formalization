/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.RawGaussianSequentialQueryCost

/-!
# Recorded membership-query cost for the lazy ball walk

The Gaussian Metropolis walk at variance parameter `s = 0` has constant density and is
exactly the ordinary ball walk.  Consequently the proposal-retaining raw execution already
built for Gaussian cooling gives an honest execution of TTC's continuous ball-walk sampler:
every active proposal performs one membership query, while the fair lazy hold performs none.

This file accounts for the continuous chain only.  Kannan--Vempala randomized rounding and
its outer rejection loop are a separate sampler stage and are not charged here.
-/

namespace Ttc.RawBallWalkQueryCost

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains
open Ttc.RawGaussianQueryCost
open scoped ENNReal Classical

variable {n : Nat}

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

@[simp] theorem gaussianWeightReal_variance_zero (x : State n) :
    gaussianWeightReal 0 x = 1 := by
  simp [gaussianWeightReal]

@[simp] theorem gaussianWeight_variance_zero (x : State n) :
    gaussianWeight 0 x = 1 := by
  simp [gaussianWeight, gaussianWeightReal_variance_zero]

@[simp] theorem metropolisAccept_variance_zero (x y : State n) :
    metropolisAccept 0 x y = 1 := by
  simp [metropolisAccept]

theorem metropolisDensity_variance_zero (delta : Real) (x y : State n) :
    metropolisDensity 0 delta x y = (ball x delta).indicator 1 y := by
  by_cases hy : y ∈ ball x delta
  · simp [metropolisDensity, hy]
  · simp [metropolisDensity, hy]

theorem metropolisMove_variance_zero (K : Set (State n)) (delta : Real) (x : State n) :
    metropolisMove K delta 0 x = ell K delta x := by
  rw [metropolisMove_apply, ell_apply]
  congr 1
  simp_rw [metropolisDensity_variance_zero]
  rw [setLIntegral_indicator measurableSet_ball]
  simp

/-- At zero variance the Gaussian Metropolis kernel is literally the ball-walk kernel. -/
theorem metropolisGaussian_variance_zero_eq_ballWalk
    {K : Set (State n)} (hK : MeasurableSet K) (delta : Real) :
    metropolisGaussian K delta 0 = ballWalk K delta := by
  ext x T hT
  rw [metropolisGaussian_apply_set K delta 0 x hT,
    ballWalk_apply_set hK delta x hT,
    metropolisMove_variance_zero]
  congr 1
  simp_rw [metropolisDensity_variance_zero]
  rw [setLIntegral_indicator measurableSet_ball]
  simp only [Pi.one_apply, setLIntegral_one]
  congr 1
  apply congrArg volume
  ext y
  simp only [mem_inter_iff]
  tauto

/-- Forgetting recorded costs in one raw zero-variance step gives the ordinary ball walk. -/
theorem map_snd_lazyRawQueryCostedKernel_eq_ballWalk
    {K : Set (State n)} (hK : MeasurableSet K) (delta : Real) (hdelta : 0 < delta)
    (x : State n) :
    Measure.map Prod.snd (lazyRawQueryCostedKernel hK delta 0 hdelta x) =
      lazy (ballWalk K delta) x := by
  rw [map_snd_lazyRawQueryCostedKernel hK delta 0 hdelta x,
    metropolisGaussian_variance_zero_eq_ballWalk hK]

/-- The full recorded-query execution has exactly TTC's lazy ball-walk endpoint law. -/
theorem map_lazyRawQueryExecution_output_eq_ballWalk
    {K : Set (State n)} (hK : MeasurableSet K) (delta : Real) (hdelta : 0 < delta)
    (mu : Measure (State n)) [IsProbabilityMeasure mu] (t : Nat) :
    Measure.map (fun omega => (omega t).2)
        (lazyRawQueryExecution hK delta 0 hdelta mu) =
      iterate (lazy (ballWalk K delta)) mu t := by
  rw [map_lazyRawQueryExecution_output hK delta 0 hdelta mu t,
    metropolisGaussian_variance_zero_eq_ballWalk hK]

/-- Expected actual membership queries of `t` lazy ball-walk transitions are exactly
`t / 2`. -/
theorem lintegral_lazyBallWalkQueryCost
    {K : Set (State n)} (hK : MeasurableSet K) (delta : Real) (hdelta : 0 < delta)
    (mu : Measure (State n)) [IsProbabilityMeasure mu] (t : Nat) :
    (∫⁻ omega, Ttc.SequentialCost.totalCost t omega
        ∂lazyRawQueryExecution hK delta 0 hdelta mu) =
      (t : ENNReal) * (2 : ENNReal)⁻¹ :=
  lintegral_lazyRawQueryTotalCost hK delta 0 hdelta mu t

#print axioms metropolisGaussian_variance_zero_eq_ballWalk
#print axioms map_lazyRawQueryExecution_output_eq_ballWalk
#print axioms lintegral_lazyBallWalkQueryCost

end Ttc.RawBallWalkQueryCost
