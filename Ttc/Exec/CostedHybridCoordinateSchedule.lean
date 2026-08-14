/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Exec.CostedPackedWarmSchedule
import Ttc.Exec.CostedAmbientGaussianRejection

/-!
# An honest cold/warm costed coordinate family

This file combines the actual one-query ambient rejection law in genuinely cold phases
with an arbitrary certified costed warm-phase family everywhere else.  In particular, it
does not identify the paper's whole fixed-rate block `sigmaSq <= 1` with the much smaller
direct-rejection region `4*n*sigmaSq <= 1`.
-/

namespace Ttc.CostedHybridCoordinateSchedule

open MeasureTheory Metric Set
open Arlib Arlib.GaussianCooling
open Ttc.CV Ttc.CostedAmbientGaussianRejection
open Ttc.CostedPackedWarmSchedule
open scoped ENNReal Classical

variable {n r m k : Nat}

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- Branch between actual cold ambient rejection and the supplied costed walk law. -/
noncomputable def hybridCoordinateLaw
    (cold : Fin m → Prop) [DecidablePred cold]
    (K : Set (State n)) (sigmaSq : Fin m → Real)
    (warm : Fin r → Fin m → Fin k → Measure (ENNReal × State n))
    (j : Fin r) (i : Fin m) (l : Fin k) : Measure (ENNReal × State n) :=
  if cold i then coldPhaseCostLaw K (sigmaSq i) else warm j i l

theorem isProbabilityMeasure_hybridCoordinateLaw
    (cold : Fin m → Prop) [DecidablePred cold]
    {K : Set (State n)} (hKm : MeasurableSet K)
    {sigmaSq : Fin m → Real} (hsigma : ∀ i, 0 < sigmaSq i)
    (warm : Fin r → Fin m → Fin k → Measure (ENNReal × State n))
    (hwarmProb : ∀ j i l, IsProbabilityMeasure (warm j i l))
    (j : Fin r) (i : Fin m) (l : Fin k) :
    IsProbabilityMeasure
      (hybridCoordinateLaw cold K sigmaSq warm j i l) := by
  unfold hybridCoordinateLaw
  split_ifs with hi
  · exact isProbabilityMeasure_coldPhaseCostLaw K (hsigma i) hKm
  · exact hwarmProb j i l

/-- Exact state marginal of the branch-selected coordinate. -/
theorem map_snd_hybridCoordinateLaw
    (cold : Fin m → Prop) [DecidablePred cold]
    {K : Set (State n)} (hKm : MeasurableSet K)
    {sigmaSq : Fin m → Real} (hsigma : ∀ i, 0 < sigmaSq i)
    (warm : Fin r → Fin m → Fin k → Measure (ENNReal × State n))
    (warmState : Fin r → Fin m → Fin k → Measure (State n))
    (hwarmState : ∀ j i l, Measure.map Prod.snd (warm j i l) = warmState j i l)
    (j : Fin r) (i : Fin m) (l : Fin k)
    (hcoldPos : cold i → 0 < ambientGaussianProb (n := n) (sigmaSq i) K) :
    Measure.map Prod.snd (hybridCoordinateLaw cold K sigmaSq warm j i l) =
      if cold i then condOn (ambientGaussianProb (n := n) (sigmaSq i)) K
      else warmState j i l := by
  unfold hybridCoordinateLaw
  split_ifs with hi
  · exact map_snd_coldPhaseCostLaw hKm (hsigma i) (hcoldPos hi)
  · exact hwarmState j i l

/-- Coordinatewise expected-query certificate.  Cold phases cost at most two actual
membership queries in expectation, hence at most `12` after the common factor `6` used by
the warm-phase cost theorem. -/
theorem six_mul_lintegral_hybridCoordinateLaw_le
    (cold : Fin m → Prop) [DecidablePred cold]
    {K : Set (State n)} (hKm : MeasurableSet K) (hn : 1 ≤ n)
    {sigmaSq : Fin m → Real} (hsigma : ∀ i, 0 < sigmaSq i)
    (hcold : ∀ i, cold i → 4 * (n : Real) * sigmaSq i ≤ 1)
    (hball : closedBall (0 : State n) 1 ⊆ K)
    (warm : Fin r → Fin m → Fin k → Measure (ENNReal × State n))
    (warmBound : Fin r → Fin m → Fin k → ENNReal)
    (hwarmCost : ∀ j i l,
      6 * (∫⁻ z, z.1 ∂(warm j i l)) ≤ warmBound j i l)
    (j : Fin r) (i : Fin m) (l : Fin k) :
    6 * (∫⁻ z, z.1 ∂(hybridCoordinateLaw cold K sigmaSq warm j i l)) ≤
      if cold i then 12 else warmBound j i l := by
  unfold hybridCoordinateLaw
  split_ifs with hi
  · have htwo := lintegral_fst_coldPhaseCostLaw_le_two hKm hn
      (hsigma i) (hcold i hi) hball
    exact (mul_le_mul_left' htwo 6).trans_eq (by norm_num)
  · exact hwarmCost j i l

/-- The branch-selected family is a complete packed operational certificate. -/
theorem hybridCoordinateCostCertificate
    (cold : Fin m → Prop) [DecidablePred cold]
    {K : Set (State n)} (hKm : MeasurableSet K) (hn : 1 ≤ n)
    {sigmaSq : Fin m → Real} (hsigma : ∀ i, 0 < sigmaSq i)
    (hcold : ∀ i, cold i → 4 * (n : Real) * sigmaSq i ≤ 1)
    (hball : closedBall (0 : State n) 1 ⊆ K)
    (warm : Fin r → Fin m → Fin k → Measure (ENNReal × State n))
    (warmState : Fin r → Fin m → Fin k → Measure (State n))
    (warmBound : Fin r → Fin m → Fin k → ENNReal)
    (hwarmProb : ∀ j i l, IsProbabilityMeasure (warm j i l))
    (hwarmState : ∀ j i l, Measure.map Prod.snd (warm j i l) = warmState j i l)
    (hwarmCost : ∀ j i l,
      6 * (∫⁻ z, z.1 ∂(warm j i l)) ≤ warmBound j i l)
    (hcoldPos : ∀ i, cold i → 0 < ambientGaussianProb (n := n) (sigmaSq i) K) :
    HybridCoordinateCostCertificate
      (hybridCoordinateLaw cold K sigmaSq warm)
      (fun j i l => if cold i then
        condOn (ambientGaussianProb (n := n) (sigmaSq i)) K
        else warmState j i l)
      (fun j i l => if cold i then 12 else warmBound j i l) := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun j i l => isProbabilityMeasure_hybridCoordinateLaw cold hKm hsigma
      warm hwarmProb j i l
  · exact fun j i l => map_snd_hybridCoordinateLaw cold hKm hsigma
      warm warmState hwarmState j i l (hcoldPos i)
  · exact fun j i l => six_mul_lintegral_hybridCoordinateLaw_le cold hKm hn
      hsigma hcold hball warm warmBound hwarmCost j i l

#print axioms map_snd_hybridCoordinateLaw
#print axioms six_mul_lintegral_hybridCoordinateLaw_le
#print axioms hybridCoordinateCostCertificate

end Ttc.CostedHybridCoordinateSchedule
