/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.AmbientGaussianRejection
import Arlib.Probability.TVCoupling

/-!
# Finite-time approximation to a rejection sampler

Stopping a rejection loop after `T` rounds changes its output law by at most the probability
that the genuine loop needs more than `T` rounds.  The generic geometric tail in
`RejectionRounds` turns this into `nu Aᶜ ^ T`.  This is the probability-theoretic ingredient
needed to replace almost-surely finite loops by deterministic query cutoffs.
-/

namespace Ttc.CV

open MeasureTheory Set
open Arlib Arlib.Probability
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E]

/-- Return the genuine first accepted draw if it occurs by round `T`, and `fallback`
otherwise. -/
noncomputable def firstAcceptedCutoff (A : Set E) (T : ℕ) (fallback : E) :
    RoundSpace E → E := fun omega =>
  if roundCountNat A omega ≤ T then firstAcceptedDraw A omega else fallback

theorem measurable_firstAcceptedCutoff {A : Set E} (hA : MeasurableSet A)
    (T : ℕ) (fallback : E) : Measurable (firstAcceptedCutoff A T fallback) := by
  let S : Set (RoundSpace E) := {omega | roundCountNat A omega ≤ T}
  have hS : MeasurableSet S :=
    (measurable_roundCountNat hA) (measurableSet_Iic : MeasurableSet (Iic T))
  exact (measurable_firstAcceptedDraw hA).piecewise hS measurable_const

/-- The cutoff and the genuine loop can disagree only on the round-count tail. -/
theorem firstAcceptedCutoff_ne_subset {A : Set E} (T : ℕ) (fallback : E) :
    {omega | firstAcceptedCutoff A T fallback omega ≠ firstAcceptedDraw A omega} ⊆
      {omega | T < roundCountNat A omega} := by
  intro omega homega
  by_contra htail
  change ¬ T < roundCountNat A omega at htail
  have hle : roundCountNat A omega ≤ T := by omega
  exact homega (by simp [firstAcceptedCutoff, hle])

/-- A `T`-round rejection cutoff is within `nu(Aᶜ)^T` of the unlimited rejection output. -/
theorem tvLe_firstAcceptedCutoff_firstAcceptedDraw (nu : Measure E)
    [IsProbabilityMeasure nu] {A : Set E} (hA : MeasurableSet A)
    (T : ℕ) (fallback : E) :
    TVLe
      (Measure.map (firstAcceptedCutoff A T fallback) (roundsMeasure nu))
      (Measure.map (firstAcceptedDraw A) (roundsMeasure nu))
      (nu Aᶜ ^ T) := by
  apply tvLe_map_map_of_measure_ne_le
  · exact measurable_firstAcceptedCutoff hA T fallback
  · exact measurable_firstAcceptedDraw hA
  · exact (measure_mono (firstAcceptedCutoff_ne_subset T fallback)).trans
      (measure_lt_roundCountNat_le nu hA T)

/-- Consequently the cutoff approximates the exact conditional law with the same geometric
error whenever the acceptance event has positive probability. -/
theorem tvLe_firstAcceptedCutoff_condOn (nu : Measure E) [IsProbabilityMeasure nu]
    {A : Set E} (hA : MeasurableSet A) (hpos : 0 < nu A)
    (T : ℕ) (fallback : E) :
    TVLe
      (Measure.map (firstAcceptedCutoff A T fallback) (roundsMeasure nu))
      (Arlib.condOn nu A) (nu Aᶜ ^ T) := by
  rw [← map_firstAcceptedDraw_eq_condOn nu hA hpos]
  exact tvLe_firstAcceptedCutoff_firstAcceptedDraw nu hA T fallback

#print axioms tvLe_firstAcceptedCutoff_firstAcceptedDraw
#print axioms tvLe_firstAcceptedCutoff_condOn

end Ttc.CV
