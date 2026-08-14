/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Exec.CostedWarmPhaseRejection
import Ttc.Volume.AmbientGaussianRejection

/-!
# Costed ambient-Gaussian rejection

This is the operational cold-phase counterpart of `CostedWarmPhaseRejection`.  One round
draws from the ambient spherical Gaussian, records one membership query, and returns the
drawn point.  Independent rounds are repeated until the point lies in `K`.
-/

namespace Ttc.CostedAmbientGaussianRejection

open MeasureTheory Metric Set
open Arlib Arlib.GaussianCooling
open Ttc.CV Ttc.CostedWarmPhaseRejection
open scoped ENNReal Classical

variable {n : Nat}

/-- A cold proposal annotated with its exact one-query cost. -/
noncomputable def oneQueryAmbientLaw (s : Real) :
    Measure (ENNReal × Space n) :=
  Measure.map (fun x : Space n => ((1 : ENNReal), x))
    (ambientGaussianProb (n := n) s)

theorem isProbabilityMeasure_oneQueryAmbientLaw {s : Real} (hs : 0 < s) :
    IsProbabilityMeasure (oneQueryAmbientLaw (n := n) s) := by
  letI : IsProbabilityMeasure (ambientGaussianProb (n := n) s) :=
    isProbabilityMeasure_ambientGaussianProb hs
  exact Measure.isProbabilityMeasure_map
    (measurable_const.prodMk measurable_id).aemeasurable

theorem map_snd_oneQueryAmbientLaw {s : Real} (hs : 0 < s) :
    Measure.map Prod.snd (oneQueryAmbientLaw (n := n) s) =
      ambientGaussianProb (n := n) s := by
  letI : IsProbabilityMeasure (ambientGaussianProb (n := n) s) :=
    isProbabilityMeasure_ambientGaussianProb hs
  let f : Space n → ENNReal × Space n := fun x => (1, x)
  have hf : Measurable f := measurable_const.prodMk measurable_id
  change Measure.map Prod.snd
      (Measure.map f (ambientGaussianProb (n := n) s)) = _
  calc
    Measure.map Prod.snd (Measure.map f (ambientGaussianProb (n := n) s)) =
        Measure.map (Prod.snd ∘ f) (ambientGaussianProb (n := n) s) :=
      Measure.map_map measurable_snd hf
    _ = Measure.map id (ambientGaussianProb (n := n) s) := by
      congr 2
    _ = ambientGaussianProb (n := n) s := Measure.map_id

theorem lintegral_fst_oneQueryAmbientLaw {s : Real} (hs : 0 < s) :
    ∫⁻ z, z.1 ∂(oneQueryAmbientLaw (n := n) s) = 1 := by
  letI : IsProbabilityMeasure (ambientGaussianProb (n := n) s) :=
    isProbabilityMeasure_ambientGaussianProb hs
  let f : Space n → ENNReal × Space n := fun x => (1, x)
  have hf : Measurable f := measurable_const.prodMk measurable_id
  change ∫⁻ z, z.1 ∂(Measure.map f (ambientGaussianProb (n := n) s)) = 1
  calc
    ∫⁻ z, z.1 ∂(Measure.map f (ambientGaussianProb (n := n) s)) =
        ∫⁻ x, (f x).1 ∂(ambientGaussianProb (n := n) s) :=
      lintegral_map measurable_fst hf
    _ = 1 := by simp [f]

/-- The actual cost/output law of ambient Gaussian draws repeated until membership in K. -/
noncomputable def coldPhaseCostLaw (K : Set (Space n)) (s : Real) :
    Measure (ENNReal × Space n) :=
  costedRejectionLaw (oneQueryAmbientLaw (n := n) s) K

theorem isProbabilityMeasure_coldPhaseCostLaw
    (K : Set (Space n)) {s : Real} (hs : 0 < s) (hKm : MeasurableSet K) :
    IsProbabilityMeasure (coldPhaseCostLaw (n := n) K s) := by
  letI : IsProbabilityMeasure (oneQueryAmbientLaw (n := n) s) :=
    isProbabilityMeasure_oneQueryAmbientLaw hs
  exact isProbabilityMeasure_costedRejectionLaw
    (oneQueryAmbientLaw (n := n) s) hKm

/-- Forgetting the query count gives exact ambient-Gaussian conditioning. -/
theorem map_snd_coldPhaseCostLaw
    {K : Set (Space n)} (hKm : MeasurableSet K) {s : Real} (hs : 0 < s)
    (hpos : 0 < ambientGaussianProb (n := n) s K) :
    Measure.map Prod.snd (coldPhaseCostLaw (n := n) K s) =
      condOn (ambientGaussianProb (n := n) s) K := by
  letI : IsProbabilityMeasure (oneQueryAmbientLaw (n := n) s) :=
    isProbabilityMeasure_oneQueryAmbientLaw hs
  have hf : Measurable (fun x : Space n => ((1 : ENNReal), x)) :=
    measurable_const.prodMk measurable_id
  have hmass : oneQueryAmbientLaw (n := n) s (liftedAccept K) =
      ambientGaussianProb (n := n) s K := by
    unfold liftedAccept
    rw [oneQueryAmbientLaw, Measure.map_apply hf
      (hKm.preimage measurable_snd)]
    rfl
  rw [coldPhaseCostLaw,
    map_snd_costedRejectionLaw (oneQueryAmbientLaw (n := n) s) hKm
      (by simpa [hmass] using hpos),
    map_snd_oneQueryAmbientLaw hs]

/-- At phase `i`, the operational cold sampler has exactly the cooling law. -/
theorem map_snd_coldPhaseCostLaw_eq_coolLaw
    {m : Nat} {sigmaSq : Nat → Real} (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (Space n)} (hKm : MeasurableSet K)
    (hball : ball (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i < m)
    (hpos : 0 < ambientGaussianProb (n := n) (sigmaSq i) K) :
    Measure.map Prod.snd
        (coldPhaseCostLaw (n := n) K (sigmaSq i)) =
      coolLaw m sigmaSq K i := by
  rw [map_snd_coldPhaseCostLaw hKm (hsigma i) hpos,
    condOn_ambientGaussianProb_eq_coolLaw hsigma hKm hball hfin hi]

/-- The exact expected membership-query count is the inverse acceptance mass. -/
theorem lintegral_fst_coldPhaseCostLaw
    {K : Set (Space n)} (hKm : MeasurableSet K) {s : Real} (hs : 0 < s) :
    ∫⁻ z, z.1 ∂(coldPhaseCostLaw (n := n) K s) =
      (ambientGaussianProb (n := n) s K)⁻¹ := by
  letI : IsProbabilityMeasure (oneQueryAmbientLaw (n := n) s) :=
    isProbabilityMeasure_oneQueryAmbientLaw hs
  rw [coldPhaseCostLaw,
    lintegral_fst_costedRejectionLaw (oneQueryAmbientLaw (n := n) s) hKm,
    lintegral_fst_oneQueryAmbientLaw hs, mul_one]
  have hf : Measurable (fun x : Space n => ((1 : ENNReal), x)) :=
    measurable_const.prodMk measurable_id
  rw [liftedAccept, oneQueryAmbientLaw,
    Measure.map_apply hf (hKm.preimage measurable_snd)]
  rfl

/-- In the cold regime, the actual recorded membership-query expectation is at most two. -/
theorem lintegral_fst_coldPhaseCostLaw_le_two
    {K : Set (Space n)} (hKm : MeasurableSet K) (hn : 1 ≤ n)
    {s : Real} (hs : 0 < s) (hcold : 4 * (n : Real) * s ≤ 1)
    (hball : closedBall (0 : Space n) 1 ⊆ K) :
    ∫⁻ z, z.1 ∂(coldPhaseCostLaw (n := n) K s) ≤ 2 := by
  rw [lintegral_fst_coldPhaseCostLaw hKm hs]
  have hacc := ambientGaussianProb_acceptance_ge_half hKm hn hs hcold hball
  have hhalf : ENNReal.ofReal (1 / 2 : Real) = (2 : ENNReal)⁻¹ := by
    norm_num [ENNReal.ofReal_div_of_pos]
  rw [hhalf] at hacc
  simpa using ENNReal.inv_le_inv' hacc

#print axioms map_snd_coldPhaseCostLaw_eq_coolLaw
#print axioms lintegral_fst_coldPhaseCostLaw
#print axioms lintegral_fst_coldPhaseCostLaw_le_two

end Ttc.CostedAmbientGaussianRejection
