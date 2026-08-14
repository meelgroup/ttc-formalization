/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.MarkovChains.Continuous.ColdTruncation
import Arlib.Probability.UniformOn

/-!
# Moment-radius truncation for a convex body

Lovasz--Vempala (2007), Lemma 5.7 states that if `X` has a log-concave distribution and
`E ||X||^2 <= R^2`, then, for `t > 1`,

`P(||X|| > t*R) < exp (1-t)`.

For the uniform distribution on a convex body, taking `t = 1 + log(1/eps)` therefore permits
truncation at radius `R*(1+log(1/eps))` with relative volume loss and total-variation cost at
most `eps`.  This file formalizes the complete volume/TV transport from that exact LV tail.

The analytic LV tail lemma itself is not yet present in the repository's log-concavity stack;
the named predicate below records its exact interface rather than assuming a circumradius.
-/

namespace Ttc.CVAdaptive

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains
open scoped ENNReal

variable {n : Nat}

/-- Exact usable interface of Lovasz--Vempala 2007, Lemma 5.7, after scaling the second
moment bound to `R`. -/
def LVNormTail (K : Set (EuclideanSpace Real (Fin n))) (R : Real) : Prop :=
  ∀ t : Real, 1 < t ->
    Arlib.uniformOn volume K {x | t * R < ‖x‖} <= ENNReal.ofReal (Real.exp (1 - t))

noncomputable def momentTruncationRadius (R eps : Real) : Real :=
  R * (1 + Real.log (1 / eps))

theorem momentTruncationRadius_pos {R eps : Real} (hR : 0 < R)
    (heps0 : 0 < eps) (heps1 : eps < 1) : 0 < momentTruncationRadius R eps := by
  have hinv : 1 < 1 / eps := by
    rw [lt_div_iff₀ heps0]
    simpa using heps1
  have hlog : 0 < Real.log (1 / eps) := Real.log_pos hinv
  unfold momentTruncationRadius
  positivity

private theorem tailSet_eq_sdiff_closedBall (K : Set (EuclideanSpace Real (Fin n)))
    (r : Real) :
    {x | r < ‖x‖} ∩ K = K \ closedBall 0 r := by
  ext x
  simp only [mem_inter_iff, mem_setOf_eq, mem_sdiff, mem_closedBall, not_le]
  aesop

/-- The LV tail at `t=1+log(1/eps)` is exactly an `eps` tail. -/
theorem lvNormTail_at_momentTruncationRadius
    {K : Set (EuclideanSpace Real (Fin n))} {R eps : Real}
    (hLV : LVNormTail K R) (heps0 : 0 < eps) (heps1 : eps < 1) :
    Arlib.uniformOn volume K
      {x | momentTruncationRadius R eps < ‖x‖} <= ENNReal.ofReal eps := by
  have hinv : 1 < 1 / eps := by
    rw [lt_div_iff₀ heps0]
    simpa using heps1
  have ht : 1 < 1 + Real.log (1 / eps) := by
    have := Real.log_pos hinv
    linarith
  have h := hLV (1 + Real.log (1 / eps)) ht
  have hexp : Real.exp (1 - (1 + Real.log (1 / eps))) = eps := by
    rw [show 1 - (1 + Real.log (1 / eps)) = -Real.log (1 / eps) by ring,
      Real.exp_neg, Real.exp_log (by positivity : 0 < 1 / eps)]
    field_simp
  simpa only [momentTruncationRadius, mul_comm, hexp] using h

/-- Relative volume loss of moment-radius truncation. -/
theorem volume_sdiff_momentTruncation_le_relative
    {K : Set (EuclideanSpace Real (Fin n))} (hKm : MeasurableSet K)
    {R eps : Real} (hLV : LVNormTail K R) (heps0 : 0 < eps) (heps1 : eps < 1) :
    volume (K \ closedBall 0 (momentTruncationRadius R eps)) / volume K <=
      ENNReal.ofReal eps := by
  have htail := lvNormTail_at_momentTruncationRadius hLV heps0 heps1
  rw [Arlib.uniformOn_apply volume hKm
    (measurableSet_lt measurable_const measurable_norm)] at htail
  rwa [tailSet_eq_sdiff_closedBall] at htail

/-- Truncation changes the uniform law by at most `eps` in total variation. -/
theorem tvLe_uniformOn_momentTruncation
    {K : Set (EuclideanSpace Real (Fin n))} (hKm : MeasurableSet K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    {R eps : Real} (hLV : LVNormTail K R) (heps0 : 0 < eps) (heps1 : eps < 1) :
    TVLe
      (Arlib.uniformOn volume (K ∩ closedBall 0 (momentTruncationRadius R eps)))
      (Arlib.uniformOn volume K) (ENNReal.ofReal eps) := by
  let A := K ∩ closedBall 0 (momentTruncationRadius R eps)
  have hAm : MeasurableSet A := hKm.inter measurableSet_closedBall
  have hratio : volume (K \ A) / volume K <= ENNReal.ofReal eps := by
    have h := volume_sdiff_momentTruncation_le_relative hKm hLV heps0 heps1
    simpa only [A, Set.sdiff_self_inter] using h
  have hepsENN : ENNReal.ofReal eps < 1 := by
    rw [ENNReal.ofReal_lt_one]
    exact heps1
  have hA0 : volume A ≠ 0 := by
    intro hAz
    have hadd : volume A + volume (K \ A) = volume K := by
      have h := measure_inter_add_sdiff (μ := volume) K hAm
      rwa [inter_eq_self_of_subset_right inter_subset_left] at h
    have htailEq : volume (K \ A) = volume K := by simpa [hAz] using hadd
    have : (1 : ENNReal) <= ENNReal.ofReal eps := by
      have hdiv : volume (K \ A) / volume K = 1 := by
        rw [htailEq, ENNReal.div_self hK0 hKtop]
      simpa [hdiv] using hratio
    exact (not_le_of_gt hepsENN) this
  exact (tvLe_condOn_subset hAm hKm inter_subset_left hA0 hKtop).mono hratio

end Ttc.CVAdaptive

#print axioms Ttc.CVAdaptive.lvNormTail_at_momentTruncationRadius
#print axioms Ttc.CVAdaptive.volume_sdiff_momentTruncation_le_relative
#print axioms Ttc.CVAdaptive.tvLe_uniformOn_momentTruncation
