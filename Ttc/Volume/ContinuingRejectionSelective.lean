import Ttc.Volume.ContinuingRejectionSignificant

/-! Selective accuracy for finite continuing rejection: retries after survival becomes
insignificant are charged by their total mass, rather than required to mix. -/

namespace Ttc.ContinuingRejectionSelective

open MeasureTheory ProbabilityTheory Set
open Arlib
open Ttc.ContinuingRejectionSignificant
open scoped ENNReal Classical BigOperators

variable {E : Type*} [MeasurableSpace E]

/-- Weighted-error version of `tvLe_acceptedMixture`. -/
theorem tvLe_acceptedMixture_weighted
    (L : Nat) (w : Fin L → ENNReal) (q : Fin L → Measure E)
    (tau : Measure E) [IsProbabilityMeasure tau]
    (tail : ENNReal) (err : Fin L → ENNReal) (fallback : E)
    (hmass : (∑ i, w i) + tail = 1)
    (hq : ∀ i, TVLe (q i) tau (err i)) :
    TVLe (acceptedMixture L w q tail fallback) tau
      ((∑ i, w i * err i) + tail) := by
  intro S hS
  have hweights : ∑ i, w i ≤ 1 :=
    (le_add_right le_rfl).trans_eq hmass
  have htau : tau S ≤ 1 := prob_le_one
  have hsumEval : (∑ i, w i • q i) S = ∑ i, w i * q i S := by
    simpa only [Measure.smul_apply, smul_eq_mul] using
      (Measure.finsetSum_apply Finset.univ (fun i ↦ w i • q i) S)
  constructor
  · rw [acceptedMixture, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply' _ hS, hsumEval]
    simp only [smul_eq_mul]
    have hsum : (∑ i, w i * q i S) ≤
        ∑ i, w i * (tau S + err i) :=
      Finset.sum_le_sum fun i _ ↦ mul_le_mul_left' ((hq i).left hS) (w i)
    have htailInd : tail * S.indicator 1 fallback ≤ tail := by
      by_cases hf : fallback ∈ S <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hf]
    calc
      (∑ i, w i * q i S) + tail * S.indicator 1 fallback ≤
          (∑ i, w i * (tau S + err i)) + tail := add_le_add hsum htailInd
      _ = (∑ i, w i) * tau S + (∑ i, w i * err i) + tail := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ ≤ tau S + (∑ i, w i * err i) + tail := by
        gcongr
        exact mul_le_of_le_one_left (by simp) hweights
      _ = tau S + ((∑ i, w i * err i) + tail) := by rw [add_assoc]
  · rw [acceptedMixture, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply' _ hS, hsumEval]
    simp only [smul_eq_mul]
    have hweighted : (∑ i, w i) * tau S ≤
        (∑ i, w i * q i S) + (∑ i, w i * err i) := by
      calc
        (∑ i, w i) * tau S = ∑ i, w i * tau S := by rw [Finset.sum_mul]
        _ ≤ ∑ i, w i * (q i S + err i) := by
          exact Finset.sum_le_sum fun i _ ↦
            mul_le_mul_left' ((hq i).right hS) (w i)
        _ = (∑ i, w i * q i S) + (∑ i, w i * err i) := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
    calc
      tau S = ((∑ i, w i) + tail) * tau S := by rw [hmass, one_mul]
      _ = (∑ i, w i) * tau S + tail * tau S := by rw [add_mul]
      _ ≤ ((∑ i, w i * q i S) + (∑ i, w i * err i)) + tail := by
        exact add_le_add hweighted (mul_le_of_le_one_right (by simp) htau)
      _ ≤ ((∑ i, w i * q i S) + tail * S.indicator 1 fallback) +
          ((∑ i, w i * err i) + tail) := by
        calc
          _ ≤ ((∑ i, w i * q i S) + (∑ i, w i * err i) + tail) +
              tail * S.indicator 1 fallback := le_add_right le_rfl
          _ = _ := by ac_rfl

/-- Only significant retries need an accurate accepted law.  All inaccurate retry weights,
together with the unresolved tail, are charged through `badMass`. -/
theorem tvLe_acceptedMixture_selective
    (L : Nat) (w : Fin L → ENNReal) (q : Fin L → Measure E)
    [∀ i : Fin L, IsProbabilityMeasure (q i)]
    (tau : Measure E) [IsProbabilityMeasure tau]
    (tail delta eta : ENNReal) (fallback : E)
    (Good : Fin L → Prop) [DecidablePred Good]
    (hmass : (∑ i, w i) + tail = 1)
    (hq : ∀ i, Good i → TVLe (q i) tau delta)
    (hbad : (∑ i with ¬ Good i, w i) + tail ≤ eta) :
    TVLe (acceptedMixture L w q tail fallback) tau (delta + eta) := by
  let err : Fin L → ENNReal := fun i ↦ if Good i then delta else 1
  have herrTV : ∀ i, TVLe (q i) tau (err i) := by
    intro i
    by_cases hi : Good i
    · simpa only [err, if_pos hi] using hq i hi
    · simpa only [err, if_neg hi] using Arlib.tvLe_one (q i) tau
  have hweights : ∑ i, w i ≤ 1 :=
    (le_add_right le_rfl).trans_eq hmass
  have herrBound : (∑ i, w i * err i) + tail ≤ delta + eta := by
    have hterm : ∀ i, w i * err i ≤
        w i * delta + if ¬ Good i then w i else 0 := by
      intro i
      by_cases hi : Good i
      · simp [err, hi]
      · simp [err, hi]
    calc
      (∑ i, w i * err i) + tail ≤
          (∑ i, (w i * delta + if ¬ Good i then w i else 0)) + tail := by
            gcongr with i
            exact hterm i
      _ = (∑ i, w i) * delta + ((∑ i with ¬ Good i, w i) + tail) := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
        rw [Finset.sum_filter]
        ac_rfl
      _ ≤ delta + eta := add_le_add
        (mul_le_of_le_one_left (by simp) hweights) hbad
  exact (tvLe_acceptedMixture_weighted L w q tau tail err fallback hmass herrTV).mono
    herrBound

/-- Telescoping identity for survival weights on a suffix. -/
theorem sum_Ico_weight_add_survival
    (w s : Nat → ENNReal) (L : Nat)
    (hrec : ∀ j, j < L → w j + s (j + 1) = s j) :
    ∀ a, a ≤ L → (∑ j ∈ Finset.Ico a L, w j) + s L = s a := by
  induction L with
  | zero =>
      intro a ha
      have : a = 0 := Nat.eq_zero_of_le_zero ha
      subst a
      simp
  | succ L ih =>
      intro a ha
      by_cases halast : a = L + 1
      · subst a
        simp
      · have haL : a ≤ L := by omega
        rw [Finset.sum_Ico_succ_top haL]
        calc
          ((∑ j ∈ Finset.Ico a L, w j) + w L) + s (L + 1) =
              (∑ j ∈ Finset.Ico a L, w j) + (w L + s (L + 1)) := by
                rw [add_assoc]
          _ = (∑ j ∈ Finset.Ico a L, w j) + s L := by
                rw [hrec L (by omega)]
          _ = s a := ih (fun j hj ↦ hrec j (by omega)) a haL

/-- With exact first-hit conservation, inaccurate retries begin only after survival has
fallen below `eta`.  Their combined weight plus the unresolved tail is therefore at most
`eta`; if survival never becomes insignificant, the usual geometric tail `r^L` applies. -/
theorem badWeights_add_survival_le_eta_add_pow
    (w s : Nat → ENNReal) (L : Nat) (eta r : ENNReal)
    (hrec : ∀ j, j < L → w j + s (j + 1) = s j)
    (hs0 : s 0 ≤ 1) (hr : r ≤ 1)
    (hmono : ∀ j, s (j + 1) ≤ s j)
    (hcontract : ∀ j, eta ≤ s j → s (j + 1) ≤ r * s j) :
    (∑ j ∈ (Finset.range L).filter (fun j ↦ ¬ eta ≤ s j), w j) + s L ≤
      eta + r ^ L := by
  classical
  let bad := (Finset.range L).filter (fun j ↦ ¬ eta ≤ s j)
  by_cases hbadEmpty : bad = ∅
  · rw [show (Finset.range L).filter (fun j ↦ ¬ eta ≤ s j) = ∅ from hbadEmpty]
    simp only [Finset.sum_empty, zero_add]
    exact survival_le_eta_add_pow s hs0 hr hmono hcontract L
  · let j0 := bad.min' (Finset.nonempty_iff_ne_empty.2 hbadEmpty)
    have hj0mem : j0 ∈ bad := Finset.min'_mem _ _
    have hj0small : s j0 ≤ eta := by
      have : ¬ eta ≤ s j0 := (Finset.mem_filter.1 hj0mem).2
      exact le_of_not_ge this
    have hsubset : bad ⊆ Finset.Ico j0 L := by
      intro j hj
      have hjrange : j ∈ Finset.range L := (Finset.mem_filter.1 hj).1
      exact Finset.mem_Ico.2 ⟨Finset.min'_le _ _ hj, Finset.mem_range.1 hjrange⟩
    have hsum : (∑ j ∈ bad, w j) ≤ ∑ j ∈ Finset.Ico j0 L, w j := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ ↦ bot_le)
    have hj0L : j0 ≤ L := (Finset.mem_range.1 (Finset.mem_filter.1 hj0mem).1).le
    have hsuffix := sum_Ico_weight_add_survival w s L hrec j0 hj0L
    calc
      (∑ j ∈ (Finset.range L).filter (fun j ↦ ¬ eta ≤ s j), w j) + s L =
          (∑ j ∈ bad, w j) + s L := rfl
      _ ≤ (∑ j ∈ Finset.Ico j0 L, w j) + s L := add_le_add hsum le_rfl
      _ = s j0 := hsuffix
      _ ≤ eta := hj0small
      _ ≤ eta + r ^ L := le_add_right le_rfl

#print axioms tvLe_acceptedMixture_weighted
#print axioms tvLe_acceptedMixture_selective
#print axioms badWeights_add_survival_le_eta_add_pow

end Ttc.ContinuingRejectionSelective
