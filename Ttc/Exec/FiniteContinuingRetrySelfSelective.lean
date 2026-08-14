import Ttc.Exec.FiniteContinuingRetrySelfDecomposition
import Ttc.Volume.ContinuingRejectionSelective

/-! Selective first-hit TV with an arbitrary self-fallback tail measure. -/

namespace Ttc.FiniteContinuingRetrySelfSelective

open MeasureTheory ProbabilityTheory Set
open Arlib
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetrySelfFallback
open Ttc.FiniteContinuingRetrySelfDecomposition
open scoped ENNReal Classical BigOperators

variable {F : Type*} [MeasurableSpace F]

/-- Selective accepted-mixture comparison where the unresolved tail is an arbitrary
subprobability measure, rather than a multiple of a fixed Dirac fallback. -/
theorem tvLe_sum_smul_add_tail_selective
    (L : Nat) (w : Fin L → ENNReal) (q : Fin L → Measure F)
    [∀ i, IsProbabilityMeasure (q i)]
    (tail tau : Measure F) [IsProbabilityMeasure tau]
    (delta eta : ENNReal) (Good : Fin L → Prop) [DecidablePred Good]
    (hmass : (∑ i, w i) + tail Set.univ = 1)
    (hq : ∀ i, Good i → TVLe (q i) tau delta)
    (hbad : (∑ i with ¬ Good i, w i) + tail Set.univ ≤ eta) :
    TVLe ((∑ i, w i • q i) + tail) tau (delta + eta) := by
  let err : Fin L → ENNReal := fun i ↦ if Good i then delta else 1
  have herrTV : ∀ i, TVLe (q i) tau (err i) := by
    intro i
    by_cases hi : Good i
    · simpa only [err, if_pos hi] using hq i hi
    · simpa only [err, if_neg hi] using Arlib.tvLe_one (q i) tau
  have hweights : ∑ i, w i ≤ 1 :=
    (le_add_right le_rfl).trans_eq hmass
  have herrBound : (∑ i, w i * err i) + tail Set.univ ≤ delta + eta := by
    have hterm : ∀ i, w i * err i ≤
        w i * delta + if ¬ Good i then w i else 0 := by
      intro i
      by_cases hi : Good i <;> simp [err, hi]
    calc
      (∑ i, w i * err i) + tail Set.univ ≤
          (∑ i, (w i * delta + if ¬ Good i then w i else 0)) + tail Set.univ := by
            gcongr with i
            exact hterm i
      _ = (∑ i, w i) * delta + ((∑ i with ¬ Good i, w i) + tail Set.univ) := by
        rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_filter]
        ac_rfl
      _ ≤ delta + eta := add_le_add
        (mul_le_of_le_one_left (by simp) hweights) hbad
  intro S hS
  have hsumEval : ((∑ i, w i • q i) + tail) S =
      (∑ i, w i * q i S) + tail S := by
    rw [Measure.add_apply, Measure.finsetSum_apply]
    simp only [Measure.smul_apply, smul_eq_mul]
  have htail : tail S ≤ tail Set.univ := measure_mono (subset_univ S)
  have htau : tau S ≤ 1 := prob_le_one
  constructor
  · rw [hsumEval]
    have hsum : (∑ i, w i * q i S) ≤
        ∑ i, w i * (tau S + err i) :=
      Finset.sum_le_sum fun i _ ↦ mul_le_mul_left' ((herrTV i).left hS) (w i)
    calc
      (∑ i, w i * q i S) + tail S ≤
          (∑ i, w i * (tau S + err i)) + tail Set.univ := add_le_add hsum htail
      _ = (∑ i, w i) * tau S + ((∑ i, w i * err i) + tail Set.univ) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, Finset.sum_mul]
        ac_rfl
      _ ≤ tau S + (delta + eta) := by
        exact add_le_add
          (mul_le_of_le_one_left (by simp) hweights) herrBound
  · rw [hsumEval]
    have hweighted : (∑ i, w i) * tau S ≤
        (∑ i, w i * q i S) + (∑ i, w i * err i) := by
      calc
        (∑ i, w i) * tau S = ∑ i, w i * tau S := by rw [Finset.sum_mul]
        _ ≤ ∑ i, w i * (q i S + err i) :=
          Finset.sum_le_sum fun i _ ↦ mul_le_mul_left' ((herrTV i).right hS) (w i)
        _ = (∑ i, w i * q i S) + (∑ i, w i * err i) := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
    calc
      tau S = ((∑ i, w i) + tail Set.univ) * tau S := by rw [hmass, one_mul]
      _ = (∑ i, w i) * tau S + tail Set.univ * tau S := by rw [add_mul]
      _ ≤ ((∑ i, w i * q i S) + (∑ i, w i * err i)) + tail Set.univ := by
        exact add_le_add hweighted (mul_le_of_le_one_right (by simp) htau)
      _ ≤ ((∑ i, w i * q i S) + tail S) + (delta + eta) := by
        calc
          _ ≤ (((∑ i, w i * q i S) + (∑ i, w i * err i)) + tail Set.univ) +
              tail S := le_add_right le_rfl
          _ = ((∑ i, w i * q i S) + tail S) +
              ((∑ i, w i * err i) + tail Set.univ) := by ac_rfl
          _ ≤ _ := by
            simpa only [add_comm] using add_le_add_left herrBound
              ((∑ i, w i * q i S) + tail S)

variable {E C : Type*} [MeasurableSpace E] [MeasurableSpace C]

/-- Self-fallback selective capstone from exact first-hit factorization.  This is the
variable-fallback counterpart of `tvLe_cutoffOutput_of_accepted_significant_initialLaw`.
The scalar recurrence hypotheses are stated explicitly so Gaussian survival analysis can
be reused unchanged. -/
theorem tvLe_map_output_selfMarginal_selective
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → E) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho : Measure E) [IsProbabilityMeasure rho] (L : Nat)
    (tau : Measure E) [IsProbabilityMeasure tau]
    (w : Fin L → ENNReal) (q : Fin L → Measure E)
    [∀ i, IsProbabilityMeasure (q i)]
    (s : Nat → ENNReal) (delta eta r : ENNReal)
    (hdecomp : Measure.map output
        (selfMarginal candidate A hA next out hnext hout roundCost hcost rho L) =
      (∑ i, w i • q i) +
        runningOutput
          (selfMarginal candidate A hA next out hnext hout roundCost hcost rho L))
    (htail : runningOutput
        (selfMarginal candidate A hA next out hnext hout roundCost hcost rho L) Set.univ = s L)
    (hmass : (∑ i, w i) + s L = 1)
    (hrec : ∀ (j : Nat) (hj : j < L), w ⟨j, hj⟩ + s (j + 1) = s j)
    (hs0 : s 0 ≤ 1) (hmono : ∀ j, s (j + 1) ≤ s j)
    (hr : r ≤ 1) (hcontract : ∀ j, eta ≤ s j → s (j + 1) ≤ r * s j)
    (hq : ∀ i : Fin L, eta ≤ s (i : Nat) → TVLe (q i) tau delta) :
    TVLe (Measure.map output
      (selfMarginal candidate A hA next out hnext hout roundCost hcost rho L))
      tau (delta + (eta + r ^ L)) := by
  classical
  have hbadN := Ttc.ContinuingRejectionSelective.badWeights_add_survival_le_eta_add_pow
    (fun j ↦ if hj : j < L then w ⟨j, hj⟩ else 0) s L eta r
    (fun j hj ↦ by simpa [hj] using hrec j hj) hs0 hr hmono hcontract
  have hbad : (∑ i ∈ (Finset.univ : Finset (Fin L)).filter
      (fun i : Fin L ↦ ¬ eta ≤ s (i : Nat)), w i) + s L ≤ eta + r ^ L := by
    rw [Finset.sum_filter] at hbadN ⊢
    rw [← Fin.sum_univ_eq_sum_range] at hbadN
    simpa using hbadN
  rw [hdecomp]
  apply tvLe_sum_smul_add_tail_selective L w q
    (runningOutput
      (selfMarginal candidate A hA next out hnext hout roundCost hcost rho L))
    tau delta (eta + r ^ L) (fun i ↦ eta ≤ s (i : Nat))
  · simpa [htail] using hmass
  · intro i hi
    exact hq i hi
  · simpa [htail] using hbad

#print axioms tvLe_sum_smul_add_tail_selective
#print axioms tvLe_map_output_selfMarginal_selective

end Ttc.FiniteContinuingRetrySelfSelective
