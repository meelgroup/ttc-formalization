import Arlib.Probability.AdaptiveTVTelescope
import Arlib.Probability.TVKernelHeterogeneous
import Arlib.Probability.InhomogeneousMarkov
import Ttc.Volume.CVDirectSequentialWarm

/-!
# Finite-path TV telescope with ideal-law averaged phase errors

Unlike a pointwise kernel telescope, the replacement error at phase `i` is measured only
after averaging the operational and ideal transition against the exact ideal prefix law.
This is the hybrid argument needed for finite continuing-retry phases: fallback states in
the operational prefix need not themselves be warm.
-/

namespace Ttc.CVIdealAveragePathTelescope

open MeasureTheory ProbabilityTheory Finset Set
open Arlib Arlib.Probability
open scoped ENNReal BigOperators

variable {X : Type*} [MeasurableSpace X]

/-- Append the next state to a history indexed through `i`. -/
def extendIic (i : Nat) : ((Finset.Iic i → X) × X) → (Finset.Iic (i + 1) → X) :=
  fun p j ↦ if h : j.1 ≤ i then p.1 ⟨j.1, Finset.mem_Iic.2 h⟩ else p.2

theorem measurable_extendIic (i : Nat) : Measurable (extendIic (X := X) i) := by
  apply measurable_pi_lambda
  intro j
  by_cases h : j.1 ≤ i
  · simp only [extendIic, h, dite_true]
    fun_prop
  · simp only [extendIic, h, dite_false]
    fun_prop

theorem extendIic_history_next (i : Nat) (omega : Nat → X) :
    extendIic i (Preorder.frestrictLe i omega, omega (i + 1)) =
      Preorder.frestrictLe (i + 1) omega := by
  funext j
  by_cases h : j.1 ≤ i
  · simp [extendIic, h, Preorder.frestrictLe]
  · have hlo : i + 1 ≤ j.1 := Nat.succ_le_iff.2 (Nat.lt_of_not_ge h)
    have hj : j.1 = i + 1 := Nat.le_antisymm (Finset.mem_Iic.1 j.2) hlo
    simp [extendIic, h, hj, Preorder.frestrictLe]

private theorem history_zero_eq_map
    (P : Nat → Kernel X X) [∀ i, IsMarkovKernel (P i)]
    (mu : Measure X) [IsProbabilityMeasure mu] :
    Measure.map (Preorder.frestrictLe 0) (inhomogeneousPathMeasure P mu) =
      Measure.map (fun x : X ↦ fun _ : Finset.Iic 0 ↦ x) mu := by
  have hzero := Ttc.CVDirectSequentialWarm.map_eval_inhomogeneousPathMeasure_zero P mu
  have hfun : Preorder.frestrictLe 0 =
      (fun x : X ↦ fun _ : Finset.Iic 0 ↦ x) ∘ (fun omega : Nat → X ↦ omega 0) := by
    funext omega j
    have hj : j.1 = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.1 j.2)
    simp [Preorder.frestrictLe, hj]
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop), hzero]

/-- **Ideal-average finite-path telescope.**  At phase `i`, only the joint transition
under the ideal prefix law must be close.  Earlier operational error is propagated through
the operational kernel by TV data processing, and later kernels never multiply it. -/
theorem tvLe_frestrictLe_inhomogeneous_of_idealAverage
    (P Q : Nat → Kernel X X)
    [∀ i, IsMarkovKernel (P i)] [∀ i, IsMarkovKernel (Q i)]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {d : ENNReal} (e : Nat → ENNReal) (hinit : TVLe mu nu d)
    (haverage : ∀ i,
      TVLe
        ((Measure.map (Preorder.frestrictLe i) (inhomogeneousPathMeasure Q nu)) ⊗ₘ
          inhomogeneousHistoryKernel P i)
        ((Measure.map (Preorder.frestrictLe i) (inhomogeneousPathMeasure Q nu)) ⊗ₘ
          inhomogeneousHistoryKernel Q i)
        (e i))
    (t : Nat) :
    TVLe
      (Measure.map (Preorder.frestrictLe t) (inhomogeneousPathMeasure P mu))
      (Measure.map (Preorder.frestrictLe t) (inhomogeneousPathMeasure Q nu))
      (d + ∑ i ∈ Finset.range t, e i) := by
  induction t with
  | zero =>
      rw [history_zero_eq_map P mu, history_zero_eq_map Q nu]
      simpa using hinit.map (by fun_prop : Measurable (fun x : X ↦ fun _ : Finset.Iic 0 ↦ x))
  | succ i ih =>
      let muI := Measure.map (Preorder.frestrictLe i) (inhomogeneousPathMeasure P mu)
      let nuI := Measure.map (Preorder.frestrictLe i) (inhomogeneousPathMeasure Q nu)
      let kP := inhomogeneousHistoryKernel P i
      let kQ := inhomogeneousHistoryKernel Q i
      letI : IsProbabilityMeasure muI := by
        dsimp only [muI]
        exact Measure.isProbabilityMeasure_map
          (Preorder.measurable_frestrictLe i).aemeasurable
      letI : IsProbabilityMeasure nuI := by
        dsimp only [nuI]
        exact Measure.isProbabilityMeasure_map
          (Preorder.measurable_frestrictLe i).aemeasurable
      have hprop : TVLe (muI ⊗ₘ kP) (nuI ⊗ₘ kP)
          (d + ∑ j ∈ Finset.range i, e j) := by
        have hbind := ih.bind_kernel (Kernel.id ×ₖ kP)
        simpa only [muI, nuI, kP, Measure.compProd_eq_comp_prod] using hbind
      have hpair : TVLe (muI ⊗ₘ kP) (nuI ⊗ₘ kQ)
          ((d + ∑ j ∈ Finset.range i, e j) + e i) :=
        hprop.trans (haverage i)
      have hjP := map_history_next_inhomogeneousPathMeasure P mu i
      have hjQ := map_history_next_inhomogeneousPathMeasure Q nu i
      change muI ⊗ₘ kP = _ at hjP
      change nuI ⊗ₘ kQ = _ at hjQ
      rw [hjP, hjQ] at hpair
      have hmap := hpair.map (measurable_extendIic i)
      rw [Measure.map_map (measurable_extendIic i) (by fun_prop),
        Measure.map_map (measurable_extendIic i) (by fun_prop)] at hmap
      have hfun : extendIic i ∘
          (fun omega : Nat → X ↦ (Preorder.frestrictLe i omega, omega (i + 1))) =
          Preorder.frestrictLe (i + 1) := by
        funext omega
        exact extendIic_history_next i omega
      rw [hfun] at hmap
      rw [Finset.sum_range_succ]
      simpa only [add_assoc] using hmap

/-- Any measurable statistic of the first `t+1` states, including the packed `Fin k`
phase-score product, inherits the same single hybrid sum. -/
theorem tvLe_map_frestrictLe_statistic_of_idealAverage
    (P Q : Nat → Kernel X X)
    [∀ i, IsMarkovKernel (P i)] [∀ i, IsMarkovKernel (Q i)]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {d : ENNReal} (e : Nat → ENNReal) (hinit : TVLe mu nu d)
    (haverage : ∀ i,
      TVLe
        ((Measure.map (Preorder.frestrictLe i) (inhomogeneousPathMeasure Q nu)) ⊗ₘ
          inhomogeneousHistoryKernel P i)
        ((Measure.map (Preorder.frestrictLe i) (inhomogeneousPathMeasure Q nu)) ⊗ₘ
          inhomogeneousHistoryKernel Q i)
        (e i))
    (t : Nat) {Y : Type*} [MeasurableSpace Y]
    (f : (Finset.Iic t → X) → Y) (hf : Measurable f) :
    TVLe
      (Measure.map (f ∘ Preorder.frestrictLe t) (inhomogeneousPathMeasure P mu))
      (Measure.map (f ∘ Preorder.frestrictLe t) (inhomogeneousPathMeasure Q nu))
      (d + ∑ i ∈ Finset.range t, e i) := by
  have h := (tvLe_frestrictLe_inhomogeneous_of_idealAverage P Q mu nu e hinit haverage t).map hf
  rw [Measure.map_map hf (Preorder.measurable_frestrictLe t),
    Measure.map_map hf (Preorder.measurable_frestrictLe t)] at h
  exact h

#print axioms extendIic_history_next
#print axioms tvLe_frestrictLe_inhomogeneous_of_idealAverage
#print axioms tvLe_map_frestrictLe_statistic_of_idealAverage

end Ttc.CVIdealAveragePathTelescope
