import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! The layer-cake identity for a measurable natural-valued runtime. -/

namespace ttc

open MeasureTheory

theorem lintegral_nat_eq_tsum_tail {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → Nat) (hf : Measurable f) :
    ∫⁻ x, (f x : ENNReal) ∂μ = ∑' k : Nat, μ {x | k < f x} := by
  have hpoint (x : α) : (f x : ENNReal) =
      ∑' k : Nat, (if k < f x then (1 : ENNReal) else 0) := by
    rw [tsum_eq_sum (s := Finset.range (f x)) (by
      intro k hk
      simp only [Finset.mem_range, not_lt] at hk
      simp [hk])]
    simp [Finset.filter_true_of_mem (show ∀ k ∈ Finset.range (f x), k < f x from
      fun _ hk => Finset.mem_range.mp hk)]
  simp_rw [hpoint]
  rw [lintegral_tsum]
  · congr 1
    funext k
    have hset : MeasurableSet {x : α | k < f x} :=
      hf measurableSet_Ioi
    have hfun : (fun x : α => if k < f x then (1 : ENNReal) else 0) =
        Set.indicator {x | k < f x} 1 := by
      funext x
      by_cases hx : k < f x <;> simp [hx, Set.indicator]
    rw [hfun, lintegral_indicator_one hset]
  · intro k
    exact (Measurable.ite (hf measurableSet_Ioi)
      measurable_const measurable_const).aemeasurable

end ttc
