import Mathlib.MeasureTheory.Measure.AEMeasurable

/-!
# Decomposition of a measure along countable almost-measurable fibers

An almost-everywhere measurable map into a countable measurable type partitions its source
measure into restrictions to the fibers of a measurable representative.  The original map
agrees with the representative on each restricted law almost everywhere.
-/

noncomputable section

namespace ttc

open MeasureTheory

/--
Every measure is the sum of its restrictions to the fibers of an almost-everywhere measurable
map into a countable type, and each summand is supported on the corresponding original fiber.

INTERNAL: generic measure-theoretic stratification used for discrete execution profiles.
-/
lemma measure_sum_by_countable_ae_fibers {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β]
    (ρ : Measure α) (f : α → β) (hf : AEMeasurable f ρ) :
    ∃ ν : β → Measure α,
      ρ = Measure.sum ν ∧ ∀ b, ∀ᵐ x ∂ν b, f x = b := by
  classical
  let g := hf.mk f
  let ν : β → Measure α := fun b => ρ.restrict (Set.preimage g {b})
  refine ⟨ν, ?_, ?_⟩
  · rw [← Measure.restrict_univ (μ := ρ)]
    have hu : (⋃ b, Set.preimage g {b}) = Set.univ := by
      ext x
      simp
    rw [← hu]
    apply Measure.restrict_iUnion
    · intro i j hij
      exact Set.pairwiseDisjoint_fiber g Set.univ
        (Set.mem_univ i) (Set.mem_univ j) hij
    · exact fun b => hf.measurable_mk (measurableSet_singleton b)
  · intro b
    filter_upwards [ae_restrict_of_ae hf.ae_eq_mk,
      ae_restrict_mem (hf.measurable_mk (measurableSet_singleton b))] with x hx hmem
    exact hx.trans hmem

end ttc

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · restricted to the countable fibers of `AEMeasurable.mk` and used
  countable additivity for their pairwise-disjoint union
-/
