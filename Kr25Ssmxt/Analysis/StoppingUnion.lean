import Kr25Ssmxt.Analysis.AbsolutePoissonTape

/-! A finite stopping-level union bound. The event at a random final level is
charged to the corresponding fixed-level event on the same source space. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem stopped_bad_le_fixed_level_sum
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (cutoff : Nat) (stop : Ω → Nat)
    (bad : Nat → Set Ω) :
    μ {ω | stop ω < cutoff ∧ ω ∈ bad (stop ω)} ≤
      ∑ level ∈ Finset.range cutoff, μ (bad level) := by
  have hsubset : {ω | stop ω < cutoff ∧ ω ∈ bad (stop ω)} ⊆
      ⋃ level ∈ Finset.range cutoff, bad level := by
    intro ω hω
    exact Set.mem_biUnion (Finset.mem_range.mpr hω.1) hω.2
  exact (measure_mono hsubset).trans
    (measure_biUnion_finset_le (Finset.range cutoff) bad)

theorem stopped_bad_real_le_fixed_level_sum
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (cutoff : Nat) (stop : Ω → Nat) (bad : Nat → Set Ω) :
    μ.real {ω | stop ω < cutoff ∧ ω ∈ bad (stop ω)} ≤
      ∑ level ∈ Finset.range cutoff, μ.real (bad level) := by
  have hsubset : {ω | stop ω < cutoff ∧ ω ∈ bad (stop ω)} ⊆
      ⋃ level ∈ Finset.range cutoff, bad level := by
    intro ω hω
    exact Set.mem_biUnion (Finset.mem_range.mpr hω.1) hω.2
  have hfinite : μ (⋃ level ∈ Finset.range cutoff, bad level) ≠ ⊤ := by
    exact ne_top_of_le_ne_top (by simp) (measure_mono (Set.subset_univ _))
  exact (measureReal_mono hsubset hfinite).trans
    (measureReal_biUnion_finset_le (Finset.range cutoff) bad)

end Kr25Ssmxt
