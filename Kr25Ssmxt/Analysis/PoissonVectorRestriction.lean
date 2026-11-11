import Kr25Ssmxt.Analysis.PoissonVectorSum

/-! Restricting an independent Poisson point-count vector to a finite
subfamily preserves its independent product law. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem poisson_vector_restrict
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (r : ι → NNReal) :
    (Measure.pi (fun i : ι => ProbabilityTheory.poissonMeasure (r i))).map
      (fun counts : ι → Nat => fun i : s => counts i.1) =
    Measure.pi (fun i : s => ProbabilityTheory.poissonMeasure (r i.1)) := by
  classical
  let μ : ι → Measure Nat := fun i => ProbabilityTheory.poissonMeasure (r i)
  let restrict : (ι → Nat) → (s → Nat) := fun counts i => counts i.1
  have hrestrict : Measurable restrict := by
    unfold restrict
    fun_prop
  change (Measure.pi μ).map restrict = _
  apply Measure.ext_of_singleton
  intro f
  let t : ι → Set Nat := fun i =>
    if hi : i ∈ s then {f ⟨i, hi⟩} else Set.univ
  have hpre : restrict ⁻¹' {f} = Set.univ.pi t := by
    ext counts
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_pi,
      Set.mem_univ, forall_true_left]
    constructor
    · intro h i
      by_cases hi : i ∈ s
      · simpa [t, hi] using congrFun h ⟨i, hi⟩
      · simp [t, hi]
    · intro h
      funext i
      have hi := h i.1
      simpa [t, i.2] using hi
  rw [Measure.map_apply hrestrict (by measurability), hpre,
    Measure.pi_pi, Measure.pi_singleton]
  have houtside : ∀ i ∈ Finset.univ, i ∉ s → μ i (t i) = 1 := by
    intro i _ hi
    simp [μ, t, hi]
  have hsubset := Finset.prod_subset (Finset.subset_univ s) houtside
  rw [← hsubset]
  rw [Finset.prod_subtype s (by intro i; rfl)]
  apply Finset.prod_congr rfl
  intro i hi
  simp [μ, t, i.2]

end Kr25Ssmxt
