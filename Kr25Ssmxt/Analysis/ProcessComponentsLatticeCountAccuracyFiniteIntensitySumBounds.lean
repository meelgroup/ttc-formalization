import Kr25Ssmxt.Model.Program

/-!
# Summing the pointwise intensity invariant

The component invariant controls the Poisson intensity attached to each lattice point.
This file isolates the finite counting step which converts those pointwise bounds into
bounds for the total Poisson mean.
-/

noncomputable section

namespace Kr25Ssmxt

/-- Uniform lower and upper bounds on the intensity of every point in a finite set sum to
the corresponding cardinality-scaled bounds on the total intensity.

INTERNAL: finite counting step in the component-prefix invariant for
`process_components_lattice_count_accuracy`.
-/
lemma process_components_lattice_count_accuracy_finite_intensity_sum_bounds
    {α : Type*} (S : Set α) (intensity : α → Real) (lower upper : Real)
    (hS : S.Finite)
    (hbounds : ∀ x ∈ S, lower ≤ intensity x ∧ intensity x ≤ upper) :
    (S.ncard : Real) * lower ≤ hS.toFinset.sum intensity ∧
      hS.toFinset.sum intensity ≤ (S.ncard : Real) * upper := by
  constructor
  · calc
      (S.ncard : Real) * lower = ∑ _x ∈ hS.toFinset, lower := by
        rw [Set.ncard_eq_toFinset_card S hS]
        simp
      _ ≤ hS.toFinset.sum intensity := by
        apply Finset.sum_le_sum
        intro x hx
        exact (hbounds x (by simpa using hx)).1
  · calc
      hS.toFinset.sum intensity ≤ ∑ _x ∈ hS.toFinset, upper := by
        apply Finset.sum_le_sum
        intro x hx
        exact (hbounds x (by simpa using hx)).2
      _ = (S.ncard : Real) * upper := by
        rw [Set.ncard_eq_toFinset_card S hS]
        simp

end Kr25Ssmxt
