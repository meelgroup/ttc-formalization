import Kr25Ssmxt.Analysis.IntegerCubulation

/-!
# Cell control for integer cubulation

This module records the two coordinatewise consequences of the half-open cube
definition: a point of a selected cell is uniformly close to its integer anchor, and
every point has such an anchor.
-/

namespace Kr25Ssmxt

/--
The concrete cell-control property needed by the homothety argument.

INTERNAL: packages the floor representative and its uniform sup-norm displacement
-/
def IntegerCubulationCellControl {n : Nat} (S : Set (Point n)) : Prop :=
  (∀ x ∈ integerCubulation S, ∃ z : Fin n → Int,
      (fun j => (z j : Real)) ∈ S ∧
        norm (x - fun j => (z j : Real)) ≤ 1) ∧
    (∀ x, ∃ z : Fin n → Int,
      (∀ j, (z j : Real) ≤ x j ∧ x j < (z j : Real) + 1) ∧
        norm (x - fun j => (z j : Real)) ≤ 1)

/--
Half-open unit cubes have integer anchors at sup-norm distance at most one.

INTERNAL: coordinatewise floor fact extracted from `integerCubulation`
-/
lemma integerCubulation_cell_control {n : Nat} (S : Set (Point n)) :
    IntegerCubulationCellControl S := by
  constructor
  · intro x hx
    rcases hx with ⟨z, hzS, hz⟩
    refine ⟨z, hzS, ?_⟩
    rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro j
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    rw [abs_le]
    constructor
    · linarith [(hz j).1]
    · linarith [(hz j).2]
  · intro x
    let z : Fin n → Int := fun j => ⌊x j⌋
    refine ⟨z, ?_, ?_⟩
    · intro j
      exact ⟨Int.floor_le (x j), Int.lt_floor_add_one (x j)⟩
    · rw [pi_norm_le_iff_of_nonneg (by norm_num)]
      intro j
      simp only [Pi.sub_apply, Real.norm_eq_abs]
      rw [abs_le]
      constructor
      · dsimp only [z]
        linarith [Int.floor_le (x j)]
      · dsimp only [z]
        linarith [Int.lt_floor_add_one (x j)]

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · proved · extracted the integer floor representative and its sup-norm bound
-/

end Kr25Ssmxt
