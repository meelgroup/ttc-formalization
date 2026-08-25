import Kr25Ssmxt.Analysis.IntegerCubulationCellControl

/-!
# Homothety sandwich for integer cubulation

A convex set containing a ball of radius greater than one traps its integer cubulation
between contractions and expansions centered at the inball center.
-/

namespace Kr25Ssmxt

/--
The centered contractions and expansions by `1 ∓ 1 / R` sandwich a convex set and its
integer cubulation.

INTERNAL: geometric heart of the cubulation boundary-layer estimate
-/
lemma cubulation_homothety_sandwich {n : Nat}
    (S : Set (Point n)) (c : Point n) (R : Real)
    (hR : 1 < R)
    (hconvex : Convex Real S)
    (hinball : Metric.closedBall c R ⊆ S)
    (hcell : IntegerCubulationCellControl S) :
    (fun x : Point n => c + (1 - 1 / R) • (x - c)) '' S ⊆
        S ∩ integerCubulation S ∧
      S ∪ integerCubulation S ⊆
        (fun x : Point n => c + (1 + 1 / R) • (x - c)) '' S := by
  have hR0 : 0 < R := by linarith
  have hRne : R ≠ 0 := ne_of_gt hR0
  have hRp1 : 0 < R + 1 := by linarith
  have hRp1ne : R + 1 ≠ 0 := ne_of_gt hRp1
  have hc : c ∈ S :=
    hinball (Metric.mem_closedBall_self hR0.le)
  let a : Real := 1 - 1 / R
  have ha : a ∈ Set.Icc (0 : Real) 1 := by
    constructor
    · dsimp [a]
      have hdiv : 1 / R < 1 := (div_lt_one hR0).2 hR
      linarith
    · dsimp [a]
      have hdiv : 0 < 1 / R := one_div_pos.mpr hR0
      linarith
  let q : Real := R / (R + 1)
  have hq : q ∈ Set.Icc (0 : Real) 1 := by
    constructor
    · exact div_nonneg hR0.le hRp1.le
    · dsimp [q]
      exact (div_le_one hRp1).2 (by linarith)
  constructor
  · intro y hy
    rcases hy with ⟨x, hxS, rfl⟩
    let y : Point n := c + a • (x - c)
    have hyS : y ∈ S := hconvex.add_smul_sub_mem hc hxS ha
    rcases hcell.2 y with ⟨z, hzcell, hzy⟩
    let zR : Point n := fun j => (z j : Real)
    let p : Point n := c + R • (zR - y)
    have hpball : p ∈ Metric.closedBall c R := by
      rw [Metric.mem_closedBall]
      calc
        dist p c = R * ‖zR - y‖ := by
          rw [dist_eq_norm]
          simp [p, norm_smul, Real.norm_eq_abs, abs_of_pos hR0]
        _ = R * ‖y - zR‖ := by rw [norm_sub_rev zR y]
        _ ≤ R * 1 := mul_le_mul_of_nonneg_left hzy hR0.le
        _ = R := mul_one R
    have hpS : p ∈ S := hinball hpball
    have hzidentity : zR = p + a • (x - p) := by
      ext j
      dsimp [zR, p, y, a]
      field_simp [hRne]
      ring
    have hzS : zR ∈ S := by
      rw [hzidentity]
      exact hconvex.add_smul_sub_mem hpS hxS ha
    constructor
    · exact hyS
    · change ∃ z : Fin n → Int, (fun j => (z j : Real)) ∈ S ∧ _
      exact ⟨z, hzS, hzcell⟩
  · intro y hy
    obtain ⟨z0, hz0S, hyz0⟩ :
        ∃ z0 : Point n, z0 ∈ S ∧ ‖y - z0‖ ≤ 1 := by
      rcases hy with hyS | hyCub
      · exact ⟨y, hyS, by simp⟩
      · rcases hcell.1 y hyCub with ⟨z, hzS, hnorm⟩
        exact ⟨(fun j => (z j : Real)), hzS, hnorm⟩
    let p : Point n := c + R • (y - z0)
    have hpball : p ∈ Metric.closedBall c R := by
      rw [Metric.mem_closedBall]
      calc
        dist p c = R * ‖y - z0‖ := by
          rw [dist_eq_norm]
          simp [p, norm_smul, Real.norm_eq_abs, abs_of_pos hR0]
        _ ≤ R * 1 := mul_le_mul_of_nonneg_left hyz0 hR0.le
        _ = R := mul_one R
    have hpS : p ∈ S := hinball hpball
    let x0 : Point n := c + q • (y - c)
    have hxidentity : x0 = p + q • (z0 - p) := by
      ext j
      dsimp [x0, p, q]
      field_simp [hRp1ne]
      ring
    have hx0S : x0 ∈ S := by
      rw [hxidentity]
      exact hconvex.add_smul_sub_mem hpS hz0S hq
    refine ⟨x0, hx0S, ?_⟩
    ext j
    dsimp [x0, q]
    field_simp [hRne, hRp1ne]
    ring

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r3 · proved · established both homothety inclusions from convexity and cell control
* r2 · reduced · stated the centered contraction/expansion sandwich from cell control
-/

end Kr25Ssmxt
