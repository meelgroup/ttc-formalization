import Kr25Ssmxt.Model.Prelude

/-!
# Power bound for the cubulation homothetic annulus

This module isolates the real-variable estimate converting the inball radius into the
relative volume of the centered homothetic annulus.
-/

namespace Kr25Ssmxt

/--
The expansion/contraction power gap is at most the allotted component error when the
inball has the radius required by the cubulation argument.

INTERNAL: scalar estimate used in the homothety-annulus volume calculation
-/
lemma cubulation_homothety_power_bound {n m : Nat}
    (hn : 0 < n) (hm : 0 < m) (R η : Real)
    (hηpos : 0 < η) (hηle : η ≤ 1)
    (hradius : 64 * (m : Real) * (n : Real) / η ≤ R) :
    0 < 1 - 1 / R ∧
      (1 + 1 / R) ^ n - (1 - 1 / R) ^ n ≤
        (η / (m : Real)) * (1 - 1 / R) ^ n := by
  have hmR : 0 < (m : Real) := by exact_mod_cast hm
  have hnR : 0 < (n : Real) := by exact_mod_cast hn
  have hm1 : 1 ≤ (m : Real) := by exact_mod_cast hm
  have hn1 : 1 ≤ (n : Real) := by exact_mod_cast hn
  have hmn : 1 ≤ (m : Real) * (n : Real) := by
    calc
      1 ≤ (m : Real) := hm1
      _ = (m : Real) * 1 := by ring
      _ ≤ (m : Real) * (n : Real) :=
        mul_le_mul_of_nonneg_left hn1 hmR.le
  have hbase : (64 : Real) ≤ 64 * (m : Real) * (n : Real) / η := by
    apply (le_div_iff₀ hηpos).2
    nlinarith [hηle, hmn]
  have hR64 : (64 : Real) ≤ R := hbase.trans hradius
  have hRpos : 0 < R := by linarith
  have hRne : R ≠ 0 := hRpos.ne'
  have hRm1pos : 0 < R - 1 := by linarith
  have hRm1ne : R - 1 ≠ 0 := hRm1pos.ne'
  let a : Real := 1 - 1 / R
  let b : Real := 1 + 1 / R
  let x : Real := 2 / (R - 1)
  have ha : 0 < a := by
    dsimp [a]
    have : 1 / R < 1 := (div_lt_one hRpos).2 (by linarith)
    linarith
  have hx : 0 ≤ x := by
    dsimp [x]
    positivity
  have hx4 : x ≤ 4 / R := by
    dsimp [x]
    apply (div_le_div_iff₀ hRm1pos hRpos).2
    nlinarith
  have hradmul : 64 * (m : Real) * (n : Real) ≤ R * η := by
    have := (div_le_iff₀ hηpos).1 hradius
    nlinarith
  have h4 : 4 / R ≤ η / (16 * (m : Real) * (n : Real)) := by
    apply (div_le_div_iff₀ hRpos
      (by positivity : 0 < (16 : Real) * (m : Real) * (n : Real))).2
    nlinarith [hradmul]
  have hxsmall : x ≤ η / (16 * (m : Real) * (n : Real)) := hx4.trans h4
  have h2nx : 2 * (n : Real) * x ≤ η / (8 * (m : Real)) := by
    calc
      2 * (n : Real) * x ≤
          2 * (n : Real) * (η / (16 * (m : Real) * (n : Real))) :=
        mul_le_mul_of_nonneg_left hxsmall (by positivity)
      _ = η / (8 * (m : Real)) := by
        field_simp [hmR.ne', hnR.ne']
        ring
  have heta8m_le_one : η / (8 * (m : Real)) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < (8 : Real) * (m : Real))).2
    nlinarith
  have h2nx_le_one : 2 * (n : Real) * x ≤ 1 := h2nx.trans heta8m_le_one
  have h2nx_le_eta : 2 * (n : Real) * x ≤ η / (m : Real) := by
    refine h2nx.trans ?_
    apply (div_le_div_iff₀ (by positivity : 0 < (8 : Real) * (m : Real)) hmR).2
    nlinarith
  have hpowx : ∀ k : Nat, k ≤ n →
      (1 + x) ^ k ≤ 1 + 2 * (k : Real) * x := by
    intro k hk
    induction k with
    | zero => norm_num
    | succ k ih =>
        have hk_le : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
        have hkR : (k : Real) ≤ (n : Real) := by exact_mod_cast hk_le
        have h2kx : 2 * (k : Real) * x ≤ 1 := by
          calc
            2 * (k : Real) * x ≤ 2 * (n : Real) * x := by
              gcongr
            _ ≤ 1 := h2nx_le_one
        rw [pow_succ]
        calc
          (1 + x) ^ k * (1 + x) ≤
              (1 + 2 * (k : Real) * x) * (1 + x) :=
            mul_le_mul_of_nonneg_right (ih hk_le) (by linarith)
          _ ≤ 1 + 2 * ((k + 1 : Nat) : Real) * x := by
            push_cast
            nlinarith [mul_nonneg hx (sub_nonneg.mpr h2kx)]
  have hratio : b = a * (1 + x) := by
    dsimp [a, b, x]
    field_simp [hRne, hRm1ne]
    ring
  constructor
  · simpa [a] using ha
  · simpa [a, b] using show b ^ n - a ^ n ≤ (η / (m : Real)) * a ^ n from by
      calc
        b ^ n - a ^ n = a ^ n * ((1 + x) ^ n - 1) := by
          rw [hratio, mul_pow]
          ring
        _ ≤ a ^ n * (2 * (n : Real) * x) := by
          gcongr
          linarith [hpowx n le_rfl]
        _ ≤ a ^ n * (η / (m : Real)) := by
          gcongr
        _ = (η / (m : Real)) * a ^ n := by ring

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r4 · proved · bounded the homothety ratio by a linear binomial induction
-/

end Kr25Ssmxt
