/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.FilterOps

/-! # The deletion and rate check, with their arithmetic and output bounds -/

set_option autoImplicit false

noncomputable section

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ttc.Tape.Tree

variable {d : ℕ}

private theorem opsTotal_rateProg (tp thresh p : Num ℝ) :
    opsTotal (rateProg tp thresh p).cost = 13 := by
  simp [rateProg, powHeld, A.log, A.exp, A.cast, A.ceil, opsTotal_add, opsTotal_one]

/-- Deletion, the scalar rate check and the optional thinning scan are all
charged on the actual program. The scans pay only for the copies at entry. -/
theorem maxOps_rateT_le (hd : 0 < d) (Th : Num ℝ) (L : Loaded d)
    (sc : Fin L.facets → Num ℝ) (t : Num ℝ) (s : State d) :
    maxOps (rateT Th L sc t s) ≤ 19 + s.X.length * (d + 2 * d * L.facets + 8) := by
  let M : ℕ∞ := ((d + 2 * d * L.facets : ℕ) : ℕ∞)
  have hm : ∀ x, maxOps (memDel L sc x) ≤ M := by
    intro x
    rw [memDel, maxOps_compute_bind, maxOps_pure, add_zero]
    exact Nat.cast_le.mpr (opsTotal_latticeMember_le hd L sc x)
  unfold rateT
  refine (maxOps_bind_le (post_filterCopiesT_size _ s.X) (17 + s.X.length * 5)
    (fun r hr => ?_)).trans ?_
  · rw [maxOps_compute_bind, maxOps_compute_bind, opsTotal_mul, opsTotal_le, Nat.cast_one]
    split_ifs
    · rw [maxOps_compute_bind, opsTotal_rateProg]
      have hkeep : ∀ _ : Fin d → Num ℤ,
          maxOps (unitT.bind fun u => compute (A.lt u
            (rateProg (A.mul t s.p).val Th s.p).val.2) : Tree d Bool) ≤ 2 := by
        intro _
        norm_num [unitT, Tree.bind, maxOps_compute, maxOps]
      have hscan := maxOps_filterCopiesT_le 2 hkeep r.1
      have hcast : (r.1.length : ℕ∞) ≤ s.X.length := Nat.cast_le.mpr hr
      let y := (rateProg (A.mul t s.p).val Th s.p).val
      have hh := maxOps_bind_uniform (f := fun r' => Tree.pure (y.1, r'.1, r'.2)) hscan
        (fun _ => (maxOps_pure _).le)
      simp only [add_zero] at hh
      exact (add_le_add le_rfl (add_le_add le_rfl (add_le_add le_rfl hh))).trans (by
        calc _ ≤ (1 : ℕ∞) + (1 + (13 + (2 + s.X.length * (2 + 3)))) :=
              add_le_add le_rfl (add_le_add le_rfl (add_le_add le_rfl
                (add_le_add le_rfl (mul_le_mul' hcast le_rfl))))
          _ = (17 : ℕ∞) + s.X.length * 5 := by ring)
    · simp only [maxOps_pure, add_zero]
      exact (by decide : (1 + 1 : ℕ∞) ≤ 17).trans
        le_self_add
  · calc _ ≤ (2 + s.X.length * (M + 3)) + (17 + s.X.length * 5) :=
          add_le_add (maxOps_filterCopiesT_le M hm s.X) le_rfl
      _ = _ := by dsimp only [M]; push_cast; ring

private theorem rateProg_capped (t p Th : Num ℝ) (hTh : 0 < Th.get) (h : Th.get ≤ t.get * p.get) :
    t.get * (rateProg (A.mul t p).val Th p).val.1.get ≤ Th.get := by
  let x := t.get * p.get / Th.get
  let k := Nat.ceil (Real.log x / Real.log 2)
  have hx : 0 < x := div_pos (hTh.trans_le h) hTh
  have hlog : Real.logb 2 x ≤ (k : ℝ) := Nat.le_ceil _
  have hratio := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hx).mp hlog
  rw [Real.rpow_natCast] at hratio
  rw [(rateProg_val _ Th p).1]
  simp only [A.mul, Num.get_mul]
  rw [← mul_div_assoc]
  change t.get * p.get / (2 : ℝ) ^ k ≤ Th.get
  apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ k)).mpr
  exact ((div_le_iff₀ hTh).mp hratio).trans_eq (mul_comm _ _)

/-- The rate guard bounds the actual next Poisson mean, on every tape. -/
theorem post_rateT_bounded (Th : Num ℝ) (L : Loaded d) (sc : Fin L.facets → Num ℝ)
    (t : Num ℝ) (s : State d) (hTh : 0 < Th.get) (hp : 0 ≤ s.p.get) :
    Post (rateT Th L sc t s) fun q => 0 ≤ q.1.get ∧ q.2.2.get = q.2.1.length ∧
      q.2.1.length ≤ s.X.length ∧ t.get * q.1.get ≤ Th.get := by
  unfold rateT
  refine Post.bind (((post_filterCopiesT (memDel L sc) s.X).and
    (post_filterCopiesT_size _ s.X)).mono fun r hr => ?_)
  refine post_compute_bind (post_compute_bind ?_)
  have he : (A.le Th (A.mul t s.p).val).val = decide (Th.get ≤ t.get * s.p.get) := by
    rw [Bool.eq_iff_iff]
    simp only [A.le, Num.val_le, A.mul, Num.get_mul, decide_eq_true_eq]
    exact decide_eq_true_iff
  rw [he]
  by_cases ht : Th.get ≤ t.get * s.p.get
  · simp only [ht, decide_true, ite_true]
    refine post_compute_bind (Post.bind (((post_filterCopiesT _ r.1).and
      (post_filterCopiesT_size _ r.1)).mono fun r' hr' => ?_))
    refine ⟨?_, hr'.1, hr'.2.trans hr.2, rateProg_capped t s.p Th hTh ht⟩
    show 0 ≤ (rateProg (A.mul t s.p).val Th s.p).val.1.get
    rw [(rateProg_val _ _ _).1]
    positivity
  · simp only [ht, decide_false, Bool.false_eq_true, ite_false]
    exact ⟨hp, hr.1, hr.2, (lt_of_not_ge ht).le⟩

end ttc.Tape
