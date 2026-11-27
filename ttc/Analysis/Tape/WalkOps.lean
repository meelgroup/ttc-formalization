/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.RuntimeBudget
import ttc.Analysis.Tape.ArithmeticOps
import ttc.Analysis.Tape.OpsExp

/-! # Arithmetic and draws of one sealed Hit-and-Run proposal -/

set_option autoImplicit false

noncomputable section

namespace ttc.Tape

open ttc.RuntimeBudget

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ttc.Tape.Tree

variable {d : ℕ}

private theorem opsTotal_normalize (hd : 0 < d) (g : NumPoint d) :
    opsTotal (normalize g).cost = 3 * d + 2 := by
  simp only [ttc.Program.normalize, opsTotal_bind, opsTotal_norm hd, opsTotal_lit, opsTotal_div, opsTotal_smul]
  omega

private theorem opsTotal_facetEndpoints (hd : 0 < d) (a x u : NumPoint d) (β' : Num ℝ) :
    opsTotal (facetEndpoints a β' x u).cost = 4 * d + 3 := by
  simp only [facetEndpoints, opsTotal_bind, opsTotal_dot_pos d hd, opsTotal_sub,
    opsTotal_div, opsTotal_lit, opsTotal_lt, opsTotal_pure]
  omega

private theorem opsTotal_maxEnd_le (x y : Option (Num ℝ)) : opsTotal (maxEnd x y).cost ≤ 1 := by
  cases x <;> cases y <;> simp [maxEnd, opsTotal_add]

private theorem opsTotal_minEnd_le (x y : Option (Num ℝ)) : opsTotal (minEnd x y).cost ≤ 1 := by
  cases x <;> cases y <;> simp [minEnd, opsTotal_add]

theorem opsTotal_chord_le (hd : 0 < d) :
    ∀ (r : ℕ) (a : Fin r → NumPoint d) (β' : Fin r → Num ℝ) (x u : NumPoint d),
      opsTotal (chord r a β' x u).cost ≤ r * (4 * d + 5)
  | 0, _, _, _, _ => by simp [chord]
  | r + 1, a, β', x, u => by
      have h := opsTotal_chord_le hd r (Fin.tail a) (Fin.tail β') x u
      simp only [chord, opsTotal_bind, opsTotal_pure, add_zero, opsTotal_facetEndpoints hd]
      exact (Nat.add_le_add (Nat.le_refl _) (Nat.add_le_add h
        (Nat.add_le_add (opsTotal_maxEnd_le _ _) (opsTotal_minEnd_le _ _)))).trans (by
          ring_nf
          exact le_rfl)

private theorem maxOps_coinT : maxOps (coinT (n := d)) = 1 := by simp [coinT, maxOps]
private theorem maxOps_unitT : maxOps (unitT (n := d)) = 1 := by simp [unitT, maxOps]
private theorem maxOps_gaussianT : maxOps (gaussianT (n := d)) = d := by simp [gaussianT, maxOps]

private theorem maxOps_pure_bind (p : Tree d (NumPoint d)) {β : Type} (f : NumPoint d → β) :
    maxOps (p.bind (fun a => Tree.pure (f a))) ≤ maxOps p := by
  rw [← add_zero (maxOps p)]
  exact maxOps_bind_uniform le_rfl (fun _ => le_rfl)

theorem maxOps_hitAndRunStepT (hd : 0 < d) (r : ℕ) (a : Fin r → NumPoint d)
    (β' : Fin r → Num ℝ) (x : NumPoint d) :
    maxOps (hitAndRunStepT r a β' x) ≤ 6 * d + 8 + r * (4 * d + 5) := by
  unfold hitAndRunStepT
  have hmove (θ : NumPoint d) (lo hi : Num ℝ) :
      maxOps (unitT.bind fun u => compute (do
        let width ← A.sub hi lo
        let shift ← A.mul u width
        let t ← A.add lo shift
        A.forEach fun i => do
          let dx ← A.mul t (θ i)
          A.add (x i) dx) : Tree d (NumPoint d)) ≤ 1 + (3 + 2 * d) := by
    refine maxOps_bind_uniform maxOps_unitT.le fun u => ?_
    rw [maxOps_compute]
    have h (t : Num ℝ) := opsTotal_forEach_le 2 d (fun i => do
      let dx ← A.mul t (θ i)
      A.add (x i) dx) (fun i => by simp [opsTotal_add])
    simp only [opsTotal_bind, opsTotal_sub, opsTotal_mul, opsTotal_add_num]
    exact_mod_cast Nat.le_trans (add_le_add le_rfl (add_le_add le_rfl (add_le_add le_rfl (h _))))
      (by omega : 1 + (1 + (1 + d * 2)) ≤ 3 + 2 * d)
  refine (maxOps_bind_uniform maxOps_coinT.le (B := (d : ℕ∞) + ((3 * d + 2 : ℕ) : ℕ∞) +
    ((r * (4 * d + 5) : ℕ) : ℕ∞) + (5 + 2 * d)) (fun stay => ?_)).trans ?_
  · cases stay
    · simp only [Bool.false_eq_true, ite_false]
      refine (maxOps_bind_uniform (p := gaussianT (n := d)) maxOps_gaussianT.le
        (B := (((3 * d + 2 : ℕ) : ℕ∞) + (((r * (4 * d + 5) : ℕ) : ℕ∞) + (5 + 2 * d))))
        (fun g => ?_)).trans ?_
      · rw [maxOps_compute_bind, opsTotal_normalize hd]
        refine add_le_add le_rfl ?_
        rw [maxOps_compute_bind]
        refine add_le_add (Nat.cast_le.mpr (opsTotal_chord_le hd r a β' x _)) ?_
        rcases (chord r a β' x (normalize g).val).val with ⟨_ | lo, _ | hi⟩
        · exact bot_le
        · exact bot_le
        · exact bot_le
        · simp only [Option.elim_some]
          rw [maxOps_compute_bind, opsTotal_lt, Nat.cast_one]
          split_ifs
          · exact (add_le_add le_rfl (hmove _ lo hi)).trans (by ring_nf; exact le_rfl)
          · simpa only [maxOps_pure, add_zero] using
              (add_le_add (show (1 : ℕ∞) ≤ 5 by decide) (show 0 ≤ (2 : ℕ∞) * d from bot_le))
      · ring_nf
        exact le_rfl
    · exact bot_le
  · push_cast
    ring_nf
    exact le_rfl

theorem maxOps_hitAndRunWalkT (hd : 0 < d) (r : ℕ) (a : Fin r → NumPoint d)
    (β' : Fin r → Num ℝ) (steps : Num ℕ) (x : NumPoint d) :
    maxOps (hitAndRunWalkT r a β' steps x) ≤ 1 + steps.get * (6 * d + 8 + r * (4 * d + 5)) := by
  unfold hitAndRunWalkT loopTree
  change (opsTotal (Charged.op (Op.num .loop) () : Prog Unit).cost : ℕ∞) + _ ≤ _
  rw [opsTotal_op, Nat.cast_one]
  refine add_le_add le_rfl ?_
  refine (maxOps_bind_uniform (maxOps_loopRounds ?_ _ _) (fun _ => maxOps_pure _ |>.le)).trans_eq (add_zero _)
  intro y
  exact (maxOps_pure_bind (hitAndRunStepT r a β' y) (fun y' => Sum.inl y')).trans
    (maxOps_hitAndRunStepT hd r a β' y)

private theorem opsTotal_roundOne_le (one : Num ℤ) (x v : Num ℝ) :
    opsTotal (do
      let fl ← floor x
      let flR ← intCast fl
      let frac ← A.sub x flR
      let up ← A.lt v frac
      if up then A.add fl one else A.pure fl : Prog (Num ℤ)).cost ≤ 5 := by
  simp only [opsTotal_bind, opsTotal_floor, opsTotal_intCast, opsTotal_sub, opsTotal_lt]
  split_ifs <;> simp

theorem maxOps_roundCoordsT (one : Num ℤ) :
    ∀ (k : ℕ) (x : Fin k → Num ℝ), maxOps (roundCoordsT (d := d) one k x) ≤ k * 6
  | 0, _ => by simp [roundCoordsT, maxOps]
  | k + 1, x => by
      rw [roundCoordsT]
      refine (maxOps_bind_uniform maxOps_unitT.le (B := 5 + k * 6) (fun v => ?_)).trans ?_
      · rw [maxOps_compute_bind]
        refine add_le_add ?_ ?_
        · exact Nat.cast_le.mpr (opsTotal_roundOne_le one (x 0) v)
        · refine (maxOps_bind_uniform (maxOps_roundCoordsT one k (Fin.tail x))
            (fun _ => maxOps_pure _ |>.le)).trans_eq (add_zero _)
      · push_cast
        ring_nf
        exact le_rfl

theorem maxOps_roundPointT_le (x : NumPoint d) : maxOps (roundPointT x) ≤ 1 + d * 6 := by
  rw [roundPointT, maxOps_compute_bind, opsTotal_lit, Nat.cast_one]
  exact add_le_add le_rfl (maxOps_roundCoordsT _ d x)

theorem maxOps_sampleTryT_le (hd : 0 < d) (L : Loaded d) (W : WalkConstants d L.facets)
    (scaled : Fin L.facets → Num ℝ) (dimN : Num ℕ) :
    maxOps (sampleTryT L W scaled dimN) ≤ sampleTryOps d L.facets W.steps.get := by
  unfold sampleTryT sampleTryOps
  let R : ℕ∞ := 1 + W.steps.get * (6 * d + 8 + L.facets * (4 * d + 5))
  let C : ℕ∞ := 1 + d * 6 + (d + 2 * d * L.facets)
  refine (maxOps_bind_uniform maxOps_gaussianT.le
    (B := 1 + (((3 * d + 2 : ℕ) : ℕ∞) + (R + (↑(d * 2 : ℕ) + C)))) fun g => ?_).trans ?_
  · refine maxOps_bind_uniform maxOps_unitT.le fun u => ?_
    rw [maxOps_compute_bind, opsTotal_ballStart hd]
    refine add_le_add le_rfl ?_
    refine maxOps_bind_uniform (maxOps_hitAndRunWalkT hd _ _ _ _ _) fun y => ?_
    rw [maxOps_compute_bind]
    refine add_le_add (Nat.cast_le.mpr ?_) ?_
    · exact opsTotal_forEach_le 2 d _ (fun _ => by simp [opsTotal_add])
    · refine maxOps_bind_uniform (maxOps_roundPointT_le _) fun z => ?_
      rw [maxOps_compute_bind, maxOps_pure, add_zero]
      have hh : (opsTotal (latticeMember L scaled z).cost : ℕ∞) ≤
          ((d + 2 * d * L.facets : ℕ) : ℕ∞) :=
        Nat.cast_le.mpr (opsTotal_latticeMember_le hd L scaled z)
      push_cast at hh
      exact hh
  · dsimp only [R, C]
    push_cast
    ring_nf
    exact le_rfl

end ttc.Tape
