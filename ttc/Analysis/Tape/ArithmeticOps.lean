/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.Interp

/-!
# Arithmetic in a facet test

These are costs of the actual sealed computations, including the casts needed
to test a stored integer point. They do not use the old TTC cost model.
-/

set_option autoImplicit false

noncomputable section

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program

variable {α β : Type}

@[simp] theorem opsTotal_bind (p : Prog α) (k : α → Prog β) :
    opsTotal (p >>= k).cost = opsTotal p.cost + opsTotal (k p.val).cost := by
  rw [Charged.cost_bind, opsTotal_add]

@[simp] theorem opsTotal_pure (a : α) : opsTotal (A.pure a).cost = 0 := by
  change opsTotal 0 = 0
  exact opsTotal_zero

@[simp] theorem opsTotal_lit (a : α) : opsTotal (A.lit a).cost = 1 := by
  simp [A.lit, opsTotal_one]

@[simp] theorem opsTotal_cell (a : α) : opsTotal (A.cell a).cost = 1 :=
  opsTotal_op _ _

@[simp] theorem opsTotal_push (xs : List α) (a : α) : opsTotal (A.push xs a).cost = 1 :=
  opsTotal_op _ _

@[simp] theorem opsTotal_mul [Mul α] (a b : Num α) : opsTotal (A.mul a b).cost = 1 := by
  simp [A.mul, opsTotal_one]

@[simp] theorem opsTotal_add_num [Add α] (a b : Num α) : opsTotal (A.add a b).cost = 1 := by
  simp [A.add, opsTotal_one]

@[simp] theorem opsTotal_le [LE α] [DecidableLE α] (a b : Num α) :
    opsTotal (A.le a b).cost = 1 := by
  simp [A.le, opsTotal_one]

@[simp] theorem opsTotal_lt [LinearOrder α] (a b : Num α) :
    opsTotal (A.lt a b).cost = 1 := by
  change opsTotal ((Num.le b a >>= fun ok => A.pure (!ok) : Prog Bool)).cost = 1
  rw [opsTotal_bind, opsTotal_pure, add_zero, Num.cost_le, opsTotal_one]

@[simp] theorem opsTotal_sub [Sub α] (a b : Num α) : opsTotal (A.sub a b).cost = 1 := by
  simp [A.sub, opsTotal_one]

@[simp] theorem opsTotal_div [Div α] (a b : Num α) : opsTotal (A.div a b).cost = 1 := by
  simp [A.div, opsTotal_one]

@[simp] theorem opsTotal_min [Min α] (a b : Num α) : opsTotal (A.min a b).cost = 1 := by
  simp [A.min, opsTotal_one]

@[simp] theorem opsTotal_max [Max α] (a b : Num α) : opsTotal (A.max a b).cost = 1 := by
  simp [A.max, opsTotal_one]

@[simp] theorem opsTotal_sqrt (a : Num ℝ) : opsTotal (A.sqrt a).cost = 1 := by
  simp [A.sqrt, opsTotal_one]

@[simp] theorem opsTotal_exp (a : Num ℝ) : opsTotal (A.exp a).cost = 1 := by
  simp [A.exp, opsTotal_one]

@[simp] theorem opsTotal_root (a : Num ℝ) (n : Num ℕ) : opsTotal (A.root a n).cost = 1 := by
  simp [A.root, opsTotal_one]

theorem opsTotal_forEach_le (B : ℕ) :
    ∀ (n : ℕ) (f : Fin n → Prog α), (∀ i, opsTotal (f i).cost ≤ B) →
      opsTotal (A.forEach f).cost ≤ n * B
  | 0, f, _ => by simp [A.forEach]
  | n + 1, f, h => by
      simp only [A.forEach, opsTotal_bind, opsTotal_pure, add_zero, Nat.succ_mul]
      exact (add_le_add (h 0) (opsTotal_forEach_le B n (fun i => f i.succ) (fun i => h i.succ))).trans
        (Nat.add_comm B (n * B)).le

theorem opsTotal_forEach_uniform (B : ℕ) :
    ∀ (n : ℕ) (f : Fin n → Prog α), (∀ i, opsTotal (f i).cost = B) →
      opsTotal (A.forEach f).cost = n * B
  | 0, f, _ => by simp [A.forEach]
  | n + 1, f, h => by
      simp only [A.forEach, opsTotal_bind, opsTotal_pure, add_zero, Nat.succ_mul, h,
        opsTotal_forEach_uniform B n (fun i => f i.succ) (fun i => h i.succ)]
      exact Nat.add_comm ..

theorem opsTotal_mapM_le (B : ℕ) (f : α → Prog β) (hf : ∀ x, opsTotal (f x).cost ≤ B) :
    ∀ l : List α, opsTotal (l.mapM f).cost ≤ l.length * B
  | [] => by
      simp only [List.mapM_nil, List.length_nil, zero_mul]
      exact (opsTotal_pure ([] : List β)).le
  | x :: xs => by
      rw [List.mapM_cons]
      simp only [opsTotal_bind, List.length_cons, Nat.succ_mul]
      have hp : ∀ (a : β) (b : List β), opsTotal ((pure (a :: b) : Prog (List β))).cost = 0 :=
        fun a b => opsTotal_pure (a :: b)
      simp only [hp, add_zero]
      exact (Nat.add_le_add (hf x) (opsTotal_mapM_le B f hf xs)).trans (Nat.add_comm ..).le

theorem opsTotal_sumList_le : ∀ l : List (Num ℕ), opsTotal (A.sumList l).cost ≤ l.length + 1
  | [] => by simp [A.sumList]
  | [x] => by simp [A.sumList]
  | x :: y :: ys => by
      simp only [A.sumList, opsTotal_bind, opsTotal_add_num, List.length_cons]
      have h := opsTotal_sumList_le (y :: ys)
      simp only [List.length_cons] at h
      omega

theorem opsTotal_firstPassing_le : ∀ l : List (Num ℝ × Bool), opsTotal (A.firstPassing l).cost ≤ 1
  | [] => by simp [A.firstPassing]
  | (x, ok) :: xs => by
      cases ok
      · simpa [A.firstPassing] using opsTotal_firstPassing_le xs
      · simp [A.firstPassing]

theorem opsTotal_dot_pos :
    ∀ (n : ℕ), 0 < n → ∀ (a x : NumPoint n), opsTotal (A.dot n a x).cost = 2 * n - 1
  | 1, _, a, x => by simp [A.dot]
  | n + 2, _, a, x => by
      simp only [A.dot, opsTotal_bind, opsTotal_mul, opsTotal_add_num,
        opsTotal_dot_pos (n + 1) (Nat.succ_pos n)]
      omega

theorem opsTotal_smul {d : ℕ} (a : Num ℝ) (x : NumPoint d) :
    opsTotal (A.smul a x).cost = d := by
  simpa only [A.smul, mul_one] using
    (opsTotal_forEach_uniform 1 d (fun i => A.mul a (x i)) (fun _ => opsTotal_mul _ _))

theorem opsTotal_addVec {d : ℕ} (x y : NumPoint d) :
    opsTotal (A.addVec x y).cost = d := by
  simpa only [A.addVec, mul_one] using
    (opsTotal_forEach_uniform 1 d (fun i => A.add (x i) (y i)) (fun _ => opsTotal_add_num _ _))

theorem opsTotal_normSq {d : ℕ} (hd : 0 < d) (x : NumPoint d) :
    opsTotal (A.normSq x).cost = 2 * d - 1 :=
  opsTotal_dot_pos d hd x x

theorem opsTotal_norm {d : ℕ} (hd : 0 < d) (x : NumPoint d) :
    opsTotal (A.norm x).cost = 2 * d := by
  simp only [A.norm, opsTotal_bind, opsTotal_normSq hd, opsTotal_sqrt]
  omega

theorem opsTotal_ballStart {d : ℕ} (hd : 0 < d) (dim : Num ℕ) (g : NumPoint d) (u : Num ℝ) :
    opsTotal (A.ballStart dim g u).cost = 3 * d + 2 := by
  simp only [A.ballStart, opsTotal_bind, opsTotal_normSq hd, opsTotal_sqrt,
    opsTotal_root, opsTotal_div, opsTotal_smul]
  omega

theorem opsTotal_gaussianLogWeight {d : ℕ} (hd : 0 < d) (s : Num ℝ) (x : NumPoint d) :
    opsTotal (A.gaussianLogWeight s x).cost = 2 * d + 4 := by
  simp only [A.gaussianLogWeight, opsTotal_bind, opsTotal_normSq hd, opsTotal_lit,
    opsTotal_mul, opsTotal_div, opsTotal_sub]
  omega

theorem opsTotal_ballProposalProg {d : ℕ} (hd : 0 < d) (dim : Num ℕ)
    (x : NumPoint d) (r : Num ℝ) (g : NumPoint d) (u : Num ℝ) :
    opsTotal (ballProposalProg dim x r g u).cost = 5 * d + 2 := by
  simp only [ballProposalProg, opsTotal_bind, opsTotal_ballStart hd,
    opsTotal_smul, opsTotal_addVec]
  omega

theorem opsTotal_properTestProg {d : ℕ} (hd : 0 < d) (r s : Num ℝ) (y : NumPoint d) :
    opsTotal (properTestProg r s y).cost = 2 * d + 2 := by
  simp only [properTestProg, opsTotal_bind, opsTotal_norm hd, opsTotal_le, opsTotal_pure]

theorem opsTotal_lazyTestProg {d : ℕ} (hd : 0 < d) (s : Num ℝ) (x y : NumPoint d) (u : Num ℝ) :
    opsTotal (lazyTestProg s x y u).cost = 4 * d + 16 := by
  simp only [lazyTestProg, opsTotal_bind, opsTotal_gaussianLogWeight hd, opsTotal_exp,
    opsTotal_div, opsTotal_lit, opsTotal_min, opsTotal_le]
  omega

theorem opsTotal_scaleAcceptTestProg {d : ℕ} (hd : 0 < d) (s c : Num ℝ)
    (y : NumPoint d) (u : Num ℝ) :
    opsTotal (scaleAcceptTestProg s c y u).cost = 4 * d + 16 := by
  simp only [scaleAcceptTestProg, opsTotal_bind, opsTotal_gaussianLogWeight hd, opsTotal_exp,
    opsTotal_div, opsTotal_lit, opsTotal_mul, opsTotal_le]
  omega

theorem opsTotal_gaussianRatioWeightProg {d : ℕ} (hd : 0 < d) (s t : Num ℝ) (x : NumPoint d) :
    opsTotal (gaussianRatioWeightProg s t x).cost = 4 * d + 11 := by
  simp only [gaussianRatioWeightProg, opsTotal_bind, opsTotal_gaussianLogWeight hd, opsTotal_exp,
    opsTotal_div]
  omega

theorem opsTotal_uniformRatioWeightProg {d : ℕ} (hd : 0 < d) (s : Num ℝ) (x : NumPoint d) :
    opsTotal (uniformRatioWeightProg s x).cost = 2 * d + 3 := by
  simp only [uniformRatioWeightProg, opsTotal_bind, opsTotal_normSq hd, opsTotal_lit,
    opsTotal_mul, opsTotal_div, opsTotal_exp]
  omega

/-- A facet pays for its dot product and a comparison. -/
theorem opsTotal_allFacets {d : ℕ} (hd : 0 < d) :
    ∀ (r : ℕ) (a : Fin r → NumPoint d) (b : Fin r → Num ℝ) (x : NumPoint d),
      opsTotal (allFacets r a b x).cost = 2 * d * r
  | 0, _, _, _ => by simp [allFacets]
  | r + 1, a, b, x => by
      simp only [allFacets, opsTotal_bind, opsTotal_pure, opsTotal_le, add_zero,
        opsTotal_dot_pos _ hd, opsTotal_allFacets hd r, Nat.mul_succ]
      omega

@[simp] theorem opsTotal_intCast (z : Num ℤ) : opsTotal (intCast z).cost = 1 := by
  rw [intCast, Charged.cost_exchange, opsTotal_exchange_relabel, Num.cost_lit, opsTotal_one]

@[simp] theorem opsTotal_floor (x : Num ℝ) : opsTotal (floor x).cost = 1 := by
  rw [floor, Charged.cost_exchange, opsTotal_exchange_relabel, Num.cost_lit, opsTotal_one]

/-- An integer point adds at most one charged cast per coordinate to the facet costs. -/
theorem opsTotal_latticeMember_le {d : ℕ} (hd : 0 < d) (L : Loaded d)
    (scaled : Fin L.facets → Num ℝ) (z : Fin d → Num ℤ) :
    opsTotal (latticeMember L scaled z).cost ≤ d + 2 * d * L.facets := by
  have hc : opsTotal (latticeReal z).cost ≤ d := by
    simpa only [latticeReal, mul_one] using
      (opsTotal_forEach_le 1 d (fun i => intCast (z i)) (fun i => (opsTotal_intCast (z i)).le))
  rw [latticeMember, opsTotal_bind, opsTotal_allFacets hd]
  exact Nat.add_le_add_right hc _

end ttc.Tape
