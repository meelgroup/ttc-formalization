/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.ChargedCV18.Program

/-!
# The counted arithmetic: values and costs

`cv18Program` (`Model/Pseudocode.lean`) runs its arithmetic through the `Counted`
programs of `Model/Prelude.lean`, on sealed numbers.  This file proves, for each of them,

* **its value**: the number it holds is the formula it stands for
  (`properTestProg_value`, `lazyTestProg_value`, `Counted.median_value`, …), read through
  `Num.get` and `NumPoint.view`.  This is what lets `Analysis/PseudocodeBridge.lean`
  identify the erased pseudocode with the analysed program; and
* **its cost**, in closed form (`properTestProg_cost = 2n + 2`, …), which is what the
  arithmetic bound on `opCost` is assembled from.
-/

open MeasureTheory
open Arlib.Computation (Num)

namespace ttc.ChargedCV18

open ArlibCommunity.Algorithms.CV18

/-! ## Values -/

@[simp] theorem NumPoint.ofLp_view {n : ℕ} (x : NumPoint n) :
    WithLp.ofLp x.view = fun i => (x i).get := rfl

theorem NumPoint.view_apply {n : ℕ} (x : NumPoint n) (i : Fin n) : x.view i = (x i).get := rfl

namespace Counted

@[simp] theorem pure_value {α : Type} (a : α) : (Counted.pure a).value = a := rfl

/-- Stated through `Charged.val_bind` rather than `rfl`, so that `simp` hands the kernel
an application of this lemma instead of a definitional unfolding of every bind. -/
@[simp] theorem bind_value {α β : Type} (m : Counted α) (f : α → Counted β) :
    (m >>= f).value = (f m.value).value :=
  Arlib.Computation.Charged.val_bind (κ := Op) (κₛ := Cell) m f

@[simp] theorem pure_value' {α : Type} (a : α) : (Pure.pure a : Counted α).value = a := rfl

@[simp] theorem lit_value {α : Type} (a : α) : (lit a).value.get = a := rfl
@[simp] theorem pick_value {α : Type} (a : α) : (pick a).value.get = a := rfl
@[simp] theorem isMember_value (b : Bool) : (isMember b).value = b := rfl
@[simp] theorem push_value {α : Type} (xs : List α) (x : α) : (push xs x).value = xs ++ [x] :=
  rfl
@[simp] theorem cell_value {α : Type} (a : α) : (cell a).value = a := rfl
@[simp] theorem add_value {α : Type} [Add α] (x y : Num α) :
    (add x y).value.get = x.get + y.get := rfl
@[simp] theorem sub_value {α : Type} [Sub α] (x y : Num α) :
    (sub x y).value.get = x.get - y.get := rfl
@[simp] theorem mul_value {α : Type} [Mul α] (x y : Num α) :
    (mul x y).value.get = x.get * y.get := rfl
@[simp] theorem div_value {α : Type} [Div α] (x y : Num α) :
    (div x y).value.get = x.get / y.get := rfl
@[simp] theorem max_value {α : Type} [Max α] (x y : Num α) :
    (max x y).value.get = Max.max x.get y.get := rfl
@[simp] theorem min_value {α : Type} [Min α] (x y : Num α) :
    (min x y).value.get = Min.min x.get y.get := rfl
@[simp] theorem le_value {α : Type} [LE α] [DecidableLE α] (x y : Num α) :
    (le x y).value = decide (x.get ≤ y.get) := rfl
@[simp] theorem lt_value {α : Type} [LinearOrder α] (x y : Num α) :
    (lt x y).value = decide (x.get < y.get) := by
  change (!decide (y.get ≤ x.get)) = decide (x.get < y.get)
  by_cases h : x.get < y.get
  · simp [h, not_le.mpr h]
  · simp [h, not_lt.mp h]
@[simp] theorem ceil_value (x : Num ℝ) : (ceil x).value.get = Nat.ceil x.get := rfl
@[simp] theorem cast_value (k : Num ℕ) : (cast k).value.get = (k.get : ℝ) := rfl
@[simp] theorem sqrt_value (x : Num ℝ) : (sqrt x).value.get = Real.sqrt x.get := rfl
@[simp] theorem log_value (x : Num ℝ) : (log x).value.get = Real.log x.get := rfl
@[simp] theorem exp_value (x : Num ℝ) : (exp x).value.get = Real.exp x.get := rfl
@[simp] theorem root_value (u : Num ℝ) (k : Num ℕ) :
    (root u k).value.get = u.get ^ ((k.get : ℝ)⁻¹) := rfl

@[simp] theorem pow_value (x : Num ℝ) : ∀ k : ℕ, (pow x k).value.get = x.get ^ k
  | 0 => by simp [pow]
  | k + 1 => by simp [pow, pow_value x k, pow_succ]

@[simp] theorem forEach_value {α : Type} : ∀ {n : ℕ} (f : Fin n → Counted α),
    (forEach f).value = fun i => (f i).value
  | 0, f => funext fun i => i.elim0
  | n + 1, f => by
      rw [forEach, bind_value, bind_value, pure_value, forEach_value]
      funext i
      refine Fin.cases rfl (fun j => rfl) i

theorem dot_value : ∀ (n : ℕ) (a x : NumPoint n),
    (dot n a x).value.get = ∑ i, (a i).get * (x i).get
  | 0, _, _ => by simp [dot]
  | 1, a, x => by simp [dot]
  | n + 2, a, x => by
      rw [Fin.sum_univ_succ]
      simp only [dot, bind_value, mul_value, add_value, dot_value (n + 1)]
      rfl

theorem normSq_value {n : ℕ} (x : NumPoint n) : (normSq x).value.get = ‖x.view‖ ^ 2 := by
  rw [normSq, dot_value, EuclideanSpace.real_norm_sq_eq]
  simp [sq, NumPoint.view_apply]

theorem norm_value {n : ℕ} (x : NumPoint n) : (norm x).value.get = ‖x.view‖ := by
  simp [norm, normSq_value, Real.sqrt_sq (norm_nonneg _)]

theorem smul_value {n : ℕ} (a : Num ℝ) (x : NumPoint n) :
    (smul a x).value.view = a.get • x.view := by
  ext i
  simp [smul, NumPoint.view_apply]

theorem addVec_value {n : ℕ} (x y : NumPoint n) : (addVec x y).value.view = x.view + y.view := by
  ext i
  simp [addVec, NumPoint.view_apply]

theorem ballStart_value {n : ℕ} (dim : Num ℕ) (g : NumPoint n) (u : Num ℝ) :
    (ballStart dim g u).value.view = (u.get ^ ((dim.get : ℝ)⁻¹) / ‖g.view‖) • g.view := by
  simp only [ballStart, bind_value, smul_value, div_value, root_value, sqrt_value,
    normSq_value, Real.sqrt_sq (norm_nonneg _)]

theorem gaussianLogWeight_value {n : ℕ} (s : Num ℝ) (x : NumPoint n) :
    (gaussianLogWeight s x).value.get = -‖x.view‖ ^ 2 / (2 * s.get) := by
  simp [gaussianLogWeight, normSq_value, neg_div]

theorem sum_value : ∀ (m : ℕ) (a : Fin m → Num ℕ), (sum m a).value.get = ∑ i, (a i).get
  | 0, _ => by simp [sum]
  | 1, a => by simp [sum]
  | m + 2, a => by
      rw [Fin.sum_univ_succ]
      simp only [sum, bind_value, add_value, sum_value (m + 1)]
      rfl

@[simp] theorem mulLit_value (c : ℝ) (x : Num ℝ) : (mulLit c x).value.get = c * x.get := rfl
@[simp] theorem divLit_value (x : Num ℝ) (c : ℝ) : (divLit x c).value.get = x.get / c := rfl
@[simp] theorem litDiv_value (c : ℝ) (x : Num ℝ) : (litDiv c x).value.get = c / x.get := rfl
@[simp] theorem litMax_value (c : ℝ) (x : Num ℝ) :
    (litMax c x).value.get = Max.max c x.get := rfl
@[simp] theorem protectedLog_value (x : Num ℝ) :
    (protectedLog x).value.get = ArlibCommunity.Algorithms.CV18.protectedLog x.get := rfl

open Classical in
/-- **The median.**  Held with its count `m = |v|`, the median program holds
`medianOf` of the numbers `v` holds. -/
theorem median_value (m : Num ℕ) (v : List (Num ℝ)) (hm : m.get = v.length) :
    (median m v).value.get = Arlib.Probability.medianOf fun i : Fin v.length => (v.get i).get := by
  set L := v.length with hL
  set V : Fin L → ℝ := fun i => (v.get i).get with hV
  have hflag : ∀ (p : Prop) [Decidable p],
      (if p then (lit (1 : ℕ)).value else (lit (0 : ℕ)).value).get = if p then 1 else 0 := by
    intro p _; split <;> rfl
  simp only [median, bind_value, pure_value, forEach_value, lt_value, le_value, div_value,
    lit_value, sum_value, hflag, decide_eq_true_eq, hm, cell_value]
  rcases Nat.eq_zero_or_pos L with hL0 | hLpos
  · have h0 : List.finRange v.length = [] :=
      List.eq_nil_of_length_eq_zero (by rw [List.length_finRange, ← hL]; exact hL0)
    rw [h0, List.find?_nil]
    rw [Arlib.Probability.medianOf, dite_eq_right (by omega : ¬ 0 < v.length)]
    rfl
  set σ := Tuple.sort V
  set k : Fin L := ⟨L / 2, Nat.div_lt_self hLpos one_lt_two⟩
  have hk : (k : ℕ) = L / 2 := rfl
  set w := V ∘ σ
  have hmono : Monotone w := Tuple.monotone_sort V
  have hmed : Arlib.Probability.medianOf V = w k := by
    rw [Arlib.Probability.medianOf, dite_eq_left (by omega : 0 < v.length)]
    rfl
  have hcount : ∀ (p : ℝ → Prop) [DecidablePred p],
      (∑ j : Fin L, if p (V j) then (1 : ℕ) else 0) =
        (Finset.univ.filter fun t => p (w t)).card := by
    intro p _
    rw [Finset.sum_boole, Nat.cast_id]
    exact (Finset.card_equiv σ (by simp [w])).symm
  have key : ∀ x : ℝ, ((∑ j, if V j < x then (1 : ℕ) else 0) ≤ L / 2 ∧
      L / 2 < ∑ j, if V j ≤ x then (1 : ℕ) else 0) ↔ x = w k := by
    intro x
    rw [hcount (· < x), hcount (· ≤ x)]
    constructor
    · rintro ⟨h1, h2⟩
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hsub : (Finset.univ.filter fun t => w t ≤ x) ⊆ Finset.Iio k := by
          intro t ht
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
          simp only [Finset.mem_Iio]
          by_contra hkt
          exact absurd (lt_of_le_of_lt ht hlt) (not_lt.mpr (hmono (not_lt.mp hkt)))
        have := Finset.card_le_card hsub
        rw [Fin.card_Iio] at this
        omega
      · have hsub : Finset.Iic k ⊆ (Finset.univ.filter fun t => w t < x) := by
          intro t ht
          simp only [Finset.mem_Iic] at ht
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact lt_of_le_of_lt (hmono ht) hgt
        have := Finset.card_le_card hsub
        rw [Fin.card_Iic] at this
        omega
    · rintro rfl
      constructor
      · have hsub : (Finset.univ.filter fun t => w t < w k) ⊆ Finset.Iio k := by
          intro t ht
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
          simp only [Finset.mem_Iio]
          by_contra hkt
          exact absurd ht (not_lt.mpr (hmono (not_lt.mp hkt)))
        have := Finset.card_le_card hsub
        rw [Fin.card_Iio] at this
        omega
      · have hsub : Finset.Iic k ⊆ (Finset.univ.filter fun t => w t ≤ w k) := by
          intro t ht
          simp only [Finset.mem_Iic] at ht
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hmono ht
        have := Finset.card_le_card hsub
        rw [Fin.card_Iic] at this
        omega
  have hex : ∃ i : Fin L, (∑ j, if V j < V i then (1 : ℕ) else 0) ≤ L / 2 ∧
      L / 2 < ∑ j, if V j ≤ V i then (1 : ℕ) else 0 := ⟨σ k, (key _).2 rfl⟩
  split
  · rename_i i h
    have hi := List.find?_some h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
    simp only [pure_value, hmed]
    exact (key _).1 hi
  · rename_i h
    obtain ⟨i, hi⟩ := hex
    have hn := List.find?_eq_none.mp h i (List.mem_finRange i)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hn
    exact absurd hi hn

end Counted

theorem ballProposalProg_value {n : ℕ} (dim : Num ℕ) (x : NumPoint n) (radius : Num ℝ)
    (g : NumPoint n) (u : Num ℝ) : (ballProposalProg dim x radius g u).value.view =
      x.view + radius.get • ((u.get ^ ((dim.get : ℝ)⁻¹) / ‖g.view‖) • g.view) := by
  simp only [ballProposalProg, Counted.bind_value, Counted.addVec_value, Counted.smul_value,
    Counted.ballStart_value]

theorem gaussianStartProg_value {n : ℕ} (rootVariance : Num ℝ) (g : NumPoint n) :
    (gaussianStartProg rootVariance g).value.view = rootVariance.get • g.view :=
  Counted.smul_value _ _

theorem properTestProg_value {n : ℕ} (rootT radius : Num ℝ) (y : NumPoint n) :
    (properTestProg rootT radius y).value =
      decide (‖y.view‖ ≤ rootT.get ∧ ‖y.view‖ ≤ radius.get) := by
  simp [properTestProg, Counted.norm_value]

theorem lazyTestProg_value {n : ℕ} (sigma2 : Num ℝ) (x y : NumPoint n) (coin : Num ℝ) :
    (lazyTestProg sigma2 x y coin).value =
      decide (coin.get ≤ lazyAcceptance sigma2.get x.view y.view) := by
  simp only [lazyTestProg, Counted.bind_value, Counted.le_value, Counted.div_value,
    Counted.min_value, Counted.lit_value, Counted.exp_value, Counted.gaussianLogWeight_value,
    lazyAcceptance, metropolisAcceptance]
  exact decide_eq_decide.mpr Iff.rfl

theorem scaleAcceptTestProg_value {n : ℕ} (sigma2 c : Num ℝ) (y : NumPoint n) (coin : Num ℝ) :
    (scaleAcceptTestProg sigma2 c y coin).value =
      decide (ENNReal.ofReal coin.get ≤
        (2 : ENNReal)⁻¹ * gaussianScaleAcceptance sigma2.get c.get y.view) := by
  simp only [scaleAcceptTestProg, Counted.bind_value, Counted.mul_value, Counted.div_value,
    Counted.exp_value, Counted.gaussianLogWeight_value, Counted.le_value, Counted.lit_value]
  congr 1
  apply propext
  unfold gaussianScaleAcceptance
  set a := Real.exp (-‖y.view‖ ^ 2 / (2 * sigma2.get))
  set b := Real.exp (-‖y.view‖ ^ 2 / (2 * (sigma2.get / (c.get * c.get))))
  have ha : 0 < a := Real.exp_pos _
  have hb : 0 < b := Real.exp_pos _
  rw [show c.get ^ 2 = c.get * c.get by ring, ← ENNReal.ofReal_div_of_pos hb,
    show (2 : ENNReal)⁻¹ = ENNReal.ofReal 2⁻¹ by simp,
    ← ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_le_ofReal_iff (by positivity)]
  constructor <;> intro h <;> linarith [show 2⁻¹ * (a / b) = a / b / 2 by ring]

theorem gaussianRatioWeightProg_value {n : ℕ} (sigma2 tau2 : Num ℝ) (x : NumPoint n) :
    (gaussianRatioWeightProg sigma2 tau2 x).value.get =
      gaussianRatioWeight sigma2.get tau2.get x.view := by
  simp [gaussianRatioWeightProg, Counted.gaussianLogWeight_value, gaussianRatioWeight]

theorem uniformRatioWeightProg_value {n : ℕ} (sigma2 : Num ℝ) (x : NumPoint n) :
    (uniformRatioWeightProg sigma2 x).value.get = uniformRatioWeight sigma2.get x.view := by
  simp [uniformRatioWeightProg, Counted.normSq_value, uniformRatioWeight]


/-! ## Costs -/

namespace Counted

theorem bind_tally {α β : Type} (m : Counted α) (f : α → Counted β) :
    (m >>= f).tally = m.tally + (f m.value).tally := rfl

@[simp] theorem bind_cost {α β : Type} (m : Counted α) (f : α → Counted β) :
    (m >>= f).cost = m.cost + (f m.value).cost := by
  simp only [cost, bind_tally, opsTotal_add]

@[simp] theorem pure_cost {α : Type} (a : α) : (Counted.pure a).cost = 0 := by
  show opsTotal (Arlib.Computation.Charged.cost
    (Arlib.Computation.Charged.pure a : Arlib.Computation.Charged Op Cell α)) = 0
  have h : (Arlib.Computation.Charged.pure a : Arlib.Computation.Charged Op Cell α).cost = 0 :=
    rfl
  rw [h, opsTotal_zero]
@[simp] theorem pure_cost' {α : Type} (a : α) : (Pure.pure a : Counted α).cost = 0 :=
  pure_cost a

/-- Every arlib `Num` operation is one operation. -/
theorem one_cost {α : Type} (c : Counted α) (o : Op)
    (h : c.tally = Arlib.Computation.CostVec.one o) : c.cost = 1 := by
  simp [cost, h]

@[simp] theorem lit_cost {α : Type} (a : α) : (lit a).cost = 1 := one_cost _ _ rfl
theorem pick_tally {α : Type} (a : α) :
    (pick a).tally = Arlib.Computation.CostVec.one Op.draw := by
  funext o
  simp [pick, tally, drawLabel, Arlib.Computation.CostVec.exchange,
    Arlib.Computation.CostVec.one, Arlib.Computation.numOpcode, Arlib.Computation.NumOps.charge]
@[simp] theorem pick_cost {α : Type} (a : α) : (pick a).cost = 1 := one_cost _ _ (pick_tally a)
theorem isMember_tally (b : Bool) : (isMember b).tally = Arlib.Computation.CostVec.one Op.query := rfl
@[simp] theorem isMember_cost (b : Bool) : (isMember b).cost = 1 := one_cost _ _ (isMember_tally b)
@[simp] theorem push_cost {α : Type} (xs : List α) (x : α) : (push xs x).cost = 1 :=
  one_cost _ _ rfl
@[simp] theorem cell_cost {α : Type} (a : α) : (cell a).cost = 1 := one_cost _ _ rfl
@[simp] theorem add_cost {α : Type} [Add α] (x y : Num α) : (add x y).cost = 1 :=
  one_cost _ _ rfl
@[simp] theorem sub_cost {α : Type} [Sub α] (x y : Num α) : (sub x y).cost = 1 :=
  one_cost _ _ rfl
@[simp] theorem mul_cost {α : Type} [Mul α] (x y : Num α) : (mul x y).cost = 1 :=
  one_cost _ _ rfl
@[simp] theorem div_cost {α : Type} [Div α] (x y : Num α) : (div x y).cost = 1 :=
  one_cost _ _ rfl
@[simp] theorem max_cost {α : Type} [Max α] (x y : Num α) : (max x y).cost = 1 :=
  one_cost _ _ rfl
@[simp] theorem min_cost {α : Type} [Min α] (x y : Num α) : (min x y).cost = 1 :=
  one_cost _ _ rfl
@[simp] theorem le_cost {α : Type} [LE α] [DecidableLE α] (x y : Num α) : (le x y).cost = 1 :=
  one_cost _ _ rfl
@[simp] theorem lt_cost {α : Type} [LinearOrder α] (x y : Num α) : (lt x y).cost = 1 := by
  simp only [lt]
  exact one_cost _ _ rfl
@[simp] theorem ceil_cost (x : Num ℝ) : (ceil x).cost = 1 := one_cost _ _ rfl
@[simp] theorem cast_cost (k : Num ℕ) : (cast k).cost = 1 := one_cost _ _ rfl
@[simp] theorem sqrt_cost (x : Num ℝ) : (sqrt x).cost = 1 := one_cost _ _ rfl
@[simp] theorem log_cost (x : Num ℝ) : (log x).cost = 1 := one_cost _ _ rfl
@[simp] theorem exp_cost (x : Num ℝ) : (exp x).cost = 1 := one_cost _ _ rfl
@[simp] theorem root_cost (u : Num ℝ) (k : Num ℕ) : (root u k).cost = 1 := one_cost _ _ rfl

@[simp] theorem mulLit_cost (c : ℝ) (x : Num ℝ) : (mulLit c x).cost = 2 := by simp [mulLit]
@[simp] theorem divLit_cost (x : Num ℝ) (c : ℝ) : (divLit x c).cost = 2 := by simp [divLit]
@[simp] theorem litDiv_cost (c : ℝ) (x : Num ℝ) : (litDiv c x).cost = 2 := by simp [litDiv]
@[simp] theorem litMax_cost (c : ℝ) (x : Num ℝ) : (litMax c x).cost = 2 := by simp [litMax]
@[simp] theorem protectedLog_cost (x : Num ℝ) : (protectedLog x).cost = 3 := by
  simp [protectedLog]

/-- `x^k` costs `k + 1`: the literal `1` and `k` multiplications. -/
@[simp] theorem pow_cost (x : Num ℝ) : ∀ k : ℕ, (pow x k).cost = k + 1
  | 0 => by simp [pow]
  | k + 1 => by simp [pow, pow_cost x k]

@[simp] theorem forEach_cost {α : Type} : ∀ {n : ℕ} (f : Fin n → Counted α),
    (forEach f).cost = ∑ i, (f i).cost
  | 0, f => by simp [forEach]
  | n + 1, f => by
      rw [Fin.sum_univ_succ, forEach, bind_cost, bind_cost, pure_cost, forEach_cost]
      simp

/-- A dot product of length `n ≥ 1` costs `2n − 1`. -/
theorem dot_cost : ∀ (n : ℕ), 0 < n → ∀ (a x : NumPoint n), (dot n a x).cost = 2 * n - 1
  | 1, _, a, x => by simp [dot]
  | n + 2, _, a, x => by
      simp only [dot, bind_cost, mul_cost, add_cost, dot_cost (n + 1) (by omega)]
      omega

/-- A sum of `m ≥ 1` terms costs `m − 1`. -/
theorem sum_cost : ∀ (m : ℕ), 0 < m → ∀ (a : Fin m → Num ℕ), (sum m a).cost = m - 1
  | 1, _, a => by simp [sum]
  | m + 2, _, a => by
      simp only [sum, bind_cost, add_cost, sum_cost (m + 1) (by omega)]
      omega

theorem normSq_cost {n : ℕ} (hn : 0 < n) (x : NumPoint n) :
    (normSq x).cost = 2 * n - 1 := dot_cost n hn _ _

theorem norm_cost {n : ℕ} (hn : 0 < n) (x : NumPoint n) : (norm x).cost = 2 * n := by
  simp only [norm, bind_cost, normSq_cost hn, sqrt_cost]
  omega

theorem smul_cost {n : ℕ} (a : Num ℝ) (x : NumPoint n) : (smul a x).cost = n := by
  simp [smul]

theorem addVec_cost {n : ℕ} (x y : NumPoint n) : (addVec x y).cost = n := by
  simp [addVec]

theorem gaussianLogWeight_cost {n : ℕ} (hn : 0 < n) (s : Num ℝ) (x : NumPoint n) :
    (gaussianLogWeight s x).cost = 2 * n + 4 := by
  simp only [gaussianLogWeight, bind_cost, normSq_cost hn, lit_cost, mul_cost, div_cost,
    sub_cost]
  omega

/-- A uniform point of the unit ball costs `3n + 2`. -/
theorem ballStart_cost {n : ℕ} (hn : 0 < n) (dim : Num ℕ) (g : NumPoint n) (u : Num ℝ) :
    (ballStart dim g u).cost = 3 * n + 2 := by
  simp only [ballStart, bind_cost, normSq_cost hn, sqrt_cost, root_cost, div_cost, smul_cost]
  omega

/-! ### The loop over a held count -/

section Loop
open Arlib.Computation

private theorem fold_none {β ι : Type} {f : β → ι → Charged Op Cell (Option β)} {a : ι}
    {l : List ι} {b : β} (h : Charged.val (f b a) = none) :
    Charged.val (Charged.foldlWhile f (a :: l) b) = b ∧
      Charged.cost (Charged.foldlWhile f (a :: l) b) = Charged.cost (f b a) := by
  unfold Charged.val at h
  rw [Charged.foldlWhile.eq_2]
  simp only [h]
  exact ⟨rfl, rfl⟩

private theorem fold_some {β ι : Type} {f : β → ι → Charged Op Cell (Option β)} {a : ι}
    {l : List ι} {b b' : β} (h : Charged.val (f b a) = some b') :
    Charged.val (Charged.foldlWhile f (a :: l) b) = Charged.val (Charged.foldlWhile f l b') ∧
      Charged.cost (Charged.foldlWhile f (a :: l) b) =
        Charged.cost (f b a) + Charged.cost (Charged.foldlWhile f l b') := by
  unfold Charged.val at h
  rw [Charged.foldlWhile.eq_2]
  simp only [h]
  exact ⟨rfl, rfl⟩

/-- A round that stops ends the fold, at the round's price. -/
theorem foldlWhile_cons_none {β ι : Type} {f : β → ι → Counted (Option β)} {a : ι}
    {l : List ι} {b : β} (h : (f b a).value = none) :
    Counted.value (Charged.foldlWhile f (a :: l) b) = b ∧
      Counted.cost (Charged.foldlWhile f (a :: l) b) = (f b a).cost :=
  let ⟨h1, h2⟩ := fold_none (f := f) (l := l) h
  ⟨h1, congrArg opsTotal h2⟩

/-- A round that continues passes its state on, and the prices add. -/
theorem foldlWhile_cons_some {β ι : Type} {f : β → ι → Counted (Option β)} {a : ι}
    {l : List ι} {b b' : β} (h : (f b a).value = some b') :
    Counted.value (Charged.foldlWhile f (a :: l) b) =
        Counted.value (Charged.foldlWhile f l b') ∧
      Counted.cost (Charged.foldlWhile f (a :: l) b) =
        (f b a).cost + Counted.cost (Charged.foldlWhile f l b') :=
  let ⟨h1, h2⟩ := fold_some (f := f) (l := l) h
  ⟨h1, (congrArg opsTotal h2).trans (opsTotal_add _ _)⟩

/-- With no rounds left, the fold holds its state and costs nothing. -/
theorem foldlWhile_nil {β ι : Type} (f : β → ι → Counted (Option β)) (b : β) :
    Counted.value (Charged.foldlWhile f [] b) = b ∧
      Counted.cost (Charged.foldlWhile f [] b) = 0 :=
  ⟨rfl, (congrArg opsTotal (Charged.cost_foldlWhile_nil f b)).trans opsTotal_zero⟩

/-- A loop over a held count is a fold over its rounds. -/
theorem iterateWhile_value {β : Type} (f : β → Counted (Option β)) (n : Num ℕ) (b : β) :
    (iterateWhile f n b).value =
      Counted.value (Charged.foldlWhile (fun b _ => f b) (List.range n.get) b) := rfl

/-- A loop over a held count costs its entry plus its rounds. -/
theorem iterateWhile_cost {β : Type} (f : β → Counted (Option β)) (n : Num ℕ) (b : β) :
    (iterateWhile f n b).cost =
      1 + Counted.cost (Charged.foldlWhile (fun b _ => f b) (List.range n.get) b) := by
  show opsTotal (Charged.cost ((Charged.op (numOpcode Op .loop) b : Charged Op Cell β) >>=
    fun b => Charged.foldlWhile (fun b _ => f b) (List.range n.get) b)) = _
  rw [Charged.cost_bind, Charged.cost_op, opsTotal_add, opsTotal_one, Charged.val_op]
  rfl

end Loop

/-- The median of `L ≥ 1` held numbers costs at most `4L² + 5`. -/
theorem median_cost_le (m : Num ℕ) (v : List (Num ℝ)) (hv : 0 < v.length) :
    (median m v).cost ≤ 4 * v.length ^ 2 + v.length + 5 := by
  simp only [median, bind_cost, forEach_cost, lt_cost, le_cost, lit_cost, div_cost, cell_cost,
    pure_cost, sum_cost v.length hv, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
  obtain ⟨k, hk⟩ : ∃ k, v.length = k + 1 := ⟨v.length - 1, by omega⟩
  split <;> rename_i h <;> simp only [pure_cost, lit_cost] <;> clear h <;>
  · rw [hk]
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega

end Counted

/-- A ball-walk proposal costs `5n + 2`. -/
theorem ballProposalProg_cost {n : ℕ} (hn : 0 < n) (dim : Num ℕ) (x : NumPoint n)
    (radius : Num ℝ) (g : NumPoint n) (u : Num ℝ) :
    (ballProposalProg dim x radius g u).cost = 5 * n + 2 := by
  simp only [ballProposalProg, Counted.bind_cost, Counted.ballStart_cost hn, Counted.smul_cost,
    Counted.addVec_cost]
  omega

/-- The starting point costs `n`. -/
theorem gaussianStartProg_cost {n : ℕ} (rootVariance : Num ℝ) (g : NumPoint n) :
    (gaussianStartProg rootVariance g).cost = n :=
  Counted.smul_cost _ _

theorem properTestProg_cost {n : ℕ} (hn : 0 < n) (rootT radius : Num ℝ) (y : NumPoint n) :
    (properTestProg rootT radius y).cost = 2 * n + 2 := by
  simp only [properTestProg, Counted.bind_cost, Counted.norm_cost hn, Counted.le_cost,
    Counted.pure_cost]

theorem lazyTestProg_cost {n : ℕ} (hn : 0 < n) (sigma2 : Num ℝ) (x y : NumPoint n)
    (coin : Num ℝ) : (lazyTestProg sigma2 x y coin).cost = 4 * n + 16 := by
  simp only [lazyTestProg, Counted.bind_cost, Counted.gaussianLogWeight_cost hn,
    Counted.exp_cost, Counted.div_cost, Counted.lit_cost, Counted.min_cost, Counted.le_cost]
  omega

theorem scaleAcceptTestProg_cost {n : ℕ} (hn : 0 < n) (sigma2 c : Num ℝ) (y : NumPoint n)
    (coin : Num ℝ) : (scaleAcceptTestProg sigma2 c y coin).cost = 4 * n + 16 := by
  simp only [scaleAcceptTestProg, Counted.bind_cost, Counted.gaussianLogWeight_cost hn,
    Counted.mul_cost, Counted.exp_cost, Counted.div_cost, Counted.lit_cost, Counted.le_cost]
  omega

theorem gaussianRatioWeightProg_cost {n : ℕ} (hn : 0 < n) (sigma2 tau2 : Num ℝ)
    (x : NumPoint n) : (gaussianRatioWeightProg sigma2 tau2 x).cost = 4 * n + 11 := by
  simp only [gaussianRatioWeightProg, Counted.bind_cost, Counted.gaussianLogWeight_cost hn,
    Counted.exp_cost, Counted.div_cost]
  omega

theorem uniformRatioWeightProg_cost {n : ℕ} (hn : 0 < n) (sigma2 : Num ℝ) (x : NumPoint n) :
    (uniformRatioWeightProg sigma2 x).cost = 2 * n + 3 := by
  simp only [uniformRatioWeightProg, Counted.bind_cost, Counted.normSq_cost hn,
    Counted.lit_cost, Counted.mul_cost, Counted.div_cost, Counted.exp_cost]
  omega

end ttc.ChargedCV18
