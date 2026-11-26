/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.StepFold

/-!
# The run's parameters

The program computes `ε' = ε/12`, `δ' = δ/(4m)`, `Thresh`, the precision `b` of `GetPrecision`
and the scales `10^b`, `10^{bn}` (`paramsProg`).  Their values are the old model's
(`paramsProg_val`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ttc (TTCState)

variable {d : ℕ}

/-! ## The two folds -/

section Folds

/-- Counting the components and their facets. -/
theorem val_countFold (one : Num ℕ) (h1 : one.get = 1) :
    ∀ (cs : List (ttc.ComponentInput d)) (acc : Num ℕ × Num ℕ),
      ((cs.foldlM (fun (acc : Num ℕ × Num ℕ) (c : ttc.ComponentInput d) => do
          let m' ← A.add acc.1 one
          let r ← A.lit c.facetCount
          let t' ← A.add acc.2 r
          A.pure (m', t')) acc).val.1.get = acc.1.get + cs.length) ∧
      ((cs.foldlM (fun (acc : Num ℕ × Num ℕ) (c : ttc.ComponentInput d) => do
          let m' ← A.add acc.1 one
          let r ← A.lit c.facetCount
          let t' ← A.add acc.2 r
          A.pure (m', t')) acc).val.2.get = acc.2.get + (cs.map (·.facetCount)).sum)
  | [], acc => by simp
  | c :: cs, acc => by
      rw [List.foldlM_cons]
      simp only [Charged.val_bind]
      obtain ⟨h1', h2'⟩ := val_countFold one h1 cs _
      refine ⟨?_, ?_⟩
      · rw [h1']
        simp [A.add, Num.get_add, h1]
        ring
      · rw [h2']
        simp [A.add, A.lit, Num.get_add, Num.get_lit]
        ring

/-- The largest ratio `required/γᵢ`, from `1`. -/
theorem val_maxFold (required : Num ℝ) :
    ∀ (Ls : List (Loaded d)) (acc : Num ℝ),
      (Ls.foldlM (fun (acc : Num ℝ) (L : Loaded d) => do
          let ratio ← A.div required L.inradius
          A.max acc ratio) acc).val.get =
        Ls.foldl (fun a (L : Loaded d) => max a (required.get / L.inradius.get)) acc.get
  | [], acc => rfl
  | L :: Ls, acc => by
      rw [List.foldlM_cons]
      simp only [Charged.val_bind, List.foldl_cons]
      rw [val_maxFold required Ls]
      simp [A.div, A.max, Num.get_div, Num.get_max]

/-- A left fold of `max` is the least bound of the start and the entries. -/
theorem foldl_max_spec {ι : Type} (g : ι → ℝ) :
    ∀ (l : List ι) (c : ℝ), c ≤ l.foldl (fun a i => max a (g i)) c ∧
      (∀ i ∈ l, g i ≤ l.foldl (fun a i => max a (g i)) c) ∧
      (l.foldl (fun a i => max a (g i)) c = c ∨ ∃ i ∈ l, l.foldl (fun a i => max a (g i)) c = g i)
  | [], c => by simp
  | i :: l, c => by
      obtain ⟨h1, h2, h3⟩ := foldl_max_spec g l (max c (g i))
      simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
      refine ⟨(le_max_left _ _).trans h1, ⟨(le_max_right _ _).trans h1, h2⟩, ?_⟩
      rcases h3 with h | ⟨j, hj, h⟩
      · rw [h]
        rcases le_total c (g i) with hc | hc
        · exact Or.inr ⟨i, Or.inl rfl, max_eq_right hc⟩
        · exact Or.inl (max_eq_left hc)
      · exact Or.inr ⟨j, Or.inr hj, h⟩

end Folds

/-! ## `GetPrecision` -/

section Precision

variable {k : ℕ} {F : ttc.LRAFormula d k}

/-- **The largest ratio, as the program folds it, is `getPrecisionRatio`.** -/
theorem foldl_ratio_eq (D : ttc.Decomposition F) (hm : 0 < D.componentCount) (η : ℝ) :
    (List.ofFn fun i => D.component i).foldl
        (fun a P => max a (ttc.latticeRadiusRequirement D η / P.inradius)) 1 =
      ttc.getPrecisionRatio D η := by
  classical
  set g : ttc.PolytopeData d → ℝ := fun P => ttc.latticeRadiusRequirement D η / P.inradius
  obtain ⟨h1, h2, h3⟩ := foldl_max_spec g (List.ofFn fun i => D.component i) 1
  set lhs := (List.ofFn fun i => D.component i).foldl (fun a P => max a (g P)) 1
  have hsup : ∀ i, Real.toNNReal (g (D.component i)) ≤
      Finset.univ.sup fun i => Real.toNNReal (g (D.component i)) :=
    fun i => Finset.le_sup (f := fun i => Real.toNNReal (g (D.component i))) (Finset.mem_univ i)
  have hne : (Finset.univ : Finset (Fin D.componentCount)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup _ hne fun i => Real.toNNReal (g (D.component i))
  unfold ttc.getPrecisionRatio
  show lhs = max 1 ((Finset.univ.sup fun i => Real.toNNReal (g (D.component i)) : NNReal) : ℝ)
  apply le_antisymm
  · rcases h3 with h | ⟨P, hP, h⟩
    · rw [h]; exact le_max_left _ _
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hP
      rw [h]
      refine le_max_of_le_right ((Real.le_coe_toNNReal _).trans ?_)
      exact_mod_cast hsup i
  · refine max_le h1 ?_
    rw [hj]
    rcases le_total (g (D.component j)) 0 with hg | hg
    · rw [Real.toNNReal_of_nonpos hg]
      exact (show ((0 : NNReal) : ℝ) ≤ 1 by norm_num).trans h1
    · rw [Real.coe_toNNReal _ hg]
      exact h2 _ (List.mem_ofFn.mpr ⟨j, rfl⟩)

end Precision


/-! ## Helpers' values -/

section HelperVals

theorem get_pow10 (b : Num ℕ) : (pow10 b).val.get = (10 : ℝ) ^ b.get := by
  simp only [pow10, Charged.val_bind, A.cast, A.lit, A.log, A.mul, A.exp, Num.get_exp, Num.get_mul,
    Num.get_log, Num.get_cast, Num.get_lit]
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

theorem get_latticeRadiusProg (m dim tot eta : Num ℝ) :
    (latticeRadiusProg m dim tot eta).val.get =
      64 * m.get * dim.get / eta.get * Real.sqrt (Real.log (4 * tot.get / eta.get)) := by
  simp [latticeRadiusProg, Charged.val_bind, A.mulLit, A.mul, A.div, A.log, A.sqrt, A.lit,
    Num.get_mul, Num.get_div, Num.get_log, Num.get_sqrt, Num.get_lit]

theorem get_getPrecision (required : Num ℝ) (Ls : List (Loaded d)) :
    (getPrecision required Ls).val.get =
      Nat.ceil (Real.log (Ls.foldl (fun a (L : Loaded d) => max a (required.get / L.inradius.get)) 1) /
        Real.log 10) := by
  have h := val_maxFold required Ls (A.lit (1 : ℝ)).val
  simp only [getPrecision, Charged.val_bind]
  rw [show (A.lit (1 : ℝ)).val.get = 1 by simp [A.lit]] at h
  simp only [A.log, A.lit, A.div, A.ceil, Num.get_ceil, Num.get_div, Num.get_log, Num.get_lit]
  simp only [A.div, A.lit] at h
  rw [h]

end HelperVals


/-! ## Values of the primitives -/

section PrimVals

theorem getA_lit {α : Type} (a : α) : (A.lit a).val.get = a := by simp [A.lit]
theorem getA_add {α : Type} [Add α] (x y : Num α) : (A.add x y).val.get = x.get + y.get := by
  simp [A.add]
theorem getA_sub {α : Type} [Sub α] (x y : Num α) : (A.sub x y).val.get = x.get - y.get := by
  simp [A.sub]
theorem getA_mul {α : Type} [Mul α] (x y : Num α) : (A.mul x y).val.get = x.get * y.get := by
  simp [A.mul]
theorem getA_div {α : Type} [Div α] (x y : Num α) : (A.div x y).val.get = x.get / y.get := by
  simp [A.div]
theorem getA_max {α : Type} [Max α] (x y : Num α) : (A.max x y).val.get = max x.get y.get := by
  simp [A.max]
theorem getA_cast (k : Num ℕ) : (A.cast k).val.get = (k.get : ℝ) := by simp [A.cast]
theorem getA_log (x : Num ℝ) : (A.log x).val.get = Real.log x.get := by simp [A.log]
theorem getA_mulLit (c : ℝ) (x : Num ℝ) : (A.mulLit c x).val.get = c * x.get := by
  simp [A.mulLit, Charged.val_bind, A.lit, A.mul]
theorem getA_divLit (x : Num ℝ) (c : ℝ) : (A.divLit x c).val.get = x.get / c := by
  simp [A.divLit, Charged.val_bind, A.lit, A.div]
theorem getA_litDiv (c : ℝ) (x : Num ℝ) : (A.litDiv c x).val.get = c / x.get := by
  simp [A.litDiv, Charged.val_bind, A.lit, A.div]

end PrimVals

/-! ## The parameters -/

section ParamsVal

variable {k : ℕ} {F : ttc.LRAFormula d k}

theorem getPrecision_eq (D : ttc.Decomposition F) (p : ttc.ApproxParams)
    (hm : 0 < D.componentCount) (m dim tot eta : Num ℝ) (hmv : m.get = D.componentCount)
    (hd : dim.get = d) (ht : tot.get = D.totalFacets) (he : eta.get = p.precisionEta) :
    (getPrecision (latticeRadiusProg m dim tot eta).val
      ((List.ofFn D.component).map loaded)).val.get = ttc.GetPrecision D p.precisionEta := by
  rw [get_getPrecision, get_latticeRadiusProg, hmv, hd, ht, he, List.foldl_map]
  have h := foldl_ratio_eq D hm p.precisionEta
  unfold ttc.latticeRadiusRequirement at h
  rw [ttc.GetPrecision, Real.logb, ← h]
  rfl

theorem paramsProg_val (D : ttc.Decomposition F) (p : ttc.ApproxParams)
    (hm : 0 < D.componentCount) :
    let cs := ttc.SealedRun.componentsOf D
    let K := (paramsProg cs (cs.map fun c => (load c).val) p.epsilon p.delta).val
    K.dimN.get = d ∧ K.dim.get = d ∧ K.epsPrime.get = p.ε' ∧
      K.deltaPrime.get = p.δ' D.componentCount ∧ K.thresh.get = p.Thresh D.componentCount ∧
      K.scale.get = ttc.decimalScale (ttc.GetPrecision D p.precisionEta) ∧
      K.scaleN.get = 10 ^ (ttc.GetPrecision D p.precisionEta * d) := by
  intro cs K
  obtain ⟨hc1, hc2⟩ := val_countFold (d := d) (A.lit (1 : ℕ)).val (by simp [A.lit]) cs
    ((A.lit (0 : ℕ)).val, (A.lit (0 : ℕ)).val)
  simp only [A.lit, Num.get_lit, zero_add] at hc1 hc2
  have hlen : cs.length = D.componentCount := List.length_ofFn
  have hsum : (cs.map (·.facetCount)).sum = D.totalFacets := by
    simp [cs, ttc.SealedRun.componentsOf, ttc.SealedRun.componentInput, List.map_ofFn,
      List.sum_ofFn, ttc.Decomposition.totalFacets, Function.comp_def]
  have hLs : cs.map (fun c => (load c).val) = (List.ofFn D.component).map loaded := by
    simp [cs, ttc.SealedRun.componentsOf, List.map_ofFn, Function.comp_def,
      val_load_componentInput]
  simp only [K, paramsProg, Charged.val_bind, val_Apure]
  rw [hLs]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [A.lit]
  · simp [A.cast, A.lit]
  · simp [A.divLit, A.div, A.lit, ttc.ApproxParams.ε']
  · simp [A.div, A.mulLit, A.mul, A.cast, A.lit, hc1, hlen, ttc.ApproxParams.δ']
  · simp only [getA_lit, getA_add, getA_sub, getA_mul, getA_div, getA_max, getA_cast, getA_log,
      getA_mulLit, getA_divLit, getA_litDiv, get_Apow]
    obtain ⟨hc1', -⟩ := val_countFold (d := d) (A.lit (1 : ℕ)).val (by simp [A.lit]) cs
      ((A.lit (0 : ℕ)).val, (A.lit (0 : ℕ)).val)
    simp only [hc1', getA_lit, zero_add, hlen]
    simp [ttc.ApproxParams.Thresh, ttc.ApproxParams.ε']
  · rw [get_pow10, getPrecision_eq D p hm _ _ _ _ ?_ ?_ ?_ ?_]
    · rfl
    · simp [A.cast, hc1, hlen, A.lit]
    · simp [A.cast, A.lit]
    · simp [A.cast, hc2, hsum, A.lit]
    · simp [A.divLit, A.div, A.lit, ttc.ApproxParams.precisionEta]
  · rw [get_pow10]
    simp only [A.mul, Num.get_mul, A.lit, Num.get_lit]
    rw [getPrecision_eq D p hm _ _ _ _ ?_ ?_ ?_ ?_]
    · simp [A.cast, hc1, hlen, A.lit]
    · simp [A.cast, A.lit]
    · simp [A.cast, hc2, hsum, A.lit]
    · simp [A.divLit, A.div, A.lit, ttc.ApproxParams.precisionEta]

end ParamsVal

end ttc.Tape
