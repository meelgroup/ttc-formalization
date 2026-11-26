/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.Corr

/-!
# One step, part one: the deletion pass and the rate check

The sealed step removes the stored copies lying in the component, then, if `t p ≥ Thresh`,
keeps each copy with probability `2^{-k}` for `k = ⌈log₂(t p / Thresh)⌉` and divides `p` by
`2^k`.  The old step does the same with `k` fair rounds of its coin stream
(`ttcPseudocode.rateCheck` after `TTCState.removeComponent`).  Read through the state
views, the two have the same law.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set ProbabilityTheory

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ttc.Tape.Tree
open ttc (TTCState samplesAfter survives fairCoinStreamLaw fairCoinLaw)

variable {d : ℕ}

/-! ## Survivors as a selection -/

section Survivors

theorem labelSurvives_iff (coins : ℕ × ℕ → Bool) (k ℓ : ℕ) :
    ttc.labelSurvives k (fun r => coins (r, ℓ)) = true ↔ survives coins k ℓ := by
  classical
  unfold ttc.labelSurvives survives
  split_ifs with h
  · simpa using h
  · simpa using h

variable (Ls : List (ttc.SampleCopy d))

theorem samplesAfter_eq_keepSet (X : Finset (ttc.SampleCopy d)) (hX : Ls.toFinset = X)
    (coins : ℕ × ℕ → Bool) (k : ℕ) :
    samplesAfter coins k X = keepSet Ls (fun i => ttc.labelSurvives k (fun r => coins (r, (Ls.get i).1))) := by
  classical
  ext copy
  simp only [samplesAfter, Finset.mem_filter, keepSet, List.mem_toFinset, mem_selectBy,
    labelSurvives_iff, ← hX]
  constructor
  · rintro ⟨hc, h0⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hc
    exact ⟨i, hi, by rw [hi]; exact h0⟩
  · rintro ⟨i, hi, h0⟩
    exact ⟨List.mem_iff_get.mpr ⟨i, hi⟩, by rw [← hi]; exact h0⟩

/-- **Distinct copies survive `k` fair rounds independently, each with probability `2^{-k}`.** -/
theorem survivors_law (hlab : (Ls.map (·.1)).Nodup) (k : ℕ) :
    fairCoinStreamLaw.map (fun coins => fun i : Fin Ls.length =>
      ttc.labelSurvives k (fun r => coins (r, (Ls.get i).1))) =
      Measure.pi fun _ : Fin Ls.length => bernoulliMeasure true false (ttc.survivalProbability k) := by
  have hP : ∀ _ : ℕ, IsProbabilityMeasure
      ((Measure.infinitePi fun _ : ℕ => fairCoinLaw).map (ttc.labelSurvives k)) := by
    intro _
    rw [ttc.labelStreamLaw_survivalProbability]
    infer_instance
  have hinj : Function.Injective fun i : Fin Ls.length => (Ls.get i).1 := by
    intro i j h
    have hinj := List.nodup_iff_injective_get.mp hlab
    have := hinj (a₁ := ⟨i, by simp⟩) (a₂ := ⟨j, by simp⟩) (by simpa using h)
    exact Fin.ext (by simpa using congrArg Fin.val this)
  have hvec : Measurable fun coins : ℕ × ℕ → Bool =>
      fun label => ttc.labelSurvives k (fun r => coins (r, label)) :=
    Measurable.of_eval fun label => (ttc.measurable_labelSurvives k).comp
      (Measurable.of_eval fun r => measurable_pi_apply (r, label))
  have hfun : (fun coins : ℕ × ℕ → Bool => fun i : Fin Ls.length =>
      ttc.labelSurvives k (fun r => coins (r, (Ls.get i).1))) =
      (fun v : ℕ → Bool => fun i : Fin Ls.length => v (Ls.get i).1) ∘
        fun coins label => ttc.labelSurvives k (fun r => coins (r, label)) := by
    funext coins i
    rfl
  rw [hfun, ← Measure.map_map (measurable_pi_iff.mpr fun i => measurable_pi_apply _) hvec,
    ttc.fairCoinStreamLaw_survivalVector k, Measure.map_infinitePi_infinitePi_of_inj hinj,
    Measure.infinitePi_eq_pi]
  simp only [ttc.labelStreamLaw_survivalProbability]

end Survivors


/-! ## The deletion pass -/

section Deletion

/-- **The filter with answers that read no tape**: the copies kept are those whose answer
is `true`. -/
theorem exec_foldlM_filterStep_det {keep : (Fin d → Num ℤ) → Tree d Bool}
    {κ : (Fin d → Num ℤ) → Bool}
    (hkeep : ∀ x b t, ∃ j, exec (keep x) b t = (some (κ x), j, b, t))
    (one : Num ℕ) (hone : one.get = 1) :
    ∀ (X : List (Fin d → Num ℤ)) (acc : List (Fin d → Num ℤ) × Num ℕ) (b : ℕ) (t : Tape d),
      Option.map (fun r : List (Fin d → Num ℤ) × Num ℕ => (r.1, r.2.get))
          (exec (X.foldlM (filterStep keep one) acc) b t).1 =
        some (acc.1 ++ X.filter κ, acc.2.get + (X.filter κ).length)
  | [], acc, b, t => by simp [exec]
  | x :: xs, acc, b, t => by
      rw [List.foldlM_cons]
      show Option.map _ (exec ((filterStep keep one acc x).bind _) b t).1 = _
      rw [exec_bind]
      have hstep : exec (filterStep keep one acc x) b t =
          ((some (if κ x then (acc.1 ++ [x], (A.add acc.2 one).val) else acc)),
            (exec (filterStep keep one acc x) b t).2.1, b, t) := by
        obtain ⟨j', hj'⟩ := hkeep (A.cell x).val b t
        simp only [filterStep, compute, Tree.bind, exec]
        rw [exec_bind, hj']
        have hx : (A.cell x).val = x := rfl
        rw [hx]
        cases κ x <;> simp [exec, A.push, ttc.Model.Operations.push]
      rw [hstep]
      simp only
      rw [exec_foldlM_filterStep_det hkeep one hone xs]
      cases h : κ x
      · simp [List.filter_cons, h]
      · simp only [List.filter_cons, h, ite_true, List.length_cons, A.add, Num.get_add, hone,
          List.append_assoc, List.singleton_append]
        congr 2
        omega

theorem filter_map_rel {α β γ : Type} (f : α → γ) (g : β → γ) (κ₁ : α → Bool) (κ₂ : β → Bool) :
    ∀ (l₁ : List α) (l₂ : List β), l₁.map f = l₂.map g →
      (∀ x ∈ l₁, ∀ y ∈ l₂, f x = g y → κ₁ x = κ₂ y) →
      (l₁.filter κ₁).map f = (l₂.filter κ₂).map g
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: l₁, y :: l₂, h, hk => by
      simp only [List.map_cons, List.cons.injEq] at h
      have ih := filter_map_rel f g κ₁ κ₂ l₁ l₂ h.2
        (fun x' hx' y' hy' => hk x' (List.mem_cons_of_mem _ hx') y' (List.mem_cons_of_mem _ hy'))
      have hxy := hk x (List.mem_cons_self ..) y (List.mem_cons_self ..) h.1
      simp only [List.filter_cons, hxy]
      split_ifs
      · simp [h.1, ih]
      · exact ih

end Deletion


section Member

/-- **The deletion test**: the sealed membership test of a stored copy's integer point in
`10^b · P` is the old membership test of its decoded point in `P`. -/
theorem latticeMember_copy (P : ttc.PolytopeData d) (b : ℕ) (scale : Num ℝ)
    (hs : scale.get = ttc.decimalScale b) (c : ttc.SampleCopy d) (hc : c.2.1 = b) :
    (latticeMember (loaded P) (scaledOffsets (loaded P) scale).val (sealZ c.2.2)).val =
      (P.presentation.memberProg c.2.toPoint).value := by
  have hpos : 0 < ttc.decimalScale b := by unfold ttc.decimalScale; positivity
  rw [Bool.eq_iff_iff]
  change accepts (loaded P) (scaledOffsets (loaded P) scale).val c.2.2 = true ↔ _
  rw [accepts_iff P b scale hs, ttc.acceptedIntegers, Set.mem_setOf_eq,
    ttc.HalfspacePresentation.memberProg, ttc.HalfspacePresentation.memberProg,
    ttc.Counted.allFacets_value, ttc.Counted.allFacets_value]
  simp only [ttc.PolytopeData.scaledPresentation, ttc.PolytopeData.scaledOffsetsProg,
    ttc.Counted.forEach, ttc.Counted.mul, ttc.LatticePoint.toPoint, hc]
  refine forall_congr' fun j => ?_
  have hdot : dotProduct (P.presentation.normal j) c.2.toPoint =
      dotProduct (P.presentation.normal j) (fun i => (c.2.2 i : ℝ)) / ttc.decimalScale b := by
    simp only [dotProduct, ttc.LatticePoint.toPoint, hc, ttc.decimalScale, Finset.sum_div,
      mul_div_assoc]
  rw [hdot, div_le_iff₀ hpos, mul_comm]

end Member

end ttc.Tape
