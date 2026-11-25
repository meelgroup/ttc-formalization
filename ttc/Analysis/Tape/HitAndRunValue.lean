/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.ValueLaw
import ttc.Analysis.HitAndRunStep

/-!
# What the sealed Hit-and-Run step computes

The sealed step (`Program.hitAndRunStep`) computes the same point as arlib's Hit-and-Run
move (`HalfspacePresentation.move`): the chord scan finds arlib's endpoints
(`chord_val`), `normalize g` is `g/‖g‖` (`normalize_val`), and on a bounded body the move
is the same (`stepValue_eq`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ArlibCommunity.Foundations.MarkovChainTheory.PolytopeChord
open ttc.HitAndRunProg (arlibNormals coeff_eq slack_eq iSup_fin_succ iInf_fin_succ)

variable {d : ℕ}

/-! ## Held points as points -/

/-- A held point, as a point of Euclidean space. -/
def toPt (x : NumPoint d) : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 fun i => (x i).get

/-- A point, held. -/
def ofPt (y : EuclideanSpace ℝ (Fin d)) : NumPoint d := (sealVector d (WithLp.ofLp y)).val

@[simp] theorem toPt_apply (x : NumPoint d) (i : Fin d) : toPt x i = (x i).get := rfl

@[simp] theorem toPt_ofPt (y : EuclideanSpace ℝ (Fin d)) : toPt (ofPt y) = y := by
  ext i
  simp [toPt, ofPt, get_sealVector]

@[simp] theorem ofPt_toPt (x : NumPoint d) : ofPt (toPt x) = x := by
  funext i
  exact Num.ext (by simp [toPt, ofPt, get_sealVector])

theorem measurable_toPt : Measurable (toPt (d := d)) :=
  (PiLp.continuous_toLp 2 _).measurable.comp
    (measurable_pi_iff.mpr fun i => Num.measurable_get.comp (measurable_pi_apply i))

theorem measurable_ofPt : Measurable (ofPt (d := d)) := Tree.measurable_sealVector

/-- The facet normals, as real vectors. -/
def getM {r : ℕ} (a : Fin r → NumPoint d) : Fin r → Fin d → ℝ := fun j i => (a j i).get

theorem getM_row {r : ℕ} (a : Fin r → NumPoint d) (j : Fin r) :
    getM a j = fun i => (a j i).get := rfl

/-- The offsets, as real numbers. -/
def getV {r : ℕ} (β' : Fin r → Num ℝ) : Fin r → ℝ := fun j => (β' j).get

/-! ## Arithmetic -/

@[simp] theorem val_Apure {α : Type} (a : α) : (A.pure a).val = a := rfl

@[simp] theorem val_cpure {α : Type} (a : α) : (Charged.pure a : Prog α).val = a := rfl

theorem val_forEach {α : Type} : ∀ {k : ℕ} (f : Fin k → Prog α),
    (A.forEach f).val = fun i => (f i).val
  | 0, f => funext fun i => i.elim0
  | k + 1, f => by
      funext i
      rw [A.forEach]
      simp only [Charged.val_bind, val_Apure, val_forEach]
      refine Fin.cases rfl (fun j => ?_) i
      simp

theorem get_dot : ∀ (k : ℕ) (a x : NumPoint k),
    (A.dot k a x).val.get = dotProduct (fun i => (a i).get) (fun i => (x i).get)
  | 0, a, x => by simp [A.dot, A.lit, dotProduct]
  | 1, a, x => by simp [A.dot, A.mul, dotProduct]
  | k + 2, a, x => by
      simp only [A.dot, Charged.val_bind, A.add, A.mul, Num.get_add, Num.get_mul, get_dot (k + 1)]
      conv_rhs => rw [dotProduct, Fin.sum_univ_succ]
      rfl

theorem val_Alt (x y : Num ℝ) : (A.lt x y).val = decide (x.get < y.get) := by
  simp only [A.lt, Charged.val_bind, Num.val_le, val_Apure]
  by_cases h : x.get < y.get
  · simp [h, not_le.mpr h]
  · simp [h, not_lt.mp h]

theorem get_norm (x : NumPoint d) : (A.norm x).val.get = ‖toPt x‖ := by
  simp only [A.norm, A.normSq, A.sqrt, Charged.val_bind, Num.get_sqrt, get_dot]
  rw [EuclideanSpace.norm_eq]
  simp [dotProduct, sq]

/-- **`normalize g` is `g/‖g‖`** (and `0` at `g = 0`). -/
theorem normalize_val (g : NumPoint d) : toPt (normalize g).val = ‖toPt g‖⁻¹ • toPt g := by
  ext i
  simp only [Program.normalize, A.smul, Charged.val_bind, val_forEach, A.mul, A.div, A.lit,
    Num.get_mul, Num.get_div, Num.get_lit, get_norm, toPt_apply, PiLp.smul_apply,
    smul_eq_mul, one_div]

/-! ## The chord -/

/-- A lower endpoint, `−∞` when there is none. -/
def optLo : Option (Num ℝ) → EReal
  | none => ⊥
  | some q => (q.get : EReal)

/-- An upper endpoint, `+∞` when there is none. -/
def optHi : Option (Num ℝ) → EReal
  | none => ⊤
  | some q => (q.get : EReal)

theorem optLo_maxEnd (o o' : Option (Num ℝ)) : optLo (maxEnd o o').val = max (optLo o) (optLo o') := by
  rcases o with _ | x <;> rcases o' with _ | y <;>
    simp [maxEnd, optLo, A.pure, A.max, Num.get_max]
  rcases le_total x.get y.get with h | h <;> simp [h, EReal.coe_le_coe_iff]

theorem optHi_minEnd (o o' : Option (Num ℝ)) : optHi (minEnd o o').val = min (optHi o) (optHi o') := by
  rcases o with _ | x <;> rcases o' with _ | y <;>
    simp [minEnd, optHi, A.pure, A.min, Num.get_min]
  rcases le_total x.get y.get with h | h <;> simp [h, EReal.coe_le_coe_iff]

open Classical in
theorem facetEndpoints_val {r : ℕ} (a : Fin r → NumPoint d) (β' : Fin r → Num ℝ)
    (x θ : NumPoint d) (j : Fin r) :
    optLo (facetEndpoints (a j) (β' j) x θ).val.1 =
        lowerCandidate (arlibNormals (getM a)) (getV β') (toPt x) (toPt θ) j ∧
      optHi (facetEndpoints (a j) (β' j) x θ).val.2 =
        upperCandidate (arlibNormals (getM a)) (getV β') (toPt x) (toPt θ) j := by
  have hc := coeff_eq (getM a) (fun i => (θ i).get) j
  have hs := slack_eq (getM a) (getV β') (fun i => (x i).get) j
  simp only [getM_row] at hc hs
  simp only [facetEndpoints, Charged.val_bind, val_Apure, val_Alt, A.lit,
    Num.get_lit, A.sub, A.div, Num.get_sub, Num.get_div, get_dot]
  refine ⟨?_, ?_⟩
  · simp only [lowerCandidate, ratio, toPt, hc, hs]
    split_ifs <;> simp_all [optLo, getV, get_dot]
  · simp only [upperCandidate, ratio, toPt, hc, hs]
    split_ifs <;> simp_all [optHi, getV, get_dot]

/-- **The chord scan finds arlib's endpoints.** -/
theorem chord_val : ∀ (r : ℕ) (a : Fin r → NumPoint d) (β' : Fin r → Num ℝ) (x θ : NumPoint d),
    optLo (chord r a β' x θ).val.1 = lowerE (arlibNormals (getM a)) (getV β') (toPt x) (toPt θ) ∧
      optHi (chord r a β' x θ).val.2 = upperE (arlibNormals (getM a)) (getV β') (toPt x) (toPt θ)
  | 0, a, β', x, θ => by simp [chord, A.pure, optLo, optHi, lowerE, upperE]
  | r + 1, a, β', x, θ => by
      obtain ⟨h1, h2⟩ := facetEndpoints_val a β' x θ 0
      obtain ⟨h3, h4⟩ := chord_val r (Fin.tail a) (Fin.tail β') x θ
      simp only [chord, Charged.val_bind, val_cpure, val_Apure, optLo_maxEnd, optHi_minEnd]
      rw [h1, h2, h3, h4]
      simp only [lowerE, upperE, iSup_fin_succ (lowerCandidate _ _ _ _),
        iInf_fin_succ (upperCandidate _ _ _ _)]
      exact ⟨rfl, rfl⟩

end ttc.Tape

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ArlibCommunity.Foundations.MarkovChainTheory.PolytopeChord
open ttc.HitAndRunProg (arlibNormals)

variable {d : ℕ}

/-! ## The step -/

/-- The polytope with held facets `a` and offsets `β'`. -/
def presOf (r : ℕ) (a : Fin r → NumPoint d) (β' : Fin r → Num ℝ) : HalfspacePresentation d :=
  ⟨r, getM a, getV β'⟩

/-- The body of the held polytope. -/
abbrev bodyOf (r : ℕ) (a : Fin r → NumPoint d) (β' : Fin r → Num ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  ArlibCommunity.Foundations.Convex.Polytope.body (arlibNormals (getM a)) (getV β')

@[simp] theorem toPt_sealVector (g : EuclideanSpace ℝ (Fin d)) :
    toPt (sealVector d (WithLp.ofLp g)).val = g := toPt_ofPt g

theorem lowerE_zero {r : ℕ} (A : Fin r → EuclideanSpace ℝ (Fin d)) (b : Fin r → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : lowerE A b x 0 = ⊥ := by
  simp [lowerE, lowerCandidate, coeff]

theorem upperE_zero {r : ℕ} (A : Fin r → EuclideanSpace ℝ (Fin d)) (b : Fin r → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : upperE A b x 0 = ⊤ := by
  simp [upperE, upperCandidate, coeff]

theorem lowerE_ne_bot {r : ℕ} {A : Fin r → EuclideanSpace ℝ (Fin d)} {b : Fin r → ℝ}
    {x θ : EuclideanSpace ℝ (Fin d)} (h : ∃ i, coeff A θ i < 0) : lowerE A b x θ ≠ ⊥ := by
  obtain ⟨i, hi⟩ := h
  refine ne_bot_of_le_ne_bot ?_ (le_iSup (lowerCandidate A b x θ) i)
  simp [lowerCandidate, hi]

theorem upperE_ne_top {r : ℕ} {A : Fin r → EuclideanSpace ℝ (Fin d)} {b : Fin r → ℝ}
    {x θ : EuclideanSpace ℝ (Fin d)} (h : ∃ i, 0 < coeff A θ i) : upperE A b x θ ≠ ⊤ := by
  obtain ⟨i, hi⟩ := h
  refine ne_top_of_le_ne_top ?_ (iInf_le (upperCandidate A b x θ) i)
  simp [upperCandidate, hi]

/-- On a bounded body, a chord that misses an endpoint is degenerate. -/
theorem not_lt_of_missing {r : ℕ} {a : Fin r → NumPoint d} {β' : Fin r → Num ℝ}
    (hK : Bornology.IsBounded (bodyOf r a β')) (hne : (bodyOf r a β').Nonempty)
    (x θ : EuclideanSpace ℝ (Fin d)) (e : Option (Num ℝ) × Option (Num ℝ))
    (h1 : optLo e.1 = lowerE (arlibNormals (getM a)) (getV β') x θ)
    (h2 : optHi e.2 = upperE (arlibNormals (getM a)) (getV β') x θ)
    (hmiss : e.1 = none ∨ e.2 = none) :
    ¬ lower (arlibNormals (getM a)) (getV β') x θ < upper (arlibNormals (getM a)) (getV β') x θ := by
  by_cases hθ : θ = 0
  · subst hθ
    simp [lower, upper, lowerE_zero, upperE_zero]
  · exfalso
    rcases hmiss with h | h
    · rw [h] at h1
      exact lowerE_ne_bot (exists_neg_coeff_of_isBounded hK hθ hne) h1.symm
    · rw [h] at h2
      exact upperE_ne_top (exists_pos_coeff_of_isBounded hK hθ hne) h2.symm

open ttc.Tape.Tree in
/-- **What one step computes**, on a bounded body: it stays if the tape's coin says so, and
otherwise makes arlib's move with the tape's Gaussian vector and uniform number. -/
theorem exec_hitAndRunStepT (r : ℕ) (a : Fin r → NumPoint d) (β' : Fin r → Num ℝ)
    (hK : Bornology.IsBounded (bodyOf r a β')) (hne : (bodyOf r a β').Nonempty)
    (x : NumPoint d) (b : ℕ) (t : Tape d) :
    Option.map toPt (exec (hitAndRunStepT r a β' x) b t).1 =
      some (if (t 0).1 then toPt x else (presOf r a β').move (toPt x) (t 1).2.1 (t 2).2.2) := by
  simp only [hitAndRunStepT, coinT, exec, Tree.bind]
  cases (t 0).1
  · simp only [Bool.false_eq_true, ite_false, gaussianT, exec, compute, Tree.bind]
    have e1 : t.tail 0 = t 1 := rfl
    simp only [e1]
    have hθ := normalize_val (sealVector d (WithLp.ofLp (t 1).2.1)).val
    rw [toPt_sealVector] at hθ
    obtain ⟨h1, h2⟩ := chord_val r a β' x (normalize (sealVector d (WithLp.ofLp (t 1).2.1)).val).val
    rw [hθ] at h1 h2
    generalize (chord r a β' x (normalize (sealVector d (WithLp.ofLp (t 1).2.1)).val).val).val = E at h1 h2 ⊢
    have hmove : (presOf r a β').move (toPt x) (t 1).2.1 (t 2).2.2 = if lower (arlibNormals (getM a)) (getV β') (toPt x) (‖(t 1).2.1‖⁻¹ • (t 1).2.1) < upper (arlibNormals (getM a)) (getV β') (toPt x) (‖(t 1).2.1‖⁻¹ • (t 1).2.1) then toPt x + (lower (arlibNormals (getM a)) (getV β') (toPt x) (‖(t 1).2.1‖⁻¹ • (t 1).2.1) + (t 2).2.2 * (upper (arlibNormals (getM a)) (getV β') (toPt x) (‖(t 1).2.1‖⁻¹ • (t 1).2.1) - lower (arlibNormals (getM a)) (getV β') (toPt x) (‖(t 1).2.1‖⁻¹ • (t 1).2.1))) • (‖(t 1).2.1‖⁻¹ • (t 1).2.1) else toPt x := rfl
    rw [hmove]
    rcases E with ⟨_ | lo, _ | hi⟩
    · rw [ite_cond_eq_false _ _ (eq_false (not_lt_of_missing hK hne _ _ _ h1 h2 (Or.inl rfl)))]; rfl
    · rw [ite_cond_eq_false _ _ (eq_false (not_lt_of_missing hK hne _ _ _ h1 h2 (Or.inl rfl)))]; rfl
    · rw [ite_cond_eq_false _ _ (eq_false (not_lt_of_missing hK hne _ _ _ h1 h2 (Or.inr rfl)))]; rfl
    · simp only [optLo, optHi] at h1 h2
      have hlo : lower (arlibNormals (getM a)) (getV β') (toPt x) (‖(t 1).2.1‖⁻¹ • (t 1).2.1) = lo.get := by
        simp [lower, ← h1]
      have hhi : upper (arlibNormals (getM a)) (getV β') (toPt x) (‖(t 1).2.1‖⁻¹ • (t 1).2.1) = hi.get := by
        simp [upper, ← h2]
      rw [hlo, hhi]
      simp only [Option.elim, exec, val_Alt]
      by_cases hlt : lo.get < hi.get
      · simp only [hlt, decide_true, ite_true, unitT, exec, Tree.bind]
        have e2 : t.tail.tail 0 = t 2 := rfl
        simp only [e2, Option.map_some]
        congr 1
        ext i
        have hθi := congrArg (fun v : EuclideanSpace ℝ (Fin d) => v i) hθ
        simp only [toPt_apply, PiLp.smul_apply, smul_eq_mul] at hθi
        simp [val_forEach, Num.get_add, Num.get_mul, Num.get_sub, hθi, A.add, A.mul, A.sub]
      · simp only [hlt, decide_false, Bool.false_eq_true, ite_false]; rfl
  · rfl

end ttc.Tape
