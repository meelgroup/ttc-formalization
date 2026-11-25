/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.ThinLaw
import ttc.Analysis.ChargedCV18.Theorem

/-!
# The charged CV18 program on the tape

`ttc.ChargedCV18.cv18Program` (the program the CV18 accuracy theorem is about) draws its
random numbers from their laws: standard Gaussian vectors and uniform numbers in `[0, 1]`.
Run on the random tape, it reads each from the next round instead (`cexec`): a Gaussian
vector from a round's Gaussian component, a uniform number from its uniform component.  A
membership query spends one call of a budget (`⊤` for none) and stops the run when it is
exhausted.

* `cexec_bind`: running a sequence is running its parts;
* `cexec_withQueryCap`: a query cap inside the program is the budget of `cexec`;
* `tapeLaw_map_cexec`: on the random tape, a program that draws only Gaussian vectors and
  uniform numbers (`ChargedStd`) has its output law `runEstimate`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace ttc.Tape

open ttc.Model.Operations
open ttc.SealedRun (roundLaw tapeLaw)
open ttc.ChargedCV18 (ChargedProgram)

variable {d : ℕ} {α β : Type}

/-! ## Running on the tape -/

/-- **A charged program on the tape**, with `b` membership calls left (`⊤`: no cap): its
result (`none` if a call found the budget exhausted), the calls left, and the tape left. -/
def cexec (O : EuclideanSpace ℝ (Fin d) → Bool) :
    ChargedProgram d α → ℕ∞ → Tape d → Option α × ℕ∞ × Tape d
  | .pure a, b, t => (some a, b, t)
  | .query x k, b, t => if b = 0 then (none, 0, t) else cexec O (k (O x)) (b - 1) t
  | .randomNat _ k, b, t => cexec O (k 0) b t
  | .randomPoint _ _ k, b, t => cexec O (k (t 0).2.1) b t.tail
  | .randomReal _ _ k, b, t => cexec O (k (t 0).2.2) b t.tail
  | .tick _ k, b, t => cexec O k b t

variable (O : EuclideanSpace ℝ (Fin d) → Bool)

theorem enat_top_sub_one : (⊤ : ℕ∞) - 1 = ⊤ := rfl

theorem enat_succ_sub_one (c : ℕ) : ((c + 1 : ℕ) : ℕ∞) - 1 = c := by
  rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, ← ENat.natCast_sub]
  simp

theorem cexec_bind (P : ChargedProgram d α) (f : α → ChargedProgram d β) (b : ℕ∞) (t : Tape d) :
    cexec O (P.bind f) b t =
      match cexec O P b t with
      | (none, b', t') => (none, b', t')
      | (some a, b', t') => cexec O (f a) b' t' := by
  induction P generalizing b t with
  | pure a => rfl
  | query x k ih =>
      simp only [ChargedProgram.bind, cexec]
      split_ifs
      · rfl
      · exact ih _ _ _
  | randomNat law k ih => exact ih _ _ _
  | randomPoint law h k ih => exact ih _ _ _
  | randomReal law h k ih => exact ih _ _ _
  | tick c k ih => exact ih _ _

/-- **A query cap inside the program is a budget**: with no outer cap, the capped program
returns the run with the cap as its budget. -/
theorem cexec_withQueryCap (P : ChargedProgram d α) (c : ℕ) (t : Tape d) :
    cexec O (P.withQueryCap c) ⊤ t = (some (cexec O P c t).1, ⊤, (cexec O P c t).2.2) := by
  induction P generalizing c t with
  | pure a => rfl
  | query x k ih =>
      cases c with
      | zero => rfl
      | succ c =>
          have h1 : ((c + 1 : ℕ) : ℕ∞) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero c
          simp only [ChargedProgram.withQueryCap, cexec, ENat.top_ne_zero, ite_false,
            enat_top_sub_one, h1, enat_succ_sub_one]
          exact ih _ c t
  | randomNat law k ih => exact ih _ c t
  | randomPoint law h k ih => exact ih _ c t.tail
  | randomReal law h k ih => exact ih _ c t.tail
  | tick ops k ih => exact ih c t

/-! ## Programs the tape can run -/

/-- A program whose random draws are standard Gaussian vectors and uniform numbers in
`[0, 1]`, the draws the tape provides. -/
def ChargedStd : ChargedProgram d α → Prop
  | .pure _ => True
  | .query _ k => ∀ a, ChargedStd (k a)
  | .randomNat _ _ => False
  | .randomPoint law _ k => law = stdGaussian (EuclideanSpace ℝ (Fin d)) ∧ ∀ g, ChargedStd (k g)
  | .randomReal law _ k => law = volume.restrict (Icc (0 : ℝ) 1) ∧ ∀ v, ChargedStd (k v)
  | .tick _ k => ChargedStd k

theorem ChargedStd.bind {P : ChargedProgram d α} {f : α → ChargedProgram d β}
    (hP : ChargedStd P) (hf : ∀ a, ChargedStd (f a)) : ChargedStd (P.bind f) := by
  induction P with
  | pure a => exact hf a
  | query x k ih => exact fun a => ih a (hP a)
  | randomNat law k ih => exact hP.elim
  | randomPoint law h k ih => exact ⟨hP.1, fun g => ih g (hP.2 g)⟩
  | randomReal law h k ih => exact ⟨hP.1, fun v => ih v (hP.2 v)⟩
  | tick c k ih => exact ih hP

/-! ## The law on the tape -/

/-- A read from the first round, then a run on the rest of the tape: the law of the read,
then the run's law. -/
theorem tapeLaw_map_draw {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (π : Round d → X) (hπ : Measurable π) (μ : Measure X) (hμ : (roundLaw d).map π = μ)
    (σ : X → Round d) (hσ : Measurable σ) (hσπ : ∀ x, π (σ x) = x)
    (F : X → Tape d → Y) (hF : Measurable fun t : Tape d => F (π (t 0)) t.tail)
    (R : X → Measure Y) (ih : ∀ x, Measurable (F x) → (tapeLaw d).map (F x) = R x) :
    (tapeLaw d).map (fun t : Tape d => F (π (t 0)) t.tail) = μ.bind R := by
  let H : X × Tape d → Y := fun p => F p.1 p.2
  have hH : Measurable H := by
    have : H = (fun t : Tape d => F (π (t 0)) t.tail) ∘ fun p : X × Tape d => cons (σ p.1) p.2 := by
      funext p
      simp only [H, Function.comp_apply, cons_zero, tail_cons, hσπ]
    rw [this]
    exact hF.comp (measurable_tape_cons.comp ((hσ.comp measurable_fst).prodMk measurable_snd))
  have hsec : ∀ x, Measurable (F x) := fun x => hH.comp (measurable_const.prodMk measurable_id)
  have hR : ∀ x S, MeasurableSet S → R x S = tapeLaw d (Prod.mk x ⁻¹' (H ⁻¹' S)) := by
    intro x S hS
    rw [← ih x (hsec x), Measure.map_apply (hsec x) hS]
    rfl
  have hRm : Measurable R := by
    refine Measure.measurable_of_measurable_coe _ fun S hS => ?_
    simp_rw [hR _ S hS]
    exact measurable_measure_prodMk_left (hH hS)
  ext S hS
  rw [Measure.map_apply hF hS, Measure.bind_apply hS hRm.aemeasurable, ← hμ,
    lintegral_map (f := fun x => R x S) ((Measure.measurable_coe hS).comp hRm) hπ,
    tapeLaw_apply_eq_lintegral (hF hS)]
  refine lintegral_congr fun r => ?_
  rw [hR _ S hS]
  rfl

theorem measurableSet_image_some {γ : Type} [MeasurableSpace γ] {T : Set γ}
    (hT : MeasurableSet T) : MeasurableSet ((some : γ → Option γ) '' T) := by
  have : (some : γ → Option γ) '' T =
      ArlibCommunity.Algorithms.CV18.optionToSum ⁻¹' (Sum.inr '' T) := by
    ext o
    cases o <;> simp [ArlibCommunity.Algorithms.CV18.optionToSum]
  rw [this]
  exact ArlibCommunity.Algorithms.CV18.measurable_optionToSum (MeasurableSet.inr_image hT)

/-- A kernel is measurable when it is after mapping by `some`. -/
theorem measurable_of_map_some {X γ : Type} [MeasurableSpace X] [MeasurableSpace γ]
    {K : X → Measure γ} (hK : Measurable fun x => (K x).map some) : Measurable K := by
  refine Measure.measurable_of_measurable_coe _ fun T hT => ?_
  have e : ∀ x, K x T = (K x).map some (some '' T) := by
    intro x
    rw [Measure.map_apply ArlibCommunity.Algorithms.CV18.measurable_some
      (measurableSet_image_some hT), Set.preimage_image_eq _ (Option.some_injective _)]
  simp_rw [e]
  exact (Measure.measurable_coe (measurableSet_image_some hT)).comp hK

/-- **On the random tape, a charged program has its output law `runEstimate`** (with no cap,
the run never stops). -/
theorem tapeLaw_map_cexec [MeasurableSpace α] (P : ChargedProgram d α) (hP : ChargedStd P)
    (hm : Measurable fun t => (cexec O P ⊤ t).1) :
    (tapeLaw d).map (fun t => (cexec O P ⊤ t).1) = (P.runEstimate O).map some := by
  induction P with
  | pure a =>
      simp only [cexec, ChargedProgram.runEstimate]
      rw [Measure.map_const, measure_univ, one_smul,
        Measure.map_dirac' ArlibCommunity.Algorithms.CV18.measurable_some]
  | query x k ih =>
      simp only [cexec, ENat.top_ne_zero, ite_false, enat_top_sub_one] at hm ⊢
      exact ih _ (hP _) hm
  | randomNat law k ih => exact hP.elim
  | randomPoint law h k ih =>
      obtain ⟨hlaw, hk⟩ := hP
      subst hlaw
      simp only [cexec, ChargedProgram.runEstimate] at hm ⊢
      have hdraw := tapeLaw_map_draw (fun r : Round d => r.2.1) (measurable_fst.comp measurable_snd) _
        roundLaw_map_gaussian (fun g => (false, g, 0))
        (measurable_const.prodMk (measurable_id.prodMk measurable_const)) (fun _ => rfl)
        (fun g t => (cexec O (k g) ⊤ t).1) hm _ fun g hg => ih g (hk g) hg
      rw [hdraw]
      have hK : Measurable fun g => (k g).runEstimate O := by
        refine measurable_of_map_some ?_
        have hH : Measurable fun p : EuclideanSpace ℝ (Fin d) × Tape d => (cexec O (k p.1) ⊤ p.2).1 := by
          have : (fun p : EuclideanSpace ℝ (Fin d) × Tape d => (cexec O (k p.1) ⊤ p.2).1) =
              (fun t : Tape d => (cexec O (k (t 0).2.1) ⊤ t.tail).1) ∘
                fun p => cons (false, p.1, 0) p.2 := by
            funext p; rfl
          rw [this]
          exact hm.comp (measurable_tape_cons.comp ((measurable_const.prodMk
            (measurable_fst.prodMk measurable_const)).prodMk measurable_snd))
        have e : ∀ g, ((k g).runEstimate O).map some =
            (tapeLaw d).map fun t => (cexec O (k g) ⊤ t).1 := fun g =>
          (ih g (hk g) (hH.comp (measurable_const.prodMk measurable_id))).symm
        simp_rw [e]
        refine Measure.measurable_of_measurable_coe _ fun S hS => ?_
        have e2 : ∀ g, ((tapeLaw d).map fun t => (cexec O (k g) ⊤ t).1) S =
            tapeLaw d (Prod.mk g ⁻¹' ((fun p : EuclideanSpace ℝ (Fin d) × Tape d =>
              (cexec O (k p.1) ⊤ p.2).1) ⁻¹' S)) := fun g =>
          Measure.map_apply (hH.comp (measurable_const.prodMk measurable_id)) hS
        simp_rw [e2]
        exact measurable_measure_prodMk_left (hH hS)
      rw [Measure.map_bind hK.aemeasurable ArlibCommunity.Algorithms.CV18.measurable_some.aemeasurable]
  | randomReal law h k ih =>
      obtain ⟨hlaw, hk⟩ := hP
      subst hlaw
      simp only [cexec, ChargedProgram.runEstimate] at hm ⊢
      have hdraw := tapeLaw_map_draw (fun r : Round d => r.2.2) (measurable_snd.comp measurable_snd) _
        roundLaw_map_unit (fun v => (false, 0, v))
        (measurable_const.prodMk (measurable_const.prodMk measurable_id)) (fun _ => rfl)
        (fun v t => (cexec O (k v) ⊤ t).1) hm _ fun v hv => ih v (hk v) hv
      rw [hdraw]
      have hK : Measurable fun v => (k v).runEstimate O := by
        refine measurable_of_map_some ?_
        have hH : Measurable fun p : ℝ × Tape d => (cexec O (k p.1) ⊤ p.2).1 := by
          have : (fun p : ℝ × Tape d => (cexec O (k p.1) ⊤ p.2).1) =
              (fun t : Tape d => (cexec O (k (t 0).2.2) ⊤ t.tail).1) ∘
                fun p => cons (false, 0, p.1) p.2 := by
            funext p; rfl
          rw [this]
          exact hm.comp (measurable_tape_cons.comp ((measurable_const.prodMk
            (measurable_const.prodMk measurable_fst)).prodMk measurable_snd))
        have e : ∀ v, ((k v).runEstimate O).map some =
            (tapeLaw d).map fun t => (cexec O (k v) ⊤ t).1 := fun v =>
          (ih v (hk v) (hH.comp (measurable_const.prodMk measurable_id))).symm
        simp_rw [e]
        refine Measure.measurable_of_measurable_coe _ fun S hS => ?_
        have e2 : ∀ v, ((tapeLaw d).map fun t => (cexec O (k v) ⊤ t).1) S =
            tapeLaw d (Prod.mk v ⁻¹' ((fun p : ℝ × Tape d =>
              (cexec O (k p.1) ⊤ p.2).1) ⁻¹' S)) := fun v =>
          Measure.map_apply (hH.comp (measurable_const.prodMk measurable_id)) hS
        simp_rw [e2]
        exact measurable_measure_prodMk_left (hH hS)
      rw [Measure.map_bind hK.aemeasurable ArlibCommunity.Algorithms.CV18.measurable_some.aemeasurable]
  | tick c k ih => exact ih hP hm

end ttc.Tape
