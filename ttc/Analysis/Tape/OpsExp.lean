/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.Ops

/-!
# Expected operation counts

`Eops p b` is the expected number of operations of `p` on the random tape.  It is at most the
worst case (`Eops_le_maxOps`) and adds up along a sequence (`Eops_bind`, `Eops_bind_capFirst`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ttc.Tape.Tree
open ttc.SealedRun (tapeLaw)

variable {d : ℕ} {α β : Type} [MeasurableSpace α] [MeasurableSpace β]

/-- **The expected operation count of a tree.** -/
def Eops (p : Tree d α) (b : ℕ) : ENNReal := ∫⁻ o, (o.2.1 : ENNReal) ∂(law p b)

theorem measurable_ops : Measurable fun o : Outcome α => (o.2.1 : ENNReal) :=
  measurable_from_top.comp measurable_snd.fst

theorem Eops_eq_tape (p : Tree d α) (b : ℕ) (hm : Measurable fun t => outcome (exec p b t)) :
    Eops p b = ∫⁻ t, ((exec p b t).2.1 : ENNReal) ∂(tapeLaw d) := by
  rw [Eops, ← tapeLaw_map_exec p b hm, lintegral_map measurable_ops hm]
  rfl

theorem Eops_le_maxOps (p : Tree d α) (b : ℕ) (hm : Measurable fun t => outcome (exec p b t)) :
    Eops p b ≤ (maxOps p : ENNReal) := by
  rw [Eops_eq_tape p b hm]
  calc ∫⁻ t, ((exec p b t).2.1 : ENNReal) ∂(tapeLaw d) ≤ ∫⁻ _, (maxOps p : ENNReal) ∂(tapeLaw d) :=
        lintegral_mono fun t => by
          have := ENat.toENNReal_le.mpr (exec_ops_le_maxOps p b t)
          simpa using this
    _ = maxOps p := by simp

theorem isProbabilityMeasure_law (p : Tree d α) (b : ℕ)
    (hm : Measurable fun t => outcome (exec p b t)) : IsProbabilityMeasure (law p b) := by
  rw [← tapeLaw_map_exec p b hm]
  exact Measure.isProbabilityMeasure_map hm.aemeasurable

/-- **Operations add up along a sequence.** -/
theorem Eops_bind {f : α → Tree d β} (hf : MeasFam f) (p : Tree d α) (b : ℕ)
    (hp : Measurable fun t => outcome (exec p b t)) :
    Eops (p.bind f) b =
      Eops p b + ∫⁻ o, o.1.elim 0 (fun a => Eops (f a) o.2.2) ∂(law p b) := by
  have hc := measurable_cont hf
  rw [Eops, law_bind hf p b hp, Measure.lintegral_bind hc.aemeasurable measurable_ops.aemeasurable, Eops,
    ← lintegral_add_left measurable_ops]
  refine lintegral_congr fun o => ?_
  obtain ⟨_ | a, m, b'⟩ := o
  · simp only [cont, Option.elim]
    rw [lintegral_dirac' _ measurable_ops]
    simp
  · simp only [cont, Option.elim]
    have := isProbabilityMeasure_law (f a) b' (hf.outcome a b')
    rw [lintegral_map measurable_ops (measurable_addOps m)]
    simp only [addOps, Nat.cast_add]
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    rfl

omit [MeasurableSpace α] in
theorem exec_ops_of_capFirst {p : Tree d α} (hp : CapFirst p) (b b' : ℕ) (t : Tape d) :
    (exec p b t).2.1 = (exec p b' t).2.1 := by
  induction p generalizing t with
  | pure a => rfl
  | fail => rfl
  | step c k ih => simp only [exec, ih c.val hp t]
  | coin k ih => simp only [exec, ih _ (hp _) _]
  | unit k ih => simp only [exec, ih _ (hp _) _]
  | gaussian k ih => simp only [exec, ih _ (hp _) _]
  | poisson r k ih => simp only [exec, ih _ (hp _) _]
  | binom N k ih => simp only [exec, ih _ (hp _) _]
  | setBudget c k ih => rfl
  | spend k ih => exact hp.elim

theorem Eops_eq_of_capFirst {p : Tree d α} (hp : CapFirst p)
    (hm : ∀ c, Measurable fun t => outcome (exec p c t)) (b b' : ℕ) : Eops p b = Eops p b' := by
  rw [Eops_eq_tape p b (hm b), Eops_eq_tape p b' (hm b')]
  simp only [exec_ops_of_capFirst hp b b']

theorem MeasFam.measurable_Eops {f : α → Tree d β} (hf : MeasFam f) (c : ℕ) :
    Measurable fun a => Eops (f a) c :=
  (Measure.measurable_lintegral measurable_ops).comp
    (hf.measurable_law.comp (measurable_id.prodMk measurable_const))

/-- **Operations along a sequence whose continuation sets the cap first.** -/
theorem Eops_bind_capFirst {f : α → Tree d β} (hf : MeasFam f) (hcf : ∀ a, CapFirst (f a))
    (p : Tree d α) (b : ℕ) (hp : Measurable fun t => outcome (exec p b t)) (c : ℕ) :
    Eops (p.bind f) b = Eops p b + ∫⁻ o, o.elim 0 (fun a => Eops (f a) c) ∂(vlaw p b) := by
  have hg : Measurable fun o : Option α => o.elim (0 : ENNReal) (fun a => Eops (f a) c) := by
    have : (fun o : Option α => o.elim (0 : ENNReal) (fun a => Eops (f a) c)) =
        Sum.elim (fun _ : Unit => (0 : ENNReal)) (fun a => Eops (f a) c) ∘
          ArlibCommunity.Algorithms.CV18.optionToSum := by
      funext o; cases o <;> rfl
    rw [this]
    exact (measurable_const.sumElim (MeasFam.measurable_Eops hf c)).comp
      ArlibCommunity.Algorithms.CV18.measurable_optionToSum
  rw [Eops_bind hf p b hp, vlaw, lintegral_map hg measurable_fst]
  congr 1
  refine lintegral_congr fun o => ?_
  obtain ⟨_ | a, m, b'⟩ := o
  · rfl
  · exact Eops_eq_of_capFirst (hcf a) (fun c' => hf.outcome a c') b' c

end ttc.Tape
