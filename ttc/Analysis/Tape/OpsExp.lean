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

/-- A bound on actual executions also bounds their expectation. Unlike
`maxOps`, this can take account of a cap installed in the program. -/
theorem Eops_le_of_exec_ops_le (p : Tree d α) (b B : ℕ)
    (hm : Measurable fun t => outcome (exec p b t))
    (hB : ∀ t, (exec p b t).2.1 ≤ B) : Eops p b ≤ B := by
  rw [Eops_eq_tape p b hm]
  calc ∫⁻ t, ((exec p b t).2.1 : ENNReal) ∂tapeLaw d
      ≤ ∫⁻ _, (B : ENNReal) ∂tapeLaw d :=
        lintegral_mono fun t => Nat.cast_le.mpr (hB t)
    _ = B := by simp

omit [MeasurableSpace α] in
/-- An arithmetic prefix adds its own charge and passes only its actual
value to the continuation. -/
theorem Eops_compute_bind (c : Prog α) (f : α → Tree d β) (b : ℕ)
    (hm : Measurable fun t => outcome (exec (f c.val) b t)) :
    Eops ((compute c).bind f) b = (opsTotal c.cost : ENNReal) + Eops (f c.val) b := by
  have h : Measurable (fun t => outcome (exec ((compute c).bind f) b t)) :=
    (measurable_addOps (opsTotal c.cost)).comp hm
  rw [Eops_eq_tape _ _ h, Eops_eq_tape _ _ hm]
  simp only [compute, Tree.bind, exec, Nat.cast_add]
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]

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

/-- A uniform cost bound on reachable continuations suffices, even when the first
stage can stop or the costs of impossible continuations are unbounded. -/
theorem Eops_bind_le_of_post {p : Tree d α} {f : α → Tree d β} {P : α → Prop}
    (hp : Post p P) (hP : MeasurableSet {a | P a}) (hf : MeasFam f)
    (hcf : ∀ a, CapFirst (f a)) (b c : ℕ)
    (hm : Measurable fun t => outcome (exec p b t)) (B : ENNReal)
    (hB : ∀ a, P a → Eops (f a) c ≤ B) :
    Eops (p.bind f) b ≤ Eops p b + B := by
  rw [Eops_bind_capFirst hf hcf p b hm c]
  have := isProbabilityMeasure_vlaw p b hm
  refine add_le_add le_rfl ?_
  calc ∫⁻ o, o.elim 0 (fun a => Eops (f a) c) ∂(vlaw p b)
      ≤ ∫⁻ _, B ∂(vlaw p b) := by
        apply lintegral_mono_ae
        filter_upwards [ae_vlaw_post hp hP b hm] with o ho
        rcases o with _ | a
        · exact bot_le
        · exact hB a (ho a rfl)
    _ = B := by simp

@[simp] theorem Eops_pure (a : α) (b : ℕ) : Eops (Tree.pure (n := d) a) b = 0 := by
  have hm : Measurable (fun t : Tape d => outcome (exec (.pure a) b t)) :=
    measurable_const (a := (some a, 0, b))
  rw [Eops_eq_tape _ _ hm]
  simp [exec]

@[simp] theorem Eops_fail (b : ℕ) : Eops (Tree.fail (n := d) (α := α)) b = 0 := by
  have hm : Measurable (fun t : Tape d => outcome (exec (Tree.fail (α := α)) b t)) :=
    measurable_const (a := (none, 0, b))
  rw [Eops_eq_tape _ _ hm]
  simp [exec]

/-- A loop with a uniform expected charge per round pays at most that charge
times its fuel. Neither an early success nor failure can add a round. -/
theorem Eops_loopRounds_le [Inhabited α] {body : α → Tree d (α ⊕ β)}
    (hm : MeasFam body) (hcf : ∀ a, CapFirst (body a)) (b : ℕ) (B : ENNReal)
    (hB : ∀ a, Eops (body a) b ≤ B) :
    ∀ (n : ℕ) (a : α), Eops (loopRounds body n a) b ≤ n * B
  | 0, _ => by simp [loopRounds]
  | n + 1, a => by
      have hloop : MeasFam (loopRounds body n) :=
        (MeasFam.loopRounds (A := Unit) (body := fun _ => body)
          (hm.comp (φ := fun q : Unit × α => q.2) measurable_snd) n).comp
          (φ := fun a : α => ((), a)) (measurable_const.prodMk measurable_id)
      have hk : MeasFam fun r : α ⊕ β =>
          r.elim (loopRounds body n) (fun c => Tree.pure (Sum.inr c)) :=
        MeasFam.sumElim (s := id) measurable_id (hloop.comp measurable_snd)
          (MeasFam.pure (measurable_inr.comp measurable_snd))
      have hc : ∀ r : α ⊕ β, CapFirst (r.elim (loopRounds body n) (fun c => Tree.pure (Sum.inr c))) := by
        rintro (a' | c)
        · exact capFirst_loopRounds hcf n a'
        · trivial
      refine (Eops_bind_le_of_post (post_of_forall (Q := fun _ => True) (fun _ => trivial) _)
        (by simp) hk hc b b (hm.outcome a b) (n * B) (fun r _ => ?_)).trans ?_
      · rcases r with a' | c
        · exact Eops_loopRounds_le hm hcf b B hB n a'
        · simp
      · calc Eops (body a) b + n * B ≤ B + n * B := add_le_add (hB a) le_rfl
          _ = ((n + 1 : ℕ) : ENNReal) * B := by push_cast; ring

end ttc.Tape
