/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.MeasTree

/-!
# The program's trees run measurably

`MeasFam` for each tree of `Analysis/Tape/TTCTrees.lean` and `Analysis/Tape/CV18Trees.lean`,
in the random arguments it is applied to, and finally `measurable_exec_estimatorT`: the run
of the whole program is a measurable function of the tape.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Set

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ttc.Tape.Tree
open ArlibCommunity.Algorithms.CV18 (measurable_some)

variable {d : ℕ} {Q : Type} [MeasurableSpace Q]

theorem MeasFam.computeEnd {δ : Type} [MeasurableSpace δ] {c : Q → Prog δ} (hc : MP c) :
    MeasFam fun q => Tree.compute (n := d) (c q) :=
  (MeasFam.compute hc (MeasFam.pure (n := d) measurable_snd)).congr fun q => rfl

/-! ## Hit-and-Run -/

theorem mf_hitAndRunStep (r : ℕ) (a : Fin r → NumPoint d) (β' : Fin r → Num ℝ)
    {x : Q → NumPoint d} (hx : Measurable x) :
    MeasFam fun q => hitAndRunStepT r a β' (x q) := by
  unfold hitAndRunStepT
  refine MeasFam.coinT ?_
  refine MeasFam.iteB measurable_snd (MeasFam.pure ?_) ?_ <;> try fun_prop
  refine MeasFam.gaussianT ?_
  refine MeasFam.compute (mp_normalize measurable_snd) ?_
  refine MeasFam.compute (mp_chord r a β' ?_ measurable_snd) ?_ <;> try fun_prop
  apply MeasFam.optionElim (β := Num ℝ)
  · fun_prop
  · exact MeasFam.pure (by fun_prop)
  apply MeasFam.optionElim (β := Num ℝ)
  · fun_prop
  · exact MeasFam.pure (by fun_prop)
  refine MeasFam.compute (mp_lt ?_ ?_) ?_ <;> try fun_prop
  refine MeasFam.iteB measurable_snd ?_ (MeasFam.pure ?_) <;> try fun_prop
  refine MeasFam.unitT ?_
  refine MeasFam.computeEnd (mp_move ?_ ?_ measurable_snd ?_ ?_) <;> fun_prop

theorem mf_hitAndRunWalk (r : ℕ) (a : Fin r → NumPoint d) (β' : Fin r → Num ℝ) (steps : Num ℕ)
    {x : Q → NumPoint d} (hx : Measurable x) :
    MeasFam fun q => hitAndRunWalkT r a β' steps (x q) := by
  unfold hitAndRunWalkT
  have hbody : MeasFam fun p : Q × NumPoint d =>
      (hitAndRunStepT r a β' p.2).bind fun y' => (Tree.pure (Sum.inl y') : Tree d _) :=
    MeasFam.bind' (mf_hitAndRunStep r a β' measurable_snd)
      (MeasFam.pure (g := fun p : (Q × NumPoint d) × NumPoint d => (Sum.inl p.2 : _ ⊕ Empty))
        (measurable_inl.comp measurable_snd))
  have hpure : Measurable fun p : Q × (NumPoint d ⊕ Empty) => Sum.elim id Empty.elim p.2 :=
    (measurable_id.sumElim measurable_from_top).comp measurable_snd
  exact MeasFam.bind' (MeasFam.loopTree (count := fun _ => steps) measurable_const
    (body := fun _ y => (hitAndRunStepT r a β' y).bind fun y' => Tree.pure (Sum.inl y'))
    hbody hx) (MeasFam.pure hpure)

end ttc.Tape
