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

/-! ## Rounding and sampling -/

theorem mf_roundCoords (one : Num ℤ) : ∀ (k : ℕ) {Q : Type} [MeasurableSpace Q]
    {q₀ : Q → Fin k → Num ℝ}, Measurable q₀ →
    MeasFam fun q => roundCoordsT (d := d) one k (q₀ q)
  | 0, _, _, _, _ => MeasFam.pure measurable_const
  | k + 1, Q, _, q₀, hq => by
      unfold roundCoordsT
      refine MeasFam.unitT ?_
      refine MeasFam.compute (mp_roundStep ?_ measurable_snd) ?_
      · exact (measurable_pi_apply 0).comp (hq.comp measurable_fst)
      refine MeasFam.bind' (mf_roundCoords one k (q₀ := fun p : (Q × Num ℝ) × Num ℤ => Fin.tail (q₀ p.1.1))
        (measurable_fin_tail.comp (hq.comp measurable_fst.fst)))
        (MeasFam.pure (measurable_fin_cons.comp (measurable_fst.snd.prodMk measurable_snd)))

theorem mf_roundPoint {p : Q → NumPoint d} (hp : Measurable p) :
    MeasFam fun q => roundPointT (p q) := by
  unfold roundPointT
  exact MeasFam.computeConst _ (mf_roundCoords _ d hp)

theorem mf_sampleTry (L : Loaded d) (W : WalkConstants d L.facets)
    (scaled : Fin L.facets → Num ℝ) (dimN : Num ℕ) :
    MeasFam fun _ : Q => sampleTryT L W scaled dimN := by
  unfold sampleTryT
  refine MeasFam.gaussianT ?_
  refine MeasFam.unitT ?_
  refine MeasFam.compute (mp_ballStart measurable_const ?_ measurable_snd) ?_
  · exact measurable_fst.snd
  refine MeasFam.bind' (mf_hitAndRunWalk _ _ _ _ measurable_snd) ?_
  refine MeasFam.compute (mp_chart W measurable_snd) ?_
  refine MeasFam.bind' (mf_roundPoint measurable_snd) ?_
  refine MeasFam.compute (mp_latticeMember L scaled measurable_snd) ?_
  refine MeasFam.pure ?_
  exact measurable_bif measurable_snd (measurable_some.comp measurable_fst.snd) measurable_const

theorem mf_sampleUntilAccepted (L : Loaded d) (W : WalkConstants d L.facets)
    (scaled : Fin L.facets → Num ℝ) (dimN : Num ℕ) :
    ∀ fuel, MeasFam fun _ : Q => sampleUntilAcceptedT L W scaled dimN fuel
  | 0 => MeasFam.fail
  | fuel + 1 => by
      unfold sampleUntilAcceptedT
      refine MeasFam.bind' (mf_sampleTry L W scaled dimN) ?_
      exact MeasFam.optionElim measurable_snd
        ((mf_sampleUntilAccepted L W scaled dimN fuel).comp measurable_fst)
        (MeasFam.pure measurable_snd)

/-! ## Thinning and the halving loop -/

theorem mf_filterCopies {keep : Q → (Fin d → Num ℤ) → Tree d Bool}
    (hkeep : MeasFam fun p : Q × (Fin d → Num ℤ) => keep p.1 p.2)
    {X : Q → List (Fin d → Num ℤ)} (hX : Measurable X) :
    MeasFam fun q => filterCopiesT (keep q) (X q) := by
  unfold filterCopiesT
  refine MeasFam.computeConst _ ?_
  refine MeasFam.computeConst _ ?_
  refine MeasFam.foldlM ?_ hX (by fun_prop)
  refine MeasFam.compute (mp_cell ?_) ?_
  · fun_prop
  refine MeasFam.bind' (hkeep.comp (φ := fun p : (Q × (List (Fin d → Num ℤ) × Num ℕ) ×
      (Fin d → Num ℤ)) × (Fin d → Num ℤ) => (p.1.1, p.2)) (by fun_prop)) ?_
  refine MeasFam.iteB measurable_snd ?_ (MeasFam.pure (by fun_prop))
  refine MeasFam.compute (mp_push ?_ ?_) ?_
  · fun_prop
  · fun_prop
  refine MeasFam.compute (mp_addN ?_ measurable_const) ?_
  · fun_prop
  exact MeasFam.pure (by fun_prop)

theorem mf_halve (K : Params) :
    ∀ (f : ℕ) {Q : Type} [MeasurableSpace Q] {p : Q → Num ℝ} {X : Q → List (Fin d → Num ℤ)}
      {size N : Q → Num ℕ},
      Measurable p → Measurable X → Measurable size → Measurable N →
      MeasFam fun q => halveT K f (p q) (X q) (size q) (N q)
  | 0, _, _, _, _, _, _, _, _, _, _ => MeasFam.fail
  | f + 1, Q, _, p, X, size, N, hp, hX, hs, hN => by
      unfold halveT
      refine MeasFam.compute ?_ ?_
      · exact MP.bind' (mp_addN hs hN) (MP.bind' (mp_cast measurable_snd)
          (mp_le measurable_snd measurable_const))
      refine MeasFam.iteB measurable_snd (MeasFam.pure ?_) ?_
      · exact ((hp.comp measurable_fst).prodMk ((hX.comp measurable_fst).prodMk
          ((hs.comp measurable_fst).prodMk (hN.comp measurable_fst))))
      refine MeasFam.bind' ((mf_filterCopies (keep := fun _ _ => Tree.coinT)
          (MeasFam.coinT (MeasFam.pure measurable_snd))
          (hX.comp measurable_fst)).congr fun q => rfl) ?_
      refine MeasFam.binomT (hN.comp measurable_fst.fst) ?_
      refine MeasFam.compute (mp_divLit 2 (hp.comp measurable_fst.fst.fst)) ?_
      exact mf_halve K f
        (Q := (((Q × Bool) × (List (Fin d → Num ℤ) × Num ℕ)) × Num ℕ) × Num ℝ)
        (p := fun x => x.2) (X := fun x => x.1.1.2.1)
        (size := fun x => x.1.1.2.2) (N := fun x => x.1.2) (by fun_prop) (by fun_prop)
        (by fun_prop) (by fun_prop)

end ttc.Tape
