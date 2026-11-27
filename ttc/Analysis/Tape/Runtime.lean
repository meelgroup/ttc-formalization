/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.RuntimeBudget
import ttc.Analysis.Tape.ComponentOps
import ttc.Analysis.Tape.FuelOps

/-! # Bounding the cost of the complete sealed estimator -/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace ttc.Tape

open ttc.RuntimeBudget

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ttc.SealedRun
open ttc.Tape.Tree

variable {d k : ℕ} {F : ttc.LRAFormula d k}

private theorem Eops_components_le (hd : 3 ≤ d) (f b : ℕ) (K : Params) (hTh : 0 < K.thresh.get) :
    ∀ (Ls : List (Loaded d)),
      (∀ L ∈ Ls, vlaw (sampleTryT L (walkConstantsProg L K.scale K.epsPrime K.dim).val
        (scaledOffsets L K.scale).val K.dimN) b {some none} ≤ (2 : ENNReal)⁻¹) →
      ∀ s : State d, ComponentStateOk K s →
      Eops (Ls.foldlM (fun s L => stepT (cv18T d) f K L s) s) b ≤
        ((Ls.map (componentOpsBudget K)).sum : ℕ) := by
  intro Ls
  induction Ls with
  | nil =>
      intro _ s _
      simp only [List.foldlM_nil, Tree.pure_eq, List.map_nil, List.sum_nil,
        Eops_pure, Nat.cast_zero, le_refl]
  | cons L Ls ih =>
      intro hacc s hs
      let next := fun s => Ls.foldlM (fun s L => stepT (cv18T d) f K L s) s
      have hmNext : MeasFam next :=
        (MeasFam.foldlM_fixed (A := Unit) (g := fun _ s L => stepT (cv18T d) f K L s)
          (fun L => mf_step f K L measurable_snd) Ls).comp
          (φ := fun s => ((), s)) (measurable_const.prodMk measurable_id)
      have hmP : MeasFam fun _ : Unit => stepT (cv18T d) f K L s :=
        mf_step _ _ _ measurable_const
      rw [List.foldlM_cons, List.map_cons, List.sum_cons, Nat.cast_add]
      refine (Eops_bind_le_of_post (post_stepT_componentStateOk f K L s hs) (measurableSet_componentStateOk K)
        hmNext (capFirst_foldlM (fun s L => capFirst_stepT f K L s) Ls)
        b b (hmP.outcome () b) _ (fun s' hs' => ih (fun L' hL => hacc L' (List.mem_cons_of_mem _ hL))
          s' hs')).trans ?_
      exact add_le_add (Eops_stepT_le hd f b K L s hTh hs (hacc L List.mem_cons_self)) le_rfl

private theorem Eops_estimatorT_le (hn : 21 ≤ d) (D : ttc.Decomposition F)
    (p : ttc.ApproxParams) (f : ℕ) :
    Eops (estimatorT (cv18T d) f (componentsOf D) p.epsilon p.delta) 0 ≤
      estimatorOpsBudget (componentsOf D) p.epsilon p.delta := by
  let cs := componentsOf D
  by_cases hn' : cs = []
  · have hm : Measurable fun t : Tape d =>
        outcome (exec (compute (A.lit (0 : ℝ))) 0 t) :=
      (MeasFam.computeEnd (Q := Unit) (MP.const (A.lit (0 : ℝ)))).outcome () 0
    change Eops (estimatorT (cv18T d) f cs p.epsilon p.delta) 0 ≤ estimatorOpsBudget cs p.epsilon p.delta
    rw [hn', estimatorT, estimatorOpsBudget]
    exact Eops_le_of_exec_ops_le _ _ _ hm (fun _ => by simp [compute, exec])
  have hlen : cs.length = D.componentCount := List.length_ofFn
  have hm : 0 < D.componentCount := by
    rw [← hlen]
    cases h : cs with
    | nil => exact (hn' h).elim
    | cons c cs => simp
  let c := cs.mapM load
  let M := paramsProg cs c.val p.epsilon p.delta
  let K := M.val
  have hcs : c.val = (List.ofFn D.component).map loaded := by
    simp [c, cs, componentsOf, val_mapM, List.map_ofFn, Function.comp_def, val_load_componentInput]
  have hK : K = paramsOf D p := by simp only [K, M, c, paramsOf, val_mapM, cs]
  obtain ⟨-, -, -, -, hT, -, -⟩ := paramsProg_val D p hm
  have hTh : 0 < K.thresh.get := by
    rw [hK, paramsOf, hT]
    exact p.threshold_pos _
  have hacc : ∀ L ∈ c.val,
      vlaw (sampleTryT L (walkConstantsProg L K.scale K.epsPrime K.dim).val
        (scaledOffsets L K.scale).val K.dimN) 0 {some none} ≤ (2 : ENNReal)⁻¹ := by
    intro L hL
    rw [hcs, List.mem_map] at hL
    obtain ⟨P, hP, rfl⟩ := hL
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hP
    rw [hK]
    exact certified_sampleTry_rejection_le hn D p i 0
  let start : State d := ⟨K.thresh, [], (A.lit (0 : ℕ)).val⟩
  have hstart : ComponentStateOk K start := ⟨hTh.le, by simpa [start] using hTh.le⟩
  let P := c.val.foldlM (fun s L => stepT (cv18T d) f K L s) start
  let finish : State d → Prog (Num ℝ) := outProg K
  let zcont := fun (Ls : List (Loaded d)) (K' : Params) (z : Num ℕ) =>
    (Ls.foldlM (fun s L => stepT (cv18T d) f K' L s) (⟨K'.thresh, [], z⟩ : State d)).bind
      fun s => compute (outProg K' s)
  let mcont := fun (Ls : List (Loaded d)) (K' : Params) =>
    (compute (A.lit (0 : ℕ))).bind (zcont Ls K')
  let ccont := fun Ls : List (Loaded d) =>
    (compute (paramsProg cs Ls p.epsilon p.delta)).bind (mcont Ls)
  have hmP : MeasFam fun _ : Unit => P :=
    (MeasFam.foldlM_fixed (A := Unit) (g := fun _ s L => stepT (cv18T d) f K L s)
      (fun L => mf_step f K L measurable_snd) c.val).comp
      (φ := fun _ : Unit => ((), start)) measurable_const
  have hmF : MeasFam fun s : State d => compute (n := d) (finish s) :=
    MeasFam.computeEnd (MP.bind' (mp_cast State.measurable_size)
      (MP.bind' (mp_mul (State.measurable_p.comp measurable_fst) measurable_const)
        (mp_div (by fun_prop) measurable_snd)))
  have hmLast : MeasFam fun _ : Unit => P.bind (fun s => compute (finish s)) :=
    MeasFam.bind' hmP (hmF.comp measurable_snd)
  have hmZero : MeasFam fun _ : Unit => mcont c.val K :=
    MeasFam.computeConst _ hmLast
  have hmSetup : MeasFam fun _ : Unit => ccont c.val :=
    MeasFam.computeConst _ hmZero
  change Eops (estimatorT (cv18T d) f cs p.epsilon p.delta) 0 ≤ estimatorOpsBudget cs p.epsilon p.delta
  rw [estimatorT_cons _ _ hn']
  change Eops ((compute c).bind ccont) 0 ≤ _
  rw [Eops_compute_bind c ccont 0 (hmSetup.outcome () 0)]
  change (opsTotal c.cost : ENNReal) + Eops ((compute M).bind (mcont c.val)) 0 ≤ _
  rw [Eops_compute_bind M (mcont c.val) 0 (hmZero.outcome () 0)]
  change (opsTotal c.cost : ENNReal) + ((opsTotal M.cost : ENNReal) +
    Eops ((compute (A.lit (0 : ℕ))).bind (zcont c.val K)) 0) ≤ _
  rw [Eops_compute_bind (A.lit (0 : ℕ)) (zcont c.val K) 0 (hmLast.outcome () 0),
    opsTotal_lit, Nat.cast_one]
  have hlast := Eops_bind_le_of_post (post_of_forall (Q := fun _ => True) (fun _ => trivial) _)
    (by simp) hmF (fun _ => trivial) 0 0 (hmP.outcome () 0) 3
    (fun s _ => Eops_le_of_exec_ops_le _ _ _ (hmF.outcome s 0) (fun t => by
      simp [compute, exec, finish, outProg, A.cast, opsTotal_one, opsTotal_add]))
  have hfold := Eops_components_le (by omega) f 0 K hTh c.val hacc start hstart
  refine (add_le_add le_rfl (add_le_add le_rfl (add_le_add le_rfl
    (hlast.trans (add_le_add hfold le_rfl))))).trans_eq ?_
  cases h : cs with
  | nil => exact (hn' h).elim
  | cons hd tl =>
      simp only [estimatorOpsBudget, ← h]
      change _ = ((opsTotal c.cost + opsTotal M.cost + 4 + (c.val.map (componentOpsBudget K)).sum : ℕ) : ENNReal)
      push_cast
      ring

/-- Expected arithmetic and draws of the same sealed run used by accuracy.
The input-only bound holds despite the two unbounded first-exit loops. -/
theorem sealed_expectedOperations_le (hn : 21 ≤ d) (F : ttc.LRAFormula d k)
    (hb : Bornology.IsBounded (ttc.solutionSet F)) (p : ttc.ApproxParams)
    (prep : ttc.TTCPreprocessor d k) :
    expectedOperations F hb p prep ≤ estimatorOpsBudget (componentsOf (prep.run F hb)) p.epsilon p.delta :=
  expectedOperations_le_of_uniform hn F hb p prep _
    (Eops_estimatorT_le hn (prep.run F hb) p)

end ttc.Tape
