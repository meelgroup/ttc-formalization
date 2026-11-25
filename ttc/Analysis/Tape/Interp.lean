/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.Tree

/-!
# The computation of a tree, on a tape

`interp_run`: running `interp p` from the oracle with tape `t` and `b` membership calls
of the cap left gives `exec p b t`'s result and remaining oracle, and spends `exec`'s
count of operations.
-/

set_option autoImplicit false

noncomputable section

namespace ttc.Tape

open Arlib.Computation (Num Charged CostVec NumOp RealOp)
open ttc.Model.Operations
open ttc.Program

variable {n : ℕ} {α β : Type}

/-- A computation of the program monad, run from the oracle `o`. -/
abbrev runFrom (X : M n α) (o : Oracle n) : Prog (Option α × Oracle n) := X.run.run o

theorem runFrom_bind (X : M n α) (F : α → M n β) (o : Oracle n) :
    runFrom (X >>= F) o =
      runFrom X o >>= fun r =>
        match r.1 with
        | none => Pure.pure (none, r.2)
        | some a => runFrom (F a) r.2 := by
  simp only [runFrom, OptionT.run_bind, Option.elimM, StateT.run_bind]
  congr 1
  funext r
  rcases r with ⟨_ | a, s'⟩ <;> rfl

theorem val_runFrom_bind (X : M n α) (F : α → M n β) (o : Oracle n) :
    (runFrom (X >>= F) o).val =
      match (runFrom X o).val with
      | (none, o') => (none, o')
      | (some a, o') => (runFrom (F a) o').val := by
  rw [runFrom_bind, Charged.val_bind]
  rcases (runFrom X o).val with ⟨_ | a, o'⟩ <;> rfl

theorem cost_runFrom_bind (X : M n α) (F : α → M n β) (o : Oracle n) :
    (runFrom (X >>= F) o).cost = (runFrom X o).cost +
      match (runFrom X o).val with
      | (none, _) => 0
      | (some a, o') => (runFrom (F a) o').cost := by
  rw [runFrom_bind, Charged.cost_bind]
  rcases h : (runFrom X o).val with ⟨_ | a, o'⟩ <;> simp

/-- One primitive followed by a continuation: if the primitive returns `some a` and the
oracle `o'` at a cost `c`, the composite's value and operation count are the
continuation's, plus `c`. -/
theorem run_step {X : M n α} {F : α → M n β} {o o' : Oracle n} {a : α}
    (hv : (runFrom X o).val = (some a, o')) :
    (runFrom (X >>= F) o).val = (runFrom (F a) o').val ∧
      opsTotal (runFrom (X >>= F) o).cost =
        opsTotal (runFrom X o).cost + opsTotal (runFrom (F a) o').cost := by
  refine ⟨by rw [val_runFrom_bind, hv], ?_⟩
  rw [cost_runFrom_bind, hv, opsTotal_add]

/-! ## The primitives -/

theorem cost_charged_bind {γ δ : Type} (p : Prog γ) (f : γ → Prog δ) :
    (Charged.bind p f).cost = p.cost + (f p.val).cost :=
  Charged.cost_bind p f

theorem cost_charged_pure {γ : Type} (a : γ) : (Charged.pure a : Prog γ).cost = 0 := rfl

variable (t : Tape n) (b : ℕ)

theorem runFrom_run (c : Prog α) (o : Oracle n) :
    (runFrom (run c) o).val = (some c.val, o) ∧ (runFrom (run c) o).cost = c.cost := by
  refine ⟨rfl, ?_⟩
  simp [runFrom, run, OptionT.lift, StateT.lift, OptionT.run, StateT.run, OptionT.mk,
    Functor.map, StateT.map, cost_charged_bind, cost_charged_pure]

theorem runFrom_withOracle (f : Oracle n → Prog (α × Oracle n)) (o : Oracle n) :
    (runFrom (withOracle f) o).val = (some (f o).val.1, (f o).val.2) ∧
      (runFrom (withOracle f) o).cost = (f o).cost := by
  refine ⟨rfl, ?_⟩
  simp [runFrom, withOracle, OptionT.lift, StateT.mk, OptionT.run, StateT.run, OptionT.mk,
    Functor.map, StateT.map, cost_charged_bind, cost_charged_pure]

theorem runFrom_failure (o : Oracle n) :
    (runFrom (failure : M n α) o).val = (none, o) ∧ (runFrom (failure : M n α) o).cost = 0 :=
  ⟨rfl, rfl⟩

theorem runFrom_pure (a : α) (o : Oracle n) :
    (runFrom (Pure.pure a : M n α) o).val = (some a, o) ∧
      (runFrom (Pure.pure a : M n α) o).cost = 0 :=
  ⟨rfl, rfl⟩

/-! ## The oracle primitives on a named oracle -/

theorem opsTotal_op (o : Op) {γ : Type} (a : γ) : opsTotal (Charged.op o a : Prog γ).cost = 1 := by
  rw [Charged.cost_op]; exact opsTotal_one o

theorem run_coin : (runFrom (Program.coin : M n Bool) (Oracle.withBudget t b)).val =
      (some (t 0).1, Oracle.withBudget t.tail b) ∧
    opsTotal (runFrom (Program.coin : M n Bool) (Oracle.withBudget t b)).cost = 1 := by
  obtain ⟨hv, hc⟩ := runFrom_withOracle (drawCoin (n := n)) (Oracle.withBudget t b)
  refine ⟨?_, ?_⟩
  · rw [Program.coin, hv, drawCoin_withBudget]; rfl
  · rw [Program.coin, hc, drawCoin_withBudget]; exact opsTotal_op _ _

theorem run_unit : (runFrom (Program.unit : M n (Num ℝ)) (Oracle.withBudget t b)).val =
      (some (sealDraw (t 0).2.2).val, Oracle.withBudget t.tail b) ∧
    opsTotal (runFrom (Program.unit : M n (Num ℝ)) (Oracle.withBudget t b)).cost = 1 := by
  obtain ⟨hv, hc⟩ := runFrom_withOracle (drawUnit (n := n)) (Oracle.withBudget t b)
  refine ⟨?_, ?_⟩
  · rw [Program.unit, hv, drawUnit_withBudget]; rfl
  · rw [Program.unit, hc, drawUnit_withBudget, Charged.cost_bind, Charged.cost_pure, add_zero]
    exact opsTotal_sealDraw _

theorem run_gaussian :
    (runFrom (Program.gaussian : M n (NumPoint n)) (Oracle.withBudget t b)).val =
      (some (sealVector n (WithLp.ofLp (t 0).2.1)).val, Oracle.withBudget t.tail b) ∧
    opsTotal (runFrom (Program.gaussian : M n (NumPoint n)) (Oracle.withBudget t b)).cost =
      n := by
  obtain ⟨hv, hc⟩ := runFrom_withOracle (drawGaussian (n := n)) (Oracle.withBudget t b)
  refine ⟨?_, ?_⟩
  · rw [Program.gaussian, hv, drawGaussian_withBudget]; rfl
  · rw [Program.gaussian, hc, drawGaussian_withBudget, Charged.cost_bind, Charged.cost_pure,
      add_zero]
    exact opsTotal_sealVector _ _

theorem toLp_get_sealVector (v : EuclideanSpace ℝ (Fin n)) :
    WithLp.toLp 2 (fun i => ((sealVector n (WithLp.ofLp v)).val i).get) = v := by
  ext i
  simp [get_sealVector]

theorem run_poisson (rate : Num ℝ) :
    (runFrom (Program.poisson rate : M n (Num ℕ)) (Oracle.withBudget t b)).val =
      (some (sealDraw (poissonQuantile (Real.toNNReal rate.get) (t 0).2.2)).val,
        Oracle.withBudget t.tail b) ∧
    opsTotal (runFrom (Program.poisson rate : M n (Num ℕ)) (Oracle.withBudget t b)).cost =
      1 := by
  obtain ⟨hv, hc⟩ := runFrom_withOracle (drawPoisson (n := n) rate) (Oracle.withBudget t b)
  refine ⟨?_, ?_⟩
  · rw [Program.poisson, hv, drawPoisson_withBudget]; rfl
  · rw [Program.poisson, hc, drawPoisson_withBudget, Charged.cost_bind, Charged.cost_pure,
      add_zero]
    exact opsTotal_sealDraw _

theorem run_binom (N : Num ℕ) :
    (runFrom (withOracle (drawBinomialHalf N) : M n (Num ℕ)) (Oracle.withBudget t b)).val =
      (some (sealDraw (binomialHalfQuantile N.get (t 0).2.2)).val,
        Oracle.withBudget t.tail b) ∧
    opsTotal (runFrom (withOracle (drawBinomialHalf N) : M n (Num ℕ))
      (Oracle.withBudget t b)).cost = 1 := by
  obtain ⟨hv, hc⟩ := runFrom_withOracle (drawBinomialHalf (n := n) N) (Oracle.withBudget t b)
  refine ⟨?_, ?_⟩
  · rw [hv, drawBinomialHalf_withBudget]; rfl
  · rw [hc, drawBinomialHalf_withBudget, Charged.cost_bind, Charged.cost_pure, add_zero]
    exact opsTotal_sealDraw _

theorem run_queryCap (c : Num ℕ) :
    (runFrom (queryCap c : M n Unit) (Oracle.withBudget t b)).val =
      (some (), Oracle.withBudget t c.get) ∧
    opsTotal (runFrom (queryCap c : M n Unit) (Oracle.withBudget t b)).cost = 1 := by
  obtain ⟨hv, hc⟩ := runFrom_withOracle (setBudget (n := n) c) (Oracle.withBudget t b)
  refine ⟨?_, ?_⟩
  · rw [queryCap, hv, setBudget_withBudget]; rfl
  · rw [queryCap, hc, setBudget_withBudget]; exact opsTotal_op _ _

theorem run_spend_zero :
    (runFrom (withOracle spendQuery : M n Bool) (Oracle.withBudget t 0)).val =
      (some false, Oracle.withBudget t 0) ∧
    opsTotal (runFrom (withOracle spendQuery : M n Bool) (Oracle.withBudget t 0)).cost = 0 := by
  obtain ⟨hv, hc⟩ := runFrom_withOracle (spendQuery (n := n)) (Oracle.withBudget t 0)
  refine ⟨?_, ?_⟩
  · rw [hv, spendQuery_withBudget_zero]; rfl
  · rw [hc, spendQuery_withBudget_zero]; exact opsTotal_zero

theorem run_spend_succ :
    (runFrom (withOracle spendQuery : M n Bool) (Oracle.withBudget t (b + 1))).val =
      (some true, Oracle.withBudget t b) ∧
    opsTotal (runFrom (withOracle spendQuery : M n Bool)
      (Oracle.withBudget t (b + 1))).cost = 0 := by
  obtain ⟨hv, hc⟩ := runFrom_withOracle (spendQuery (n := n)) (Oracle.withBudget t (b + 1))
  refine ⟨?_, ?_⟩
  · rw [hv, spendQuery_withBudget_succ]; rfl
  · rw [hc, spendQuery_withBudget_succ]; exact opsTotal_zero

/-! ## The theorem -/

/-- The result, the oracle left, and the operations spent by running `interp p` from the
oracle with tape `t` and `b` calls left. -/
theorem interp_run (p : Tape.Tree n α) (b : ℕ) (t : Tape n) :
    (runFrom (Tree.interp p) (Oracle.withBudget t b)).val =
        ((Tree.exec p b t).1, Oracle.withBudget (Tree.exec p b t).2.2.2 (Tree.exec p b t).2.2.1) ∧
      opsTotal (runFrom (Tree.interp p) (Oracle.withBudget t b)).cost = (Tree.exec p b t).2.1 := by
  induction p generalizing b t with
  | pure a => exact ⟨rfl, by simp [Tree.interp, Tree.exec, (runFrom_pure a _).2]⟩
  | fail => exact ⟨rfl, by simp [Tree.interp, Tree.exec, (runFrom_failure _).2]⟩
  | step c k ih =>
      obtain ⟨hv, hc⟩ := run_step (F := fun x => Tree.interp (k x)) (runFrom_run c _).1
      obtain ⟨iv, ic⟩ := ih c.val b t
      refine ⟨hv.trans iv, ?_⟩
      simp only [Tree.interp, Tree.exec]
      rw [hc, (runFrom_run c _).2, ic]
  | coin k ih =>
      obtain ⟨pv, pc⟩ := run_coin t b
      obtain ⟨hv, hc⟩ := run_step (F := fun x => Tree.interp (k x)) pv
      obtain ⟨iv, ic⟩ := ih (t 0).1 b t.tail
      refine ⟨hv.trans iv, ?_⟩
      simp only [Tree.interp, Tree.exec]
      rw [hc, pc, ic]
  | unit k ih =>
      obtain ⟨pv, pc⟩ := run_unit t b
      obtain ⟨hv, hc⟩ := run_step (F := fun x => Tree.interp (k x.get)) pv
      obtain ⟨iv, ic⟩ := ih (t 0).2.2 b t.tail
      refine ⟨hv.trans iv, ?_⟩
      simp only [Tree.interp, Tree.exec]
      rw [hc, pc]
      exact congrArg _ ic
  | gaussian k ih =>
      obtain ⟨pv, pc⟩ := run_gaussian t b
      obtain ⟨hv, hc⟩ := run_step
        (F := fun g => Tree.interp (k (WithLp.toLp 2 fun i => (g i).get))) pv
      obtain ⟨iv, ic⟩ := ih (t 0).2.1 b t.tail
      simp only [toLp_get_sealVector] at hv hc
      refine ⟨hv.trans iv, ?_⟩
      simp only [Tree.interp, Tree.exec]
      rw [hc, pc, ic]
  | poisson rate k ih =>
      obtain ⟨pv, pc⟩ := run_poisson t b rate
      obtain ⟨hv, hc⟩ := run_step (F := fun x => Tree.interp (k x.get)) pv
      obtain ⟨iv, ic⟩ := ih _ b t.tail
      refine ⟨hv.trans iv, ?_⟩
      simp only [Tree.interp, Tree.exec]
      rw [hc, pc]
      exact congrArg _ ic
  | binom N k ih =>
      obtain ⟨pv, pc⟩ := run_binom t b N
      obtain ⟨hv, hc⟩ := run_step (F := fun x => Tree.interp (k x.get)) pv
      obtain ⟨iv, ic⟩ := ih _ b t.tail
      refine ⟨hv.trans iv, ?_⟩
      simp only [Tree.interp, Tree.exec]
      rw [hc, pc]
      exact congrArg _ ic
  | setBudget c k ih =>
      obtain ⟨pv, pc⟩ := run_queryCap t b c
      obtain ⟨hv, hc⟩ := run_step (F := fun _ => Tree.interp k) pv
      obtain ⟨iv, ic⟩ := ih c.get t
      refine ⟨hv.trans iv, ?_⟩
      simp only [Tree.interp, Tree.exec]
      rw [hc, pc, ic]
  | spend k ih =>
      cases b with
      | zero =>
          obtain ⟨pv, pc⟩ := run_spend_zero t
          obtain ⟨hv, hc⟩ := run_step (F := fun x => Tree.interp (k x)) pv
          obtain ⟨iv, ic⟩ := ih false 0 t
          refine ⟨hv.trans iv, ?_⟩
          simp only [Tree.interp, Tree.exec]
          rw [hc, pc, ic, zero_add]
      | succ b =>
          obtain ⟨pv, pc⟩ := run_spend_succ t b
          obtain ⟨hv, hc⟩ := run_step (F := fun x => Tree.interp (k x)) pv
          obtain ⟨iv, ic⟩ := ih true b t
          refine ⟨hv.trans iv, ?_⟩
          simp only [Tree.interp, Tree.exec]
          rw [hc, pc, ic, zero_add]

end ttc.Tape
