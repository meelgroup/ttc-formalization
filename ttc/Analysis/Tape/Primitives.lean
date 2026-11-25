/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.Agree

/-!
# The program's primitives as trees

Each primitive of the program monad (`Model/SealedProgram.lean`) as a tree, and the
statement that the tree stands for it (`interp_*`).  A procedure's tree is written from
these with `Tree.bind`, following the procedure's text.
-/

set_option autoImplicit false

noncomputable section

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program

variable {n : ℕ} {α β : Type}

namespace Tree

instance : Monad (Tree n) where
  pure := .pure
  bind := Tree.bind

@[simp] theorem bind_eq (p : Tree n α) (f : α → Tree n β) : p >>= f = p.bind f := rfl

@[simp] theorem pure_eq (a : α) : (Pure.pure a : Tree n α) = .pure a := rfl

@[simp] theorem interp_bind' (p : Tree n α) (f : α → Tree n β) :
    interp (p >>= f) = interp p >>= fun a => interp (f a) := interp_bind p f

@[simp] theorem interp_pure (a : α) : interp (Tree.pure (n := n) a) = Pure.pure a := rfl

@[simp] theorem interp_fail : interp (Tree.fail : Tree n α) = failure := rfl

/-- Charged arithmetic. -/
def compute (c : Prog α) : Tree n α := .step c .pure

/-- A fair coin. -/
def coinT : Tree n Bool := .coin .pure

/-- A uniform number in `[0, 1]`, sealed. -/
def unitT : Tree n (Num ℝ) := .unit fun v => .pure (sealDraw v).val

/-- A standard Gaussian vector, sealed. -/
def gaussianT : Tree n (NumPoint n) :=
  .gaussian fun g => .pure (sealVector n (WithLp.ofLp g)).val

/-- A Poisson number, sealed. -/
def poissonT (rate : Num ℝ) : Tree n (Num ℕ) := .poisson rate fun k => .pure (sealDraw k).val

/-- A `Binomial(N, 1/2)` number, sealed. -/
def binomT (N : Num ℕ) : Tree n (Num ℕ) := .binom N fun k => .pure (sealDraw k).val

/-- Set CV18's query cap. -/
def queryCapT (c : Num ℕ) : Tree n Unit := .setBudget c (.pure ())

/-- Spend one membership call of the cap. -/
def spendT : Tree n Bool := .spend .pure

@[simp] theorem interp_compute (c : Prog α) : interp (compute (n := n) c) = run c := by
  simp only [compute, interp]
  exact _root_.bind_pure _

@[simp] theorem interp_coinT : interp (coinT (n := n)) = Program.coin := by
  simp only [coinT, interp]
  exact _root_.bind_pure _

theorem sealDraw_get {γ : Type} (x : Num γ) : (sealDraw x.get).val = x :=
  Num.ext rfl

@[simp] theorem interp_unitT : interp (unitT (n := n)) = Program.unit := by
  simp only [unitT, interp, sealDraw_get]
  exact _root_.bind_pure _

theorem sealVector_get (g : NumPoint n) :
    (sealVector n fun i => (g i).get).val = g := by
  funext i
  exact Num.ext (get_sealVector n _ i)

@[simp] theorem interp_gaussianT : interp (gaussianT (n := n)) = Program.gaussian := by
  show (Program.gaussian >>= fun g : NumPoint n =>
    (Pure.pure (sealVector n fun i => (g i).get).val : M n _)) = _
  simp only [sealVector_get]
  exact _root_.bind_pure (m := M n) _

@[simp] theorem interp_poissonT (rate : Num ℝ) :
    interp (poissonT (n := n) rate) = Program.poisson rate := by
  simp only [poissonT, interp, sealDraw_get]
  exact _root_.bind_pure _

@[simp] theorem interp_binomT (N : Num ℕ) :
    interp (binomT (n := n) N) = withOracle (drawBinomialHalf N) := by
  simp only [binomT, interp, sealDraw_get]
  exact _root_.bind_pure _

@[simp] theorem interp_queryCapT (c : Num ℕ) : interp (queryCapT (n := n) c) = queryCap c := by
  simp only [queryCapT, interp]
  exact _root_.bind_pure _

@[simp] theorem interp_spendT : interp (spendT (n := n)) = withOracle spendQuery := by
  simp only [spendT, interp]
  exact _root_.bind_pure _

theorem interp_ite (c : Bool) (p q : Tree n α) :
    interp (if c then p else q) = if c then interp p else interp q := by
  cases c <;> rfl

end Tree

end ttc.Tape
