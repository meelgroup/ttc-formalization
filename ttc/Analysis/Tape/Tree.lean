/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Model.SealedProgram

/-!
# Tape programs: the sealed program as a tree

A computation of the program monad `Program.M` (`Model/SealedProgram.lean`) is a function
of the sealed oracle, and a function cannot be inducted on.  A `Tree` is the same kind of
computation written as a tree: a step of charged arithmetic (`step`), a read of the tape
(`coin`, `unit`, `gaussian`, `poisson`, `binom`), a change to CV18's query cap
(`setBudget`, `spend`), a stop (`fail`), or a result (`pure`).

A tree has two readings here:

* `interp` — the computation of the program monad it stands for;
* `exec p b t` — what it does on the tape `t` with `b` membership calls of the cap left:
  its result (`none` if it stopped), the operations it spent, the calls left, and the tape
  left.

`interp_run` says they agree: running `interp p` from the oracle with tape `t` and `b`
calls left gives `exec p b t`'s result and remaining oracle, and spends `exec`'s count of
operations.  `Analysis/Tape/Law.lean` gives `exec`'s law on the random tape.
-/

set_option autoImplicit false

noncomputable section

namespace ttc.Tape

open Arlib.Computation (Num Charged CostVec NumOp RealOp)
open ttc.Model.Operations

/-! ## The primitives, on an oracle named by `Oracle.withBudget` -/

section Primitives

variable {n : ℕ}

@[simp] theorem get_sealDraw {α : Type} (a : α) : (sealDraw a).val.get = a := rfl

theorem opsTotal_one (o : Op) : opsTotal (CostVec.one o) = 1 := by
  classical
  simp [opsTotal, CostVec.one]

theorem opsTotal_add (c c' : CostVec Op) : opsTotal (c + c') = opsTotal c + opsTotal c' := by
  simp [opsTotal, Finset.sum_add_distrib]

@[simp] theorem opsTotal_zero : opsTotal 0 = 0 := by simp [opsTotal]

theorem opsTotal_exchange_relabel (o : Op) (c : CostVec Op) :
    opsTotal (CostVec.exchange (relabelLit o) c) = opsTotal c := by
  classical
  simp only [opsTotal, CostVec.exchange]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun o' _ => ?_
  rw [← Finset.mul_sum]
  have : ∑ i, relabelLit o o' i = 1 := by
    unfold relabelLit
    split_ifs <;> simp [CostVec.one]
  rw [this, mul_one]

theorem opsTotal_exchange_drawLabel (c : CostVec Op) :
    opsTotal (CostVec.exchange drawLabel c) = opsTotal c := by
  classical
  simp only [opsTotal, CostVec.exchange]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun o' _ => ?_
  rw [← Finset.mul_sum]
  have : ∑ i, drawLabel o' i = 1 := by
    unfold drawLabel
    split_ifs <;> simp [CostVec.one]
  rw [this, mul_one]

@[simp] theorem opsTotal_sealDraw {α : Type} (a : α) : opsTotal (sealDraw a).cost = 1 := by
  simp only [sealDraw, Charged.cost_exchange, opsTotal_exchange_drawLabel, Num.cost_lit]
  exact opsTotal_one _

theorem get_sealVector : ∀ (m : ℕ) (v : Fin m → ℝ) (i : Fin m), ((sealVector m v).val i).get = v i
  | 0, _, i => i.elim0
  | m + 1, v, i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simp only [sealVector, Charged.val_bind, Charged.val_pure, Fin.cons_succ]
        exact get_sealVector m (Fin.tail v) j

theorem opsTotal_sealVector : ∀ (m : ℕ) (v : Fin m → ℝ), opsTotal (sealVector m v).cost = m
  | 0, _ => by simp [sealVector]
  | m + 1, v => by
      simp only [sealVector, Charged.cost_bind, Charged.cost_pure, opsTotal_add,
        opsTotal_sealDraw, opsTotal_sealVector m, add_zero]
      ring

end Primitives

/-! ## Trees -/

/-- A computation of the program monad as a tree. -/
inductive Tree (n : ℕ) (α : Type) : Type 1 where
  | pure (result : α)
  | fail
  | step {β : Type} (c : Prog β) (next : β → Tree n α)
  | coin (next : Bool → Tree n α)
  | unit (next : ℝ → Tree n α)
  | gaussian (next : EuclideanSpace ℝ (Fin n) → Tree n α)
  | poisson (rate : Num ℝ) (next : ℕ → Tree n α)
  | binom (count : Num ℕ) (next : ℕ → Tree n α)
  | setBudget (budget : Num ℕ) (next : Tree n α)
  | spend (next : Bool → Tree n α)

namespace Tree

variable {n : ℕ} {α β γ : Type}

/-- Sequential composition. -/
def bind : Tree n α → (α → Tree n β) → Tree n β
  | .pure a, f => f a
  | .fail, _ => .fail
  | .step c k, f => .step c fun x => (k x).bind f
  | .coin k, f => .coin fun x => (k x).bind f
  | .unit k, f => .unit fun x => (k x).bind f
  | .gaussian k, f => .gaussian fun x => (k x).bind f
  | .poisson r k, f => .poisson r fun x => (k x).bind f
  | .binom N k, f => .binom N fun x => (k x).bind f
  | .setBudget c k, f => .setBudget c (k.bind f)
  | .spend k, f => .spend fun x => (k x).bind f

/-- `p`, and `q` wherever `p` stops. -/
def orElse : Tree n α → Tree n α → Tree n α
  | .pure a, _ => .pure a
  | .fail, q => q
  | .step c k, q => .step c fun x => (k x).orElse q
  | .coin k, q => .coin fun x => (k x).orElse q
  | .unit k, q => .unit fun x => (k x).orElse q
  | .gaussian k, q => .gaussian fun x => (k x).orElse q
  | .poisson r k, q => .poisson r fun x => (k x).orElse q
  | .binom N k, q => .binom N fun x => (k x).orElse q
  | .setBudget c k, q => .setBudget c (k.orElse q)
  | .spend k, q => .spend fun x => (k x).orElse q

/-! ## The computation a tree stands for -/

open ttc.Program in
/-- **The computation of the program monad a tree stands for**: each node is the
corresponding primitive of `Program`. -/
def interp : Tree n α → M n α
  | .pure a => Pure.pure a
  | .fail => failure
  | .step c k => run c >>= fun x => interp (k x)
  | .coin k => Program.coin >>= fun x => interp (k x)
  | .unit k => Program.unit >>= fun x => interp (k x.get)
  | .gaussian k => Program.gaussian >>= fun g =>
      interp (k (WithLp.toLp 2 fun i => (g i).get))
  | .poisson r k => Program.poisson r >>= fun x => interp (k x.get)
  | .binom N k => withOracle (drawBinomialHalf N) >>= fun x => interp (k x.get)
  | .setBudget c k => queryCap c >>= fun _ => interp k
  | .spend k => withOracle spendQuery >>= fun x => interp (k x)

/-! ## The run on a tape -/

/-- **What a tree does on the tape `t`** with `b` membership calls of the cap left: the
result (`none` if it stopped), the operations spent, the calls left, and the tape left. -/
def exec : Tree n α → ℕ → Tape n → Option α × ℕ × ℕ × Tape n
  | .pure a, b, t => (some a, 0, b, t)
  | .fail, b, t => (none, 0, b, t)
  | .step c k, b, t =>
      let r := exec (k c.val) b t
      (r.1, opsTotal c.cost + r.2.1, r.2.2)
  | .coin k, b, t =>
      let r := exec (k (t 0).1) b t.tail
      (r.1, 1 + r.2.1, r.2.2)
  | .unit k, b, t =>
      let r := exec (k (t 0).2.2) b t.tail
      (r.1, 1 + r.2.1, r.2.2)
  | .gaussian k, b, t =>
      let r := exec (k (t 0).2.1) b t.tail
      (r.1, n + r.2.1, r.2.2)
  | .poisson rate k, b, t =>
      let r := exec (k (poissonQuantile (Real.toNNReal rate.get) (t 0).2.2)) b t.tail
      (r.1, 1 + r.2.1, r.2.2)
  | .binom N k, b, t =>
      let r := exec (k (binomialHalfQuantile N.get (t 0).2.2)) b t.tail
      (r.1, 1 + r.2.1, r.2.2)
  | .setBudget c k, _, t =>
      let r := exec k c.get t
      (r.1, 1 + r.2.1, r.2.2)
  | .spend k, 0, t => exec (k false) 0 t
  | .spend k, b + 1, t => exec (k true) b t

end Tree

end ttc.Tape
