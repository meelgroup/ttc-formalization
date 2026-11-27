/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Batteries.Tactic.OpenPrivate
import ttc.Analysis.RealRAMLemmas

/-! # Equations for the analysis of the sealed oracle

The proof uses the oracle constructor to describe intermediate states. The
program seal forbids that constructor, including through this helper.
-/

set_option autoImplicit false

noncomputable section

namespace ttc.Model.Operations

open Arlib.Computation
open private Oracle.mk from ttc.Model.Operations

/-- The intermediate oracle with the remaining tape and query cap. -/
def Oracle.withBudget {n : ℕ} (tape : Tape n) (budget : ℕ) : Oracle n :=
  Oracle.mk tape budget

theorem ofTape_eq {n : ℕ} (t : Tape n) : Oracle.ofTape t = Oracle.withBudget t 0 := rfl

theorem setBudget_withBudget {n : ℕ} (b : Num ℕ) (t : Tape n) (k : ℕ) :
    setBudget b (Oracle.withBudget t k) =
      Charged.op (Op.num .loop) ((), Oracle.withBudget t b.get) :=
  rfl

theorem spendQuery_withBudget_zero {n : ℕ} (t : Tape n) :
    spendQuery (Oracle.withBudget t 0) = pure (false, Oracle.withBudget t 0) :=
  rfl

theorem spendQuery_withBudget_succ {n : ℕ} (t : Tape n) (k : ℕ) :
    spendQuery (Oracle.withBudget t (k + 1)) = pure (true, Oracle.withBudget t k) :=
  rfl

theorem drawCoin_withBudget {n : ℕ} (t : Tape n) (k : ℕ) :
    drawCoin (Oracle.withBudget t k) =
      Charged.op Op.draw ((t 0).1, Oracle.withBudget t.tail k) :=
  rfl

theorem drawUnit_withBudget {n : ℕ} (t : Tape n) (k : ℕ) :
    drawUnit (Oracle.withBudget t k) = (do
      let u ← sealDraw (t 0).2.2
      pure (u, Oracle.withBudget t.tail k)) :=
  rfl

theorem drawGaussian_withBudget {n : ℕ} (t : Tape n) (k : ℕ) :
    drawGaussian (Oracle.withBudget t k) = (do
      let g ← sealVector n (WithLp.ofLp (t 0).2.1)
      pure (g, Oracle.withBudget t.tail k)) :=
  rfl

theorem drawPoisson_withBudget {n : ℕ} (rate : Num ℝ) (t : Tape n) (k : ℕ) :
    drawPoisson rate (Oracle.withBudget t k) = (do
      let r ← sealDraw (poissonQuantile (Real.toNNReal rate.get) (t 0).2.2)
      pure (r, Oracle.withBudget t.tail k)) :=
  rfl

theorem drawBinomialHalf_withBudget {n : ℕ} (N : Num ℕ) (t : Tape n) (k : ℕ) :
    drawBinomialHalf N (Oracle.withBudget t k) = (do
      let r ← sealDraw (binomialHalfQuantile N.get (t 0).2.2)
      pure (r, Oracle.withBudget t.tail k)) :=
  rfl

end ttc.Model.Operations
