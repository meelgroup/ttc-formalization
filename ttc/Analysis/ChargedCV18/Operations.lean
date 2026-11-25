/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.Computation.Num

/-!
# Operations: the arithmetic currency of CV18

`cv18Program` (`Model/Pseudocode.lean`) holds every number it computes as a sealed
`Arlib.Computation.Num`, and does its arithmetic with arlib's charged operations on
them.  This file names what one charged operation can be:

* `Op` — the currency: an arithmetic operation of arlib's `NumOp` (`num`), or a real-RAM
  operation of arlib's `RealOp` (`real`: `ℕ → ℝ`, `√`, `exp`, `log`, `u^{1/k}`).
  `NumOps Op` and `RealOps Op` make arlib's names the ones `Op` uses.  Two more are
  CV18's own, as in barbarik4: `query` (one membership-oracle call, `Counted.isMember`) and
  `draw` (one random number read into the sealed world, `Counted.pick`); and one more for
  lists, `cell` (one list cell written, `Counted.push`, or read, `Counted.cell`).
* `Cell` — the storage currency.  No space bound is claimed, so it has one kind.

The tally of a charged computation, `Charged.cost`, is a `CostVec Op`: how many
operations of each kind it spent.  `opsTotal` prices every operation at `1`.
A membership query is charged one `query` here, and is also a step of the program itself,
counted by `ChargedProgram.queryCost`.

Operations are vocabulary, not evidence: nothing here asserts a bound.
-/

namespace ttc.ChargedCV18


open Arlib.Computation

/-- **One charged operation** of CV18: standard arithmetic (`num`), a real-RAM operation
(`real`), a membership-oracle call (`query`), one random number read (`draw`), or one list
cell written or read (`cell`). -/
inductive Op
  | num (o : NumOp)
  | real (o : RealOp)
  | query
  | draw
  | cell
  deriving DecidableEq, Repr

/-- Every operation, listed. -/
def Op.all : List Op :=
  [.num .lit, .num .add, .num .sub, .num .mul, .num .div, .num .max, .num .min,
   .num .cmp, .num .ceil, .num .loop,
   .real .cast, .real .sqrt, .real .exp, .real .log, .real .root, .query, .draw, .cell]

theorem Op.mem_all (o : Op) : o ∈ Op.all := by
  rcases o with o | o | _ | _ | _
  · cases o <;> decide
  · cases o <;> decide
  · decide
  · decide
  · decide

instance : Fintype Op := Fintype.ofList Op.all Op.mem_all

/-- `Op` uses arlib's names for the standard arithmetic operations. -/
instance : NumOps Op where
  charge := Op.num
  charge_injective := fun _ _ h => Op.num.inj h

/-- `Op` uses arlib's names for the real-RAM operations. -/
instance : RealOps Op where
  charge := Op.real
  charge_injective := fun _ _ h => Op.real.inj h

/-- The storage currency.  No space bound is claimed, so it has one kind. -/
inductive Cell
  | cell
  deriving DecidableEq

/-- **The number of operations in a tally**, every operation priced at `1`. -/
def opsTotal (c : CostVec Op) : ℕ := ∑ o, c o

@[simp] theorem opsTotal_zero : opsTotal 0 = 0 := by simp [opsTotal]

@[simp] theorem opsTotal_add (c d : CostVec Op) : opsTotal (c + d) = opsTotal c + opsTotal d := by
  simp [opsTotal, Finset.sum_add_distrib]

@[simp] theorem opsTotal_one (o : Op) : opsTotal (CostVec.one o) = 1 := by
  simp [opsTotal, CostVec.one]

@[simp] theorem opsTotal_many (o : Op) (k : ℕ) : opsTotal (CostVec.many o k) = k := by
  simp [opsTotal, CostVec.many]

theorem opsTotal_sum {ι : Type*} (s : Finset ι) (c : ι → CostVec Op) :
    opsTotal (∑ i ∈ s, c i) = ∑ i ∈ s, opsTotal (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, opsTotal_add, ih]

end ttc.ChargedCV18
