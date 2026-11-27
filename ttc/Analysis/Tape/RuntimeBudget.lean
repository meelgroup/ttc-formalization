/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Model.Program

/-! # Intermediate operation budgets for the sealed TTC proof

The random part is bounded by the number of components, the population cap,
CV18's charged cooling budget and the charged length of a walk and its
retries. The deterministic setup terms use the same charged arithmetic as the
program. No budget reads the cost of a random execution.
-/

set_option autoImplicit false

noncomputable section

namespace ttc.RuntimeBudget

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program

variable {d : ℕ}

/-- Arithmetic budget for one capped cooling run, including the membership
arithmetic, the cap installation, and the fallback literal. -/
def cappedRunOps (G : ttc.Program.RunConstants) (d M : ℕ) : ℕ :=
  G.schedule.length * (2 * d + 83) + (7 * d + 84) +
    ((12 * d + 31) + M) * G.queryBudget.get + 2

/-- An operation budget for the sealed cooling call. The first term is the
charged cost of computing its deterministic input constants. Each repetition
then pays for a capped cooling run and one append, and the final term pays for
the median of the resulting estimates. -/
def cv18TapeOpsBudget (d M : ℕ) (eps roundness p : Num ℝ) : ℕ :=
  let c := runConstantsProg d eps roundness p
  let G := c.val
  let r := G.repetitions.get
  opsTotal c.cost + (1 + r * (cappedRunOps G d M + 1)) + (r * (4 * r + 5) + 5)

/-- The fixed cost bound for one proposal, including the membership test
after rounding, in terms of the actual walk length computed by the program. -/
def sampleTryOps (d r steps : ℕ) : ℕ :=
  13 * d + 5 + 2 * d * r + steps * (6 * d + 8 + r * (4 * d + 5))

/-- The expected tail charge combines one rate multiplication, one Poisson
draw, at most five rounds of halving in expectation, and the sampler. -/
def tailOpsBudget (K : Params) (L : Loaded d) : ℕ :=
  let cap := Nat.floor K.thresh.get
  let c := walkConstantsProg L K.scale K.epsPrime K.dim
  let B := sampleTryOps d L.facets c.val.steps.get
  1 + (1 + (8 + 4 * cap) * 5) + (opsTotal c.cost + (1 + cap * (2 * B + 3)))

/-- This is a deterministic bound computed only from the input of the step.
It does not depend on the current rate, random decisions, or the fuel. -/
def componentOpsBudget (K : Params) (L : Loaded d) : ℕ :=
  let x := (cv18ParamsProg K L).val
  let Q := cv18TapeOpsBudget d (2 * d * L.facets) x.1 x.2.2 x.2.1
  let cap := Nat.floor K.thresh.get
  opsTotal (cv18Offsets L).cost + opsTotal (cv18ParamsProg K L).cost + Q +
    (8 + opsTotal (scaledOffsets L K.scale).cost +
      (19 + cap * (d + 2 * d * L.facets + 8)) + tailOpsBudget K L)

/-- Input-only operation budget for a complete sealed run. We read the
deterministic tally of setup, then add the worst-case expected cost of each
component, one initial literal and the three final scalar operations. -/
def estimatorOpsBudget (cs : List (ComponentInput d)) (eps delta : ℝ) : ℕ :=
  match cs with
  | [] => 1
  | _ :: _ =>
      let c := cs.mapM load
      let p := paramsProg cs c.val eps delta
      opsTotal c.cost + opsTotal p.cost + 4 + (c.val.map (componentOpsBudget p.val)).sum

end ttc.RuntimeBudget
