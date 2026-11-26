# A machine-checked volume estimator for SMT(LRA) formulas

This is a Lean 4 and Mathlib formalization of TTC from *Efficient Volume
Computation for SMT Formulas* (preliminary version at KR 2025). TTC estimates
the volume of the solution set of a linear real arithmetic formula. It combines
Cousins–Vempala Gaussian cooling (CV18), lattice sampling by Hit-and-Run, and a
Poisson-thinning counter.

## What is proved

Both public theorems in [Model/Theorem.lean](ttc/Model/Theorem.lean) concern the
same sealed program.

- **Theorem 1** (`ttc_theorem1_volume_accuracy`) bounds the relative error by
  `ε` with probability at least `1 − δ`.
- **Theorem 3** (`ttc_theorem3_expected_runtime`) bounds the expected operation
  tally of that execution by `RuntimeBudget.estimatorOpsBudget`. The tally
  covers setup, all CV18 arithmetic including facet membership and median
  selection, component scans and thinning, Hit-and-Run including rounding and
  rejected attempts, and the final estimate. It does not count hypothetical
  re-executions with progressively larger fuel.

The budget is an explicit function of the preprocessed inputs and parameters.
Its random-work terms use the CV18 caps, the population cap, the walk length
and a bound on retries in expectation. The new theorem does not claim that
this budget has been reduced to the paper's `Õ(m n⁵ ρ² r_max)` expression.
The older measure-level runtime argument is retained under `Analysis/` for
reference and is not the public runtime claim.

## Assumptions and cost model

- The solution set is bounded, and `0 < ε, δ ≤ 1`. The dimension must be at least
  21, as required by the formalized Hit-and-Run mixing theorem.
- Preprocessing supplies a certified polytope decomposition. Boolean
  abstraction, DNF conversion, normalization, and solving the linear programs
  for the inscribed ball and bounding radius are outside the charged run.
  Loading their results and computing the lattice precision are charged.
- The tally is for an exact real RAM, not bit complexity or floating-point
  time. The currency includes arithmetic, comparisons, casts, transcendental
  primitives, random draws, and charged storage accesses. Poisson and binomial
  quantiles are unit-cost draws in this model. A standard Gaussian vector is
  charged per coordinate. Polytope membership is **not** an oracle primitive.

## Audit surface

| File | Role |
|---|---|
| [Prelude.lean](ttc/Model/Prelude.lean) | Inputs, formulas, decompositions, and preprocessing interface |
| [Operations.lean](ttc/Model/Operations.lean) | Real-RAM currency, sealed numbers, and the random oracle |
| [Program.lean](ttc/Model/Program.lean) | Charged TTC, CV18, and Hit-and-Run programs |
| [Run.lean](ttc/Model/Run.lean) | Tape law, execution, output law, and expected tally |
| [RuntimeBudget.lean](ttc/Model/RuntimeBudget.lean) | Explicit input-only bounds |
| [Theorem.lean](ttc/Model/Theorem.lean) | Public accuracy and runtime claims |

The build runs the program seal, model-closure checks, and surplus checks for
both the program and the full model. The program seal checks for uncharged
scalar arithmetic and free access to the tape or the operation counter.
Model closure checks the public statements and execution definitions for
dependencies outside the model. The surplus checks look for author-written
definitions that are not reached from the estimator or the public theorems.

## Verification

Run `lake exe cache get` on a fresh checkout, then `lake build`. The toolchain
is Lean 4.35.0 and the dependency revisions are pinned in `lakefile.toml`.
The build prints the axioms of both headline theorems and the audit results.
