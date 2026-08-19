import Ttc.Audit.ClosureCommands
import Ttc.Model.Pseudocode
import Ttc.Model.Theorem

/-!
# Audit: what the `TTC` statement is actually made of

Two machine checks, ported verbatim in structure and naming from
`nfalean/ApproxNFA/Monadic/ClosureCheck.lean`, so that the two developments read alike and an
auditor who has seen one has seen the other.

**1. No probability space of ours** (`#closure`, `#closureOfType`). The definitional closure of
the declaration mentions none of *this* development's probability-space constructions: no
`Ttc.TtcProb` (the 59-field hypothesis bundle), no `Ttc.Oracles` (the oracle bundle the
pseudocode runs over), no `Ttc.trajLaw` / `Ttc.trajOracles` / `Ttc.totalRate` (the coupled
Poisson family of `Coupling/Family`), no `Ttc.MonteCarlo.coins` (the volume oracle's coin
space), and nothing from `Ttc.Coupling` or `Ttc.Process`.

(Mathlib's `MeasureTheory` API is of course a probability-space development; that is Mathlib's
business. The point of the check is whether *this* development has to construct a probability
space of its own in order to *state* its theorem.)

**2. `Model/`, `Probability/` and `Geometry/` are the whole audit surface**
(`#modelClosure`, `#modelClosureOfType`). Every `Ttc` constant the declaration transitively
unfolds to is *defined in a file under `Ttc/Model/`, `Ttc/Probability/` or
`Ttc/Geometry/`*. This is the check that backs the reader-facing promise made in `Ttc.lean`:
open those three directories — four files of model, four short files of probability
vocabulary, one file of convex geometry — and every constant the headline mentions is
defined in front of you. It is strictly stronger than check 1, and it fails the build the
moment a definition the statement depends on drifts out of them, which is exactly the
regression worth catching.

The surface was one directory until the probability vocabulary was moved out of
`Model/Prelude` into `Ttc/Probability/`, and two until the canonical `(Am, bv)` description
was moved out into `Ttc/Geometry/`. **Why it is three, and what bounds the second and third,
is argued at "The audit surface" below — read that before quoting this check**; the short
version is that `Ttc.ttc` is a `Measure`, so the ambient randomness is part of what the
headline's type unfolds to no matter where it is filed, and `Ttc/Probability/` is held to
vocabulary-plus-nothing-the-walk-can-see in exchange for being admitted, while
`Ttc/Geometry/` is held to definitions-only.

The counts did not move when `Ttc/Geometry/` was split off — 109 / 157 / 199 / 206 before
and after — which is the point: the same constants are in the same closures, filed
somewhere that says more accurately what they are. The counts *did* move on 2026-08-12,
when `Ttc.ttc` became four-ary and its body took on the two fixed per-call prices. The
number the invocations below print is the current one; quote that, not this sentence.

## `Ttc.ttc` and `Ttc.ttc_volume` are deliberately NOT checked, and here is the argument

`Ttc/Model/Theorem.lean` carries one algorithm and one theorem, both at the oracles the paper
specifies — Cousins–Vempala Gaussian cooling for volume, the hit-and-run / ball-walk hybrid
for sampling.  Neither is checked below, and the omission is a decision rather than an
oversight.

Until 2026-08-19 they *were* checked, because `Ttc.ttc` was then a different object: the
algorithm at *reference* oracles — hit-and-miss Monte Carlo and the lazy ball walk, correct
and exponential in `n` — charged at two fixed per-call prices it was not proved to pay.  That
version was deleted, together with every price, bridge and witness attached to it.  What
replaced it is the algorithm at the constructed backends, and that object cannot be checked.

**Why it cannot be checked.**  Naming the fast algorithm *is* naming the construction.
Measured with this file's own `closureAux` and `outsideSurface`, the statement reaches **805
constants, 637 of them outside the surface, across 108 modules** — the whole `Ttc/Exec/` cost
layer and much of `Ttc/Volume/`: kernels, retry laws, Poisson trajectories, certificates,
schedules, the backend.  Not envelopes and prices; everything.  There is no small set to
relocate: the cost is the algorithm, not the packaging.

**Why the list below was not extended.**  Admitting those 108 modules would make the surface
108 modules wide, and the reader-facing promise — open three directories and every constant
the headline mentions is in front of you — would mean nothing.  A promise that covers
everything is not a promise.  So the surface is left as it is, and the headline is stated
outside it.

**What is therefore still guaranteed, and what is not.**  The *specification* keeps the
four-file promise: `Ttc.ttcAlgOutput` is `alg:ttc` with the oracle bundle as an argument, its
closure is checked below, and the build fails if it drifts.  The *instantiation* — which
volume estimator, which sampler, at which envelope — has no such guarantee, and
`Ttc/Model/Theorem.lean`'s docstring says so in place.  A reader checking *what the paper's
algorithm is* need not leave `Model/`; a reader checking *what was proved about running it*
must read the construction.  That asymmetry is real and is the honest state of the
development, not a gap to be papered over by widening a definition until it says nothing.

Trading it away was the deliberate choice: one theorem about the algorithm that actually
executes the paper's oracles is worth more than two theorems of which the checkable one is
about oracles nobody would run.

## What "closure" means here, precisely

`closureAux` walks **both** the type and the value (`ci.value?`) of each constant it reaches.
In this Lean version `ConstantInfo.value?` returns `none` for theorems, so the walk has an
asymmetry that is worth stating because it is exactly the notion we want:

* **definitions** are unfolded through their *bodies* — what a `def` is built from is in scope;
* **theorems** are entered only through their *types* — a proof term's internals are not.

That is the right notion for an audit of a *statement*: we care about what the headline
*means*, not about which lemmas its proof happens to chain together. A proof is free to use
the measure-theoretic product space; a statement that mentions it has a different meaning.

Note that `Ttc.Params` bundles five *proof* fields, so some proof terms are genuinely part of
what the algorithm is (see `Model/Pseudocode`'s docstring); those are reached through the
types they inhabit, as they should be.

## Status in this repo

`#modelClosure` **passes** on the algorithm-side specification `Ttc.ttcAlgOutput`; that
invocation is enabled at the bottom of this file, so a definition drifting out of
`Ttc/Model/` **or** `Ttc/Probability/` fails `lake build`. `#closure` still fails on it, on
the monadic-versus-oracle gap and on the probability vocabulary; **every constant it names is
defined inside the surface**, so the two checks disagree by construction rather than by
filing (see the measurement section below).

`Ttc.Audit.forbidden` and `Ttc.Audit.forbiddenModules` were **not** touched by the move to
`Ttc/Probability/`, deliberately: every definition kept its existing full name, so
`` `Ttc.trajLaw `` and `` `Ttc.MonteCarlo `` still match exactly what they matched before,
and check 1 measures exactly what it used to. Renaming them into a `Ttc.Probability.*`
namespace would have made those two entries silently dead, which is the sort of quiet
weakening this file exists to prevent.
-/

section Invocations

-- #closure Ttc.ttcAlgOutput
#modelClosure Ttc.ttcAlgOutput

/-! ### The reference oracles are gone from behind `Ttc.ttc`, and this checks it

`Ttc.ttc` used to run hit-and-miss Monte Carlo (`Ttc.mcVol`) for volume and the lazy ball
walk for sampling.  It now runs Cousins–Vempala Gaussian cooling and the hit-and-run / ball-
walk hybrid.  A docstring saying so would be a name standing in for an analysis
(`CLAUDE.md` §13), so the three checks below *are* the analysis: `#absentFromClosure` walks
`Ttc.ttc`'s definitional closure and throws if it finds the constant named.

`Ttc.mcVol` still exists, and files that define it are still on `Ttc.ttc`'s **import** path —
they are imported for other definitions, and `Ttc/Exec/Final.lean`'s separate end-to-end
theorem is still proved about it.  Import reachability is not definitional reachability, and
it is the second one that says which oracle a run executes.  These checks measure the second.

**A fourth check was written and it failed, which is the useful part.**
`#absentFromClosure Ttc.mixSteps in Ttc.ttc` throws: the lazy ball walk's step count *is*
still behind `Ttc.ttc`.  That is not a leftover — it is the hybrid sampler's low-dimension
branch, and `Ttc.ttc` is defined at every `n`, so the branch is part of the definition.

⚠ **What that branch means changed on 2026-08-19.**  The threshold was `1100`, so a run at
`21 ≤ n < 1100` — a dimension `Ttc.ttc_volume` admits — genuinely took ball-walk steps, with
the `4 ^ n` that implies.  The spherical-cap estimate now holds from `n ≥ 21`, so
`Ttc.hybridTransitionBound` is hit-and-run at `21 ≤ n` and the ball-walk branch is
**unreachable under the headline's hypotheses**.  It remains in the closure because `Ttc.ttc`
is total and the `if` is still there; it is no longer a walk any theorem here describes.  The
check is inverted below into `#inClosure` so that the dependence cannot silently disappear
without the build noticing.

`#inClosure` also serves as the control on the two negative checks: a negative result from a
walk that was looking in the wrong place would prove nothing, so the two positive checks —
the constructed volume estimator and the constructed sampler kernel, both of which pass for
the right reason — are what make the negatives worth reading.

One measurement worth recording, because it is a distinction the checks make sharply.
`Ttc.hybridTransitionBound` and `Ttc.mixStepsBound` are **not** in the closure, while
`Ttc.mixSteps` and `Ttc.kv97HybridKernel` are.  The first two are *envelope* arithmetic —
they appear in what `Ttc.ttc_volume` bounds the cost by, not in what the run does — and the
last two are the run's own kernel.  The walk sees the algorithm, not the analysis of it,
which is what makes "which oracle does this execute" a question it can answer. -/

#absentFromClosure Ttc.mcVol in Ttc.ttc
#absentFromClosure Ttc.MonteCarlo.hitData in Ttc.ttc
#inClosure Ttc.TtcSlowRuntimePerPhase.slowPerPhaseImplementation in Ttc.ttc
#inClosure Ttc.kv97HybridKernel in Ttc.ttc
#inClosure Ttc.mixSteps in Ttc.ttc

end Invocations
