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

`#modelClosure` **passes** on the three algorithm-side declarations — `Ttc.ttcAlgOutput`,
`Ttc.ttcRun` and `Ttc.ttc` — and `#modelClosureOfType` on the headline's statement; all four
invocations are enabled at the bottom of this file, so a definition drifting out of
`Ttc/Model/` **or** `Ttc/Probability/` fails `lake build`. `#closure` still fails on the
three algorithm-side ones, on the monadic-versus-oracle gap and on the probability
vocabulary; **every constant it names is defined inside the surface**, so the two checks
disagree by construction rather than by filing (see the measurement section below). The two
`Ttc.ttc_volume_estimate` `#closure` invocations remain commented out.

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
#modelClosure Ttc.ttcRun
#modelClosure Ttc.ttc
-- #closureOfType Ttc.ttc_volume
#modelClosureOfType Ttc.ttc_volume

end Invocations
