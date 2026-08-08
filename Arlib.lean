/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Probability
import Arlib.Lattice
import Arlib.Convexity
import Arlib.MarkovChains

/-!
# Arlib — staging area

General, reusable Lean 4 + Mathlib material distilled out of this project:
randomized rounding, lattice-point counting, total variation, convexity, and
Markov chain mixing. Nothing here mentions `TTC`, SMT formulas, or any other
kr-25-ssm-specific object.

**Why it lives here and not in `arlib`.** The shared library
(https://github.com/meelgroup/arlib) is pinned to Lean/Mathlib **v4.15.0**; this
project is pinned to **v4.32.0**, so the two cannot be path-dependencies of each
other today. This directory is therefore a *staging area*: it is written against
`Arlib.*` namespaces and arlib's own conventions (Apache-2.0 header,
mathlib-style docstrings, one area root per directory) so that moving it into
`arlib/Arlib/` once that repo is bumped is a mechanical `git mv`.

**The rule that keeps that promise:** no file under `Arlib/` may `import Ttc.*`.
Check it with

```bash
grep -rn "^import Ttc" Arlib/     # must return nothing
```

`Ttc/**` may import both.
-/
