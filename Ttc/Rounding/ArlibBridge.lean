/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Rounding.Tent
import Arlib.Lattice.Rounding.Tent

/-!
# `Ttc.Rounding` ↔ `Arlib.Lattice.Rounding`: what has been re-based, and what has not

The `Arlib/` staging area holds the material with no project-specific content,
written against `Arlib.*` namespaces so that porting it into the shared `arlib`
repository is a `git mv`. For a while it *duplicated* the tent-kernel material in
`Ttc/Rounding/`. This module records how much of that duplication has been
removed, and why the rest cannot be removed the same way.

## Re-based: `Ttc/Rounding/Tent.lean`

`Ttc/Rounding/Tent.lean` is now a **pure re-export** of
`Arlib/Lattice/Rounding/Tent.lean` — a single `export` inside `namespace Ttc`.
No proof is duplicated; each `Ttc.*` name below is an *alias* for the `Arlib`
constant of the same base name, so it is definitionally (indeed syntactically)
the same declaration, and every downstream `simp`/`rw`/`unfold` behaves exactly
as it did before.

| `Ttc.*` (alias) | `Arlib.Lattice.Rounding.*` (definition) |
| --- | --- |
| `Ttc.tent` | `tent` |
| `Ttc.tent_nonneg` | `tent_nonneg` |
| `Ttc.tent_of_abs_le` | `tent_of_abs_le` |
| `Ttc.tent_eq_zero_of_one_le` | `tent_eq_zero_of_one_le` |
| `Ttc.tent_eq_zero_of_notMem` | `tent_eq_zero_of_notMem` |
| `Ttc.continuous_tent` | `continuous_tent` |
| `Ttc.tent_hasCompactSupport` | `tent_hasCompactSupport` |
| `Ttc.integrable_tent` | `integrable_tent` |
| `Ttc.integral_tent` | `integral_tent` |
| `Ttc.integral_id_mul_tent` | `integral_id_mul_tent` |

The `private theorem integral_eq_interval` helper is private on both sides and is
not part of the interface; it exists only inside the `Arlib` module now.

The `example`s at the end of this file *check* the aliasing claim mechanically:
each is closed by `rfl`, which for a `Prop`-valued alias means the two names
elaborate to the same constant.

## Not re-based (and why)

Everything else under `Ttc/Rounding/` has a genuinely different dependency shape
from its `Arlib` counterpart, so it cannot be collapsed by re-export:

* `Ttc/Rounding/ProdKernel.lean`, `ProdLaw.lean`, `RoundLaw.lean`,
  `RoundMoments.lean`, `PiLintegral.lean`, `TentSum.lean` — these are stated in
  terms of the project-specific `Ttc.RoundingKernel` structure and
  `Ttc.Model.Prelude` (`Ttc.Space`, the facet-system setting), reached via
  `Ttc.Rounding.Cl`. `Arlib/Lattice/Rounding/{ProdKernel,RoundLaw,
  KernelIntegral}.lean` prove the same mathematics on a Mathlib-only chain, with
  different statements. Collapsing these needs the `RoundingKernel` abstraction
  itself to move to `Arlib` first — a real refactor, not a re-export.
* `Ttc/Rounding/Cl.lean`, `ClB.lean` — genuinely project-specific: they are about
  `Ttc.FacetSystem` and `claim:cl`. These stay in `Ttc` permanently.
* `Ttc/Rounding/Hoeffding.lean` — the sub-Gaussian tail estimate; the general
  form lives in `Arlib/Probability/SubgaussianTail.lean`, but the `Ttc` file is
  phrased over the project's rounding setting.

## The order a full migration should follow

1. `Tent.lean` — **done** (this file's subject).
2. Move the `RoundingKernel` structure itself to `Arlib` (as a Mathlib-only
   abstraction over `EuclideanSpace ℝ (Fin n)`), leaving `Ttc.RoundingKernel` as
   an abbreviation.
3. Then `ProdKernel`/`ProdLaw`/`RoundLaw`/`RoundMoments`/`PiLintegral`/`TentSum`
   collapse to re-exports the same way `Tent.lean` did.
4. `Cl.lean`/`ClB.lean` never move.
-/

namespace Ttc.Rounding.ArlibBridge

/-! ### Mechanical checks that the `Ttc` names really are the `Arlib` ones -/

example : @Ttc.tent = @Arlib.Lattice.Rounding.tent := rfl

example : @Ttc.tent_nonneg = @Arlib.Lattice.Rounding.tent_nonneg := rfl

example : @Ttc.tent_of_abs_le = @Arlib.Lattice.Rounding.tent_of_abs_le := rfl

example :
    @Ttc.tent_eq_zero_of_one_le = @Arlib.Lattice.Rounding.tent_eq_zero_of_one_le := rfl

example :
    @Ttc.tent_eq_zero_of_notMem = @Arlib.Lattice.Rounding.tent_eq_zero_of_notMem := rfl

example : @Ttc.continuous_tent = @Arlib.Lattice.Rounding.continuous_tent := rfl

example :
    @Ttc.tent_hasCompactSupport = @Arlib.Lattice.Rounding.tent_hasCompactSupport := rfl

example : @Ttc.integrable_tent = @Arlib.Lattice.Rounding.integrable_tent := rfl

example : @Ttc.integral_tent = @Arlib.Lattice.Rounding.integral_tent := rfl

example :
    @Ttc.integral_id_mul_tent = @Arlib.Lattice.Rounding.integral_id_mul_tent := rfl

end Ttc.Rounding.ArlibBridge
