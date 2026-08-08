/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Lattice.Rounding.Tent

/-!
# The rounding displacement in one coordinate (re-export)

The paper cites `rnd` to `KV97` without giving a construction. The standard one —
and the one whose properties the analysis actually uses — is **independent
coordinatewise randomized rounding**:

  `xₖ = ⌊pₖ⌋ + Bernoulli(pₖ − ⌊pₖ⌋)`.

Fix a lattice point `x` and ask for the density of `p` in one coordinate given
that it rounds to `x`. Writing `u = p − x`: for `u ∈ [0,1)` we have `⌊p⌋ = x` and
the Bernoulli must fail, probability `1 − u`; for `u ∈ [−1,0)` we have
`⌊p⌋ = x − 1` and it must fire, probability `1 + u`. So the density is the
**triangular ("tent") density** `1 − |u|` on `[−1,1]`.

That single function carries every property `claim:cl` needs of the displacement:
it is a probability density (`Ttc.integral_tent`), supported in `[−1,1]`
(`Ttc.tent_eq_zero_of_one_le`), and has **mean zero** (`Ttc.integral_id_mul_tent`)
— the three hypotheses of `Ttc.rounding_tail_bound`, per coordinate. Independence
across coordinates then comes from taking the product.

## Provenance

This material is *not* project-specific: it is Mathlib-only, and it lives in the
`Arlib` staging area as `Arlib.Lattice.Rounding` (destined for the shared `arlib`
repository). This module is a **pure re-export** — `export` installs each name as
an alias in the `Ttc` namespace, so `Ttc.tent` *is* the constant
`Arlib.Lattice.Rounding.tent` (not a copy), and every downstream `simp`/`rw`
that unfolds it behaves exactly as before. There is no duplicated proof here.

See `Ttc/Rounding/ArlibBridge.lean` for the full map of which `Ttc.Rounding`
declarations come from `Arlib` and which are still project-specific.
-/

namespace Ttc

-- Re-export the one-dimensional tent density and its analytic properties from
-- the `Arlib` staging area under their historical `Ttc.*` names. These are
-- aliases, not definitions: `Ttc.tent` and `Arlib.Lattice.Rounding.tent` are the
-- same constant.
export Arlib.Lattice.Rounding
  (tent tent_nonneg tent_of_abs_le tent_eq_zero_of_one_le tent_eq_zero_of_notMem
    continuous_tent tent_hasCompactSupport integrable_tent integral_tent
    integral_id_mul_tent)

end Ttc
