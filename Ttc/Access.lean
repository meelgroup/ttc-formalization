/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.TtcProb

/-!
# `Access`: derived accessors on `Ttc.TtcProb`

The `def`s that read a `Ttc.TtcProb` rather than assume anything about it: the
DNF the algorithm works with, its length, the `j`-th polytope of the
decomposition, and the good event of the `m` `Vol_ED` calls. They live here so
that `Model/ProblemSetting` holds the paper's problem setting and nothing else.
-/

namespace Ttc

open MeasureTheory Pointwise

namespace TtcProb

variable {A : Type*} {n : ℕ} (T : TtcProb A n)

/-- **The DNF the algorithm works with** — line 16's output on the input formula. A
`def`, not a field: the structure carries the *procedure* and the formula, so the
cube list is determined by the input rather than supplied beside it. -/
@[reducible] def D : DNF A := T.toDNF T.φ

/-- **`m`, the number of decomposed polytopes** — the length of the cube list the
main loop folds over. This is `thm:runtime`'s `m`, and `Ttc.TtcProb.cubes_le`
bounds it by the parameter block's `P.m`. -/
def numCubes : ℕ := T.D.length

/-! ### `Vol_ED`'s good event

Two definitions naming what the `m` `Vol_ED` calls of `alg:ttc` line 24 are, so
that `volCoins_good` above has something to be *membership in*. Everything proved
about them — that the former field `volED_hi` follows, and that the event has
probability at least `1 − δ/4` — is in `Ttc/Volume/Bridge.lean`. -/

/-- The `j`-th polytope of the decomposition, with its membership proof — the
`j`-th iteration of `alg:ttc`'s main loop, hence the `j`-th `Vol_ED` call. -/
def cubeAt (j : Fin T.D.length) : {c : Cube A // c ∈ T.toDNF T.φ} :=
  ⟨T.D.get j, List.get_mem _ _⟩

/-- **The good event of the `m` `Vol_ED` calls**, at the parameters `alg:ttc`
lines 18 and 24 use. -/
def volEvent : Set T.volAlg.Ω :=
  volGood T.volAlg T.gammaHat T.P.epsPrime T.P.deltaPrime
    (fun j => T.cen (T.cubeAt j)) (fun j => region T.M (T.D.get j))

end TtcProb

end Ttc
