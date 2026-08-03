/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Analysis.CountVector
import Ttc.Analysis.Capstone

/-!
# The distributional contract on the oracle bundle

`Ttc.Oracles` fixes only the *shape* of the four external calls; their
distributions are what `lem:numlattice` is about. This file states them.

## What may be assumed, and about which draws

`Ttc.TtcProb.clockBound` is the number of draws the run can possibly consume:
`Ttc.run_congr` proves the run is unchanged by any oracle bundle agreeing below
it. So the laws below are asserted **only for `c < clockBound`** — asserting them
for every clock would be assuming more than the algorithm can observe, and would
also make the degenerate witness (which runs no cubes at all) fail for no reason.

## Why this is weaker than what it replaces

`numlattice` asserts a *quantitative accuracy guarantee* — that the output lands
within `(1±ε/3)` of `L` with probability `1−δ`. These fields assert only that the
**primitives behave as specified**: a Poisson draw is Poisson, a thinning keeps
each copy independently with probability `½`. Nothing here mentions accuracy,
`ε`, or `δ`. Getting from one to the other is the whole `Analysis/Chernoff`,
`Analysis/Thinning` and `Analysis/SketchProcess` development.
-/

namespace Ttc

open MeasureTheory ProbabilityTheory

namespace TtcProb

variable {A : Type*} {n : ℕ} (T : TtcProb A n)

/-- **The number of draws the run can consume.** Each cube costs at most
`3·fuel + 2`: `fuel` thinnings in the first loop, one Poisson, `2·fuel` more of
each in the second, and the `GenerateSamples` draw. `Ttc.run_congr` shows the run
never reads a clock at or above this. -/
noncomputable def clockBound : ℕ := T.D.length * (3 * T.fuel + 2)

/-- The run only reads draws below `Ttc.TtcProb.clockBound` — the reason the laws
below need only constrain those. -/
theorem run_eq_of_agree_below (O' : Oracles n (Cube A)) (ω : T.Ω)
    (hvol : (T.O ω).vol = O'.vol) (hcov : (T.O ω).covered = O'.covered)
    (hah : ∀ c < T.clockBound, (T.O ω).halve c = O'.halve c)
    (hap : ∀ c < T.clockBound, (T.O ω).pois c = O'.pois c)
    (hag : ∀ c < T.clockBound, (T.O ω).gen c = O'.gen c) :
    ttcOutput T.P T.O T.fuel T.ρ T.D ω = run T.P O' T.fuel T.ρ T.D :=
  run_congr T.P hvol hcov T.fuel T.ρ T.D hah hap hag

end TtcProb

/-- **The distributional contract on the oracle bundle.**

Each field constrains one primitive, and only on the draws the run can reach.
Together they are what `lem:numlattice` needs of the randomness — and, unlike
`numlattice` itself, they say nothing about accuracy. -/
structure OracleLaws {A : Type*} {n : ℕ} (T : TtcProb A n) : Prop where
  /-- **The Poisson draws are Poisson** (`alg:ttc` lines 38, 41). -/
  pois_law : ∀ c < T.clockBound, ∀ (i : Cube A) (j : ℕ) (lam : ℝ), 0 ≤ lam →
    @Measure.map T.Ω ℕ T.mΩ _ (fun ω => (T.O ω).pois c i j lam) T.μ
      = poissonMeasure lam.toNNReal
  /-- **The thinning is a fair independent coin per copy** (`alg:ttc` lines 33,
  40): the multiplicity of each lattice point is thinned `Binomial(·, ½)`, and the
  points are thinned independently of one another. -/
  halve_law : ∀ c < T.clockBound, ∀ (j : ℕ) (X : Multiset (Space n)),
    @Measure.map T.Ω (Fin T.latCard → ℕ) T.mΩ _
        (fun ω => T.cnt ((T.O ω).halve c j X)) T.μ
      = Measure.pi fun i => binomial (T.cnt X i) half

/-! ## ⚠️ NO WITNESS

**`Ttc.OracleLaws` currently has no witness, and nothing consumes it.**

Its only witness was the degenerate `trivialProb`, which has been removed —
`Ttc.TtcProb` now carries the sampler fields, and no instance with `D = []`
satisfies them. The non-degenerate witness `Ttc.Box.boxProb` does **not** satisfy
this contract either: `pois_law` demands the draw match its `lam` argument for
*every* `lam`, whereas `Ttc.trajOracles` reads the coupled family and ignores
`lam`.

These are two different ways to model the same sampling, and the development uses
the trajectory one (`Analysis/Coupling`, `Analysis/RunCoupling`), from which
`lem:numlattice` is proved. This structure is kept only as a record of the
alternative; **any theorem proved from it would be vacuous**, and none is.
-/

end Ttc
