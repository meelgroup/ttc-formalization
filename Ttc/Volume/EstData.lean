/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Model.ProblemSetting

/-!
# `Volume/EstData`: what `Vol_ED` **computes**, with no probability space of ours

This file holds the *data* half of the constructed volume oracle: the definitions
`Ttc.mcVol` unfolds to, and nothing else.  Every theorem about them — measurability,
unbiasedness, the Bernoulli variance, Chebyshev — stays in `Ttc/Volume/MonteCarlo.lean`,
which imports this file.

## Why the split exists

`Ttc.mcVol` is the number `alg:ttc` line 24 reads.  For `Ttc.run` to *call* it rather than
receive it as an oracle field, the definitions below must be reachable from
`Ttc/Model/Pseudocode.lean`, which is the audit surface.  They now are: this file imports
only `Ttc.Model.ProblemSetting` (hence only `Ttc.Model.Prelude` and Mathlib), so
`Model/Pseudocode` may import it without a cycle.

## Data versus law: what had to move, and what did not

The obstruction was `Ttc.MonteCarlo.nSamp`, the sample count.  It is `⌈(ε²·p·q)⁻¹⌉ + 1`
where `q` is the hitting probability, and `q` used to be *defined* as
`(Ttc.MonteCarlo.coinLaw n (target K)).toReal` — a measure this development constructs
(`Arlib.uniformOn` on the unit ball).  Defining the sample count that way would have put
our own probability space inside the algorithm's definitional closure.

It does not have to be.  The hitting probability has a closed form in Lebesgue volume
alone — `Ttc.MonteCarlo.hitData` below — and the two agree exactly whenever `K` really is
enclosed by `Metric.ball 0 (rad K)`, which is `Ttc.MonteCarlo.hit_eq_hitData`
(`Volume/MonteCarlo.lean`), the hypothesis `Ttc.MonteCarlo.correct` establishes for itself.
So `nSamp` is defined from `hitData`, the coin law appears only in the *theorems*, and the
definitional closure of `Ttc.mcVol` contains **no measure constructed by this development**.

**What could not be separated, and is not claimed to be.**  `MeasureTheory.volume` — that
is, Mathlib's Lebesgue measure on `ℝⁿ` — stays in the closure, in three places, and each is
genuinely needed at definition time:

* `Ttc.MonteCarlo.scale`, the constant the returned estimate is multiplied by, is the volume
  of the enclosing ball;
* `Ttc.MonteCarlo.target` tests the coins against `MeasureTheory.toMeasurable volume K`
  rather than `K`, which is what makes `est_meas` hold for *every* `K`
  (see `Volume/MonteCarlo.lean`'s docstring);
* `Ttc.MonteCarlo.hitData` is a ratio of two Lebesgue volumes.

A volume estimator whose output does not mention volume would be a different object.  What
the split buys is precisely that the measure in the closure is *Mathlib's*, not one of ours
— which is the distinction `Ttc/Audit/ClosureCheck.lean` draws.

## Contents

`Ttc.roundBody`, and then, in `Ttc.MonteCarlo`: `rad`, `target`, `hitData`, `scale`,
`nSamp`, `ind`, `score`, `est`; finally `Ttc.mcVol`.
-/

namespace Ttc

open MeasureTheory Pointwise

/-- **The normalisation `Vol_ED` is called on.** `K` moved so that its inscribed
ball becomes the unit ball at the origin: the image of `K` under
`y ↦ γ⁻¹ · (y − c)`.

Cousins–Vempala Theorem 1.1 (`Ttc.VolumeAlgorithm`, `Volume/Oracle`) speaks only about
bodies containing the unit ball, whereas `Ttc.TtcProb.ball_subset` supplies a ball
of radius `γ̂` about a centre that is not the origin. This is the change of
variable that closes the gap; that it does is *proved* in `Ttc/Volume/Bridge.lean`
(`Ttc.VolumeAlgorithm.of_ball`), not assumed.

Lives here rather than in `Model/Prelude` because it is this oracle's
normalisation, not vocabulary of the paper's problem — and here rather than in
`Volume/Oracle` because `Ttc.mcVol` is built from it and this file is the part of the
construction `Model/Pseudocode` may import. -/
noncomputable def roundBody {n : ℕ} (c : Space n) (γ : ℝ) (K : Set (Space n)) :
    Set (Space n) := γ⁻¹ • ((-c) +ᵥ K)

end Ttc

namespace Ttc.MonteCarlo

open MeasureTheory

variable {n : ℕ}

/-! ## The enclosing radius

`Ttc.MonteCarlo.correct` hands over exactly three facts about `K` — convex, contains the
unit ball, finite volume — and `Arlib.Convexity.exists_closedBall_superset_of_convex` turns
them into a radius (`Ttc.MonteCarlo.exists_ball_superset`).  `rad` picks one by choice,
totally: it is defined (as `1`) even when no radius exists, so that `est` is a total
function and `est_meas` needs no hypothesis. -/

open scoped Classical in
/-- A radius enclosing `K`, chosen classically; `1` if there is none. -/
noncomputable def rad (K : Set (Space n)) : ℝ :=
  if h : ∃ R : ℝ, 0 < R ∧ K ⊆ Metric.ball (0 : Space n) R then h.choose else 1

/-! ## The target set

`target K` is the set the *coins* are tested against: the measurable hull of `K`, pulled
back along `x ↦ rad K • x`.  It is measurable for **every** `K`
(`Ttc.MonteCarlo.measurableSet_target`), which is what makes
`Ttc.VolumeAlgorithm.est_meas` — quantified over all `K`, measurable or not — provable. -/

/-- The measurable hull of `K`, in unit-ball coordinates. -/
noncomputable def target (K : Set (Space n)) : Set (Space n) :=
  (fun x : Space n => rad K • x) ⁻¹' toMeasurable volume K

/-! ## The estimator -/

/-- **The hitting probability, as arithmetic**: `Vol K / Vol(ball 0 (rad K))`, written out
in Lebesgue volume alone.

This is the *data* form of the chance that one rescaled coin lands in `K`.  The *law* form
is `Ttc.MonteCarlo.hit`, `(coinLaw n (target K)).toReal`, and the two are equal exactly
when `K ⊆ Metric.ball 0 (rad K)` — `Ttc.MonteCarlo.hit_eq_hitData`, proved in
`Volume/MonteCarlo.lean`, where the enclosure hypothesis is available.

Only this form is used to *define* the sample count, so that the coin law stays out of the
algorithm's definitional closure; see this file's docstring. -/
noncomputable def hitData (K : Set (Space n)) : ℝ :=
  (rad K ^ n)⁻¹ * (volume K).toReal / (volume (Metric.ball (0 : Space n) 1)).toReal

/-- The volume of the enclosing ball, `Vol(ball 0 (rad K)) = (rad K)ⁿ · Vol(ball 0 1)`. -/
noncomputable def scale (K : Set (Space n)) : ℝ :=
  rad K ^ n * (volume (Metric.ball (0 : Space n) 1)).toReal

/-- The number of samples: `⌈(ε²·p·q)⁻¹⌉ + 1`, where `q = Ttc.MonteCarlo.hitData K` is the
hitting probability in its arithmetic form.  Noncomputable, and `Θ(Rⁿ/(ε²p))` — exponential
in `n`.  See the module docstring of `Ttc/Volume/MonteCarlo.lean`. -/
noncomputable def nSamp (K : Set (Space n)) (ε pf : ℝ) : ℕ :=
  ⌈(ε ^ 2 * pf * hitData K)⁻¹⌉₊ + 1

/-- The indicator of `target K`, as a function of one coin. -/
noncomputable def ind (K : Set (Space n)) : Space n → ℝ :=
  Set.indicator (target K) (1 : Space n → ℝ)

/-- The `i`-th sample's score: `1` if the `i`-th rescaled coin lands in `K`, else `0`. -/
noncomputable def score (K : Set (Space n)) (i : ℕ) : (ℕ → Space n) → ℝ :=
  fun ω => ind K (ω i)

/-- **The estimate.** `Vol(ball 0 (rad K)) · (#hits / N)`. -/
noncomputable def est (K : Set (Space n)) (ε pf : ℝ) (ω : ℕ → Space n) : ℝ :=
  scale K / (nSamp K ε pf : ℝ) * ∑ i ∈ Finset.range (nSamp K ε pf), score K i ω

end Ttc.MonteCarlo

namespace Ttc

open scoped Classical in
/-- **`Vol_ED`'s output, as a function of the volume oracle's coins.**

`Ttc.ttc_volume` carries `vol : Cube A → ℝ` together with a binder `volED_eq`
pinning it to `volAlg.est`.  With `volAlg` fixed to the *constructed* oracle
`Ttc.VolumeAlgorithm.monteCarlo`, `vol` is no longer a free function: it is this
term, and `volED_eq` becomes the theorem `Ttc.mcVol_eq` (`Exec/VolDischarge`).

Off the DNF the value is `0`; the algorithm never reads it (only `i ∈ D` is ever
queried), and totality is what lets the definition avoid a proof argument.

Defined here rather than in `Exec/VolDischarge` so that `Model/Pseudocode` can reach it:
this file imports only `Model/ProblemSetting`. -/
noncomputable def mcVol {A : Type*} {n : ℕ} (M : A → Set (Space n)) (D : DNF A)
    (cen : {c : Cube A // c ∈ D} → Space n) (γ ε' δ' : ℝ)
    (c : ℕ → Space n) (i : Cube A) : ℝ :=
  if hi : i ∈ D then
    γ ^ n * MonteCarlo.est (roundBody (cen ⟨i, hi⟩) γ (region M i)) ε' δ' c
  else 0

end Ttc

/-! ## Axiom audit

Every declaration of this file, checked transitively (`CLAUDE.md` §4).  Expect
`[propext, Classical.choice, Quot.sound]` throughout. -/

#print axioms Ttc.roundBody
#print axioms Ttc.MonteCarlo.rad
#print axioms Ttc.MonteCarlo.target
#print axioms Ttc.MonteCarlo.hitData
#print axioms Ttc.MonteCarlo.scale
#print axioms Ttc.MonteCarlo.nSamp
#print axioms Ttc.MonteCarlo.ind
#print axioms Ttc.MonteCarlo.score
#print axioms Ttc.MonteCarlo.est
#print axioms Ttc.mcVol
