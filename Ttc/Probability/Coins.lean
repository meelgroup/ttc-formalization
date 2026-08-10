/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Probability.Independence.InfinitePi
import Arlib.Probability.UniformOn

/-!
# The volume oracle's coin space

`Vol_ED` (`alg:ttc` line 24) is a Monte-Carlo estimator; its randomness is a countable
i.i.d. sequence of uniform draws from the unit ball of `ℝⁿ`.

**Vocabulary only.**  Two definitions, no `Prop`, nothing assumed.  Neither mentions
`TTC`, a formula or a convex body — the ambient space is spelled
`EuclideanSpace ℝ (Fin n)` rather than `Ttc.Space n` precisely so that this file needs
nothing of ours (the two are the same type; `Ttc.Space` is a reducible `abbrev`).
Independence of the coordinates (`ProbabilityTheory.iIndepFun_infinitePi`), measurability
of the estimator, unbiasedness and Chebyshev are all downstream, in
`Volume/MonteCarlo.lean`.

This file used to be part of `Model/Prelude`; see `Ttc/Audit/ClosureCheck.lean` for why
the audit surface is `Ttc/Model/` **together with** `Ttc/Probability/`.
-/

namespace Ttc.MonteCarlo

open MeasureTheory

/-- **One coin**: the uniform distribution on the unit ball of `Ttc.Space n`. -/
noncomputable def coinLaw (n : ℕ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)

/-- **All the coins**: a countable i.i.d. sequence of uniform draws from the unit ball.

This is the `Ω`/`μ` of `Ttc.VolumeAlgorithm.monteCarlo`.  It is the infinite product
measure `MeasureTheory.Measure.infinitePi`; independence of the coordinates is
`ProbabilityTheory.iIndepFun_infinitePi`. -/
noncomputable def coins (n : ℕ) : Measure (ℕ → EuclideanSpace ℝ (Fin n)) :=
  Measure.infinitePi (fun _ : ℕ => coinLaw n)

end Ttc.MonteCarlo
