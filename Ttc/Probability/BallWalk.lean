/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.MarkovChains.Continuous.ConvexBodyMixing

/-!
# `GenerateSamples`' chain: the lazy ball walk and how long it is run for

The two Markov-chain objects the sampler is: the law of the lazy ball walk after `t`
steps, and the `t` it is run for.

**Vocabulary only.**  Two definitions, no `Prop`, nothing assumed.  Nothing here
mentions the target measure: `Ttc.ballWalkLaw` is an iterate of a Markov kernel, and only
`Ttc.tvLe_ballWalkLaw_inflated` (`Sampler/Construct`) ties it to the uniform distribution.
Nothing mentions `TTC` or a formula either — the ambient space is spelled
`EuclideanSpace ℝ (Fin n)` rather than `Ttc.Space n` so that this file needs nothing of
ours (the two are the same type; `Ttc.Space` is a reducible `abbrev`).

`Ttc.mixSteps` is filed here, with the chain, rather than with the arithmetic: its body is
a closed form in reals, but what it *names* is a number of steps of that chain — it is
`Arlib.MarkovChains.conductanceMixingTime`, whose meaning is fixed by
`Arlib.MarkovChains.tv_le_of_conductance_decay` (`√M (1 − φ²/2)^t ≤ eps` from that step
onwards), at the conductance floor
`Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope` produces.  Its only consumer is
`Ttc.kv97ContLaw`, where it is the time argument of a law.

This file used to be part of `Model/Prelude`; see `Ttc/Audit/ClosureCheck.lean` for why
the audit surface is `Ttc/Model/` **together with** `Ttc/Probability/`.
-/

namespace Ttc

open MeasureTheory

/-- **The step count.**  `Arlib.MarkovChains.conductanceMixingTime` at the conductance
floor that `Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope` produces for a body of
diameter `Dm` containing a ball of radius `γ`, walked with step `δ` from an `Mw`-warm
start, to reach total-variation accuracy `eps`. -/
noncomputable def mixSteps (n : ℕ) (γ Dm δ Mw eps : ℝ) : ℕ :=
  Arlib.MarkovChains.conductanceMixingTime Mw
    (min ((γ / (γ + Dm)) ^ n / 32)
      ((1 / 2 : ℝ) ^ n / Dm * ((γ / (γ + Dm)) ^ n) ^ 2 * δ / (128 * (n : ℝ)))) eps

/-- **The law of the lazy ball walk on `K` with step `δ` after `t` steps from `mu0`.**

This is the sampler's output law.  It is an iterate of a Markov kernel — nothing about
the target `Arlib.uniformOn volume K` appears in it. -/
noncomputable def ballWalkLaw {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ)
    (mu0 : Measure (EuclideanSpace ℝ (Fin n))) (t : ℕ) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  Arlib.MarkovChains.iterate (Arlib.MarkovChains.lazy (Arlib.MarkovChains.ballWalk K δ)) mu0 t

end Ttc
