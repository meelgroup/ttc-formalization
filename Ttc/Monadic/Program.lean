/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Monadic.EventMeasurable

/-!
# `Monadic/Program`: `TTC`'s run, as one law on one space

`Ttc.ttc_accuracy_single_measure` (`Monadic/EventMeasurable`) states the accuracy
guarantee over the composition–product

```
MonteCarlo.coins n ⊗ₘ ttcTrajKernel …
```

— the volume oracle's coins, then the trajectory law at the rates *that* draw
produced.  This file gives that measure a name, `Ttc.ttcLaw`, so that the headline
`Ttc.ttc_volume_estimate` can state **both** of its conjuncts about a single point
`p = (c, t)` of a single space, drawn from a single law: no iterated integral, and
no pair of separately-quantified coin sequences.

`Ttc.ttcLaw` is the analogue of nfalean's `ApproxNFA.countNFAM`, with one honest
difference recorded in `Monadic/MeasurePr`'s docstring and repeated here: ours is a
`MeasureTheory.Measure`, not a `PMF`.  `Ttc.MonteCarlo.coins` is
`MeasureTheory.Measure.infinitePi` of the uniform law on a Euclidean ball — atomless
on an uncountable space — so there is no `PMF` whose `toOuterMeasure` it is, and the
`PMF` monad is simply unavailable.  What survives is the Giry-monad structure:
`Ttc.ttcTrajKernel` is a genuine Markov kernel (`Monadic/Kernel`), so `⊗ₘ` is the
monadic bind of a probability measure with it, and `Ttc.ttcLaw` is again a
probability measure (`Ttc.instIsProbabilityMeasureTtcLaw`).

Three declarations, no proof content: `Ttc.ttcLaw`, its `rfl` lemma
`Ttc.ttcLaw_def`, and the `IsProbabilityMeasure` instance.
-/

namespace Ttc

open MeasureTheory ProbabilityTheory

section Law

variable {A : Type*} {n : ℕ} (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)

/-- **The law of one run of `TTC(F, ε, δ)`**: a measure on pairs
`p = (volume coins, sample trajectory)`.

The composition–product of the volume oracle's coin law `Ttc.MonteCarlo.coins` with
the coin-indexed trajectory kernel `Ttc.ttcTrajKernel` — that is, draw the volume
coins `c`, then draw the trajectory from the coupled family at the rates `c`
produced.  Everything the algorithm reads on a run is a function of `p`: the oracle
bundle is `Ttc.ttcOracleBundle … p.1 p.2`, the output is
`Ttc.ttcAlgOutput … (that bundle)`, and the charged cost is `Ttc.ttcCost … p.1 p.2`.

This is what makes `Ttc.ttc_volume_estimate`'s two conjuncts statements about *the
same run*, and it is why that theorem has no iterated integral. -/
noncomputable def ttcLaw :
    Measure ((ℕ → Space n) × (ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ)) :=
  MonteCarlo.coins n ⊗ₘ ttcTrajKernel atoms φ ε δ hε0 hε1 hn hφ hpos

/-- **What `Ttc.ttcLaw` is**, by `rfl`: the composition–product of the volume coins
with the coin-indexed trajectory kernel.  This is the identification that lets
`Ttc.ttc_accuracy_single_measure` be quoted verbatim as the headline's accuracy
conjunct. -/
theorem ttcLaw_def :
    ttcLaw atoms φ ε δ hε0 hε1 hn hφ hpos
      = MonteCarlo.coins n ⊗ₘ ttcTrajKernel atoms φ ε δ hε0 hε1 hn hφ hpos := rfl

/-- **A run's law is a probability measure.**  `Ttc.MonteCarlo.coins` is one
(`Ttc.MonteCarlo.instIsProbabilityMeasureCoins`) and `Ttc.ttcTrajKernel` is Markov
(`Ttc.isMarkovKernel_ttcTrajKernel`), so Mathlib's instance for `⊗ₘ` applies. -/
instance instIsProbabilityMeasureTtcLaw :
    IsProbabilityMeasure (ttcLaw atoms φ ε δ hε0 hε1 hn hφ hpos) := by
  rw [ttcLaw_def]
  infer_instance

end Law

#print axioms ttcLaw
#print axioms ttcLaw_def
#print axioms instIsProbabilityMeasureTtcLaw

end Ttc
