/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Probability.Trajectory
import Ttc.Probability.Coins
import Ttc.Probability.BallWalk
import Ttc.Probability.Sampler

/-!
# `Ttc/Probability/`: the ambient randomness, and nothing else

The measures, kernels and densities `alg:ttc` draws from.  **None of these is a step of
the algorithm** — they are what its two coin sequences are *governed by*, and the law
whose mass function the level-`0` rates are read off.  `Model/Pseudocode` stays
pseudocode because they are here.

Since `Ttc.ttc` (`Model/Pseudocode`) is a `Measure` and `Ttc.ttc_volume_estimate`
(`Model/Theorem`) is a statement about that measure, this vocabulary is unavoidably part
of what the headline's *type* unfolds to.  That is why `Ttc/Audit/ClosureCheck.lean`
audits `Ttc/Model/` **together with** `Ttc/Probability/`, and why the contents of this
directory are held to a rule as strict as `Model/`'s: read that file's docstring before
adding anything here.

| file | contents | imports of ours |
| --- | --- | --- |
| `Probability/Trajectory` | `half`, `thinKernel`, `chainKernel`, `trajLaw`, and the two Markov-kernel instances Ionescu–Tulcea takes as instance arguments; then the five read-offs of a trajectory (`toMultiset`, `trajThin`, `trajPois`, `trajGen`, `padRow`) and the two contracts about them (`trajThin_le`, `card_trajGen`) | `ModelSupport` |
| `Probability/Coins` | `MonteCarlo.coinLaw`, `MonteCarlo.coins` | none |
| `Probability/BallWalk` | `mixSteps`, `ballWalkLaw` | none |
| `Probability/Sampler` | `kv97SampD`, `kv97ContLaw`, `e2eSampD` | `Model/Prelude` |

Two of the four files import Mathlib and `Arlib` only, so a reader may take them as
ambient background.  `Probability/Sampler` and `Probability/Trajectory` are the
exceptions, and deliberately so: the sampler's mass function is indexed by the cubes of a
DNF and normalised over a cube's own region, so `Ttc.Cube`, `Ttc.DNF`, `Ttc.region`,
`Ttc.latticeScale` and `Ttc.intLattice` are in its statement; and a *read-off* of a
trajectory is a `Multiset (Ttc.Space n)`, so `Probability/Trajectory`'s second half needs
`Model/Prelude` through `ModelSupport`.  Their own docstrings say what making them
independent would cost.

**Definitions, and two contracts.**  Sixteen `def`s and two `instance`s, plus exactly two
`Prop`s: `Ttc.trajThin_le` and `Ttc.card_trajGen`, the sub-multiset and cardinality
contracts `Ttc.Oracles` demands of the trajectory read-offs.  They are here because a
theorem cannot be stated upstream of the definition it is about and `Ttc.algOracles`
needs them at elaboration time, so they cannot go downstream either; both are invisible
to `Ttc/Audit/ClosureCheck.lean`, which enters a theorem only through its type.  No
hypothesis bundle, no `@[simp]` lemma, nothing assumed.  Every *other* property of these
objects — that the kernels are Markov, that the walk mixes, that the estimator is
unbiased, that the loops terminate almost surely — is proved *outside* this directory
(`Process/Thinning`, `Process/Truncation`, `Coupling/Family`, `Sampler/Construct`,
`Volume/MonteCarlo`), and none of it is needed to read the statement.

**What is *not* here.**  The canonical linear description of the dilated cubes —
`Ttc.facetOf`, `Ttc.canonAm`, `Ttc.canonBv`, `Ttc.canonDm`, `Ttc.canonRfac` — is convex
geometry read off the formula, not randomness, and stays in `Model/Prelude` with the rest
of the geometry vocabulary.  Filing it here would make the directory's name a lie.
-/
