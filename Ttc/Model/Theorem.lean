/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Monadic.MeasurePr
import Ttc.Monadic.Program

/-!
# The main theorem: `thm:volumettc` + `thm:runtime` for `TTC(F, ε, δ)`

The **statement layer**, and nothing else: this file contains one theorem,
`Ttc.ttc_volume_estimate`, and no definition, no auxiliary lemma and no proof to work
through — the accuracy half is `Ttc.ttc_accuracy_single_measure` (`Monadic/EventMeasurable`)
and the running-time half is the second component of `Ttc.ttc_volume_api` (`Exec/Api`),
read at `p.1` and `p.2`.

Audit path — `Model/`'s **four files**: `Model/Prelude` (the vocabulary),
`Model/ProblemSetting` (what `Vol(F)` is and what `(1 ± ε)` means),
`Model/Pseudocode` (`alg:ttc` and its preprocessing, transcribed line by line, ending
in the algorithm's output `Ttc.ttcAlgOutput`, its oracle-free form `Ttc.ttcRun`, and the
law `Ttc.ttc` of the pair `(estimate, cost)`), this file — **and `Ttc/Probability/`'s
four**, which hold the ambient random objects the two coin sequences are governed by.

The surface is two directories rather than one because `Ttc.ttc` is a `Measure`: the
ambient randomness is part of what this theorem's type unfolds to wherever it is filed.
`Ttc/Probability/` is bounded in exchange — definitions only (eleven `def`s and two
Markov-kernel instances, no `Prop`, no hypothesis bundle, nothing assumed) — and
`Ttc/Audit/ClosureCheck.lean` checks both directories together, fails the build on
drift, and says why.

`TTC` takes three inputs, so three inputs is what this statement takes: the formula
`F = (atoms, φ)`, the accuracy `ε`, the confidence `δ`.  **Eleven binders**

```
atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos
```

and among them there is no interpretation, no parameter block, no converter, no
oracle, no precision, no inscribed-ball data — and no boundedness hypothesis.

## What the guarantee is stated over: one object, one run, both halves

    ttc atoms φ ε δ cVol cSample : Measure (ℝ × ℕ)

— **`TTC(F, ε, δ)` itself**, defined in `Model/Pseudocode` as

    (MonteCarlo.coins n).bind fun c =>
      (trajLaw (algRates atoms φ ε δ c)).map fun t =>
        (ttcRun atoms φ ε δ c t, algCost atoms φ ε δ c t cVol cSample)

— draw the volume coins `c`, then the sample trajectory `t` at the rates *that* draw
produced, and read off the pair `(estimate, cost)`.  **Both conjuncts below speak about
the same `r`**: the accuracy half about `r.1`, the running-time half about `r.2`.  This
mirrors `ApproxNFA.countNFAM A n ε δ : PMF (ℝ × ℕ)`.

`Measure.bind`/`Measure.map` rather than `⊗ₘ`, deliberately: the `⊗ₘ` spelling would be
definitionally equal to `Ttc.ttcPairLaw` but would drag `Ttc.ttcTrajKernel` and its
measurability proof into `Model/`.  The price is that the bridge
`Ttc.ttc_eq_ttcPairLaw` (`Monadic/Program`) is a three-step proof rather than `rfl` — and
that bridge is what makes `ttc` an honest name for the run rather than a fresh definition
nothing connects to the analysis.

**Why `cVol` is now a number and `cSample` is still a binder.**  `alg:ttc` line 24's
`Vol_ED` and line 43's `GenerateSamples` are oracle calls whose per-call cost the paper
never fixes, so `Ttc/Runtime.lean` leaves them parametric.  Both used to be binders here.
`cVol` no longer is: it is the explicit natural

```
⌈(γ⁻¹ · diam (Sol(preprocess atoms φ) at the dilated atoms) + 1)ⁿ / (ε'² · δ')⌉₊ + 1
γ  = algGamma atoms φ ε δ                        -- `q·γ̂`, the dilated inscribed radius
ε' = (algBlock atoms φ ε δ).epsPrime  = ε/12
δ' = (algBlock atoms φ ε δ).deltaPrime = δ/(5m)
```

and `Ttc.ttcVolCoins_le_ttcVolPrice` (`Exec/PriceList`) proves it dominates the number of
coins the constructed `Vol_ED` reads **at every cube of the DNF** — uniformly, because
each cube's region is inside the solution set (`Ttc.region_subset_sol`) and
`Metric.diam` is monotone, so `diam (region M i) ≤ diam (sol M φ)` for all `i`.  Nothing
in the substitution is an assumption: `Ttc.MonteCarlo.nSamp_roundBody_le`
(`Volume/RadBound`) is the per-cube closed form and it is unconditional, since
`Ttc.MonteCarlo.rad` is the *infimum* of the enclosing radii.

**`cVol` is exponential in the dimension, and the conjunct below must not be read as a
polynomial bound.**  The `(…)ⁿ` is hit-and-miss Monte Carlo's rejection factor: sampling
uniformly from a ball of radius `R` to hit a body of inradius `1` needs `Θ(Rⁿ)` draws.
The price is `Θ((diam/γ)ⁿ / (ε'²·δ'))` and no rearrangement makes it smaller.

`cSample` **remains a binder, and that is a finding rather than an omission.**
`Ttc.mixSteps_le` (`Exec/SampleBound`) is a per-cube closed form, `Θ(4ⁿ·(γ+Dm)^{4n}/γ^{4n})`
— also exponential in `n` — but it is evaluated at three quantities that move with the
cube: the inflated body's diameter, the warm-start ratio `Vol(P'ᵢ)/Vol(B)` and the TV
tolerance `ε'/(4·Vol(P'ᵢ))`.  A *uniform* price needs an upper bound on `Vol(P'ᵢ)`, the
volume of the Kannan–Vempala inflated dilated polytope, and this development proves none:
the only statement about that body's size is the *hypothesis* `hD` of
`Ttc.mixCost_le_mixSteps`, never discharged at the run's own cubes.  `Exec/PriceList`'s
docstring records the exact residue.

**Three undercounts stand, and a concrete `cVol` must not be read as denying them.**
`Ttc.kv97SampD`'s rejection rounds are unbounded and counted nowhere; `alg:ttc` lines
32–42's `while` loops are uncharged; and `Ttc.mixSteps` does not occur in `Ttc.ttcRun`'s
definitional closure at all — it enters through `Ttc.ttcRates`, the *law*, while
`GenerateSamples` is the read-off `Ttc.trajGen`.  So `cSample` prices the chain the
sampler's law is defined by, not steps the run takes.  A bound on an undercount is not a
bound on the count, and nothing here bounds a running time.

**There is no iterated integral.**  Earlier versions of this statement carried
`∫⁻ c, trajLaw (ttcRates … c) {t | …} ∂(MonteCarlo.coins n)` — outer over the volume
coins, inner the trajectory law at the rates that run produced — and so quantified the
two coin sequences separately, in two different places, in the two conjuncts.  Folding
it into one measure is `Ttc.lintegral_good_event_eq_compProd`, and it is not free: it
needs the good event measurable **jointly** in `c` and `t`, which is what
`Monadic/EventMeasurable` establishes (`Ttc.CountablyDetermined`, since `Ttc.run` folds
through a `Multiset (Space n)` state that carries no measurable structure and
`Ttc.absorbLevel` is an unbounded `Nat.sInf` search).

### Why a `Measure` and not a `PMF`

nfalean's `ApproxNFA.countNFAM` is an honest `PMF (ℝ × ℕ)` — its randomness is a finite
coin sequence — and its headline is stated in the `PMF` monad.  `Ttc.ttcLaw` cannot be:
`Ttc.MonteCarlo.coins` is `MeasureTheory.Measure.infinitePi` of the uniform law on a
Euclidean ball, an **atomless** measure on an uncountable space, so there is no `PMF`
whose `toOuterMeasure` it is.  This is a fact about the object, not a stylistic choice;
`Monadic/MeasurePr`'s docstring works through the consequences.  What does survive is
the Giry-monad structure: `Ttc.ttcTrajKernel` is a Markov kernel, `⊗ₘ` is the monadic
bind, and `Ttc.ttcLaw` is a probability measure.

`Pr[p ← μ; E p]` below is `Monadic/MeasurePr`'s notation for `(μ {p | E p}).toReal` —
Mathlib's measure at Mathlib's `setOf`, read as a real.  Nothing of ours is named by it.

### The running-time half: `All[…]`, and what it did and did not cost

Earlier versions of this statement wrote the running-time half as a pointwise
`∀ p, … → ttcTerminates … → …`, because the `All[…]` form was **not provable**: off the
absorption guard `Ttc.absorbLevel` degenerates (`Nat.sInf ∅ = 0`), the exit level defaults
to the entry level, and the count handed to `GenerateSamples` ranges over all of
`ℕ → Fin k → ℕ`, so no constant bounds it.  The plan of record was to interrupt-truncate
the algorithm, as nfalean does.

**That turned out to be unnecessary.**  `Ttc.trajLaw_ae_terminates` (`Process/Truncation`)
shows the loops terminate `trajLaw`-almost surely: under `trajLaw θ` the level-`j` count
vector is `⨂ₛ Pois(θₛ/2ʲ)`, and *both* summands of the guard are read off that vector, so
at any level with `ω j = 0` the guard reads `Thresh < 0 + 0` — refuted by `0 ≤ Thresh`,
whatever the cube, state, entry level or sample coins.  `Pr[ω j ≠ 0] ≤ Λ/2ʲ` is summable.
One geometric series; no union bound over cubes and no Chernoff.
`Ttc.ae_ttcLaw_ttcTerminates` transports it, and `Ttc.all_ttcPairLaw_cost_le` is the
guard-free bound this conjunct is.

The pointwise form is still **false** without truncation, and remains so; what changed is
that the a.e. form no longer needs it.  The design for a truncated variant is recorded in
`Process/Truncation` and deliberately not applied — with the warning that its sentinel
would have to be `-1`, not `0`: `0` is a legitimate output of `Ttc.run`
(`Findings/SmallBody`), and at `ε = 1` we have `0 ∈ relErr 1 V`, so a `0` sentinel would
let interrupted runs count as *correct*.

**What `All[…]` is here, precisely.**  nfalean's is `PMF.support p ⊆ {x | E x}`, which is
tempting to read as "no exceptional outcome exists at all", i.e. strictly stronger than
almost-everywhere.  **It is not**: for a `PMF`,
`support p ⊆ {x | E x}` ⟺ `∀ x, ¬E x → p x = 0` ⟺ `p.toOuterMeasure {¬E} = 0`, so the
support form and the a.e. form *coincide*.  A discrete law has no room for a
large-but-null exceptional set.  Ours is `∀ᵐ`, and by
`Ttc.all_ttcPairLaw_iff_atoms` the same collapse holds for `Ttc.ttc` — it is a pushforward
along a countably determined map, hence carried by a countable set.  So this conjunct is
the exact analogue of nfalean's, not a weakening of it.

**Two strictly stronger statements are kept**, since this one is not the sharpest in every
direction: `Ttc.ttcPairLaw_cost_le_of_terminates` bounds the cost over
`Set.range (Ttc.ttcPair …)` — every run the program can produce, no exceptional set at all
— and `Ttc.all_ttcPairLaw_cost_le_of_terminates` carries the sharper `max`-shaped
`Ttc.ttcThresh` instead of the sum below.  They are **incomparable** with this conjunct:
they are sharper in the bound, weaker in the hypothesis.  The constant here is at most a
factor 2 off on the threshold term (`max a b ≤ a + b`, both branches kept, both proved
nonnegative), which is the price of dropping the guard.

A support-based quantifier is in fact available to us: `AllS[x ← μ; E x]`
(`Monadic/MeasurePr`) is `μ.support ⊆ {x | E x}` over Mathlib's topological
`Measure.support`, and both carriers here — `(ℕ → Space n) × (ℕ → Fin k → ℕ)` and
`ℝ × ℕ` — get every instance it needs by `infer_instance`.  An earlier version of this
docstring claimed that support "does not carry full mass"; **that was wrong**, and is
refuted in `Monadic/MeasurePr`: `Measure.measure_compl_support` needs only
`[HereditarilyLindelofSpace]`, which second countability supplies here, so the support is
conull automatically.

The real reason is the one that survives: `AllS` is still **strictly weaker** than the
pointwise `∀ p`, and for *this* measure the gap is real rather than hypothetical.
`Ttc.MonteCarlo.coinLaw` is `Arlib.uniformOn volume (Metric.ball 0 1)`, so `ttcLaw` is
supported on a proper closed subset of the carrier and is not `IsOpenPosMeasure` — the
hypothesis under which `AllS` and `∀` would coincide (`allS_iff_forall`).  Restating the
runtime half as `AllS[…]` would therefore genuinely discard the claim at coin sequences
leaving the unit ball.  `Monadic/MeasurePr` proves both gaps are strict, by
counterexample rather than by prose: `exists_all_and_not_allS` and
`exists_allS_and_not_forall`, giving `∀ ⟹ AllS ⟹ All` with both arrows strict.

The same collapse happens for **our** law, for a structural reason rather than by
analogy: `Ttc.ttcPairLaw` (`Monadic/Program`) is a pushforward along a *countably
determined* map, so it is carried by a countable set, and
`Ttc.ae_map_iff_atoms_of_countablyDetermined` (`Monadic/Pair`) — hypothesis named, not
silent — gives `∀ᵐ r, E r ↔ ∀ r, ttcPairLaw {r} ≠ 0 → E r`, instantiated for this law as
`Ttc.all_ttcPairLaw_iff_atoms`.  So a support-style quantifier over the pair law buys
nothing over `All[…]` either.

**So which does the conjunct below use?  `All[…]`.**  An earlier version of this
statement — and of this paragraph — used a pointwise `∀ p` guarded by
`Ttc.ttcTerminates`, on the reasoning that the guarded pointwise form is strictly
stronger than any of the three quantifiers above.  That reasoning was sound but is now
beside the point: once `Ttc.ae_ttcLaw_ttcTerminates` made the guard discharageable, the
`All[…]` form became available **with no termination hypothesis at all**, and an
unconditional a.e. bound is not comparable to a conditional pointwise one.

Two strictly sharper statements are kept for readers who want them, and they are
**incomparable** with the conjunct below — sharper in the bound, weaker in the
hypothesis: `Ttc.ttcPairLaw_cost_le_of_terminates`, over `Set.range (Ttc.ttcPair …)`
("every run the program can produce", no exceptional set whatever), and
`Ttc.all_ttcPairLaw_cost_le_of_terminates`, which carries the `max`-shaped
`Ttc.ttcThresh` rather than the sum spelled out below.  The constant here is at most a
factor 2 off on the threshold term — `max a b ≤ a + b`, both branches kept and both
proved nonnegative — and that factor is exactly what dropping the guard cost.

## What is measured: `Model/Pseudocode`'s own `Ttc.ttcRun`

The accuracy conjunct says, in one term,

```
Pr[ r ← ttc atoms φ ε δ cVol cSample;
    r.1 ∈ relErr ε (volSol (atomSet atoms) φ) ]
  ≥ 1 − δ
```

and `r.1` is `Ttc.ttcRun … c t` at the run `ttc` drew.

`Ttc.ttcRun` is **the algorithm on one run**, and it takes **no oracle argument**.
`Model/Pseudocode` defines `Ttc.ttcAlgOutput` as `Ttc.run` — the fold of `alg:ttc`
lines 22–46 — over the preprocessed formula's cubes
`Ttc.toDNFd (Ttc.preprocess atoms φ)`, at the computed parameter block
`Ttc.inputParamsTotal` (lines 17–20) and the computed precision `Ttc.runPrec` (line 17),
with the estimate divided by `qⁿ` for the dilation `q = Ttc.runScale` (lines
A10–A13); its last argument is the **oracle bundle**, because `alg:ttc` line 24's
`Vol_ED` and line 43's `GenerateSamples` are calls into one — exactly as the paper
prints them.  `Ttc.ttcRun` is that term with the bundle **filled in** from the run
`(c, t)` itself: `Vol_ED` is the Monte-Carlo estimator `Ttc.mcVol` at the volume
coins `p.1`, and `thin`, `Pois`, `GenerateSamples` are the read-offs
`Ttc.trajThin`, `Ttc.trajPois`, `Ttc.trajGen` of the sample trajectory `p.2`, over
the lattice enumeration `Ttc.latticeEnum` — `Ttc.mcVol` and `Ttc.latticeEnum` in
`Model/Pseudocode`, the three trajectory read-offs in `Ttc/Probability/Trajectory`
beside the law they read.

Nothing about that bundle is assumed: it is a closed term, and
`Ttc.ttcRun_eq_ttcAlgOutput` (`Exec/Api`) proves — by `rfl` — that
`Ttc.ttcRun … p.1 p.2` is `Ttc.ttcAlgOutput … (Ttc.ttcOracleBundle … p.1 p.2)`.  So
`Ttc.ttcRun` is not a rename: it is the same term, and the machine check
`#modelClosure Ttc.ttcRun` (`Audit/ClosureCheck`) confirms that every `Ttc` constant
it unfolds to is defined under `Ttc/Model/` **or `Ttc/Probability/`** — 152 and 5
respectively, the five being the trajectory read-offs.  The target is the **user's
own** `Vol(F)`, at the original `φ`: neither preprocessing pass moves it.

The runtime conjunct names no `Exec/Api` vocabulary at all.  Earlier versions were
stated in the folded terms `Ttc.ttcTerminates`, `Ttc.ttcCost`, `Ttc.ttcNumCubes` and
`Ttc.ttcThresh`; the bound is now **explicit arithmetic** in `ε`, `δ` and
`m = |Ttc.toDNFd (Ttc.preprocess atoms φ)|`, following
`ApproxNFA.approxNFA_countNFA`, which writes its `49924·n·(n+1)·m³·log(…)` out for the
same reason.  `Ttc.ttcComplexity` (`Exec/Complexity`) is the same expression under a
name, and `Ttc.ttcCost_le_ttcComplexity` is where it is proved; neither is named here.

## What the statement names

This file is *one declaration* — no `def`, no auxiliary lemma — and the theorem's type
names **nothing defined outside the audit surface**.  That is not a claim about filing:
`#modelClosureOfType Ttc.ttc_volume_estimate` (`Audit/ClosureCheck`) walks the type's
transitive definitional closure and fails the build unless every `Ttc` constant in it is
defined under `Ttc/Model/` or `Ttc/Probability/`.  The declarations the type mentions
directly are

```
ttc   relErr   volSol   atomSet   toDNFd   preprocess
```

all in `Model/`, plus Mathlib's `Real.log` and the numerals.

**No proof term is named.**  Every name above is a quantity, applied to
`(atoms, φ, ε, δ)` — and, for `Ttc.ttc`, the charging convention `(cVol, cSample)` —
and nothing else; the theorem's hypotheses appear only as its own binders, never inside
the terms it measures.  `Ttc.preprocess_bdd`, a proof term earlier versions applied
inside the accuracy conjunct, is gone: `Ttc.ttcParamsTotal` decides the five side
conditions classically, so the algorithm is a closed function of the data.

The first line is **the run and its law**: the law of a single run of the algorithm
and the index the sample coins range over.  The **oracle bundle is gone** from the
statement — the accuracy conjunct is stated over `Ttc.ttcRun`, and
`Ttc.ttcRun_eq_ttcAlgOutput` (`Exec/Api`, by `rfl`) is what makes that legitimate.
`Ttc.ttcIndex` survives only in the *runtime* conjunct, and
`Ttc.algIndex_eq_ttcIndex` (`Exec/Api`, by `rfl`) is its `Model/` form.  `ttcLaw`
absorbs what used to be three separate names in this statement (`Ttc.trajLaw`,
`Ttc.ttcRates`, `Ttc.MonteCarlo.coins`) — those are now inside `Monadic/Program`'s
definition, which is where the probability space belongs: `alg:ttc` treats `Vol_ED`
and `GenerateSamples` as oracle calls, so the *construction* that discharges them is
proof content, not statement content.  The last line is the runtime conjunct's four
folded names, each with its `rfl` lemma in `Exec/Api`.

`Ttc.preprocess_bdd` used to be named here, and it was a **proof term** rather than a
quantity: `Ttc.Params` bundles five *proof* fields, so `Ttc.inputParams` — and hence
`Ttc.ttcAlgOutput` — could not be applied without a boundedness proof.  It is gone.
`Ttc.inputParamsTotal` (`Model/Pseudocode`) decides the five side conditions
classically instead of taking them, so the block, the run, and every quantity above
are functions of the data alone; `Ttc.inputParamsTotal_eq_inputParams` shows the
block is unchanged wherever this theorem's own hypotheses hold.

The property is machine-checkable in one `run_cmd`: walk
`Ttc.ttc_volume_estimate`'s type past its binders, collect
`Expr.getUsedConstants`, and keep those whose defining module starts with `Ttc`
but not `Ttc.Model`.  `Ttc.ttcRun_eq_ttcEstimate` (`Exec/Api`, by `rfl`) is the
bridge in the other direction, identifying the measured term with the run's estimate;
`Ttc.ttcLaw_def` (`Monadic/Program`, by `rfl`) is the corresponding bridge for the law.

The fact that this theorem's proof is a pair of bare applications, with no rewriting,
is the structural check that the names above name what they claim to name: a wrong
abbreviation is a build error, not a silent divergence.

## What is assumed

Four things an auditor needs and this file deliberately does **not** restate, so
that it stays the statement:

* the **definitional closure** — what the named terms unfold to outside `Model/`
  (the `Exec/Api` auxiliaries, the constructed oracle bundle, the constructed
  sampler, the parameter block, and the run's probability space, now reached through
  `Ttc.ttcLaw`);
* the **three preprocessing steps** the headline certifies `alg:ttc` *plus*, and
  which of them change the algorithm's behaviour;
* the **two residual hypotheses** `hφ` and `hpos`, and what is known about each;
* that **`hbdd` was derived**, not dropped.

All four are in [`AUDIT.md`](../../AUDIT.md) §1h, which is written to be read
alongside this file.  `Model/Pseudocode`'s `A1`–`A13` block is the pseudocode for
the preprocessing itself.
-/

namespace Ttc

open MeasureTheory Set
open Ttc.Monadic

/-- **`thm:volumettc` + `thm:runtime`.**  `TTC` is run on `F = (atoms, φ)` at accuracy
`ε` and confidence `δ`, and **both halves speak about the same run** `p = (c, t)` drawn
from the same law `Ttc.ttcLaw` — the volume coins, then the sample trajectory at the
rates that draw produced.  No iterated integral.

* **Accuracy.**  `Pr[ TTC(F, ε, δ) ∈ (1 ± ε)·Vol(F) ] ≥ 1 − δ`, the probability being
  the one `Ttc.ttcLaw` assigns.  The output is `Model/Pseudocode`'s own
  `Ttc.ttcRun` — the fold of `alg:ttc` lines 22–46 at the computed parameter block and
  precision, rescaled by `1/qⁿ`, with `Vol_ED` and `GenerateSamples` read off the run
  itself rather than taken as an oracle argument — and the target is the **user's own**
  `Vol(F)`.
* **Running time.**  Almost every run — `All[…]`, i.e. `∀ᵐ`, and with **no termination
  hypothesis**: the absorption loops halt `Ttc.ttc`-almost surely
  (`Ttc.ae_ttcLaw_ttcTerminates`), so the guard earlier versions carried is discharged
  rather than assumed.  `alg:ttc`'s charged cost (one `Vol_ED` call plus one
  `GenerateSamples` draw per returned point) is at most
  `m · (C_vol + C_sample · (Θ + 1))`, written out as explicit arithmetic in `ε`, `δ` and
  `m = |toDNFd (preprocess atoms φ)|` so that the conjunct names nothing this file's
  reader cannot find — with `C_vol` **substituted** by the explicit
  `⌈(γ⁻¹·diam(Sol) + 1)ⁿ / (ε'²·δ')⌉₊ + 1`, which is **exponential in the dimension `n`**.
  `C_sample` is still a binder; the module docstring says exactly what blocks it and
  which three undercounts a concrete number here does *not* repair.  See the module
  docstring for which quantifier this is and what it is not.

Eleven binders, all conditions on the input; only `hφ` and `hpos` are shape
hypotheses.  `AUDIT.md` §1h has the three preprocessing steps, what is known about
`hφ`/`hpos`, why `hbdd` is derived, and the definitional closure.  Correctness, not
efficiency: both oracle routes are exponential in `n`. -/
theorem ttc_volume_estimate {A : Type*} {n : ℕ}
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)
    (cSample : ℕ) :
    -- (accuracy) the estimate returned is within `(1 ± ε)·Vol(F)` with probability `≥ 1 − δ`
    (1 - δ ≤
      Pr[r ← ttc atoms φ ε δ
            (⌈((algGamma atoms φ ε δ)⁻¹
                  * Metric.diam
                      (sol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ)) + 1) ^ n
                / ((algBlock atoms φ ε δ).epsPrime ^ 2
                    * (algBlock atoms φ ε δ).deltaPrime)⌉₊ + 1) cSample;
        r.1 ∈ relErr ε (volSol (atomSet atoms) φ)])
    ∧
    -- (running time) **almost every** run — `All[…]` is `∀ᵐ`, so a null exceptional set
    -- is permitted — and, unlike earlier versions, under **no termination hypothesis**:
    -- charged at most `m·(c_vol + c_samp·(Θ + 1))`, with `c_vol` the explicit
    -- `⌈(γ⁻¹·diam(Sol) + 1)ⁿ / (ε'²·δ')⌉₊ + 1` — **exponential in `n`**
    (All[r ← ttc atoms φ ε δ
            (⌈((algGamma atoms φ ε δ)⁻¹
                  * Metric.diam
                      (sol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ)) + 1) ^ n
                / ((algBlock atoms φ ε δ).epsPrime ^ 2
                    * (algBlock atoms φ ε δ).deltaPrime)⌉₊ + 1) cSample;
      (r.2 : ℝ) ≤
        ((toDNFd (preprocess atoms φ)).length : ℝ)
          * (((⌈((algGamma atoms φ ε δ)⁻¹
                    * Metric.diam
                        (sol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ))
                      + 1) ^ n
                  / ((algBlock atoms φ ε δ).epsPrime ^ 2
                      * (algBlock atoms φ ε δ).deltaPrime)⌉₊ + 1 : ℕ) : ℝ)
              + (cSample : ℝ)
              * (41472 * Real.log (30 / δ) / (ε ^ 2 * (12 - ε))
                  + 15 * (Real.log (15 / (2 * δ))
                      + Real.log ((toDNFd (preprocess atoms φ)).length))
                  + 1))]) := by
  rw [ttc_eq_ttcPairLaw]
  refine ⟨ttc_accuracy_pairLaw atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1
    (⌈((algGamma atoms φ ε δ)⁻¹
          * Metric.diam (sol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ))
            + 1) ^ n
        / ((algBlock atoms φ ε δ).epsPrime ^ 2
            * (algBlock atoms φ ε δ).deltaPrime)⌉₊ + 1) cSample, ?_⟩
  have h := all_ttcPairLaw_cost_le atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1
    (⌈((algGamma atoms φ ε δ)⁻¹
          * Metric.diam (sol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ))
            + 1) ^ n
        / ((algBlock atoms φ ε δ).epsPrime ^ 2
            * (algBlock atoms φ ε δ).deltaPrime)⌉₊ + 1) cSample
  simpa only [ttcComplexity_def] using h

#print axioms ttc_volume_estimate

end Ttc
