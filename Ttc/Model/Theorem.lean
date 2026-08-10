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

Audit path — `Model/`, then stop, **four files**: `Model/Prelude` (the vocabulary),
`Model/ProblemSetting` (what `Vol(F)` is and what `(1 ± ε)` means),
`Model/Pseudocode` (`alg:ttc` and its preprocessing, transcribed line by line, ending
in the algorithm's output `Ttc.ttcAlgOutput` and its oracle-free form `Ttc.ttcRun`),
this file.

`TTC` takes three inputs, so three inputs is what this statement takes: the formula
`F = (atoms, φ)`, the accuracy `ε`, the confidence `δ`.  **Eleven binders**

```
atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos
```

and among them there is no interpretation, no parameter block, no converter, no
oracle, no precision, no inscribed-ball data — and no boundedness hypothesis.

## What the guarantee is stated over: one law, one point, both halves

    ttcLaw atoms φ ε δ hε0 hε1 hn hφ hpos
      : Measure ((ℕ → Space n) × (ℕ → Fin (ttcIndex …) → ℕ))

— **the law of one run of `TTC(F, ε, δ)`**, defined and documented in `Monadic/Program`
as the composition–product of the volume oracle's coin law with the coin-indexed
trajectory kernel: draw the volume coins `c`, then draw the sample trajectory `t` from
the coupled family at the rates *that* draw produced.  A point of its space is a whole
run `p = (c, t)`, and **both conjuncts below speak about the same `p`** — the accuracy
half about the output `Ttc.ttcRun … p.1 p.2`, the running-time half about the charged
cost `Ttc.ttcCost … p.1 p.2`.

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

### Why the running-time half is `∀ p` and not `All[p ← ttcLaw; …]`

Deliberate, and it is the **stronger** statement.  nfalean writes its running-time half
as `All[r ← countNFAM …; …]`, where `All` is `PMF.support p ⊆ {x | E x}`.  It is tempting
to read that as "no exceptional outcome exists at all", i.e. as strictly stronger than
almost-everywhere.  **It is not**: for a `PMF`,
`support p ⊆ {x | E x}` ⟺ `∀ x, ¬E x → p x = 0` ⟺ `p.toOuterMeasure {¬E} = 0`, so the
support form and the a.e. form *coincide*.  A discrete law has no room for a
large-but-null exceptional set.

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

The cost bound we can actually prove holds at *every* point of the space, null or not.
Writing it as `All[…]` or `AllS[…]` would throw that away to look more like nfalean.  So
it is a plain `∀ p`, and it is strictly stronger than all of them.  The measure-side
counterpart, for the paired law, is `Ttc.ttcPairLaw_cost_le_of_terminates`, stated over
`Set.range (Ttc.ttcPair …)` — "every run the program can produce" — which is the honest
analogue of nfalean's shape.

## What is measured: `Model/Pseudocode`'s own `Ttc.ttcRun`

The accuracy conjunct says, in one term,

```
Pr[ p ← ttcLaw …;
    ttcRun atoms φ ε δ … p.1 p.2 ∈ relErr ε (volSol (atomSet atoms) φ) ]
  ≥ 1 − δ
```

`Ttc.ttcRun` is **the algorithm on one run**, and it takes **no oracle argument**.
`Model/Pseudocode` defines `Ttc.ttcAlgOutput` as `Ttc.run` — the fold of `alg:ttc`
lines 22–46 — over the preprocessed formula's cubes
`Ttc.toDNFd (Ttc.preprocess atoms φ)`, at the computed parameter block
`Ttc.inputParams` (lines 17–20) and the computed precision `Ttc.runPrec` (line 17),
with the estimate divided by `qⁿ` for the dilation `q = Ttc.runScale` (lines
A10–A13); its last argument is the **oracle bundle**, because `alg:ttc` line 24's
`Vol_ED` and line 43's `GenerateSamples` are calls into one — exactly as the paper
prints them.  `Ttc.ttcRun` is that term with the bundle **filled in** from the run
`(c, t)` itself: `Vol_ED` is the Monte-Carlo estimator `Ttc.mcVol` at the volume
coins `p.1`, and `thin`, `Pois`, `GenerateSamples` are the read-offs
`Ttc.trajThin`, `Ttc.trajPois`, `Ttc.trajGen` of the sample trajectory `p.2`, over
the lattice enumeration `Ttc.latticeEnum` — every one of them defined in
`Model/Pseudocode`.

Nothing about that bundle is assumed: it is a closed term, and
`Ttc.ttcRun_eq_ttcAlgOutput` (`Exec/Api`) proves — by `rfl` — that
`Ttc.ttcRun … p.1 p.2` is `Ttc.ttcAlgOutput … (Ttc.ttcOracleBundle … p.1 p.2)`.  So
`Ttc.ttcRun` is not a rename: it is the same term, and the machine check
`#modelClosure Ttc.ttcRun` (`Audit/ClosureCheck`) confirms that every `Ttc` constant
it unfolds to is defined under `Ttc/Model/`.  The target is the **user's own**
`Vol(F)`, at the original `φ`: neither preprocessing pass moves it.

The runtime conjunct is stated in the folded vocabulary of `Exec/Api` —
`Ttc.ttcTerminates`, `Ttc.ttcCost`, `Ttc.ttcNumCubes`, `Ttc.ttcThresh` — each of
which unfolds by `rfl` to the corresponding term of `Runtime.lean`
(`Ttc.ttcTerminates_def`, `Ttc.ttcCost_def`, `Ttc.ttcNumCubes_def`,
`Ttc.ttcThresh_def`).

## What the statement names

This file is *one declaration* — no `def`, no auxiliary lemma — and the theorem's
type names, outside `Model/`, only

```
ttcLaw  ttcIndex
preprocess_bdd
ttcTerminates  ttcCost  ttcThresh  ttcNumCubes
```

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

`Ttc.preprocess_bdd` is the odd one out, and it is a **proof term**, not a quantity:
`Bornology.IsBounded (sol (atomSet atoms) (preprocess atoms φ))`, derived from `hφ`
and `hpos` alone (`Exec/BddFromPos`).  It appears because `Ttc.Params` bundles five
*proof* fields, so `Ttc.inputParams` — and hence `Ttc.ttcAlgOutput` — cannot be
applied without it.  `Model/Pseudocode`'s docstring, "The divergence from the
reference layout", states this plainly and says what removing it would cost.

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
* **Running time.**  For **every** point `p` of the run space — not merely almost every
  one; see the module docstring on why this is deliberately `∀ p` and not `All[…]` —
  `alg:ttc`'s charged cost `Ttc.ttcCost` (one `Vol_ED` call plus one `GenerateSamples`
  draw per returned point) is at most `Ttc.ttcNumCubes · (C_vol + C_sample · Ttc.ttcThresh)`,
  that is `m · (C_vol + C_sample · Thresh)`, under `Ttc.ttcTerminates`.

Eleven binders, all conditions on the input; only `hφ` and `hpos` are shape
hypotheses.  `AUDIT.md` §1h has the three preprocessing steps, what is known about
`hφ`/`hpos`, why `hbdd` is derived, and the definitional closure.  Correctness, not
efficiency: both oracle routes are exponential in `n`. -/
theorem ttc_volume_estimate {A : Type*} {n : ℕ}
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    -- (accuracy) `alg:ttc`'s own output on the run `p`, with no oracle argument, is
    -- within `(1 ± ε)·Vol(F)` with probability `≥ 1 − δ`
    (1 - δ ≤
      Pr[p ← ttcLaw atoms φ ε δ hε0 hε1 hn hφ hpos;
        ttcRun atoms φ ε δ hε0 hε1 hn (preprocess_bdd atoms φ hφ hpos) p.1 p.2
            ∈ relErr ε (volSol (atomSet atoms) φ)])
    ∧
    -- (running time) `alg:ttc`'s charged cost, on **every** run `p`, under
    -- `Ttc.ttcTerminates` — pointwise, not almost everywhere
    (∀ p : (ℕ → Space n) × (ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ),
      ∀ cVol cSample thr : ℕ,
      (thr : ℝ) = ttcThresh atoms φ ε δ hε0 hε1 hn hφ hpos →
      ttcTerminates atoms φ ε δ hε0 hε1 hn hφ hpos p.1 p.2 →
      ttcCost atoms φ ε δ hε0 hε1 hn hφ hpos p.1 p.2 cVol cSample
        ≤ ttcNumCubes atoms φ * (cVol + cSample * thr)) :=
  ⟨ttc_accuracy_single_measure atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1,
    fun p => (ttc_volume_api atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos).2 p.1 p.2⟩

#print axioms ttc_volume_estimate

end Ttc
