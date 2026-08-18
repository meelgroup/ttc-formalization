# How to audit this formalisation

`lake build` being green and `#print axioms` returning
`[propext, Classical.choice, Quot.sound]` proves that the development has **no
holes**. Neither proves that it states the **right theorem about the right
object**. That check is human-only, and this file is designed to let you make it
in a few minutes without reading a single hard proof.

**No line numbers appear on this page, on purpose.** Earlier versions carried
~180 `#L` anchors and most of them drifted within a day. Everything below names a
*file* and a *declaration*; use your editor's go-to-definition, or `grep -n` for
the name. Every name on this page was checked to exist in the compiled
environment; §5 has the probe that re-checks them all in one pass.

> **Two deliberate exceptions**, both in §0a–§0d, both because there is no
> declaration name to point at: **§0d**, whose subject is stale *docstring prose*,
> and the tables in **§0a/§0b**, which anchor freshly landed declarations whose
> names are not yet load-bearing anywhere else. Expect those numbers to drift and
> re-`grep` the name, which is always given alongside.

The vocabulary, the pseudocode and the problem statement are in
[`Ttc/Model/`](Ttc/Model/) — **four files** (the audit surface also includes
[`Ttc/Probability/`](Ttc/Probability/)'s four short files, since the
headline is a statement about a `Measure`; see §1b):
[`Prelude`](Ttc/Model/Prelude.lean) (the vocabulary),
[`ProblemSetting`](Ttc/Model/ProblemSetting.lean) (what `Vol(F)` is and what
`(1 ± ε)·b` means), [`Pseudocode`](Ttc/Model/Pseudocode.lean) (`alg:ttc` and the
preprocessing, transcribed line by line, together with the parameter block the
algorithm computes) and [`Theorem`](Ttc/Model/Theorem.lean) (**one theorem, and
nothing else** — no `def`, no auxiliary lemma, and a proof that is a single
application). Everything *proved* about `Vol_ED` was moved out to
[`Ttc/Volume/Bridge.lean`](Ttc/Volume/Bridge.lean) to keep that true.

**Re-run `ls Ttc/Model/` rather than trusting the previous sentence.** This page
has more than once named a file count the directory did not have, in both
directions, and the count is the cheapest thing on the page to re-check.

> **`Model/Theorem` states the input-level theorem, not the bundle one.**
> [`Ttc.TtcProb.volume_estimate`](Ttc/Estimate.lean), whose type names the bundle's
> *assumed* oracle field `T.O` and its *assumed* precision field `T.ρ`, still exists
> and is still load-bearing, but it lives in
> [`Ttc/Estimate.lean`](Ttc/Estimate.lean) as proof content. What `Model/Theorem`
> states is [`Ttc.ttc_volume_estimate`](Ttc/Model/Theorem.lean) — the same
> guarantee over `TTC`'s own inputs `(atoms, φ, ε, δ)`, with **no oracle argument**
> (the bundle the run reads is the closed term `Ttc.algOracles`, in
> `Model/Pseudocode`) and **no precision argument** (every occurrence is
> `P.precision gammaHat`, i.e. `GetPrecision`'s output). §1 reads the bundle type;
> §1e reads the headline.

> **`Model/` is not the whole *development*, and reading only it understates the
> result.** The strongest statement, [`Ttc.ttc_volume_final`](Ttc/Exec/Final.lean),
> lives **outside** `Model/`, because its hypothesis list is what is left after
> several of `Model/`'s assumptions have been *constructed away*. §1d is about it
> and §1c about the oracle-free statement it is assembled from. This is a claim
> about strength, not about the audit surface — see the next paragraph, which is
> about the surface and points the other way.

**Where the `Model/` boundary is drawn, and that a machine now checks it.**
`Model/Theorem`'s type names **only** `Model/` definitions, and this is checked
rather than asserted: `#modelClosureOfType Ttc.ttc_volume_estimate`
([`Ttc/Audit/ClosureCheck.lean`](Ttc/Audit/ClosureCheck.lean)) walks the headline's
type through every `def` body it reaches and **fails the build** if any `Ttc`
constant in that closure is defined outside `Ttc/Model/`. At the time of writing it
reports **201 `Ttc` constants, 0 outside `Model/`**; the direct names in the type
are ten, likewise all in `Model/`. Three companion invocations do the same for
`Ttc.ttcAlgOutput`, `Ttc.ttcRun` and `Ttc.ttc`. So the sentence "open `Model/` and
every constant the headline means is defined in front of you" is now a build-time
invariant, not a filing convention.

**Three things that check does *not* say**, each of which this page has at some
point stated as though it did:

* **It is not about imports.** `Model/Theorem` imports `Monadic/MeasurePr` and
  `Monadic/Program`, and hence transitively the development, for the
  `Pr[…]`/`All[…]` notation the statement is written in and for the bridge lemma
  its proof applies. Notation is not a constant, which is how the closure stays
  clean while the import graph does not. There is **no** closed system
  `Prelude → ProblemSetting → Pseudocode → Theorem → Mathlib`; do not claim one.
* **It is not about proofs.** `closureAux` never walks a theorem's *value*, so no
  proof term appears in any closure report. That is the right notion for auditing a
  statement — a proof may construct the product measure space, whereas a statement
  that *names* it means something different — but the reports are silent about what
  the proofs use. §5's dependency walk is the check for that.
* **It was not achieved by shrinking the statement.** The probability spaces the
  headline's type names — the sample-coin law `Ttc.trajLaw` and the volume-coin law
  `Ttc.MonteCarlo.coins` — are still named; they were **moved into** the audit
  surface, along with the canonicalisation data and the constructed sampler's law.
  `Model/` therefore now *does* import the probability and convex-geometry
  development it is the front of (through `Arlib`), which is the price paid, and it
  is the opposite trade from the one the reference layout makes: nfalean's
  `ApproxNFA/Model/Theorem.lean` names `(countNFAExec A n ε δ).P.Pr` and lets
  `countNFAExec` sit outside its `Model/`.

> **Where exactly each of those constants lives is in motion**, and this page
> should not be read for it. The `Model/` boundary has been re-cut several times in
> a day — a `Ttc/ModelSupport.lean` for carrier-generic bookkeeping and a migration
> of the thinning kernels into `Arlib` were both in flight while this was written.
> `grep`, or run `#closureReportOfType`, rather than quoting a filename from here.
> The **rule** is stable and is what to hold this layout to: a declaration belongs
> in `Model/` exactly when the statement's meaning depends on it, and belongs
> outside when it does not.

The definitional closure — what those `Model/` names unfold to, and what is
therefore in the trusted base — is §1h, and it is the larger of the two things to
read before quoting the statement.

---

## 0. The oracle-replacement work (2026-08-11) — read this before §1 if you came for it

A large body of work landed on 2026-08-11 aimed at **replacing both oracles**: the
volume oracle by Cousins–Vempala Theorem 1.1 (arXiv:1409.6011), and the sample
oracle by Lovász–Vempala Theorem 1.1 (*Hit-and-Run from a Corner*). If you are
auditing that, the four human-only checks for it are here; §§1–5 below still
describe the **existing, unconditional** TTC capstones, which are untouched.

**The single most important thing to understand: nothing was replaced
destructively.** Both original paths remain, and both remain the unconditional
ones:

| Oracle | Original path — still present, still unconditional | New path — conditional |
| --- | --- | --- |
| Volume | `Ttc.mcVol`, `Ttc.VolumeAlgorithm.monteCarlo` — correct, **exponential in `n`** | `Ttc.ttc_accuracy_cousinsVempala` (`Ttc/Exec/CVBackend.lean`), through `VolumeAlgorithm.cousinsVempalaOfRuns` |
| Sample | `Ttc.kv97SamplerOfBallWalk` — `law_tv` is a **theorem** (`mixesWithin_lazy_ballWalk_polytope`), step count `2^Θ(n)·log(…)` | `Ttc.kv97SamplerOfHitAndRun` (`Ttc/Sampler/ConstructHitAndRun.lean`) — `law_tv` from an **assumed** `HitAndRunTheorem11Input` |

**The two new entry points are the declarations to read.** For the volume side,
`Ttc.ttc_accuracy_cousinsVempala`; for the sample side,
`Ttc.kv97SamplerOfHitAndRun`. Read their *types*. Note that the generalisation
underneath the volume one is definitional, not a parallel copy —
`Ttc.volOfAlg_monteCarlo`, `Ttc.volGoodOf_monteCarlo` and
`Ttc.Box.bxTtcProbAlg_eq` are all `rfl`, which is the cheapest possible evidence
that the existing path was not disturbed.

Two further honesty notes on the volume entry point, both in its docstring: the
`1 − δ` is at a **fixed good coin** (integrating the coin out costs a further
`δ/4`, and that integration is *not* performed), and the `hω` binder hides a
**search** cost — `Ttc.exists_volGood_coin` certifies inhabitation only. There is
also **no joint CV witness**: the `monteCarlo` bundle is witnessed jointly and
unconditionally, but the CV one only degenerately, blocked on `big`.

So the honest one-line summary is: **the replacements exist as conditional entry
points alongside retained unconditional ones**, not as substitutions. A green
build over the new path certifies the *reduction*, not the algorithm.

**What is genuinely assumed, and who owns it.** In descending order of depth:

* **`hLS` / `hLSs`** — Lovász–Simonovits 1993 Corollary 1.5 (conductance → TV).
  Binders of `Arlib/MarkovChains/Continuous/HitAndRunMixing.lean`.
  ~~**This is the one binder owned by nobody.**~~ **Corrected 2026-08-12, and read
  §0c before quoting this bullet.** `hLS` is **discharged** for a reversible kernel
  with non-negative spectrum (`Arlib.MarkovChains.ls_of_hasNonnegSpectrum`), and in
  particular for any **lazy** chain from reversibility alone
  (`Arlib.MarkovChains.ls_lazy`), both in
  `Arlib/MarkovChains/Continuous/ConductanceToTV.lean`, from Cheeger's hard
  direction (`Cheeger.lean`) and `L2Mixing.lean` — both of which predate the claim.
  It is **not** discharged for the *plain* hit-and-run kernel, and cannot be: `hLS`
  is outright **false** for a general reversible chain (the `Bool` swap-kernel
  counterexample), so that residue is a **paper error** — *Hit-and-Run from a
  Corner* §5 applies Cor. 1.5 to a non-lazy chain — and not a missing proof. The
  lazy repair costs a factor `2` in the conductance and `4` in the deadline.
  `hLSs`, the `s`-conductance form, is **provably unreachable** by this L2 route.
* **`hIso`** — Lovász–Vempala Theorem 2.1. **Known FALSE as stated**; see below.
* **`hloc`** — the Localization Lemma at the shape `thm:iso` needs.
  `Arlib.hloc_of_localization` reduces it to the localization stack; residuals are
  that stack's (C) continuity requirement and (F) `v ≠ 0`. **Since 2026-08-12 this
  is no longer on the critical path to `thm:iso`**: `Convexity/IsoOpenClosed.lean`
  and `Convexity/IsoIndicator.lean` prove `thm:iso` with **no localization binder at
  all**, by routing around the stack rather than through it. `hloc` remains open,
  and (C) remains an obstruction (§0b); it is just no longer what blocks the
  isoperimetric inequality. §0e.
* **`hsampler`** of `Ttc/Volume/CVEstimator.lean` — the CV phase ratios. Note the
  unclosed seam: `HitAndRunTheorem11Input.at_steps` yields `TVLe` to
  `Arlib.uniformOn`, **not** to `coolLaw`; uniform→Gaussian is CV §4's
  speedy/Metropolis machinery ~~and is not attempted~~. **Corrected 2026-08-12: it
  is attempted, and largely done.** `Arlib.GaussianCooling.coolLaw_eq_uniformOn_gaussianWeight`
  (`GaussianCooling/PhaseMeanRoute.lean:216`) proves `coolLaw` **is** the Gaussian-weighted
  uniform law unconditionally, and `MetropolisMixingUncond.lean` gives a mixing bound
  to exactly that law with no isoperimetry hypothesis. What stops it is not the
  machinery but the local-conductance floor those theorems carry, which §0e shows is
  contradictory on the cube for `n ≥ 3`.

**Non-vacuity — where it is weaker than you would like (check 4).** Three of the
new bundles have witnesses that are *inhabited but forced*, and each says so:

* `Ttc/Volume/CVEstimator.lean`'s witness scores are deterministic, so `hsampler`
  holds at `η = 0` — satisfiability, not a certificate about the paper's phases.
* `Ttc.exists_hitAndRun_binders_box` takes `H : HitAndRunTheorem11Input` as a
  hypothesis and **does not construct one**. It cannot: that structure *is* LV
  Theorem 1.1.
* `Arlib/Convexity/HlocFromLocalization.lean`'s witness is vacuous in `hLoc` — and
  this one is the interesting case, because the agent **proved the vacuity is
  forced**. `Arlib.hloc_antecedent_false_of_isoperimetry` shows `hloc`'s antecedent
  is the exact negation of `thm:iso`'s conclusion, so a "genuinely satisfied
  antecedent" witness **cannot exist**. That is a machine-checked impossibility
  result, and it is the only way to beat the existing witness rather than
  hand-tune it.

**Costs, quoted here so they need not be reassembled from three files (check 5).**

* `Ttc/Volume/CVEstimator.lean` needs `Θ(n·L⁴·log(1/p)/κ³)` samples — **worse than
  the paper's**. It establishes *accuracy*; it must **never** be quoted as
  establishing `O*(n³)`.
* ~~The `(1d-2)` discharge holds at `1/(2√3) ≈ 0.289`, not CV's `ln 2 ≈ 0.693`, so
  the separation threshold grows by `2√3·ln 2 ≈ 2.401`.~~ **Closed 2026-08-12 — see
  §0e.** `Arlib.oneDim_isoperimetry_gaussianFactor_sharp`
  (`Arlib/Convexity/OneDimSharp.lean:518`) proves `(1d-2)` at `√(2/π)/σ`, and
  `Arlib.log_two_le_sqrt_two_div_pi` (`:554`) is the machine-checked
  `ln 2 ≤ √(2/π)`, so the whole downstream stack runs at the paper's own `ln 2` and
  the `2.401` threshold penalty is gone.
* ~~`StarPolar.lean` proves KLS 3.5 at separation `δ/n`, **not** `δ/√n`, a `√n`
  loss.~~ **Superseded 2026-08-12 — the `√n` is recovered, and it is still not `n⁴`.**
  `Arlib.MarkovChains.kls_lemma35_at_sep_sqrt_dim` (`LensMin.lean`) proves the
  **`min` form** of KLS95 Lemma 3.5 at `δ/√n` at constant `1/40`, and
  `kls_lemma35_at_sep_sqrt_dim_sharp` (`OverlapSqrt.lean`) sharpens it to `1/8`, and
  `kls_lemma35_at_sep_sqrt_dim_quarter` (`LensSharp.lean`) to `1/4`.
  **The `√n` is real** — at a fixed kernel step it is exactly a factor `√n` in `Φ`
  (`speedy_sqrt_gain`, `DeltaCap.lean`) — **but `n⁴` still does not follow.** The two
  blockers this bullet used to name have both moved since it was written: a
  **Metropolis** overlap lemma at `δ/√n` now exists
  (`metropolisGaussian_overlap_sqrt_of_convex`, `MetropolisOverlapSqrt.lean`) and
  `hiso` is **discharged** for the density that lemma's conductance corollary uses
  (`OneDimSharp.lean`). What blocks `n⁴` now is a *different* fact, and it is a
  negative: the local-conductance floor those theorems need is **unsatisfiable on
  the cube** (`EllFloor.lean`). Read §0b's three layers and then §0e; do not stop at
  the first.
* The hit-and-run step count is polynomial in `n`, but `R²/r²` is unbounded for a
  general body; well-roundedness is *assumed* via binders, not achieved.

**The paper errors this work found** are collected in
[`CV-ROADMAP.md`](CV-ROADMAP.md) §0″. The one with audit consequences:
**LV Theorem 2.1 is false as stated** (its hypothesis constrains `h` only on
cross-pair chords while its conclusion integrates over all of `K`; for `n ≥ 2` the
chords can miss a positive-measure set). Consequence: any theorem still carrying
the *unrepaired* `hIso` is **vacuous** at `K = [0,4]²` and generically for `n ≥ 2`
— a green build over an empty guarantee. The repair is to add
`∀ x ∈ K, h x ≤ 1/3`, which the paper's own §4 application verifies.

**Two of this page's sibling docstrings were refuted** and are corrected in place:
the "`hIso` needs Borsuk–Ulam" claim in `HitAndRunConductance.lean`, and the
"Mathlib does not support polar decomposition" claim in `SpeedyOverlap.lean`
(Mathlib has it, *and this repo already wrapped it*). Treat confident-sounding
docstrings in this development as claims to re-check, not as findings. **§0d lists
the docstrings currently known to be stale and not yet corrected** — read it before
you believe any "this is not proved anywhere" sentence you meet in a `.lean` file.

---

## 0a. The goal-state capstone `Ttc.ttc_runtime_mn4` (2026-08-12)

> ## ⚠ THIS SECTION DOES **NOT** SAY THAT `TTC` RUNS IN `O(m·n⁴)` ⚠
>
> It says that a **charged-cost** statement of that shape now exists, over one run
> of a **different program** from the headline's, under **38 named hypotheses**, of
> which **five have no route to a proof anywhere in this repository**. Do not quote
> the exponent without the sentence that follows it.

### What the theorem is

[`Ttc.ttc_runtime_mn4`](Ttc/Exec/RuntimeMN4.lean) (`Ttc/Exec/RuntimeMN4.lean:409`)
is one theorem about **one run** of `Ttc.ttcPoly` — `alg:ttc` with the
Cousins–Vempala volume estimator swapped in for hit-and-miss Monte Carlo and the
hit-and-run law swapped in for the lazy ball walk — with two conjuncts over the
identical measure:

* **accuracy**, `1 − δ ≤ Pr[ r.1 ∈ (1 ± ε)·Vol(F) ]`, and
* **charged cost**, `All[ (r.2 : ℝ) ≤ m · n⁴ · (explicit factors) ]`,

with `Ttc.PolyComplexity.threshFactor` expanded to closed arithmetic in the bound
(`Ttc.ttc_runtime_mn4_threshFactor` proves the expansion is the definition, by
`rfl`), so no project `def` stands between the reader and the number.

This is **not** a new mathematical result. It is
`Ttc.ttcPoly_volume_estimate_cv` (`Exec/PolyAccuracy.lean:751`) renamed to a stable
goal-state name, with four accounting-error binders discharged — `hrfac`, `hep0`,
`hep1`, `heps1`, all four theorems of this repository at hypotheses the statement
already carried. `Ttc.ttc_runtime_mn4_tol_le_one` (`RuntimeMN4.lean:358`) is the
`heps1` discharge.

**One thing did change, and it is the substantive edit of 2026-08-12 (later in the
day).** The capstone no longer runs on `Ttc.cvVolAlg`. `Ttc.ttcPoly_volume_estimate_cv`
runs `Ttc.VolumeAlgorithm.cousinsVempalaOfRuns`, whose `hphase_mean` is an **equation**
`∫ g dν = chain(i+1)/chain(i)`; `Ttc.ttc_runtime_mn4` runs
`Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMean`
(`Ttc/Volume/CVInstantiate.lean:458`, new), whose `hphase_mean` is the **interval**
`∫ g dν ∈ (1 ± ε/(2(2+ε)m))·(chain(i+1)/chain(i))`. The two constructors produce the
same `Ω`, `μ` and `est` and establish the same `VolumeAlgorithm` guarantee, so both
conjuncts are unchanged; only the hypothesis is weaker. **The residual-hypothesis count
is unchanged at 38** — nothing was discharged. What changed is that one of the 38 is now
a statement something could in principle prove; see "the five with no route" below.

The one binder that had to move with it is `hphase_var`, now stated at
`Arlib.GaussianCooling.varBudget (ε/2)` rather than `varBudget ε`. `varBudget` is
monotone, so this is a **strictly stronger** hypothesis than the one it replaces. That
it is *forced* is a docstring argument (`CVInstantiate.lean:441-448`) resting on a real
lemma — `Arlib.GaussianCooling.exp_varBudget` (`GaussianCooling/Schedule.lean:186`),
`exp (varBudget κ) − 1 = κ²/5` — and on the accuracy split
`cousinsVempalaOfApproxMean` performs; **it is not itself a theorem**. There is no
declaration asserting "no split keeps the full `varBudget ε`".

### The binder count, printed by the build rather than asserted by this page

A `#binderProfile` elaborator at the foot of `RuntimeMN4.lean` walks the compiled
`ConstantInfo.type` and prints the counts at build time:

```
Ttc.ttc_runtime_mn4              68 raw ∀-binders = 64 explicit + 2 implicit + 2 instance
Ttc.ttcPoly_volume_estimate_cv   72 raw ∀-binders = 68 explicit + 2 implicit + 2 instance
```

Of the 64 explicit binders of `Ttc.ttc_runtime_mn4`, **26 are data** a caller
supplies and **38 are residual hypotheses**. `72` is the *raw* binder count of the
predecessor, not a hypothesis count.

```
raw ∀-binders                     68
  = explicit                      64
      of which data               26
      of which HYPOTHESES         38   ← the number to watch
  + implicit ({A}, {n})            2
  + instance                       2   (1 data, 1 trivial hypothesis)
```

### The 38, by group

The full table — every binder by name, its statement, and what discharges it — is
the module docstring's ledger in
[`Ttc/Exec/RuntimeMN4.lean`](Ttc/Exec/RuntimeMN4.lean), §"The ledger". It is the
authority; this is the summary a human needs to decide whether to read it.

| group | count | what it is |
| --- | --- | --- |
| **A** — FPRAS parameter range and input conditions | 7 | `hε0 hε1 hδ0 hδ1 hn hφ hpos`. Exactly what `Ttc.ttc_volume_estimate` also carries; conditions on the *user's* input, not debts. They will never go away |
| **B** — Lovász–Vempala Theorem 1.1 | 1 | `H : Ttc.HitAndRunTheorem11Input`. **Inhabited nowhere.** |
| **C** — Cousins–Vempala's residual sampler hypotheses | 5 | `hσ hg hgb` are conditions on caller-chosen schedule/score data; `hphase_mean` (now the **interval** form) and `hphase_var` (now at `varBudget (ε/2)`) are where the development actually stops |
| **D** — the hit-and-run warm start | 9 | `hrin hin hRout hout hsigma hM hSm` are caller-supplied start data; `hS` and `hdom` are Theorem 1.1's exceptional-start and `M`-warmness hypotheses |
| **E** — the sampler-side cost regime | 6 | `hR1 hgam0 hgamR hMw1` are regime conditions on free binders; `hMwB` is the warm-start bound; `hepn` is `1/2ⁿ ≤ ε'` |
| **F** — the volume-side (Gaussian cooling) cost regime | 10 | `hL hkap0 hkap1 hcc1 hcc hp0 hp1 hMc hed0 hed1`, all conditions on free binders of the statement. They say which regime the quoted `n⁴` is the cost in |

`7 + 1 + 5 + 9 + 6 + 10 = 38`.

### The five with no route to a proof — the honest core of the debt

~~six~~ **five, since the `hphase_mean` rewire of 2026-08-12.** The count of
*residual hypotheses* did not move; what moved is which of them are routeless.

| binder | what it assumes | where the repository stops |
| --- | --- | --- |
| `H : Ttc.HitAndRunTheorem11Input` | Lovász–Vempala 2005 Thm 1.1, hit-and-run mixing from a warm start | `Ttc/Sampler/HitAndRunTheorem11.lean`, a structure with one field `mixing`, **inhabited nowhere**. Its own proof would rest on LS93 Cor. 1.5 — see §0c |
| `hphase_var` | the second-moment bound for the phase score, at `varBudget (ε/2)` | `Ttc/Volume/CVInstantiate.lean:476`. A *transport* problem: CV §5.1's corresponding bound for the **ideal** estimator is proved unconditionally (`Arlib.GaussianCooling.fixed_var_bound_ratio_indicator`) |
| `hS` | the start gives the exceptional set little mass | Thm 1.1's exceptional-start hypothesis, in measure form |
| `hdom` | off the exceptional set the start is `M`-warm | same source |
| `hMwB` | `Mwarm ≤ (2R)ⁿ` — the warm-start bound | `Ttc/Exec/SampPriceHR.lean`: **nothing in this repository constructs a warm start at any `M`** |

**`hphase_mean` left this table, and it is worth reading why, because the reason is
not "it was proved".** In the *equation* form `Ttc.cvVolAlg` still carries
(`∫ g dν = chain(i+1)/chain(i)`) it was routeless **in principle**:
`Arlib.GaussianCooling.exists_tvLe_coolLaw_integral_phaseScore_ne`
(`Arlib/Convexity/GaussianCooling/PhaseMeanRoute.lean:518`) exhibits, for every
`ε ∈ (0,1]`, a probability measure `ν` at total variation `≤ ε` from `coolLaw` whose
phase-score integral is exactly `(1−ε)·(chain(i+1)/chain(i))` — so no
total-variation bound whatsoever, however strong, implies the equality. (Read that
theorem for what it is: a **counterexample to the implication "TV ⇒ the equation"**,
not a refutation of the equation, which holds exactly at `coolLaw` itself —
`Arlib.GaussianCooling.integral_phaseScore_coolLaw` — and at a degenerate kernel,
`exists_markovKernel_mixesWithin_coolLaw_exact`, at TV exactly `0` in one step.)

In the **interval** form the capstone now carries, it is routeless only *in
practice*: `Ttc.CV.sampledPhase_mean_mem_relErr` derives exactly that interval from
a TV guarantee `hTV` on a sampler for `Arlib.GaussianCooling.coolLaw`, and
`Ttc.VolumeAlgorithm.cousinsVempalaOfSampler` is the constructor that walks it.
What is missing is the sampler — a proved `hTV` at the accuracy the slack conditions
need. **That is the same open problem as row 1, not a separate impossibility.**

Everything else among the 38 is an input condition, a condition on caller-chosen
schedule/start data, a regime condition on a free binder of the statement, or —
in the single case of `hepn` — scheduled, with a named landing lemma.

### Five reasons this is not an `O(m·n⁴)` runtime claim

Reproduced from `RuntimeMN4.lean`'s own boxed warning, which is the authority.
Each is alone fatal to the unconditional reading.

1. **The charged cost is an undercount.** `Ttc.ttcPolyCost` charges **one unit per
   oracle call** and nothing else. It prices at **zero** the arithmetic inside a
   call, the sampler's rejection rounds, and `alg:ttc` lines 32–42's `while` loops.
   `r.2` is a call count with unit prices attached, not a running time.
2. **This is `Ttc.ttcPoly`, not `Ttc.ttc`.** `Model/Theorem.lean`'s headline runs
   `Ttc.algOracles`, and the prices *that* run can be shown to pay
   (`Ttc.ttcVolPrice`, `Ttc.ttcSampPrice`) are exponential in `n`. Swapping the
   oracles is a modelling choice — see the box at the head of `Exec/PricedHeadline.lean`.
3. **The accuracy conjunct is conditional** on all 38, most sharply on the five above.
4. **The warm start is assumed** (`hMw1`/`hMwB`).
5. **The `n⁴` needs a temperature-scale body (`R = O(σ)`).** In the Cousins–Vempala
   regime `R ≍ σ√n` the conductance floor forces a smaller step, the per-draw cost
   becomes `n⁴` and the total `n⁵`; and `Arlib.MarkovChains.exists_halfspace_max_lt`
   proves the obvious route to recovering the missing `√n` is **false**, not open.

### Non-vacuity (check 4) — reported, not papered over

* `Ttc.isProbabilityMeasure_ttcPoly` (`Exec/PolyRun.lean`) is the **measure-level**
  check: a `Measure.bind` of a non-measurable family is the zero measure, at which
  every `All[…]` holds vacuously and every `Pr[…]` is `0`. That instance rules it
  out at every `V`, hence at `Ttc.cvVolAlg`.
* `Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMeanWitness`
  (`Volume/CVInstantiate.lean:634`) shows the Cousins–Vempala hypothesis bundle
  **this theorem actually quantifies over** (rows 9–13) is jointly satisfiable. It
  is degenerate on purpose (zero phases), so it witnesses satisfiability and nothing
  else. It is *not* `Ttc.Box.exists_cvVolAlg_witness` (`Exec/CVBackend.lean:774`),
  which witnesses `Ttc.cvVolAlg`'s bundle — the one carrying the **equation** form
  of row 12, no longer the bundle the capstone runs on.
* **There is no full witness for `Ttc.ttc_runtime_mn4`, and there must not be a
  faked one.** One would have to inhabit `Ttc.HitAndRunTheorem11Input`, which is
  exactly the assumed content of LV Theorem 1.1. The witness on the
  *unconditional* path is `Ttc.ttc_volume_estimate_poly_two_cube`
  (`Exec/TheoremPoly.lean`), at exponential prices.

### Semantic `def`s (check 6)

`RuntimeMN4.lean` introduces **no `def` into the mathematical development**. It
contains exactly one `def` — `private partial def Ttc.Audit.binderProfileAux`, the
meta-level `Lean.Expr → Nat × Nat × Nat` binder counter behind `#binderProfile`. It
is not `Prop`-valued, asserts nothing, and appears in no statement.

### `Ttc.SamplerCost.samplePrice_le_quartic_eps` — the `hepn` binder's landing lemma

`Ttc/Exec/SampPriceEps.lean:183` proves the per-sample price bound **without** the
regime hypothesis `1/2ⁿ ≤ ε'`, by declining to absorb `log(1/ε')` into `n·log(2R)`:

```
samplePrice n γ R M ε' rfac  ≤  2⁶² · n³ · rfac · (R²/γ²) · (n·log(2R) + log(1/ε'))
```

**This is a per-consumer choice, not an unconditional elimination.** `samplePrice`
grows without bound as `ε' → 0`, so no `ε'`-free right-hand side can drop the
hypothesis; what the lemma does is move the dependence from a *hypothesis* into a
visible *term*. `Ttc.SamplerCost.samplePrice_le_quartic_of_eps`
(`SampPriceEps.lean:261`) recovers the old `ε'`-free shape from it, at `2⁶³` rather
than `2⁶²` — the factor `2` is exactly the `log(1/ε') ≤ n·log(2R)` step. A consumer
that prints `2⁶²` literally must print `2⁶³` instead.

**The capstone does not yet use it.** `Ttc.ttc_runtime_mn4` still carries `hepn`,
and `RuntimeMN4.lean` does not import `SampPriceEps.lean`. The ledger therefore
stays at **38**; the module docstring's §"The `hepn` swap" spells out the three-step
change that would take it to 37.

---

## 0b. The `δ/√n` results in `Arlib` — proved, and what still stands between them and a runtime

> ## ⚠ THE `√n` IS REAL — AND `n⁴` STILL DOES NOT FOLLOW ⚠
>
> KLS95 Lemma 3.5 and Cousins–Vempala's `cor:overlap` are now proved at separation
> `δ/√n` instead of `δ/n`, and at a **fixed kernel step** the conductance gain is
> exactly `√n`. What still blocks `n⁴` is **not** a step-size cap.
>
> ⚠ **This section was written before the isoperimetry work of later the same day,
> and two of its statements are superseded. Read §0e with it.** The "named missing
> piece" it identifies — a Metropolis overlap lemma at `δ/√n` — has landed
> (`MetropolisOverlapSqrt.lean`), and `hiso` is no longer a hypothesis of that
> lemma's conductance corollary (`OneDimSharp.lean`). What replaced them is a
> **negative**: the local-conductance floor those theorems need is unsatisfiable on
> the cube (`EllFloor.lean`). Everything below about the `√n` itself, and about
> `hcomp` for the *speedy* walk, still stands.

### What is proved

*Line numbers in this table drifted after it was written; the declaration names are
the authority — `grep -n` for them. Where a re-checked number is known it is given.*

| declaration | statement | hypotheses beyond the paper's |
| --- | --- | --- |
| `Arlib.MarkovChains.kls_lemma35_at_sep_sqrt_dim` (`Continuous/LensMin.lean:423`) | **KLS95 Lemma 3.5, `min` form, at separation `δ/√n`**, constant `1/40`: `vol(K ∩ B(u,δ) ∩ B(v,δ)) ≥ (1/40)·min{ℓ(u),ℓ(v)}·vol(δBₙ)` | **none.** `2 ≤ n`, `Convex ℝ K`, `u, v ∈ K`, `0 < δ`, `‖u−v‖ ≤ δ/√n`. No measurability of `K` (convex sets are null-measurable), no floor on `ℓ`, no `d_ℓ` comparability |
| `Arlib.MarkovChains.kls_lemma35_at_sep_sqrt_dim_sharp` (`Continuous/OverlapSqrt.lean:364`) | the same at constant **`1/8`** | none |
| `Arlib.MarkovChains.kls_lemma35_at_sep_sqrt_dim_quarter` (`Continuous/LensSharp.lean:569`) | the same at constant **`1/4`**, identical binders — **this is the sharpest of the three, and the one to quote** | none |
| `Arlib.MarkovChains.overlap_speedyWalk_sqrt_of_ell_comparable` (`Continuous/OverlapSqrt.lean:527`) | **`cor:overlap` at `δ/√n`**, constant **12**: `1 ≤ 12·(P_u(Tᶜ) + P_v(T))` | **one, and it is load-bearing** — `ℓ`-comparability, `d_ℓ(u,v) < 1/3`, written division-free. It is Cousins–Vempala's own hypothesis, but it is a hypothesis. The variant that actually discharges `hoverlap`, `…_of_ell_comparable_global` (`:556`), takes comparability **globally over `K`** and weakens the constant to `20` |
| `Arlib.MarkovChains.conductance_speedyGaussian_ge_of_ell_comparable` (`Continuous/OverlapSqrt.lean:669`) | `thm:speedyconductance` with `hoverlap` discharged: `Φ ≥ δ·log2/(640·σ·√n)` for `δ ≤ σ/(8√n)` | `hcomp` as above, **and `hiso`** — and §0e's discharge does **not** reach this one: it is proved for the Gaussian-times-log-concave density, whereas the speedy walk's stationary law is `1_K·ℓ` |
| `Arlib.MarkovChains.speedy_sqrt_gain` (`Continuous/DeltaCap.lean:299`) | at **one and the same kernel** `speedyWalk K δ`, the `δ/√n` bound is exactly `√n` times the `δ/n` one | none — pure arithmetic on the two conclusions |
| `Arlib.MarkovChains.metropolis_hfloor_forces_step_cap` (`Continuous/DeltaCap.lean:132`) | the Metropolis acceptance floor `hfloor` **caps** `δ ≤ (ln 20)·σ/√n ≈ 3σ/√n` once `σ√n ≤ R` | only hypotheses `conductance_metropolisGaussian_sharp_ge` already makes, plus `σ√n ≤ R` |
| `Arlib.MarkovChains.sup_bounds_agree_at_own_caps` (`Continuous/DeltaCap.lean:357`) | both bounds, each at **its own** maximal `δ`, equal `ln2/(5120·n)` | none — and see below for why this comparison is **not** the operative one |

**Do not write "the step is *forced* to `Θ(σ/√n)`" without the qualifier.** The
proved statement is one-sided: `metropolis_hfloor_forces_step_cap` is an **upper**
bound `δ ≤ (ln 20)·σ/√n`, and it carries the extra hypothesis `σ√n ≤ R`, which the
sharp Metropolis conductance theorem does not make. Nothing in `DeltaCap.lean`
concludes `… ≤ δ`. The companion `acceptance_factor_ge_of_step_le` (`:227`) runs
under the *opposite* radius hypothesis `R ≤ σ√n` and says only that at
`δ ≤ σ/(8√n)` the acceptance factor is `≥ e^{−1/4}`. The honest sentence is: the
floor caps the step at `≈ 3σ/√n`, and `σ/(8√n)` is feasible — so `Θ(σ/√n)` is the
operative *scale*, bounded above by proof and shown feasible by proof. The two ends
are a factor `≈ 24` apart and `hδσ` is **not** implied by the floor.

**The mechanism, in one sentence**, since it is what closed a gap the repository had
documented as needing "a genuinely different argument": pair a point behind `u` with a
point ahead of `v`; the sign conditions cancel the `t`-linear terms, so the midpoint's
excess over `δ` is **quadratic** (`t²/(4δ)`, i.e. `δ/(4n)` at `t = δ/√n`, not the
`δ/(2√n)` a bare triangle inequality gives), which a `(1 − 1/n)` homothety absorbs at
constant cost; then Brunn–Minkowski. `Arlib.MarkovChains.midpoint_mem_ball_inter`
(`LensMin.lean:109`) is the crux.

### What the `√n` does and does not buy — three layers, and do not stop at the first

`Arlib/MarkovChains/Continuous/DeltaCap.lean` exists to settle exactly this question,
and its answer has three layers. Reading only the first gets it backwards.

**Layer 1 — the two bounds, each at its own cap, agree.** Compare the two conductance
theorems as *statements*:

| theorem | cap on `δ` | conductance bound | at its own maximal `δ` |
| --- | --- | --- | --- |
| `conductance_speedyWalk_ge_of_convex` (`Continuous/StarPolar.lean:626`) | `δ ≤ σ/8` | `δ·log2/(640·σ·n)` | `log2/(5120·n)` |
| `conductance_speedyGaussian_ge_of_ell_comparable` (`Continuous/OverlapSqrt.lean:669`) | `δ ≤ σ/(8√n)` | `δ·log2/(640·σ·√n)` | `log2/(5120·n)` |

They are **identically equal**, and this is a theorem, not this page's arithmetic:
`Arlib.MarkovChains.sup_bounds_agree_at_own_caps` (`DeltaCap.lean:357`). It makes the
`√n` look illusory.

**Layer 2 — that comparison is an artifact, and the `√n` is real.** The `δ` of
`conductance_speedyGaussian_ge` (`SpeedyConductanceSharp.lean:320`) is an
**isoperimetric scale**, not a step size: that theorem takes the kernel `P` as a
parameter independent of its own `δ`. The two rows above are **one theorem at two
parameterizations** of it — `StarPolar.lean` instantiates at `δ_abs := δ/√n` with
kernel `speedyWalk K δ` (`speedyGaussian_reparam_cap`, `speedyGaussian_reparam_conclusion`),
`OverlapSqrt.lean` at `δ_abs := δ` with the *same* kernel. **Neither shrank any cap**;
both inherited `hδσ` from the abstract theorem. What differs is only which overlap
lemma each can supply. So:

* At **one and the same kernel step** `speedyWalk K δ`, the second bound is exactly
  `√n` times the first — `Arlib.MarkovChains.speedy_sqrt_gain` (`DeltaCap.lean:299`).
* The operative step is set by the **Metropolis acceptance floor**, not by these caps.
  `metropolis_hfloor_forces_step_cap` (`DeltaCap.lean:132`) shows `hfloor` forces
  `δ ≤ (ln 20)·σ/√n ≈ 3σ/√n` once `σ√n ≤ R`; at the nominal `δ = σ/8` the acceptance
  factor is `e^{−√n/8}` (`acceptance_floor_at_step_sigma_div_eight`) — exponentially
  small in `n`, and no `θ ≤ 1` compensates — while at `δ ≤ σ/(8√n)` it is `≥ e^{−1/4}`
  (`acceptance_factor_ge_of_step_le`). So `σ/√n` is the right scale.
* Evaluated at that operative step `δ = σ/(8√n)`: `Φ ≥ log2/(5120·n^{3/2})` on the old
  route (`speedy_old_bound_at_operative_step`) against `Φ ≥ log2/(5120·n)` on the new
  (`speedy_new_bound_at_operative_step`) — **a genuine factor `√n` in `Φ`, hence a
  factor `n` in the step count `1/Φ²`.**

**The step-size cap is therefore not the obstruction**, and any statement that the `√n`
"cancels" is wrong.

**Layer 3 — and `n⁴` still does not follow.** ⚠ **Both bullets below were true when
written and both have since been overtaken. Keep reading into §0e.**

* ~~**The `δ/√n` overlap lemma exists only for the *unfiltered* speedy walk.**~~
  `Arlib.MarkovChains.metropolisGaussian_overlap_of_convex`
  (`MetropolisConductanceSharp.lean:238`) concludes only for pairs at separation `δ/n`,
  which is why the sharp Metropolis theorem lands on `δ·log2/(640σn)`. ~~A Metropolis
  overlap lemma at separation `δ/√n` is the named missing piece.~~ **It landed the same
  day**: `Arlib.MarkovChains.metropolisGaussian_overlap_sqrt_of_convex`
  (`MetropolisOverlapSqrt.lean:164`), at constant `20`. It needs no `ℓ`-comparability;
  it needs a **uniform local-conductance floor** `hell` together with `hfloor`
  instead — and that pair is exactly what `EllFloor.lean` proves contradictory on the
  cube. §0e.
* ~~**`hcomp` and `hiso` remain hypotheses.**~~ `hcomp` — `ℓ`-comparability at `δ/√n` —
  **does** remain a hypothesis of the speedy-walk route, is Cousins–Vempala's own, and
  is not automatic on every convex body (next subsection). **`hiso` no longer remains**
  for the *filtered* route: `Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo`
  (`OneDimSharp.lean:1040`) proves that binder character for character. It does **not**
  reach the speedy walk's own `hiso`, whose density is `1_K·ℓ` rather than
  `1_K·γ_σ`. §0e.

Every file involved says so itself, and none may be quoted otherwise:
`OverlapSqrt.lean`'s §"No rate claim" ("nothing below asserts, or may be quoted as
asserting, a polynomial mixing time"), `LensMin.lean`'s §"What is *not* done here", and
`DeltaCap.lean`'s closing line ("Nothing in this file is a mixing-time or
polynomial-time statement, and none of it may be quoted as one").

*A side finding, recorded because it removes a distraction rather than a blocker.*
`DeltaCap.lean` §3 shows `hδσ`'s own `√n` is removable — its real content is the
dimension-free `16·(ln 2)·δ ≤ σ`, so the honest cap is `σ/(16 ln 2) ≈ σ/11.09` and
`δ ≤ σ/8` genuinely fails (`not_isoStep_quarter_at_sigma_div_eight`). The file
**deliberately does not re-prove** `conductance_speedyGaussian_ge` with the weaker
binder — that would mean editing a file it does not own — and no declaration in it
claims the relaxed theorem. It is also not needed: the operative step `Θ(σ/√n)` is well
inside the existing cap.

### What the comparability hypothesis costs, and that the counterexample survives

`Arlib.MarkovChains.exists_overlap_speedyWalk_sqrt_dim_counterexample`
(`Continuous/LensHalfspace.lean`) proves that the conclusion of
`overlap_speedyWalk_convex` is **false** at separation `δ/√n`. Nothing above
contradicts it: `exists_ell_not_comparable_at_sqrt_dim_counterexample`
(`OverlapSqrt.lean:816`) re-derives that witness (`n = 23409`, `δ = 1`,
`K = apexConeBody u v`) and proves it violates comparability by a wide margin —
`d_ℓ(u,v) > 0.95` against a hypothesis that permits `1/3`. **That is the whole content
of the new theorem**: reinstating Cousins–Vempala's `d_ℓ(u,v) < 1/3`, which
`overlap_speedyWalk_convex` deliberately deletes, is exactly what the `√n` costs.

The `min` form is also the *only* form available: the `max` form is **false**, by
`Arlib.MarkovChains.exists_halfspace_max_lt`.

**`lem:f-dist` is not proved.** Cousins–Vempala do not assume `d_ℓ < 1/3` in
`cor:overlap`; they *derive* it from `d_h(u,v) < 1/4` for `h = f·ℓ`, via a
Gaussian-ratio estimate the paper states only "for `n` large enough" and whose
arithmetic is tight. Formalising it would turn `hcomp` from a hypothesis into a
consequence of the consumer's existing binder. `ell_le_of_densDist_ell_lt`
(`OverlapSqrt.lean:599`) supplies the second half of that bridge already.

**Non-vacuity.** `Arlib.MarkovChains.exists_overlap_speedyWalk_sqrt_comparable_witness`
(`OverlapSqrt.lean:711`) meets every hypothesis simultaneously on a **bounded convex
body of positive volume** (`K = B(0,1) ⊆ ℝ²`, `δ = 3`, where `ℓ` is constant), which is
the point: the *other* route to `hoverlap`, the local-conductance floor `11 ≤ 20·ℓ(x)`
of `overlap_speedyWalk`, is satisfiable by **no** bounded convex body at all (`ℓ → 1/2`
at every boundary point), so that theorem is empty for convex bodies and its own witness
is `K = ℝ²`.

### The Localization continuity gap is an **obstruction**, not unfinished work

`Arlib/Convexity/LocalizationMeasurable.lean` settles the status of the two residuals
this page used to list for the localisation stack, **(C)** continuity of the integrands
and **(F)** `v ≠ 0`.

* **(F) is closed.** `Arlib.exists_needle_of_compact_convex` (`:226`) is the missing
  composition — compact convex body ⟶ chain ⟶ needle — which nothing had joined, with
  `v ≠ 0` recovered along the way (it was available one level down and *discarded* by a
  `-` pattern). `Arlib.exists_needle_of_compact_convex_witness` (`:266`) is the
  non-vacuity check, on the closed unit ball.
* **(C) is an obstruction.** Two theorems, both about a Lebesgue-null hyperplane:
  * `Arlib.exists_null_measurableSet_needleIntegral_eq_one` (`:442`) — a measurable `S`
    with `volume S = 0`, hence `∫_T 1_S = 0` for **every** `T`, together with a needle
    and profile meeting every clause `hLoc` imposes, for which the needle integral is
    `1`. Modifying an integrand on a null set leaves every hypothesis untouched and
    moves the conclusion by `1`. **Therefore no argument that controls `1_{S₁}` only
    through its a.e. class — `L¹` density, Lusin, Vitali–Carathéodory, in-measure
    approximation — can produce `hLoc`.**
  * `Arlib.exists_transverse_oscillation_eq_one` (`:550`) — for that same `S` and
    **every** body of positive volume, some point has transverse oscillation exactly
    `1`. The moduli of `Arlib.exists_tendsto_transverse_modulus` are therefore `≥ 1` at
    every stage of every chain, so they do not tend to `0`. That lemma is the *unique*
    place the localisation limit passage consumes continuity. **So weakening
    `Continuous` to `Measurable` is closed too.**

  **`hLoc` is not claimed false.** A needle is a null set, and Fubini forbids a null set
  meeting every line in positive length, so an integrand cannot defeat *every* needle.
  What is proved is that the two routes available to this repository are closed, and
  that `Arlib.Convexity.LocalizationLSC`'s boundary — `S` open for the positivity slot,
  an unremovable `η`-slack for the equality slot — is where the approximation route
  genuinely stops.

`LocalizationMeasurable.lean` contains **no** `def`, `structure`, `class` or named
`Prop`, and no theorem in it takes the Localization Lemma, the isoperimetric inequality
or Dyer–Frieze as a hypothesis. Nothing in it is named for a statement it does not prove.

---

## 0c. `hLS` is discharged for lazy chains — and the plain kernel is a *paper* gap

`AUDIT.md` used to call `hLS` "the one binder owned by nobody". **That was wrong,
and it was wrong before it was written.** Lovász–Simonovits 1993 Corollary 1.5 —
conductance ⟹ geometric TV decay — was already provable in this repository:

* `Arlib.MarkovChains.sq_conductance_div_two_le_spectralGap`
  (`Continuous/Cheeger.lean`) — the **hard** direction of Cheeger, `Φ²/2 ≤ gap`;
* `Arlib.MarkovChains.tvLe_iterate_of_ofReal_le_conductance`
  (`Continuous/L2Mixing.lean`) — *literally the body of the `hLS` binder*.

`Arlib/MarkovChains/Continuous/ConductanceToTV.lean` is the glue. What it lands:

* **`Arlib.MarkovChains.ls_of_hasNonnegSpectrum`** — the `hLS` binder, **verbatim,
  proved**, for a reversible kernel with non-negative spectrum on a space carrying a
  measurable set of mass in `(0, 1/2]`.
* **`Arlib.MarkovChains.ls_lazy`** — the same for `lazy P`, from `IsReversible P pi`
  **alone**: `hasNonnegSpectrum_lazy` supplies the spectral hypothesis from
  reversibility. The price is quoted, not hidden — `ofReal_half_le_conductance_lazy`
  and `lsThreshold_half`: half the conductance, four times the deadline.
* `Arlib.MarkovChains.tvLe_iterate_of_exceptional_of_isReversible` — LV Theorem 1.1
  with `hLS` **eliminated**, proved by handing `ls_of_hasNonnegSpectrum` to the
  `hLS` slot with no massaging; and `tvLe_iterate_lazy_hitAndRun_unitBall`, where
  the only residual assumptions are `hLem41` and `hIso`.
* The one genuinely new proof is
  `Arlib.MarkovChains.smallSets_nonempty_of_rayleighSet_nonempty`, a median argument
  buying the kernel-free hypothesis.

**What is *not* discharged, and why it is a finding rather than a to-do.**

* **`hLS` for the plain (non-lazy) hit-and-run kernel is not reachable**, and
  `hLS` is *false* for a general reversible chain: `HitAndRunMixing.lean` records
  the swap kernel `P x = dirac (!x)` on `Bool`, which is `piHalf`-reversible with
  conductance `1` and has `d_TV = 1/2` for every `t` against a bound `√2·2⁻ᵗ`.
  §5 of *Hit-and-Run from a Corner* applies Cor. 1.5 to a **non-lazy** chain. So
  the two results agree, and the conclusion is about the paper: **with laziness the
  argument works at 4× the deadline; without it, it is false.** The paper needs the
  lazy kernel.
* **`hLSs`, the `s`-conductance form, is provably unreachable by this route.** Its
  premise `ofReal ph ≤ conductanceS P pi s` is *strictly weaker* than what Cheeger
  consumes, since `conductance ≤ conductanceS`. It needs the LS93
  curve/localisation argument plus atomless `π`, and is not attempted.

`H : Ttc.HitAndRunTheorem11Input` is therefore still inhabited nowhere — §0a row 1
is unaffected by this. What changed is *why*: not "nobody owns the conductance⟹TV
step" but "the paper applies it to a kernel for which it is false, and the lazy
repair costs a factor 4".

---

## 0d. Known-stale `.lean` docstrings, not yet corrected

Recorded here rather than fixed, so a later pass has a worklist and no reader takes
a confident "this is not proved anywhere" sentence at face value. Each entry gives
`file:line`, the stale claim, and what refutes it. **Line numbers here are
deliberate and are the exception to this page's no-line-numbers policy** (see the
top of the page): a docstring paragraph has no declaration name to point at.

| `file:line` | the stale claim | what refutes it |
| --- | --- | --- |
| `Ttc/Model/Theorem.lean:27` | "**Nine** binders — `atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos`" | the list it prints has **eleven** entries, and eleven is the count. See §5's binder-count subsection |
| `Arlib/Convexity/LocalizationLemma.lean:76-89` | gap **(G1)** needs the two-measure ham-sandwich, i.e. Borsuk–Ulam, "which Mathlib `v4.32` does not have" | `Arlib.exists_flat_cut_zero_pos` (`Convexity/LocalizationAssembly.lean:415`) cuts with arbitrary *signed* integrands, so Borsuk–Ulam is not needed. `HitAndRunConductance.lean:76` already records this; `LocalizationLemma.lean` does not |
| `Arlib/Convexity/LocalizationTransverse.lean:42-47` | "## What is *not* proved here — nothing shows that the bodies produced by `Arlib.exists_flat_cut_chain` are closed" | `Arlib/Convexity/LocalizationClosed.lean` closes chain closedness; `Arlib.exists_flat_cut_chain_collinear_compact_ge` (`:219`) delivers compact bodies |
| `Arlib/Convexity/NeedleProfile.lean:105-113, 124` | **(G2c)**, the affine change of coordinates, is "the one undischarged ingredient" of the needle stack | the route of record no longer runs through this file's profile machinery: `Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_chain` (`NeedleSlabChain.lean`) reaches the needle conclusions via the slab/chain route, and `Arlib.exists_needle_of_compact_convex` (`Convexity/LocalizationMeasurable.lean:226`) is the composed entry point. **Verify before editing** — G2c may still be open *for this file's own statements* |
| `Arlib/MarkovChains/Continuous/SpeedyOverlap.lean:59-62` | KLS95 Lemma 3.5 "is **not** proved here", and its proof needs a polar decomposition "which Mathlib does not support today" | `Arlib.MarkovChains.kls_lemma35_at_sep_sqrt_dim` (`LensMin.lean:423`) proves the `min` form at `δ/√n` with **no** polar decomposition — a midpoint/Brunn–Minkowski argument. Mathlib *does* have polar decomposition and this repo wraps it (`lintegral_polar_at`, `HitAndRun.lean:479`) |
| `Arlib/MarkovChains/Continuous/MixingFromConductance.lean:79-94` | Cheeger's hard direction and the decay bound "are not proved in this file" and "none of that is attempted here" | true *of that file*, but misleading: `Cheeger.lean` and `L2Mixing.lean` import it and supply exactly the listed missing pieces. Flagged from `HitAndRunMixing.lean`, left to the file's owner |
| `Arlib/Convexity/LocalizationMeasurable.lean:18` | cites "`AUDIT.md:147-149` records two residuals of the localisation stack" | **drifted**, by this very edit: inserting §0a–§0d pushed everything below down by several hundred lines, and `AUDIT.md:147-149` is now the `hLS` bullet. The content it means — residuals **(C)** and **(F)** — is §0b's "The Localization continuity gap is an obstruction" subsection. A live illustration of why this page names declarations rather than lines |
| `Arlib/Convexity/GaussianCooling/Unblock.lean:77-83` | a chain stationary for `Arlib.uniformOn (volume.withDensity g) K` "is a Metropolis-filtered … chain, and **no such kernel is built in this library**" | `Arlib.MarkovChains.metropolisGaussian` (`Continuous/MetropolisGaussian.lean:444`) is that kernel, and `isReversible_metropolisGaussian` (`:586`) proves the stationary law. Note `BallWalk.lean:24` is **not** stale — it says the filter is not applied *in that file*, which is correct |

**Added 2026-08-12, second pass.** Eight more, found while re-deriving §0e and §0f.
The first three are the load-bearing ones: each asserts, in a file a reader would
treat as authoritative, that something is *not* done which now is.

| `file:line` | the stale claim | what refutes it |
| --- | --- | --- |
| `Arlib/Convexity/GaussianCooling/PhaseMeanApprox.lean:105-118` | its whole §2, "The repository's own framing is stale, in two files this agent may not edit" — four factual claims, **all four now false**: that `CVInstantiate.lean:83` says "This is where the development actually stops"; that `RuntimeMN4.lean:133` is hypothesis #12; that `cousinsVempalaOfRuns` is at `CVInstantiate.lean:265`; and that "the **live** path … the one `Ttc.ttc_runtime_mn4` goes through — was never rewired to the approximate-mean constructor" | the quoted sentence was **deleted** from `CVInstantiate.lean` (`:83` now opens "**`hphase_mean` is the deep one, and it is stated too strongly here.**"); `RuntimeMN4.lean:133` is now hypothesis **#8**, `H`; `cousinsVempalaOfRuns` is at `:298`; and **the live path was rewired** — `Ttc.ttc_runtime_mn4` (`RuntimeMN4.lean:409`) runs `Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMean`. The worst entry in this table: an `Arlib` file asserting a `Ttc`-side defect that has since been fixed |
| `Arlib/MarkovChains/Continuous/MetropolisOverlapSqrt.lean:273-277` | `hiso` "is **not proved in this repository**", therefore the theorem "is not a mixing-time bound and not an `O*(n³)` claim, and may not be quoted as either" | the first half is false: `Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo` (`Convexity/OneDimSharp.lean:1040`) proves that exact binder, and `conductance_metropolisGaussian_sharp_sqrt_ge_of_convex` (`:1073`) is the discharged corollary. `MetropolisMixing.lean:70` already flags it. **The second half is still correct**, and §0e explains why it is the more important half |
| `Ttc/Volume/CouplingAccuracy.lean:114-120` | of the chain layer: "No single body is yet known to satisfy both. Flagged, not faked." | `Arlib.GaussianCooling.exists_couplingRoute_chain_witness` (`GaussianCooling/CouplingRouteUncond.lean:256`) exhibits one — `K = B(0,1) ⊆ ℝ²`, every binder discharged. The **first** bullet of that same section (the `k ≥ 2` indexing caveat, `:105-113`) is still accurate, and the section's headline — "the composition has none" — is still true |
| `Arlib/Convexity/GaussianCooling/PhaseMeanRoute.lean:118-136` | §4's bug-oracle finding: that `CVInstantiate.lean:81-82` justifies the obstruction with the false premise "a Markov chain run for finitely many steps is at total-variation distance `> 0` from its stationary law" | the finding was **acted on**. `CVInstantiate.lean:89-95` now says the opposite and cites `Arlib.MarkovChains.mixesWithin_const` as the refutation. The theorem `exists_markovKernel_mixesWithin_coolLaw_exact` is unaffected; only the framing is stale |
| `Ttc/Exec/PolyAccuracy.lean:723-727`, `Ttc/Exec/CVBackend.lean:494-495`, `Ttc/Exec/PolyRun.lean:40-41` | all three quote `CVInstantiate.lean:83` as saying "this is where the development actually stops" | that sentence no longer exists anywhere in `CVInstantiate.lean`. `Ttc/Volume/PhaseFromSampler.lean:62` already records the quote as stale; these three do not |
| `Ttc/Exec/CVBackend.lean:491`, `Ttc/Exec/PolyRun.lean:39`, `Ttc/Volume/PhaseFromSampler.lean:350`, `Arlib/Convexity/GaussianCooling/PhaseMeanRoute.lean:30` | all four cite `Ttc/Volume/CVInstantiate.lean:265` for `Ttc.VolumeAlgorithm.cousinsVempalaOfRuns` | the declaration is at **`:298`** — ~30 lines of docstring were inserted above it. `PhaseMeanRoute.lean:31` additionally cites `:277-286` for the two binders; they are at `:310-319`. `CVBackend.lean:654` and `:772` cite `:342` for `cousinsVempalaOfRunsWitness`; it is at `:375` |
| `Arlib/Convexity/GaussianCooling/CouplingRoute.lean:90,100` and `CouplingRouteUncond.lean:62` | name the estimator lemma `Ttc.CV.volume_accuracy_of_samples` | the namespace is **`Ttc.CVEst`** (`Ttc/Volume/CVEstimator.lean:582`). `CouplingAccuracy.lean:30-31` records the correction; those two files do not |
| `Arlib/Convexity/IsoIndicator.lean:95` and `:798` | cite `AUDIT.md:192` and `CV-ROADMAP.md:240` for the `(1d-2)` constant | both are line citations into *this* page and `CV-ROADMAP.md`, and this very edit moved them again — and the content they point at is now struck through, because `OneDimSharp.lean` closed that gap. Cite the section, not the line. (`LocalizationMeasurable.lean:18`'s citation of `AUDIT.md:147-149` is already in the table above and has drifted a second time.) |

Two things this table is **not**. It is not a list of unsound claims — every
declaration in every file above is proved and axiom-clean; the staleness is in
prose about *what else exists*. And it is not exhaustive: it is what one pass
found. `AUDIT.md`'s standing advice stands — treat a confident-sounding docstring
in this development as a claim to re-check.

---

## 0e. `thm:iso` is discharged — and a *floor* is what blocks the runtime now (2026-08-12)

> ## ⚠ THE DEEP PROBABILITY OBSTRUCTION IS GONE, AND THE RUNTIME DID NOT MOVE ⚠
>
> Read both halves or neither. **Half one:** the isoperimetric inequality
> Cousins–Vempala's conductance bound needs is now a **theorem**, with no
> localization binder, for exactly the density the Metropolis-filtered Gaussian ball
> walk uses; and the mixing bound built on it —
> `4·5120²·n²·(log M + 2·log(1/ε))/(log 2)² + 1` steps suffice — carries **no
> isoperimetry hypothesis at all**. **Half two:** that bound also carries a
> *pointwise local-conductance floor*, and `EllFloor.lean` proves the floor is
> **unsatisfiable on the cube `[-1,1]ⁿ` for `n ≥ 3`** — a body squarely inside the
> class the Gaussian-cooling volume oracle quantifies over. So the theorem is true
> and **vacuous where the oracle needs it**. Nothing here is a mixing-time or
> polynomial-time claim about any convex body the algorithm meets.

### The `(1d-2)` constant, and why it was the whole gap

The metric branch of `thm:iso` reads `d / c` for the `(1d-2)` constant `c`, and every
downstream consumer writes `d / log 2`. This repository had `(1d-2)` only at
`1/(2√3) ≈ 0.2887` (`Arlib.oneDim_isoperimetry_gaussianFactor_unconditional`,
`Convexity/ConcaveProfileIso.lean:631`) against Cousins–Vempala's `ln 2 ≈ 0.6931` — a
factor `2.4` short, and short in the wrong direction, so the consumer's binder could
not be filled.

[`Arlib/Convexity/OneDimSharp.lean`](Arlib/Convexity/OneDimSharp.lean) closes it:

* `Arlib.oneDim_isoperimetry_gaussianFactor_sharp` (`:518`) proves `(1d-2)` at
  **`√(2/π)/σ ≈ 0.7979/σ`**, with exactly the hypotheses of the `1/(2√3)` version.
* `Arlib.log_two_le_sqrt_two_div_pi` (`:554`) is the machine-checked
  `ln 2 ≤ √(2/π)`. (The strict `>` is arithmetic in the docstring; the non-strict
  `≤` is what the weakening needs, and it is what is proved.)
* `Arlib.oneDim_isoperimetry_gaussianFactor_logTwo` (`:572`) is the `√(2/π)` theorem
  weakened along it to `log 2 / σ` — the shape the stack consumes.

The crux is three lines and uses **no** Brascamp–Lieb, **no** Hensley bound and no
variance hypothesis: `h = F·γ_σ` with `F` log-concave is `σ^{-2}`-strongly
log-concave, so tilting by the Gaussian re-centred at `x` leaves a log-concave
function, which cannot exceed its value at `x` on *both* sides
(`Arlib.gaussian_domination_of_logConcave`, `:212`); on the side where it does not,
the mass is at most `h(x)·σ√(π/2)` (`Arlib.needle_tail_mass_le`, `:354`).
`Arlib.exists_gaussian_tails_gt` (`:1212`) shows `σ√(π/2)` is the ceiling **of this
argument**, and `Arlib.uniform_saturates_hensley` (`:1171`) diagnoses where the old
`1/(2√3)` was lost — not in Hensley's bound, which is tight for the uniform weight,
but in the pointwise Cheeger step.

### `thm:iso` itself — two theorems, and what each costs

| declaration | what it is | the price |
| --- | --- | --- |
| `Arlib.gaussianRestricted_isoperimetry_openClosed` (`Convexity/IsoOpenClosed.lean:854`) | `thm:iso` for a general `h = f·e^{−‖x‖²/2σ²}` with `f` log-concave, **no `hloc` and no localization binder of any kind** — the `(1d-2)` input is discharged inside the proof | **three hypotheses**, in the file's own words: `S₁, S₂` **open**, `S₃` **closed**, and `h` **continuous and bounded** (plus `Integrable h`). Its separation threshold is `2√3·d`, **not** `d/ln 2` |
| `Arlib.gaussianIndicator_isoperimetry_measurable` (`Convexity/IsoIndicator.lean:476`) | the same for the **indicator** density `1_K·γ_{σ²}`, with `S₁ S₂ S₃` merely **measurable** | **two more hypotheses**: `hRσ : √3·R ≤ 2σ√n` and `hK0 : volume K ≠ 0`. `hRσ` is what turns the density branch into metric separation; without it the route survives only at the reduced constant `min(d, 4σd√n/(2√3·R))` |

The two are joined at `ln 2` in `OneDimSharp.lean`
(`gaussianRestricted_isoperimetry_openClosed_logTwo` `:631`,
`gaussianIndicator_isoperimetry_measurable_logTwo`), and the payoff is

* **`Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo` (`OneDimSharp.lean:1040`)** —
  the `hiso` binder of `Arlib.MarkovChains.conductance_metropolisGaussian_sharp_sqrt_ge`
  (`MarkovChains/Continuous/MetropolisOverlapSqrt.lean:284-295`) **character for
  character**, proved; and
* **`Arlib.conductance_metropolisGaussian_sharp_sqrt_ge_of_convex`
  (`OneDimSharp.lean:1073`)** — that conductance bound with `hiso` gone. The only
  hypothesis it adds is `hRσ`.

**Scope this, and do not write a flat "`hiso` is discharged".** The discharge covers
exactly **one** binder. Still carried, unproved, elsewhere in the tree: the `δ/n`
Metropolis theorem `conductance_metropolisGaussian_sharp_ge`
(`MetropolisConductanceSharp.lean:431`, binder at `:438` — **no `_of_convex` variant
exists**), and the whole speedy-walk family (`SpeedyWalk.lean:976, 1210, 1322`;
`SpeedyToUniform.lean:230, 278`; `OverlapSqrt.lean:680`;
`SpeedyConductanceSharp.lean:333`). §0b's table row for
`conductance_speedyGaussian_ge_of_ell_comparable` is *not* affected by this section.

### The Metropolis overlap lemma at `δ/√n` — §0b's "named missing piece", landed

`Arlib.MarkovChains.metropolisGaussian_overlap_sqrt_of_convex`
(`MetropolisOverlapSqrt.lean:164`) concludes
`1 ≤ 20·(metropolisGaussian K δ s u Tᶜ + metropolisGaussian K δ s v T)` for pairs at
separation `< δ/√n` — the filtered analogue §0b named as missing. It needs **no**
`ℓ`-comparability. What it needs instead is the pair

```
hell   : ∀ x ∈ K, ofReal θ ≤ ell K δ x
hfloor : 1 ≤ 20 · e^{−(2Rδ+δ²)/(2σ²)} · (1/4) · θ
```

and `conductance_metropolisGaussian_sharp_sqrt_ge` (`:278`) carries the pair up into
`Φ ≥ δ·log2/(640·σ·√n)`. Sharpest lens constant behind it: `1/4`,
`Arlib.MarkovChains.volume_lens_ge_min_ball_inter_quarter` (`LensSharp.lean:409`).

> **`LensSharp` does not refute `1/(e+1)`, and this page must not say it does.** The
> `1/(e+1) ≈ 0.269` discussion is a numeric remark in that file's module docstring
> (`:88-104`) about where *this proof skeleton* tops out at `n = 2` (half-space factor
> `≤ 1/2`, midpoint `≤ 0.5223`, harmonic combination `0.2555`). It is unformalised
> prose and it is a ceiling on the argument, not on the constant. The proved constant
> is `1/4`; `1/(e+1)` is neither achieved nor refuted.

### Mixing, and the arithmetic

`Arlib/MarkovChains/Continuous/MixingSqrt.lean` does the `Φ⁻²` bookkeeping —
`mixesWithin_at_operative_step` (`:361`) turns `Φ ≥ (σ/(8√n))·log2/(640σ√n)` into
`5120²·n²·(log M + 2·log(1/ε))/(log 2)² + 1` steps, and the two ratio brackets
(`conductanceMixingTime_old_le_dim_mul_new` `:442`,
`dim_mul_conductanceMixingTime_new_sub_one_le_old` `:468`) pin the old route at a
factor `n` worse. `MetropolisMixing.lean` instantiates it at the Metropolis kernel
(still carrying `hiso`), and **`MetropolisMixingUncond.lean` is the same with `hiso`
discharged**: `mixesWithin_lazy_metropolisGaussian_at_operative_step_of_convex`
(`:130`) and three companions.

Three things to keep straight about "unconditional":

1. It means **"no `hiso` binder"** and nothing more. `hell`, `hfloor`, the new `hRσ`,
   the body's geometry and the warm start all remain binders.
2. The step count is a **hypothesis on `t`** (`… + 1 ≤ t`), i.e. "that many steps
   suffice" — not a conclusion of the form `t = O(…)`.
3. The **plain-chain** pair (`:196`, `:223`) still carries
   `hpsd : HasNonnegSpectrum`, which is proved for no Metropolis kernel here and is
   not removable (the `Bool` swap kernel is the counterexample). Only the **lazy**
   pair is free of it, at `4×` the deadline.

`exists_mixesWithin_lazy_metropolisGaussian_uncond_witness` (`:291`) discharges every
hypothesis of the two lazy theorems at once — and **read where**: `n = 2`,
`K = B(0,1/2) ⊆ ℝ²`, `δ = 1`, `σ = 8√2`, `θ = 1/4`. `B(0,1/2)` does **not** contain
the unit ball, so the witness sits *outside* the Gaussian-cooling consumer's class,
and `n = 2` is precisely where the next subsection's negative does not bite. There is
no witness for the plain-chain pair or for the two phase-law theorems (`:443`,
`:476`).

### `EllFloor.lean` — the decisive negative, stated precisely

**Do not write "`hell` is unsatisfiable".** `hell` alone is satisfiable — trivially at
`θ ≤ 0`, and non-trivially by this very file's `le_ell_of_ball_subset_of_radius`
(`EllFloor.lean:498`) at `θ = (1/(1+2R))ⁿ`. What is proved is that **`hell` and
`hfloor` are jointly contradictory**:

| declaration | statement |
| --- | --- |
| `Arlib.MarkovChains.two_pow_card_mul_ell_le_one` (`EllFloor.lean:244`) | if `k` of the coordinate half-spaces `{y j ≤ x j}` support `K` at `x` then `2^k · ell K δ x ≤ 1`, **at every step size `δ`**. No convexity, measurability or boundedness. Proof: the coordinate-reflection group |
| `Arlib.MarkovChains.le_two_pow_neg_of_ell_floor_cube` (`:359`) | any `θ` meeting `hell` on `[-1,1]ⁿ` has `θ ≤ 2⁻ⁿ` |
| `Arlib.MarkovChains.metropolis_ell_floor_unsatisfiable_on_cube` (`:402`) | **`n ≥ 3`, `hell`, `hfloor` (the `1/4` shape) ⟹ `False`** — `θ`, `δ`, `σ`, `R` all universally quantified, so this is "no `θ`, at any step size" |
| `Arlib.MarkovChains.metropolis_ell_floor_dim_unsatisfiable_on_cube` (`:483`) | the same for the `(1−1/n)ⁿ` shape of `hfloor`, at **`n ≥ 5`** |
| `Arlib.MarkovChains.exists_convex_body_meeting_all_but_ell_floor` (`:417`) | **the attribution theorem** — at `σ = 1`, `δ = 1/(8√n)`, `R = √n`, the cube meets *every other* binder, including `ball 0 1 ⊆ K` and `hRσ`, and no `θ` meeting `hell` on it satisfies `hfloor`. So the failure is the local-conductance floor's alone |

The body is `[-1,1]ⁿ`, side `2`, **not** the unit cube — it contains the unit ball
(`ball_subset_cube`, `:307`), which is exactly what puts it inside the class
`Ttc/Volume/CVInstantiate.lean:148,153` quantifies over (`Convex ℝ K`,
`ball 0 1 ⊆ K`, `volume K ≠ ⊤`). `hfloor` forces `θ ≥ 1/5`; a corner forces
`θ ≤ 2⁻ⁿ`; `2⁻ⁿ < 1/5` from `n = 3`.

**This is the same phenomenon as §0b's remark that `overlap_speedyWalk`'s floor
`11 ≤ 20·ℓ(x)` is satisfiable by no bounded convex body — sharpened, not
duplicated.** That remark was about `ℓ → 1/2` at a *smooth* boundary point and was
prose. `EllFloor` proves a quantitative, dimension-dependent version — `ℓ ≤ 2⁻ᵏ` at a
`k`-fold corner, at every `δ`, by a group argument — for the *filtered* kernel's
floor, and turns it into a `→ False`.

**What it does not rule out.** `n = 2`. Corner-free bodies — the file exhibits no
restricted class inside the consumer's class on which `hell` holds at `θ ≥ 1/5`, but
it does not prove none exists; what it does prove is that every *pointwise* floor of
the shape this repository has is exponentially small once `ball 0 1 ⊆ K` forces
`R ≥ 1` (`general_ell_floor_le_three_pow_neg`, `:527`, `≤ 3⁻ⁿ`). And it does not
touch the truth of `conductance_metropolisGaussian_sharp_sqrt_ge_of_convex`, which is
true — and vacuous on the cube.

**What survives is the average, not the infimum.** `isSmooth_of_ball_subset` (`:549`)
proves **every** convex `K ⊇ B(0,1)` is `(δ, 1 − (1−δ)ⁿ)`-smooth, i.e.
`(1−δ)ⁿ·vol K ≤ ∫_K ℓ`, for every `0 < δ < 1`. `IsSmooth` constrains the *average* of
`ℓ` and is blind to the corner; `cube_smooth_but_no_pointwise_floor` (`:613`) states
both facts on one body.

### The speedy route, and why it is not the way round

`Arlib/Convexity/EllLogConcave.lean` proves the two positive facts one would need —
`Arlib.isLogConcave_ell_toReal` (`:262`, no hypothesis on `δ`) and
`Arlib.continuous_ell_toReal` (`:431`) — and then records **two** (not three)
obstructions to using them for the speedy walk's own `hiso`:

1. **no Gaussian factor.** `hrev` forces the stationary law to be a scalar multiple of
   `ellMeasure K δ`, density `1_K·ℓ`; every unconditional `n`-dimensional
   isoperimetric inequality here is for `f·e^{−‖x‖²/2σ²}`, and the compensating
   `e^{+‖x‖²/2σ²}` is log-**convex**;
2. **measurable vs open/closed.** The speedy binder quantifies over measurable
   `S₁ S₂ S₃`; the general-`f` capstone is proved only for `S₁, S₂` open and `S₃`
   closed, and the measurable upgrade is indicator-specific.

**Both are narrative docstring arguments, not proved negatives** — every declaration
in that file is a positive result or a witness. The only machine-checked negative in
this cluster is `Arlib.exists_separated_no_disjoint_open_enlargement`
(`IsoOpenClosed.lean:1205`), and it refutes the open-enlargement **mechanism**, not
the statement. `ellGaussian_isoperimetry_openClosed_logTwo` (`EllLogConcave.lean:474`)
is, in the file's own words, "an **instance** of an existing theorem, not a new one".

### Non-vacuity and semantic `def`s for this section

Every one of `IsoOpenClosed`, `IsoIndicator`, `OneDimSharp`, `EllLogConcave`,
`LensMin`, `LensSharp`, `OverlapSqrt`, `DeltaCap`, `MetropolisOverlapSqrt`,
`MixingSqrt`, `MetropolisMixing`, `MetropolisMixingUncond` and `EllFloor` contains
**no `def`, `structure`, `class` or `axiom`** — every declaration is a `theorem`. So
check 6 is empty for the whole cluster. Witnesses exist for
`gaussianRestricted_isoperimetry_openClosed` (`IsoOpenClosed.lean:916`),
`gaussianIndicator_isoperimetry_measurable` (`IsoIndicator.lean:873`),
`oneDim_isoperimetry_gaussianFactor_sharp` (`OneDimSharp.lean:1096`),
`conductance_metropolisGaussian_sharp_sqrt_ge` (`MetropolisOverlapSqrt.lean:344`,
every binder **except** `hiso`), and the mixing theorems (`MetropolisMixing.lean:397`
except `hiso`; `MetropolisMixingUncond.lean:291`, with the class caveat above).

### `Arlib/Probability/TVTensor.lean`

TV tensorization, used by the coupling route of §0f: `Arlib.Probability.TVLe.prod`
(`:226`) gives `TVLe (μ₁ ⊗ μ₂) (μ₁' ⊗ μ₂') (e₁ + e₂)` and `TVLe.pi` (`:284`) the
finite-product form at `∑ᵢ eᵢ`. `IsProbabilityMeasure` is load-bearing on all four
arguments: the hybrid step integrates the `e₂` slack against `μ₁'`, and
`∫⁻ e₂ ∂μ₁' = e₂·μ₁'(univ)` collapses to `e₂` only because `μ₁'(univ) = 1`.
**That necessity is argued in the docstring and is not mechanised** — the file's one
negative, `not_tvLe_prod_witness_quarter` (`:412`), proves a *different* sharpness
(that `e₁ + e₂` cannot be replaced by one factor's `1/4`). Do not call it a
counterexample to the normalisation claim.

---

## 0f. The Cousins–Vempala phase-mean routes, and the layer with no witness (2026-08-12)

`hphase_mean` is the binder §0a's ledger calls row 12. Three files attack it and one
composes the result; the honest summary is that the **abstract** layers are real and
the **composed** layer has no non-vacuity witness at all.

### `coolLaw` is the mixing bound's stationary law — proved, unconditionally

`Arlib.GaussianCooling.coolLaw_eq_uniformOn_gaussianWeight`
(`GaussianCooling/PhaseMeanRoute.lean:216`) proves

```
coolLaw m σsq K i = Arlib.uniformOn (volume.withDensity (gaussianWeight (σsq i))) K
```

under `0 < σsq j`, `MeasurableSet K`, `ball 0 1 ⊆ K`, `volume K ≠ ⊤` and `i < m`. No
error term, no `hiso`, no warm start. That is the join between §0e's mixing bound and
Cousins–Vempala's phase laws, and it is the reason the coupling route below composes
at all.

### The negative on the *equation* — read what it actually says

`Arlib.GaussianCooling.exists_tvLe_coolLaw_integral_phaseScore_ne`
(`PhaseMeanRoute.lean:518`) is **a counterexample to the implication "a TV bound gives
the equation"**, not a refutation of the equation. For every `ε ∈ (0,1]` it exhibits a
probability measure `ν` with `TVLe ν (coolLaw …) ε` whose phase-score integral is
exactly `(1−ε)·(chain(i+1)/chain(i))` — so the relative error *is* the TV error, and
no mixing theorem short of exact sampling can deliver equality. The equation itself
holds exactly at `coolLaw` (`integral_phaseScore_coolLaw`) and at a degenerate kernel
(`exists_markovKernel_mixesWithin_coolLaw_exact`, `:557`, TV exactly `0` in one step).
That is precisely why the capstone was rewired to the interval form (§0a).

### Route A — `PhaseMeanApprox.lean`, and what it costs

`integral_phaseScore_mem_Icc_of_tvLe` (`:262`) derives the *interval* hypothesis from
a TV bound `e` plus a slack condition
`exp(R²/(2σᵢ²))·e ≤ η·(chain(i+1)/chain(i))`; `integral_prod_phaseScore_mem_relErr`
(`:311`) telescopes it over the phases under a budget `2mη ≤ τ`. **Both are `hiso`-
free and warm-start-free.** The two composed forms (`:366`, `:466`) carry `hiso`
verbatim and a warm start.

The cost: `log(1/tvBudget) = R²/(2σᵢ²) + log(1/η) + log(1/r)`, machine-checked as
`Arlib.GaussianCooling.log_one_div_tvBudget_exp` (`:433`). **That identity is the
whole of the machine-checked content.** The reading that `R²/(2σᵢ²)` is polynomially
large in `n` on a cooling schedule — hence that Route A costs the exponent — is
arithmetic in the docstring, and the file says so itself at `:167`. Do not upgrade it.

Witnesses exist for the two `hiso`-free layers (`:576`, `:605`); the composed ones
have none, and the file says so.

### Route B — the coupling route, composed, with a chain-layer witness

* `Arlib.GaussianCooling.le_measureReal_runMeasure_of_failure_budget`
  (`GaussianCooling/CouplingRoute.lean:213`) — the abstract transfer: if every
  coordinate law is within TV `b` of the exact one and `(r·m)·b ≤ ρ`, then a success
  probability `q` at the exact laws transfers to `q − ρ` at the sampled ones. Built on
  §0e's `TVLe.pi`. Witness at `:442`, at `b = 1/4 > 0` with `ν ≠ ν'` provably.
* `Arlib.GaussianCooling.le_measureReal_runMeasure_metropolisGaussian_budget_of_convex`
  (`CouplingRouteUncond.lean:184`) — the same with the coordinate laws instantiated at
  `iterate (lazy (metropolisGaussian K δᵢ σᵢ²)) mu0 t` and `hiso` discharged by
  `Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo`. `hRσ` replaces it; `hell`,
  `hfloor` and the warm start remain.
* **`Arlib.GaussianCooling.exists_couplingRoute_chain_witness`
  (`CouplingRouteUncond.lean:256`) is the chain-layer non-vacuity witness**, and it
  discharges every binder of that theorem including `hgood`, plus `0 < q − ρ` so the
  conclusion is not the trivial `0 ≤ measure`. **Read the parameters**: `n = 2`,
  `r = m = 1`, `K = B(0,1) ⊆ ℝ²`, and the estimator is `V ≡ 1`, `acc = 0`, `q = 1`,
  with the warm start *being* the stationary law (`M = 1`). It certifies the chain
  layer is instantiable. It certifies nothing about any estimator.

### ⚠ `Ttc/Volume/CouplingAccuracy.lean` — the composed layer has **no witness**

`Ttc.CVCoupling.volume_accuracy_couplingRoute` (`:152`) and
`Ttc.CVCoupling.volume_accuracy_metropolisGaussian` (`:240`) join Route B's transfer
to the estimator: here the abstract `q` is **concretely `1 − p`**, supplied by
`Ttc.CVEst.volume_accuracy_of_samples` (`Ttc/Volume/CVEstimator.lean:582`) — note the
namespace is `Ttc.CVEst`, not `Ttc.CV`, and two `Arlib` docstrings still get this
wrong (§0d). The conclusion is `1 − p − ρ ≤ (runMeasure …).real {ω | …}`.

**There is no non-vacuity witness for either theorem, and the file says so** (`:89`:
"This file adds no witness of its own, and the composition has none"). It contains
exactly two theorems and no `exists_*` declaration. The two witnesses it could
inherit live on incompatible spaces — `exists_couplingRoute_witness` on
`RunSpace Bool 1 1`, and `CVEstimator`'s bundle witnesses on `Unit` with
deterministic scores, so `hsampler` there holds only at `η = 0`. **This is a
CLAUDE.md §11 check-3 hole and is reported as one.** It is not *known* vacuous —
the pieces are individually satisfiable — but "not known vacuous" is not
"certified non-vacuous", and this page will not blur them.

Two further caveats of that file, one live and one stale:

* **live — the `k ≥ 2` run-space indexing caveat** (`:105-113`).
  `Arlib.Probability.RunSpace E r m = Fin r → Fin m → E` carries **one** `E`-coordinate
  per (run, phase), so for `k ≥ 2` the binders `hindep_in` and `hsample_mean`
  constrain `k` functions of a *single* coordinate, which forces degeneracy unless `E`
  itself packs `k` draws. The bundle is cleanly satisfiable at `k = 1`, so the theorems
  are not vacuous on that account; but the "`k` independent samples per phase" reading
  of `volume_accuracy_metropolisGaussian`, where `E = EuclSpace n` is forced, needs
  `k = 1`. Flagged in the file, not fixed;
* **stale** — its second bullet (`:114-120`) says no body is known to satisfy the
  chain layer's hypotheses. One is; see §0d.

Note also that this file still carries `hiso` as a binder (`:248-259`): it has **not**
been switched to the `_of_convex` version, so §0e's discharge has not yet reached it.

### What remains — the whole list, after §§0a–0f

Stated once, so that no reader has to reassemble it, and stated in the order of how
much mathematics is left in each:

1. **Sampler existence.** `H : Ttc.HitAndRunTheorem11Input` is inhabited nowhere
   (§0a row 1), and no sampler in this repository comes with a proved `hTV` at the
   accuracy Cousins–Vempala's slack conditions need (§0a, §0f). Everything else on
   the volume side that used to look deep now reduces to this.
2. **Hypothesis applicability — the `ell` floor, and the speedy route.** The
   Metropolis conductance and mixing theorems are true and their isoperimetry is
   discharged, but their local-conductance floor is contradictory on the cube for
   `n ≥ 3` (§0e), so they say nothing about the bodies the volume oracle quantifies
   over. The speedy walk, whose stationary density `1_K·ℓ` has no corner problem,
   has its **own** undischarged `hiso`, and `EllLogConcave.lean`'s two obstructions
   to closing it are arguments, not theorems (§0e). This is where the mathematics
   now is.
3. **The estimator's connection to a real algorithm.** `Ttc/Volume/CouplingAccuracy.lean`
   composes the transfer with the estimator and has **no non-vacuity witness**
   (§0f); `hphase_var` is still routeless (§0a); and the `k ≥ 2` run-space indexing
   caveat means the "`k` samples per phase" reading of the composed theorem needs
   `k = 1`.
4. **A cost model with no complexity field.** `Ttc.VolumeAlgorithm`
   (`Ttc/Volume/Oracle.lean:70-93`) has exactly seven fields — `Ω`, `mΩ`, `μ`,
   `isProb`, `est`, `est_meas`, `correct` — and **not one of them mentions a step
   count, an oracle-call count or a cost**. Its `correct` field is an accuracy
   guarantee and nothing else. So no instantiation of it, Cousins–Vempala's
   included, can *state* a complexity, let alone prove one; all charging happens
   outside, in `Ttc.ttcPolyCost`. **This one is a design decision, not a proof
   problem** — and it is why §0a's `m·n⁴` is a charged-cost statement rather than a
   runtime.

The exponent arithmetic over the charged-cost model is unchanged by anything in
§§0e–0f, and was already done before them.

> **STALE as of 2026-08-18 — see §0g.** Items 1–3 of the list above are superseded:
> the sampler-existence and hypothesis-applicability obligations are discharged along
> the *slow canonical* route, and two unconditional runtime capstones now exist. Item 4
> (the cost model carrying no complexity field) still stands and is still a design
> decision, not a proof problem. The list is kept because §§0a–0f are a dated record.

---

## 0g. Three unconditional runtime capstones, and the honest complexity (2026-08-18)

**The two capstones.** Both are about TTC's own inputs `(atoms, φ, ε, δ)`, both carry
**no** oracle, certificate, implementation, or cost-side binder, and in both the
implementation appears as a **closed term with no arguments**:

| Capstone | `file:line` | Family |
|---|---|---|
| `Ttc.TtcSlowRuntimeUnconditional.ttc_volume_runtime_unconditional` | `Ttc/Exec/TtcSlowRuntimeUnconditional.lean:506` | uniform slack, `slowMinStepsEnvelope` |
| `Ttc.TtcSlowRuntimeSharp.ttc_volume_runtime_sharp` | `Ttc/Exec/TtcSlowRuntimeSharp.lean:621` | sharp slack (`…/6`), sharp transport bound |
| `Ttc.TtcSlowRuntimePerPhase.ttc_volume_runtime_perPhase` | `Ttc/Exec/TtcSlowRuntimePerPhase.lean:1094` | sharp slack **+ P2**: per-phase stream count, retry cap and `n`-aware radius |

Residual input conditions on each: `0 < eps`, `eps ≤ 1`, `0 < delta`, `delta ≤ 1`,
`21 ≤ n`, `phi.IsPositive`, `0 < volSol …` — **identical across all three**, including the
dimension threshold. `lake build Ttc` green at **9464 jobs**; `#print axioms` on all three
= `[propext, Classical.choice, Quot.sound]`.

**How to re-check in two minutes** (do not trust this table):

```
lake build Ttc
echo 'import Ttc
#check @Ttc.TtcSlowRuntimeSharp.ttc_volume_runtime_sharp
#print axioms Ttc.TtcSlowRuntimeSharp.ttc_volume_runtime_sharp
#check @Ttc.TtcSlowRuntimePerPhase.ttc_volume_runtime_perPhase
#print axioms Ttc.TtcSlowRuntimePerPhase.ttc_volume_runtime_perPhase' > /tmp/p.lean
lake env lean /tmp/p.lean
```

Read only the printed **type**. The check that matters: `slowSharpImplementation` /
`slowPerPhaseImplementation` appear with no arguments. If either ever acquires one, that
capstone has stopped being unconditional and this section is wrong.

### The complexity, stated honestly

Charged-cost, per polytope, `ρ` the aspect ratio, `L = log(16nρ²)` absorbed into `Õ`:

| state | total |
|---|---|
| baseline | `Õ(m n⁹ ρ⁸ / ε⁴)` |
| P1 sharp — wired | `Õ(m n⁷ ρ⁸ / ε⁴)` |
| **P1 + P2 per-phase — operative** | **`Õ(m n⁶ ρ⁸ / ε⁴)`** |
| paper `thm:runtime` | `O(m n⁵ ρ² r_max)` |

**Three claims this section explicitly does NOT make**, each of which was asserted at
some point during development and is false or unproved:

1. **Not "P1 proves a factor `n²`".** What is machine-checked is `sharp ≤ loose`
   (`CVSharpSlowSteps.slowSharpStepsEnvelope_le_min`,
   `CVSharpUniformParameters.slowSharpRetriesCap_le_slowUniformRetriesCap`), both
   **conditional on `2 ≤ n` and `1 ≤ R`**. The `n²` reading comes from the share-floor
   exponent dropping `8nR² → 8R²`; that drop is *not* formalised as a numeric factor,
   and the capstone's proof does not use either inequality — it cites them.
2. **Not "P1 + P2 reach the paper's `n⁵`".** They reach `n⁶`. P2 is worth a factor `n`,
   not `n²`: it divides the stream count `k` by `n`, and its second effect (raising
   `blockShare` by `n/6`) is invisible because the share floor is
   `min (blockShare) (exp branch)` and the exponential branch dominates the `min`.
3. **Not "the charged cost is a runtime".** Item 4 of §0f's list is unchanged:
   `Ttc.VolumeAlgorithm` still has no complexity field, so all charging happens
   outside, in `Ttc.ttcPolyCost`. These are charged-cost statements.

### P2 was blocked; the repair, and what it cost (2026-08-18)

**Resolved — this subsection is kept as the record of *why* `perPhaseSlack` carries a `/6`
divisor and an `n`-aware mean-tail floor.** As first declared,
`exists_slowOneRunCertificate_canonical_perPhase` was unreachable at its own schedule; the
diagnosis below is what the repair answers, and it is now discharged
(`Ttc/Exec/CVPerPhaseFrontier.lean`: `perPhase_canonical_hphaseMoment`,
`perPhase_canonical_hsteps`, `perPhase_mix_add_tail_transport_le`).

**The repair, in two parts.** (A) `perPhaseSlack` divides the transport allowance by `6`,
buying the tail a `(5/6)·(2/n)·ratio²` budget the original declaration had spent entirely on
mixing. (B) `perPhaseMeanTailFloor` takes `min (scoreAwareMeanEta m k eps / 4)
(1 / (6·n·exp(R²/(2·slowSourceInitialVariance n))))` — the `n`-aware floor the constant-divisor
analysis below correctly predicted was also needed. The price is a larger truncation radius:
`q²` grows by `4·log n / n`, i.e. additively in `log n` and *shrinking* relative to `q²`
itself, which is why the factor `n` survives into the total. The §3-vs-§6 deadline/radius
mismatch noted below was closed by routing the capstone through `perPhaseStepsEnvelope` and
`perPhaseQEnv` rather than the score-aware pair.

**What it did not cost: accuracy.** The two accuracy facts were pinned at
`k := correctedRuntimeSamples` and monotonicity runs the wrong way for the smaller per-phase
`k`, but both are true at **every** `k` — `CVGaussianScoreAwareMeanBudget.lean:131` bounds
`correctedAlpha⁴ ≥ 1` and then spends the sample count to recover the factor, where
`correctedAlpha⁴ ≥ correctedAlpha` gives the same bound with no constraint on `k`. The
`k`-generic forms are `slowAccuracyRequested_half_lt_one_any` and
`slowAccuracyRequested_half_le_any` (`Ttc/Exec/TtcSlowRuntimePerPhase.lean:484`, `:496`). So
the per-phase route pays **nothing** in accuracy for its `n`-fold smaller stream count, and two
shipped lemmas turned out stronger than their statements admitted.

**The original diagnosis follows, unedited.**

The binder that fails is `hphaseMoment` (`Ttc/Exec/CVPerPhaseFrontier.lean:1208`) — the
only route to `factor := perPhaseFactor`, i.e. the binder the whole factor `n` is paid for
by. Every proved way to it goes through
`CVSharpFactorSeven.operational_path_phaseScore_memLp_and_sq_moment_le_factor_of_targetTV_bound`,
whose `hslack` (`:357`) demands

```
(mixError i + targetError).toReal * (B² * (1 + 2T))  ≤  (T − C) * ratio²
```

Note the LHS carries **`mixError + targetError`**. What the declared schedule supplies is
`CVGaussianScoreAwareParameters.scoreAwareMixError_mul_boundSq_le_slack` (`:123`):

```
mixError i * boundSq i  ≤  slack i
```

— **exactly tight, no divisor.** At `perPhaseSlack = (2/n)·ratio²` and
`perPhaseBoundSqGen = E²·(3+8/n)`, the mixing error alone saturates the entire budget and
the radial tail `targetError` has nowhere to go. The loose route declares
`slowUniformSlack = phaseMomentSlackSeven/2` and the sharp route `slowSharpSlack = …/6`;
**those divisors are precisely the headroom that pays for the tail.** `perPhaseSlack`
declares the mixing slack at the full transport allowance `(C−1)·ratio²` with none.
`CVPerPhaseMomentBundle`'s own Step 9 docstring (`:931–934`) admits this in advance.

Verified here independently of the agent that reported it, by reading all four definitions.

**Why the repair is not a one-token change.** A constant divisor `c` leaves
`(1−1/c)·(2/n)·ratio²` for the tail — an `O(1/n)` allowance — while the available tail
budget (`slowTargetError_rAware_scaled_le` + `slowCanonical_htailBudget`) is a **constant**
fraction of `ratio²`. So a divisor alone works below a fixed `n` while the theorem
quantifies over all `n ≥ 21`. The repair needs an `n`-aware mean-tail floor as well, i.e. a
larger global truncation radius `q` at logarithmic cost. A second, independent gap also
survives the slack repair: `CVPerPhaseFrontier` §3's step bound is at `slowScoreAwareSteps`
(fixed warm) + `slowGlobalRadiusQ`, while §6 needs `slowCanonicalSteps` (compounding warm) +
`slowUniformQ` — wrong deadline function and wrong radius.

**A `def` hazard, now partly discharged**, flagged per §11 — the three cases differ and the
file's boxed warning (`TtcSlowRuntimePerPhase.lean:50`) separates them:

* `slowPerPhaseOV n R2 eps p` — **certified**. `ttc_volume_runtime_perPhase` bounds the real
  run's expected query cost at exactly this constant. It is `slowPerPhaseOVGen` at the two
  per-phase slots `perPhaseLenv` / `perPhaseTenv` **and at no other pair**.
* `slowPerPhaseOVGen` and `slowPerPhaseOverhead … Lenv Tenv` — **declared only**, parametric in
  `(Lenv, Tenv)`; nothing runs within them at an arbitrary pair.
* `slowPerPhaseOV_le_slowSharpOV` **no longer exists**, and could not: once `slowPerPhaseOV`
  sits at the per-phase envelopes the two routes run at different share floors, retry caps and
  truncation radii, so the comparison is false as stated. Its content survives verbatim as
  `slowPerPhaseOVGen_sharpEnv_le_slowSharpOV` (`:752`) at explicit *sharp* slots — a comparison
  of two declared envelopes, not a runtime claim. The honest quantified payoff is
  `nmul_slowPerPhaseRetained_le_three_slowActualRetained` (`:284`): factor `n/3` in the retained
  scalar at a **common** `(Lenv, Tenv)`.

**What the estimate missed.** The trade quantification that authorised this route priced
the `log(1/share)` cost of the tighter slack. It was right about that (the realised ratio
`(9n+24)/36` is additive in `log n`, and negative at the sharp exponent). It did not price
two feasibility constraints: the first-moment layer, which the frontier agent repaired with
`perPhaseMixError_succ_mean_le_half`, and the **radial tail**, which is what blocks. A cost
comparison is not a feasibility check, and this route needed both.

### The `IsWarm` experiment: BLOCKED, and why that verdict saved the program (2026-08-18)

Run as a single decision experiment before any implementation, on the reasoning that if `IsWarm`
could not be obtained from something weaker than measure equality on `c . K`, the whole L1-L4
chain was wasted effort. File: `Arlib/Convexity/GaussianCooling/WarmTransportExperiment.lean`,
6 declarations, `lake build` green at 2588 jobs, all `[propext, Classical.choice, Quot.sound]`.

**The hypothesis was right about the lemma it named.** Warmness need never be transported: run the
mixing chain on the measure that is warm and pay the gap additively. `Arlib.TVLe` already had
everything — `TVLe.trans` (`Arlib/Probability/TV.lean:142`) and the hypothesis-free kernel
pushforwards `MarkovChains.tvLe_step` / `tvLe_iterate` (`Warmness.lean:293`, `:303`) — so the
transport lemma is one line:

```lean
theorem tvLe_iterate_of_isWarm_source … :
    Arlib.TVLe (Arlib.MarkovChains.iterate P mu t) pi (eps + zeta) :=
  (Arlib.MarkovChains.tvLe_iterate P hclose t).trans (hmix nu0 hwarm inferInstance)
```

And `map_combinedOutput_condOn_ellGaussianProb_eq_coolLaw` really can be dissolved at all 13 of
its uses: the 4+ TV-side ones absorb the `+eps` inside the existing `zeta <= 1/16` and
`32*zeta + (eta + contraction^L)` budget; the 4 warm-side ones go through the **delta-free**
factorization `map_combinedOutput_condOn_proposal` (`CVIdealCombinedAccepted.lean:97`, no delta
binder) plus `ell <= 1` plus `IsWarm.trans`, needing only the averaged deficit `Z >= 1 - eps`.

**What blocks is one step later, and is a SECOND, independent use of `ell = 1` on `c . K`.**
`isWarm_standardScaledRaw_coolLaw_succ_ellGaussianProb_ratio`
(`Ttc/Exec/CVGaussianAdaptiveAcceptedWarm.lean:44`) turns its `hdeltan : delta <= 1/(2n)` into
`hdc : delta <= 1 - c` and feeds
`Arlib.GaussianCooling.isWarm_ellGaussianProb_of_supported_on_shrunken`
(`Arlib/Convexity/GaussianCooling/WarmSpeedy.lean:149`, binder `hdc` at `:151`). Its conclusion
puts `ellGaussianProb` in the **reference** slot — `ell` in the *denominator*. The next phase's
warm start must be warm against the ell-weighted stationary law of the next phase's chain, and
that reference is intrinsic: the mixing theorem's `hwarm` is against the kernel's own stationary
measure, which at `delta ~ 1/sqrt n` *is* the deficient weighting.

**Machine-checked no-go** for the algebraic escape (`ell` in a denominator, `top * 0 = 0`):

```lean
theorem not_exists_isWarm_transport_of_tvLe_reference :
    not exists f : ENNReal -> ENNReal -> ENNReal,
      forall mu nu nu' M eps, IsWarm M mu nu -> TVLe nu nu' eps -> IsWarm (f M eps) mu nu'
```

Witness `mu = dirac true`, `nu = eps*dirac true + (1-eps)*dirac false`, `nu' = dirac false`: the
perturbation is arbitrarily small and the constant destroyed arbitrarily good, so the failure is
not quantitative. A pointwise `ell >= const` on `c . K` would be needed instead, and (in prose,
not formalised) that is false for legal `K` at `delta ~ 1/sqrt n` — points of `c . K` are only
`1 - c = 1/(2n)` deep while the ball has radius `1/sqrt n`.

**Two restructurings could clear it; both are separate programs, not additions.** A KLS97-style
truncation restricting to `{ell >= 3/4}` and paying the volume deficit (already stubbed:
`KLS97Shell.lean`, `PhaseSamplerTVTruncated.lean`); or an **ell-carrying seed** that never strips
`ell` in the rejection step, where the pure-convexity bound `ell(c.x) >= c^n ell(x) >= ell(x)/2`
matches the two `ell` factors with **no pointwise floor at all**. The second looks materially
cheaper and is the one to scope if P4 is revisited.

**Value of the experiment:** an OPEN verdict would have sent three agents to build the
Gaussian-weighted deficit bound and both halves of the `1/8`, and they would have hit
`CVGaussianAdaptiveAcceptedWarm.lean:88` at the end. This is what the experiment existed to
prevent, and it is the pattern to repeat before any further P4 work.

### KLS scoping result, 2026-08-18 — the question dissolves, and P4 is worth `n` only

Scoped before dispatching work, after mis-scoping `hLem41` by not surveying. Two corrections to
what this file said an hour earlier, both decided by reading the definitions:

**1. P4 is worth a factor `n`, NOT `n·rho^2`.** On the other `min` branch
`delta = sqrt s / (max 8 (2q) * sqrt n)`, the variance **does** cancel in `s/delta^2` — but
`q^2 = 16 + 4 log(20A)/n` with `A ~ exp(R^2/(2 s0))/(20 b)` is `16 + Theta(rho^2)`, and on that
branch `q^2` enters the deadline **multiplicatively** through `max(8, 2q)^2`. So

```
delta = 1/(2n)                         deadline = Theta(s * P * n^3)   = n^3 rho^4
delta = sqrt s/(max 8 (2q) sqrt n)     deadline = Theta(max(8,2q)^2 * n^2 * P) = n^2 rho^4
```

`s` cancels exactly (independently confirmed by `AdjustableRadiusSampler.lean:86-92`, which is
that algebraic identity, and by `AdjustableRadiusGaussian.lean`'s docstring at `:14-17`), and the
`rho` exponent is **unchanged**. So the earlier claim in this file — that the last `n` and the
last `rho^2` are one obstruction — is **wrong on the `rho^2` half**. Its justification ("`q`
enters only as `log F`, paid once") holds on the `1/(2n)` branch, where `q` appears only through
the truncation radius; it fails on the other branch. Switching branches recovers `n` and **no**
`rho^2`.

**2. The local-conductance floor is not what blocks the branch switch.** The mixing/conductance
chain takes **no** local-conductance input at all: `conductance_speedyMetropolisGaussian_ge_uncond_adjustable`
(`Arlib/MarkovChains/Continuous/AdjustableRadiusGaussian.lean:238`) has hypotheses `21 <= n`,
`1 < q`, positivity, `delta <= sigma/(max 8 (2q) sqrt n)`, measurable/convex/nonzero-volume `K`
and a radius bound — **no `hell`, no `hiso`** — and its step binder is already the `sqrt n`
branch. Verified by reading the statement. Moreover the averaged bound the KLS route would supply
**already exists unconditionally at `delta ~ 1/sqrt n`**:
`Arlib.isSmooth_sqrt_of_ball_subset` (`Arlib/Convexity/SmoothSqrt.lean:620`), with no isotropy,
well-roundedness or diameter hypothesis. Its only consumers are in `UniformSamplerSharp.lean`;
nothing in the Gaussian chain uses it.

**What actually forces `delta = 1/(2n)`** is the **speedy-to-target rejection map and the
`IsWarm` transport riding on it**. `map_combinedOutput_condOn_ellGaussianProb_eq_coolLaw`
(`Ttc/Exec/CVIdealCombinedAccepted.lean:121`) is an **equality of measures**, `rw`-consumed into
an `IsWarm` hypothesis at `CVGaussianAdaptiveAcceptedWarm.lean:161`. `IsWarm` is an `L-infinity`
density-ratio bound; an averaged argument yields only TV, and **this repository already contains a
machine-checked refutation of that weakening**: `Arlib.exists_supported_on_shrunken_not_isWarm`
(`Arlib/Convexity/GaussianCooling/WarmSpeedy.lean:102`) — a Dirac supported on the shrunken body
with `forall M, not IsWarm M`, `M = infinity` included. Verified by reading it.

**The one decision-relevant experiment**, before any implementation work: can `IsWarm` for the
accepted output be obtained from anything weaker than measure equality on `c . K`? If not, the
whole L1-L4 chain (a Gaussian-weighted deficit bound, a TV version of the shrunken-body equality,
and the two halves of the `1/8`) is wasted effort. The `1/8` itself is `(1/2) * (1/4)` and **both**
halves rest on exactness. A replacement floor in `[1/16, 1/8]` re-threads mechanically; below
`1/16` it additionally forces a generic replacement for `isWarm_condOn_sixteenth`
(`Ttc/Exec/CVGaussianAcceptedWarm.lean:53`), whose `1/16` is baked into its proof.

Note this makes P4 **not** comparable to localization-for-indicators in kind: nothing in Mathlib
is missing here (unlike `hLov`/KLS97 Cor 4.6, AUDIT section 0m, which needs boundary Hausdorff
measure). It is new analysis plus one architectural unknown, not a capability gap.

### Why the `delta = 1/(2n)` cap cannot simply be relaxed (P4), 2026-08-18

Investigated because the cap is the single largest avoidable term in the development: on the
other branch of `radiusQDelta`'s `min` the variance **cancels**, making the per-phase deadline
both `rho`-free and one power of `n` cheaper — worth `n·rho^2`. It is **not** an arbitrary
constant, and relaxing it is not an engineering change. The chain, verified by reading it:

1. `Arlib.MarkovChains.ell_eq_one_on_shrunken` (`Arlib/MarkovChains/Continuous/KLS97Shell.lean:111`)
   — for `x` in the shrunken body `c·K` and `delta <= 1 - c`, the local conductance is
   **exactly 1**, because `ball (c•y) (1-c) ⊆ K` by convexity together with `ball 0 1 ⊆ K`.
2. `Ttc.CVIdealCombinedAccepted.eighth_le_ellGaussianProb_combinedAccept` (`:181`) consumes it at
   the hard-coded `c = 1 - 1/(2n)`, with hypothesis `hdeltan : delta <= 1/(2n)` (`:185`), to
   produce the `1/8` acceptance floor.
3. `Ttc.CVHybridRadiusQOperationalLocalPair` (`:120`) is where the two meet: `hdeltan` comes from
   `radiusQDelta_le_n`, and `hdeltaC : delta <= 1 - c` is *literally the same number*.

**So `1/(2n)` in `radiusQDelta` and `1/(2n)` in `c` are one quantity, and the binding constraint
is `c^n = Theta(1)`.** At `c = 1 - 1/(2n)`, `c^n -> e^{-1/2} ~ 0.607` — a constant, which is what
makes `1/8` available. At the step size we want, `delta ~ 1/(2*sqrt n)`, we would need
`c = 1 - 1/(2 sqrt n)` and then `c^n ~ e^{-sqrt n / 2}` — **exponentially small**, destroying the
acceptance floor and everything downstream of it.

`delta = O(1/n)` is therefore **tight for the shrunken-body technique**, not a lossy bound. The
inradius is pinned at 1 by `ball 0 1 ⊆ K`, so there is no slack to exploit in the hot phases
either: the body grows, but the inradius does not.

**The two real routes, both research:**

* **Average local conductance (KLS97 s-conductance).** Replace "`ell = 1` pointwise on a shrunken
  body" with a bound on `∫ ell`, which stays near 1 at `delta ~ 1/sqrt n` because only a thin
  boundary shell has `ell < 1`. This is the standard literature route and would give the `n`.
* **Hit-and-run (Lovász–Vempala 2005).** No step size at all, so the whole `radiusQDelta` question
  disappears. Already stated as `Arlib.MarkovChains.tvLe_iterate_hitAndRun_unitBall`
  (`HitAndRunMixing.lean:944`) with three open binders — `hLem41` (spherical-cap estimate
  `q2 < 3/8`), `hIso` (localization), `hLS` (lazy-vs-plain modelling fork). Ledger in §0h.

**Recommendation: hit-and-run.** It subsumes the s-conductance route, and it is also the only one
of the two that touches the residual `rho^4` — which is a *proved* lower bound for the ball-walk TV
accounting (`CVRetryDeadlineSplit.log_ratio_sq_le_scoreAwareRetries_mul_payload`) but is a
property of the walk, not of TTC. LV bound the conductance of every subset rather than needing an
`s`-conductance argument, which is precisely what removes the polynomial dependence the ball walk
cannot shed.

### What actually remains

* **`ρ⁶`.** Of this, `ρ⁴` is a proved **lower bound** — `CVRetryDeadlineSplit`'s
  `log_ratio_sq_le_scoreAwareRetries_mul_payload` shows it is structural to the TV
  accounting, not an artefact of a lossy bound. One `ρ²` is recoverable on the cost side —
  see the next subsection, which corrects both the route and its advertised price.
* **One factor `n` — and, CORRECTED 2026-08-18, this is NOT the same obstruction as the last `ρ²`.** `Tenv ∝ n³` via
  `σ_m · n / δ_Q²` with `δ_Q = 1/(2n)` — the `radiusQDelta` `min` resolving to `1/(2n)`
  rather than `√σ/(max 8 (2q)√n)`. On the other branch `σ/δ² = q²n` is both `ρ`-free
  and one power of `n` cheaper. This is a local-conductance question: research.
* **`thm:decompose`** — still not formalised at all, still not planned.

### The `retryEnv` lever: Route A dead, Route B priced, Route C live (2026-08-18)

`RUNTIME-ENDGAME.md` advertised this as "one factor `L ≈ ρ²` off the total". That was a
payoff quoted without its price, and the route it named does not work. Full analysis in
`PLAN-RETRYENV.md`; the load-bearing findings:

1. **Route A (a pointwise cost bound) is dead.** `roundQueryCost` is a sum of
   `Arlib.MarkovChains.properProposalWaitCost` terms, and that is a **tail-sum geometric
   waiting time** with no pointwise bound. The plan's escape hatch — "if
   `acceptance_floor_le_speedyMetropolisMove` gives `ℓ ≥ c`, Route A wins outright" — is a
   **conflation**: that floor bounds the *Metropolis acceptance factor*, not the local
   conductance, and it takes `hstuck` (i.e. `ℓ(x) > 0`) as an input rather than proving it.
2. **Mass-scaled warmness is dead**, by the counterexample the plan itself records: warmness
   bounds the density, not the mass.
3. **Route B (the L²(π) route) reduces exactly to `Q = (∫_K ℓ⁻¹ dγ)/(∫_K ℓ dγ)`** — the
   quantity the speedy walk was *invented to avoid*. The `ℓ`-weighting of the reference law
   makes the first moment of `ℓ⁻¹` trivial and the second moment a *first* moment of `ℓ⁻¹`
   under Lebesgue, which the averaged-conductance hypothesis does not control. Do not build
   Route B without first pricing `Q`.
4. **Route C is live and its mathematics is proved.** Hölder at `p = 1 + 1/(2n)` against the
   warm density needs only a *fractional* moment of `ℓ⁻¹`, and never touches `Q`.
   `Arlib/MarkovChains/Continuous/LocalConductanceMoment.lean` (22 theorems),
   `Arlib/MarkovChains/Continuous/WarmHolder.lean` (5), `Ttc/Exec/CVHolderRetryCost.lean` (6)
   — all zero `sorry`, all `[propext, Classical.choice, Quot.sound]`. The headline is
   `Ttc.CVHolderRetryCost.lintegral_stepCost_rpow_le`: `∫ ((ℓ·acc)⁻¹)^{1+1/(2n)} dπ ≤ 80`, an
   absolute constant, where at `p = 1` the same integral is the *existing* `10/3`.
5. **The honest price, which the old plan omitted.** `Lenv` goes from `ρ²` to
   `min(ρ², O(n))` — the Hölder conjugate `q ≈ 2n` is intrinsic, coming from
   `ℓ ≳ (u/δ)^n`, i.e. from local conductance genuinely being exponentially small in `n` at a
   sharp corner. So the total becomes `Õ(m · n⁶ · ρ⁶ · min(ρ², n) / ε⁴)`: strictly better when
   `ρ² > n`, never worse, worst case `Õ(m n⁷ρ⁶/ε⁴)`. **It trades one `ρ²` for one `n`. It is
   not a free `ρ²`.**

**Nothing above changes the operative complexity.** It stays `Õ(m n⁶ρ⁸/ε⁴)` until a *fourth
capstone* states the Hölder envelope. Arlib theorems and a cost lemma certify mathematics;
only a capstone certifies TTC's runtime. The two remaining steps, and why the second is the
long pole, are in `PLAN-RETRYENV.md` §5.

---

## 0g. An unconditional polynomial-time uniform sampler — and why TTC is still not polynomial (2026-08-12)

> ## ⚠ READ BOTH COLUMNS ⚠
>
> **Landed.** There is now a **uniform sampler on a convex body whose mixing bound
> is a theorem with no mathematical hypothesis at all** — no isoperimetry binder,
> no warm-start binder, no smoothness binder, no comparability binder. Hypotheses:
> `2 ≤ n`, `K` measurable and convex, `B(0,1) ⊆ K`, a diameter bound `D`, and
> `0 < ρ ≤ 1`. Step count `O(n⁴·D²·log(1+D)/ρ²)`. It is packaged in the exact shape
> `Ttc.HitAndRunTheorem11Input.mixing` demands, and priced.
>
> **Not landed.** **`Ttc.ttc` and `Ttc.ttcPoly` are not rewired onto it.**
> `HitAndRunTheorem11Input` is still the assumed, nowhere-inhabited contract every
> `Ttc/Exec/` sampling number rests on; `Ttc.ttcSampPrice` is unchanged and still
> `Θ(4ⁿ(γ+Dm)^{4n}/γ^{4n})`; the *volume* oracle is exponential independently and by
> construction (§0, `Ttc.ttcVolPrice`). **Nothing in this subsection makes TTC run in
> polynomial time, and none of it may be quoted as if it did.**

### The Arlib stack: three binders, three theorems

`Arlib.MarkovChains.mixesWithin_lazy_speedyWalk_uniformOn`
(`MarkovChains/Continuous/SpeedyToUniform.lean:226`) consumes exactly three mathematical
inputs. Each is now produced:

| binder | discharged by | the constant |
| --- | --- | --- |
| `hiso` — isoperimetry for `ellProb K δ` | `Arlib.hiso_ellProb_of_ball_bound` ([`Convexity/LogConcaveIso.lean`](Arlib/Convexity/LogConcaveIso.lean)) | **`κ = 1/(8R)` for `K ⊆ B(0,R)` — free of `n`.** Proved by pinning `σ = 2R` in the Gaussian-tilt isoperimetry `gaussianRestricted_isoperimetry_openClosed_logTwo` (§0e), *not* by a `σ → ∞` limit, which sends the coefficient to `0`. The literature's sharp constant is `2/D` in the `min` form; **this is `1/(8D)` in the product form, and the file says so** |
| `hwarm` — a warm start *for `ellProb K δ`*, not for `uniformOn volume K` | `Arlib.MarkovChains.isWarm_uniformOn_unitBall_ellProb` ([`MarkovChains/Continuous/WarmEllProb.lean`](Arlib/MarkovChains/Continuous/WarmEllProb.lean)) | `M = (1+D)ⁿ·vol K/vol B(0,1)`, from the **samplable** start `uniformOn volume (ball 0 1)`. **Exponential in `n`, and that is fine**: only `log M` enters `conductanceMixingTime`. Contrast `IsWarm.refl` (`SpeedyWalk.lean:1343`), which starts the chain from its own stationary law and is useless as an algorithm |
| `hsmooth : IsSmooth K δ s` | `Arlib.MarkovChains.isSmooth_of_ball_subset` ([`EllFloor.lean:549`](Arlib/MarkovChains/Continuous/EllFloor.lean)) at `s = 1 − (1−δ)ⁿ ≈ nδ`; sharpened by `isSmooth_sqrt_of_ball_subset` ([`SmoothSqrt.lean:620`](Arlib/MarkovChains/Continuous/SmoothSqrt.lean)) to `s = 4e²δ√n` | `IsSmooth` is an **average** condition, not a pointwise floor — which is why it is satisfiable where §0e's pointwise `hell`/`hfloor` is *provably not* |

Composition: [`SpeedyUniformPoly.lean`](Arlib/MarkovChains/Continuous/SpeedyUniformPoly.lean)
(tunes `δ` so the bias is a named `ρ` rather than an opaque `s/(1−s)`) →
[`UniformSamplerUncond.lean`](Arlib/MarkovChains/Continuous/UniformSamplerUncond.lean) →
[`UniformSamplerSharp.lean`](Arlib/MarkovChains/Continuous/UniformSamplerSharp.lean).

### Two routes, and TTC's backend is on the *slower* one

Both are unconditional. They differ only in the step size `δ`, and the step count is `δ⁻²`.

| route | `δ` | `φ` at `κ = 1/(8D)` | steps | theorem |
| --- | --- | --- | --- | --- |
| **uncond** | `ρ/(4n)` | `min(1/32, ρ/(8192·D·n²))` | `O(n⁵·D²·log(1+D)/ρ²)` | `mixesWithin_lazy_speedyWalk_uniformOn_uncond_steps` (`UniformSamplerUncond.lean:339`) |
| **sharp** | `ρ/(128√n)` | `min(1/32, ρ/(262144·D·n^{3/2}))` | `O(n⁴·D²·log(1+D)/ρ²)` | `mixesWithin_lazy_speedyWalk_uniformOn_sharp_steps` (`UniformSamplerSharp.lean:358`) |

⚠ **Do not read "sharp beats uncond" as a numerical fact at every `n`.** The exponent
improves for all `n`; the *constants* run the other way, and what is proved is
`steps_sharp_le_steps_uncond` (`UniformSamplerSharp.lean:498`) **under `1024 ≤ n`** —
`φ_sharp/φ_uncond = √n/32`, so below `n = 1024` the sharpened route is numerically worse.
`sqrtSharp_sq_gain_eq` (`:457`) is the exact identity `1024·φ_sharp² = n·φ_uncond²`, with no
inequality and no dimension hypothesis.

⚠ **And `Ttc.speedyMixSteps` is built on `ρ/(4n)`** — the `n⁵` route
([`Ttc/Sampler/SpeedyBackend.lean:176`](Ttc/Sampler/SpeedyBackend.lean)). The `n⁴` sharp
route is proved in `Arlib` and **is not what any `Ttc/` declaration consumes**. Rebuilding
`speedyMixSteps` on `mixesWithin_lazy_speedyWalk_uniformOn_sharp_steps` is a *known,
unstarted* task, not a claimed one.

A third route, at `O(n³·D²·log(1+D)/ρ²)`, is proved conditionally in the same file —
`mixesWithin_lazy_speedyWalk_uniformOn_sqrtCond` (`:619`) still carries `hiso` and
`hwarm` as well; **`…_sharp3` (`:701`) is the one to read**, with `hiso`/`hwarm`
discharged and `hcomp` the *single* remaining mathematical binder — resting on the
conductance sharpening
`conductance_speedyWalk_sqrt_ge` ([`SpeedyConductanceSqrt.lean:277`](Arlib/MarkovChains/Continuous/SpeedyConductanceSqrt.lean)),
whose binder is
`hcomp : ∀ x y ∈ K, ‖x − y‖ ≤ δ/√n → ell K δ x ≤ ofReal (3/2) · ell K δ y`.
**`hcomp` is unproved.** The `K_δ`-shrinkage route to it is refuted in the same file:
`ell_goodPoints_le_ell` runs the wrong way, and confinement forces `1 − vol S/vol K ≤ r` at
every finite `t` (`obstruction_ballOne_in_ballTwo`, `UniformSamplerSharp.lean:892`).

### The `Ttc`-facing layer

| file | what it is |
| --- | --- |
| [`Ttc/Sampler/SpeedyBackend.lean`](Ttc/Sampler/SpeedyBackend.lean) | `Ttc.speedyMixSteps`, and `tvLe_iterate_lazy_speedyWalk_uniformOn_at_steps` — the conclusion of `HitAndRunTheorem11Input.mixing` **as a theorem**. `..._ballTwo_dim2` (`:600`) discharges every hypothesis at `K = B(0,2)`, `n = 2`, `ρ = 1/2`: a zero-hypothesis instance, which is precisely what `HitAndRunTheorem11Input` has never had |
| [`Ttc/Sampler/SpeedyBackendUncond.lean`](Ttc/Sampler/SpeedyBackendUncond.lean) | `tvLe_transport_inscribedAffine` discharges the `hequiv` scaling-equivariance seam, via `SpeedyAffine.map_speedyWalk_affineChart` ([`SpeedyAffine.lean`](Arlib/MarkovChains/Continuous/SpeedyAffine.lean): `D ↦ D/γ`, `δ ↦ γδ`, `ρ` unchanged), so the `B(0,1) ⊆ K` normalisation is not a restriction. Witnesses at `γ ≠ 1` |
| [`Ttc/Exec/SampPricePoly.lean`](Ttc/Exec/SampPricePoly.lean) | `drawOpCharge_le_poly` (`:303`): `≤ 2³⁰·n⁶·rfac·(Dm/γ)²·(log(1+Dm/γ) + log(2/ρ))/ρ²`. The `n⁶` is the `n⁵` route × `n` per draw |
| [`Ttc/Exec/SpeedySamplerChain.lean`](Ttc/Exec/SpeedySamplerChain.lean) | `speedyWalk_mixes_and_drawPrice_le_poly` (`:260`) — mixing **and** price at the same `t`, in one conjunction |

### The comparison against the incumbent exponential price — per route, with the threshold

Three separate numbers. **Collapsing them to one is an error**; each is proved against a
different right-hand side.

| claim | against | file:line |
| --- | --- | --- |
| polynomial price is **larger** at `n = 2` | `mixStepsBound` | `expTerm_lt_polyPrice_at_dim_two`, `SpeedySamplerChain.lean:308` |
| polynomial price ≤ exponential at **`n = 3`** | `mixStepsBound` (`= 16384·4ⁿ·n²·(D/γ)²·((γ+D)/γ)^{4n}·(…)`) | `polyPrice_le_expTerm_at_dim_three`, `:347` |
| polynomial price ≤ exponential at **`n = 29`** | `2048·4ⁿ·log(√Mw/eps)`, a *lower* bound on `mixSteps` itself | `polyPrice_le_expLowerBound_at_dim_29`, `:426` |
| polynomial is `o(exponential)` in `n`, at fixed geometry | `mixStepsBound` | `polyPrice_isLittleO_mixStepsBound`, `SampPricePoly.lean:504` |

### The structural blocker — why `poly ≤ ttcSampPrice` is not merely unfinished

The chain to `Ttc.ttcSampPrice` **at TTC's own arguments** is not closed, and the reason is
not a missing lemma. The polynomial bound carries `1/ρ²` where the exponential bound carries
`log(1/eps)`. Fixing `n` and sending the accuracy to `0`, the two diverge in opposite
directions, so **no comparison uniform in the accuracy parameter exists**, at any dimension
threshold. `polyPrice_isLittleO_mixStepsBound` is stated at *fixed* `ρ`, `eps` for exactly
this reason. The bookkeeping items on top of that blocker — `2·ttcSampInradius ≤
ttcSampDiamPrice`, `ttcSampTolPrice ≤ 1`, an `rfac` bound — are real but secondary.

⚠ **This blocker is `speedyWalk`-specific, and the earlier text here overstated it.**
Struck: ~~any reading on which this is an obstruction *for TTC*~~. Lovász–Vempala,
*Hit-and-Run from a Corner* (2005), Thm 1.1 gives hit-and-run
`m > 10¹⁰·n²R²/r²·ln(M/ε)` — **logarithmic** in `1/ε` — and says in terms that the
polynomial dependence is *"unavoidable for the ball walk"* and is what hit-and-run
removes. That is the route `Ttc.HitAndRunTheorem11Input` has always named, and it is
already stated in this repository: `Arlib.MarkovChains.tvLe_iterate_hitAndRun_unitBall`
(`HitAndRunMixing.lean:944`) with `Arlib.MarkovChains.lvThreshold` (`:829`) carrying the
`ln(M/ε)`. So the `1/ρ²` above is a fact about the *speedy/ball* backend of §0g and about
its comparison to `ttcSampPrice` — **not** a barrier to a polynomial-time TTC. See §0h.

With that scoping, the rest stands. It is
`README.md` finding **§19** ("the speedy walk's stationary bias does not decay with
time") surfacing in the price algebra. The `1/ρ²` is there because the bias is a
property of the *stationary* law `ellProb K δ`, so it is removed only by shrinking `δ`,
and `δ` enters the step count as `δ⁻²`; running longer does not help. At the
lattice-counting tolerance `ρ = θ/V` with `V` exponentially large, `1/ρ²` is itself
exponential — which is exactly §19's conclusion. **One finding, two surfaces.**
Removing it needs the trajectory-level holding-time argument §19 names (conditionally
independent `Geom(ℓ(Yᵢ))` given the jump chain, on a `Kernel.traj` trajectory measure);
nothing in this subsection attempts it.

### Also landed, and what it does *not* upgrade

* [`Arlib/Convexity/GaussianCooling/WarmChain.lean`](Arlib/Convexity/GaussianCooling/WarmChain.lean)
  — `isWarm_coolLaw_succ_exp`: each Gaussian-cooling phase is **`e`-warm** for the next,
  free of `n`, under the schedule `σ²ᵢ₊₁ ≤ (1 + 2/n)σ²ᵢ`. Crux `chain_succ_le_pow_mul`
  (`Z(i+1) ≤ λⁿZ(i)`) by the rescaling `x ↦ λx`, shorter and slightly more general than
  Cousins–Vempala's polar/cone argument. This is why the cooling-ratio binder
  `cc ≤ 1 + 2/n` (§0a, binder #33) has the shape it has.
* [`Arlib/MarkovChains/Continuous/BallWalkTransfer.lean`](Arlib/MarkovChains/Continuous/BallWalkTransfer.lean)
  — `le_conductanceS_lazy_ballWalk_of_ball_subset` (`:479`): a **polynomial `s`-conductance**
  bound, `min(1/16, ofReal(1/(8R))·ofReal(δ/(2n))/64)/2`, on the exact kernel
  `Ttc.ballWalkLaw` iterates, every binder discharged.
* **None of this touches `hphase_mean`/`hphase_var` or CV's `thm:iso`.** §0e's "sharp
  constant remains open" stands: `κ = 1/(8R)` is a *ball-bound* isoperimetry for the speedy
  walk's own stationary law `ellProb`, a different object from the Gaussian-restricted
  measure the volume oracle needs. ~~The Gaussian-target chain still wants a kernel
  reversible for `1_K·ℓ·γ`, and no such kernel is verified in this repository.~~
  **Corrected later the same day — see the next bullet; that sentence was written before
  `SpeedyGaussian.lean` was verified and is false.**
* [`Arlib/MarkovChains/Continuous/SpeedyGaussian.lean`](Arlib/MarkovChains/Continuous/SpeedyGaussian.lean)
  — **the kernel reversible for `1_K·ℓ·γ` now exists.**
  `Arlib.MarkovChains.speedyMetropolisGaussian` (a speedy proposal with a Gaussian
  Metropolis filter) is a Markov kernel, and `isReversible_speedyMetropolisGaussian`
  (`:446`) proves it reversible for `ellGaussianMeasure K δ s`, the measure with density
  `ℓ·e^{−‖x‖²/(2s)}` on `K` — **with no convexity of `K` and no positivity of `δ` or `s`**,
  only `MeasurableSet K`. Corollaries for the normalised `ellGaussianProb` and for
  invariance. The crux is `ellGaussian_mul_speedyMetropolisGaussian`, in which `ℓ`
  cancels out of the moving term — that cancellation *is* the speedy device. The stuck-point
  guard is not ported: it is subsumed by the `(1 − m(x))·δ_x` atom.
  `exists_speedyMetropolisGaussian_witness` (`:656`) discharges everything on `K = B(0,1)`
  and proves **`0 < P₀({0}ᶜ) < 1`** — the `< 1` half certifies the filter genuinely rejects,
  so this is **not `speedyWalk` in disguise** (`speedyWalk`'s move probability is exactly `1`
  at every non-stuck point). That is stronger than the repository's `metropolisGaussian`
  precedent.
  ⚠ **Scope: a kernel and its reversibility, and nothing more.** No conductance bound, no
  mixing bound, no spectral gap. `conductance_speedyWalk_ge_of_convex` (`StarPolar.lean:626`)
  is stated for `speedyWalk` and does **not** apply. `conductance_speedyGaussian_ge`
  (`SpeedyConductanceSharp.lean:320`) *is* abstract in its kernel and would accept this one,
  but three things are missing and none is proved for it anywhere: **(1)** `hoverlap` — the
  repository's speedy overlap lemmas are about the *uniform* law on `B(x,δ) ∩ K`, and the
  filter thins it by `min(1, g(y)/g(x))`, so the geometric estimate must be multiplied by an
  acceptance floor re-derived against the speedy normaliser; **(2)** the `hpi` bridge from
  the `ℝ≥0∞` density `ℓ·g` to that theorem's real-density form; **(3)** `hiso` wiring from
  `Arlib.ellGaussian_isoperimetry_measurable_logTwo`, whose `hellKpos`, `hellLip`, `hLσ` must
  be discharged. This is the next work list, not a claim.
* `Ttc.VolumeAlgorithm` still has **no complexity field** (§0f). Nothing above changes that.

---

## 0h. The route of record for the sampler: Lovász–Vempala 2005, and the three binders left

**Source.** László Lovász and Santosh Vempala, *Hit-and-Run from a Corner* (2005),
`faculty.cc.gatech.edu/~vempala/papers/start.pdf`. **Theorem 1.1**, verbatim:

> Let `K` be a convex body that contains a ball of radius `r` and is contained in a ball of
> radius `R`. Let `σ` be a starting distribution and let `σ_m` be the distribution of the
> current point after `m` steps of hit-and-run in `K`. Let `ε > 0`, and suppose the density
> function `dσ/dπ_K` is bounded by `M` except on a set `S` with `σ(S) ≤ ε/2`. Then for
> `m > 10¹⁰·n²·R²/r²·ln(M/ε)`, the total variation distance of `σ_m` and `π_K` is less
> than `ε`.

The paper's own framing of why this is the route: it *"improves on existing bounds by
reducing the dependence on `M` and `ε` from polynomial (**which is unavoidable for the ball
walk**) to logarithmic, while maintaining the optimal dependence on `r`, `R` and `n`."* And
the mechanism: *"At the heart of this theorem is a bound of `Ω(r/(nR))` on the conductance
of **every subset** (Theorem 4.2) — for the ball walk, the conductance of small sets can be
arbitrarily small; therefore the need for a warm start."*

**`Ttc.HitAndRunTheorem11Input` is this theorem.** Its `(M, S, hS, hdom)` clause is LV 1.1's
"bounded by `M` except on a set `S` with `σ(S) ≤ ε/2`" — so residual hypotheses **#21, #22
and #27** (`hS`, `hdom`, `hMwB`) are *the paper's own hypothesis*, not repository debt.
**Owner-authorised 2026-08-12 to remain as hypotheses** ("you can use a hypothesis … that
TTC starts with warmth `M`").

**And LV 1.1 is already stated here, as a theorem, with three binders left.**
`Arlib.MarkovChains.tvLe_iterate_hitAndRun_unitBall` (`HitAndRunMixing.lean:944`),
threshold `Arlib.MarkovChains.lvThreshold` (`:829`):

| binder | state | what closing it takes |
| --- | --- | --- |
| `hLem41` — LV Lemma 4.1 / Lovász (1999) Lemma 8, the TV overlap for cross-ratio-near points | **one estimate short.** `tvLe_hitAndRun_lemma41` (`HitAndRunOverlap.lean:583`) proves it with the spherical-cap probability `q₂` as a *binder*; every other input of the paper's proof is discharged (`hitAndRun_ball_medianStep_le`, `chordLength_mul_norm_le`, `hitAndRun_chord_bad_le`). `…_unconditional` (`:751`) is **vacuous for `n ≥ 2`** — it plugs in the trivial `q₂ = 1 − 1/n`, making the bound exceed `1`. The file says what is owed: `q₂ < 3/8`, against a true cap probability of `1/2` at `n = 2` and `0.4226…` at `n = 3` | the **spherical-cap concentration estimate**: `P(‖x−u‖·‖u−v‖ < √n·\|⟪x−u, u−v⟫\|) → P(\|N(0,1)\| ≥ 1) ≈ 0.317 < 3/8`, hence a dimension threshold. Then **constant-chasing downstream**: `…_of_le_three_eighths` gives `1 − (3/8 − q₂)/120 ≈ 1 − 1/2069`, weaker than the `1 − 1/500` that `conductance_hitAndRun_ge` (`HitAndRunConductance.lean:999`) was derived against, so its `1/(2²⁷·n·D)` must be re-derived |
| `hIso` — LV Theorem 2.1, cross-ratio isoperimetry | **one binder from done.** `Arlib.thm21_of_localization` (`LovaszVempalaIso.lean:733`) proves Theorem 2.1 for the uniform density with the Localization Lemma as its **single** binder `hloc`. Note the printed Theorem 2.1 is **false as stated** and the repair (`∀ x ∈ K, h x ≤ 1/3`) is already inserted — `Arlib.not_hIso_two` | **the localization discharge**, at `g₁ = 1_{T₁} − A·1_K`, `g₂ = A·h·1_K − 1_{K∖T₁∖T₂}` (`LovaszVempalaIso.lean:163`) |
| `hLS` — the Lovász–Simonovits `√W·(1 − φ²/2)^t` step | **a fork, not a gap.** Discharged for **lazy** chains (`ConductanceToTV.lean`, `ls_lazy`); the general form for plain kernels is **refuted** — the swap kernel on `Bool` (`HitAndRunMixing.lean:127-148`) — and that is a *paper* gap, not a repository one | a **modelling decision**: restate the contract over `lazy (hitAndRun K)`. Costs a factor `2` in the step count; nothing in `ttcRun` executes hit-and-run steps, so nothing downstream is disturbed. **Changes a stated interface — must not be done silently** |

### The crux, and why it pays twice

`hloc` for LV's Theorem 2.1 is **the same object** as `hloc` for CV's `thm:iso` —
`LovaszVempalaIso.lean:724` says so directly (*"Compare `Arlib.gaussianRestricted_isoperimetry`'s
`hloc`"*). Both instantiate the Localization Lemma at **indicator-based** integrands, and
both are blocked by the same thing: `Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear`
(`LocalizationClosed.lean:380`) requires **`Continuous g₁, g₂`**. That is `AUDIT.md`'s
long-standing item **(C)**.

So the single highest-leverage lemma in this repository is: **discharge the Localization
Lemma for indicator integrands** — by mollification with a limit passage, or by weakening
the collinear form's `Continuous` hypothesis to lower semicontinuity plus boundedness (and
discharging `v ≠ 0`). It unlocks CV's `thm:iso` *and* LV's `hIso` *and* hence
`HitAndRunTheorem11Input`, which in turn discharges residual hypothesis **#8** and — via
`Ttc.VolumeAlgorithm.cousinsVempalaOfSampler` — **`hphase_mean`** (`RuntimeMN4.lean:244`:
*"what is missing is the sampler, i.e. a proved `hTV` — the same open problem as #8"*).

**What would still remain after all of that:** `hphase_var` (#13, routeless), the `r → 1`
rescaling seam (`HitAndRunMixing.lean:168-180`, self-described "finite bookkeeping"), the
`hdom` shape reconciliation (the contract's `uniformOn K (A \ S)` versus the theorem's
`uniformOn K A` — the contract is the *stronger* form, so an inhabitant weakens cleanly),
and §0f's cost-model scope decision. **Not** the `1/ρ²` of §0g: that belongs to the
speedy/ball backend and is not on this route.

### ☠ DEAD THEOREMS — `hIso_of_thm21` and `conductance_hitAndRun_ge_of_thm21` (2026-08-12)

**Do not build on `Arlib.hIso_of_thm21` or `Arlib.conductance_hitAndRun_ge_of_thm21`
(`Arlib/Convexity/CrossRatioIsoBridge.lean`). Their `hthm21` hypothesis is FALSE**, so both
are vacuously true and prove nothing. Refuted by `Arlib.not_thm21_book`
(`Arlib/Convexity/WeightedIsoBook.lean`) at `n = 1`, `K = closedBall 0 1`.

**The defect is two missing clauses.** The `hIso` binder of `conductance_hitAndRun_ge`
(`HitAndRunConductance.lean:1005-1010`) reads `… MeasurableSet T₁ → MeasurableSet T₂ →
T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ → …`. The `hthm21` binder
(`CrossRatioIsoBridge.lean:445-453`) **dropped `T₁ ⊆ K` and `T₂ ⊆ K`**. With `u ∉ K`,
`crossRatioDist K u v ≥ 1` always — the chord parameters satisfy `0 < a ≤ 1 < b` and
`d_K(u,v) = (b−a)/(a(b−1))` — so `min 1 (d_K u v)/3 = 1/3` and the chord hypothesis
degenerates into the global `g ≤ 1/3` it already assumes, carrying **zero** geometric
information. Witness: `U₁` a ball of volume `vol K/2` placed far outside `K`, `U₂` of
relative volume `9/10` inside `K`, `g ≡ 1/3`, `A = 1/2`; the conclusion would assert
`vol K/6 ≤ vol K/10`.

**Lovász–Vempala Theorem 2.1 itself is untouched** — there `S₁, S₂, S₃` partition `K`, so the
subset clauses hold by construction. This is an encoding defect introduced in this
repository, not a defect in the source.

**Repaired:** `Arlib.hIso_measurable_of_thm21_sub`, `Arlib.hIso_book`,
`Arlib.conductance_hitAndRun_ge_book` (`WeightedIsoBook.lean`) rerun the same proofs against
`hthm21sub` — identical but with `U₁ ⊆ K → U₂ ⊆ K →` inserted. **Repoint anything aimed at
the dead pair.**

> **⚠ Audit lesson, recorded because it was missed here.** The dead pair was verified by
> checking that `conductance_hitAndRun_ge_of_thm21` composes into `conductance_hitAndRun_ge`
> by `exact`, and that check **passed**. It had to: a false hypothesis makes any composition
> typecheck. `#print axioms` was clean, `lake build` was green, the composition was
> machine-checked — and the theorem was worthless. This is exactly `CLAUDE.md` §11's
> non-vacuity failure mode. **A binder must be checked for satisfiability, not only for
> fit.** The cheap test: diff the new binder against the binder it claims to serve, clause
> by clause. Two missing clauses were visible by eye.

### ⚠ The acceptance test needed strengthening — 2026-08-12

The old test was: *`grep -rn "HitAndRunTheorem11Input" --include="*.lean" Ttc/ Arlib/` must
show a **constructor application**, not only the `structure` declaration and binders.*

**That test now passes, and it must not be read as a green light.**
`Ttc.hitAndRunTheorem11Input_of_binders` (`Ttc/Sampler/HitAndRunBackend.lean:587`) really
does build a `HitAndRunTheorem11Input` — `refine ⟨?_⟩` over the `mixing` field. But it takes
`HLem41`, `HIso`, `HLS` as hypotheses **universally quantified over all `n` and all `K`**,
which is *stronger* than the per-body binders elsewhere. It is a **reduction of inhabitation
to three named statements**, not a witness. The file says so itself.

**The corrected test, in three parts.** All three must hold:
1. a constructor application exists — **now true**;
2. it takes **no hypothesis** that is itself unproved — currently **false**, three remain;
3. a `Nonempty Ttc.HitAndRunTheorem11Input` or a `def`/`instance` of that type with no
   hypotheses elaborates — currently **false**.

Until (2) and (3) hold, every hit-and-run cost number in `Ttc/Exec/` is arithmetic without
meaning, exactly as §0a says. This is `CLAUDE.md` §11's non-vacuity check: a conditional
constructor is precisely the failure mode that check exists to catch.

---

## 0i. `hcomp` is discharged; the volume oracle's blocker is now a *single* named theorem (2026-08-13)

Two things changed today, in opposite directions. Read both before quoting anything in
`SpeedyGaussianConductance.lean` or `OverlapPerPair.lean`.

### (a) Proved: Cousins–Vempala's `lem:f-dist`, and with it `hcomp`

`Arlib.MarkovChains.ell_comparable_of_densDist`
(`Arlib/MarkovChains/Continuous/OverlapPerPair.lean:232`) is CV `1409.6011`'s `lem:f-dist`
(`vol3_journal.tex:548`, the paper's Lemma 6.3): from `d_h(u,v) < 1/4` for `h = ℓ·γ`,
`‖u−v‖ ≤ δ/√n`, `δ ≤ σ/(8√n)` and `K ⊆ 4σ√n·Bₙ`, conclude `ℓ(u) ≤ (3/2)ℓ(v)` and
symmetrically.

Consequences, all axiom-clean, all verified by a forced rebuild (`Built`, 3442 jobs):

* `overlap_speedyWalk_sqrt_perPair` (`:276`) and
  `conductance_speedyMetropolisGaussian_ge_perPair` (`:361`) — the `hcomp` binder is
  **removed**, not moved. It was *globally false*
  (`exists_ell_not_comparable_at_sqrt_dim_counterexample`); the consumer's own
  `densDist h u v < 1/4` clause, previously documented as "not used", now carries it.
* The dimension threshold `n ≥ 21` is **derived**, not assumed — it is CV's unquantified
  "for `n` large enough", computed in `gaussianWeightReal_le_of_cv` (`:95`) at the bracket
  `9/8` (rather than the paper's `1.1`, because `(4/3)·(9/8) = 3/2` exactly).
* `ell_comparable_of_densDist_witness` (`:406`) discharges the entire hypothesis bundle at
  two **distinct** points, so the `densDist` premise is not secretly diagonal-only.

### (b) Found: `hellLip`/`hLσ` has no witness with non-constant `ℓ` — INFORMAL

`conductance_speedyMetropolisGaussian_ge` (`SpeedyGaussianConductance.lean:530`) and its
`_perPair` refinement still carry

    hellLip : ∀ u ∈ K, ∀ v ∈ K, ℓ(u) ≤ ℓ(v)·exp(Lf·‖u−v‖)
    hLσ     : √3·(σ²·Lf + R) ≤ 2σ√n

**Nothing in the repository discharges these, and the following argument — which is
INFORMAL, not machine-checked — says nothing can, at the operative step.** `hLσ` caps
`Lf ≤ 2√n/(√3·σ)`, so over a distance `δ ≤ σ/(8√n)` the permitted variation of `log ℓ` is
`Lf·δ ≤ 2/(8√3) ≈ 0.144`. But `ℓ` at a cube corner is `≤ 2⁻ⁿ`
(`Arlib.MarkovChains.two_pow_mul_ell_cube_corner_le_one`, **machine-checked**, `EllFloor.lean:327`)
and `≈ 1` at distance `δ√n` inward, so the true rate is `≈ √n·log 2/δ = 8n·log 2/σ`, which
exceeds the cap `1.15√n/σ` for every `n ≥ 1`. The only witness in the tree
(`ellGaussian_isoperimetry_measurable_logTwo_strict_witness`) takes `Lf = 0` on a body so
small that `ℓ` is constant.

So `conductance_speedyMetropolisGaussian_ge` and `_perPair` are **not** mixing-time,
spectral-gap or runtime bounds, and must not be quoted as such. Turning the argument above
into a refutation lemma, in the style of `EllFloor.lean`'s
`metropolis_ell_floor_unsatisfiable_on_cube`, is deferred work.

`hellLip` is an artefact of *this repository's* route, not of the mathematics: CV's `thm:iso`
(`vol3_journal.tex:467`) uses no Lipschitz control of `ℓ` anywhere. It enters at exactly one
place — `Arlib.norm_sub_ge_of_densDist_weighted` (`Arlib/Convexity/IsoWeighted.lean:237`),
which converts the density branch `4(d/σ)√n ≤ d_h(u,v)` into a *metric* separation
`‖u−v‖ ≥ 2√3·d` so that `exists_disjoint_open_enlargement_weighted` can build disjoint open
enlargements and thereby lift the isoperimetric inequality from open/closed sets to
measurable ones.

### (c) The Metropolis route is refuted on the consumer's class — and this one IS machine-checked

`Arlib/MarkovChains/Continuous/EllFloor.lean` settles it: `hfloor` forces `θ ≥ 1/5`, the cube
`[-1,1]ⁿ` is in the consumer's class (`CVInstantiate.lean:148,153`), and `ℓ ≤ 2⁻ⁿ` at its
corner, so `metropolis_ell_floor_unsatisfiable_on_cube` shows no `θ` meets `hell` and
`hfloor` together for `n ≥ 3`. `MetropolisMixingUncond.lean` is therefore
**`hiso`-unconditional only**; its `hell`/`hfloor` pair restricts the body class to bodies
with no corner at scale `δ`, which excludes the polytopes TTC's volume oracle is applied to.
Its non-vacuity witness `exists_mixesWithin_lazy_metropolisGaussian_uncond_witness` uses
`K = B(0,1/2) ⊆ ℝ²` with `δ = 1` — a body *contained in the proposal ball*, which violates
the consumer's `ball 0 1 ⊆ K`.

### (d) The blocker, stated as one theorem

Both routes fail at the same joint, and it is not isoperimetry — the `ℓ`-weighted
isoperimetric inequality is **already proved with no Lipschitz hypothesis of any kind**:

    Arlib.ellGaussian_isoperimetry_openClosed_logTwo   (Arlib/Convexity/EllLogConcave.lean:474)

for `h(x) = ℓ(x)·e^{−‖x‖²/(2σ²)}`, obtained by instantiating the general log-concave-weight
Gaussian isoperimetry at `f = ℓ` via `Arlib.isLogConcave_ell_toReal` (`:262`). Its **only**
deficiency against the `hiso` binder of
`Arlib.MarkovChains.conductance_speedyGaussian_ge` is set regularity: it needs `S₁, S₂` open
and `S₃` closed, whereas `hiso` is stated for **measurable** `S₁, S₂, S₃`.

> **The blocker is the measurable upgrade of `ellGaussian_isoperimetry_openClosed_logTwo`,
> reached without the metric-enlargement detour.**

**UPDATE, same day — this blocker is now CLOSED for a general log-concave cofactor.** See
§0j. What remains of it is the instantiation at `f = ℓ`, which needs only integrability and
positive mass for `h = ℓ·γ`.

The detour is what costs `hellLip`, and the repository already proves the detour cannot be
repaired in general: `Arlib.exists_separated_no_disjoint_open_enlargement`
(`Arlib/Convexity/IsoOpenClosed.lean:1205`) exhibits separated sets with no disjoint open
enlargement. So the upgrade has to go through the localization directly, on the measurable
sets — CV's own route, and the machinery is in
`Arlib/Convexity/LocalizationMeasurable.lean`. Everything downstream — the speedy-walk
conductance, its transfer to the uniform walk (`HoldingTime.lean`, `SpeedyToUniform.lean`),
`hphase_mean`, `hphase_var` — is already routed.

The average-`ℓ` facts needed on the far side are already unconditional on the whole class:
`isSmooth_of_ball_subset` (`EllFloor.lean`) gives `(1−δ)ⁿ·vol K ≤ ∫_K ℓ` for every convex `K`
with `ball 0 1 ⊆ K`, which is what `tvLe_ellProb_uniformOn` (`SpeedyToUniform.lean:207`)
consumes — the same infimum-to-average dissolution that fixed `hIso`, `hLem41` and `hcomp`.

---

## 0j. `thm:iso` is proved for **measurable** sets — the paper's unproved step, discharged (2026-08-13)

Cousins–Vempala's Theorem 5.4 (`thm:iso`, `1409.6011/vol3_journal.tex:467`) is stated for an
*arbitrary* partition of `ℝⁿ`. Its proof reduces to the one-dimensional inequalities via the
step at `vol3_journal.tex:499`:

> "By a standard combinatorial argument, we can assume that `Zᵢ = {t : (1−t)a+tb ∈ Sᵢ}` are
> intervals that partition `[a,b]`."

**The paper does not prove that step**, and it is the reason this repository had `thm:iso`
only for `S₁, S₂` open and `S₃` closed (`gaussianRestricted_isoperimetry_openClosed_logTwo`,
`OneDimSharp.lean:631`), where the reduction is available.

### The capstone

```lean
Arlib.gaussianRestricted_isoperimetry_measurable_logTwo   -- Arlib/Convexity/IsoMeasurableUncond.lean:119
```

Identical to the open/closed capstone binder for binder, except that `IsOpen S₁`,
`IsOpen S₂`, `IsClosed S₃` become `MeasurableSet S₁`, `MeasurableSet S₂`, `MeasurableSet S₃`,
plus an added `hd : 0 < d`. Axiom-clean; full tree 3713 jobs, 0 errors, 0 `sorry`.

### The `ℓ`-weighted instantiation — `hellLip` and `hLσ` deleted

```lean
Arlib.ellGaussian_isoperimetry_measurable_logTwo_uncond   -- Arlib/Convexity/IsoMeasurableUncond.lean:139
```

`thm:iso` for measurable sets at `h = ℓ·γ`. Set against
`Arlib.ellGaussian_isoperimetry_measurable_logTwo` (`Arlib/Convexity/IsoWeighted.lean:851`),
which reaches the same conclusion through the metric-enlargement detour, the binders
`hellLip`, `hLσ` — and the parameters `R` and `Lf` they mention — are **gone**. Log-concavity
of `ℓ` (`isLogConcave_ell_toReal`) does the work log-Lipschitzness was being asked for,
because the route never converts the density branch.

Its side conditions come from `Arlib/Convexity/EllGaussianFacts.lean`
(`ellGaussian_continuous`, `ellGaussian_le_one`, `ellGaussian_integrable`,
`ellGaussian_integral_pos`), which extracts and generalises what had been proof-local `have`s
inside `ellGaussian_isoperimetry_openClosed_logTwo`. Notably none of them needs
`MeasurableSet K`; only the log-concavity of `ℓ` does.

### The idea, and why it is not blocked by the repository's own counterexample

The previous route to the measurable case (`exists_disjoint_open_enlargement_gaussianIndicator`,
`IsoIndicator.lean:405`) discharges the *density* branch of the separation disjunction by
converting it into the *metric* branch. That needs a global log-Lipschitz bound on `h` — free
for `1_K·γ`, and the unsatisfiable `hellLip` for `ℓ·γ` (§0i(b)).

The new route **never converts the density branch.** Each pair stays in whichever branch it
was in, and only the *thresholds* move, from `d` to any `d' < d`. What that needs is a
perturbation bound for `densDist`, which uniform continuity on a compact set supplies — and
crucially **the thickening radius is chosen after the compact sets**, so it has no inequality
to satisfy against `σ`, `R` or `n`. A global Lipschitz constant does; that is `hLσ`, and it
fails.

`Arlib.exists_separated_no_disjoint_open_enlargement` (`IsoOpenClosed.lean:1205`) — which
shows disjoint open supersets of `S₁, S₂` need not exist at all — is evaded, not contradicted:
there the two sets touch *inside* `{h = 0}`. The route never asks for supersets of `S₁, S₂`,
only of compact subsets of `S₁ ∩ {h > 0}` and `S₂ ∩ {h > 0}`, which are disjoint compacts and
so a positive distance apart; the discarded part carries no mass because `h` vanishes there.

### The four pieces, each independently forced-rebuilt and axiom-clean

| file | key theorem | content |
|---|---|---|
| `Arlib/Convexity/IsoInnerRegular.lean` | `exists_compact_subset_setIntegral_ge` | inner regularity **inside `{h > 0}`** — the `∀ x ∈ C, 0 < h x` clause is load-bearing |
| `Arlib/Convexity/IsoEnlargeContinuous.lean` | `exists_disjoint_open_enlargement_of_continuous` | the crux; `densDist_ge_sub_of_perturb` is its arithmetic core (`3η/m`) |
| `Arlib/Convexity/IsoEnlargeMeasurable.lean` | `exists_enlargement_of_measurable` | the composition, with the `2ε` residual bookkeeping |
| `Arlib/Convexity/IsoEnlargeSlack.lean` | `gaussianRestricted_isoperimetry_measurable_of_enlargements` | slack-tolerant reduction + the limits `ε ↓ 0`, `d' ↑ d` |

### Non-vacuity, and what each witness certifies

* `exists_disjoint_open_enlargement_of_continuous_witness` — an instance where the **metric
  branch is FALSE** at the only pair, so the density branch carries the disjunction alone.
  That instance is out of reach of the Lipschitz route, which is the point of the file.
* `exists_enlargement_of_measurable_witness` — both `S₁` and `S₂` of positive `h`-mass, so
  the composition does not reduce to its degenerate branches.
* `exists_enlargements_witness` — `S₁, S₂` **not open** and the conclusion's left side
  strictly positive, so the data is genuinely outside the reach of the open/closed capstone.
* `gaussianRestricted_isoperimetry_measurable_logTwo_witness`
  (`IsoMeasurableUncond.lean:216`) — the **capstone's own** bundle, discharged at the closed
  slab partition `{⟪e,x⟫ ≤ −1/4}`, `{1/4 ≤ ⟪e,x⟫}` with `f ≡ 1`, `σ = 1`, `d = log 2/4`. Its
  last two conjuncts prove `¬IsOpen S₁` and `¬IsOpen S₂`, so the capstone is exhibited being
  applied exactly where `gaussianRestricted_isoperimetry_openClosed_logTwo` cannot be. Strict
  positivity of the left-hand side for the same slab data comes from
  `exists_enlargements_witness`.

### What this does NOT give — read before quoting it

**The capstone carries `hhc : Continuous h`, and the consumer's density is not continuous.**

The continuity binder is *inherited*, not added: `gaussianRestricted_isoperimetry_openClosed_logTwo`
(`OneDimSharp.lean:631`) already carries it, and §0j changes only the three regularity binders
on `S₁, S₂, S₃`. But Cousins–Vempala's Theorem 5.4 itself assumes only that `f` is log-concave,
which **includes discontinuous indicators** — so what is proved here is Theorem 5.4 for
measurable sets *for continuous `h`*, which is strictly weaker than the paper's statement.

That matters because it is exactly the case the consumer needs. `hiso` in
`Arlib.MarkovChains.conductance_speedyGaussian_ge` is instantiated, via
`Arlib.MarkovChains.hpi_ellGaussian`, at

    h = Set.indicator K (fun x => (ell K δ x).toReal * gaussianWeightReal (σ^2) x)

which is **discontinuous across `∂K`**: `ℓ > 0` at a boundary point (a corner still has
`ℓ ≥ 2⁻ⁿ > 0`) while the indicator drops to `0`. So `gaussianRestricted_isoperimetry_measurable_logTwo`
instantiates at `ℓ·γ` — the density of `ellGaussian_isoperimetry_openClosed_logTwo`, with no
indicator — and **not** at the consumer's `1_K·ℓ·γ`. Nor is the gap a monotonicity one that
could be waved through: `∫ ℓ·γ > ∫ 1_K·ℓ·γ` by the collar mass just outside `K`, and the
residual set `(U₁ ∪ U₂)ᶜ` picks that collar up on the right-hand side.

So the remaining work is **not** a one-line instantiation. It is an indicator bridge, and the
template for it is already in the tree — `Arlib.gaussianIndicator_isoperimetry_measurable`
(`Arlib/Convexity/IsoIndicator.lean:476`) does exactly this for `1_K·γ`, by running the
open/closed capstone at the *continuous* mollified density
`h_j = e^{−j·dist(x, closure K)}·γ` and letting `j → ∞` by dominated convergence
(`tendsto_setIntegral_expNegInfDist_mul_gaussian`, `setIntegral_indicator_closure_eq`;
`volume (frontier K) = 0` via `Ttc.CousinsVempala.volume_interior_eq` reconciles `closure K`
with `K`). The version needed here carries the extra factor `ℓ`, and — unlike the indicator
case — may use the **density** branch, because §0j's enlargement does not require converting
it. `Arlib.isLogConcave_exp_neg_infDist` (`IsoIndicator.lean:152`) supplies log-concavity of
the mollifier.

Until that bridge lands, **nothing in §0j may be quoted as a conductance, mixing-time or
runtime statement**, and §0i(b)'s scope warning on `SpeedyGaussianConductance.lean` stands
exactly as written.

---

## 0k. `thm:speedyconductance` is unconditional — `hellLip` and `hLσ` are gone (2026-08-13)

§0j closed the measurable case of `thm:iso` for a *continuous* density, and flagged that the
consumer needs the **indicator** density `1_K·ℓ·γ`, which is discontinuous across `∂K`. That
bridge is now built, and the conductance bound follows.

### The two new capstones

```lean
Arlib.ellGaussianIndicator_isoperimetry_measurable_logTwo  -- Arlib/Convexity/IsoIndicatorEll.lean:89
Arlib.conductance_speedyMetropolisGaussian_ge_uncond       -- Arlib/Convexity/SpeedyGaussianUncond.lean:112
```

The second is Cousins–Vempala's `thm:speedyconductance` (`vol3_journal.tex:624`):

    Φ(speedyMetropolisGaussian K δ σ²) ≥ δ·log 2 / (640·σ·√n)

with respect to `ellGaussianProb K δ σ²`, carrying **no isoperimetric and no comparability
hypothesis**. Against `conductance_speedyMetropolisGaussian_ge_perPair`
(`OverlapPerPair.lean:361`), the binders `hLf`, `hellLip`, `hLσ` and the parameter `Lf` are
deleted; everything else, including the conclusion, is verbatim.

### Why the mollification bridge closes

Run the §0j capstone at `g j = e^{−j·d(x, K̄)}·ℓ·γ` with the parts cut to `K`
(`S₁' = S₁ ∩ K`, `S₂' = S₂ ∩ K`, `S₃' = (S₁' ∪ S₂')ᶜ`). Then:

* **the separation hypothesis transfers exactly** — on `K`, `d(x,K̄) = 0`, so `g j = h`
  pointwise and `densDist (g j) u v = densDist h u v` for all `u,v ∈ K`, for every `j`. No
  comparison estimate, and the density branch is never converted. This is what the older
  route (`gaussianIndicator_isoperimetry_measurable`, `IsoIndicator.lean:476`) cannot do: it
  must force every pair into the metric branch, which is what costs a Lipschitz constant;
* **two of the three integrals never move** — `S₁', S₂' ⊆ K`, so `∫_{S₁'} g j = ∫_{S₁} h`
  for every `j`;
* **only the mass and the residual take a limit**, and both land exactly:
  `∫ g j → ∫_{K̄} ℓγ = ∫ h` and `∫_{S₃'} g j → ∫_{S₃} h`, using `S₃' ∩ K = S₃ ∩ K` from the
  partition and `volume (frontier K) = 0` for convex `K`.

Supporting file: `Arlib/Convexity/EllMollifier.lean` (13 theorems — log-concavity of the
mollified cofactor, the four analytic side conditions, and the two dominated-convergence
limits).

### Non-vacuity — and why it is not routine here

`conductance_speedyMetropolisGaussian_ge_uncond_witness` (`SpeedyGaussianUncond.lean:150`)
discharges **every** binder simultaneously at `n = 21`, `K = B̄(0,1)`, `σ = 100`, `δ = 1`,
`R = 1`, and carries the conductance conclusion itself as its last conjunct.

This is the point: the binders it drops are exactly the ones §0i(b) argues have **no** witness
with non-constant `ℓ`, so `conductance_speedyMetropolisGaussian_ge_perPair` had no
unconditional instance at all. Here `δ = 1` on a body of radius `1`, so `ℓ` is genuinely
non-constant, and the bundle is still met.

### What this does NOT give

A conductance bound is not a mixing time and not a running time. The conductance-to-TV step
and the speedy-to-target transfer (`SpeedyToUniform.lean`, `HoldingTime.lean`) are separate
and are **not** performed here, and `hphase_mean`/`hphase_var` — the two remaining hypotheses
of the volume algorithm (`CVInstantiate.lean:255`) — are still open until they are. `R`
survives in the binders because the *overlap* side still needs it, via
`acceptance_floor_of_cv`; only the isoperimetry side became `R`-free.

§0i(b)'s scope warning on `SpeedyGaussianConductance.lean` still applies to the theorems
*in that file*, which continue to carry `hellLip`; it no longer describes the state of the
art, which is this section.

---

## 0l. The sampler chain closes; four `Ttc` interface binders are refuted (2026-08-13)

### Landed unconditionally

| Cousins–Vempala result | repo theorem |
|---|---|
| `lem:speedy-to-ball` (`:915`) | `sum_lintegral_inv_ell_iterate_speedyWalk_le` (`WastedSteps.lean`) |
| `lem:sigma-roundness` (`:882`) | `gaussian_rounded` (`LambdaBoundSharp.lean`) |
| both KLS97 inputs to `lem:map-speedy-to-ball`, at `δ ≤ 1/(2n)` | `KLS97Shell.lean` |
| the crux of `lem:map-speedy-to-ball` | `condOn_ellGaussianMeasure_shrunken` (`SpeedyExactOnShrunken.lean`) |
| a cooling schedule meeting the variance budget | `GeneralRate.lean` |

`lem:speedy-to-ball` bounds the **sum of per-step conditional expected holding times** — CV's own
linearity-of-expectation quantity — not the path-level step count of a single trajectory, which
needs the unproved time change `ω_t = Y_{N_t}`.

### The cooling obstruction was an artefact, and the phase count is now known exactly

`PhaseVar.lean`'s `geomSchedule_total_cooling_lt` showed the fixed rate `α = 1/n` cannot both meet
the variance budget and cool. `GeneralRate.lean` shows this is an artefact of `α` being too large:
`generalCoolRate_lt_fixedRate` puts the admissible rate below `1/n` by a factor `16L/κ`, and

    α = log(1+ε²/5)/(16(n+1)log(nR²)),   m = Θ(n·log²(nR²)/ε²)

meets budget and cooling simultaneously (`exists_admissible_volume`). `generalPhaseCount_ge_of_budget`
is a **matching lower bound**, so that phase count is *forced*, not merely sufficient.

**Why it is worse than the paper's `O*(n)`.** CV do not shrink `α`. At `vol3_journal.tex:1440` they
spread the budget as `1 + (cᵢ−1)/kᵢ` with `kᵢ` samples averaged per phase. The repo's shape
`1 + κ/m` is the `kᵢ = 1` specialisation, and under `kᵢ = 1` the `Θ̃(n/ε²)` count is forced.
Recovering `O*(n)` needs per-phase sample counts in the interface — a change of hypothesis shape,
not a sharper estimate.

### Four binders of `cousinsVempala` that cannot be supplied at its own generality

`cousinsVempala` quantifies over **every** `K` with `Convex ℝ K`, `ball 0 1 ⊆ K`, `volume K ≠ ⊤`.
At that generality:

1. **`MeasurableSet K` is false.** `ball 0 2 ∪ S` with `S ⊆ sphere 0 2` arbitrary is convex,
   contains the unit ball, has finite volume, and can be non-Borel — Mathlib's `MeasurableSet` on
   `EuclideanSpace` is Borel, and completeness of Lebesgue measure does not help. Recorded in
   `PhaseFromTV.lean`, which works around it by scoring `interior K` (open, hence Borel), using
   `Convex.addHaar_frontier` to keep the chain ratios and exact law unchanged.
2. **No radius is exposed**, but `hphase_var`'s bound `B = e^{R²/(2σᵢ²)}` needs one; `coolRatio` is
   unbounded on an unbounded body.
3. **The terminal constant is refuted.** `hterm_not_dischargeable` (`TerminalMoment.lean`) shows the
   uniform constant `1 + 2/n` FAILS at the terminal phase for every `n ≥ 1`, on a fixed-rate
   schedule, at `K = B₁`. The terminal weight is the constant `1`, so the ratio computes exactly to
   `e^{R²/(2σᵢ²)}` — `≥ 1` by Cauchy–Schwarz, unbounded as `σᵢ² ↓ 0`.
   **The paper locates the defect**: CV prove `1 + 2/n` only for Gaussian→Gaussian
   (`lem:fixed-var-bound`, `:1353`); the terminal step is `lem:starting-gauss` (`:1326`), which
   *assumes* `σᵢ² ≥ C²n` and yields the different constant `e²`, and `lem:accuracy` (`:1419`) pays
   for it with a separate `(1 + e²/k)` factor. The `Ttc` binder collapses that two-constant
   accounting into one, and the collapse is what is unsound. Repair: `hflat`, i.e.
   `R² ≤ 2σᵢ²·log(1+2/n)` at the terminal index (`hphase_var_of_tvLe_of_flat`).
4. **`hgb`** — the uniform-in-`K` bound impossibility already at `CVInstantiate.lean:629`–`633`.

These are refutations, not gaps: no amount of further proving supplies them. The interface must be
amended to carry them as binders.

### Scope

None of this is a running time. `VolumeAlgorithm` still has no complexity field, so no runtime is
even statable inside the interface; the intended route is a step-count theorem outside it.

---

## 1. Is the capstone about the real object?

Read only the **type** of one declaration — everything before the `:=`.

**[`Ttc.TtcProb.volume_estimate`](Ttc/Estimate.lean)** — `thm:volumettc`.
This is the type as the compiler prints it, not a paraphrase:

```lean
theorem Ttc.TtcProb.volume_estimate {A : Type u_1} {n : ℕ} (T : Ttc.TtcProb A n) :
    1 - T.δ ≤
      (T.μ {ω | Ttc.ttcOutput T.P T.O T.toDNF T.ρ T.φ ω
        ∈ Ttc.relErr T.ε (Ttc.volSol T.M T.φ)}).toReal
```

*With probability at least `1 − δ`*, the algorithm's output lies in
`(1 ± ε)·Vol(F)`. Four things make that a claim rather than a shape:

* **The measured thing is the algorithm — with three deviations, listed below.**
  [`Ttc.ttcOutput`](Ttc/TtcProb.lean) is
  [`Ttc.run`](Ttc/Model/Pseudocode.lean), the line-by-line transcription of
  `alg:ttc`, with the oracles drawn at `ω`. Read `Model/Pseudocode` against
  `sections/algo.tex`; the control flow is the whole algorithm and there is no
  second model it is quietly swapped for. **But the sampling interface is not
  verbatim**, and this is the one place where "the measured thing is the
  algorithm" needs qualifying:

  | Deviation | `algo.tex` | Here | Content? |
  | --- | --- | --- | --- |
  | both `while` loops as exit levels | lines 32–35, 39–42 | `Ttc.haltLevel`, `Ttc.absorbLevel` (an `sInf`) | **No**, where the loop terminates: the exit level is what the loop computes. On a run where the second loop never exits, the model says "stay put" — a corner nothing depends on (deviation (b) in `Model/Pseudocode`). |
  | thinning reads a level, not a coin | lines 33, 40 | `thin j₀ j' X` | **No.** `p` only decreases, so each level is reached at most once per run; a read-off at the target level is a bijection with iterating the coin. |
  | `pois` told the cube and level | line 38, 41 | `pois i j λ` | **Yes.** |
  | `gen` told the cube and level | line 43 | `gen i j N ρ` | **Yes.** |

  The last two are genuine: `GenerateSamples(P(cᵢ), Nᵢ, ρ)` and `Pois(t·p)` are
  *rate-blind* in the paper. They are level-aware here because `lem:numlattice`'s
  `Err(j)` must be an event about a level-`j` process coupled to the run, and a
  rate-blind sampler provably cannot realise that coupling — README finding 15.
  This is no longer a hypothetical: the coupling is now built, it uses the extra
  arguments, and it is **load-bearing for the headline**.
  [`Ttc.trajOracles`](Ttc/Coupling/Family.lean) is a `Ttc.Oracles` bundle
  answering every call by reading a trajectory of the level family,
  [`Ttc.card_run_eq_sum_traj`](Ttc/Coupling/Run.lean) proves the run driven by it
  satisfies `|𝒳| = ∑ₛ ω(J)ₛ` pathwise, and the `oracle_eq` field of
  `Ttc.TtcProb` asserts that the instance's own oracles *are* that bundle.
  **An auditor should read the headline as being about a version of `TTC` whose
  sampler knows which epoch it is in, and whose randomness is the coupled
  Poisson/thinning family.** Whether that is the same algorithm is a judgement
  the reader must make; it is not a difference the machine can see.
* **The target is `Vol(F)`, not a surrogate.**
  [`Ttc.volSol`](Ttc/Model/ProblemSetting.lean) is `(volume (sol M φ)).toReal` —
  Mathlib's Lebesgue measure of the set of real points satisfying the formula. No
  discretisation, no rational grid.
* **That set is what the algorithm enumerates.**
  [`Ttc.TtcProb.sol_eq_union`](Ttc/Capstone.lean) says
  `⋃ c ∈ T.D, region T.M c = sol T.M T.φ` — `thm:decomposition`, *proved* from the
  `isDNF` field via
  [`Ttc.sol_eq_iUnion_region`](Ttc/Lattice/Decomposition.lean).
* **The interval is the paper's.**
  [`Ttc.relErr`](Ttc/Model/ProblemSetting.lean) is `ε b ↦ Set.Icc ((1−ε)b) ((1+ε)b)`,
  and `T.μ` is a probability measure (field `isProb`).

### The `toReal ⊤` hazard, and why the headline is not vacuous

`volSol M φ` is `(volume (sol M φ)).toReal`, and `ENNReal.toReal ⊤ = 0`. So a
formula with an **unbounded** solution set would be assigned volume `0`, and the
capstone would read "the algorithm returns approximately `0`" — true, and
worthless.

The hazard is real, not hypothetical:
[`Ttc.VolSolCheck.volSol_tt_eq_zero`](Ttc/Volume/VolSolCheck.lean) proves that
for `n ≥ 1` and **any** interpretation, `volSol M ⊤ = 0` even though
`Sol(⊤) = ℝⁿ`.

What rules it out is `Ttc.TtcProb`'s field `volume_ne_top`
([`Ttc/TtcProb.lean`](Ttc/TtcProb.lean)) — but that is stated **per cube**,
`∀ i, volume (region M i.val) ≠ ⊤`, not for `sol M φ`. Both steps are proved:

* [`Ttc.VolSolCheck.volume_sol_ne_top`](Ttc/Volume/VolSolCheck.lean) — a
  `DNF` is a `List`, hence finite, so countable subadditivity gives
  `volume (sol M φ) ≠ ⊤` with **no** measurability hypothesis.
* [`Ttc.TtcProb.ofReal_volSol`](Ttc/Volume/VolSolCheck.lean) — the quotable one:
  `ENNReal.ofReal (volSol T.M T.φ) = volume (sol T.M T.φ)`. `volSol` loses no
  information, so `volume_estimate`'s right-hand side is the genuine Lebesgue
  volume and never the `toReal ⊤` artefact.

### An independent reading of what is measured

Nothing previously cross-checked `volSol` against a second definition — the whole
correctness claim rested on one reading of `BForm.holds`, a `Prop`-valued
recursion that nothing forced to be the ordinary truth tables.

[`Ttc.VolSolCheck.volSol_eq_lra`](Ttc/Volume/VolSolCheck.lean) supplies it: with
`M` forced to `fun a => (atoms a).halfspace` by the `M_eq` field,

```
volSol … φ = (volume {x | evalBool (fun a => decide (∑ i, coeff i * x i ≤ bound)) φ}).toReal
```

where `evalBool` is an independent `Bool`-valued evaluator proved to agree with
`holds` ([`Ttc.VolSolCheck.holds_iff_evalBool`](Ttc/Volume/VolSolCheck.lean)).
The right-hand side mentions no `Ttc` definition except the syntax type `BForm` —
no `sol`, no `region`, no `toDNF`. It is **not** `rfl`.

Two weaker checks are honest `rfl`s and are labelled as such in the file:
`volSol M φ = (volume {x | φ.holds fun a => x ∈ M a}).toReal` is definitional. It
does pin down the measure — Mathlib's `MeasureTheory.volume` on
`EuclideanSpace ℝ (Fin n)`, no bespoke measure anywhere.

Measurability is separate and now unconditional in the LRA fragment:
[`Ttc.VolSolCheck.measurableSet_sol_lra`](Ttc/Volume/VolSolCheck.lean) — `Sol(F)`
is an honest measurable set, not merely an outer-measure value.

---

## 1b. The second capstone: `Ttc.ttc_volume`

[`Ttc.ttc_volume`](Ttc/Exec/Endgoal.lean) is the same result stated **without a
`TtcProb`**: every assumption is a visible `∀`-binder, and the probability space
is *constructed from the inputs* rather than assumed. Its conclusion measures
`Ttc.ttcOutput` under `Ttc.trajLaw θ`, and it carries a second conjunct about
`Ttc.runCost` (conditional on `Ttc.Terminates`).

**Why it exists.** `volume_estimate`'s type shows one opaque parameter, `T`,
behind which sit 59 structure fields. `ttc_volume` is the same content with the
fields spelled out, so an auditor can read the assumptions off the type instead of
reconstructing them from a `structure`. It is the honest measure of the project's
remaining debt.

**Do not read it as strictly stronger.** It is a different trade, not a free win:
`ttc_volume` fixes the sample space to the trajectory space, whereas
`volume_estimate` quantifies over an arbitrary `Ω`/`μ`/`O` that `law_eq` and
`oracle_eq` then pin to that same space. Neither implies the other for free.

**How many binders.** The compiled `Ttc.ttc_volume` has **38 top-level binders**;
`Endgoal.lean`'s module docstring says "36 binders … 28 residual". Those **agree**:
the probe counts the raw type, which includes the two implicit ambient parameters
`{A}` and `{n}` from the `variable` line; the docstring counts explicit binders,
which is what a caller must supply. `38 raw = 36 explicit + 2 implicit`, and
`36 = 4 inputs + 4 definitional + 28 residual`. An earlier revision of this file
recorded the two as a discrepancy; they were counting different things.

Still: the file is under active edit, so **do not trust the number, trust the
probe** — §5 carries a three-line re-count against the compiled environment.

Four binders came off when `Ttc/Exec/Coverage.lean` was wired in: `Ttc.coveredOracles`
pins `alg:ttc` line 27's membership test to `Ttc.coverOfRegion`, so `cover`, `memPt`,
`memPt_eq` and `cover_eq` are gone. Read `Coverage.lean`'s "Not yet in this file"
paragraph before treating that as costless: the congruence justifying the pinning is
established at the level of the oracle bundle, **not yet at the level of the run**.

`Ttc.ttc_volume` is **not** reached from `Ttc.TtcProb.volume_estimate` (§5's walk
reports `false`). An earlier revision concluded from this that "they are siblings,
not a chain". **That was wrong — it only checked one direction.** The walk in the
*other* direction reports `true`: `Ttc.TtcProb.volume_estimate` **is** reached from
`Ttc.ttc_volume`, and the closures nest strictly —

| walk from | closure size (re-measured; see the caveat below) |
| --- | --- |
| `Ttc.TtcProb.volume_estimate` | 51662 |
| `Ttc.ttc_volume` | 51777 (superset: 115 extra, of which 114 substantive; 0 missing) |

**The absolute sizes are the least durable numbers on this page.** These are a
re-measurement; the previous revision recorded 51652 / 51766 / 114 extra, and the
drift came from ordinary refactoring, not from anything about the theorems. What
survives a refactor is the *shape* — `0 missing`, and a positive surplus — so read
those two and re-run §5's walk rather than quoting the totals.

The extras **include `Ttc.ttc_volume` itself** — a closure always contains
its own start node — so the substantive figure is **114**. The `0 missing` is
exact and needs no such caveat: `Ttc.TtcProb.volume_estimate` is genuinely reached
from `Ttc.ttc_volume`, so it is in both closures. Stating it as a bare "strict
superset" would be the same self-inclusion slip in mirror image, and is worth
avoiding because "strict superset" and "superset once you discount the start node"
are different claims about the numbers even when the conclusion is unchanged.

So they *are* a chain, in the direction that matters: `ttc_volume` is built **on**
`volume_estimate` and uses everything it uses. This is worth stating explicitly
because the dangerous shape is the opposite one — a restated capstone whose name
suggests it supersedes the original while its closure is a strict *subset*, i.e. a
weaker theorem wearing the stronger one's title. The measurement rules that out
here. Re-run it after any refactor of `Endgoal.lean`; a one-directional check
cannot distinguish the two cases.

---

## 1c. The third capstone: `Ttc.ttc_volume_endToEnd` — **no oracle binders**

> **This is no longer the strongest statement in the development, and earlier
> revisions of this page said it was.** [`Ttc.ttc_volume_final`](Ttc/Exec/Final.lean)
> is — it removes this statement's polytope description *and* reprices its budget to
> a clean `1 − δ`. **§1d** is about it, and it is what a referee should read first.
> §1c remains worth reading on its own, because the oracle/input distinction below
> is what the whole route is for, and because §1d's binder list is this one's minus
> nine entries.

[`Ttc.ttc_volume_endToEnd`](Ttc/Exec/EndToEnd.lean) is `Ttc.ttc_volume`'s shape
with **every oracle binder gone** — the volume estimator, the rate function and
the sampler are all *constructed*, not assumed. (Its budget is restated in the
user's `δ` by `Ttc.ttc_volume_clean` in
[`Ttc/Exec/Budget.lean`](Ttc/Exec/Budget.lean); see caveat 3.)

**What "no oracle binders" means, exactly.** None of these appears in its type:

> `volAlg`, `volCoins`, `volED_eq`, `volCoins_good`, `vol`, `vol_pos`, `θ`,
> `theta_eq`, `gen_mem`, `sampD`, `sampler`.

That list is the whole of what `Ttc.ttc_volume` assumed about the two external
algorithms (`Vol_ED`, `GenerateSamples`) and about the rates joining them. Each is
now supplied: `vol` by [`Ttc.VolumeAlgorithm.monteCarlo`](Ttc/Volume/MonteCarlo.lean)
through [`Ttc.ttc_volume_monteCarlo`](Ttc/Exec/VolDischarge.lean), `θ` by
`Ttc.rates`, and `sampD`/`sampler` by
`Ttc.e2eSampD` and
[`Ttc.e2eSampler`](Ttc/Exec/EndToEnd.lean) — the latter via
[`Ttc.kv97SamplerOfBody`](Ttc/Sampler/Construct.lean), whose `law_tv` is **proved**
from
[`Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope`](Arlib/MarkovChains/Continuous/ConvexBodyMixing.lean).

**Oracle hypotheses (now zero) versus legitimate inputs (still present).** These
are different things and the distinction is the whole content of this section. An
*oracle hypothesis* asserts that some algorithm nobody here builds behaves well —
it is the shape that makes a formalisation circular, because the assumed accuracy
is a restatement of what is being proved. A *legitimate input* is a fact about the
formula, the polytopes, or the regime, which a caller supplies and can check.
`ttc_volume_endToEnd` has none of the first kind and plenty of the second. Its
remaining hypotheses, read off the type:

| Group | Binders | What they are |
| --- | --- | --- |
| Inputs | `atoms`, `φ`, `ε`, `δ`, `M`, `toDNF`, `P`, `cen`, `γ̂` | the formula, the accuracy pair, the interpretation, the AllSAT procedure, the parameter block, the cube centres and the inscribed radius |
| Parameter range and ties | `hε0`, `hε1`, `hδ0`, `hδ1`, `hn`, `M_eq`, `hP` | `ε, δ ∈ (0,1]`, `1 ≤ n`, `M` **is** the half-space reading, `P` **is** `ttcParams …` |
| Input conditions | `isDNF`, `isPositive`, `hm`, `hr`, `hbdd`, `hcoeff`, `hgammaHat`, `ball_subset` | the DNF is correct and positive, at least one cube and one facet, `Sol(F)` bounded, no zero facet normal, `γ̂ > 0` and each `P(cᵢ)` contains `B(cen i, γ̂)` |
| Loop length | `hlen` | the AllSAT call returns no duplicate cube (`(toDNF φ).length ≤ P.m`) |
| Polytope description | `Jt`, `Am`, `bv`, `hdil` + `rfac`, `hr1`, `hcard` | a linear system whose body **contains** each dilated region, and a bound on its facet count |
| Diameter | `Dm`, `hDbody` | those bodies are bounded |
| Regime | `big` | `(1−ε')·Thresh/8 ≤ ∑θ`, stated about the **constructed** rates |

Every one of those is checkable of an instance without knowing anything about a
sampler's mixing behaviour. That is the difference from `law_tv`, and it is why
this statement is worth a separate section.

**Four caveats. None of them is optional reading.**

1. **The sampler's accuracy is a theorem; the sampler's *non-triviality* is not.**
   What is proved is that no accuracy *assumption* is made — `law_tv` is discharged
   for `Ttc.e2eSampler`, so the disguised-oracle move (take `contLaw i` to *be*
   `Arlib.uniformOn volume P'ᵢ` and close `law_tv` by `TVLe.refl`) is not what
   happens here. What is **not** proved is that the finite-time lazy ball-walk
   iterate actually *differs* from `uniformOn` on the inflated body:
   `contLaw i ≠ Arlib.uniformOn volume P'ᵢ` is **not a theorem**, and proving it
   needs the `L²`/aperiodicity input (no eigenvalue `−1` in the continuous setting)
   which is **absent from the tree**. The three weaker facts that *are* proved, and
   which are what the file may be quoted for, are
   [`Ttc.kv97ContLaw_eq_iterate`](Ttc/Sampler/Construct.lean) (the law really is a
   `mixSteps`-fold iterate of the walk kernel),
   [`Ttc.kv97SamplerOfBody_start_ne_target`](Ttc/Sampler/Construct.lean) (the start
   is not the target) and
   [`Ttc.exists_kv97Sampler_box`](Ttc/Sampler/Construct.lean) (a concrete instance
   at a tolerance proved `≤ 1/2`, so `law_tv` is not the vacuous `≥ 1`). On the
   volume side the analogous check exists and is sharper:
   [`Ttc.MonteCarlo.monteCarlo_est_ne_volume`](Ttc/Volume/MonteCarlo.lean) exhibits a convex
   `K ⊇ B(0,1)` of finite volume, an accuracy, a confidence and a coin at which
   `(VolumeAlgorithm.monteCarlo n).est K ε pf ω ≠ (volume K).toReal`. So unlike
   `cousinsVempalaWitness` (§3c) the Monte-Carlo oracle is provably **not** the
   exact oracle in disguise.
2. **Exponential in the dimension, throughout.**
   [`Ttc.VolumeAlgorithm.monteCarlo`](Ttc/Volume/MonteCarlo.lean) is hit-and-miss
   Monte Carlo, whose sample count is exponential in `n`; the ball walk's step
   count is exponential in `n` too (it inherits
   [`Arlib.uniformOn_iso_of_convex`](Arlib/Convexity/IsoBall.lean)'s
   `κ = 2⁻ⁿ/D`). **Unconditional is not the same as efficient**, and this statement
   is only the first. `thm:runtime` remains out of scope: the second conjunct is a
   *charged cost* for `alg:ttc`'s loops conditional on `Ttc.Terminates`, not a
   polynomial-time claim and not a termination proof.
3. **The budget is `1 − δ − δ/4`, not `1 − δ`.** The extra `δ/4` is what the
   volume oracle's own failure event costs once its coins are integrated out
   against `Ttc.MonteCarlo.coins` — the conclusion is
   an `∫⁻ … ∂(MonteCarlo.coins n)`, inherited from `Ttc.ttc_volume_monteCarlo`, not
   the fixed-good-coin conclusion of `Ttc.ttc_volume`. Consequently the bound is
   **vacuous for `δ > 4/5`**, and in particular at the `ε = δ = 1` corner where
   §3b's older witness lives it reads `−1/4 ≤ …`. (A reparametrised corollary,
   [`Ttc.ttc_volume_clean`](Ttc/Exec/Budget.lean) — `Ttc.ttc_volume_endToEnd_delta`
   is a legacy `alias` for it, and both names resolve — runs this theorem at
   the internal failure parameter `δ₀ = 4δ/5` so that its conclusion reads `1 − δ`
   in the *user's* `δ`. That removes the `δ > 4/5` corner from the statement, at
   the price of a tighter internal budget; it does not change anything else on this
   page, and the caveat above is still the right one for
   `Ttc.ttc_volume_endToEnd` itself. §1d quantifies the price.)
4. **`hDbody` *has* been eliminated, and the correction is instructive.** This item
   used to read "`hDbody` could not be eliminated", and the argument for that was:
   `hbdd` bounds `sol M φ`, hence each `region M i`, while `hdil` only says the
   *described* body `body (Am i) (bv i)` is a **superset** of the dilated region,
   and a superset of a bounded set may be unbounded — so the description has to be
   told it is bounded. **Every clause of that is true about `hdil`, and the
   conclusion is still wrong**, because it is a statement about the binder rather
   than about what is provable. The *canonical* system read off `atoms` satisfies an
   **equality**,
   [`Ttc.canon_body_eq_smul_region`](Ttc/Exec/CanonPolytope.lean) —
   `Arlib.Polytope.body (canonAm …) (canonBv …) = s • region …` — so its body *is*
   the dilated region, `hbdd` bounds it directly, and `hDbody` follows. §1d is the
   statement in which it, and the eight other description binders, are gone.
   The pair `hdil`/`hDbody` is still what stops the degenerate description `Am = 0`
   (whose body is all of `ℝⁿ`) from satisfying **this** statement's hypotheses; the
   canonical system simply never takes that shape.

**Where it sits in the dependency graph.** The walk in §5 (re-run from this
theorem, not inherited) reports `true` for `Ttc.ttc_volume_monteCarlo`,
`Ttc.kv97SamplerOfBody`, `Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope`,
`Ttc.VolumeAlgorithm.monteCarlo` and `Arlib.uniformOn_iso_of_convex` — so the
Monte-Carlo oracle, the ball walk and the unconditional isoperimetric inequality
are all genuinely load-bearing here, not merely imported.

Two entries in that walk deserve care. `Ttc.TtcProb.volume_estimate` is reached
(**`true`**), so this is a *chain* on the original capstone in the sense of item 3
of "Checks that a green build does not perform", not a sibling wearing its title.
But the constant `Ttc.ttc_volume` itself is **not**
reached (`false`): the end-to-end proof goes through `ttc_volume_monteCarlo`, which
is an independently stated corollary rather than an application of `ttc_volume`.
The two statements' conclusions agree modulo the `δ/4` and the coin integral, but
that agreement is a fact about the *text* of the two types, which a reader must
check by eye — the machine does not certify it.

**Non-vacuity for *this* statement is in §3e**: two structurally different
instances at `(1/2, 1/2)` and `(1/4, 1/4)`, with the achieved bounds `3/8` and
`11/16` **proved positive in the statement**. It is the box, at one cube. The
strongest witness on this page is §3g's, but it witnesses `ttc_volume_final`, not
this statement — read which theorem a witness instantiates before ranking it.

---

## 1d. The fourth capstone: `Ttc.ttc_volume_final` — **no oracle, no polytope description, `1 − δ`**

[`Ttc.ttc_volume_final`](Ttc/Exec/Final.lean) is the strongest result in the
development and the statement a referee should read first. Read only its type, and
then the module docstring of `Exec/Final.lean` for which `δ` is which.

**What it takes.** `(atoms, φ, ε, δ)` and input conditions — **26 explicit
binders** (28 raw, the extra two being the implicit ambient `{A}` and `{n}` from the
`variable` line). In order:

```
atoms φ ε δ hε0 hε1 hδ0 hδ1 hn M M_eq toDNF isDNF isPositive hm hr P hP hlen
hbdd hcoeff cen gammaHat hgammaHat ball_subset big
```

Group them against §1c's table and the difference is exactly this: §1c's
**Polytope description** and **Diameter** rows are gone — all nine of
`Jt Am bv hdil rfac hr1 hcard Dm hDbody` (ten binders, counting the `[Fintype Jt]`
instance). Nothing was added in their place. Everything else is unchanged, and is
a legitimate input in §1c's sense: checkable of an instance without knowing
anything about a sampler's mixing behaviour.

**What it concludes.**
`1 - δ ≤ (∫⁻ c, trajLaw … ∂(MonteCarlo.coins n)).toReal`, conjoined with
`alg:ttc`'s charged cost bound `runCost … ≤ (toDNF φ).length * (cVol + cSample *
thr)` conditional on `Ttc.Terminates`. The accuracy half is over the **joint** law
of the run and the constructed volume oracle's coins, exactly as in §1c — that has
not changed and is not a defect, it is finding 13a's budget being paid rather than
conditioned away.

### Why the description binders go: an equality, not an inclusion

[`Ttc.ttc_volume_endToEnd_canon`](Ttc/Exec/CanonPolytope.lean) is the step that
removes them, and the reason it works is worth one paragraph because §1c's caveat 4
got it wrong in the other direction for two revisions.

`hdil` asked only for `latticeScale ρ • region M i.val ⊆ body (Am i) (bv i)`. What
the canonical system read off `atoms` satisfies is
[`Ttc.canon_body_eq_smul_region`](Ttc/Exec/CanonPolytope.lean),

```
Arlib.Polytope.body (canonAm atoms D i) (canonBv atoms D s i) = s • region (fun a => (atoms a).halfspace) i.val
```

for `0 < s` — an **equality**, strictly stronger than the `⊆`. `hdil` is then
`le_of_eq` of it; and `hDbody`, which genuinely does *not* follow from `hbdd` under
an inclusion, does follow under an equality, because the described body is the
dilated region and nothing larger. `hcard` holds with **equality** too
(`rfac := Nat.card (FacetIndex (toDNF φ))` and `Fintype.card (Fin N) = N`), so no
slack enters `Ttc.Params.gamma` or `Ttc.Params.thresh`; the facet count the
parameter block already stored is the one used. The switched-off rows of other
cubes read `⟪0, x⟫ ≤ 0`, true of every point
([`Ttc.canon_row_of_ne`](Ttc/Exec/CanonPolytope.lean)), so the padding costs
nothing.

### Why the budget is clean: a repricing, not a strengthening

**State this the right way round or it becomes an overstatement.** `hP` reads

```
hP : P = ttcParams (toDNF φ) n ε (4 * δ / 5) hε0 hε1 hn hm hr
```

The algorithm is run at the **internal** failure parameter `δ₀ = 4δ/5`, and
`1 − δ₀ − δ₀/4 = 1 − 4δ/5 − δ/5 = 1 − δ` exactly. `hδ0`/`hδ1` and the conclusion are
in the **user's** `δ`; *every other* occurrence — `P.δ`, `P.deltaPrime = δ/(5m)`,
`P.thresh`, `P.precision`, the sample counts and the charged `runCost` — is at
`δ₀`. No step of the analysis improves.

**The price, which must be quoted alongside the clean `1 − δ`:**

* **Monte-Carlo sample count per polytope: a factor `5/4`, a 25 % increase.**
  `δ' = δ₀/(4m) = δ/(5m)` against `δ/(4m)`, and
  `Ttc.MonteCarlo.nSamp K ε' δ'` is `⌈(ε'²·δ'·q)⁻¹⌉₊ + 1`, so the count goes from
  `⌈4m/(δ ε'² q)⌉₊ + 1` to `⌈5m/(δ ε'² q)⌉₊ + 1`. This feeds the `cVol` term of the
  cost conjunct.
* **`P.thresh`: an *additive* increase, not a multiplicative one.**
  `log(24/δ₀) = log(30/δ) = log(24/δ) + log(5/4)`, so the first branch of `Thresh`
  grows by the additive `24·log(5/4)/((1−ε')ε'²)` and the second by
  `15·log(5/4) ≈ 3.35`. In `ε` that is an additive `O(1/ε²)`.
* **`ε` is untouched.** `ε' = ε/12`, `η = ε/8`, `κ` and `γ` depend on `δ` not at
  all.

**What it buys.** The statement is informative on all of `δ ∈ (0,1)` instead of
only `δ ∈ (0, 4/5)`, where `1 − δ − δ/4` was already `≤ 0` and certified nothing.
At `δ = 1` the bound is `0` — no longer negative, still uninformative.

The same repricing applied one rung lower, to `Ttc.ttc_volume_endToEnd` itself
(polytope description retained), is
[`Ttc.ttc_volume_clean`](Ttc/Exec/Budget.lean); `Ttc.ttc_volume_endToEnd_delta` is
an `alias` for it, kept because earlier revisions of this page and of `README.md`
used that name. Both resolve to the same declaration.

### The caveats §1c lists still apply, unchanged

Removing binders removed **no** cost and **no** scope limitation. In particular:

1. **The sampler is not proved to differ from `uniformOn`.** `law_tv` is a theorem,
   so no *accuracy assumption* is made; but
   `contLaw i ≠ Arlib.uniformOn volume P'ᵢ` is **not** a theorem, and proving it
   needs the `L²`/aperiodicity input that is **absent from the tree**. §1c caveat 1
   lists the three weaker facts that *are* proved.
2. **Exponential in the dimension, on both routes.** `VolumeAlgorithm.monteCarlo` is
   `Θ(Rⁿ/(ε²p))` samples; the ball walk's certified step count is `2^Θ(n)·log(…)`.
   **"Unconditional" and "efficient" are independent claims and only the first is
   established here.** `thm:runtime` stays out of scope. The `5/4` above is a
   constant factor on top of an already exponential construction.
3. **The `trajLaw`/`trajOracles` identification is inherited unchanged** — see §4.
   `ttc_volume_final` is built on `Ttc.TtcProb.volume_estimate` through the chain,
   so removing an oracle is not the same as removing the model.
4. **`ttc_volume_final` now has a witness of its own, and it is not the box** —
   §3g. [`Ttc.TwoCube.ttc_volume_final_two_cube`](Ttc/Witness/TwoCube.lean)
   instantiates **this theorem**, at every `(ε, δ) ∈ (0,1]²`, on a DNF with **two**
   cubes, with every binder discharged including `big`. Until it landed, the
   strongest statement in the development had **no** non-vacuity witness at all.
   The witnesses of §3a–§3f are all the single-cube box and are witnesses for
   *other* statements; at `m = 1` the `m`-way union bound,
   `thm:decomposition`'s union and `lem:numlattice`'s multi-cube content are not
   exercised, and §3g is where they are. What §3g does **not** prove:
   `volSol = Vol₁ + Vol₂` (the two regions are proved disjoint; volume additivity
   is neither proved nor needed).

---

## 1e. The statement layer: `Ttc.ttc_volume_estimate` — the theorem `Model/` states

[`Ttc.ttc_volume_estimate`](Ttc/Model/Theorem.lean) is what an auditor who reads
only `Model/` reads. It is the **one declaration** in
[`Model/Theorem.lean`](Ttc/Model/Theorem.lean) — no `def`, no auxiliary lemma —
and its proof is three lines: rewrite by
[`Ttc.ttc_eq_ttcPairLaw`](Ttc/Monadic/Program.lean) — which is *not* `rfl`, because
`Ttc.ttc` is deliberately stated with `Measure.bind`/`map` so that no measurability
proof enters `Model/` — then apply `Ttc.ttc_accuracy_pairLaw` and
`Ttc.all_ttcPairLaw_cost_le`. Short enough that it is still the structural check
that the names in the statement name what they claim to: a wrong abbreviation
would be a build error, not a silent divergence.

> ⚠ **Read this first (2026-08-12): there are now four headline theorems, and this
> section describes the second of them.** Everything below about "eleven binders" is
> the *price-parametric* statement, which was renamed and moved:
>
> | theorem | file | prices, and binder count |
> | --- | --- | --- |
> | `Ttc.ttc_volume_estimate` | `Ttc/Model/Theorem.lean` | **fixed inside `Ttc.ttc`'s own definition**, at the Cousins–Vempala and hit-and-run numbers. **11 explicit / 13 raw** — the same eleven as the parametric one, with `cVol cSample` gone. Runtime side reads `m·n⁴·(…)` under a `∀ R γ` guard |
> | `Ttc.ttc_volume_estimate_parametric` | `Ttc/Exec/PricedHeadline.lean` | free, over `Ttc.ttcCharged`. **13 explicit / 15 raw** — the eleven plus `cVol cSample`. This is the old headline modulo that rename, and is what everything below means |
> | `Ttc.ttcPoly_volume_estimate_cv` | `Ttc/Exec/PolyAccuracy.lean` | the *swapped-bundle* run — genuinely Cousins–Vempala over hit-and-run. **68 explicit / 72 raw**, conditional on `Ttc.HitAndRunTheorem11Input`, which is **inhabited nowhere** |
> | `Ttc.ttc_runtime_mn4` | `Ttc/Exec/RuntimeMN4.lean` | the **goal-state capstone**: the row above with four accounting binders discharged. **64 explicit / 68 raw**, of which **38 are residual hypotheses**. §0a is the ledger |
>
> The first one's measure takes **four arguments and no prices**: `Ttc.ttc atoms φ ε δ`.
> Since 2026-08-12 `Ttc.ttc` is a four-ary `def` in `Model/Pseudocode`, equal by `rfl` to
> `Ttc.ttcCharged atoms φ ε δ (cvVolPriceAt …) (hrSampPriceAt …)` — the equation is the
> lemma `Ttc.ttc_def`, and `Ttc.ttcCharged` is the price-parametric law (the old six-ary
> `Ttc.ttc`, renamed) that every downstream result is proved over. The two prices are
> defined beside `Ttc.stepCost`/`Ttc.runCost`/`Ttc.algCost` in the same file, and the `rfl`
> bridges `Ttc.cvVolPriceAt_eq`/`Ttc.hrSampPriceAt_eq` (`Exec/VolPriceCVAlg`) prove each
> equals the `Ttc/Exec/` price it is named after, so the names do not stand in for the
> analysis.
>
> They are **not** prices this run is proved to pay: `cVol` and
> `cSample` are unit multipliers in `Ttc.stepCost` (`Model/Pseudocode:202`,
> `stepCost cVol cSample N = cVol + cSample * N`), so *any* pair of naturals yields a
> bound of that shape — at `0` it yields `r.2 ≤ 0`. Fixing them is a modelling choice.
> `Ttc.ttcVolPrice` and `Ttc.ttcSampPrice` are the numbers this run *is* shown to pay
> (§ below), and both are exponential in `n`. See the boxed warning at the head of
> `Ttc/Exec/PricedHeadline.lean`.

It takes **eleven binders about the algorithm and its input**, and its type
contains no `Ttc.TtcProb`, no `Ttc.VolumeAlgorithm` and no `Ttc.KV97Sampler`:

```
atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos
```

In `Ttc.ttc_volume_estimate_parametric` two more explicit binders follow them,
`cVol cSample : ℕ`, the per-call costs the running-time conjunct is charged in; every
"eleven" on this page means the list above and excludes those two. That statement's
raw arity is therefore **15** — eleven, plus the two costs, plus the implicit ambient
`{A}` and `{n}` — and its explicit arity is **13**.

**`Ttc.ttc_volume_estimate` itself has exactly the eleven above: 11 explicit, 13 raw.**
The two prices are gone; the ambient `{A}`, `{n}` remain. §5's probe prints the raw
number; say which convention you are quoting.

**Eleven binders**, and it is worth naming what is *not* among them: no
interpretation `M`, no parameter block `P`, no DNF converter, no oracle argument,
no precision argument, no inscribed-ball data, no regime condition
`hvol : Thresh/4 ≤ Vol(F)`, no `hcoeff`, no per-cube full-dimensionality `hint`,
and **no boundedness hypothesis `hbdd`**. Those did not all go the same way, and
the difference matters more than the count: some were substituted for definitions,
some were *derived*, and **four rounds removed binders by changing what the
algorithm is handed or does** — a dilation, a constructed inscribed ball, a
cleanup and a pruning. §1g grades all four; §1h grades the three *preprocessing
passes* (dilation, pruning, cleanup) as what the headline certifies `alg:ttc`
**plus**, with the constructed ball alongside them. Read both before quoting this
statement.

**Two conjuncts, not one — and both about the same run.** Both are stated over a
single law on a single space: `Ttc.ttcCharged atoms φ ε δ cVol cSample : Measure (ℝ × ℕ)`
(and, for the fixed-price headline, its four-ary specialisation
`Ttc.ttc atoms φ ε δ`, equal to it by `Ttc.ttc_def`)
([`Model/Pseudocode`](Ttc/Model/Pseudocode.lean)), the algorithm's own law on
`(estimate, charged cost)` — draw the volume coins, draw the sample trajectory at
the rates they produced, return the pair. **There is no iterated integral.** The
accuracy conjunct is `1 − δ ≤ Pr[r ← ttc …; r.1 ∈ relErr ε (volSol …)]` — the
measured quantity is `Model/Pseudocode`'s own `Ttc.ttcRun` on the preprocessed
input, divided by the dilation factor to the `n`, and the target is the **user's
own** `volSol (atomSet atoms) φ`. The proof goes through
[`Ttc.ttcPairLaw`](Ttc/Monadic/Program.lean)
`: Measure ((ℕ → Space n) × (ℕ → Fin (ttcIndex …) → ℕ))`, the composition–product of
the volume coins with the coin-indexed trajectory kernel, of which `Ttc.ttc` is a
pushforward; that is a proof-side object and is not named by the statement. Folding
the earlier
`∫⁻ c, trajLaw … {t | …} ∂(MonteCarlo.coins n)` into that one measure is
[`Ttc.lintegral_good_event_eq_compProd`](Ttc/Monadic/EventMeasurable.lean), which
needs the good event measurable **jointly** in `c` and `t`. `Ttc.ttc` is a
`MeasureTheory.Measure`, not a `PMF` (nfalean's `ApproxNFA.countNFAM` is one):
`Ttc.MonteCarlo.coins` is atomless on an uncountable space, so no `PMF` has it as
its outer measure — see [`Monadic/MeasurePr`](Ttc/Monadic/MeasurePr.lean).

The running-time conjunct bounds `alg:ttc`'s *charged* cost by
`m · (C_vol + C_sample · (Thresh + 1))`, spelled out as an explicit expression in
`ε`, `δ` and the preprocessed DNF's length. **Read its quantifier carefully — this
page has had it wrong in both directions.** It is `All[r ← ttc …; …]`, and `All[…]`
in [`Monadic/MeasurePr`](Ttc/Monadic/MeasurePr.lean) is Mathlib's `∀ᵐ`: the bound
holds **almost every** run, not every one. There is **no termination hypothesis**;
the guard was discharged, not assumed (`Ttc.ae_ttcLaw_ttcTerminates`,
`Ttc.all_ttcPairLaw_cost_le`). What the a.e. form costs is at most a factor 2 on
the threshold term, because the guard-free bound uses a sum where the guarded one
uses a `max`; the sharper guarded forms are kept as
`Ttc.ttcPairLaw_cost_le_of_terminates` and
`Ttc.all_ttcPairLaw_cost_le_of_terminates`, and they are **incomparable** with this
conjunct — sharper in the bound, weaker in the hypothesis. The a.e. form is not the
weakening it looks like: `Ttc.ttcPairLaw` is a pushforward along a countably
determined map, so `Ttc.all_ttcPairLaw_iff_atoms` collapses `∀ᵐ` to "at every atom",
which is exactly nfalean's `PMF.support` shape. None of this is a polynomial-time
claim (`thm:runtime` remains out of scope, and both oracle routes are exponential
in `n` — §1c caveat 2).

The first nine binders (`atoms … hn`) are exactly `ApproxNFA.approxNFA_countNFA`'s
(the nfalean template) binder list; they are the inputs and the parameter range and
assert nothing about the instance. The other **two** — `hφ` and `hpos` — are the
honest residue, and both are conditions on the *input*:

| binder | says | status |
| --- | --- | --- |
| `hφ : φ.IsPositive` | the formula is negation-free | removable in principle, at a price that is itself machine-checked — §1g's third negative result and [`Ttc/Findings/OpenHalfspace.lean`](Ttc/Findings/OpenHalfspace.lean) |
| `hpos : 0 < volSol (atomSet atoms) φ` | the solution set has positive volume | **strictly weaker than the per-cube full-dimensionality `hint` it replaced**: [`Ttc.volSol_pos_of_interior`](Ttc/Exec/Prune.lean) proves `hint → hpos`, and [`Ttc.hint_not_derivable`](Ttc/Exec/Degenerate.lean) refutes the converse |

`hφ` and boundedness are **logically independent in both directions** — this is why
neither could ever be dropped in favour of the other while `hbdd` was a binder
([`Ttc.Independence.exists_isBounded_not_isPositive`](Ttc/Findings/Independence.lean),
[`Ttc.Independence.exists_isPositive_not_isBounded`](Ttc/Findings/Independence.lean),
the latter also at a non-degenerate witness as
[`…exists_isPositive_not_isBounded_halfspace`](Ttc/Findings/Independence.lean)).
That file claims nothing more: it does **not** claim any particular pair is the
weakest usable one. **`hbdd` is now gone, and it went by derivation rather than by
weakening** — §1h has the derivation and why it became available only after the
pruning round.

**`hvol` is no longer a binder, and §1f is no longer about the headline's last
binder.** §1f's counterexample [`Ttc.Box.big_not_derivable`](Ttc/Exec/Regime.lean)
still stands and is *why* the algorithm had to be amended; the amendment (a dilation
step) is §1g's first item.

### What this statement names, and what it does not

This is the boundary the four-file target is drawn around, and it is the thing to
check first, because it is the one claim about `Model/` that a machine can settle.

* **The algorithm's own data is `Model/Pseudocode`'s.** The transcriptions
  `Ttc.run` / `Ttc.ttcAlgOutput` / `Ttc.ttcRun`, the converter `Ttc.toDNFd`, the three preprocessing passes
  `Ttc.pruneForm` / `Ttc.cleanForm` / `Ttc.preprocess`, the inscribed-ball
  construction `Ttc.ballData` / `Ttc.cenOf` / `Ttc.gammaOf`, the dilation factor
  `Ttc.scaleFactor`, and the parameter block `Ttc.ttcParams` / `Ttc.inputParams`
  (`alg:ttc` lines 17–20) are all declarations of
  [`Model/Pseudocode.lean`](Ttc/Model/Pseudocode.lean). `Ttc.volSol` and
  `Ttc.relErr` are `Model/ProblemSetting`'s; the vocabulary (`Ttc.BForm`,
  `Ttc.sol`, `Ttc.region`, `Ttc.Params` and its derived constants including
  `Ttc.Params.precision`) is `Model/Prelude`'s.
* **Nothing remains outside `Model/`.** The constructed oracle bundle
  (`Ttc.algOracles`), the sample-coin law `Ttc.trajLaw` and the volume-coin law
  `Ttc.MonteCarlo.coins` are all named by the statement and all defined under
  `Model/` — `trajLaw` and `MonteCarlo.coins` in `Model/Prelude`, the bundle in
  `Model/Pseudocode`. All are *constructions*, not assumptions, which is the
  content of §1c and §1d.

**This is the opposite trade from the reference layout**, and an auditor should
know which one is in force: nfalean's `ApproxNFA/Model/Theorem.lean` names
`(countNFAExec A n ε δ).P.Pr` and lets `countNFAExec` sit outside its `Model/`,
keeping `Model/` readable before the development. Here the objects were moved *in*
instead, so `Model/Prelude` imports four `Arlib.*` modules and `Model/Theorem`
imports `Monadic/`. The statement's closure is clean; `Model/` is no longer a layer
you can read first. §5 has the probe; run it rather than trusting this subsection,
especially after any move between `Model/` and `Exec/`.

What this boundary does **not** buy is self-containedness of the *bodies*: the
names above abbreviate terms that reach into `Arlib`'s mixing and convex-geometry
stack, and that definitional closure — the real trusted base — is §1h.

### What is *not* an input, and what replaced it

**Read the third column before the second.** Substituting a definition for a
binder is bookkeeping; deriving a binder is a genuine gain; changing the algorithm
so that a binder holds is neither, and is the row an auditor is most likely to
misread as a stronger theorem.

| Was a binder | Is now | Kind |
| --- | --- | --- |
| `M`, `M_eq` | `Ttc.atomSet atoms`, a definition of [`Model/Pseudocode`](Ttc/Model/Pseudocode.lean). `M_eq` was an equation *defining* `M` | substitution |
| `P`, `hP` | `Ttc.inputParams …`, a definition (`alg:ttc` lines 17–20), at the internal failure parameter `δ₀ = 4δ/5` — §1d prices that | substitution (with §1d's repricing) |
| `toDNF`, `isDNF`, `isPositive` | pinned to `Ttc.toDNFd`; `isDNF` is `Ttc.toDNFd_isDNFOf`, `isPositive` follows from `hφ` on the **input formula** | substitution, but see "bought rather than proved" below |
| `hm` | `Ttc.one_le_card_cubes_of_ne_nil` together with `Ttc.toDNFd_ne_nil` — `Ttc.BForm` has no `false` constructor and `IsPositive (.neg _)` is `False`, so a positive formula's DNF is never `[]` | derived from `hφ` |
| `hr` | [`Ttc.one_le_card_facets_of_isBounded`](Ttc/Exec/CubeBounds.lean) — a literal-free cube has `region = Set.univ ⊆ sol`, and `Set.univ` is unbounded in `Ttc.Space n` for `n ≥ 1`, so boundedness excludes it | derived |
| `hlen` | [`Ttc.length_toDNFd_le_card`](Ttc/Exec/Dedup.lean), with **equality** | derived, once the converter is `toDNFd` |
| `T.O` | a closed term, not a hypothesis: the constructed oracle bundle, with `Ttc.mcVol` (a Monte-Carlo estimator) for `Vol_ED` and the covered-lattice sampler for the rest | **construction** — §1c, and item 7 of "Checks that a green build does not perform" |
| `T.ρ` | `P.precision γ̂` = [`Ttc.Params.precision`](Ttc/Model/Prelude.lean) = `⌈log₁₀(γ/γ̂)⌉`, `GetPrecision`'s **output** | substitution |
| `hvol : Thresh/4 ≤ Vol(F)` | **discharged by amending the algorithm**: the input is dilated by `Ttc.runScale` and the estimate divided by `cⁿ` ([`Ttc.hvol_scaled`](Ttc/Exec/Rescaled.lean)) | **algorithm change** — §1g |
| `cen`, `gammaHat`, `hgammaHat`, `ball_subset` | `Ttc.autoCen`/`Ttc.autoGamma`, built from [`Ttc.cenOf`](Ttc/Model/Pseudocode.lean)/[`Ttc.gammaOf`](Ttc/Model/Pseudocode.lean). `ball_subset` becomes the unconditional [`Ttc.ball_subset_cenOf`](Ttc/Exec/Inscribed.lean); `hgammaHat` becomes [`Ttc.gammaOf_pos_of_interior`](Ttc/Exec/Inscribed.lean), which needs full-dimensionality — supplied by the pruning. **Not the paper's LP** | **algorithm change** — §1g |
| `hcoeff` | the algorithm is run on the cleaned formula [`Ttc.cleanForm`](Ttc/Model/Pseudocode.lean), for which it holds outright ([`Ttc.coeff_ne_zero_toDNFd_cleanForm`](Ttc/Exec/Cleanup.lean)) | **algorithm change, but the benign one**: [`Ttc.sol_cleanForm`](Ttc/Exec/Cleanup.lean) is an **exact set equality** — §1g |
| `hint : ∀ i, (interior (region …)).Nonempty` | the degenerate cubes are *pruned* ([`Ttc.pruneForm`](Ttc/Model/Pseudocode.lean)), and the surviving hypothesis is the strictly weaker `hpos` | **algorithm change** — pruning moves `Sol(F)` by a null set; §1h |
| `hbdd : IsBounded (sol (atomSet atoms) φ)` | [`Ttc.isBounded_sol_pruneForm_of_volSol_pos`](Ttc/Exec/BddFromPos.lean) — boundedness of the *pruned* `Sol`, proved from `hφ` and `hpos` alone | **derived**, and the derivation is only available after the pruning round — §1h |

### The one thing that was bought rather than proved

`hlen` is a duplicate-freeness condition and `Ttc.toDNF` **provably fails it**
([`Ttc.toDNF_length_gt_card_cubes`](Ttc/Exec/Statement.lean): `a ∨ a` has DNF
`[[a],[a]]`). Pinning the converter to the deduplicated
[`Ttc.toDNFd`](Ttc/Model/Pseudocode.lean) changes *what the algorithm runs on*.
Deduplication preserves the semantics exactly
([`Ttc.mem_toDNFd`](Ttc/Exec/Dedup.lean) — same cubes, hence
the same `IsDNFOf`, the same regions, the same union) but it changes the **cost
profile**: `m` shrinks, so `P.deltaPrime = δ₀/(4m)` grows and each surviving cube is
estimated at a looser confidence. Read it as a repricing, exactly like the
`δ₀ = 4δ/5` one of §1d — not as a free win.

**Consequence, and do not skip it:** `Ttc.ttc_volume_estimate` is **not** strictly
stronger than [`Ttc.ttc_volume_stmt`](Ttc/Exec/Statement.lean). That statement runs
on `Ttc.toDNF`, this one on `Ttc.toDNFd`; they are guarantees about *different runs*
of the algorithm, and neither implies the other. `Exec/Statement.lean` is
deliberately kept and is deliberately off the headline's import closure.

### The four inscribed-ball binders that used to stay

`cen`, `gammaHat`, `hgammaHat`, `ball_subset` described the inscribed ball `alg:prec`
line 86 computes by an LP, and were kept as instance *data* because replacing them
with a bare existence hypothesis would force the conclusion to name a
`Classical.choose` and make `big` unprovable for concrete instances. They are now
gone — but the ball that replaced them **is** a `Classical.choose`
([`Ttc.ballData`](Ttc/Model/Pseudocode.lean)), and what made that affordable is that
`big` is no longer a binder either. See §1g for what the constructed ball is and is
not.

### Non-vacuity

[`Ttc.TwoCube.ttc_volume_estimate_two_cube_full`](Ttc/Witness/FullTwoCube.lean)
applies **this theorem** — not a predecessor — to the two-cube witness at every
`n ≥ 1` and every `(ε, δ) ∈ (0,1]²`, and
[`…_two_cube_full_at`](Ttc/Witness/FullTwoCube.lean) pins `(1/3, 9/10)` and
`(1/2, 1/4)` with the achieved bounds `1/10` and `3/4` proved **strictly positive
inside the statement**, so neither conclusion is the vacuous `0 ≤ (…).toReal`;
[`Ttc.TwoCube.twoProbFull_pos_ne_top`](Ttc/Witness/FullTwoCube.lean) is the separate
`≠ ⊤` check. The residual obligation `hpos` is discharged by
[`Ttc.TwoCube.twoVolPos`](Ttc/Witness/FullTwoCube.lean) — one application of
`Ttc.volSol_pos_of_interior` to
[`Ttc.TwoCube.interior_region_nonempty_two_d`](Ttc/Witness/FullTwoCube.lean), with
no volume computed — and
[`Ttc.TwoCube.twoProbFull_def`](Ttc/Witness/FullTwoCube.lean) writes the named
probability out, by `rfl`, in exactly the shape the headline's conclusion has. The
hypotheses transported to the deduplicated cube list are in
[`Ttc/Witness/Inputs.lean`](Ttc/Witness/Inputs.lean), whose
`Ttc.TwoCube.toDNFd_twoForm` proves the two-cube DNF is already duplicate-free —
**special to this witness**, not a general fact.

### The two per-call charges `cVol`, `cSample`: parametric upstream, fixed in the headline, exponential in fact

> ⚠ **Read this box before the subsection.** `cVol`/`cSample` are **no longer binders
> of `Ttc.ttc_volume_estimate`.** They are binders of
> `Ttc.ttc_volume_estimate_parametric`, the price-parametric statement over
> `Ttc.ttcCharged`, which is what everything below is about. In the headline they are
> **fixed**, at `Ttc.cvVolPriceAt` and `Ttc.hrSampPriceAt` (`Model/Pseudocode`), inside
> `Ttc.ttc`'s own *definition* — and those are **not** either of the two derived bounds
> below. See the box at the head of §1e.

#### What the fixing did and did not change

**Did:** the headline's running-time conjunct now reads `m · n⁴ · (…)`, so the shape
`thm:runtime` prints is the shape the theorem states. `Ttc.ttc_volume_estimate` lost
two binders in the process — it is **11 explicit / 13 raw**, not the 13/15 earlier
revisions of this page and of the README quote.

**Did not:** make the run pay those prices. `Ttc.ttc`'s oracle bundle is the closed
term `Ttc.algOracles` — hit-and-miss Monte Carlo over the lazy ball walk — and
`cVol`/`cSample` are unit multipliers in `Ttc.stepCost`'s fold, so substituting *any*
pair of naturals yields a law of this shape (at `0`, the charged cost is identically
`0`). Charging the Cousins–Vempala and hit-and-run prices inside a run that executes
neither oracle is a **modelling choice, not a costing of this run**. The prices this
run *can* be shown to pay are `Ttc.ttcVolPrice` and `Ttc.ttcSampPrice`, and they are
still exponential in `n` — the closed forms are below and are unchanged.

**So the sentence this subsection used to end with —** "substituting `O(n⁴)` into the
headline would assert what the formalisation refutes" — **is now too strong for the
headline and exactly right for the run.** Precisely: the *statement* has been given the
`n⁴` shape at fixed prices, legally, as arithmetic; what remains refuted is that
`Ttc.ttc`'s **own** oracles cost `O(n⁴)`, and what remains unproved is that `TTC` runs
in `O(m·n⁴)` at all. §0a's `Ttc.ttc_runtime_mn4` is the nearest thing to the latter, and
it is a charged-cost bound over a *different program* under 38 hypotheses.

`alg:ttc` line 24's `Vol_ED` and line 43's `GenerateSamples` are oracle calls whose
per-call cost the paper never fixes, so the statement quantifies over them. That keeps
the running-time half a claim about **every** charging convention rather than one
arbitrary one. (nfalean needs no such parameter: its cost model is entirely internal.)

Both are nevertheless *derived* quantities with proved closed forms — the statement is
parametric by choice, not for want of them:

* `Ttc.CostModel.coinCost_est_eq` is an **equality**, `coinCost (MonteCarlo.est K ε pf)
  = MonteCarlo.nSamp K ε pf`, and `Ttc.ttcVolCoins_le_ttcVolPrice` (`Exec/PriceList`)
  bounds it uniformly over the DNF's cubes by `⌈(γ⁻¹·diam(Sol) + 1)ⁿ / (ε'²·δ')⌉₊ + 1`.
* `Ttc.ttcSampleSteps_le_ttcSampPrice` (`Exec/SamplePrice`) bounds the sampler's chain
  length uniformly by `⌈Ttc.mixStepsBound at cube-free arguments⌉₊`, under exactly the
  five input conditions the headline already carries.

**Those prices are exponential in `n`, not `O(n⁴)`.** `cVol` is `Θ((diam/γ)ⁿ/(ε'²·δ'))`
— hit-and-miss Monte Carlo's rejection factor — and `cSample` is
`Θ(4ⁿ·(γ+Dm)^{4n}/γ^{4n})`, with a further `(1+κ/(10^ρ·q·γ̂))ⁿ·10^(ρn)·qⁿ` inside the
logarithm. `thm:runtime`'s `cVol = O(n⁴)`, `cSample = O(n³)` are the **paper's** figures,
for a Cousins–Vempala oracle and a polynomial sampler; **this development proves neither,
and for the constructions it does build the true prices are exponential.** Reading the
headline's fixed `O(n⁴)` charge as a statement about `Ttc.algOracles` would therefore
assert what the formalisation refutes — see the box at the head of this subsection for
what the fixing does and does not claim.

Three further reasons a concrete numeral there would overclaim: `mixSteps` does not occur
in `Ttc.ttcRun`'s definitional closure at all — it enters through `Ttc.ttcRates`, the
*law* — so `cSample` prices the chain the sampler's law is defined by rather than steps
the run takes; `Ttc.kv97SampD`'s rejection rounds are unbounded and counted nowhere; and
`alg:ttc` lines 32–42's `while` loops and per-step arithmetic are uncharged. **A bound on
an undercount is not a bound on the count, and nothing here bounds a running time.**

### Which quantifier the running-time half uses, and what it is not

`All[r ← μ; E r]` is `∀ᵐ r ∂μ`, and it carries **no termination hypothesis**: the
absorption loops halt `Ttc.ttc`-almost surely (`Ttc.trajLaw_ae_terminates`,
`Process/Truncation`; transported by `Ttc.ae_ttcLaw_ttcTerminates`), so the guard earlier
versions carried is discharged rather than assumed. The *pointwise* form remains **false**
without interrupt-truncation — off the absorption guard `Ttc.absorbLevel` degenerates
(`Nat.sInf ∅ = 0`) and the count handed to `GenerateSamples` is unbounded — but the a.e.
form no longer needs it. A truncated variant is designed in `Process/Truncation` and
deliberately not applied; its sentinel would have to be `-1`, not `0`, since `0` is a
legitimate output of `Ttc.run` (`Findings/SmallBody`) and `0 ∈ relErr 1 V`, so a `0`
sentinel would let interrupted runs count as *correct*.

This is **not** weaker than nfalean's support-based `All`. For a `PMF`,
`support p ⊆ {x | E x}` ⟺ `p.toOuterMeasure {¬E} = 0`, so the support and a.e. forms
coincide; and by `Ttc.all_ttcPairLaw_iff_atoms` the same collapse holds for `Ttc.ttc`,
which is a pushforward along a countably determined map and hence carried by a countable
set. `Monadic/MeasurePr` proves `∀ ⟹ AllS ⟹ All` with **both arrows strict**
(`exists_all_and_not_allS`, `exists_allS_and_not_forall`), and restating the conjunct with
`AllS` would genuinely discard the claim at coin sequences leaving the unit ball, since
`Ttc.MonteCarlo.coinLaw` is `Arlib.uniformOn volume (Metric.ball 0 1)` and so `ttcLaw` is
not `IsOpenPosMeasure`.

Two strictly sharper statements are kept, **incomparable** with the conjunct — sharper in
the bound, weaker in the hypothesis: `Ttc.ttcPairLaw_cost_le_of_terminates` (over
`Set.range (Ttc.ttcPair …)`, no exceptional set at all) and
`Ttc.all_ttcPairLaw_cost_le_of_terminates` (the `max`-shaped `Ttc.ttcThresh` rather than
the sum). The constant in the headline is at most a factor 2 off on the threshold term
(`max a b ≤ a + b`, both branches kept and proved nonnegative); that factor is what
dropping the guard cost.

### Why a `Measure` and not a `PMF`

`Ttc.MonteCarlo.coins` is `MeasureTheory.Measure.infinitePi` of the uniform law on a
Euclidean ball — an **atomless** measure on an uncountable space — so there is no `PMF`
whose `toOuterMeasure` it is. This is a fact about the object, not a stylistic choice;
`Monadic/MeasurePr` works through the consequences. What survives of the Giry structure:
`Ttc.ttcTrajKernel` is a Markov kernel, `⊗ₘ` is the monadic bind, `Ttc.ttcLaw` is a
probability measure. `Model/Pseudocode` spells `Ttc.ttc` with `Measure.bind`/`Measure.map`
rather than `⊗ₘ` deliberately: the `⊗ₘ` form is definitionally `Ttc.ttcPairLaw` but would
drag `Ttc.ttcTrajKernel` and its measurability proof into `Model/`. The price is that
`Ttc.ttc_eq_ttcPairLaw` (`Monadic/Program`) is a three-step proof rather than `rfl`.

There is also **no iterated integral**. Earlier versions carried
`∫⁻ c, trajLaw (ttcRates … c) {t | …} ∂(MonteCarlo.coins n)`, quantifying the two coin
sequences separately in the two conjuncts. Folding them into one measure is
`Ttc.lintegral_good_event_eq_compProd`, and it is not free: it needs the good event
measurable **jointly** in `c` and `t`, which is what `Monadic/EventMeasurable` establishes
via `Ttc.CountablyDetermined` (`Ttc.run` folds through a `Multiset (Space n)` state with no
measurable structure, and `Ttc.absorbLevel` is an unbounded `Nat.sInf` search).

> **Do not cite [`Ttc/Witness/Headline.lean`](Ttc/Witness/Headline.lean) for this.**
> `Ttc.TwoCube.ttc_volume_estimate_two_cube` and `…_at` witness
> [`Ttc.ttc_volume_inputs`](Ttc/Exec/Inputs.lean) — several rungs down, below the
> dilation, the constructed ball and the cleanup — and that file says so itself
> (its own "moved on twice" predates the cleanup round). Dilating the input makes it
> a **different run** with a different probability; no equality between the two
> numbers is claimed and none should be read into the shared names.

---

## 1f. `big` is independent — proved, not conceded

> **This section is about a binder the headline no longer has.** `big`, and its
> readable successor `hvol : Thresh/4 ≤ Vol(Sol F)`, are both gone from
> `Ttc.ttc_volume_estimate` (§1e). They are gone because the **algorithm was
> amended** (§1g), not because the counterexample below stopped being true. Read
> this section as: *why `alg:ttc` as printed needs the regime condition*.

[`Ttc.Box.big_not_derivable`](Ttc/Exec/Regime.lean) is the answer to the obvious
question about that binder. It exhibits an explicit box instance satisfying
**every other hypothesis** of `Ttc.ttc_volume_final` — `isDNF`, `isPositive`, `hm`,
`hr`, `hP`, `hlen`, `hbdd`, `hcoeff`, `hgammaHat`, `ball_subset`, all asserted
positively in one conjunction — together with `¬big`. Note that refuting a
`∀ c ∈ mcGood, …` requires `mcGood` to be inhabited, which
`Ttc.Box.mcGood_box_nonempty` supplies; without it the refutation would be vacuous.

**Why `big` cannot be derived.** The only quantitative fact the development has
about the sampler is `eq:almostuniform`, which pins each lattice point's mass to
`(1 ± ε')/N`. Summing over the `N` enumerated points, **the `N` cancels** — refining
the precision multiplies the summand count by `10^(ρn)` and divides each summand by
the same factor, so `ρ = ⌈log₁₀(γ/γ̂)⌉` cannot rescue it. What remains
([`Ttc.Box.sum_rates_box_window`](Ttc/Exec/Regime.lean)) is

```
(1 − ε')²·Vol(Sol F)  ≤  ∑ θ  ≤  (1 + ε')²·Vol(Sol F)
```

while `Thresh` depends only on `(ε, δ, m)` and does not shrink with the body. So:

> **`big` ⟺ the solution set is large.** *Sufficient*
> ([`Ttc.Box.big_of_thresh_le_volume`](Ttc/Exec/Regime.lean)):
> `Thresh/8 ≤ (1−ε')²·Vol(Sol F)`. *Necessary*
> ([`Ttc.Box.thresh_le_volume_of_big`](Ttc/Exec/Regime.lean)):
> `big ⟹ (1−ε')·Thresh/8 ≤ (1+ε')²·Vol(Sol F)`. The gap between the two is
> `((1+ε')/(1−ε'))² ≤ 1.40`. It **fails** whenever
> `Vol(Sol F) < (1−ε')·Thresh/(8(1+ε')²)`, and no choice of `γ̂` or precision
> affects that. Every other hypothesis is scale-free: shrinking `[0,a]ⁿ` with
> `γ̂ = a/2` preserves all of them while `∑ θ → 0`.

This is why the development's own witnesses size their boxes at `max 1 Thresh`. An
auditor should read **`alg:ttc` as printed** as: *correct only on instances whose
solution set is large relative to the threshold `Thresh(ε, δ, m)`*. The headline
`Ttc.ttc_volume_estimate` has no such condition because it is about the **amended**
algorithm, the one with the dilation line (§1g).

**The paper has the same gap, and this is where it is.** `sections/analysis.tex:284`
defines `j*` as the smallest `j` with `1/(2^j·10^{ρn}) < Θ/(4|S^{(m)}|)`; the proof
of `lem:numlattice` then bounds one term using "`p` decreases from `1/2^{j*−1}` to
`1/2^{j*}`" (`:289`) and the other using `Λ_{j*−1} > (1−ε')Θ/8` (`:295`) — **both
require `j* ≥ 1`, which is never stated**. At `j* = 0` the first sum is empty and the
second term is the sure event, so the displayed bound reads `≤ 1`. `j* = 0` is exactly
`Vol(Sol F) ≲ Θ/4`. `big` is therefore not an artefact of the formalisation: it is the
paper's unstated precondition, made visible. Written up as **README finding 20**, with
the numeric size of the excluded regime (`Vol ≳ 4.8 × 10⁵` at `ε = δ = 0.1`).

`Ttc/Exec/Regime.lean` contains **no `def`, `structure` or `class` at all**, which
is the structural check that nothing in it is `big` wearing a hat.

### `big` is now derived, and the independence is unaffected

[`Ttc.big_of_volume`](Ttc/Exec/RegimeMain.lean) proves `big` from
`hvol : Thresh/4 ≤ Vol(Sol F)`, which is what turned `big` from a binder into a
theorem; `hvol` itself was then discharged by the dilation (§1g), which is why
neither appears in the headline's eleven binders (§1e). The chain is four steps, each
a named lemma:

| Step | Lemma |
| --- | --- |
| every enumerated lattice point contributes `≥ (1−ε')²(1−η)/10^{ρn}` — **pointwise, no fiber counting** | [`Ttc.rate_ge_pointwise`](Ttc/Exec/RegimeSum.lean) |
| hence `∑ θ ≥ (1−ε')²(1−η)·L` | [`Ttc.sum_rates_ge_of_pointwise`](Ttc/Exec/RegimeSum.lean) |
| `L ≥ Vol(Sol F)/(1+η)` | [`Ttc.lattice_of_dnf`](Ttc/Lattice/Assembled.lean), upper half |
| `(1−ε')(1−η)/(1+η) ≥ 1/2` on `ε ∈ (0,1]` | [`Ttc.half_le_of_eps`](Ttc/Exec/RegimeMain.lean) |

with the two per-cube inputs supplied by
[`Ttc.e2eSampD_almostUniform`](Ttc/Exec/RegimeInputs.lean) (`eq:almostuniform` for
the capstone's own sampler, at every cube, **with no nonemptiness hypothesis**) and
[`Ttc.lattice_cube_of_dnf`](Ttc/Exec/RegimeCube.lean) (`lem:lattice` per cube over
plain data).

**Read `big → hvol` as a change of presentation, not of strength.** `hvol` is false
for small bodies exactly as `big` was; `Ttc.Box.big_not_derivable` is what says so,
and it is unchanged. The two-cube witness satisfies `hvol` at that rung because it
sizes its boxes at `max 1 Thresh`
([`Ttc.TwoCube.two_cube_thresh_le_volSol`](Ttc/Witness/TwoCubeVol.lean)). Getting rid
of `hvol` altogether was **not** a change of presentation — that is §1g.

---


## 1g. Four rounds that changed the algorithm, not the analysis

The seventeen-binder statement carried `hvol : Thresh/4 ≤ Vol(Sol F)`, four binders
describing the inscribed ball, and `hcoeff`. All three groups are gone, a fourth
round (pruning) removed `hint`, and **an auditor must know that none of them went
away by a sharper proof.** In one line each:

| Round | Binders removed | What actually happened | Is the algorithm's behaviour changed? |
| --- | --- | --- | --- |
| dilation ([`Exec/Rescaled`](Ttc/Exec/Rescaled.lean)) | `hvol` | the input is scaled up by `c` before the run and the estimate divided by `cⁿ` after | **yes** — a new line in `alg:ttc`; the printed algorithm is *wrong*, not merely unproved, on a small body |
| constructed ball ([`Exec/Inscribed`](Ttc/Exec/Inscribed.lean)) | `cen`, `gammaHat`, `hgammaHat`, `ball_subset` | the ball is chosen classically instead of supplied | **yes** — it is *some* inscribed ball, not `alg:prec`'s maximal one; the run uses a possibly larger `ρ` |
| cleanup ([`Exec/Cleanup`](Ttc/Exec/Cleanup.lean), [`Exec/CleanInput`](Ttc/Exec/CleanInput.lean)) | `hcoeff` | the algorithm is handed `Ttc.cleanForm atoms φ` rather than `φ` | **only the description** — [`Ttc.sol_cleanForm`](Ttc/Exec/Cleanup.lean) is an *exact set equality*, so the body measured is literally the same set |
| pruning ([`Exec/Prune`](Ttc/Exec/Prune.lean)) | `hint` (replaced by the weaker `hpos`) | the degenerate, lower-dimensional cubes are dropped before the run | **yes** — `Sol(F)` changes by a null set; this is also what made the derivation of `hbdd` available |

The four rows are not equally serious, and the table's last column is the point.
§1h grades the same steps as *preprocessing* and is the complete list; read it,
not this table, for what the headline certifies `alg:ttc` **plus**.

### `hvol` → a dilation step

`alg:ttc` sets `p ← 1` and only ever halves it (lines 21, 33, 40), so the sketch is
`Poisson(Λ)` with `Λ ≤ Vol(Sol F)`, and a Poisson count has relative standard
deviation `Λ^(-1/2)`. On a body of volume `10⁻⁶` the run draws `Pois(10⁻⁶)` points and
returns `0`, which is not in `(1 ± ε)·10⁻⁶`. **The printed algorithm is wrong there**,
and [`Ttc.Box.big_not_derivable`](Ttc/Exec/Regime.lean) is the machine-checked form.

So the algorithm was amended: dilate the input by
`c = Ttc.scaleFactor n P γ̂ = max 1 (Thresh/(Vₙ·γ̂ⁿ))`, run, divide the estimate by
`cⁿ`. `Vol(c·S) = cⁿ·Vol(S)` exactly ([`Ttc.volSol_scaleAtoms`](Ttc/Exec/Scale.lean)),
`c` is computable from `γ̂` and `n` **with no knowledge of `Vol`**, and after the
dilation the body clears the threshold
([`Ttc.thresh_le_scaled_ball_volume`](Ttc/Exec/ScaleFactor.lean)), so `hvol` is
discharged ([`Ttc.hvol_scaled`](Ttc/Exec/Rescaled.lean)).

> **What is certified is `alg:ttc` *plus one line*.** The paper's algorithm does not
> dilate. `Ttc.ttc_volume_estimate` is unconditional for the amended algorithm; it says
> nothing about the printed one on a small body, where the printed one is false.

The parameter block is unchanged by the dilation — it is computed from
`(toDNFd φ, n, ε, δ)`, so [`Ttc.inputParams_scaleAtoms`](Ttc/Exec/Rescaled.lean) is
`rfl`. That is why `c` can be defined from `P` without circularity.

### `cen`, `gammaHat`, `hgammaHat`, `ball_subset` → `GetPrecision` constructs the ball

`alg:prec` line 86 is `γ̂ ← MaxInscribedBall(P^i)`: the ball is *computed*.
[`Ttc.ballData`](Ttc/Model/Pseudocode.lean) picks an inscribed ball per cube,
[`Ttc.gammaOf`](Ttc/Model/Pseudocode.lean) takes the least radius, and
[`Ttc.ball_subset_cenOf`](Ttc/Exec/Inscribed.lean) is **unconditional** — a region with
empty interior gets radius `0`, and `Metric.ball _ 0 = ∅` is inside anything. Only
positivity needs an input condition, and that is `hint`.

The centre map and radius the headline actually uses are
[`Ttc.autoCen`](Ttc/Exec/Rescaled.lean) and
[`Ttc.autoGamma`](Ttc/Exec/Rescaled.lean) — `cenOf`/`gammaOf` at `Ttc.atomSet atoms`
and `Ttc.toDNFd _`. Note **at which formula**: in `Ttc.ttc_volume_estimate` every
occurrence is `autoCen atoms (cleanForm atoms φ)` / `autoGamma atoms (cleanForm atoms
φ)`, since the cleaned formula is what the algorithm is handed; only the accuracy
*target* `volSol (atomSet atoms) φ` is at the original `φ`.

Two caveats, both in the module docstring:

* **This is not the LP, and it is not a maximal ball.** `Ttc.ballData` is
  `Exists.choose` on "a ball of positive radius fits"; nothing in the file claims
  optimality, and `Ttc.gammaOf` then takes the *least* of the per-cube radii.
  Non-maximality is sound but not free: the radius enters only through
  `ρ = ⌈log₁₀(γ/γ̂)⌉`, and a smaller `γ̂` makes `ρ` **larger** — a finer lattice, a
  more expensive but still correct run. The guarantee is unaffected; the **cost is
  looser than `alg:prec`'s**, and the run is not the paper's run.
* **`hint` is a genuine restriction on the input, and it is proved not derivable.**
  A DNF cube may be empty (two contradictory literals) or lower-dimensional (an
  equality-like conjunction such as `x ≤ 0 ∧ −x ≤ 0`), and then no positive-radius
  ball exists and `γ̂ = 0`. `hint` is exactly the condition under which `alg:prec`'s
  LP is feasible. See "The three negative results" below.

### `hcoeff` → run on the cleaned formula

`hcoeff` said *no facet of the DNF has a zero normal vector*; it is needed because
the KV97 rounding argument divides by `‖A_ij‖`. A zero normal is not a constraint at
all: with a nonnegative bound the half-space is `Set.univ`
([`Ttc.atomSet_eq_univ_of_coeff_zero`](Ttc/Exec/Cleanup.lean)) and the literal can be
deleted; with a negative bound it is `∅`
([`Ttc.atomSet_eq_empty_of_coeff_zero`](Ttc/Exec/Cleanup.lean)) and the whole cube
can be dropped. [`Ttc.cleanDNF`](Ttc/Model/Pseudocode.lean) does both, and
[`Ttc.coeff_ne_zero_cleanDNF`](Ttc/Exec/Cleanup.lean) holds **with no hypothesis at
all**.

> **This round is benign, and it is the only one of the three that is.**
> [`Ttc.sol_cleanForm`](Ttc/Exec/Cleanup.lean) is an equality of **sets** —
> `sol (atomSet atoms) (cleanForm atoms φ) = sol (atomSet atoms) φ` — so
> [`Ttc.volSol_cleanForm`](Ttc/Exec/CleanInput.lean) is an equality of volumes, the
> accuracy conclusion is stated about the **original** `volSol (atomSet atoms) φ`, and
> **no post-processing of the estimate is needed**. Only the *description* handed to
> the algorithm — the list of polytopes — changes. Contrast the dilation, where
> `Sol(F)` genuinely moves to `c · Sol(F)` and the estimate is divided by `cⁿ`.

One thing had to move with the DNF: `Ttc.IsDNFOf` quantifies over **all** Boolean
assignments, not only those induced by a point, and
[`Ttc.not_isDNFOf_cleanDNF`](Ttc/Exec/Cleanup.lean) is the machine-checked refutation
of the naive "clean the DNF in place" version. So the *formula* is rebuilt from the
cleaned cubes, `Ttc.cleanForm = dnfForm ∘ cleanDNF ∘ toDNFd`
([`Ttc.toDNF_dnfForm`](Ttc/Exec/Cleanup.lean) is what makes that round-trip work).
No hypothesis is added: the side condition `cleanDNF atoms (toDNFd φ) ≠ []` follows
from the headline's own `hint` via
[`Ttc.sol_nonempty_of_interior`](Ttc/Exec/CleanInput.lean) and
[`Ttc.cleanDNF_ne_nil_of_sol_nonempty`](Ttc/Exec/Cleanup.lean), and the three
transported obligations are
[`Ttc.isPositive_cleanForm`](Ttc/Exec/Cleanup.lean) (unconditional),
[`Ttc.cleanBdd`](Ttc/Exec/CleanInput.lean) and
[`Ttc.cleanInt`](Ttc/Exec/CleanInput.lean).

### The three negative results

These are the results that stop an auditor reading the residual hypotheses as
"conditions someone has not got round to removing yet".  They are stated about
`hint`, `hφ` and boundedness — the first because `hint` is what the *pruning* round
replaced by the weaker `hpos` (§1h), the other two because they are what remains
and what was derived.  All three are unaffected by the binder count moving.

**1. `hint` is not derivable.**
[`Ttc.hint_not_derivable`](Ttc/Exec/Degenerate.lean) exhibits
[`Ttc.degForm`](Ttc/Exec/Degenerate.lean) — `(x ≤ 0 ∧ −x ≤ 0) ∨ (x ≤ 1 ∧ −x ≤ 1)` in
dimension `1` — satisfying `hφ`, `hbdd`, `hcoeff` **and** `0 < Vol(F)`
([`Ttc.volSol_degForm_pos`](Ttc/Exec/Degenerate.lean), so the conclusion is not
vacuous for it) while `hint` fails. The obvious repair is blocked *in principle*, not
merely unattempted: dropping the degenerate cubes is invisible to the volume
([`Ttc.volume_biUnion_nondegenCubes`](Ttc/Exec/Degenerate.lean),
[`Ttc.volSol_eq_toReal_biUnion_nondegenCubes`](Ttc/Exec/Degenerate.lean)) but
provably destroys `Ttc.IsDNFOf`
([`Ttc.not_isDNFOf_nondegenCubes_degForm`](Ttc/Exec/Degenerate.lean)) — and
`lem:lattice` counts **lattice points**, which are themselves a null set, so an
almost-everywhere decomposition would give no control over the count. Nor can `hint`
be weakened to "some cube is full-dimensional": `Ttc.gammaOf` is an infimum, and
`ball_subset` is consumed per cube downstream because the walk runs inside *every*
cube.

**2. `hφ` and `hbdd` are independent — both ways.**
[`Ttc.Independence.exists_isBounded_not_isPositive`](Ttc/Findings/Independence.lean)
gives a formula with solution set `[−1, 1] ⊆ ℝ¹`, bounded, containing a genuine
negation (the third atom is there so the negated conjunct is not vacuous), so `hbdd`
does not imply `hφ`.
[`Ttc.Independence.exists_isPositive_not_isBounded`](Ttc/Findings/Independence.lean)
gives `Ttc.BForm.tt`, and
[`…exists_isPositive_not_isBounded_halfspace`](Ttc/Findings/Independence.lean) the
non-degenerate version — the single atom `x₀ ≤ 0`, whose solution set is a genuine
half-space (`≠ Set.univ`) and still unbounded — so `hφ` does not imply `hbdd`. One is
syntactic, the other semantic; **neither can be dropped in favour of the other**. The
file explicitly does *not* claim the pair is the weakest usable one.

**3. `hφ` is removable in principle, at a price that is stated.**
[`Ttc/Findings/OpenHalfspace.lean`](Ttc/Findings/OpenHalfspace.lean) is the costing,
and its verdict is *bounded refactor, two extra hypotheses, not research-scale*. The
volume cannot see the difference between a closed and an open half-space
([`Ttc.volume_halfspace_open_eq`](Ttc/Findings/OpenHalfspace.lean),
[`Ttc.volume_sol_openAtomSet_eq`](Ttc/Findings/OpenHalfspace.lean), the atom's normal
being nonzero is *necessary* there), and `Ttc.posify` turns an arbitrary cube into a
positive one with the volume preserved
([`Ttc.posify_isPositive`](Ttc/Findings/OpenHalfspace.lean),
[`Ttc.volume_sol_eq_iUnion_posify`](Ttc/Findings/OpenHalfspace.lean)). The three
prices, each machine-checked:

* the **lattice count** does see the difference —
  [`Ttc.exists_latticeCount_ne_of_open`](Ttc/Findings/OpenHalfspace.lean): `x ≤ 0 ∧
  −x ≤ 0` in `n = 1` is `{0}` closed and `∅` open, same volume `0`, count `1` against
  `0` at **every** precision. So the refactored run would enumerate the lattice points
  of the *closed relaxation*, a provably different set — a repricing, not bookkeeping;
* `hbdd` stops transferring
  ([`Ttc.exists_isBounded_region_not_isBounded_posify`](Ttc/Findings/OpenHalfspace.lean)):
  it would have to be assumed of the relaxation, which is strictly stronger;
* `toDNFd φ ≠ []` stops being free — `Ttc.BForm` has no `false` constructor, and
  positivity is currently what makes the DNF nonempty, so a binder appears.

Nothing in that file removes `hφ`, and **nothing in it is imported by the capstone**.

### Non-vacuity at eleven binders

> ⚠ 2026-08-12: this witnesses `Ttc.ttc_volume_estimate_parametric`. The **eleven**
> binders of `Ttc.ttc_volume_estimate` are exactly this list — that statement's two extra
> binders were `cVol cSample`, which it no longer has — so the same two-cube data meets
> them. See `Ttc.TwoCube.ttc_volume_estimate_two_cube_fixed` (below), added so the
> fixed-price headline has a witness of its own rather than one by instantiation-in-prose.

[`Ttc.TwoCube.ttc_volume_estimate_two_cube_full`](Ttc/Witness/FullTwoCube.lean) applies
**this** statement to the two-cube instance at every `n ≥ 1` and every
`(ε, δ) ∈ (0,1]²`, and
[`…_full_at`](Ttc/Witness/FullTwoCube.lean) pins `(1/3, 9/10)` and `(1/2, 1/4)` with
the bounds `1/10` and `3/4` proved strictly positive inside the statement. `hpos`
holds by [`Ttc.TwoCube.twoVolPos`](Ttc/Witness/FullTwoCube.lean), one application of
`Ttc.volSol_pos_of_interior` to full-dimensionality — and *that* holds because each
region contains an open ball of positive radius, a few lines from
`Ttc.TwoCube.ball_subset_two_d` and `Ttc.TwoCube.gamT_pos`, no box geometry
([`Ttc.TwoCube.interior_region_nonempty_two_d`](Ttc/Witness/FullTwoCube.lean)). The
former binders `hcoeff`, `hint` and `hbdd` are **not passed at all** any more; the
first two were discharged upstream by the cleanup and the pruning, and the third is
derived (§1h).

**The earlier two-cube theorems — including those in
[`Ttc/Witness/Headline.lean`](Ttc/Witness/Headline.lean) — witness
`Ttc.ttc_volume_inputs`, not this statement.** The run here is on the *dilated* body
of the *cleaned* formula under the *constructed* ball
([`Ttc.TwoCube.twoProbFull`](Ttc/Witness/FullTwoCube.lean)), and it is **not**
`Ttc.TwoCube.twoAccD`, the undilated run on the raw formula under the supplied ball.
They are different runs with different probabilities; no equality between the two
numbers is claimed, and none should be read into the shared names.

---

## 1h. What lies beyond `Model/`: the definitional closure, the preprocessing, and the hypotheses

This section is the prose that [`Ttc/Model/Theorem.lean`](Ttc/Model/Theorem.lean)
deliberately does not carry, so that that file stays the statement.  Read the two
together.  Four things belong here and not there, and an auditor needs all four:
the **definitional closure**, the **three preprocessing steps** the headline
certifies `alg:ttc` *plus*, the **two residual hypotheses** `hφ` and `hpos`, and the
fact that **`hbdd` was derived** rather than dropped.

### The boundary, and how to re-check it

The target layout is four files: the algorithm — `alg:ttc`, the preprocessing, the
converter, the inscribed-ball construction, the dilation factor and the parameter
block — in [`Model/Pseudocode`](Ttc/Model/Pseudocode.lean); the theorem, and
nothing else, in [`Model/Theorem`](Ttc/Model/Theorem.lean).

**What the theorem's type names outside `Model/` is now nothing**, and that is
machine-checked: `#modelClosureOfType Ttc.ttc_volume_estimate` is live in
[`Ttc/Audit/ClosureCheck.lean`](Ttc/Audit/ClosureCheck.lean) and fails `lake build`
on drift.  §5's boundary probe re-runs the same question by hand; run it after any
move between `Model/` and `Exec/`.

**Read that as a move, not a disappearance — this is the whole content of the
section.**  The two things that used to be outside are still named by the
statement; they were relocated *into* `Model/Prelude`, and with them the
constructed sampler's law, the canonicalisation data and the Poisson/thinning
kernels.  So `Model/` now imports the probability and convex-geometry development
it is the front of (four `Arlib.*` modules), which is the price that was paid.  It
is the opposite trade from the reference layout, where nfalean's
`ApproxNFA/Model/Theorem.lean` names `(countNFAExec A n ε δ).P.Pr` and lets
`countNFAExec` sit outside its `Model/`.  An auditor should know which trade is in
force before deciding what "read `Model/` and stop" buys.

### Definitional closure — what the `Model/` names unfold to

The statement names quantities; their **bodies are not self-contained**, and this
is the enumeration of what the statement's *meaning* depends on.  Since the moves
above, every one of these is defined inside the audit surface `Model/` ∪
`Ttc/Probability/` — so the list is no longer a list of things beyond the boundary,
but of things **inside** it that a reader of the surface must actually read rather
than skim:

* **The run wrappers** the quantities are built from — the count of enumerated
  lattice points, the rate vector `Ttc.algRates`, the run's output `Ttc.ttcRun`,
  the oracle bundle `Ttc.algOracles`, the precision and the dilation, together with
  the charging model `Ttc.stepCost`/`Ttc.runCost` (all `Model/Pseudocode`).
* **The constructed oracle bundle** — the covered-lattice bundle over `Ttc.mcVol`,
  which is the volume oracle
  [`Ttc.VolumeAlgorithm.monteCarlo`](Ttc/Volume/MonteCarlo.lean)'s estimator.  So
  `Vol_ED` is a *constructed* Monte-Carlo estimator, not an assumed one.
* **The constructed sampler** — `Ttc.e2eSampD`, `Ttc.kv97ContLaw`, `Ttc.mixSteps`
  and the canonicalisation data
  `Ttc.canonRfac`/`Ttc.canonAm`/`Ttc.canonBv`/`Ttc.canonDm` (all `Model/Prelude`),
  which stand for the KV97 / ball-walk development in `Arlib` that they are built
  from.  **That development is the trusted base beyond `Model/` now**, reached
  through `Model/Prelude`'s `Arlib` imports rather than through a `Ttc` constant.
* **The run's probability space** — `Ttc.trajLaw` for the sample coins and
  `Ttc.MonteCarlo.coins` for the volume coins (`Model/Prelude`).

What is **not** in the closure is every proof: `Exec/Prune`, `Exec/BddFromPos`,
`Exec/Final` and the whole probabilistic development are consumed only by
`Ttc.ttc_volume_api`'s proof, not by the statement.  Nor is any `Exec/Api`
wrapper: `Ttc.ttcInput`, `Ttc.ttcEstimate`, `Ttc.ttcCost` and their siblings —
which earlier revisions of this section listed as the closure — are the vocabulary
the `Exec/` capstones are stated in, and the headline no longer routes through
them.

### The `Exec/Api` wrapper vocabulary, in detail

**These are no longer names in the headline's type**, which now reads through
`Ttc.ttc` and `Model/Pseudocode`'s own vocabulary; they are what the `Exec/`
capstones of §1b–§1d are stated in, and what `Ttc.ttc_volume_api` — the theorem
`Model/Theorem`'s proof applies — concludes about.  The list stays because an
auditor moving between §1b–§1d and §1e needs both vocabularies, and because the
`rfl` bridges below are what stop the two from being two models.

Each is a pure abbreviation carrying an identifying `rfl` lemma
(`Ttc.ttcEstimate_def` and friends) — nothing is asserted by naming, which is the
`def`-that-stands-in-for-a-proof hazard of §4 being closed by construction.

* **`Ttc.ttcInput`** — the formula `TTC` is actually run on: the user's `φ` with its
  degenerate cubes pruned and its zero-normal atoms cleaned.
  `Ttc.ttcInput_eq_preprocess` pins it, by `rfl`, to `Model/Pseudocode`'s own
  [`Ttc.preprocess`](Ttc/Model/Pseudocode.lean).
* **`Ttc.ttcScale`** — the dilation the run applies to its input; the headline
  divides the run's output by `ttcScale ^ n`, which is exactly the preprocessing's
  dilation lines taken back out.
* **`Ttc.ttcBlock`**, **`Ttc.ttcPrec`** — the parameter block `alg:ttc` computes
  (lines 17–20) and `GetPrecision`'s output `ρ`, both at the preprocessed formula.
* **`Ttc.ttcIndex`** — `|Sol(F) ∩ 𝕃ⁿ|` at the computed precision, i.e. the index the
  run's sample coins range over, so a sample trajectory has type
  `ℕ → Fin (ttcIndex …) → ℕ`.
* **`Ttc.ttcOracleBundle`** — the oracle bundle `alg:ttc` reads on the run `(c, t)`:
  the constructed Monte-Carlo `Vol_ED` at the volume coins, the covered-lattice
  sampler at the sample coins.  **A closed term, not a hypothesis.**
* **`Ttc.ttcRates`** — the level-`0` rate vector `θ` (`alg:ttc` line 20) at the volume
  coins `c`: the sampler's mass at each enumerated lattice point times that point's
  cube's volume estimate. `Ttc.trajLaw` of it is the law the sample coins are drawn from.
* **`Ttc.ttcEstimate`** — what `TTC(F, ε, δ)` returns on the run `(c, t)`, brought back
  to the original scale: the run's output at the dilated input, divided by
  `ttcScaleⁿ`. **The division is part of the measured quantity** — the run is performed
  on the dilated body `c · Sol(F)`, whose volume is `cⁿ · Vol(Sol F)`, so this, and not
  the raw output, is what the accuracy conjunct compares with `Ttc.volSol` of the
  original body.
* **`Ttc.ttcThresh`** — the sample threshold `Thresh` of the computed parameter block,
  the quantity the cost bound is linear in.
* **`Ttc.ttcTerminates`** — the run's absorption loop exits at every cube
  (`Ttc.Terminates` at the computed parameter block, the run's own oracles and the
  preprocessed formula's cube list). **This is the hypothesis `thm:runtime` needs and
  the paper leaves unstated.**
* **`Ttc.ttcCost`** — the charged cost of the run `(c, t)`: `Ttc.runCost` at the computed
  parameter block, the run's oracles, the per-call costs `cVol`/`cSample` and the
  computed precision, folded over the preprocessed formula's cube list.
* **`Ttc.ttcNumCubes`** — `m`, the length of the preprocessed formula's DNF. The cost
  bound is `m · (C_vol + C_sample · Thresh)`.

`Ttc.ttcEstimate_eq_ttcOutput` pins the measured quantity, by `rfl`, to
[`Ttc.ttcOutput`](Ttc/TtcProb.lean) divided by
`ttcScaleⁿ` — the two bridges back to the transcription are that lemma and
`Ttc.ttcInput_eq_preprocess`, and they are what stop the wrapper vocabulary from
being a second model.  (`Ttc.ttcOutput` is the oracle-indexed random variable
`run P (O ω) ρ (toDNF φ)`; its binders `Ω`, `O`, `toDNF` are `Ttc.TtcProb` fields of
the same names, which is why it lives in `Ttc/TtcProb.lean` and not in `Model/`.
Neither `Ttc.ttcAlgOutput` nor `Ttc.ttcRun` unfolds to it.)

### What is certified is `alg:ttc` plus three preprocessing steps

Read this before quoting the statement.  Two of the three change what the algorithm
*does*; only one is cosmetic.

* **A dilation** (`Exec/Rescaled`).  `alg:ttc` sets `p ← 1` and only halves it, so its
  sketch is `Poisson(Λ)` with `Λ ≤ Vol(Sol F)`; on a body of volume `10⁻⁶` it draws
  `Pois(10⁻⁶)` points and returns `0`.  **The printed algorithm is wrong there**, not
  merely unproved (`Ttc.Box.big_not_derivable`, README finding 20).  So the input is
  dilated by `Ttc.runScale` and the estimate divided by `cⁿ`.
* **A pruning** ([`Exec/Prune`](Ttc/Exec/Prune.lean)).  Degenerate
  (lower-dimensional) cubes are dropped.  This changes `Sol(F)` by a null set:
  `Ttc.sol_pruneForm_subset` is a genuine `⊆` and **deliberately not an equality**
  — the file's own docstring says so, and says that is why it proves a `Ttc.volSol`
  equality (`Ttc.volSol_pruneForm`) instead of a `Ttc.sol` one.  The step is sound
  *only* because the conclusion merely measures `sol`.  (No lemma in the tree
  exhibits an input where the inclusion is *strict*; on `Ttc.degForm` in particular
  it is not, since the pruned cube `{0}` sits inside the surviving `[−1, 1]`.  An
  earlier revision of this page claimed strictness there and was wrong.)
* **A cleanup** ([`Exec/Cleanup`](Ttc/Exec/Cleanup.lean)).  Zero-normal atoms are
  constant-folded.  Benign, and the only one of the three that is:
  `Ttc.sol_cleanForm` is an **exact set equality**.

The inscribed ball is *constructed* (`Ttc.autoCen`, `Ttc.autoGamma`), but it is **not**
`alg:prec` line 86's LP — it is *some* inscribed ball, and non-maximality only inflates
`ρ = ⌈log₁₀(γ/γ̂)⌉`, so the guarantee is unaffected and only the precision is looser.

### The two residual hypotheses

* `hφ : φ.IsPositive` — negation-free.  Independent of boundedness in **both**
  directions ([`Ttc.Independence.exists_isBounded_not_isPositive`](Ttc/Findings/Independence.lean),
  [`Ttc.Independence.exists_isPositive_not_isBounded`](Ttc/Findings/Independence.lean)),
  so neither could ever replace the other.  Removable in principle at a price that
  is itself machine-checked — see
  [`Findings/OpenHalfspace.lean`](Ttc/Findings/OpenHalfspace.lean), and §1g's third
  negative result for the three items of that price.  Nothing in that file removes
  `hφ`, and nothing in it is imported by the capstone.
* `hpos : 0 < volSol (atomSet atoms) φ` — the solution set has positive volume.
  Strictly weaker than the per-cube full-dimensionality `hint` it replaced:
  [`Ttc.volSol_pos_of_interior`](Ttc/Exec/Prune.lean) proves that implication, and
  [`Ttc.hint_not_derivable`](Ttc/Exec/Degenerate.lean) refutes the converse.

Those are the only two.  §1g's **three negative results** are what stop a reader
treating them, and the removed `hint`, as hypotheses nobody has got round to
deleting: `hint` is proved not derivable and the obvious repair is proved blocked;
`hφ` and boundedness are proved independent in both directions; and the cost of
removing `hφ` is costed rather than guessed.

### `hbdd` is gone — **derived**, not dropped

The statement used to carry a further binder,
`hbdd : Bornology.IsBounded (sol (atomSet atoms) φ)`.  What the chain actually needs is
boundedness of `Sol` of the **pruned** formula, and
[`Ttc.isBounded_sol_pruneForm_of_volSol_pos`](Ttc/Exec/BddFromPos.lean) proves exactly
that from `hφ` and `hpos` alone: `hpos` bounds the volume of `Sol(F)` away from `⊤`, every
surviving cube's region is convex with a nonempty interior *by construction*, and a
convex set with an interior point and finite volume is bounded
(`Ttc.isBounded_of_convex_of_interior_of_volume_ne_top` — the step Mathlib does not
have).  The pruned `Sol` is the finite union of those regions.

That derivation became possible **only after the pruning round**.  Before it a cube of
the DNF can be a *line*: convex, unbounded, and of volume `0` — so it contributes
nothing to `Vol(F)` and `hpos` was perfectly consistent with an unbounded `Sol(F)`.
`Ttc.hint_not_derivable` (`Exec/Degenerate`) is the machine-checked witness that
`hpos` does not imply per-cube full-dimensionality, which is exactly the gap.
Pruning deletes those cubes, `Ttc.interior_nonempty_pruneForm` supplies the interior
point, and only then does "positive volume" imply "bounded".  Nothing here claims
`0 < Vol(F) → IsBounded (sol (atomSet atoms) φ)` at the **unpruned** formula; that
implication is false, and it is not needed.

Non-vacuity: `Ttc.TwoCube.ttc_volume_estimate_two_cube_full` (`Witness/FullTwoCube.lean`).
The audit is `AUDIT.md` §1e–§1g.

`sorry`-free, axioms `[propext, Classical.choice, Quot.sound]`.

### 1h-i. Four deviations from `algo.tex`

These are the places where the Lean transcription in
[`Model/Pseudocode`](Ttc/Model/Pseudocode.lean) does not say quite what the paper
says.  They used to be recorded in that file's module docstring; they are here
because they are audit commentary about the modelling, not a description of what the
file defines.

**(a) The `while` loops are exit levels, not iterations.**  Neither loop is written as
a recursion.  `Ttc.haltLevel` and `Ttc.absorbLevel` are the **least level at or above
the current one at which the loop's guard fails**, an `sInf` over `ℕ`, and the step
jumps straight there.  This is what the loops compute when they terminate, and it
needs no termination proof — which matters, because the second loop has none to give:
it exits when repeated thinning brings `Nᵢ + |𝒳|` under `Thresh`, which happens only
with high probability.  A fuelled recursion would have been the alternative, and it
forces an iteration budget into the statement of the main theorem; this does not.

**(b) An empty exit set exits immediately.**  When no level satisfies the exit
condition — the run where the algorithm loops forever — the set that
`Ttc.absorbLevel` takes an `sInf` over is empty, `Nat.sInf` returns `0` by convention,
and the `max` with the entry level degenerates to "stay put".  Nothing depends on this
corner: every consequence drawn from an exit level is of the form "every level
strictly below it had the guard true" (`Ttc.lt_haltLevel`, `Ttc.lt_absorbLevel`,
`Invariants`), which is vacuously true when the loop does not move.

**(c) The thinning is a read-off at a level, not a repeated coin.**
`Ttc.Oracles.thin j₀ j' X` is the sub-multiset of `X` that survives down to level
`j'`, having entered the step at level `j₀` — one call, not `j' − j₀` of them.  This is
what lets the loops be exit levels: the guard at a candidate level `j'` can be
evaluated without running the loop to get there.  The only law assumed of it is
`Ttc.Oracles.thin_le`: thinning **removes** copies, never invents them.  Note that
`thin j₀ j₀` is a no-op on the states the run reaches, but is not assumed to be the
identity outright — the concrete family in `Coupling/Family` realises it as a cap
against the level-`j₀` counts, which is the identity exactly there.

**(d) The randomised calls are told the cube and the level.**  `pois` takes `(i, j)`
and `gen` takes `(i, j)`, where `algo.tex:38,41,43` pass neither.  The index is what
names the draw: two calls with different `(i, j)` are different draws, which is what a
distributional hypothesis needs in order to speak of independence.  The level in
particular is needed because `lem:numlattice`'s `Err(j)` must be an event about a
level-`j` process coupled to the run, and a level-blind sampler cannot realise that
coupling — see README finding 15.

### 1h-ii. Which of the four preprocessing steps are in the paper

`Ttc.ttc_volume_estimate` does not measure a run of `alg:ttc` on the user's `F`.  It
measures a run on an input that four steps have already rewritten, with the returned
estimate divided by `qⁿ`.  `Model/Pseudocode` transcribes those four steps as lines
A1–A13, in the same style as `alg:ttc` itself.  §1h above lists three of them from the
`Exec/` side; this is the same list read off the transcription, with the fourth
(cleaning) added.

**Steps 1, 3 and 4 are not in the paper's `alg:ttc`.**  Step 2 is not printed there
either, but unlike the other three it is not a change to the algorithm: it rewrites the
input syntax and leaves the body alone.

* **Step 1, the pruning (A2–A3), is not in `alg:ttc`.**  It changes `Sol(F)` — by a
  **null set only**: the deleted cubes have convex regions with empty interior, so
  `Ttc.sol_pruneForm_subset` is a genuine `⊆` and may in general be *strict* (an
  isolated lower-dimensional piece sitting beside the surviving union is dropped),
  while the **measure** is preserved exactly (`Ttc.volSol_pruneForm`).  The soundness
  of the substitution rests on that volume equality, not on any claim about the set,
  and it is legitimate solely because the headline's conclusion merely **measures**
  `Ttc.sol`.  (`Ttc.degForm` is *not* an example of the strictness — its `thinCube`
  region is the point `0` inside `fatCube`'s `[−1,1]`, so pruning leaves `Sol`
  unchanged there.  It is the witness for something else: that pruning destroys
  `Ttc.IsDNFOf`, `Ttc.not_isDNFOf_nondegenCubes_degForm`, because `IsDNFOf` is a
  statement about Boolean valuations rather than about the solution set.)
* **Step 2, the cleaning (A4–A6), does not change what the algorithm does.**
  `Ttc.sol_cleanForm` is an **exact set equality**: a literal `0·x ≤ b` with `0 ≤ b`
  denotes `Set.univ` and a cube containing one with `b < 0` denotes `∅`, so deleting
  them is constant folding.  Not printed in `alg:ttc`, but nothing is lost or gained.
* **Step 3, the ball construction (A7–A9), is not `alg:ttc`.**  `alg:prec` line 86
  computes the *maximum* inscribed ball by an LP; `Ttc.ballData` picks *some* inscribed
  ball, classically.  Non-maximality only inflates the precision `ρ = ⌈log₁₀(γ/γ̂)⌉`, so
  the guarantee is untouched and only the run gets more expensive.
* **Step 4, the dilation (A10–A13), is not in `alg:ttc` and changes what the algorithm
  does.**  `alg:ttc` sets `p ← 1` and only ever halves it, so its sketch is
  `Poisson(Λ)` with `Λ ≤ Vol(Sol F)`; on a body of volume `10⁻⁶` it draws `Pois(10⁻⁶)`
  points and returns `0`.  **The printed algorithm is wrong there**
  (`Ttc.Box.big_not_derivable`, README finding 20).  So the input is dilated by
  `q = Ttc.scaleFactor` and the estimate divided by `qⁿ` — exact, because volume is
  homogeneous of degree `n` (`Ttc.volSol_scaleAtoms`).

### 1h-iii. The transcription is complete, and three `rfl`s say so

Every line of `Model/Pseudocode`'s A1–A13 table is a definition of *that* file, with
no exception — `Ttc.toDNFd`, the line-16 converter, included.  In particular
`Ttc.atomSet`, `Ttc.nondegenCubes` and `Ttc.pruneForm` — which used to sit in
`Exec/Inputs`, `Exec/Degenerate` and `Exec/Prune` — are there, and so is their
composite with the cleaning pass, `Ttc.preprocess`.  Every *theorem* about them stays
in `Exec/`; only the definitions moved.

That the headline really measures these definitions is machine-checked.  Its accuracy
conjunct is stated about `Ttc.ttcRun` *directly*, so no bridge is needed to see what
is measured; three `rfl` lemmas in `Exec/Api` connect that term to the run's own
vocabulary:

* `Ttc.ttcRun_eq_ttcAlgOutput` — `Ttc.ttcRun` **is** `Ttc.ttcAlgOutput` at the
  constructed oracle bundle `Ttc.ttcOracleBundle`.  This is the lemma that makes
  `Ttc.ttcRun` the algorithm rather than a rename of it.
* `Ttc.ttcRun_eq_ttcEstimate` — and it **is** the run's estimate.  That is lines
  A12–A13 at the bundle the development builds.
* `Ttc.ttcInput_eq_preprocess` — the formula that run is on is `Ttc.preprocess atoms
  φ`.  That is lines A2–A6.

So a reader who reads `Model/Prelude`, `Model/ProblemSetting`, `Model/Pseudocode` and
`Model/Theorem`, and stops, has read the algorithm that is certified *and* the input it
is certified on.  Nothing in the algorithm's statement is left in `Exec/`.

**What this does not make true.**  The transcription being complete is a claim about
*where the definitions live*, not a claim that the transcribed algorithm is the
paper's.  The four honesty notes of §1h-ii stand unchanged.

### 1h-iv. Why `Model/Pseudocode` carries proofs at all

`Model/Pseudocode` is not proof-free, and a reader who expects a pure transcription
should know why.

**The criterion, which is what to check — not the count, which keeps moving.**  A
theorem belongs in this file exactly when something the file *defines* cannot be
written down without it.  Everything failing that test has been evicted — to
`Exec/Params`, `Exec/Dedup`, and `Ttc/ModelSupport.lean` for the facts that are
carrier-generic bookkeeping with nothing of `alg:ttc` in their statements.  The
residue has come down from 27 declarations to a single figure and was still
falling while this was written; **count it with
`grep -cE '^(private )?theorem ' Ttc/Model/Pseudocode.lean`** rather than quoting
this page.  At the last measurement it was **4 theorems and no instance**, in the
two groups below.

The reason they cannot simply be moved out is worth stating, because the obvious
reason is the wrong one.  `closureAux` never walks a **theorem's** value
(`ConstantInfo.value?` is `none` for theorems in Lean 4.32), and `Ttc.algOracles`'
two proof fields are lifted into anonymous `Ttc.algOracles._proof_1/_2`, which are
themselves theorems — so three of the four are invisible to `#modelClosure` while still
being required for the file to *elaborate*.  **But a theorem a `def`'s body names is
not invisible**, and one of them is exactly that: `Ttc.latticeEnum` is
`Classical.choose` of `Ttc.exists_latticeEnum`, so that theorem is in every closure
report and must stay inside the audit surface outright.  (`Ttc.exists_cubeOf` is in
the same position and escapes only by being `private`, since a private name begins
`_private` rather than `Ttc`; measured, un-`private`ing it would take
`#modelClosure Ttc.ttc` from 199 to 200 and the statement closure from 206 to 207.)
For the other three the binding constraint is not the audit at
all but their **statements** — see below.  Pushing one downstream produces an
elaboration error; pulling one upstream produces a type error.

1. **What the run's own oracle bundle cannot be built without** (2).  This group is
   the price of `#modelClosure Ttc.ttcRun` passing.  `Ttc.algOracles` constructs an
   `Ttc.Oracles`, and that structure has two **proof** fields, so the two discharges
   `Ttc.trajThin_le` and `Ttc.card_trajGen` are literally part of the term — those
   two now sit in [`Ttc/Probability/Trajectory.lean`](Ttc/Probability/Trajectory.lean)
   with the five trajectory read-offs they are about, which is inside the audit
   surface just as `Model/` is.  What could not follow them is
   `Ttc.latticeEnum_injective`, the argument `thin_le` is applied to, whose statement
   names `Ttc.latticeEnum`; and `Ttc.latticeEnum` is itself `Classical.choose`n from
   `Ttc.exists_latticeEnum`, so that theorem is part of the definition — and is the
   one theorem here that *is* visible to `#modelClosure`, because a `def` body names
   it.
2. **What line 20's rate vector cannot be built without** (2).  `Ttc.cubeOf` is
   `Classical.choose`n from the private `Ttc.exists_cubeOf`, and `Ttc.cubeOf_spec` is
   that choice's `choose_spec`; `Ttc.rates` reads both through `Ttc.cubeAt`.

**What keeps the residue here is the theorems' own statements**: each mentions a
definition that is itself in the measured closure, so moving the theorem means moving
the definition — which is exactly how the two multiset/cardinality contracts left.
They were bookkeeping about a trajectory rather than about `alg:ttc`, so the five
read-offs they mention could honestly be re-filed beside the trajectory law and the
contracts could travel with them.  `Ttc.latticeEnum` and `Ttc.cubeOf` have no such
home: one enumerates lattice points of a region, the other looks up which cube
contains a point, and neither is probability.  The facts whose statements survived
being rephrased without that vocabulary — the count-vector dictionary
(`Ttc.count_toMultiset` and friends) and the `Set.ncard` enumeration lemma — went to
[`Ttc/ModelSupport.lean`](Ttc/ModelSupport.lean), which `Model/Pseudocode` imports;
read that file's docstring for what the import costs.  The two guarded membership
properties of the enumeration (`Ttc.latticeEnum_mem`, `Ttc.latticeEnum_onto`) and
`Ttc.card_toMultiset` were never in this group and are correspondingly **not** in
`Model/`: they live in `Exec/Endgoal` and `Coupling/Family`.

---

## 2. What is assumed? Read the fields of `TtcProb`

Every global hypothesis is a field of
[`Ttc.TtcProb`](Ttc/TtcProb.lean). There are no others: the theorem
quantifies over the structure and adds nothing — no side hypothesis, no
`variable`, no instance argument carrying content.

> **Read this table as the assumptions of `volume_estimate` and `ttc_volume`, not
> of the strongest result.** Eleven of the things below —
> `volAlg`, `volCoins`, `volED_eq`, `volCoins_good`, `vol`, `vol_pos`, `θ`,
> `theta_eq`, `gen_mem`, `sampD`, `sampler` (and hence `sampler`'s own `law_tv`) —
> are **constructed** on the `Ttc.ttc_volume_endToEnd` route of §1c and appear in
> no binder of it. What survives there is the "assumed of the input" rows, plus a
> linear description of the dilated regions and the regime condition `big` — and on
> the `Ttc.ttc_volume_final` route of §1d **the linear description is gone too**, so
> what survives is the "assumed of the input" rows, `hlen` and `big`. Where a
> row below says "assumed of the external algorithm" or "assumed of the sampler",
> check §1c and §1d before quoting it as a residual assumption of the development.

**`Ttc.TtcProb` has 59 fields.** That number, and the field list below, were read
out of the compiled environment with `Lean.getStructureFields`, not by grepping
the file. That distinction has bitten this project before: `Ttc/TtcProb.lean`'s
docstrings quote field-shaped Lean at two-space indentation, so a `grep` for
`^  name :` reports fields that are *prose about theorems* — `samp_unif`,
`theta_lo`, `theta_hi` and `volED_hi` all appear that way and **none of them is a
field**. §5 has the dump command.

**No lemma of the paper is assumed outright any more, and no field asserts a
probability bound.** `lem:lattice` used to be two fields; it is now *proved*
([`Ttc.TtcProb.lattice_lo`](Ttc/Lattice/Assembled.lean),
[`lattice_hi`](Ttc/Lattice/Assembled.lean)) from the geometric fields below, which
are hypotheses about the **input**, not about the analysis. `lem:numlattice` used
to be one more field, then a weaker `numlattice_union` field asserting only the
epoch covering. **Both are now theorems**
([`Ttc.TtcProb.numlattice`](Ttc/Coupling/NumLattice.lean),
[`Ttc.TtcProb.numlattice_union`](Ttc/Coupling/Transfer.lean) — the latter carries
the deleted field's statement verbatim, so you can diff it against an older
checkout).

**Three more have become theorems since the last version of this page, and this
is the single biggest change on it.** `samp_unif`, `theta_lo` and `theta_hi` were
fields; all three are now proved:

* [`Ttc.TtcProb.samp_unif`](Ttc/Sampler/Bridge.lean) — `eq:almostuniform` itself,
  the two-sided pointwise bound
  `(1−ε')/|P(cᵢ) ∩ 𝕃ⁿ| ≤ sampD i x ≤ (1+ε')/|P(cᵢ) ∩ 𝕃ⁿ|`, with a statement
  byte-identical to the deleted field's.
* [`Ttc.TtcProb.theta_lo`](Ttc/Sampler/Bridge.lean),
  [`theta_hi`](Ttc/Sampler/Bridge.lean) — the paper's Invariant, per lattice
  point.

They are proved from the new field `sampler` (below) together with `theta_eq`.
**This is what put the Kannan–Vempala development on the headline's dependency
path**: §5's walk *from `Ttc.TtcProb.volume_estimate`* reaches 150 `Arlib.*`
declarations, 29 of them in `Arlib.KV97`, including `Arlib.KV97.theorem2` — and
the walk from `Ttc.ttc_volume_endToEnd` reaches 432 and 35. See
[`AUDIT-KV97.md`](AUDIT-KV97.md), whose §0 is about exactly this.

Be careful about what that buys **at the level of `TtcProb`**. The assumption did
not disappear there; it **moved**, from a bound on `θ` to a description of a
sampler (`sampler`, a `Ttc.KV97Sampler`), whose own quantitative field `law_tv`
is an assumption about a continuous draw. §4 and `AUDIT-KV97.md` §2 say so in
detail. What *is* a real gain even at this level is that the assumption is a
**named published theorem's hypothesis** rather than a hand-placed inequality.

> **This paragraph is about `TtcProb` and `ttc_volume` only.** One level up,
> `Ttc.ttc_volume_endToEnd` (§1c) binds no `sampler` at all: it supplies
> [`Ttc.e2eSampler`](Ttc/Exec/EndToEnd.lean), whose `law_tv` is a theorem. So
> "`law_tv` is the open oracle" — which earlier revisions of this page said
> flatly, and which was true when they said it — is now **false as a statement
> about the development**, and true only as a statement about the `KV97Sampler`
> interface read in isolation.

### The fields

Grouped as they appear in the structure. The order is the compiled order.

| Field(s) | What it asserts | Status |
| --- | --- | --- |
| `ε`, `δ`, `hε0`, `hε1`, `hδ0`, `hδ1` | `ε, δ ∈ (0,1]` | the theorem's own parameters |
| `atoms`, `M`, `M_eq` | each atom is a linear constraint `A x ≤ b`, and `M` interprets it as that half-space | **assumed of the input** — this is what "SMT(LRA)" means |
| `φ`, `toDNF` | the Boolean abstraction of `F` (line 15), and the circuit-AllSAT procedure (line 16) | `φ` with `atoms` **is** the input formula; the DNF is *computed* from it, not a second input |
| `isDNF` | `toDNF φ` and `φ` agree on every Boolean assignment | **assumed** of the external `ToDNF`/AllSAT tool — the one thing line 16 is trusted for. `thm:decomposition` is *proved* from it |
| `isPositive` | no literal of `D` is negated | **assumed of the input** — see §4 and README finding 5 |
| `Ω`, `mΩ`, `μ`, `isProb` | a probability space for the algorithm's randomness | structure, not an assumption |
| `P`, `eps_eq`, `delta_eq`, `dim_eq` | the parameter block, run at the theorem's own `ε` and `δ` and in the ambient dimension | inputs + three ties that used to be missing |
| `cubes_le`, `facets_le` | `m` bounds the number of cubes, `r` the number of facets | **assumed of the input**; the paper's `m`, `r` |
| `normal_ne_zero` | every facet's normal vector is nonzero | **assumed of the input**; a zero normal is not a facet |
| `O` | the `ω`-indexed oracle bundle | input; pinned by `oracle_eq` below |
| `cen`, `gammaHat`, `hgammaHat`, `ball_subset` | each `P(cᵢ)` contains an `ℓ₂`-ball of radius `γ̂ > 0` about its own centre | **assumed of the input** — `lem:nonconv`'s own hypothesis, in the paper's words. The LP of `alg:prec` that computes `γ̂` is **not modelled** |
| `volume_ne_top` | each `P(cᵢ)` has finite volume | **assumed of the input** — the paper leaves it implicit |
| `ρ`, `rho_eq` | the precision is `GetPrecision`'s output, `ρ = ⌈log₁₀(γ/γ̂)⌉` | `alg:prec` line 91, transcribed — and **load-bearing**, see §4 |
| `gen_mem` | `GenerateSamples` returns points of `P(cᵢ) ∩ 𝕃ⁿ` | **assumed of the external sampler** — `Ttc.Oracles` fixes only *how many* it returns. Not distributional |
| `L`, `L_eq` | `L` **is** `\|Sol(F) ∩ 𝕃ⁿ\|/10^(ρn)` ([`Ttc.normalisedCount`](Ttc/Lattice/Decomposition.lean)) | definition, not an assumption |
| **— from here the fields describe the sampler —** | | |
| `Lidx`, `ptE`, `ptE_inj`, `ptE_mem`, `ptE_onto` | the lattice points the coupled family is indexed by, and a *bijective* enumeration of them onto `Sol(F) ∩ 𝕃ⁿ` | **assumed of the sampler** — structure of the model. `ptE_mem`/`ptE_onto` are what make `Lidx` the paper's `N` and not an arbitrary index |
| `θ` | each point's level-`0` Poisson rate | input; pinned by `theta_eq` |
| `vol` | the rate the run draws each cube with | input; pinned by `volED_eq` |
| `sampD` | the sampler's per-cube discrete law on `P(cᵢ) ∩ 𝕃ⁿ` | input; pinned by `sampler`'s `sampD_eq` |
| **`sampler`** | **a [`Ttc.KV97Sampler`](Ttc/Sampler/Interface.lean) at this `M`, `toDNF φ`, `ρ`, `ε'`, `sampD`** | **assumed of the sampler — the strongest field on this page, jointly with `law_eq`.** Its 15 fields are tabulated below |
| **`theta_eq`** | `∀ s, ∃ i ∈ D, ptE s ∈ region M i ∧ θ s = sampD i (ptE s) * vol i` — each point's rate is *its cube's* volume estimate times the sampler's mass at it | **assumed** — this is the join between the geometry and the probability. It replaced the two free inequalities `theta_lo`/`theta_hi`, which are now derived from it |
| `cover`, `memPt`, `memPt_eq`, `cover_eq` | the coverage test and cube membership on the enumerated points, and that the two agree | **assumed** — combinatorial, checkable of an instance |
| `toTraj`, `toTraj_meas` | each `ω` reads as a trajectory `ℕ → Fin Lidx → ℕ`, measurably | structure |
| **`law_eq`** | **`μ.map toTraj = trajLaw θ`** — the randomness **is** the coupled level family (`Ttc.trajLaw`) | **assumed of the sampler.** Not "the draws are Poisson"; "the draws are *this construction*" |
| **`oracle_eq`** | **`O ω = trajOracles ptE_inj vol cover memPt (toTraj ω)`** — the oracles answer by reading that trajectory | **assumed of the sampler**; pins `O` completely |
| **`volAlg`** | **`Vol_ED` is Cousins–Vempala Theorem 1.1** ([`Ttc.VolumeAlgorithm`](Ttc/Volume/Oracle.lean), `vol3_journal.tex:144`) | **assumed of the external algorithm — and this is the whole of what is assumed about it.** A named published theorem, checkable against the paper line by line. **Not proved.** See §3 and [`CV-ROADMAP.md`](CV-ROADMAP.md) |
| `volCoins`, **`volED_eq`** | the coins the `m` calls consumed, and **`vol i = γ̂ⁿ · volAlg.est (roundBody …) ε' δ' volCoins`** — the run's estimates *are* Theorem 1.1's output on the normalised polytope | **transcription of `alg:ttc` line 24.** This is what stops `vol` being a free function of the right shape. The `γ̂ⁿ` rescaling is the rounding bridge [`Ttc.VolumeAlgorithm.of_ball`](Ttc/Volume/Bridge.lean), which is **proved** |
| **`volCoins_good`** | **`vol i ∈ (1±ε')·Vol(P(cᵢ))`** for every cube — the `m` calls all succeeded | **assumed, but with its probability proved.** It replaced the former deterministic field `volED_hi` (which asserted the bound at *every* sample point, i.e. that `Vol_ED` never fails). [`Ttc.TtcProb.volGood_prob_budget`](Ttc/Volume/Bridge.lean) shows it holds with probability `≥ 1 − δ/4`; [`Ttc.TtcProb.volCoins_mem_volEvent`](Ttc/Volume/Bridge.lean) shows it *is* that event and not something stronger. **Read README finding 13a for what this does and does not buy** |
| `vol_pos` | `0 < vol i` for every cube `i ∈ D` | **assumed of the instance** — with the *derived* [`Ttc.TtcProb.vol_lt_two_total`](Ttc/Coupling/Transfer.lean) it is what `Ttc.rate_small_of_epoch` needs, which is how the old `rate_small` field became a theorem |
| **`big`** | **`(1−ε')·Thresh/8 ≤ ∑θ`** — the instance is large enough for the sketch to be worth running | **assumed of the instance**, and a genuine assumption — but it is the paper's own regime, not an artifact. It is what `Ttc.exists_epoch` needs to build `j*`, and [`Ttc.Box.boxProb`](Ttc/Witness/BoxProb.lean) arranges it by choosing the box side from `Thresh`. At two cubes the box's route (which needs `N = L`) does not apply and [`Ttc.TwoCube.big_two`](Ttc/Witness/TwoCube.lean) discharges it differently — §3g |

### The 15 fields of `Ttc.KV97Sampler`

New since the last version of this page, and **the interface changed shape while
this page was being written** — it previously carried a *pointwise density*
(`contDensity`, `density_au`, `density_int`); it now carries a *law and a
total-variation bound*. That swap is [`AUDIT-KV97.md`](AUDIT-KV97.md) §4b's own
recommendation, acted on; §4b explains why the pointwise route is not merely
harder but **unattainable** for a real ball-walk sampler.

| Field(s) | What it asserts | Status |
| --- | --- | --- |
| `J`, `fintypeJ` | the facet index of the dilated polytopes, finite | structure |
| `Amat`, `bvec` | the linear description of the *dilated* polytope `10^ρ · P(cᵢ)` | input |
| `dilate_eq` | `10^ρ · P(cᵢ) ⊆ body (Amat i) (bvec i)` | **assumed of the input.** Note this is an **inclusion**, weakened from the equality it used to be: the one consumer, `Ttc.TtcProb.samp_almostUniform_subtype`, uses only `⊆`. The name still says `eq`; [`Ttc.KV97Sampler.dilate_subset`](Ttc/Sampler/Bridge.lean) is the honest alias |
| `facetBound`, `one_le_facetBound`, `card_le_facetBound` | KV97's `r ≥ 1` really bounds the facet count | **assumed of the input**; pays for the union bound over facets |
| `contLaw`, `isProbContLaw` | the law the continuous draw is made from, a probability measure | input |
| `contVol`, `contVol_pos`, `contVol_eq` | the normalising volume, positive, **and equal to `Vol(P')`** | `contVol_eq` is a *definition*, not a hypothesis. Under the old density formulation `contVol` cancelled out of `sampD` and was a free gauge (`reNormalise`, now deleted, proved any positive value worked); under TV it is **determined**, because the tolerance is `ε'/(4·contVol i)` and shrinking it strictly strengthens `law_tv`. Positivity plus `contVol_eq` forces `Vol(P') ∉ {0, ⊤}` for free, so this costs no new assumption |
| **`law_tv`** | **`TVLe (contLaw i) (uniformOn volume (inflated …)) (ofReal (ε'/(4·contVol i)))`** | **the one quantitative field of the bundle.** A continuous almost-uniform sampler on the inflated dilated polytope, at tolerance `ε'/(4·Vol(P'))`. It is still an *assumption* for anyone who supplies a `Ttc.KV97Sampler` by hand — but it is **no longer an open oracle for the development**: [`Ttc.kv97SamplerOfBody`](Ttc/Sampler/Construct.lean) constructs a bundle whose `law_tv` is **proved**, from a lazy ball walk, and that is what `Ttc.ttc_volume_endToEnd` uses. Read §1c caveat 1 for what is *not* proved about that construction, and `AUDIT-KV97.md` §2 for the history |
| `sampD_eq` | `sampD i x` **is** the rejection-normalised rounding law: `∫ prodTent (10^ρ·x) p ∂contLaw i` divided by the same sum over all lattice points of the dilated cube | **definition of the sampler**, not a bound on it. This is what makes `sampD` the thing KV97 Theorem 2 is about |

### Almost-uniform sampling, `eq:almostuniform`

`GenerateSamples` is assumed only to draw from a distribution within a `(1±ε')`
factor of uniform on `P(cᵢ) ∩ 𝕃ⁿ`. **That is no longer an assumption at all** —
it is [`Ttc.TtcProb.samp_unif`](Ttc/Sampler/Bridge.lean), a theorem, derived from
`sampler` through KV97 Theorem 2. What replaced it as an assumption is `law_tv`,
one level down: the *continuous* draw is almost uniform, and the *discrete* one is
proved to be. And on the `Ttc.ttc_volume_endToEnd` route even that is discharged —
the continuous draw is a lazy ball-walk iterate and `law_tv` is proved of it
(§1c). The chain `ball walk → law_tv → samp_unif → eq:almostuniform` is a chain of
theorems end to end there.

Two consequences an auditor should verify rather than assume: the accuracy budget
is `(1±ε')³(1±η) ⊆ (1±ε/2)`
([`Ttc.Params.epsPrime_window`](Ttc/Constants/Parameters.lean)) — `ε/3` no longer
suffices — and `δ' = δ/(4m)` ([`Ttc.Params.deltaPrime`](Ttc/Model/Prelude.lean)),
which is what pays for the sampler's failure event `E_samp` beside `Vol_ED`'s
`E_vol`.

> **`Ttc.Params.epsPrime_window` is NOT reached by the headline** — §5's walk
> reports `false`. It is a statement *about* the constants, proved, but the
> headline's arithmetic goes another way. Do not read it as a load-bearing step.
> `Ttc.Params.kappa_div_gamma_le`, `shell_factor_bound` and
> `shell_factor_bound_deflated` *are* reached.

A one-sided bound would **not** do, and this is the one place where the paper's
choice of `≤` versus a two-sided window is doing real work: from
`D(x) ≤ (1+ε')/|P ∩ 𝕃ⁿ|` alone one gets only `D(A) ≥ |A|/|P ∩ 𝕃ⁿ| − ε'`, an
additive loss that is vacuous exactly when `A` is the small part of `P(cᵢ)` no
later cube covers — which is the mass the estimate is made of. `theta_lo` would be
unprovable and the lower half of the headline would fail.

There is **no `jstar` row**, and that is the point: an epoch index in the right
window used to be five fields of this table, and is now produced by
[`Ttc.exists_epoch`](Ttc/Coupling/Transfer.lean) from `big` and
[`Ttc.TtcProb.thresh_pos`](Ttc/Coupling/Transfer.lean).
[`Ttc.Box.exists_jstar`](Ttc/Witness/BoxProb.lean) still exists in the witness
file; a reverse-dependency scan of the compiled environment confirms **nothing
uses it**.

**Where the `δ` comes from.** It is not hand-waved, and it is not conditional on
an assumed covering. The sampler fields give the covering
([`Ttc.TtcProb.numlattice_union`](Ttc/Coupling/Transfer.lean), proved via
[`Ttc.numlattice_union_of_model`](Ttc/Coupling/Transfer.lean) from
[`Ttc.traj_numlattice_le`](Ttc/Coupling/Run.lean)); the covering plus the *proved*
sizes of the three contributions
([`Ttc.numlattice_failure_le`](Ttc/Process/SketchProcess.lean), at the algorithm's
own `Thresh` and `δ'`) gives `Pr[ output ∈ (1±ε/2)·L ] ≥ 1 − δ`
([`Ttc.TtcProb.numlattice`](Ttc/Coupling/NumLattice.lean)); the deterministic
chain shows that event is *contained in* the `(1±ε)·Vol(F)` event; measure
monotonicity does the rest. The `δ` is earned — given that the sampler is the one
`law_eq`, `oracle_eq` and `sampler` describe.

Nothing anywhere here is about running time (`thm:runtime` is out of scope for
`volume_estimate`; `Ttc.ttc_volume`'s second conjunct is a *cost bound* conditional
on `Ttc.Terminates`, not a termination proof).

---

## 3. Is the theorem non-vacuous?

A `∀ (T : TtcProb A n), …` proves nothing if `TtcProb` is uninhabited. There are
now **five** hypothesis-bundling structures in play, and each needs its own
witness. Their limitations differ, and the limitations matter as much as the
existence. §3e, §3f and §3g are about the binder-form statements, which bundle
nothing but still need a witness that their hypothesis lists are jointly
satisfiable. **Read which theorem each witness instantiates**: every witness in
§3a–§3f is the same single-cube box, and each is a witness for a statement weaker
than the strongest one; **§3g is the witness for `Ttc.ttc_volume_final` itself,
and its DNF has two cubes.** §3f's closing paragraph says what the box leaves
untested and §3g says which of it the two-cube witness reaches.

### 3a. `Ttc.TtcProb` — the headline's structure

[`Ttc.Box.nonempty_ttcProb`](Ttc/Witness/BoxProb.lean), witnessed by
[`Ttc.Box.boxProb`](Ttc/Witness/BoxProb.lean): **the box `[0,c]ⁿ`**, cut out by
`2n` positive linear atoms ([`Ttc.boxAtoms`](Ttc/Witness/Box.lean)) as the single
cube of a one-cube DNF ([`Ttc.boxCube`](Ttc/Witness/Box.lean),
[`Ttc.boxDNF`](Ttc/Witness/Box.lean)) representing the conjunction of those atoms
([`Ttc.boxForm`](Ttc/Witness/Box.lean),
[`Ttc.boxDNF_isDNFOf`](Ttc/Witness/Box.lean)), sampled by the coupled family. It
needs `1 ≤ n`, because `Ttc.Params` requires a positive dimension and `dim_eq`
ties it to the ambient one.

**It is NOT degenerate.** Check these four things:

* **Nonempty solution set, positive volume.** `Sol(F) = [0,c]ⁿ`
  ([`Ttc.sol_boxForm`](Ttc/Witness/Box.lean)), a genuine polytope. The geometric
  fields are exercised, not vacuous: `ball_subset` is discharged by
  [`Ttc.ball_subset_region_boxCube`](Ttc/Witness/Box.lean) (the inscribed ball of
  radius `c/2` about the centre), `volume_ne_top` by
  [`Ttc.volume_region_boxCube_ne_top`](Ttc/Witness/Box.lean), `isPositive` by
  [`Ttc.boxDNF_isPositive`](Ttc/Witness/Box.lean), and `normal_ne_zero` by
  [`Ttc.boxAtoms_normal_ne_zero`](Ttc/Witness/Box.lean).
* **`L` is large, not zero.** The side is `c = max 1 Thresh`
  ([`Ttc.Box.side`](Ttc/Witness/BoxProb.lean)), and
  [`Ttc.Box.side_le_Lval`](Ttc/Witness/BoxProb.lean) proves `Thresh ≤ c ≤ cⁿ ≤ L`,
  from [`Ttc.normalisedCount_box_ge`](Ttc/Witness/Box.lean) — which holds at
  *every* precision `ρ`, so `c` may be picked before `ρ` is fixed. The instance
  therefore clears the regime the epoch estimate needs — the `big` field,
  discharged from
  [`Ttc.Box.epsPrime_thresh_le_Lval`](Ttc/Witness/BoxProb.lean).
* **The sampler fields are discharged by proof, not by an empty failure event.**
  `Ω` *is* the trajectory space, `μ` is `trajLaw θ`, `toTraj` is the identity, so
  `law_eq` is `Measure.map_id` and `oracle_eq` is `rfl`; the run is therefore a
  genuinely random one, and `Ttc.TtcProb.numlattice_union` instantiated here is
  the real bound (its self-coupled form is
  [`Ttc.numlattice_union_of_traj`](Ttc/Coupling/Transfer.lean)). `vol_pos` is
  `Ttc.Box.volume_bx_pos`. The `Vol_ED` fields are discharged too, not dodged:
  `volAlg` is [`Ttc.VolumeAlgorithm.exact`](Ttc/Volume/Bridge.lean) — the oracle
  that returns `Vol(K)` on the nose and never fails — so `volCoins` is the unique
  point of `Unit`, `volED_eq` is the rounding bridge's
  [`Ttc.toReal_volume_eq`](Ttc/Volume/Bridge.lean) applied to the box, and
  `volCoins_good` holds because the exact volume lies in `(1±ε')·Vol` for
  `ε' > 0`. **This is the *ideal* corner of Theorem 1.1, not an appeal to
  emptiness**: the box has positive finite volume, so the interval is genuine.
* **The rates spread `L` evenly, so `∑θ = L` exactly.**
  [`Ttc.Box.th`](Ttc/Witness/BoxProb.lean) is the constant `L/Lidx` and
  [`Ttc.Box.sum_th`](Ttc/Witness/BoxProb.lean) proves the total is `L`. This is
  the **ideal instance** CLAUDE.md §13 asks for: every error coefficient is `0`,
  `Vol_ED` returns the exact volume ([`Ttc.Box.vl`](Ttc/Witness/BoxProb.lean)),
  and the accuracy window is discharged with nothing to spend
  ([`Ttc.window_of_exact`](Ttc/Coupling/Transfer.lean)).

The old witness `Ttc.trivialProb` (empty DNF, `L = 0`, everything vacuous) has
been **deleted**. It could not survive the sampler fields: `D = []` forces
`Lidx = 0`, which contradicts positivity of the total rate.

(`Ttc.TtcAnalysis` in [`Capstone`](Ttc/Capstone.lean) is an internal device for
the arithmetic, not part of any statement, and needs no witness. An earlier
primitive-by-primitive oracle contract `Ttc.OracleLaws` used to be listed here
with **no witness**; it has been **deleted**, consumed by nothing.)

### 3b. `Ttc.ttc_volume` — and why 3a does not cover it

[`Ttc.Box.ttc_volume_box`](Ttc/Exec/Endgoal.lean) is `Ttc.ttc_volume` applied to
the box's own data. It is currently the **only** witness that the residual
hypotheses of `ttc_volume` are *jointly* satisfiable.

**`Ttc.Box.nonempty_ttcProb` does not automatically witness it**, and the reason
is worth knowing because it is the kind of gap that hides:
`ttc_volume` asks for `hP : P = Ttc.ttcParams (toDNF φ) n ε δ …`, an equation
pinning the parameter block to the canonical closed term, whereas
[`Ttc.Box.par`](Ttc/Witness/BoxProb.lean) stores `m = max 1 (…)` and
`r = max 1 (…)`. Those are *not* syntactically `ttcParams`.
[`Ttc.Box.par_eq_ttcParams`](Ttc/Exec/Endgoal.lean) is what closes it, given
`1 ≤ #cubes` and `1 ≤ #facets`.

**Two limitations to state plainly.**

1. `Ttc.Box.par` fixes **`ε = 1` and `δ = 1`**. So the probability half of
   `ttc_volume_box`'s conclusion reads `1 − 1 ≤ …`, i.e. `0 ≤ …` — *trivially
   true*. The witness certifies that the **hypothesis bundle is inhabited**, which
   is the §11 obligation and is what it is for; it certifies nothing about the
   conclusion at a useful accuracy.
2. It inherits 3a's idealisations — exact volume oracle, exact rates.

### 3c. `Ttc.VolumeAlgorithm` — the `Vol_ED` oracle

Two witnesses, in [`Ttc/Volume/CousinsVempala.lean`](Ttc/Volume/CousinsVempala.lean):
[`Ttc.VolumeAlgorithm.cousinsVempalaWitness`](Ttc/Volume/CousinsVempala.lean) and
`cousinsVempalaBiasedWitness`. Each instantiates every argument of the
`Ttc.VolumeAlgorithm.cousinsVempala` construction — `Ω = Unit`, `μ = dirac ()`,
one phase, a deterministic score, `κ = 0` — and discharges all fourteen of its
hypotheses.

**Read this one carefully; it is the easiest to overstate.**
[`Ttc.VolumeAlgorithm.cousinsVempalaWitness_est`](Ttc/Volume/CousinsVempala.lean)
is `rfl` to `(volume K).toReal`, at *every* accuracy, confidence and coin. The
witness is therefore [`Ttc.VolumeAlgorithm.exact`](Ttc/Volume/Bridge.lean) **in
disguise**: an exact oracle wearing the Cousins–Vempala construction's clothes.

What it shows: the fourteen hypotheses are **mutually consistent** — the bundle is
not self-contradictory, so `cousinsVempala` is not a statement about nothing.

What it does **not** show, and must not be read as showing: that **the paper's
Gaussian schedule meets them**. It is a degenerate schedule. The three hypotheses
that a real sampler would have to supply — `hphase_mean`, `hphase_var`,
`hphase_indep` — are met here only because the phase estimator is a constant. The
module docstring says this in its own words; so does
[`CV-ROADMAP.md`](CV-ROADMAP.md).

> **Since 2026-08-12 there is a fourth constructor and a fourth witness**, and the
> capstone uses them: `Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMean`
> (`Ttc/Volume/CVInstantiate.lean:458`), whose `hphase_mean` is an interval rather
> than an equation and whose `hphase_var` is at `varBudget (ε/2)`, witnessed by
> `cousinsVempalaOfRunsApproxMeanWitness` (`:634`) — degenerate in the same way
> (zero phases), for the same reason. §0a and §0f are the audit surface for that
> change. `hphases_pos` was also **deleted** as a binder of
> `VolumeAlgorithm.cousinsVempalaOfApproxMean` (`CousinsVempala.lean:2065`), the
> `m = 0` case now being handled in the proof; `cousinsVempalaOfSampler` still
> carries it.

`Ttc.VolumeAlgorithm.cousinsVempala` is **not** reached by either capstone (§5's
walks report `false` from `Ttc.TtcProb.volume_estimate` *and* from
`Ttc.ttc_volume_endToEnd`): `volAlg` is an assumed field of `TtcProb`, and this
file is the *assembly towards* discharging it, not the discharge.

**And it was not what discharged it.** `volAlg` is gone from
`Ttc.ttc_volume_endToEnd`, but by a different construction —
[`Ttc.VolumeAlgorithm.monteCarlo`](Ttc/Volume/MonteCarlo.lean), hit-and-miss Monte
Carlo, exponential in `n`. `Ttc/Volume/CousinsVempala.lean` was **bypassed, not
proved**; it remains the only route to a *polynomial-time* volume oracle.

**Three later constructions in that file are not degenerate — and what they show is
mostly negative.** `Ttc.VolumeAlgorithm.cousinsVempalaOfSampler`,
`…OfSamplerFixedRate` and `…OfSamplerCooling` take a genuine sampler rather than a
constant score; `hTV` — the sampler itself — is their only mathematical debt. What
they establish about the schedule is worth reading before quoting any of it:

* **The fixed-rate schedule does not anneal.** `Arlib.geomSchedule_total_cooling_lt`
  proves that an `α = 1/n` schedule meeting the per-phase variance budget cools by a
  factor **less than `11/10`**. Consequently
  `Ttc.CV.cold_start_mem_relErr_of_fixedRate_fields` shows that the telescope's
  *first factor alone* already estimates `Vol K` to within `11/(5n)` — the
  construction is consistent and non-vacuous, but at that schedule it is not
  computing anything the cold start did not already know.
* **The general-`α` schedule does anneal, and annealing is not free.**
  `Ttc.CV.cool_schedule_anneals` gives total cooling `≥ e^L` at
  `m = ⌈8(n+1)L²/κ⌉`, and `Ttc.CV.cool_flat_slacks_satisfiable` checks the whole
  hypothesis set at a strictly positive TV error, with no lower bound on `n`. But
  enlarging `m` to buy cooling tightens the per-phase budget `κ/m` by the same
  factor, and `Ttc.CV.cold_start_exponent_ge_of_coolRate` locates the crossover
  against `11/(5n)` at `e^{2L} ≳ 17.6·L²/κ²` — essentially dimension-free. Below it
  the general-`α` schedule inherits the fixed-rate degeneracy in full.
* **No rate or running-time claim is made anywhere in that file.** A polynomial
  phase count is not a polynomial algorithm; the per-phase sampling cost is
  untouched.

`CV-ROADMAP.md` §0′ carries the critical-path table and the nine findings against
the Cousins–Vempala paper (five of them statements false as printed).

### 3d. Downstream structures with partial witnesses

> **The 2026-08-12 additions to this list are in §0e and §0f rather than here**,
> because they are all `∀`-binder bundles rather than structures: the isoperimetry
> and Metropolis-mixing witnesses (§0e's closing subsection), the chain-layer
> coupling witness `Arlib.GaussianCooling.exists_couplingRoute_chain_witness`, and
> — **loudly** — the fact that `Ttc/Volume/CouplingAccuracy.lean`'s two composed
> theorems have **no witness at all** (§0f). Read those before concluding that this
> page's witness inventory is complete.

Two more, both in `Arlib/`, both witnessing hypothesis bundles that are *not yet*
on the headline's path but are where the remaining oracles will be discharged.
Their limitations are the point:

* **`hiso` is no longer open** — *this* `hiso`, the **ball walk's** isoperimetric
  binder, which is a different statement from Cousins–Vempala's `thm:iso` of §0e and
  is discharged at an **exponentially small** constant. Do not read the two as one.
  An earlier revision of this file said the
  isoperimetric inequality (`∀ d > 0, ∀ A B …, κ·d·π(A)·π(B) ≤ π(K \ A \ B)`) was
  "the open end of the whole Phase-4 stack", carried as a `∀`-binder by every
  mixing theorem. It is now a theorem, with nothing assumed:
  [`Arlib.uniformOn_iso_unitBall`](Arlib/Convexity/IsoBall.lean) for the Euclidean
  unit ball at `κ = (1/2)ⁿ⁺¹`, and
  [`Arlib.uniformOn_iso_of_convex`](Arlib/Convexity/IsoBall.lean) for **every**
  bounded convex body at `κ = 2⁻ⁿ/D`. The proof is an elementary chord argument
  that deliberately bypasses the localization machinery.

  Consequently
  [`Arlib.MarkovChains.exists_unconditional_mixing_unitBall`](Arlib/MarkovChains/Continuous/UnitBallMixing.lean)
  is the first statement in this development where isoperimetry, local
  conductance, Cheeger, the `L²` decay and the total-variation bound are all
  *discharged simultaneously* rather than assumed — no geometric hypothesis, and
  the warm start discharged by the stationary measure itself.

  **Read the cost before quoting it.** `κ = 2⁻⁽ⁿ⁺¹⁾` is exponentially small, so
  the conductance and the mixing time it feeds are exponential in `n`. This is
  **not** a polynomial-time sampler. A polynomial constant still needs the
  localization route, whose sole remaining obstruction is (P1) in
  [`Arlib/Convexity/PositionalCut.lean`](Arlib/Convexity/PositionalCut.lean).
  `Arlib.uniformOn_dyerFrieze_dim_one` gives the sharp `κ = 2/D`, but only in
  dimension one.
* [`Arlib.PointwiseRoute.exists_theorem2_of_tvLe_witness`](Arlib/MarkovChains/Continuous/PointwiseRoute.lean)
  witnesses that Theorem 2's TV hypotheses are satisfiable — but **only in the
  degenerate `ε = 0` corner**, where `μ` *is* the uniform measure exactly and the
  `TVLe` is discharged by reflexivity. It is a real non-vacuity check and it meets
  CLAUDE.md §11, but it is **weaker than it looks**: it exhibits no sampler that is
  approximately uniform, only one that is exactly uniform.

  **That gap is now closed**, by
  [`Arlib.TVWitness`](Arlib/MarkovChains/Continuous/TVWitness.lean).
  `exists_nondegenerate_theorem2_of_tvLe_witness` inhabits the *whole* hypothesis
  bundle at **strictly positive** total variation, on the Kannan–Vempala cube
  itself (`volume = 2ⁿ⁺¹` exactly, escape mass `E = 0` exactly), and pins the
  distance: any valid `ε` satisfies `θ/V ≤ ε`, so the distance *is* `θ/V`, computed
  rather than bounded. Two structurally different witnesses are given —
  `boxAtomLaw` (atomic) and `boxDensityLaw` (absolutely continuous), so the
  inhabitation does not depend on the atom.

  The atomic one also proves `∀ ε, ¬ PointwiseClose μ (uniformOn volume S) ε`. That
  is the load-bearing part: the TV bundle is inhabited by exactly the class of laws
  the pointwise route provably **cannot** describe, which is why the sampler
  interface was moved off `density_au` and onto `law_tv`. The swap is vindicated,
  not merely asserted.

A third, in the same family and listed here because §4 of
[`AUDIT-KV97.md`](AUDIT-KV97.md) depends on it:
[`Arlib.KV97.exp_neg_one_le_acceptance_cube`](Arlib/Lattice/KV97/Lemma1.lean),
the Lemma 1 witness, takes `pt` **constant** (`fun _ => 0`). Since injectivity of
`pt` is now a *proved requirement* for `acceptance` to be a probability at all
(`AUDIT-KV97.md` §4h), this witness certifies only that the **bounds'** hypothesis
bundle is inhabited — not that the quantity bounded is a probability in that
instance.

### 3e. `Ttc.ttc_volume_endToEnd` — the binder-form non-vacuity check

`ttc_volume_endToEnd` bundles nothing: its hypotheses are `∀`-binders, so it adds
no sixth structure to the five above. It still needs a witness, for the same
reason — a hypothesis list can be jointly unsatisfiable — and the one it has is
better than every §3a–§3d witness here on three separate axes. (§3f does the same
for the clean-budget statements and reaches a `δ` this one cannot; the arity
caveat there applies to this witness equally, and §3g is where arity is answered —
for a different, stronger theorem.)

* **It instantiates the headline itself, not a weaker variant.**
  [`Ttc.Box.ttc_volume_endToEnd_box_at`](Ttc/Exec/EndToEnd.lean) is
  `Ttc.ttc_volume_endToEnd` applied to the box `[0,c]ⁿ`, at **every**
  `(ε, δ) ∈ (0,1]²`. §5's walk from it reaches `Ttc.ttc_volume_endToEnd`
  (`true`), which is what rules out the failure mode of a witness quietly
  discharging a restated, weaker statement.
* **Two instances, at different parameters, both informative.**
  [`Ttc.Box.exists_two_ttc_volume_endToEnd_instances`](Ttc/Exec/EndToEnd.lean)
  gives `(ε, δ) = (1/2, 1/2)` and `(1/4, 1/4)`, packaged through
  [`Ttc.Box.AtParamsE2E`](Ttc/Exec/EndToEnd.lean) so the parameters are exposed
  and comparable. The achieved bounds are `3/8` and `11/16`, and **both are proved
  `> 0` inside the statement** — so unlike §3b's `ttc_volume_box`, which runs at
  `ε = δ = 1` and concludes `0 ≤ …`, these conclusions carry information. This is
  the pair check of "Checks a green build does not perform" item 4, passed.
* **The two degeneracies that would make it hollow are excluded by name.**
  [`Ttc.Box.bxRates_pos`](Ttc/Exec/EndToEnd.lean) proves the constructed rates are
  strictly positive at every good coin — the collapsed `θ ≡ 0` satisfies `theta_eq`
  vacuously and would make `big` unsatisfiable, so ruling it out is not decoration.
  [`Ttc.Box.endToEnd_box_lintegral_pos_ne_top`](Ttc/Exec/EndToEnd.lean) closes the
  `ENNReal.toReal ⊤ = 0` trap of §1: wherever the budget `1 − δ − δ/4` is positive,
  the bound itself forces the integral inside the `toReal` to be both nonzero and
  finite. Note the direction — finiteness is **read off** the proved positive
  bound, not assumed alongside it.

**What it still does not show.** It is one body, the box, with a linear
description and diameter chosen for it; nothing here says the hypothesis bundle is
satisfiable for an *arbitrary* positive DNF, and the geometric binders `Jt`, `Am`,
`bv`, `hdil`, `Dm`, `hDbody` are exactly where a hard instance would bite. (§1d's
`Ttc.ttc_volume_endToEnd_canon` removes those six binders from the *statement*, by
constructing them; that is a different thing from a witness at a second body, and
§3f's arity caveat is not touched by it. A witness at a second body *does* now
exist — §3g's, a pair of disjoint boxes — but it witnesses
`Ttc.ttc_volume_final`, not this statement.)

### 3f. `Ttc.ttc_volume_final` and `Ttc.ttc_volume_clean` — the clean-budget witnesses

[`Ttc.Box.ttc_volume_clean_box_at`](Ttc/Exec/Budget.lean) puts the clean statement
on the box at **every** `(ε, δ) ∈ (0,1]²`, with no oracle at all, and
[`Ttc.Box.exists_two_ttc_volume_clean_instances`](Ttc/Exec/Budget.lean) gives the
pair. Two things make it a stronger check than §3e's, and one thing makes it no
stronger at all.

* **It reaches a regime §3e provably could not.** The pair is
  `(ε, δ) = (1/3, 9/10)` and `(1/2, 1/4)`, achieved bounds `1/10` and `3/4`, both
  proved `> 0` in the statement
  ([`Ttc.Box.clean_box_at_nine_tenths`](Ttc/Exec/Budget.lean),
  [`clean_box_at_one_quarter`](Ttc/Exec/Budget.lean)). At `δ = 9/10 > 4/5` the old
  budget was `1 − δ − δ/4 = −1/8`, a lower bound no `toReal` can fail, i.e. no
  information. That comparison is not left as prose:
  [`Ttc.Box.old_budget_vacuous_at_nine_tenths`](Ttc/Exec/Budget.lean) proves
  `1 − 9/10 − (9/10)/4 = −1/8 ∧ … ≤ 0` alongside `1 − 9/10 = 1/10 ∧ 0 < 1/10`, so
  the claim "the re-budgeting bought a regime" is itself machine-checked.
* **The `toReal ⊤ = 0` trap is closed here too.**
  [`Ttc.Box.clean_box_prob_pos_ne_top_at_nine_tenths`](Ttc/Exec/Budget.lean) reads
  off the positive bound that the integral inside the `toReal` is nonzero and
  finite — the same direction as §3e, at a point §3e could not reach.
* **Read how it is proved, not only what it says.** `ttc_volume_clean_box_at` is
  **not** an application of `Ttc.ttc_volume_clean`: it is §3e's box instance of
  `Ttc.ttc_volume_endToEnd` repriced at `δ₀ = 4δ/5`, so its conclusion has the
  clean statement's shape while its proof runs through the unrepriced one. That is
  sound — the repricing is the same arithmetic `ttc_volume_clean` performs — but it
  means this witness certifies the *shape* only, and the same goes for
  `clean_box_at_nine_tenths` and `clean_box_at_one_quarter`.
  **The witness that applies `Ttc.ttc_volume_clean` itself is
  [`Ttc.Box.atParamsClean_of`](Ttc/Exec/Budget.lean)**, whose proof term supplies
  all ten description arguments (`Fin n ⊕ Fin n`, `bxNormal`, `bxOffsetOf`,
  `hdil_box`, `bfac`, `one_le_bfac`, `card_le_bfac`, `bxDm`, `hDbody_box`) and so
  typechecks only if all ten hold. It discharges
  [`Ttc.Box.AtParamsClean`](Ttc/Exec/Budget.lean), which carries those ten as
  fields and ties the sampler law to `e2eSampD … rfac Am bv cen gammaHat Dm` — a
  package that asserts nothing it does not discharge. The other capstones applied
  directly are §3e's (`Ttc.ttc_volume_endToEnd`, to the box) and §3g's
  (`Ttc.ttc_volume_final`, to the two-cube DNF).
* **`Ttc.ttc_volume_final` does not dominate `Ttc.ttc_volume_clean`.** Worth
  stating because it is the natural assumption and it is wrong. The running-time
  conjuncts are character-for-character identical, but the accuracy conjuncts
  integrate different measures: `clean`'s names `e2eSampD … rfac Am bv … Dm` in the
  **bound** variables, `final`'s names `canonRfac`/`canonAm`/`canonBv`/`canonDm`.
  `final` is `clean` instantiated at the one canonical description, and a point of
  a `∀` does not give back the `∀`. The implication runs `clean ⟹ final` only, so
  each needs its own witness — which is why both exist.
* **It is the same body.** `Ttc.Box.sideS`/`rhoS`/`parS`/`volMC`/`bxSampD` differ
  between the two instances (the internal parameters are `18/25` and `1/5`), so the
  parameters are provably not forced — but the *geometry* is the single-cube box in
  both, exactly as in §3a–§3e. See the arity caveat below.

**The arity caveat, which applies to every witness in §3a–§3f.**
`Ttc.Box.length_toDNF_boxForm` proves `(toDNF (boxForm n hn)).length = 1`. **Every
witness in §3a–§3f is that one-cube box**, so at those rungs the multi-cube
machinery is exercised by nothing:

* `hlen` is a `Nodup` condition in disguise — `P.m = Nat.card {c // c ∈ toDNF φ}`
  counts *distinct* cubes and a list is never shorter than its distinct-element
  count, so `hlen` holds exactly when `toDNF φ` repeats no cube. At length 1 that
  content is never exercised.
* The `m`-way union bound over cubes, `thm:decomposition`'s union
  ([`Ttc.TtcProb.sol_eq_union`](Ttc/Capstone.lean)) and `lem:numlattice`'s
  multi-cube content are exercised only at `m = 1`.
* So is the per-cube composition of the volume and the sampling errors.

The statements are **not** vacuous — the hypothesis lists are jointly satisfiable
and the conclusions carry numbers. But the witness is the easiest case. Do not
read §3f's `> 0` bounds as evidence about arity; they are evidence about `δ`.
Arity is what §3g answers, and it answers it for the strongest statement rather
than for this one.

### 3g. `Ttc.ttc_volume_final` — the two-cube witness, and the first witness this theorem has had

[`Ttc.TwoCube.ttc_volume_final_two_cube`](Ttc/Witness/TwoCube.lean) instantiates
**`Ttc.ttc_volume_final` itself** — §1d's statement, the strongest in the
development — at every `(ε, δ) ∈ (0,1]²`, with **every binder discharged,
including `big`**. Not `ttc_volume_endToEnd_ofSampler`, not `ttc_volume_clean`,
not `ttc_volume_endToEnd`: §5's walk from it (and from
`ttc_volume_final_two_cube_at`) reports `true` for `Ttc.ttc_volume_final`, which
is the check that rules out a witness quietly discharging a restated weaker
statement. **Before this landed, `ttc_volume_final` had no non-vacuity witness at
all** — the strongest statement in the tree was unwitnessed, and that was a real
gap, not a formality. Earlier revisions of this page said flatly that every
witness in the development was the single-cube box; that was true when they said
it and is false now.

**The construction.** Atoms indexed by `(Fin n ⊕ Fin n) ⊕ (Fin n ⊕ Fin n)`, the
left copy cutting out `[0,c]ⁿ` and the right `[lo, lo+c]ⁿ`, with
`c = max 1 Thresh(ε, 4δ/5)` and `lo = (⌈c·10^ρ⌉₊ + 1)/10^ρ`. `lo > c` gives
disjointness; `lo` being a multiple of the lattice spacing puts a lattice point in
the second box. The order is not circular: `ρ` depends only on `(n, ε, δ)` and the
DNF's *shape* (`m = 2`, `r = 4n`), never on `lo`.

**What arity two exercises, as theorems and not as prose.**

* [`Ttc.TwoCube.card_toDNF_eq_two`](Ttc/Witness/TwoCube.lean) is an **equality**,
  `Nat.card {c // c ∈ toDNF (twoForm n)} = 2` — not a `2 ≤ …`. This is the
  anti-degeneracy fact everything else rests on: the DNF genuinely has two cubes.
* [`Ttc.TwoCube.sol_eq_union_two`](Ttc/Witness/TwoCube.lean) — `Sol(F)` is the
  union of the two regions, which are **distinct, nonempty and disjoint**.
* [`Ttc.TwoCube.cenT_left_ne_right`](Ttc/Witness/TwoCube.lean) — the two
  inscribed-ball centres genuinely differ, so `cen` is not a constant function.
  `γ̂` is shared; `cen` is not.

The single-cube box exercises none of those three.

**Why `big` needed a new argument, which is the substantive part.** The box
discharges `big` through [`Ttc.Box.sum_bxRates_ge`](Ttc/Exec/EndToEnd.lean), whose
route relies on `N = L` — true only when there is one cube. With two cubes
`cubeAt` varies with the point, `N₁ ≠ N₂` in general, and `L = N₁ + N₂`. The
replacement bounds every rate below by `min(q₁, q₂)`, `qᵢ = (1−ε')·V̂ᵢ/Nᵢ`
([`Ttc.TwoCube.min_qT_le_ratesT`](Ttc/Witness/TwoCube.lean), which **case-splits
on which cube `cubeAt s` returned** — the branch no single-cube witness has), and
then uses `Nᵢ ≤ L`. It also required an exact volume computation that did not
exist in the tree, `Ttc.TwoCube.volume_sbx : volume [lo, lo+c]ⁿ = ofReal c ^ n`,
because the box files carried only positivity plus a global lattice bound.

**Two instances, with the bound a positive numeral in the statement.**
[`Ttc.TwoCube.ttc_volume_final_two_cube_at`](Ttc/Witness/TwoCube.lean) gives
`(ε, δ) = (1/3, 9/10)` at `1/10` and `(1/2, 1/4)` at `3/4`, both proved `> 0`
inside the statement, and the first carries `4/5 < 9/10 < 1` alongside — the
regime the old `1 − δ − δ/4` budget could not reach at all. The two runs differ in
side, precision, corner and parameter block, so the parameters are provably not
forced. [`Ttc.TwoCube.twoProb_pos_ne_top_at_nine_tenths`](Ttc/Witness/TwoCube.lean)
closes the `ENNReal.toReal ⊤ = 0` reading, the same direction as §3e and §3f:
finiteness is read off the proved positive bound.

**Nothing is assumed to make it work.** No `Prop` bundling a hypothesis is
introduced; the sampler is `Ttc.e2eSampler`, whose `law_tv` is a theorem; the
volume estimates are the Monte-Carlo oracle's own output; and the linear
description of the two dilated regions is the canonical one of
`Exec/CanonPolytope`.

**What it does not show, and a reader will assume the first of these.**

* **`volSol = Vol₁ + Vol₂` is NOT proved.** Disjointness of the two regions is
  proved; additivity of the volume over them is not, and the capstone does not
  need it. Do not quote the witness as establishing it.
* **It is not an efficiency claim.** Everything on this route is exponential in
  the dimension, and at `m = 2` every exponential cost is paid twice — the
  Monte-Carlo sample count, the ball walk's certified step count and the lattice
  enumeration alike. `thm:runtime` stays out of scope. "Unconditional" and
  "efficient" remain independent claims and only the first is established.
* **The §1c/§1d caveats are inherited unchanged**, in particular that the
  finite-time ball-walk iterate is not proved to *differ* from `uniformOn` on the
  inflated body.
* **It is two bodies of the same shape.** Nothing here says the hypothesis bundle
  is satisfiable for an arbitrary positive DNF; arity three, unequal sides and
  overlapping regions are all still untried.

---

## 4. Where a name stands in for a proof

`#print axioms` cannot see a definition whose *name* claims more than its body
proves. These are the residual assumptions of that kind. None is hidden — each is
stated in the file that introduces it — but they are collected here because they
are exactly what a green build does not certify.

> **The 2026-08-12 material adds nothing to this section, and that is a checked
> claim, not an omission.** Every file behind §0e and §0f — `IsoOpenClosed`,
> `IsoIndicator`, `OneDimSharp`, `EllLogConcave`, `LocalizationMeasurable`,
> `LensMin`, `LensSharp`, `OverlapSqrt`, `DeltaCap`, `MetropolisOverlapSqrt`,
> `MixingSqrt`, `MetropolisMixing`, `MetropolisMixingUncond`, `EllFloor`,
> `TVTensor`, `PhaseMeanRoute`, `PhaseMeanApprox`, `CouplingRoute`,
> `CouplingRouteUncond`, `Ttc/Volume/CouplingAccuracy` — contains **no `def`,
> `structure`, `class` or `axiom` at all; every declaration is a `theorem`.
> `Ttc/Exec/RuntimeMN4.lean`'s single `def` is the meta-level binder counter behind
> `#binderProfile`, is not `Prop`-valued and appears in no statement. The one name
> in that file's runtime bound that could stand in for a proof,
> `Ttc.PolyComplexity.threshFactor`, is **expanded away** in the statement, and
> `Ttc.ttc_runtime_mn4_threshFactor` proves the expansion *is* the definition by
> `rfl`. The names that remain in the bound (`canonRfac`, `toDNFd`, `preprocess`)
> are computed from the input by the algorithm itself, not claimed identities.
> One name that **does** promise a semantic identity is
> `Arlib.GaussianCooling.coolLaw`, and it is **proved**, not asserted:
> `coolLaw_eq_uniformOn_gaussianWeight` (`PhaseMeanRoute.lean:216`) — §0f.

**The strongest residual assumption is a pair of `def`s asserted to be the
implementation.** The `law_eq` and `oracle_eq` fields say that two `def`s
(`Ttc.trajLaw`,
[`Ttc.trajOracles`](Ttc/Coupling/Family.lean)) *are* the algorithm's sampler. They
are honest about what they are: every property either one is used for is proved
(table at the end of this section). What no proof can establish is that a real
`TTC` implementation's sampler equals them. So:

> **An auditor should read the headline as: given that `TTC`'s randomness is the
> coupled Poisson/thinning family read through `trajOracles`, its output is within
> `(1±ε)·Vol(F)` with probability `≥ 1−δ`.** The conditional is a modelling claim
> about the sampler, not an unproved probability estimate. That is a strictly
> better position than the previous one — where the *conclusion* of the paper's
> hardest lemma was assumed — but it is not "assumption-free".

An earlier revision of this box also carried "and that its continuous draw meets
`law_tv`". **That clause is now removable, and only that clause.**
`Ttc.ttc_volume_endToEnd` (§1c) constructs the continuous draw and proves
`law_tv`, so the almost-uniformity of the sampler is no longer part of the
conditional. What is **not** removable is the `trajLaw`/`trajOracles`
identification: it remains the strongest residual assumption on every route,
including the oracle-free one **and `Ttc.ttc_volume_final` (§1d)**, because
`ttc_volume_endToEnd` is built on `Ttc.TtcProb.volume_estimate` (§5's walk reports
it reached) and `ttc_volume_final` is built on `ttc_volume_endToEnd`; both inherit
it unchanged. Removing an oracle is not the same as removing the model, and
removing the polytope description is not either.

**Corrections to earlier versions of this page, so you can tell drift from fact:**

* This page used to say `rate_eq_L` "assumes `∑θ = L` exactly" and that
  `Ttc.window_of_two_sided` "exists and is unused". **Both are wrong now.**
  `rate_eq_L` is **not a field of `Ttc.TtcProb`** — it does not exist. And a
  reverse-dependency scan shows `Ttc.window_of_two_sided` **is** used, by
  `Ttc.window_of_exact` and by `Ttc.TtcProb.numlattice_union`. The two-sided
  window is the live route; the exact one is the corner case.
* This page used to name a field `vol_eq` as what pins `vol`. There is no such
  field; it is **`volED_eq`**.
* This page used to say `Ttc.Oracles`' hypothesis-carrying fields are `halve_le`
  and `gen_card`. **There is no `halve_le`.** `Ttc.Oracles` has exactly seven
  fields — `vol`, `covered`, `thin`, `thin_le`, `pois`, `gen`, `gen_card` — and
  the two carrying hypotheses are **`thin_le`** and `gen_card`. The paper calls
  the operation `halve`; the Lean name is `thin`.

**The `jstar` block is gone, and that is a sharp improvement.** It used to assume
an epoch index in the right window *exists* for the instance — five fields, one of
them a chosen `j*` and the rest its window.
[`Ttc.exists_epoch`](Ttc/Coupling/Transfer.lean) now proves such an index exists
for *every* instance satisfying `big`, so the proof no longer takes the epoch it
evaluates at from the hypothesis bundle. Its hypotheses are exactly `0 < Thresh`,
`0 ≤ ε'` and `big`.

**Two facts the deletion needed, both now theorems.**
[`Ttc.TtcProb.thresh_pos`](Ttc/Coupling/Transfer.lean) proves `Thresh > 0` from
`alg:ttc` line 20's own formula rather than leaving it implicit — `δ ≤ 1` forces
`log(24/δ) ≥ log 24 > 0`, and `ε' = ε/12 ∈ (0, 1/12]` keeps `(1−ε')ε'²` positive —
and [`Ttc.TtcProb.vol_lt_two_total`](Ttc/Coupling/Transfer.lean) proves each cube's
rate is below twice the total. Together with `vol_pos` they feed
[`Ttc.rate_small_of_epoch`](Ttc/Coupling/Transfer.lean), which replaces the old
`rate_small` field.

**No mathematics is missing on the `lem:numlattice` path.** Every *estimate* the
proof invokes is a theorem here, including the one the paper imports from Soos et
al.: `lem:chernoff` is proved from the Poisson moment generating function upwards
([`Ttc/Process/Chernoff.lean`](Ttc/Process/Chernoff.lean)), as are both of its
applications, `lem:process`, the epoch series, and the `Vol_ED` failure budget the
paper omits. All four original obstacles to composing them into a statement about
`Ttc.run` are cleared:

* ~~`Ttc.Oracles` cannot express independence.~~ **Fixed** — calls are
  level-indexed, so independence across levels is statable, and `Err(j)`/`Nois(j)`
  are events about that index.
* ~~`lem:process` is only a pmf identity.~~ **Fixed** —
  [`Ttc.countLaw_eq_pi`](Ttc/Process/PoissonLaws.lean) gives it as an identity of
  measures, with independence, thinning and superposition as corollaries.
* ~~The halvings form a stopping time.~~ **Resolved** — and reading the paper's
  invariant as conditioning turns out to be *false* (README finding 14). The
  correct non-adaptive reading is
  [`Ttc.levelLaw`](Ttc/Process/SketchProcess.lean), and both branch estimates plus
  the whole `δ` budget are proved over it
  ([`Ttc.numlattice_failure_le`](Ttc/Process/SketchProcess.lean)).
* ~~The coupling is missing.~~ **Built** — README finding 15's construction exists.
  [`Ttc.trajOracles`](Ttc/Coupling/Family.lean) is an honest `Ttc.Oracles` bundle
  (both interface contracts discharged; `gen_card` holds unconditionally, via a
  never-taken filler branch) whose answers are read off a trajectory of the coupled
  level family. Driving the *real* `Ttc.run` off it,
  [`Ttc.card_run_eq_sum_traj`](Ttc/Coupling/Run.lean) proves `|𝒳| = ∑ₛ ω(J)ₛ`
  **pathwise**, at the run's own stopping level `J`, on every nested trajectory —
  and nestedness holds almost surely
  ([`Ttc.trajLaw_ae_nested`](Ttc/Coupling/Run.lean)). That is equality of random
  variables, strictly stronger than the equality in law `lem:process` supplies.
  Assembling it with the transported level estimates,
  [`Ttc.traj_numlattice_le`](Ttc/Coupling/Run.lean) proves `lem:numlattice`'s bound
  for that run outright, with a *smaller* right-hand side than the paper's (no
  `+ δ/2`, no factor `m`). **No probability claim is assumed in it**: its
  hypotheses are `hlo`/`hhi` (supplied by the already-proved `lem:lattice`),
  `hsmall`/`hrate` (conditions on `Thresh` and `vol`), `hall`/`hcov` (the cubes
  cover the lattice points; the coverage test agrees with cube membership) and
  `hpt` (the enumeration is injective) — read them off the signature rather than
  from this gloss, which is not a guarantee of completeness.
* **And the transport off the trajectory model is done.**
  [`Ttc.numlattice_union_of_model`](Ttc/Coupling/Transfer.lean) closes it: given
  `oracle_eq`, the run's failure event is the `toTraj`-preimage of the
  trajectory-space one; `Measure.le_map_apply` bounds its measure by the pushforward
  (no measurability of the event is needed — the inequality runs one way); and
  `law_eq` says that pushforward is `trajLaw θ`.

Two further things an auditor should not skip:

* **Termination is not assumed anywhere.** Both `while` loops are modelled as exit
  levels, and one might expect the result to need to know that the second loop
  actually exits. It does not: `traj_numlattice_le` holds whatever level the run
  reaches, because the coupling makes the output a function of that level and the
  `Err` estimate covers every level below the cap. The work is done instead by
  `traj_numlattice_le`'s `hsmall` hypothesis, that no cube's rate still triggers
  the first loop at level `j*−1`. That used to be the `rate_small` field; it is now
  *derived*. The paper addresses none of this.
* **What the exit-level model says on a non-terminating run.** `Nat.sInf` of an
  empty set is `0`, so if the absorption loop's guard never fails the model has the
  loop stay put rather than diverge. Nothing rests on that branch: every
  consequence drawn from an exit level has the form "every level strictly below it
  had the guard true" ([`Ttc.lt_haltLevel`](Ttc/Invariants.lean),
  [`Ttc.lt_absorbLevel`](Ttc/Invariants.lean)), which is vacuous there. This is
  deviation (b) of `Model/Pseudocode`.

**Exit levels, not fuel.** This page once said both `while` loops "take an explicit
iteration budget and return the current state when it runs out". That was
**wrong**, and is recorded here so the error is not reintroduced. They are
[`Ttc.haltLevel`](Ttc/Model/Pseudocode.lean) and
[`Ttc.absorbLevel`](Ttc/Model/Pseudocode.lean), each the *least level at or above
the current one at which the loop's guard fails* — an `sInf` over `ℕ`, not a
budget. No termination theorem is claimed, and claiming one would be false: the
second loop terminates only with high probability.

**The geometric fields are hypotheses about the input, and they are real.**
`ball_subset`, `volume_ne_top`, `normal_ne_zero`, `isPositive`, `cubes_le`,
`facets_le` are not consequences of anything here; they are what the paper assumes
of the decomposition (`ball_subset` verbatim, the rest implicitly). Two are worth
staring at:

* `isPositive` **excludes negated atoms**, which the paper's algorithm does not. A
  negated atom denotes an *open* half-space, and on a facet hyperplane the lattice
  count of a set and of its closure differ — so this is not a technicality volume
  arguments wash out. See README finding 5. Concretely: `lem:lattice` is proved
  here for positive DNFs only.
* `volume_ne_top` is implied by `ball_subset` plus boundedness, which the paper
  never states. It is assumed rather than derived.

**`L` is the lattice count, not a bare real.** The `L_eq` field pins it to
[`Ttc.normalisedCount`](Ttc/Lattice/Decomposition.lean) `= |Sol(F) ∩ 𝕃ⁿ|/10^(ρn)`, and
`lem:lattice` is proved about *that*.

**The oracle bundle constrains almost nothing — but `oracle_eq` does.**
[`Ttc.Oracles`](Ttc/Model/Pseudocode.lean) has **seven** fields: five are the
external calls (`vol`, `covered`, `thin`, `pois`, `gen`) and only two carry a
hypothesis —
`thin_le` (thinning returns a sub-multiset) and `gen_card` (`GenerateSamples`
returns exactly `N` points, for every precision `ρ`). Nothing in the *bundle*
states that `vol` is an accurate volume estimate, that `pois c λ` is
Poisson-distributed, or that `thin j₀ j'` keeps each element independently with
probability `2^(j₀−j')`. That is deliberate: it is what makes the bundle
inhabitable by `Ttc.trajOracles`. What supplies the distributional content is not
the bundle but `oracle_eq` and `law_eq`.

**The `level` is not in the pseudocode; `p` is.** `Ttc.SketchState` carries the
level `j` in place of the rate, with `p = 2^(−j)` a definition. An auditor
comparing against `algo.tex` will find `p`, not `j`. The index is present because
an *unindexed* oracle cannot model fresh randomness: an unindexed thinning applied
twice to the same multiset would return the same answer, so a thinning that
happened to be a no-op would freeze `𝒳` forever. Read the level as naming the draw
*and* carrying the paper's `p`.

**The coupling's definitions carry proving lemmas, not just names.**

| `def` | What the name promises | Proved by |
| --- | --- | --- |
| [`Ttc.levelLaw`](Ttc/Process/SketchProcess.lean) | the law of the level-`j` process | `Ttc.chainLaw_eq_levelLaw` — nested thinning from level `0` reproduces it at every `j` |
| [`Ttc.totalRate`](Ttc/Process/SketchProcess.lean) | the total rate at level `j` | definitionally `(∑ θ)/2ʲ`; used only through that |
| [`Ttc.famCount`](Ttc/Coupling/Family.lean), `Ttc.trajLaw` | the coupled family and its law | `Ttc.map_trajLaw_eval` — coordinate `j` carries exactly `levelLaw θ j`; `Ttc.trajLaw_ae_nested` — it is a *nested* thinning |
| [`Ttc.trajOracles`](Ttc/Coupling/Family.lean) | oracles that read the family | it is a `Ttc.Oracles`, so both interface contracts are discharged in the definition; that the *run* it drives realises the family is `Ttc.card_run_eq_sum_traj` |
| [`Ttc.CoupledAt`](Ttc/Coupling/Run.lean), [`Ttc.PoisAt`](Ttc/Coupling/Run.lean) | "the state is the family here" | preserved by every loop operation (`Ttc.coupledAt_thin`, `coupledAt_step`, `coupledAt_foldl`) and read off by `Ttc.count_of_coupledAt` |
| [`Ttc.haltLevel`](Ttc/Model/Pseudocode.lean), [`Ttc.absorbLevel`](Ttc/Model/Pseudocode.lean) | "the level the `while` loop exits at" | `Ttc.le_haltLevel`/`le_absorbLevel` — it is at or above the entry level; `Ttc.lt_haltLevel`/`lt_absorbLevel` — every level strictly below it had the guard true |
| [`Ttc.Box.Lval`](Ttc/Witness/BoxProb.lean) | the witness's normalised lattice count | it is `Ttc.normalisedCount` by definition, and `Ttc.Box.side_le_Lval` proves `Thresh ≤ c ≤ L` |
| [`Ttc.Box.th`](Ttc/Witness/BoxProb.lean) | the witness's rates | `Ttc.Box.sum_th` — they total `L` exactly |
| [`Ttc.KV97Sampler.contVol`](Ttc/Sampler/Interface.lean) | "the volume `contLaw` is normalised against" | **now a field equation**, `contVol_eq`, not a naming convention. Under the old density interface this identification was *not* made and was argued to be unnecessary; under TV it is necessary and is asserted |
| [`Ttc.Box.cleanProb`](Ttc/Exec/Budget.lean) | "the box run's accuracy probability at the clean budget" | **checked, and harmless.** It is a `def` — the transcribed `∫⁻ … ∂(MonteCarlo.coins n)` — and it **asserts nothing**: [`Ttc.Box.cleanProb_def`](Ttc/Exec/Budget.lean) proves it equal to the integral in `Ttc.Box.ttc_volume_clean_box_at`'s accuracy conjunct **by `rfl`**. Its only purpose is to let the numeral instances of §3f state the achieved bound without retranscribing the integral. Note its `δ` argument is the *internal* `δ₀`; the lemmas always feed it `4 * δ / 5` |
| [`Ttc.Box.cleanAcc`](Ttc/Exec/Budget.lean) | the same as a real | `(cleanProb …).toReal`, definitionally. No further claim; §3f's `> 0` results are what give it content |
| [`Ttc.canonAm`, `Ttc.canonBv`, `Ttc.canonDm`, `Ttc.canonRfac`](Ttc/Exec/CanonPolytope.lean) | "the canonical linear description of the dilated regions" | proved, not named: [`Ttc.canon_body_eq_smul_region`](Ttc/Exec/CanonPolytope.lean) is an **equality** of the body with `s • region …`, [`canon_dist_le_canonDm`](Ttc/Exec/CanonPolytope.lean) is the diameter bound, and `canonRfac` is the facet count on the nose (`Fintype.card (Fin N) = N`), so `hcard` holds with equality |

The one place a name is doing work no lemma checks is
[`Ttc.padPoint`](Ttc/Coupling/Family.lean), the filler `trajOracles.gen` returns
when asked for a count the family cannot supply. That branch is never taken by the
run — `gen` is always passed the `N` that `pois` produced — and nothing downstream
depends on what it contains; it exists so that `gen_card` holds unconditionally.

**`GetPrecision` is a formula, not an algorithm — but it is not inert.** `γ̂` is
still an input: the LP of `alg:prec` that computes the largest inscribed ball, and
the loop taking the max over polytopes, are **not modelled**. What *is* proved is
that the precision it returns is exactly what the accuracy proof needs:
[`Ttc.gamma_le_latticeScale_mul`](Ttc/Lattice/Assembled.lean) shows
`ρ = ⌈log₁₀(γ/γ̂)⌉` makes `10^ρ·γ̂ ≥ γ`, which gives the *dilated* polytopes the
inscribed radius `lem:nonconv` requires. So `rho_eq` is load-bearing: delete it and
`lem:lattice` no longer goes through.

**The parameter block is a transcription, checkable only by eye.** The constants in
[`Ttc.Params`](Ttc/Model/Prelude.lean) — `η`, `ε'`, `Thresh`, `γ`, `ρ`; `κ` is `lem:nonconv`'s constant and lives in [`Constants/Parameters`](Ttc/Constants/Parameters.lean) —
assert by their definitions that they are what `alg:ttc` (lines 17–20) and
`alg:prec` (line 86) compute. Read them beside `sections/algo.tex`. `κ` and `γ`
enter `lem:lattice` through
[`Ttc.Params.shell_factor_bound`](Ttc/Constants/Parameters.lean) and
`shell_factor_bound_deflated`, both **reached** by the headline; so are
`Ttc.Params.kappa_div_gamma_le` and `Ttc.gamma_le_latticeScale_mul`.
`Ttc.TtcProb.numlattice` reads `ε'` and `Thresh` off the block and feeds them to
`Ttc.numlattice_failure_le`, also reached. `Ttc.Params.epsPrime_window` is **not**
reached. Re-check all of this with the probe in §5 rather than taking it on trust.

---

## 5. Re-checking the machine-checkable part

```bash
lake exe cache get && lake build     # zero "declaration uses 'sorry'" warnings
```

> **A build caveat that has already caused a false all-clear.** The `Ttc` lean_lib
> declares **no `globs`**, so `lake build` compiles only what `Ttc.lean`
> transitively imports: a `.lean` file under `Ttc/` that nothing imports is **never
> built at all**, and `import Ttc` cannot reach it. `Arlib` *does* declare
> `globs = ["Arlib", "Arlib.+"]`, so an unwired file under `Arlib/` still gets
> built but is invisible to `import Arlib`. Those two failure modes look identical
> in a report and are not the same. Check for orphans before trusting a sweep:
>
> ```bash
> # every Ttc/Arlib module, minus every module named in an import — the difference is orphans
> comm -23 \
>   <(find Ttc Arlib -name '*.lean' | sed 's|/|.|g;s|\.lean$||' | sort) \
>   <(grep -rhE '^import (Ttc|Arlib)' Ttc.lean Arlib.lean Ttc/ Arlib/ \
>     | sed 's/^import //' | sort -u)
> ```
>
> **Re-run it; never read a list of orphans off this page.** The answer changes
> within the hour — it normally names whatever some agent is mid-way through
> landing, and it named a different file on each of several consecutive revisions
> of this page. (One of those runs was over `Ttc.Exec.CanonicalPolytope` versus
> `Ttc.Exec.CanonPolytope`, **two names differing by four letters**, with the roles
> reversed between revisions; that is how a wrong entry survived three rewrites.
> `CanonicalPolytope` has since been deleted, after being checked against
> `CanonPolytope` and found to agree except that `CanonPolytope`'s crux
> `canon_body_eq_smul_region` holds for *every* `s > 0` rather than only at
> `s = latticeScale ρ`.) At the last run it reported one orphan, `Ttc.Probability`,
> a subtree being landed as this was written and therefore **not compiled by
> `lake build` at all**. `Ttc.lean` does import `Ttc.Exec.EndToEnd`,
> `Ttc.Exec.Budget`, `Ttc.Exec.CanonPolytope` and `Ttc.Exec.Final`, so §1c's and
> §1d's capstones *are* inside the build graph.
> **Nothing an orphan contains may be cited as proved**, whether or not an `.olean`
> exists for it — under `Arlib`'s globs one usually does.
>
> One wrinkle worth knowing: `comm` needs both inputs sorted in the *same*
> collation. Run the pipeline under `LC_ALL=C`, or it emits
> `comm: file 1 is not in sorted order` and a wrong difference.

```lean
import Ttc
#print axioms Ttc.TtcProb.volume_estimate
-- [propext, Classical.choice, Quot.sound]
#print axioms Ttc.TtcProb.lattice_lo
#print axioms Ttc.TtcProb.numlattice
#print axioms Ttc.TtcProb.numlattice_union      -- the ex-field
#print axioms Ttc.TtcProb.samp_unif             -- the ex-field: eq:almostuniform
#print axioms Ttc.TtcProb.theta_lo              -- the ex-field
#print axioms Ttc.TtcProb.theta_hi              -- the ex-field
#print axioms Ttc.TtcProb.thresh_pos            -- Thresh > 0, no longer implicit
#print axioms Ttc.TtcProb.vol_lt_two_total      -- a cube's rate < twice the total
#print axioms Ttc.traj_numlattice_le
#print axioms Ttc.ttc_volume                     -- the structure-free capstone
#print axioms Ttc.Box.boxProb                    -- the non-vacuity witness
#print axioms Ttc.Box.nonempty_ttcProb
#print axioms Ttc.Box.ttc_volume_box             -- ttc_volume's witness
#print axioms Ttc.ttc_volume_endToEnd            -- §1c: no oracle binders
#print axioms Ttc.e2eSampler                     -- its law_tv is a theorem
#print axioms Ttc.VolumeAlgorithm.monteCarlo     -- the constructed volume oracle
#print axioms Ttc.Box.ttc_volume_endToEnd_box_at -- §3e: the witness
#print axioms Ttc.Box.exists_two_ttc_volume_endToEnd_instances
#print axioms Ttc.Box.bxRates_pos                -- rates not collapsed to 0
#print axioms Ttc.Box.endToEnd_box_lintegral_pos_ne_top   -- not toReal ⊤ = 0
#print axioms Ttc.ttc_volume_final               -- §1d: THE result — no oracle, no
                                                 --   polytope description, clean 1 − δ
#print axioms Ttc.ttc_volume_endToEnd_canon      -- §1d: description binders gone
#print axioms Ttc.canon_body_eq_smul_region      -- §1d's crux: body = s • region
#print axioms Ttc.ttc_volume_clean               -- §1d: the repricing, one rung lower
#print axioms Ttc.ttc_volume_endToEnd_delta      -- legacy alias for the above
#print axioms Ttc.Box.ttc_volume_clean_box_at    -- §3f: the clean-budget witness
#print axioms Ttc.Box.clean_box_at_nine_tenths   -- §3f: bound 1/10 > 0 at δ = 9/10
#print axioms Ttc.Box.old_budget_vacuous_at_nine_tenths -- §3f: −1/8 ≤ 0, in the library
#print axioms Ttc.Box.clean_box_prob_pos_ne_top_at_nine_tenths -- not toReal ⊤ = 0
#print axioms Ttc.Box.exists_two_ttc_volume_clean_instances
#print axioms Ttc.Box.cleanProb_def              -- §4: the def asserts nothing (rfl)
#print axioms Ttc.TwoCube.ttc_volume_final_two_cube      -- §3g: ttc_volume_final ITSELF,
                                                 --   on a TWO-cube DNF, big included
#print axioms Ttc.TwoCube.ttc_volume_final_two_cube_at   -- §3g: 1/10 at δ = 9/10, and 3/4
#print axioms Ttc.TwoCube.card_toDNF_eq_two      -- §3g: EXACTLY two cubes (an equality)
#print axioms Ttc.TwoCube.sol_eq_union_two       -- §3g: two distinct disjoint regions
#print axioms Ttc.TwoCube.cenT_left_ne_right     -- §3g: the two ball centres differ
#print axioms Ttc.TwoCube.min_qT_le_ratesT       -- §3g: big at m = 2, by cases on cubeAt
#print axioms Ttc.TwoCube.volume_sbx             -- §3g: the shifted box's exact volume
#print axioms Ttc.TwoCube.twoProb_pos_ne_top_at_nine_tenths -- §3g: not toReal ⊤ = 0
#print axioms Ttc.ttc_volume_estimate            -- §1e: the eleven-binder headline
#print axioms Ttc.hvol_scaled                    -- §1g: the dilation discharges hvol
#print axioms Ttc.ball_subset_cenOf              -- §1g: the constructed ball, uncond.
#print axioms Ttc.sol_cleanForm                  -- §1g: the cleanup is a set EQUALITY
#print axioms Ttc.ttc_volume_cleanInput          -- §1g: hcoeff gone, nothing added
#print axioms Ttc.hint_not_derivable             -- §1g: hint is not derivable
#print axioms Ttc.not_isDNFOf_nondegenCubes_degForm -- §1g: and the repair is blocked
#print axioms Ttc.Independence.exists_isBounded_not_isPositive   -- §1g: hbdd ⊬ hφ
#print axioms Ttc.Independence.exists_isPositive_not_isBounded   -- §1g: hφ ⊬ hbdd
#print axioms Ttc.exists_latticeCount_ne_of_open -- §1g: what dropping hφ would cost
#print axioms Ttc.TwoCube.ttc_volume_estimate_two_cube_full -- §1e: non-vacuity, now
```

All 28 declarations of `Ttc/Exec/EndToEnd.lean` report
`[propext, Classical.choice, Quot.sound]`; the file itself ends with a block that
prints them, so `lake build Ttc.Exec.EndToEnd` re-checks the whole set without
your writing anything.

```bash
# the greps drop docstrings that quote the words in backticks
grep -rnE "\bsorry\b|\badmit\b|native_decide|sorryAx|^axiom " \
  Ttc.lean Ttc/ Arlib.lean Arlib/ | grep -v '`sorry`' | grep -v '`sorryAx`'
```

**This does not return nothing, and that is expected.** It returns exactly two
lines, both English prose and neither Lean: `Ttc/Exec/Coverage.lean` and
`Ttc/Exec/Endgoal.lean` each contain the sentence "`CLAUDE.md` §4 does not admit
an unchecked proof", and `\badmit\b` matches the bare verb. Earlier revisions of
this page said the command "must return nothing", which was true when they wrote
it. **Read the hits rather than tightening the pattern until they disappear** — a
pattern tuned to produce silence stops being a check. `#print axioms` above and the
README's full-development sweep are the authoritative tests; both are clean, and
`lake build` emits zero `declaration uses 'sorry'` warnings.

See the README's [Verifying the claim](README.md#verifying-the-claim) for the
full-development axiom sweep.

### Read the assumptions off the compiled structure, not off the file

This is the check that catches the failure mode §2 warns about — docstrings in
`Ttc/TtcProb.lean` quote field-shaped Lean, so `grep` over-reports.

```lean
import Ttc
open Lean in
run_cmd do
  let env ← Lean.getEnv
  for s in [`Ttc.TtcProb, `Ttc.KV97Sampler, `Ttc.VolumeAlgorithm, `Ttc.Oracles] do
    let fs := Lean.getStructureFields env s
    Lean.logInfo m!"{s}: {fs.size} fields: {fs.toList}"
```

Expected at the time of writing: `Ttc.TtcProb` **59**, `Ttc.KV97Sampler` **15**,
`Ttc.VolumeAlgorithm` **7**, `Ttc.Oracles` **7**. If the numbers differ, §2's table
is stale and this command's output — not the table — is the truth.

### Count the capstones' binders

```lean
import Ttc
open Lean in
partial def cntF : Expr → Nat
  | .forallE _ _ b _ => cntF b + 1
  | _ => 0
open Lean in
run_cmd do
  let env ← Lean.getEnv
  for n in [`Ttc.ttc_volume, `Ttc.ttc_volume_toDNF,
            `Ttc.ttc_volume_endToEnd, `Ttc.ttc_volume_endToEnd_canon,
            `Ttc.ttc_volume_clean, `Ttc.ttc_volume_final] do
    Lean.logInfo m!"{n}: {cntF (env.find? n).get!.type} top-level binders"
```

**This counts the raw type**, which includes the two implicit ambient parameters
`{A}` and `{n}` from the `variable` line. So `Ttc.ttc_volume_final` reports **28**,
against the **26 explicit** binders §1d lists and a caller must supply — the same
`raw = explicit + 2` relation §1b explains for `Ttc.ttc_volume`. Quote whichever
you like, but say which.

Add `` `Ttc.ttc_volume_estimate `` to the list and it reports **13 raw**: the two
implicits and the **eleven** binders §1e lists
(`atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos`). `raw = explicit + 2` holds for this
theorem again.

> ⚠ **Corrected 2026-08-12, twice over, and the history is worth keeping.** This
> paragraph used to report **15 raw** — the two implicits, the eleven, and the two
> per-call cost constants `cVol`/`cSample` — and to conclude that
> `raw = explicit + 2` was *wrong* for this theorem, scolding an earlier revision for
> quoting "11 explicit / 13 raw" by applying the relation instead of running the
> probe. `cVol`/`cSample` are no longer binders (§1e's box), so the earlier revision's
> arithmetic is now the right answer, reached the wrong way. **Run the probe.** The
> claim "11 and 13" on this page is a report of a build the author ran, not a
> derivation, and it goes stale the moment a binder moves.

For `Ttc.ttc_runtime_mn4` (§0a) do **not** use this probe: `RuntimeMN4.lean` ships
`#binderProfile`, which splits the raw count by `BinderInfo` and prints
`68 raw = 64 explicit + 2 implicit + 2 instance` at build time. `cntF` above would
report only the `68`, and 4 of those are not obligations anyone discharges.

### Re-check the `Model/` boundary yourself

This is the by-hand form of the check behind the top-of-page claim that the
headline's *type* names nothing outside `Model/`. The build already runs the
stronger version — `#modelClosureOfType Ttc.ttc_volume_estimate` in
[`Ttc/Audit/ClosureCheck.lean`](Ttc/Audit/ClosureCheck.lean) walks the whole
definitional closure and **throws**, where this probe only reads the conclusion's
direct names and only reports. Run this one when you want to see the list; rely on
the build for the guarantee. Both are worth re-running after **any** move between
`Model/` and `Exec/`.

```lean
import Ttc
open Lean in
run_cmd do
  let env ← Lean.getEnv
  let some ci := env.find? `Ttc.ttc_volume_estimate | throwError "missing"
  let mut t := ci.type
  while t.isForall do t := t.bindingBody!
  let mut bad : Array Name := #[]
  for c in t.getUsedConstants do
    if let some m := env.getModuleFor? c then
      let ms := m.toString
      if ms.startsWith "Ttc" && !ms.startsWith "Ttc.Model" then bad := bad.push c
  Lean.logInfo m!"named outside Ttc.Model: {bad.toList}"
```

It walks past the binders, collects the constants of the **conclusion**, and keeps
those whose defining module is under `Ttc` but not under `Ttc.Model`. Mathlib names
are filtered out by the `Ttc` prefix test, so what comes back is exactly the
project's own leakage.

**What it reported when this was written: the empty list.** The sample-coin law
`Ttc.trajLaw`, the volume-coin law `Ttc.MonteCarlo.coins`, the constructed
sampler's law and the canonicalisation data are all still *named* by the statement
— they were moved into `Model/`, which is why they no longer show up here. The cost
of that move is that `Model/Prelude` imports `Arlib`, so `Model/` is no longer
readable before the probability and convex-geometry development. That trade is the
opposite of the reference layout's, where nfalean keeps `countNFAExec`
(`ApproxNFA/Algorithm/Faithful.lean`) outside `ApproxNFA/Model/` and accepts the
leak instead.

**What would indicate a leak**, and what each would mean:

* `Ttc.TtcProb`, `Ttc.KV97Sampler` or `Ttc.VolumeAlgorithm` — a *hypothesis bundle*
  back in the statement. This is the one that matters: it would mean the headline
  had reacquired an assumed oracle or an assumed sampler, and §1c's whole point
  would be gone from the statement layer.
* An `Exec/` definition of the **algorithm's own data** — the preprocessed input,
  the dilation factor, the parameter block, the precision, the converter. These
  belong in `Model/Pseudocode` under the target layout; finding one here means the
  algorithm is being described from two places, which is the arrangement that lets
  the statement and the transcription drift apart silently.
* Anything from `Exec/Final`, `Exec/Budget`, `Exec/EndToEnd` or the probabilistic
  development — proof machinery in the statement. `Ttc.ttc_volume_api`'s proof may
  reach all of it; the *type* must not.

An empty answer is **not** the target and should be treated with suspicion rather
than satisfaction: it would mean the probability space had been re-declared inside
`Model/`, and `Model/` would then no longer be a layer you can read before the rest
of the development. Note also what the probe does not do: it says nothing about
what the named terms **unfold to**. That is §1h's definitional closure, and no
probe replaces reading it.

### Which results does the headline actually reach?

Paste this into a file and `lake env lean` it; it walks the headline's transitive
constant set and reports membership. **An import only says a file is visible, not
that any of its results is used** — the walk is what settles it, and it is the
check to re-run after any refactor.

```lean
import Ttc
import Arlib
open Lean in
run_cmd do
  let env ← Lean.getEnv
  let mut seen : Lean.NameSet := {}
  let mut todo := [`Ttc.TtcProb.volume_estimate]
  while !todo.isEmpty do
    let n := todo.head!; todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      for c in ci.getUsedConstantsAsSet do todo := c :: todo
  let names := seen.toList
  Lean.logInfo m!"reached {names.length}; Arlib.*: \
    {(names.filter (fun n => (`Arlib).isPrefixOf n)).length}"
  for t in [`Ttc.TtcProb.numlattice, `Ttc.TtcProb.numlattice_union,
            `Ttc.traj_numlattice_le, `Ttc.trajLaw, `Ttc.exists_epoch,
            `Ttc.TtcProb.thresh_pos, `Ttc.TtcProb.vol_lt_two_total,
            `Ttc.numlattice_failure_le, `Ttc.Params.shell_factor_bound,
            `Ttc.Params.shell_factor_bound_deflated, `Ttc.Params.kappa_div_gamma_le,
            `Ttc.gamma_le_latticeScale_mul, `Ttc.prodKernel_claim_cl_b,
            `Ttc.Params.epsPrime_window, `Ttc.TtcProb.samp_unif,
            `Ttc.TtcProb.theta_lo, `Ttc.TtcProb.theta_hi,
            `Arlib.KV97.theorem2, `Arlib.TVLe,
            `Ttc.almostUniform_of_kv97_law, `Ttc.almostUniform_of_kv97_density,
            `Ttc.ttc_volume, `Ttc.VolumeAlgorithm.cousinsVempala] do
    Lean.logInfo m!"{t} reached: {seen.contains t}"
```

**What it reports at the time of writing, and what each answer means:**

| Result | Reached | Reading |
| --- | --- | --- |
| `numlattice`, `numlattice_union`, `traj_numlattice_le`, `trajLaw`, `exists_epoch`, `thresh_pos`, `vol_lt_two_total`, `numlattice_failure_le` | **true** | the coupling and `lem:numlattice` are load-bearing |
| `shell_factor_bound`, `shell_factor_bound_deflated`, `kappa_div_gamma_le`, `gamma_le_latticeScale_mul`, `prodKernel_claim_cl_b` | **true** | "the constants are verified" and "the theorem holds" meet for `η`, `κ`, `γ`, `ρ` |
| `samp_unif`, `theta_lo`, `theta_hi` | **true** | the ex-fields really are derived, not merely restated |
| **`Arlib.KV97.theorem2`, `Arlib.TVLe`, `Ttc.almostUniform_of_kv97_law`** | **true** | **KV97 is on the headline's path.** 150 `Arlib.*` declarations are reached, 29 of them `Arlib.KV97.*` (re-measured; an earlier revision said ~137) |
| `Ttc.almostUniform_of_kv97_density` | **false** | proved, but **no longer load-bearing** — its hypothesis is a pointwise *density* and the interface no longer has one. Retained for the pointwise route; do not cite it as live |
| `Ttc.Params.epsPrime_window` | **false** | proved, off the path |
| `Ttc.ttc_volume`, `Ttc.VolumeAlgorithm.cousinsVempala` | **false** | siblings/future work, not steps of this proof |

**A correction this page has had to make twice, in opposite directions.** An old
version reported `Ttc.traj_numlattice_le` as `false` and warned against treating
the coupling as load-bearing; that warning was withdrawn when it went `true`.
A later version implied `Arlib.KV97.ratio_bounds_tuned_sharp` was on the path; it
is now **`false`**, because the TV migration replaced the pointwise route it
belonged to. The lesson is the same both times: **run the walk, don't read the
import graph, and don't trust this table over the walk.**

### The same walk from the oracle-free capstone

**Seed it at `` `Ttc.ttc_volume_final `` — §1d's statement — for the strongest
version of this question.** The numbers below were measured from
`` `Ttc.ttc_volume_endToEnd_delta `` (= `Ttc.ttc_volume_clean`) and from
`` `Ttc.ttc_volume_endToEnd ``; `ttc_volume_final` sits above both, reaching
`ttc_volume_endToEnd_canon` and through it everything in the tables below, so every
`true` row is inherited and every `false` row has to be **re-checked, not assumed**
— a constant off one route can be on another. Re-run the walk at the seed you
intend to quote; the counts in particular will have moved.

Re-seeding `todo` changes the question: not "is the coupling load-bearing" but
**"are the constructed oracles the ones actually being used, or is something
idealised sneaking in?"** From `` `Ttc.ttc_volume_endToEnd_delta `` that walk
reaches **52645** constants and reports:

| Result | Reached | Reading |
| --- | --- | --- |
| `Ttc.VolumeAlgorithm.monteCarlo`, `Ttc.mcVol`, `Ttc.MonteCarlo.coins` | **true** | the volume oracle in use is the *constructed* one |
| `Ttc.e2eSampler`, `Ttc.e2eSampD`, `Ttc.kv97SamplerOfBody`, `Ttc.kv97ContLaw` | **true** | the sampler in use is the constructed lazy ball walk |
| `Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope` | **true** | `law_tv` really is discharged by the mixing stack, not restated |
| `Arlib.uniformOn_iso_of_convex`, `Arlib.KV97.theorem2` | **true** | isoperimetry and KV97 are both on the path |
| **`Ttc.VolumeAlgorithm.exact`** | **false** | **the anti-cheat that matters.** The idealised zero-error oracle is *not* used anywhere beneath the capstone, so the result is not a perfect-oracle result in disguise |
| `Ttc.VolumeAlgorithm.cousinsVempala` | **false** | the *assumed* Cousins–Vempala oracle is off the path; the Monte-Carlo construction replaced it |

The last two rows are the point of running this walk at all. A reader who checks
only `#print axioms` cannot distinguish "the oracle was constructed" from "the
oracle was assumed to be exact" — both are axiom-clean. Only the walk separates
them.

**The same walk, re-seeded at `` `Ttc.ttc_volume_endToEnd `` itself** — §1c's
statement, one step below the `_delta` reparametrisation — reaches **52644**
constants, **432** of them `Arlib.*` and **35** `Arlib.KV97.*`. It confirms every
row above and settles four more questions:

| Result | Reached | Reading |
| --- | --- | --- |
| `Ttc.ttc_volume_monteCarlo`, `Ttc.ttc_volume_endToEnd_ofSampler` | **true** | the composition really is applied, not restated |
| **`Ttc.TtcProb.volume_estimate`** | **true** | **this is a chain on §1's capstone**, not a sibling wearing its title — the check "Checks a green build does not perform" item 3 exists for |
| **`Ttc.ttc_volume`** | **false** | the *constant* is not in the proof term: the route runs `volume_estimate → ttc_volume_monteCarlo → endToEnd`, and `ttc_volume` is a parallel restatement. So "`endToEnd` is `ttc_volume` with the oracles removed" is a claim about the **text of the two types**, to be checked by eye; the machine does not certify it |
| `Ttc.ttc_volume_rates` | **false** | its *ingredients* (`Ttc.rates`, `theta_eq_rates`, `gen_mem_of_geometry`) are used; the packaged corollary is not |
| `Arlib.uniformOn_iso_unitBall` | **false** | only the general convex-body isoperimetric inequality is on the path, not the unit-ball special case |
| `Ttc.Params.epsPrime_window`, `Ttc.almostUniform_of_kv97_density` | **false** | still off the path, exactly as for the older capstone |

**And re-seed it once more at `` `Ttc.TwoCube.ttc_volume_final_two_cube ``**, §3g's
witness. That walk reports `Ttc.ttc_volume_final` **`true`** — which is the check
that the witness instantiates the strongest statement rather than a restated
weaker one — and likewise from `` `Ttc.TwoCube.ttc_volume_final_two_cube_at ``.
`Arlib.uniformOn_iso_of_convex`, `Ttc.VolumeAlgorithm.monteCarlo` and
`Ttc.kv97SamplerOfBody` all come back `true` from it too, so the whole constructed
chain is live *through the witness* and not only through the theorem.

Two numbers to read carefully rather than quote. **52644 versus 52645** is the
one-node difference between the two roots, not a discrepancy. And **432 `Arlib.*`
declarations** against the **150** reported for the walk from
`Ttc.TtcProb.volume_estimate` measures how much of the mixing/isoperimetry stack
the constructed sampler drags in — it is a statement about *breadth of
dependency*, and specifically **not** evidence about efficiency or about how much
of Cousins–Vempala is formalised.

### The same walk from the statement layer, `Ttc.ttc_volume_estimate`

Re-seed `todo` at `` `Ttc.ttc_volume_estimate `` — §1e's theorem, the one `Model/`
states — and the walk reaches **53700** constants, **433** of them `Arlib.*`, and
every row of the two tables above is reproduced.  (`Ttc.ttc_volume_final` reaches
**52679** / **433**, so the statement layer is the larger of the two, not a
restatement inside it.)  Every figure in this section was re-measured together;
the previous revision's 52629 / 52630 / 52694 and 419 / 420 were one refactor
behind, which is the normal state for these numbers:

| Result | Reached | Reading |
| --- | --- | --- |
| `Ttc.VolumeAlgorithm.monteCarlo`, `Ttc.mcVol`, `Ttc.MonteCarlo.coins` | **true** | the volume oracle is the constructed one |
| `Ttc.e2eSampler`, `Ttc.e2eSampD`, `Ttc.kv97SamplerOfBody`, `Ttc.kv97ContLaw` | **true** | the sampler is the constructed lazy ball walk |
| `Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope`, `Arlib.uniformOn_iso_of_convex`, `Arlib.KV97.theorem2` | **true** | mixing, isoperimetry and KV97 are all load-bearing |
| `Ttc.Params.precision` | **true** | the precision really is `GetPrecision`'s output, in the *type* as well as the proof |
| `Ttc.TtcProb.volume_estimate` | **true** | the bundle theorem moved out of `Model/` but is still what this rests on |
| **`Ttc.VolumeAlgorithm.exact`** | **false** | the anti-cheat: the idealised zero-error oracle is not used |
| `Ttc.VolumeAlgorithm.cousinsVempala` | **false** | the *assumed* CV oracle is off the path |

Removing `T.O` and `T.ρ` from the statement therefore did **not** quietly swap in a
different oracle: the same constructed ones are reached, and the same idealised one
is not.

### Do the names on this page still exist?

The claim at the top — that every name here was checked against the compiled
environment — is worth re-running after any refactor, and it is one `run_cmd`:
scrape the backticked `` `Ttc.* ``/`` `Arlib.* `` names out of `README.md`,
`AUDIT.md` and `Ttc.lean`, and report those for which `env.find?` is `none`.
Of the 300 names cited at the time of writing, it flags 62 — and **almost all of
those flags are not bugs**, which is the part to get right before acting on it:

* **Module names** (`Ttc.Capstone`, `Arlib.Convexity`, …) are files, not
  constants; `env.find?` will never see them. Filter them by testing whether the
  dotted name is a `.lean` path.
* **`export` aliases are invisible to `env.find?`.** `Ttc.tent` resolves — to
  `Arlib.Lattice.Rounding.tent` — but is not a constant of that name, so the probe
  reports it missing. Confirm with `#check` before believing the probe.
* **Deliberate historical references** (`Ttc.trivialProb`, `Ttc.OracleLaws`) are
  cited precisely to say they were deleted.

After filtering, the run found exactly one real defect: two citations of
`Ttc.monteCarlo_est_ne_volume` that should have been
`Ttc.MonteCarlo.monteCarlo_est_ne_volume` — a wrong namespace, not a wrong name,
which is the failure mode a reader is least likely to catch by eye. Both are
fixed above. The lesson is the shape of the check, not its result: a name probe
whose false-positive rate is 98% is still worth running, provided you classify
before you edit.

> **Scratchpad hazard, met while producing the table above.** The first run of this
> probe was written to a shared scratchpad path that a concurrently-running agent
> overwrote between the write and the run, so the output that came back was a
> *different probe's* — with a different, unstated root. It was internally
> plausible and would have been easy to report. Give probe files unique names, and
> make the probe **print its own root**, as the version above does.

---

## Checks that a green build does not perform

`CLAUDE.md` §4's three checks — `#print axioms`, zero `sorry` warnings, a grep sweep
— establish that the proofs have no holes. They do **not** establish that the right
statement is proved, and the failure modes below all survive a green, `sorry`-free,
axiom-clean build indefinitely. Each was found in this tree; none would have been
caught by running the standard checks harder.

**1. Coverage — does `lake build` compile the file at all?** This depends on the
library, and the two regimes fail in opposite directions:

* `Ttc` has **no `globs`**, so an unwired file is *never compiled*. Verified
  directly, not inferred: a deliberately broken unimported file under `Ttc/` left
  `lake build Ttc` at exit 0 and the **same job count**. `Ttc/Exec/Coverage.lean`
  sat finished and green on disk for hours this way.
* `Arlib` **has `globs`**, so an unwired file is compiled (it cannot silently rot)
  but stays unreachable from `import Arlib` — and an in-progress file breaks the
  whole library target for reasons unrelated to any proof.

An `.olean` existing proves neither reachability nor coverage. Note also that
elaborating a file directly (`lake env lean`) passes for files outside the build
graph, so it is orthogonal to coverage in exactly the direction that hides the gap.
This is the worst of the seven, because the reassuring signal and the missing coverage
come from the *same command*: running it more often increases confidence about
precisely the files it cannot see.

**2. Load-bearingness — is the result actually used?** An import proves a file is
*visible*, never that anything in it is *used*. §5's walk from the capstone's proof
term via `getUsedConstantsAsSet` is the check. It has caught a result everyone
assumed was on the headline path and was not.

**3. Containment is not subsumption.** Comparing two capstones' closures tells you
less than it appears to. The same subset relation can mean "B is built on A" (a
chain) or "A and B are siblings sharing a branch". Here `ttc_volume`'s closure
strictly contains `volume_estimate`'s **because it is built on it**; in a sibling
repo the identical relation held between two theorems where *neither* reached the
other. A one-directional reachability check cannot distinguish these — walking from
A gives `false` in both cases — and an earlier revision of this file drew the wrong
conclusion from exactly that.

*Diagnostic:* the self-inclusion off-by-one lands on whichever side the reachability
does **not** run. Chain — nothing missing, and the surplus silently includes the
start node, so a reported `n` extras is substantively `n − 1`. Siblings — each
closure holds its own theorem, and the smaller one's sole leftover is exactly that.
So the shape of the off-by-one reveals the structure before a second walk is run.

**4. Non-vacuity is not enough — a bundle can be inhabited yet *forced*.** The
witness may satisfy the hypotheses only by collapsing a quantity the surrounding
argument treats as free. `#print axioms` is blind to this because nothing is ever
*asserted*: the degeneracy lives in *which objects* satisfy the hypotheses. Two
instances in this tree, both fixed:

* `exists_unconditional_mixing_unitBall` started the walk at its **own stationary
  measure**, so `MixesWithin` held for reasons unrelated to anything the file proves;
* `Ttc.Box.ttc_volume_box` runs at `ε = δ = 1`, making its accuracy conjunct
  `0 ≤ …`. `Ttc.Box.ttc_volume_box_accuracy_is_trivial` proves that conjunct
  *verbatim* without mentioning `ttc_volume` at all — a machine-checked demonstration
  that it carries zero information.

*The check:* a **pair** of inhabitants differing in the parameter, structurally where
possible (`Arlib.TVWitness` gives one atomic and one absolutely continuous law, so
inhabitation provably does not depend on the atom). A pair is a property of two
objects, so unlike "make the coefficients non-degenerate" it needs no prior guess
about which coefficient matters — exhibit the pair and the parameter is provably
free; fail, and the failure *is* the finding.

*A third dimension of the same failure, and the one this tree was slowest to
close:* the **arity** of the instance. Every witness in §3a–§3f is a one-cube DNF,
so until §3g landed `m` was forced at `1` in every witness the development had,
while the theorems quantified over all `m` — and a pair of instances differing in
`(ε, δ)` says nothing
about that, because the parameter it varies is the wrong one. §3g is the fix, and
it is what makes the fix visible: `Ttc.TwoCube.card_toDNF_eq_two` is an equality to
`2`, not a `2 ≤ …`, precisely so that the anti-degeneracy content is a theorem and
not an inference from a construction.

*Better than the check:* an interface constraint making the degenerate instance
**inexpressible** rather than merely discouraged. The pair check must be remembered;
a constraint holds whether or not anyone looks. On the evidence so far the pair check
earns its keep mainly as a detector for *missing interface constraints* — one level
up from the parameter — rather than for forced coefficients, which tend to be visible
in the field list anyway.

**5. Quote the cost with the result, in the docstring of the result.** A bound
validated at convenient parameters and stated without a range is a scope claim
disguised as a theorem. Ask what the bound does at the **consumer's** parameters, not
at the ones that are easy to check.

*Two distinct shapes, with different remedies.* A route that **degrades** — weaker
asymptotically, failing at a computable crossover — wants the range stated. A route
with a **floor** — a fixed bias that no amount of the natural resource buys you out
of — wants abandoning. Finding 19 is the second kind and the route was abandoned.

*Failure mode to expect:* when a result is proved in one file and consumed in
another, the caveat reliably ends up in the **composing** file only, because that is
where the cost feels relevant while writing. Quotation follows the *statement*, so
the caveat must be duplicated into the proving file even though that is redundant for
anyone reading top to bottom. `Arlib/Convexity/IsoBall.lean` had exactly this defect:
its theorems said "no hypotheses, unconditionally" and the exponential constant was
documented three files away.

**6. Infrastructure claims deserve *more* scrutiny than mathematical ones**, not
less. They feel like observations rather than assertions, which is backwards — a
wrong build-system belief silently invalidates whatever it certifies, without ever
producing a red build. Prefer a check that produces a **number** (a job count) over
one that produces an **absence** (a missing `.olean`): an absence is equally
consistent with "not built" and with "the build died before reaching it".

**7. Discharging a hypothesis by *construction* moves a cost the statement cannot
see.** This is the failure mode §1c and §1d are exposed to, and it is new here: it did not
exist while the oracles were binders, because a binder at least *names* the thing
you are assuming. Replace the binder with a term and the assumption is gone in a
sense the machine can verify — `#print axioms` is unchanged, the binder count
drops, and nothing in the type records that
[`Ttc.VolumeAlgorithm.monteCarlo`](Ttc/Volume/MonteCarlo.lean) needs exponentially
many samples in `n`, or that
`Ttc.mixSteps` is `2^{Θ(n)}·log(…)`. An
accuracy-only conclusion is **silent about cost by construction**, so the more
expensive the object you build, the better the theorem looks.

*Why this is not item 5.* Item 5 is about a **bound** whose parameter range is
quoted somewhere other than the statement — the cost is in the mathematics and the
defect is where it is written down. Here the cost is in a **definition**, and no
amount of quoting fixes it, because the statement has no slot for it: the theorem
is true, the term exists, and "exponential" is not expressible in the type. Item 5
asks *what does the bound do at the consumer's parameters*; item 7 asks *what did
it cost to make the hypothesis go away*.

*The check:* for every binder removed between two revisions of a capstone, name
the term that replaced it and state its cost in the same breath — "no oracle
remains" and "both constructions are exponential in `n`" are one sentence, not
two. Then confirm the replacement is not the idealised object in disguise, by
walking for it: §5's walk reporting `Ttc.VolumeAlgorithm.exact` **`false`** is that
confirmation for the volume oracle, and
[`Ttc.MonteCarlo.monteCarlo_est_ne_volume`](Ttc/Volume/MonteCarlo.lean) is the sharper form.
Note the asymmetry the sampler side leaves open — `law_tv` is discharged, but
`contLaw i ≠ uniformOn volume P'ᵢ` is **not proved** (§1c caveat 1), so on that
side the disguise is ruled out only by construction and by the start-versus-target
lemma, not by a theorem saying the built law differs from the ideal one.

*Two more binder removals to apply the check to, both landed after item 7 was
written.* **(a)** §1d's nine polytope-description binders were replaced by
`Ttc.canonAm`/`canonBv`/`canonRfac`/`canonDm`. The cost here is genuinely **nil**,
and that is checkable rather than asserted: the substitution is an *equality*
(`Ttc.canon_body_eq_smul_region`) and `hcard` holds with equality, so
`Ttc.Params.gamma` and `Ttc.Params.thresh` read the same facet count they read
before. This is the one case in the tree where "no cost" is the right answer.
**(b)** §1d's clean `1 − δ` replaced no binder at all — it changed the *value* `hP`
ties `P` to, from `δ` to `4δ/5`. Item 7's check still applies, and its answer is a
number: `5/4` on the Monte-Carlo sample count, an additive `24·log(5/4)/((1−ε')ε'²)`
on `Thresh`. Quote those with the `1 − δ`, or the sentence "the guarantee is a clean
`1 − δ`" is item 7's failure mode wearing a budget's clothes.


## 0m. `hLov` is off the critical path: `λ ≥ 1/2` proved outright (2026-08-13)

§0h and the `LovaszSmoothing*` files route Cousins–Vempala's `lem:lambda-bound`
(`vol3_journal.tex:853`, `λ(f) ≥ 1/2`) through Lovász–Vempala's smoothing `f̂` and their
Lemma 6.3, and terminate in the unproved binder `hLov`. That binder is **not closable in
Mathlib today**: LV Lemma 6.3 rests on LV Lemma 6.4 = KLS97 Corollary 4.6, whose proof needs
the `(n−1)`-dimensional surface measure of a convex body together with
`vol(K) ≥ (r/n)·vol_{n−1}(∂K)`. Mathlib has no boundary Hausdorff measure of a convex body
with the Cauchy/Fubini projection formula, so the route stops there.

**It does not matter for the polytime volume oracle.** Every consumer in this repository —
`WastedSteps.lean`'s `hlam` — takes the *uniform* average
`avgLocalConductance K δ = (∫_K ℓ)/vol(K)`, and that quantity is bounded below outright at
step `δ ≤ 1/(2n)`:

    ∫_K ℓ  ≥  ∫_{cK} ℓ  =  vol(cK)  =  cⁿ·vol(K)  ≥  (1/2)·vol(K),        c = 1 − 1/(2n),

the middle equality being `ell_eq_one_on_shrunken` (ℓ is *identically* 1 on the shrunken
body at `δ ≤ 1 − c`) and `cⁿ ≥ 1/2` being `half_le_one_sub_inv_two_mul_pow`. Both were
already proved in `KLS97Shell.lean`; the new file
[`LambdaFromShrunken.lean`](Arlib/MarkovChains/Continuous/LambdaFromShrunken.lean) assembles
them:

* `half_mul_volume_le_lintegral_ell` — `(1/2)·vol K ≤ ∫_K ℓ`, multiplicative form.
* `half_le_avgLocalConductance` — `1/2 ≤ λ`, the shape `hlam` takes.
* `sum_lintegral_inv_ell_iterate_speedyWalk_le_uncond` — `lem:speedy-to-ball`'s wasted-step
  count with `hlam` **discharged**: `∑ᵢ ∫ ℓ⁻¹ dQᵢ ≤ 2·t·M`. The only hypothesis left is the
  warm start, which is a genuinely separate input.

*Why Cousins–Vempala could not argue this way, and what it costs.* CV need `λ` at
`δ ≤ min{σ,1}/(4096√n)`, where `ℓ ≡ 1` on `cK` is false — hence their appeal to Lemma 6.3.
The bound above buys CV's own constant `1/2` at the price of the smaller step `1/(2n)`:
conductance is proportional to `δ`, so `1/Φ²` grows by `(σ√n/δ)²`. That is polynomial, and
the chain here already runs at `δ = 1/(2n)` (`SamplerStepCount.lean`). The composed
cold/warm step `δ := min(σ/(8√n), 1/(2n))` is `≤ 1/(2n)` unconditionally, so no case split
is needed.

*What is still not proved.* LV Lemma 6.3 itself, and `λ` at CV's larger step. `hLov` remains
a carried hypothesis in `LovaszSmoothing.lean` and `LovaszSmoothingSharp.lean`. Neither is
on the path to a polynomial-time volume oracle.

**Three transcription defects in CV §6, all confirmed against the sources** (recorded because
each one silently changes a statement):

1. `:862` — LV's smoothing `f̂` minimises over convex `C ⊆ rB` with `vol(C) = ω_n rⁿ/**16**`
   (LV §6.1); CV transcribe "a convex subset `D` of `δBₙ` of **half** its volume". Different
   functions. `LovaszSmoothingSharp.lean` defines `ballSmoothing16` at LV's normalisation;
   the pre-existing `LovaszSmoothing.lean`'s `hLov` is stated about the *half*-volume
   function, which LV's Lemma 6.3 says nothing about.
2. `:851` — CV define `a`-rounded with a **universal** quantifier ("any level set `L`
   contains a ball of radius `a·μ_f(L)`"); LV p. 311 define it **existentially** ("it has a
   level set `L` of probability at most `s` that contains a ball of radius `a·s`"). CV's is
   the stronger hypothesis, so their appeal survives — but the printed definition is not the
   source's.
3. The pointwise step `f̂ ≤ ℓ·f` is proved here only as `f̂ ≤ 2ℓf` in general, and this is
   **structural, not slack**: a half-ball has volume `V/2` and so contains exactly **eight**
   disjoint `V/16` pieces, never sixteen (`exists_eight_sixteenthBalls`). Any argument whose
   only input is "log-concavity gives a half-ball on which `f ≤ f(x)`" caps at `2ℓf`. The
   sharp form is proved at every maximum point of `f` and under an explicit balance
   condition (`ballSmoothing16_le_ell_mul_of_isMax`, `_of_balanced`).

LV's Lemma 6.1 (constant `2`) and Lemma 6.2 (log-concavity of `f̂`) *are* proved in full
generality at LV's own constants (`ballSmoothing16_mul_volume_le_two_mul`,
`isLogConcaveENN_ballSmoothing16`), which required building the convex-partition machinery
(`exists_volume_cut_eq`, `exists_convex_partition`) from scratch.

## 0n. The sampler's per-phase obligations close; the critical path moves to the phase induction (2026-08-13)

Four files landed together, all forced-rebuilt (`Built`, not `Replayed`), all `#print axioms`
clean at `[propext, Classical.choice, Quot.sound]`, zero `sorry`.

**(a) The warm start is discharged** —
[`WarmSpeedy.lean`](Arlib/Convexity/GaussianCooling/WarmSpeedy.lean). This was the critical
path. `PhaseSamplerTV.lean` carried `IsWarm (ofReal M) mu0 (ellGaussianProb K δ σ²)` unproved:
`WarmChain.lean` warms one *Gaussian* law against the next, while the speedy stationary law
carries the extra `ℓ` factor, and `EllFloor.lean` refutes any uniform pointwise floor on `ℓ`
for this class. Closed on the shrunken body instead: for `μ` supported on `c·K`, `ℓ ≡ 1` there
and `ℓ ≤ 1` on `K` give `μ S ≤ M·(ellGaussianProb K δ s) S` with the **same** `M`. The
`ℓ`-deficit only shrinks the speedy normaliser, so the crux is free; the factor `2` enters
once, at conditioning, via `coolLaw i (c·K) ≥ 1/2`. Composed constant `2e`.

A refutation came with it, machine-checked rather than asserted:
`exists_supported_on_shrunken_not_isWarm` shows support on `c·K` **alone** gives warmness for
**no** `M`, `⊤` included — `IsWarm` is a supremum over all measurable sets while
`ellGaussianProb` is absolutely continuous, so a Dirac mass on `c·K` gives ratio `1/0` at a
singleton. This is the tenth binder in this project to be refuted after looking plausible.

**(b) `λ ≥ 1/2` without Lovász–Vempala** — see §0m. Also proved in its Gaussian-weighted form
in [`WastedStepsGaussian.lean`](Arlib/MarkovChains/Continuous/WastedStepsGaussian.lean) §7.

**(c) The Gaussian wasted-step analogue** — same file. New unconditional structural fact
`metropolisMove = ℓ · speedyMetropolisMove` (no hypotheses at all), the exact one-step
identity `E_x[exit time] = (ℓ(x)·a(x))⁻¹` for the real trajectory, and the averaged bound
`3·∑ ≤ 10·t·M` with **both** `λ ≥ 1/2` and the acceptance floor `a ≥ 3/5` proved rather than
assumed. `hwarm` is the only non-geometric hypothesis left in it — and (a) supplies it.
New binder relative to the uniform file: `hKR : ∀ x ∈ K, ‖x‖ ≤ R`, unavoidable because the
acceptance floor degrades with `‖x‖`.

**(d) The cold-phase regime** — see the commit for
[`ColdPhaseRegime.lean`](Arlib/MarkovChains/Continuous/ColdPhaseRegime.lean). `hσn : 4 ≤ σ√n`
is gone; cold phases cost `n²` and are `σ`-free, against `σ²n³` warm, so the previously
excluded phases were the *cheapest*.

**(e) The measurability mismatch is closed** —
[`InteriorBridge.lean`](Arlib/Convexity/GaussianCooling/InteriorBridge.lean).
`Ttc/Volume/CVAmended.lean` deliberately carries no `MeasurableSet K` binder and must not
(§ `CousinsVempala.lean:819`: a convex set need not be Borel, so such a binder would be
*false*), while the whole sampler chain needs measurability. The bridge is that the sampler
can run on `interior K` — open, convex, containing the unit ball — and

    coolLaw m σsq (interior K) i  =  coolLaw m σsq K i

**as an equality of measures**, not a TV estimate, because `Convex.addHaar_frontier` makes
`interior K =ᵐ K` and both `Measure.restrict` and the normaliser `chain` read the set only
through `volume.restrict`. No measurability hypothesis on `K` appears anywhere in that file.

### What the critical path is now

Not a per-phase fact — the **end-to-end phase induction**. Two caveats of (a) name it:

1. **The start is conditioned.** Phase `i+1` starts from `condOn (coolLaw i) (c·K)`, not from
   `coolLaw i`. CV's rejection routine returns a point distributed as `coolLaw i` on all of
   `K`; starting unconditioned is *not* coverable here, because outside `c·K` the local
   conductance can be exponentially small (`EllFloor.lean`), so that sup-ratio is unbounded.
   The repair — redraw until the sample lands in `c·K`, `≤ 2` expected draws and `n`-free by
   `half_le_coolLaw_smul_set` — is not itself formalised, and is exactly what `Ttc`'s sampler
   map `X` must be defined as.
2. **The start is the *exact* phase-`i` law**, not the previous phase's sampler output.

Item 2 is the substantive one, and the accounting must not be assumed additive.
TV-closeness does **not** transfer warmness — (a)'s own refutation is the counterexample, since
an `ε`-mass atom survives TV-closeness — so the induction has to run through TV directly, via
data processing under the walk kernel plus `TVLe.condOn`, and `condOn` inflates by `~1/μ(A)`
**per phase**. The honest recursion is therefore `e_{i+1} ≤ C·e_i + 64·ε_phase` with `C ≈ 4`
at mass `≥ 1/2` — **geometric, not additive**. That is survivable, not fatal: mixing cost is
logarithmic in accuracy, so `ε_phase := ε_final·C^{−m}` adds only `~m·log C` to each phase's
`log(1/ε)` deadline, an extra factor `~m`, polynomial. Whoever writes the induction should
take the geometric accounting explicitly, or produce a genuine coupling that makes it
additive — and must not inherit "additive bookkeeping" as an unexamined assumption.

### Two residual gaps, both named, neither on the polytime critical path

* `hRσ : R ≤ 2σ√n` (isoperimetric compatibility, `IsoIndicator.lean:83`) reads `R ≤ 2` at
  ColdStart's `σ² = 1/n`, excluding bodies of radius `> 2` at their coldest variances.
  Truncation to `K ∩ closedBall 0 (2σ√n)` is the fix; the discarded mass must be bounded by
  the **full-space** Gaussian tail (R-free, exponentially small), not by `vol(K)·max γ`,
  which would only trade `R ≤ 2` for `R ≤ e^{3/2}`.
* `hLov` — §0m. Blocked on Mathlib, off the critical path.

## §0o — Where items 1–3 come from in the literature, and a correction to §0n

Provenance for the three items §0n left on the critical path, with `file:line` into the
local sources, plus one correction to §0n that changes which Lean route is cheapest.

### The citations

| item | source | what it says |
|---|---|---|
| phase induction | CV `lem:accuracy`, `1409.6011/vol3_journal.tex:1419`, eqn `eqn:exact-chance` at **:1429**, consumed at **:1588** | `Pr(X_i^j = X̄_i^j, ∀ i,j) ≥ 1 − tν`, "by induction and the definition of total variation distance" |
| `hTV` wiring | CV `lem:map-speedy-to-ball`, **:942**, adapting **KLS95 Theorem 4.16** (`BF02574061.pdf`), stated at **:940**; estimator side `lem:fn-indep` **:1398**, `lem:cov-bd` **:1405**, `lem:exp-bd` **:1412**, all from **[LV2]** = Lovász–Vempala, *Simulated annealing in convex bodies and an O\*(n⁴) volume algorithm*, JCSS 72(2):392–417, 2006 | per-phase `‖R − Q‖_tv ≤ 10ε` from `O(1)` expected samples |
| time change | CV `lem:speedy-to-ball`, **:915**, attributed to **[CV2014]** = Cousins–Vempala, *A cubic algorithm for computing Gaussian volume*, SODA 2014, 1215–1228 | `E[ball-walk steps] ≤ Mt/λ` |

### Correction to §0n: CV's composition is additive, and ours is geometric only by choice

§0n asserted the recursion "**must**" be geometric. That overstates it. CV's own accounting
is **additive** (`t·ν`), and reading :1428–1429 shows why: they never propagate an approximate
*law* through the phases at all. They use the **coupling characterisation** of TV — with
probability `1 − tν` the entire run coincides pointwise with an exact run — so the
conditioning/redraw step costs nothing, because one couples the *randomness* rather than the
distributions. Conditioning is not non-expansive on laws, but it is harmless under a coupling.

So there are two routes with different prices, and §0n named only the second:

1. **CV's coupling route** — additive. Blocked in this library: `Arlib/Probability/TV.lean:67`
   states there is no coupling characterisation of TV here, and Mathlib has no maximal coupling
   to import. Closing that is the expensive part.
2. **Law-propagation route** — additive *through the chain* by the Markov-kernel data-processing
   inequality, but paying a multiplicative constant at the one conditioning step per phase.
   The constant is **8**, not the `C ≈ 4` §0n guessed: `Arlib.tvLe_condOn_half`
   (`MapSpeedyToTarget.lean:232`) proves `TVLe (condOn μ A) (condOn ν A) (8ε)` at mass `≥ 1/2`,
   and that is the sharp constant this library actually has.

Route 2 remains polynomial for the reason §0n gave (mixing is logarithmic in accuracy, so
`ε_phase := ε_final·8^{−m}` costs a factor `~m`). It is the cheaper route **in Lean**, and it is
the one being taken. The geometric constant is therefore a stated engineering choice, not a
mathematical necessity — which is the part §0n got wrong.

The one lemma route 2 needs and this library lacks is named at `Arlib/Probability/TV.lean:69`:
**no data-processing inequality for a Markov kernel.** Everything else for the induction exists.

### Item 3 is a gap Cousins–Vempala also have

`lem:speedy-to-ball`'s cited source [CV2014] is **not** among the local PDFs, but CV reproduce
the proof in full at **:919–938**, and it is exactly the linearity-of-expectation argument that
`WastedSteps.lean` already formalises: "For any point `x`, the expected number of steps until a
proper step is made is `1/ℓ(x)` … by linearity of expectation". CV then identify that sum with
"the number of ball-walk steps the trajectory takes" **definitionally**.

So the residual gap recorded at `TrajTransfer.lean:99-105` (the path-level time change
`ω_t = Y_{N t}`, blocked on measurability of the successive jump times) is **not** a failure to
formalise a published proof — it is a step no source in the local set proves. Consequence for
the capstone: what is proved is a bound on expected **step count**, and a *running-time* claim
needs either the time change proved outright or an explicit statement that it adopts CV's
convention. This must not be blurred in the README.

## §0p — Items 1–3 after this round: what landed, and the one arithmetic trap

Three files landed (`6e44eb1`, `05ead4f`, `e8d7d0b`). Full tree: 3746 jobs, **3989 theorems
scanned, 0 non-standard axioms, 0 `sorry`**.

### Item 1 — phase induction. Skeleton proved, not yet instantiated.

`Arlib/Convexity/GaussianCooling/PhaseInduction.lean`: `TVLe.iterate` (chain steps cost
**nothing**), `tvLe_phase_step` (the single conditioning per phase costs **8**), and
`tvLe_phaseChain : TVLe (Qh m) (Q m) (nu * ∑_{j<m} 8^j)`, witnessed non-vacuously on `Bool`
with `Qh 2 ≠ Q 2` and error strictly in `(0,1)`.

**Correction to §0o and to `TV.lean`'s old Scope paragraph.** §0o said the kernel
data-processing inequality was the one missing lemma. It was never missing:
`Arlib.tvLe_step` / `Arlib.tvLe_iterate` (`Warmness.lean:293`, `:302`) have had it all along,
resting on `lintegral_le_of_tvLe` (`:241`), and in a **strictly stronger** form than the new
`TVLe.bind` — no `IsProbabilityMeasure`, no `ε ≠ ⊤`. `TV.lean`'s Scope paragraph asserted the
absence and has been rewritten. New code should prefer `Arlib.tvLe_step`.

What remains for item 1 is the **instantiation** of `tvLe_phaseChain` at the real chain.

### Item 3 — time change. Pathwise half proved; probabilistic half blocked on Mathlib.

`Arlib/MarkovChains/Continuous/TimeChange.lean` clears the obstruction named at
`TrajTransfer.lean:105`: `measurable_jumpTime` (with `measurable_properCount`,
`measurable_jumpChain`, and adaptedness), and

    jumpChain_properCount : jumpChain ω (properCount ω t) = ω t

for **every** path, no hypotheses. A proper step is defined pathwise as *the path moved*, and
`pathMeasure_ballWalk_properStep` proves that notion coincides with the ball walk's acceptance
event, probability exactly `ell K δ x` — that bridge is what makes the names honest. Hence
`lintegral_jumpTime_one_pathMeasure_ballWalk : E[first jump time] = (ell x)⁻¹`.

**Still open, and the reason is now exact**: the `j`-th sojourn for `j ≥ 1`, and the jump
chain's law, both need the **strong Markov property for `Kernel.trajMeasure`**. Verified
independently: `grep -rn StrongMarkov` over all of Mathlib v4.32 returns **nothing**, and
`Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean` has no shift lemma and no stopping-time
lemma. So the *running-time* claim is still not closed, and must not be quoted as closed.

### Item 2 — `hTV` discharged, with two honest limits

`Ttc/Volume/CVSampler.lean`: `hTV_cvLaw` proves `CVAmended.lean:246`'s `hTV` body verbatim;
`cousinsVempalaOfSpeedySampler` is the `hTV`-free constructor. Run on `interior K` and
transported by `coolLaw_interior` — an equality, so no `MeasurableSet K` binder appears.

* **Prose refuted, not a theorem.** `CVAmended.lean:318-323` and `PhaseFromTV` §5 assert that
  `ν` is fixed before `K` is seen and therefore cannot track `coolLaw … K i` for every `K`.
  `Measure.infinitePi` indexes over an *arbitrary* type; index by `(K, ε, p)` and project.
  Nothing machine-checked is contradicted — the prose is.
* **Phase-`0` warm start is a hypothesis.** `WarmSpeedy` warms phase `i+1` from phase `i`;
  phase `0` has no predecessor and nothing warms it. The witness discharges it only by taking
  `mu0` stationary — satisfiability, not an algorithm.
* **The constructor's witness is degenerate at `phases = 0`**, exactly as the pre-existing
  amended witness at `CVAmended.lean:310` already is. Inherited, not a regression; `hbudget`
  is the binder that blocks a real schedule (`geomSchedule_total_cooling_lt` forces total
  cooling `< 1.1`).

### The arithmetic trap, and the fix that already exists but is not wired

`hTV_cvLaw` carries `hRadσ : Rad K ε p ≤ 2√(σsq K ε p j)·√n` at **every** `j`. Since `σsq`
increases, it binds at `j = 0`. A non-circular Gaussian cooling must start cold,
`σ₀² ≲ 1/n` (`ColdStart.lean` — otherwise `chain 0 ≈ vol K`, the unknown). Together these
force **`R ≤ 2`**, i.e. `K ⊆ 2·Bₙ`: a sandwiching ratio of at most 2, which is not the general
problem.

This is **not** a limitation of Cousins–Vempala, and not even a limitation of this repository —
it is an artefact of `CVSampler` reaching for the *untruncated*
`tvLe_speedyRejection_coolLaw_of_mixing`. Both pieces needed to remove it are already proved
and are simply not chained:

* `ColdTruncation.mixesWithin_lazy_speedyMetropolisGaussian_cold_truncated` — mixing with **no
  radius binder on `K` at all**, at a σ-free `104857600·n²` step count, on
  `K ∩ closedBall 0 (2σ√n)`;
* `ColdTruncation.tvLe_coolLaw_inter_closedBall` — the TV price of that truncation, back to
  `coolLaw … K i`.

**The next task is therefore well-defined**: a truncated analogue of
`tvLe_speedyRejection_coolLaw_of_mixing` chaining those two through the rejection routine,
then re-deriving `hTV_cvLaw` without `hRadσ`. That, not the phase induction, is now the
shortest path to a non-circular sampler.

### §0p, corrected on two points after review

**(a) `hTV` is discharged for a SURROGATE, and the surrogate must be named.**
`CVSampler.phaseStart` is, verbatim:

    | 0     => mu0
    | i + 1 => condOn (coolLaw m σsq (interior K) i) ((1 - 1/(2n)) • interior K)

so phase `i+1` restarts from the **exact** phase-`i` law, never from phase `i`'s *sampler
output*; and the coin space draws phases independently (`Measure.infinitePi`). This is exactly
CLAUDE.md §1's "idealized independent-runs product space", and §1's corollary applies: the
capstone is honest only once the **coupling lemma** back to the real sequential sampler is in
place. That coupling is precisely the un-instantiated `tvLe_phaseChain` of item 1. Instantiating
it inflates `tvErr` from `64·acc` to `64·acc·∑_{j<m} 8^j`, absorbable by `acc ↦ acc·8^{−m}` at
`+m·log 8` per deadline — polynomial. **"`hTV` discharged" therefore does not mean "the sampler
debt is paid."** It means the per-phase debt is paid and the cross-phase coupling is not.

**(b) `hbudget` is a top-two blocker, not an inherited aside.**
`geomSchedule_total_cooling_lt` (`PhaseVar.lean:620`) reads, verbatim: `0 < n`, `ε ≤ 1`,
`0 ≤ ε`, `2m ≤ n·varBudget ε` ⊢ `(1 + 1/n)^m < 11/10`. So the interface's own binders cap
**total cooling below 1.1**. Getting from a cold start `σ₀² ≈ 1/(4n)` to the uniform law needs
total cooling of order `n²`. Hence the amended interface can **never** be instantiated
non-degenerately until `hbudget` is repaired — which is why every witness for it, the
pre-existing one at `CVAmended.lean:310` and the new one alike, sits at `phases = 0`.

**Revised next-task ranking**: (1) the truncated analogue of
`tvLe_speedyRejection_coolLaw_of_mixing`, removing the `R ≤ 2` circularity from already-proved
pieces; (2) repair `hbudget`; (3) the phase-`0` warm start (`ColdStart.lean` plus CV
`lem:starting-gauss`, `vol3_journal.tex:1326`, where CV's own `σ₀² = 1/(4n)` start comes from);
(4) instantiate `tvLe_phaseChain` to supply (a)'s coupling. Two further notes for whoever does
(4): `PhaseInduction`'s `TVLe.step`/`TVLe.iterate` are built on the weaker `TVLe.bind` and
should be re-pointed at `Warmness.tvLe_step`/`tvLe_iterate`, which are in scope and carry no
`IsProbabilityMeasure` or `ε ≠ ⊤`; and the hardcoded `8` is provisional — `chainErr_le` is
already `C`-general, so recompute `C` at instantiation rather than forcing `8`.

## §0q — Provisional runtime accounting under the current route (arithmetic, not a theorem)

What exponent does the route actually reach, assuming every open task above lands? Dropping
constants, and reading the step counts off the theorems as they are stated today:

| quantity | shape | source |
|---|---|---|
| phases `m` | `n log n` | CV `lem:accuracy`, `vol3_journal.tex:1440-1460` (`m₁ ≤ 2n log 4n` plus `log(C²n)` chunks) |
| per-phase accuracy | `acc = ε·C^{−m}`, so `log(1/acc) ~ log(1/ε) + m·log C ~ n log n` | the **geometric** composition of `tvLe_phaseChain`, `C = 8` |
| per-phase steps `t` | `n²·log(1/acc) ~ n³ log n` | `ColdTruncation`'s σ-free `104857600·n²·(log M + 2 log(1/acc))/log²2` |
| **total** | **`n⁴ log² n`** | `m·t` |

So the route is **polynomial**, but a full factor `n log n` worse than Cousins–Vempala's
`O*(n³)`. That factor is *entirely* the price of the geometric composition: each phase's
deadline carries `m·log C` where CV's carries only `log(1/ε)`, because CV compose additively
via the coupling characterisation of TV (§0o) and this library composes through laws.

Two consequences worth stating plainly:

1. **`n⁴ log² n` is the honest target to claim** while the composition runs through
   `tvLe_phaseChain`. Claiming `O*(n³)` would require the coupling route, i.e. a maximal
   coupling / coupling characterisation of TV, which neither this library nor Mathlib has.
2. Recovering `O*(n³)` is therefore a *well-defined* future task with a known price: build the
   coupling characterisation of `TVLe`, and the `C^m` collapses to `m`. It is not needed for a
   polytime claim, only for a sharp one.

Nothing above is machine-checked; it is arithmetic over theorem statements that are. It is
recorded here so that no README or capstone quotes `O*(n³)` for a route that delivers `n⁴`.

## §0r — The `R ≤ 2` circularity: removed per-phase, narrowed to `R ≤ 7.10` end-to-end

`Arlib/Convexity/GaussianCooling/PhaseSamplerTVTruncated.lean` proves
`tvLe_speedyRejection_coolLaw_truncated_of_mixing`: the truncated analogue of
`PhaseSamplerTV.lean:198`, chaining `mixesWithin_lazy_speedyMetropolisGaussian_cold_truncated`
→ `tvLe_speedyRejection_coolLaw` → `TVLe.trans` with `tvLe_coolLaw_inter_closedBall`.

**Per-phase the radius condition is gone.** `hR`, `hKR : ∀ x ∈ K, ‖x‖ ≤ R` and
`hRσ : R ≤ 2σ√n` are all absent; the only hypotheses on `K` are the four the interface already
carries (`MeasurableSet`, `Convex`, `ball 0 1 ⊆ K`, `volume K ≠ ⊤`). Witness at
`K = closedBall 0 10 ⊆ ℝ²¹`, which proves `¬(R ≤ 2σ√n)` — the untruncated binder is **false**
for that body — with total error `ofReal (501/1000) < 1`. Both declarations
`[propext, Classical.choice, Quot.sound]`, forced rebuild `Built`.

### But the end-to-end consequence is not "unrestricted", and must be stated

The truncation price `C` is carried as the binder `hCb`. Its minimal admissible value, with
`a := σ²n` and the optimal split `θ = 3/4`, is

    C_min = √(πn) · exp( n · [ −1.30685 + 1/(2a) + ½ ln a ] ).

**Verified independently, not taken from the agent's report.** The bracket is negative — so `C`
decays in `n` — only for `a ≲ 12.61`; at `a = 16` it is `+0.111`, i.e. `C` grows like `e^{0.11n}`
and the bound is worthless. Two consequences:

1. **The theorem's own `hcold : σ√n ≤ 4` (i.e. `a ≤ 16`) is WIDER than `hCb` can support.**
   For `a ∈ (12.61, 16]` the binder bundle is satisfiable only at a useless `C`, so the theorem
   is effectively vacuous there despite the binder permitting it. The usable window is
   `σ√n ≤ 3.55`. The witness sits at `a = 1`, so it is honest, but the *usable* window is
   narrower than the binder advertises. Anyone quoting `hcold` should quote `3.55`, not `4`.
2. **End-to-end across a whole schedule, the radius is capped at `R ≤ 7.10`.** The truncated
   theorem covers `a ∈ (0, 12.61]` with no radius condition; the untruncated one covers
   `a ≥ R²/4`. Every phase needs one of the two, so the two windows must overlap:
   `R²/4 ≤ 12.61`, i.e. **`R ≤ 7.102`**.

So the honest headline is **`R ≤ 2` → `R ≤ 7.10`**: a 3.55× improvement and the removal of the
*circularity* (the cold start no longer constrains the body at all), but **not** the removal of
the radius restriction. A genuinely unrestricted `R` needs the truncation price to decay for
large `a` too, which fails for the present bound because `C` is measured against the unit-ball
normaliser lower bound `e^{−1/(2s)}·vol(B(0,1))` — a bound that becomes very lossy once
`vol(K) ≫ vol(B(0,1))`. **The next task on this thread is a normaliser lower bound that scales
with `vol(K)` rather than with the unit ball.** `ColdTruncation.lean`'s header already declares
the Stirling bound on `Γ(n/2+1)` that a general-`n` proof would need to be out of scope.

Inherited and unchanged: cross-phase composition is not addressed here — the truncation radius
`2σ√n` moves with the phase, so successive cold phases run on **different** truncated bodies.
