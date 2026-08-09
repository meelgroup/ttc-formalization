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

The vocabulary, the pseudocode and the assumptions are in
[`Ttc/Model/`](Ttc/Model/) — **four files**
([`Prelude`](Ttc/Model/Prelude.lean), [`Pseudocode`](Ttc/Model/Pseudocode.lean),
[`ProblemSetting`](Ttc/Model/ProblemSetting.lean),
[`Theorem`](Ttc/Model/Theorem.lean)) —
carrying declarations and assumptions, and no proofs worth the name. Everything
*proved* about `Vol_ED` was moved out to
[`Ttc/Volume/Bridge.lean`](Ttc/Volume/Bridge.lean) to keep that true.

> This page twice said "four files" while `Model/` held five (`Endgoal` was the
> extra one). `Endgoal.lean` has since moved to [`Ttc/Exec/`](Ttc/Exec/), and `ls
> Ttc/Model/` at the time of writing returns exactly `Prelude.lean`,
> `ProblemSetting.lean`, `Pseudocode.lean`, `Theorem.lean` — four. §1b is about
> `Exec/Endgoal`. Re-run `ls Ttc/Model/` rather than trusting this sentence.

> **`Model/Theorem` no longer states the bundle version.** It used to state
> [`Ttc.TtcProb.volume_estimate`](Ttc/Estimate.lean), whose type names the bundle's
> *assumed* oracle field `T.O` and its *assumed* precision field `T.ρ`. That
> theorem still exists and is still load-bearing, but it lives in
> [`Ttc/Estimate.lean`](Ttc/Estimate.lean) as proof content. What `Model/Theorem`
> states now is [`Ttc.ttc_volume_estimate`](Ttc/Model/Theorem.lean) — the same
> guarantee over `TTC`'s own inputs `(atoms, φ, ε, δ)`, with **no oracle argument**
> (the bundle is the closed term `Ttc.runOracles`) and **no precision argument**
> (every occurrence is `P.precision gammaHat`, i.e. `GetPrecision`'s output). §1
> reads the old type; §1e reads the new one.

> **`Model/` is no longer the whole audit surface.** It used to be true that
> "everything you need is in `Ttc/Model/`". It is not true any more: the strongest
> statement in the development, [`Ttc.ttc_volume_final`](Ttc/Exec/Final.lean),
> lives **outside** `Model/`, because its hypothesis list is what is left after
> several of `Model/`'s assumptions have been *constructed away*. §1d is about it,
> §1c about the oracle-free statement it is assembled from, and an auditor who
> reads only `Model/` will read a strictly weaker statement than the one the
> project now claims.

**One caveat this page used to overstate.** It said "nothing in `Model/` refers to
a definition outside `Model/` except Mathlib." That is not accurate and never was:
`ProblemSetting` names [`Ttc.trajLaw`](Ttc/Coupling/Family.lean) and
[`Ttc.trajOracles`](Ttc/Coupling/Family.lean) in its `law_eq` and `oracle_eq`
fields, and `region`/`FacetIndex`/`Oracles` come from elsewhere too. Those two
are the strongest assumptions in the development and §4 is about exactly that, so
an auditor **does** have to follow those two names out of `Model/`. Everything
else in the four files is Mathlib or locally defined.

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
  [`Ttc.ttcOutput`](Ttc/Model/Pseudocode.lean) is
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
  [`Ttc.volSol`](Ttc/Model/Prelude.lean) is `(volume (sol M φ)).toReal` —
  Mathlib's Lebesgue measure of the set of real points satisfying the formula. No
  discretisation, no rational grid.
* **That set is what the algorithm enumerates.**
  [`Ttc.TtcProb.sol_eq_union`](Ttc/Capstone.lean) says
  `⋃ c ∈ T.D, region T.M c = sol T.M T.φ` — `thm:decomposition`, *proved* from the
  `isDNF` field via
  [`Ttc.sol_eq_iUnion_region`](Ttc/Lattice/Decomposition.lean).
* **The interval is the paper's.**
  [`Ttc.relErr`](Ttc/Model/Prelude.lean) is `ε b ↦ Set.Icc ((1−ε)b) ((1+ε)b)`,
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

What rules it out is the field `volume_ne_top`
([`ProblemSetting`](Ttc/Model/ProblemSetting.lean)) — but that is stated **per
cube**, `∀ i, volume (region M i.val) ≠ ⊤`, not for `sol M φ`. Both steps are
proved:

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

| walk from | closure size |
| --- | --- |
| `Ttc.TtcProb.volume_estimate` | 51652 |
| `Ttc.ttc_volume` | 51766 (superset: 114 extra, of which 113 substantive; 0 missing) |

The "114 extra" **includes `Ttc.ttc_volume` itself** — a closure always contains
its own start node — so the substantive figure is **113**. The `0 missing` is
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
[`Ttc.rates`](Ttc/Sampler/Rates.lean), and `sampD`/`sampler` by
[`Ttc.e2eSampD`](Ttc/Exec/EndToEnd.lean) and
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
   against [`Ttc.MonteCarlo.coins`](Ttc/Volume/MonteCarlo.lean) — the conclusion is
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
only `Model/` reads. It takes **12 explicit binders** (14 raw, the extra two being
the implicit ambient `{A}` and `{n}`), and its type contains no `Ttc.TtcProb`, no
`Ttc.VolumeAlgorithm` and no `Ttc.KV97Sampler` — checked by a probe over the
compiled type, not by reading:

```
atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hbdd hpos
```

**Twelve binders**, and the earlier `hvol : Thresh/4 ≤ Vol(F)` is **not among them** —
it is gone, and so are `hcoeff` and the four inscribed-ball binders `cen`,
`gammaHat`, `hgammaHat`, `ball_subset`. Three rounds landed after the
seventeen-binder form, and **not one of them was a sharper analysis** — each changed
what the algorithm is handed or does. §1g grades them, and two of the three are
changes a reader could mistake for a stronger theorem. Read §1g before quoting this
statement.

The first nine (`atoms … hn`) are exactly `ApproxNFA.approxNFA_countNFA`'s (the
nfalean template) binder list; they are the inputs and the parameter range and assert
nothing about the instance. The other **three** — `hφ`, `hbdd`, `hint` — are the
honest residue, every one a condition on the *input*:

| binder | says | status |
| --- | --- | --- |
| `hφ : φ.IsPositive` | the formula is negation-free | removable in principle, at a price — §1g and [`Ttc/Findings/OpenHalfspace.lean`](Ttc/Findings/OpenHalfspace.lean) |
| `hbdd : IsBounded (sol (atomSet atoms) φ)` | `Sol(F)` is bounded | **necessary** — `Ttc.volSol` is an `ENNReal.toReal` and `toReal ⊤ = 0`, so without it the theorem would certify "the output is ≈ 0" (README finding 16) |
| `hint : ∀ i, (interior (region (atomSet atoms) i.val)).Nonempty` | every polytope of the decomposition is full-dimensional | **proved not derivable** — [`Ttc.hint_not_derivable`](Ttc/Exec/Degenerate.lean) |

`hφ` and `hbdd` are **logically independent in both directions** — neither can be
dropped in favour of the other
([`Ttc.Independence.exists_isBounded_not_isPositive`](Ttc/Findings/Independence.lean),
[`Ttc.Independence.exists_isPositive_not_isBounded`](Ttc/Findings/Independence.lean),
the latter also at a non-degenerate witness as
[`…exists_isPositive_not_isBounded_halfspace`](Ttc/Findings/Independence.lean)).
That file claims nothing more: it does **not** claim `hφ ∧ hbdd` is the weakest usable
pair.

**`hvol` is no longer a binder, and §1f is no longer about the headline's last
binder.** §1f's counterexample [`Ttc.Box.big_not_derivable`](Ttc/Exec/Regime.lean)
still stands and is *why* the algorithm had to be amended; the amendment (a dilation
step) is §1g's first item.

### What is *not* an input, and what replaced it

| Was a binder | Is now |
| --- | --- |
| `M`, `M_eq` | `Ttc.atomSet atoms`, a definition. `M_eq` was an equation *defining* `M`; substituting it is a substitution, not a strengthening |
| `P`, `hP` | `Ttc.inputParams …`, a definition (`alg:ttc` lines 17–20). Same reason |
| `toDNF`, `isDNF`, `isPositive` | pinned to `Ttc.toDNFd`; `isDNF` is `Ttc.toDNFd_isDNFOf`, `isPositive` follows from `hφ` on the **input formula** |
| `hm` | `Ttc.one_le_card_cubes_of_isPositive` — `Ttc.BForm` has no `false` constructor and `IsPositive (.neg _)` is `False`, so a positive formula's DNF is never `[]` |
| `hr` | `Ttc.one_le_card_facets_of_isBounded` — a literal-free cube has `region = Set.univ ⊆ sol`, and `Set.univ` is unbounded in `Ttc.Space n` for `n ≥ 1`, so `hbdd` excludes it |
| `hlen` | `Ttc.length_toDNFd_le_card`, with **equality** |
| `T.O` | `Ttc.runOracles`, a closed term: `Ttc.mcVol` for `Vol_ED`, `Ttc.coveredOracles` for the rest |
| `T.ρ` | `P.precision gammaHat` = [`Ttc.Params.precision`](Ttc/Model/Prelude.lean) = `⌈log₁₀(γ/γ̂)⌉`, `GetPrecision`'s **output** |
| `hvol : Thresh/4 ≤ Vol(F)` | **discharged by amending the algorithm**: the input is dilated by [`Ttc.runScale`](Ttc/Exec/Rescaled.lean) and the estimate divided by `cⁿ` ([`Ttc.hvol_scaled`](Ttc/Exec/Rescaled.lean)). §1g — this one is *not* a substitution |
| `cen`, `gammaHat`, `hgammaHat`, `ball_subset` | [`Ttc.autoCen`](Ttc/Exec/Rescaled.lean) and [`Ttc.autoGamma`](Ttc/Exec/Rescaled.lean), built from [`Ttc.cenOf`](Ttc/Exec/Inscribed.lean)/[`Ttc.gammaOf`](Ttc/Exec/Inscribed.lean). `ball_subset` becomes the unconditional [`Ttc.ball_subset_cenOf`](Ttc/Exec/Inscribed.lean); `hgammaHat` becomes [`Ttc.gammaOf_pos_of_interior`](Ttc/Exec/Inscribed.lean), which needs `hint`. **Not the paper's LP** — §1g |
| `hcoeff` | the algorithm is run on the cleaned formula [`Ttc.cleanForm`](Ttc/Exec/Cleanup.lean), for which it holds outright ([`Ttc.coeff_ne_zero_toDNFd_cleanForm`](Ttc/Exec/Cleanup.lean)). Benign: [`Ttc.sol_cleanForm`](Ttc/Exec/Cleanup.lean) is an **exact set equality** — §1g |

### The one thing that was bought rather than proved

`hlen` is a duplicate-freeness condition and `Ttc.toDNF` **provably fails it**
([`Ttc.toDNF_length_gt_card_cubes`](Ttc/Exec/Statement.lean): `a ∨ a` has DNF
`[[a],[a]]`). Pinning the converter to the deduplicated
[`Ttc.toDNFd`](Ttc/Exec/Dedup.lean) changes *what the algorithm runs on*.
Deduplication preserves the semantics exactly (`Ttc.mem_toDNFd` — same cubes, hence
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
([`Ttc.ballData`](Ttc/Exec/Inscribed.lean)), and what made that affordable is that
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
`≠ ⊤` check. The new obligation `hint` is discharged by
[`Ttc.TwoCube.interior_region_nonempty_two_d`](Ttc/Witness/FullTwoCube.lean), and
[`Ttc.TwoCube.twoProbFull_def`](Ttc/Witness/FullTwoCube.lean) writes the named
probability out, by `rfl`, in exactly the shape the headline's conclusion has. The
hypotheses transported to the deduplicated cube list are in
[`Ttc/Witness/Inputs.lean`](Ttc/Witness/Inputs.lean), whose
`Ttc.TwoCube.toDNFd_twoForm` proves the two-cube DNF is already duplicate-free —
**special to this witness**, not a general fact.

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
neither appears in the headline's twelve binders (§1e). The chain is four steps, each
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


## 1g. Three rounds that changed the algorithm, not the analysis

The seventeen-binder statement carried `hvol : Thresh/4 ≤ Vol(Sol F)`, four binders
describing the inscribed ball, and `hcoeff`. All three groups are gone, and **an
auditor must know that none of them went away by a sharper proof.** In one line each:

| Round | Binders removed | What actually happened | Is the algorithm's behaviour changed? |
| --- | --- | --- | --- |
| dilation ([`Exec/Rescaled`](Ttc/Exec/Rescaled.lean)) | `hvol` | the input is scaled up by `c` before the run and the estimate divided by `cⁿ` after | **yes** — a new line in `alg:ttc`; the printed algorithm is *wrong*, not merely unproved, on a small body |
| constructed ball ([`Exec/Inscribed`](Ttc/Exec/Inscribed.lean)) | `cen`, `gammaHat`, `hgammaHat`, `ball_subset` | the ball is chosen classically instead of supplied | **yes** — it is *some* inscribed ball, not `alg:prec`'s maximal one; the run uses a possibly larger `ρ` |
| cleanup ([`Exec/Cleanup`](Ttc/Exec/Cleanup.lean), [`Exec/CleanInput`](Ttc/Exec/CleanInput.lean)) | `hcoeff` | the algorithm is handed `Ttc.cleanForm atoms φ` rather than `φ` | **only the description** — [`Ttc.sol_cleanForm`](Ttc/Exec/Cleanup.lean) is an *exact set equality*, so the body measured is literally the same set |

The three rows are not equally serious, and the table's last column is the point.

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
[`Ttc.ballData`](Ttc/Exec/Inscribed.lean) picks an inscribed ball per cube,
[`Ttc.gammaOf`](Ttc/Exec/Inscribed.lean) takes the least radius, and
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
can be dropped. [`Ttc.cleanDNF`](Ttc/Exec/Cleanup.lean) does both, and
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

These are the results that stop an auditor reading the twelve binders as "three
hypotheses someone has not got round to removing yet".

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

### Non-vacuity at twelve binders

[`Ttc.TwoCube.ttc_volume_estimate_two_cube_full`](Ttc/Witness/FullTwoCube.lean) applies
**this** statement to the two-cube instance at every `n ≥ 1` and every
`(ε, δ) ∈ (0,1]²`, and
[`…_full_at`](Ttc/Witness/FullTwoCube.lean) pins `(1/3, 9/10)` and `(1/2, 1/4)` with
the bounds `1/10` and `3/4` proved strictly positive inside the statement. `hint`
holds because each region contains an open ball of positive radius — a few lines from
`Ttc.TwoCube.ball_subset_two_d` and `Ttc.TwoCube.gamT_pos`, no box geometry
([`Ttc.TwoCube.interior_region_nonempty_two_d`](Ttc/Witness/FullTwoCube.lean)). The
former thirteenth binder `hcoeff` is **not passed at all** any more; it was discharged
upstream by the cleanup.

**The earlier two-cube theorems — including those in
[`Ttc/Witness/Headline.lean`](Ttc/Witness/Headline.lean) — witness
`Ttc.ttc_volume_inputs`, not this statement.** The run here is on the *dilated* body
of the *cleaned* formula under the *constructed* ball
([`Ttc.TwoCube.twoProbFull`](Ttc/Witness/FullTwoCube.lean)), and it is **not**
`Ttc.TwoCube.twoAccD`, the undilated run on the raw formula under the supplied ball.
They are different runs with different probabilities; no equality between the two
numbers is claimed, and none should be read into the shared names.

---

## 1h. The headline's definitional closure, its preprocessing, and its hypotheses

This section is the prose that `Ttc/Model/Theorem.lean` deliberately does not carry,
so that that file stays the statement.  Read the two together.

### Definitional closure — what those seven bodies reach for

The seven definitions are *stated* here; their **bodies are not self-contained**.
Exactly as in the reference layout, the names live in `Model/` and the terms they
abbreviate live outside it, and this is the enumeration of everything outside
`Model/` that the statement's meaning therefore depends on.  **None of the
following is in `Model/`; all of it is the trusted base beyond `Model/`.**

* **The `Exec/Api` auxiliaries** the bodies name directly — `Ttc.ttcInput` (the
  preprocessed formula, `Ttc.cleanForm ∘ Ttc.pruneForm`), its two discharged
  obligations `Ttc.ttcInput_isPositive` and `Ttc.ttcInput_bdd`, the inscribed-ball
  and dilation data `Ttc.ttcRadius`, `Ttc.ttcScale`, `Ttc.ttcAtoms`,
  `Ttc.ttcAtoms_bdd`, `Ttc.ttcCen`, `Ttc.ttcScaledRadius`, the parameter block
  `Ttc.ttcBlock`, the precision `Ttc.ttcPrec`, and the oracle bundle
  `Ttc.ttcOracleBundle`.
* **Through those, the `Exec/Inputs` run wrappers** `Ttc.runCount`, `Ttc.runRates`,
  `Ttc.ttcRunOutput`, `Ttc.runOracles`, `Ttc.runPrec`, `Ttc.inputParams`, and the
  dilation `Ttc.runScale` / `Ttc.scaledAtoms` (`Exec/Rescaled`), the deduplicated
  cube list `Ttc.toDNFd` (`Exec/Dedup`) and the cost/termination predicates
  `Ttc.runCost` and `Ttc.Terminates` (`Runtime`).
* **The constructed oracle bundle** — `Ttc.coveredOracles` (`Exec/Endgoal`) over
  `Ttc.mcVol` (`Exec/VolDischarge`), which is the volume oracle
  `Ttc.VolumeAlgorithm.monteCarlo` (`Volume/MonteCarlo`).  So `Vol_ED` is a
  *constructed* Monte-Carlo estimator, not an assumed one.
* **The constructed sampler** — `Ttc.e2eSampD` (`Exec/EndToEnd`) and the KV97 /
  ball-walk development it is built from, together with the canonicalisation data
  `Ttc.canonRfac`/`Ttc.canonAm`/`Ttc.canonBv`/`Ttc.canonDm` (`Exec/Canonical`).
* **The parameter block** — `Ttc.ttcParams` (`Exec/Params`), which `Ttc.inputParams`
  instantiates at `δ₀ = 4δ/5`.
* **The run's probability space** — `Ttc.trajLaw` (`Coupling/Family`) for the sample
  coins and `Ttc.MonteCarlo.coins` (`Volume/MonteCarlo`) for the volume coins.

So the definitional closure of what is asserted is `Model/Prelude` +
`Model/ProblemSetting` + `Model/Pseudocode` + this file + the list above.  What is
*not* in it is every proof: `Exec/Prune`, `Exec/BddFromPos`, `Exec/Final` and the
whole probabilistic development are consumed only by `Ttc.ttc_volume_api`'s proof,
not by the statement.

### The seven quantities, in detail

`Ttc/Exec/Api.lean` defines these seven (section `Measured`, after `ttc_volume_api`)
and gives each a one-line docstring; the detail lives here.  `Ttc/Model/Theorem.lean`
holds the theorem and nothing else, and names them.

* **`Ttc.ttcIndex`** — `|Sol(F) ∩ 𝕃ⁿ|` at the computed precision, i.e. the index the
  run's sample coins range over, so a sample trajectory has type
  `ℕ → Fin (ttcIndex …) → ℕ`.
* **`Ttc.ttcRates`** — the level-`0` rate vector `θ` (`alg:ttc` line 20) at the volume
  coins `c`: the sampler's mass at each enumerated lattice point times that point's
  cube's volume estimate. `Ttc.trajLaw` of it is the law the sample coins are drawn from.
* **`Ttc.ttcEstimate`** — what `TTC(F, ε, δ)` returns on the run `(c, t)`, brought back
  to the original scale: `Ttc.ttcRunOutput` at the dilated input, divided by
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

Each carries an identifying `rfl` lemma (`Ttc.ttcEstimate_def` and friends) alongside them in
`Exec/Api.lean`, and `Ttc.ttcEstimate_eq_ttcOutput` pins the measured quantity to
`Model/Pseudocode`'s own `Ttc.ttcOutput` — lines A12–A13 of that file's transcription.

### What is certified is `alg:ttc` plus three preprocessing steps

Read this before quoting the statement.  Two of the three change what the algorithm
*does*; only one is cosmetic.

* **A dilation** (`Exec/Rescaled`).  `alg:ttc` sets `p ← 1` and only halves it, so its
  sketch is `Poisson(Λ)` with `Λ ≤ Vol(Sol F)`; on a body of volume `10⁻⁶` it draws
  `Pois(10⁻⁶)` points and returns `0`.  **The printed algorithm is wrong there**, not
  merely unproved (`Ttc.Box.big_not_derivable`, README finding 20).  So the input is
  dilated by `Ttc.runScale` and the estimate divided by `cⁿ`.
* **A pruning** (`Exec/Prune`).  Degenerate (lower-dimensional) cubes are dropped.  This
  changes `Sol(F)` by a null set — `Ttc.sol_pruneForm_subset` is a genuine `⊆`, strict on
  `Ttc.degForm` — and is sound *only* because the conclusion merely measures `sol`
  (`Ttc.volSol_pruneForm`).
* **A cleanup** (`Exec/Cleanup`).  Zero-normal atoms are constant-folded.  Benign:
  `Ttc.sol_cleanForm` is an exact set equality.

The inscribed ball is *constructed* (`Ttc.autoCen`, `Ttc.autoGamma`), but it is **not**
`alg:prec` line 86's LP — it is *some* inscribed ball, and non-maximality only inflates
`ρ = ⌈log₁₀(γ/γ̂)⌉`, so the guarantee is unaffected and only the precision is looser.

### The two residual hypotheses

* `hφ` — negation-free.  Independent of boundedness in **both** directions
  (`Ttc.Independence.exists_isBounded_not_isPositive`,
  `Ttc.Independence.exists_isPositive_not_isBounded`), so neither can replace the other.
  Removable in principle at a bad price — see `Findings/OpenHalfspace.lean`.
* `hpos` — `0 < Vol(F)`.  Strictly weaker than the per-cube full-dimensionality it
  replaced: `Ttc.volSol_pos_of_interior` proves that implication, and
  `Ttc.hint_not_derivable` refutes the converse.

### `hbdd` is gone — **derived**, not dropped

The statement used to carry a twelfth binder,
`hbdd : Bornology.IsBounded (sol (atomSet atoms) φ)`.  What the chain actually needs is
boundedness of `Sol` of the **pruned** formula, and
`Ttc.isBounded_sol_pruneForm_of_volSol_pos` (`Exec/BddFromPos`) proves exactly that
from `hφ` and `hpos` alone: `hpos` bounds the volume of `Sol(F)` away from `⊤`, every
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
the file. That distinction has bitten this project before: `ProblemSetting.lean`'s
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
path**: §5's walk *from `Ttc.TtcProb.volume_estimate`* reaches 137 `Arlib.*`
declarations, 29 of them in `Arlib.KV97`, including `Arlib.KV97.theorem2` — and
the walk from `Ttc.ttc_volume_endToEnd` reaches 419 and 35. See
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
| `L`, `L_eq` | `L` **is** `\|Sol(F) ∩ 𝕃ⁿ\|/10^(ρn)` ([`Ttc.normalisedCount`](Ttc/Model/Prelude.lean)) | definition, not an assumption |
| **— from here the fields describe the sampler —** | | |
| `Lidx`, `ptE`, `ptE_inj`, `ptE_mem`, `ptE_onto` | the lattice points the coupled family is indexed by, and a *bijective* enumeration of them onto `Sol(F) ∩ 𝕃ⁿ` | **assumed of the sampler** — structure of the model. `ptE_mem`/`ptE_onto` are what make `Lidx` the paper's `N` and not an arbitrary index |
| `θ` | each point's level-`0` Poisson rate | input; pinned by `theta_eq` |
| `vol` | the rate the run draws each cube with | input; pinned by `volED_eq` |
| `sampD` | the sampler's per-cube discrete law on `P(cᵢ) ∩ 𝕃ⁿ` | input; pinned by `sampler`'s `sampD_eq` |
| **`sampler`** | **a [`Ttc.KV97Sampler`](Ttc/Sampler/Interface.lean) at this `M`, `toDNF φ`, `ρ`, `ε'`, `sampD`** | **assumed of the sampler — the strongest field on this page, jointly with `law_eq`.** Its 15 fields are tabulated below |
| **`theta_eq`** | `∀ s, ∃ i ∈ D, ptE s ∈ region M i ∧ θ s = sampD i (ptE s) * vol i` — each point's rate is *its cube's* volume estimate times the sampler's mass at it | **assumed** — this is the join between the geometry and the probability. It replaced the two free inequalities `theta_lo`/`theta_hi`, which are now derived from it |
| `cover`, `memPt`, `memPt_eq`, `cover_eq` | the coverage test and cube membership on the enumerated points, and that the two agree | **assumed** — combinatorial, checkable of an instance |
| `toTraj`, `toTraj_meas` | each `ω` reads as a trajectory `ℕ → Fin Lidx → ℕ`, measurably | structure |
| **`law_eq`** | **`μ.map toTraj = trajLaw θ`** — the randomness **is** the coupled level family ([`Ttc.trajLaw`](Ttc/Coupling/Family.lean)) | **assumed of the sampler.** Not "the draws are Poisson"; "the draws are *this construction*" |
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

`Ttc.VolumeAlgorithm.cousinsVempala` is **not** reached by either capstone (§5's
walks report `false` from `Ttc.TtcProb.volume_estimate` *and* from
`Ttc.ttc_volume_endToEnd`): `volAlg` is an assumed field of `TtcProb`, and this
file is the *assembly towards* discharging it, not the discharge.

**And it was not what discharged it.** `volAlg` is gone from
`Ttc.ttc_volume_endToEnd`, but by a different construction —
[`Ttc.VolumeAlgorithm.monteCarlo`](Ttc/Volume/MonteCarlo.lean), hit-and-miss Monte
Carlo, exponential in `n`. `Ttc/Volume/CousinsVempala.lean` was **bypassed, not
proved**, and nothing in it has been discharged; it remains the only route to a
*polynomial-time* volume oracle. `CV-ROADMAP.md` §0(0) says the same from the other
side.

### 3d. Downstream structures with partial witnesses

Two more, both in `Arlib/`, both witnessing hypothesis bundles that are *not yet*
on the headline's path but are where the remaining oracles will be discharged.
Their limitations are the point:

* **`hiso` is no longer open.** An earlier revision of this file said the
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

**The strongest residual assumption is a pair of `def`s asserted to be the
implementation.** The `law_eq` and `oracle_eq` fields say that two `def`s
([`Ttc.trajLaw`](Ttc/Coupling/Family.lean),
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
[`Ttc.normalisedCount`](Ttc/Model/Prelude.lean) `= |Sol(F) ∩ 𝕃ⁿ|/10^(ρn)`, and
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
| [`Ttc.famCount`](Ttc/Coupling/Family.lean), [`Ttc.trajLaw`](Ttc/Coupling/Family.lean) | the coupled family and its law | `Ttc.map_trajLaw_eval` — coordinate `j` carries exactly `levelLaw θ j`; `Ttc.trajLaw_ae_nested` — it is a *nested* thinning |
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
[`Ttc.Params`](Ttc/Model/Prelude.lean) — `η`, `ε'`, `Thresh`, `κ`, `γ`, `ρ` —
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
> This normally reports a handful of files that some agent is mid-way through
> landing. **Re-run it; do not trust the list below.** At the time of writing it
> reports **none**: every module under `Ttc/` is imported by `Ttc.lean` and built.
> (A revision of this page written minutes earlier reported `Ttc.Witness.TwoCube`,
> which was mid-landing at the time and has since been wired in. Re-run the probe.)
> `Ttc.Exec.CanonicalPolytope` was an orphan while it was being written; both this
> page and the README described it as one, and a still earlier revision said the
> same of `Ttc.Exec.CanonPolytope` when the roles were reversed. **The two names
> differ by four letters**, which is how that confusion survived three revisions.
> It is now settled by deletion rather than by documentation:
> `CanonicalPolytope` is **gone**. The two were compared before anything was
> removed and did not disagree — identical binder lists and conclusions, the same
> `rfac` and `Dm` — except that `CanonPolytope`'s crux
> `canon_body_eq_smul_region` holds for *every* `s > 0` where the other held only
> at `s = latticeScale ρ`, so the headline was already proved from the more general
> route. The deleted file's non-vacuity chain was ported first and survives as
> `Ttc.Box.exists_two_ttc_volume_endToEnd_canon_instances`. That this entry was
> wrong in three successive revisions is the argument for re-running the probe
> rather than reading it. Files named as orphans in still earlier
> revisions (`Ttc.Exec.Coverage`, `Arlib.Convexity.NeedleLimit`,
> `Arlib.MarkovChains.Continuous.TVWitness`) have since been wired in, and
> `Ttc.Exec.EndToEnd`, `Ttc.Exec.Budget`, `Ttc.Exec.CanonPolytope` and
> `Ttc.Exec.Final` are all imported by `Ttc.lean`, so §1c's and §1d's capstones *are*
> inside the build graph. **Nothing an orphan contains may be cited as proved**,
> whether or not an `.olean` exists for it — under `Arlib`'s globs one usually does.
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
#print axioms Ttc.ttc_volume_estimate            -- §1e: the twelve-binder headline
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
`ProblemSetting.lean` quote field-shaped Lean, so `grep` over-reports.

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
| **`Arlib.KV97.theorem2`, `Arlib.TVLe`, `Ttc.almostUniform_of_kv97_law`** | **true** | **KV97 is now on the headline's path.** ~137 `Arlib.*` declarations are reached, 29 of them `Arlib.KV97.*` |
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
reaches **52630** constants and reports:

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
statement, one step below the `_delta` reparametrisation — reaches **52629**
constants, **419** of them `Arlib.*` and **35** `Arlib.KV97.*`. It confirms every
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

Two numbers to read carefully rather than quote. **52629 versus 52630** is the
one-node difference between the two roots, not a discrepancy. And **419 `Arlib.*`
declarations** against the **137** reported for the walk from
`Ttc.TtcProb.volume_estimate` measures how much of the mixing/isoperimetry stack
the constructed sampler drags in — it is a statement about *breadth of
dependency*, and specifically **not** evidence about efficiency or about how much
of Cousins–Vempala is formalised.

### The same walk from the statement layer, `Ttc.ttc_volume_estimate`

Re-seed `todo` at `` `Ttc.ttc_volume_estimate `` — §1e's theorem, the one `Model/`
states — and the walk reaches **52694** constants, **420** of them `Arlib.*`, and
every row of the two tables above is reproduced:

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
[`Ttc.mixSteps`](Ttc/Sampler/Construct.lean) is `2^{Θ(n)}·log(…)`. An
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

