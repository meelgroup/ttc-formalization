# A Lean 4 formalisation of *Efficient Volume Computation for SMT Formulas*

Machine-checked, `sorry`-free, axiom-clean formalisation of the analysis of the
`TTC` algorithm (Shaw, Sarkar, Meel), following the methodology in
[`CLAUDE.md`](CLAUDE.md).

**Every declaration in this development is proved.** There is no `sorry`, no
custom `axiom`, and no `native_decide`, in either library (see
[Verifying the claim](#verifying-the-claim)).

**[`Ttc.ttc_volume_final`](Ttc/Exec/Final.lean) is the strongest result in the
development, and the one to read first.** It takes `(atoms, φ, ε, δ)` and input
conditions *only* — **26 explicit binders** (28 raw, counting the implicit ambient
`{A}` and `{n}`) — and binds **no oracle** and **no linear description of the input
polytopes**. Its conclusion is
`1 − δ ≤ (∫⁻ c, trajLaw … ∂(MonteCarlo.coins n)).toReal`, conjoined with `alg:ttc`'s
charged cost bound. Its binders, in order, are all legitimate inputs:
`atoms φ ε δ hε0 hε1 hδ0 hδ1 hn M M_eq toDNF isDNF isPositive hm hr P hP hlen hbdd
hcoeff cen gammaHat hgammaHat ball_subset big`.

**Both oracles are discharged — at exponential cost, and with caveats that
have to be read alongside the claim.** None of `volAlg`, `volCoins`, `volED_eq`,
`volCoins_good`, `vol`, `vol_pos`, `θ`, `theta_eq`, `gen_mem`, `sampD` or `sampler`
appears in the type of `ttc_volume_final`, nor in the type of
[`Ttc.ttc_volume_endToEnd`](Ttc/Exec/EndToEnd.lean), the oracle-free statement it is
assembled from. The volume estimator is constructed
([`Ttc.VolumeAlgorithm.monteCarlo`](Ttc/Volume/MonteCarlo.lean)), the level-`0` rates
are constructed (`Ttc.rates`), and the sampler is
constructed (`Ttc.e2eSampler`, [`Exec/EndToEnd`](Ttc/Exec/EndToEnd.lean), a lazy
ball walk over `Ttc.kv97ContLaw`) with its one quantitative field `law_tv`
**proved** rather than assumed.

**The clean `1 − δ` is a repricing, not a strengthening.** This is the single
easiest thing on this page to state misleadingly, so it is stated here rather than
in a footnote. `hP` reads
`P = ttcParams (toDNF φ) n ε (4 * δ / 5) …`: the algorithm is run at the **internal**
failure parameter `δ₀ = 4δ/5`, and `1 − δ₀ − δ₀/4 = 1 − δ` exactly. No step of the
analysis improves. The cost is quantified rather than waved at: the Monte-Carlo
sample count per polytope rises by a factor **5/4, a 25 % increase**, and `P.thresh`
grows **additively** — `log(30/δ)` in place of `log(24/δ)` — not multiplicatively.
What the repricing buys is that the statement is informative on all of `δ ∈ (0,1)`
instead of only `δ ∈ (0, 4/5)`. At `δ = 1` the bound is `0`: no longer negative,
still uninformative.

Four things the claim is **not**:

* **It is not an efficiency claim. "Unconditional" and "efficient" are
  independent, and the development establishes the first only.** Everything on
  this route is exponential in the dimension: `VolumeAlgorithm.monteCarlo` is
  hit-and-miss Monte Carlo at `Θ(Rⁿ/(ε²p))` samples, and the ball walk's certified
  step count is exponential in `n` as well. `thm:runtime` remains out of scope —
  the running-time conjunct of the capstone is `alg:ttc`'s charged cost, not a
  polynomial-time claim.
* **At the step count actually used, it is still not proved that the ball-walk
  iterate differs from `uniformOn` on the inflated body** — but this is no longer
  all-or-nothing, and the range now in the library is explicit.
  [`Arlib/MarkovChains/Continuous/NonStationary.lean`](Arlib/MarkovChains/Continuous/NonStationary.lean)
  proves distinctness two ways, each with its `t`-range as a **hypothesis of the
  statement**, so neither can be misread as general:
  `ballWalkLaw_ne_uniformOn_of_lt` by support growth, valid while
  `r + t·δ < R` (the support after `t` steps of size `δ` cannot have left
  `closedBall c (r + t·δ)`, so it misses a positive-volume part of `K`); and
  `ballWalkLaw_ne_uniformOn_of_lt_inv_pow_mul` by laziness, from `μ_t ≥ 2^(−t)·μ₀`
  setwise, valid while `π S < 2^(−t)·μ₀ S`. The first reaches `t ≈ R/δ`, which is
  `O(√n)` in the regime `δ ≍ γ/√n`; the second reaches `t ≈ log₂(μ₀S/πS)`, which is
  `Θ(n)` on the unit ball and, being independent of `δ`, is the better of the two
  when `δ` is large. **`Ttc.mixSteps` is `2^Θ(n)`, so neither route reaches it**
  and the caveat stands where it matters. The residual obstruction is unchanged and
  real: Mathlib has no spectral theory for a Markov operator on `L²(π)`, so there is
  nothing to hang an eigenvalue-`−1` exclusion on. What *is* proved throughout is
  that no *accuracy assumption* about the sampler is made: `law_tv` is a theorem,
  via `Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope`.
* **The guarantee is over the *joint* law of the run and the volume oracle's
  coins**, not conditioned on a good coin: the conclusion is an
  `∫⁻ … ∂(MonteCarlo.coins n)`, so the oracle's failure budget is paid explicitly
  (finding 13a). The intermediate statements
  [`Ttc.ttc_volume_endToEnd`](Ttc/Exec/EndToEnd.lean) and
  [`Ttc.ttc_volume_endToEnd_canon`](Ttc/Exec/CanonPolytope.lean) therefore conclude
  `1 − δ − δ/4`, which is **vacuous for `δ > 4/5`**; that is stated rather than
  patched, and `ttc_volume_final` removes the corner by repricing (above), not by
  improving the estimate.
* **It is not the same theorem as `Ttc.TtcProb.volume_estimate`.** That one — the
  abstract result over the 59-field `Ttc.TtcProb` bundle — is untouched, still
  concludes `1 − δ`, and still carries the oracles as *fields*, including `law_eq`
  and `oracle_eq`: that the algorithm's randomness **is** the coupled
  Poisson/thinning family of [`Coupling/Family`](Ttc/Coupling/Family.lean). Those
  two are a modelling judgement no machine check can settle; in the capstone they
  are discharged by *being* that construction, which is a different thing from
  their being true of a real implementation. See
  §[What is assumed](#what-is-assumed).

### The three steps to `Ttc.ttc_volume_final`

`ttc_volume_final` is a composition and nothing else. Its two ingredients are
statements in their own right, and the honest description of each is "an
intermediate step", not "the strongest result" — earlier revisions of this page
said the latter of `ttc_volume_endToEnd`, and that is now superseded.

1. [`Ttc.ttc_volume_endToEnd`](Ttc/Exec/EndToEnd.lean) — `(atoms, φ, ε, δ)`, the
   input conditions, **and a linear description of the input polytopes**; no oracle
   binder; conclusion `1 − δ − δ/4`.
2. [`Ttc.ttc_volume_endToEnd_canon`](Ttc/Exec/CanonPolytope.lean) — the same, with
   the polytope description gone: it discharges the nine named binders
   `Jt Am bv hdil rfac hr1 hcard Dm hDbody` (ten, counting the `[Fintype Jt]`
   instance). `M_eq` already says each `region M c` *is* a polytope, presented by
   the rows `atoms l` for `l ∈ c`, so the description was never independent input.
   **An earlier version of this README said `hDbody` could not be eliminated**,
   reasoning that `hdil` only makes `Polytope.body (Am i) (bv i)` a *superset* of
   the dilated region — so a bounded region could sit inside an unbounded described
   body. That was correct about `hdil` and wrong about what is provable: the
   canonical system satisfies an **equality**,
   `Ttc.canon_body_eq_smul_region : Arlib.Polytope.body (canonAm …) (canonBv …) = s • region …`,
   so the described body *is* the dilated region and `hbdd` bounds it directly.
   `hcard` holds with **equality** too (`rfac := Nat.card (FacetIndex (toDNF φ))`,
   `Fintype.card (Fin N) = N`), so no slack enters `Params.gamma` or
   `Params.thresh`.
3. `ttc_volume_final` instantiates (2) at `δ₀ = 4δ/5` — the repricing described
   above.

[`Ttc.ttc_volume_clean`](Ttc/Exec/Budget.lean) is the same repricing applied one
rung lower, to `ttc_volume_endToEnd` itself: it still carries the polytope
description, and concludes `1 − δ`. `Ttc.ttc_volume_endToEnd_delta` is an `alias`
for it — a legacy name kept because this page and `AUDIT.md` used it; both names
resolve to the same declaration.

**Non-vacuity, and it is checked rather than asserted — the strongest statement
now has its own witness, and it is not the box.**
[`Ttc.TwoCube.ttc_volume_final_two_cube`](Ttc/Witness/TwoCube.lean) instantiates
**`Ttc.ttc_volume_final` itself** — not `ttc_volume_endToEnd_ofSampler`, not
`ttc_volume_clean`, not `ttc_volume_endToEnd` — at every `(ε, δ) ∈ (0,1]²`, on a
DNF with **two** cubes, with **every binder discharged, `big` included**. A
transitive dependency walk from it returns `true` for `Ttc.ttc_volume_final` (and
likewise from `Ttc.TwoCube.ttc_volume_final_two_cube_at`). Before it landed, the
strongest result in the development had **no non-vacuity witness at all** — that
was a real gap, and this is what closes it.

The witness is two disjoint axis-aligned boxes of the same side: atoms indexed by
`(Fin n ⊕ Fin n) ⊕ (Fin n ⊕ Fin n)`, the left copy cutting out `[0,c]ⁿ` and the
right `[lo, lo+c]ⁿ`, with `c = max 1 Thresh(ε, 4δ/5)` and
`lo = (⌈c·10^ρ⌉₊ + 1)/10^ρ`. `lo > c` is what makes the two regions disjoint, and
`lo` being a multiple of the lattice spacing is what puts a lattice point in the
second box. There is no circularity in that order of construction: `ρ` depends
only on `(n, ε, δ)` and the DNF's *shape* (`m = 2`, `r = 4n`), never on `lo`.

What the arity buys is stated as theorems rather than as prose.
[`Ttc.TwoCube.card_toDNF_eq_two`](Ttc/Witness/TwoCube.lean) is an **equality**,
`Nat.card {c // c ∈ toDNF (twoForm n)} = 2` — not a `2 ≤ …` — so the DNF genuinely
has two cubes; `Ttc.TwoCube.sol_eq_union_two` makes `Sol(F)` the union of two
**distinct, nonempty and disjoint** regions; and
`Ttc.TwoCube.cenT_left_ne_right` proves the two inscribed-ball centres genuinely
differ, so `cen` is not constant. The single-cube box exercises none of the three.

**The regime condition `big` needed a genuinely new argument at arity two**, and
this is the interesting part. The box's route
(`Ttc.Box.sum_bxRates_ge`) relies on `N = L`, which is true only when there is one
cube. With two cubes `cubeAt` varies with the point, `N₁ ≠ N₂` in general, and
`L = N₁ + N₂`. The replacement bounds every rate below by `min(q₁, q₂)` with
`qᵢ = (1−ε')·V̂ᵢ/Nᵢ` ([`Ttc.TwoCube.min_qT_le_ratesT`](Ttc/Witness/TwoCube.lean),
which **case-splits on which cube `cubeAt s` returned** — the branch no
single-cube witness has), and then uses `Nᵢ ≤ L`. It also required an exact volume
computation that did not previously exist,
`Ttc.TwoCube.volume_sbx : volume [lo, lo+c]ⁿ = ofReal c ^ n`, since the box files
carried only positivity plus a global lattice bound.

Two structurally different instances are exhibited, each with its achieved bound a
numeral proved `> 0` **inside the statement**
([`Ttc.TwoCube.ttc_volume_final_two_cube_at`](Ttc/Witness/TwoCube.lean)):
`(ε, δ) = (1/3, 9/10)` at `1/10`, and `(1/2, 1/4)` at `3/4`. The first carries
`4/5 < 9/10 < 1` in the statement alongside — it sits in exactly the regime the old
`1 − δ − δ/4` budget could not reach — and
`Ttc.TwoCube.twoProb_pos_ne_top_at_nine_tenths` rules out the
`ENNReal.toReal ⊤ = 0` artefact.

**Two things the two-cube witness does not prove, and a reader will assume both.**
First, `volSol = Vol₁ + Vol₂` is **not** proved. Disjointness is; additivity of the
volume is not, and the capstone does not need it. Second, none of this is an
efficiency claim: everything here is exponential in the dimension, and at `m = 2`
every exponential cost is paid twice.

One rung lower the witnesses are the single-cube box `[0,c]ⁿ`, and they are
witnesses for *different* theorems — read which theorem each instantiates, because
they do not all instantiate what their names suggest.
`Ttc.Box.ttc_volume_endToEnd_box_at` is an application of
**`Ttc.ttc_volume_endToEnd`** to the box; `Ttc.Box.ttc_volume_clean_box_at` is not
an application of `ttc_volume_clean` at all — it is that box instance repriced at
`δ₀ = 4δ/5`, so its conclusion has `ttc_volume_clean`'s shape while its proof runs
through `ttc_volume_endToEnd`. `Ttc.Box.ttc_volume_clean_box_at` covers every
`(ε, δ) ∈ (0,1]²`, and
`Ttc.Box.exists_two_ttc_volume_clean_instances` exhibits **two structurally
different** instances, at `(ε,δ) = (1/3, 9/10)` and `(1/2, 1/4)`, with achieved
bounds `1/10` and `3/4`, both proved `> 0` inside the statement.

The real witness for `ttc_volume_clean` is
[`Ttc.Box.atParamsClean_of`](Ttc/Exec/Budget.lean), which is a direct application
of `ttc_volume_clean` to the box — verified by reading the proof term, which
supplies all ten description arguments and therefore typechecks only if all ten
hold. `Ttc.Box.AtParamsClean` is the package it discharges; it carries the ten as
fields and ties the sampler law to `e2eSampD … rfac Am bv cen gammaHat Dm`, so it
asserts nothing that is not discharged.

**`Ttc.ttc_volume_final` does not dominate `Ttc.ttc_volume_clean`, and an earlier
version of this file implied otherwise.** The two running-time conjuncts are
identical, but the accuracy conjuncts integrate *different measures*: `clean`'s
mentions `e2eSampD … rfac Am bv … Dm` in the **bound** variables, while `final`'s
mentions `canonRfac`/`canonAm`/`canonBv`/`canonDm`. So `final` is `clean`
instantiated at the one canonical description, and a point of a `∀` does not give
back the `∀` — for a user-supplied `Am`/`bv` the sampler is a different function
and `final` says nothing about it. The implication runs `clean ⟹ final` only.
`clean` is the stronger proposition; `final` is the one that asks less of a
caller. Both are kept, and each has its own witness.
`Ttc.Box.old_budget_vacuous_at_nine_tenths` puts the `1 − δ − δ/4 = −1/8`
comparison in the library rather than only in prose, and
`Ttc.Box.clean_box_prob_pos_ne_top_at_nine_tenths` reads off that the integral
inside the `toReal` is nonzero and finite. At the unrepriced budget,
`Ttc.Box.exists_two_ttc_volume_endToEnd_instances` gives the pair `(1/2,1/2)` and
`(1/4,1/4)`, bounds `3/8` and `11/16`.
`Ttc.Box.length_toDNF_boxForm` proves `(toDNF (boxForm n hn)).length = 1`, so at
those rungs the multi-cube machinery is still exercised only at `m = 1`: `hlen` is
a `Nodup` condition in disguise — `P.m = Nat.card {c // c ∈ toDNF φ}` counts
*distinct* cubes and a list is never shorter than its distinct-element count, so
`hlen` holds exactly when `toDNF φ` repeats no cube, and at length 1 that content
is never touched — and the same goes for the `m`-way union bound over cubes,
`thm:decomposition`'s union and the per-cube composition of the volume and
sampling errors. All of that *is* exercised at `m = 2` on the statement where it
matters most, the strongest one.

**What has moved from assumption to theorem** is, by now, most of the paper:

* **`lem:lattice`** used to be two fields; it is now
  [`Ttc.TtcProb.lattice_lo`/`lattice_hi`](Ttc/Lattice/Assembled.lean).
* **`lem:numlattice`** used to be one field, then a weaker `numlattice_union`
  field; **both are now theorems**
  ([`Ttc.TtcProb.numlattice`](Ttc/Coupling/NumLattice.lean),
  [`Ttc.TtcProb.numlattice_union`](Ttc/Coupling/Transfer.lean) — the latter with
  the deleted field's statement verbatim).
* **`eq:almostuniform` (`eq:sampler`)** used to be the field `samp_unif`, and
  before the sampler work it was the pair of fields `theta_lo`/`theta_hi` (the
  paper's Invariant). All three are now theorems with byte-identical statements
  ([`Ttc.TtcProb.samp_unif`](Ttc/Sampler/Bridge.lean),
  [`theta_lo`](Ttc/Sampler/Bridge.lean),
  [`theta_hi`](Ttc/Sampler/Bridge.lean)), proved by
  `Ttc.almostUniform_of_kv97_density` — i.e. by Kannan–Vempala's Theorem 2 and
  the `ℤⁿ → 𝕃ⁿ` transport.
* **The epoch index `j*`** used to be five fields (`jstar`, `hjstar`,
  `rate_small`, `rate_le`, `lamStar_ge`); it is now *constructed* by
  [`Ttc.exists_epoch`](Ttc/Coupling/Transfer.lean).
* **`Vol_ED`'s deterministic accuracy** used to be the field `volED_hi`; it is now
  [a theorem](Ttc/Volume/Bridge.lean) derived from `volCoins_good`, which is an
  *event* whose probability is itself proved
  ([`volGood_prob_budget`](Ttc/Volume/Bridge.lean), `≥ 1 − δ/4`).
* **The `1 − δ` is no longer only "at one good coin of `Vol_ED`".**
  [`Ttc.volume_estimate_joint`](Ttc/Coupling/Product.lean) proves `1 − δ − δ/4`
  over the **joint** randomness of the run and the volume oracle — see
  [finding 13a](#13a-what-is-still-assumed-about-vol_ed) for the three caveats
  (it is a *composition*-product, not a product; the bound is vacuous for
  `δ > 4/5`; and the single-sample-point form carries a visible measurability
  hypothesis).

**The Kannan–Vempala development is load-bearing, not a parallel justification.**
A transitive dependency walk over the compiled environment, starting from
`Ttc.TtcProb.volume_estimate`, returns `true` for `Arlib.KV97.theorem2`,
`Arlib.KV97.ratio_bounds_tuned_sharp`, `Ttc.almostUniform_of_kv97_density`,
`Ttc.escape_of_mem_body` and `Ttc.TtcProb.samp_unif`. The walk script is in
[`AUDIT.md`](AUDIT.md) §5 and in [Verifying the claim](#verifying-the-claim);
re-run it rather than trusting this sentence.

**And so is the convexity / Markov-chain stack, which used to be off the path.**
The same walk started from `Ttc.ttc_volume_endToEnd` returns `true` for
`Ttc.ttc_volume_monteCarlo`, `Ttc.kv97SamplerOfBody`,
`Ttc.VolumeAlgorithm.monteCarlo`,
`Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope` and
`Arlib.uniformOn_iso_of_convex` (note the namespace is `Arlib.`, not
`Arlib.Convexity.`). So the chain isoperimetry → conductance → Cheeger → `L²` →
mixing → `law_tv` → sampler → capstone is genuinely load-bearing, not merely
imported. Re-run the walk rather than trusting this sentence.

**The sampler's quantitative hypothesis is now a theorem, and its shape changed
twice — say so plainly.** `samp_unif` was a quantitative `(1 ± ε')` bound on a
*discrete* law; it became `KV97Sampler.density_au`, a `(1 ± ε'/4)` bound on a
*continuous* density; and it is now `KV97Sampler.law_tv`, a **total-variation**
bound at tolerance `ε'/(4·Vol(P′))` (finding 17 records why the pointwise form had
to go). `law_tv` is the only quantitative field of `KV97Sampler`, and
`Ttc.e2eSampler` discharges it, so on the capstone's route nothing about the
sampler's accuracy is assumed. What an implementer owes is then not an inequality
but an identification: that the shipped `GenerateSamples` *is* the lazy ball walk
this development builds. See [`END-TO-END-PLAN.md`](END-TO-END-PLAN.md) STATUS.

Formalising also acted as a referee: it turned up **three genuine errors**
(findings 1, 3, 14) and **four genuine gaps** (2, 10, 13, 15) in the published
proofs of *this* paper, plus further discrepancies in Kannan–Vempala (recorded
separately in [`AUDIT-KV97.md`](AUDIT-KV97.md)) and one hazard in what a Lean
statement can silently claim (16), all of them machine-checked. See
[Findings](#findings-the-formalisation-as-a-referee).

**Auditing this in a few minutes:** read [`AUDIT.md`](AUDIT.md), then the four
statement files of [`Ttc/Model/`](Ttc/Model/) — `Prelude`, `Pseudocode`,
`ProblemSetting`, `Theorem` — then
[`Ttc/Volume/VolSolCheck.lean`](Ttc/Volume/VolSolCheck.lean) (which is the audit
surface for the single symbol `volSol`). That fixes what every name means and
what the abstract theorem claims. For the **oracle-free capstone** add three more
*types*, and only their types: `Ttc.ttc_volume` in
[`Ttc/Exec/Endgoal.lean`](Ttc/Exec/Endgoal.lean) (the same result restated over
`(atoms, φ, ε, δ)` with every residual obligation a visible binder),
`Ttc.ttc_volume_endToEnd` in [`Ttc/Exec/EndToEnd.lean`](Ttc/Exec/EndToEnd.lean)
(the same statement with the oracle binders gone) and `Ttc.ttc_volume_final` in
[`Ttc/Exec/Final.lean`](Ttc/Exec/Final.lean) (that statement with the polytope
description gone and the budget repriced to `1 − δ`). The other directories hold
the proofs.

## Where this is against the end goal

[`END-TO-END-PLAN.md`](END-TO-END-PLAN.md) opens with the target, and the README
should state it plainly: **the capstone must eventually take `(M, φ, ε, δ)` as
its inputs**, following `ApproxNFA.approxNFA_countNFA` (in the sibling `nfalean`
project, `ApproxNFA/Model/Theorem.lean`) exactly —

```lean
theorem ttc_volume (M : A → Set (Space n)) (φ : BForm A) (ε δ : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    <only genuine input conditions on (M, φ)> :
    (1 - δ ≤ (ttcExec M φ ε δ).P.Pr
       (fun ω => pseudocodeOutput M φ ε δ ω ∈ relErr ε (volSol M φ)))
    ∧ <the runtime half>
```

`Ttc.ttc_volume_estimate` ([`Ttc/Model/Theorem.lean`](Ttc/Model/Theorem.lean))
**is** that shape, and closer to it than the paragraph below used to say: it takes
`(atoms, φ, ε, δ)` and **two** input conditions (`hφ`, `hpos` — `hbdd` is derived
and `hint` is gone with the pruning round), both halves in one conjunction, no
bundle quantified over, no oracle argument, and the precision
`P.precision gammaHat` computed by `GetPrecision` rather than supplied. The
probability is no longer an iterated integral either: both conjuncts are over one
run of one law, `Ttc.ttc`. The one difference from the target display that survives
is the internal `δ₀ = 4δ/5` that buys the clean `1 − δ`. `hlen` and `big` are
discharged upstream.

**But it is no longer a restatement of `Ttc.ttc_volume_final`.** Five rungs sit
between them, and three of those rungs *changed the algorithm*: the run is on the
input **dilated** by `Ttc.runScale` with the estimate divided by `cⁿ`
([`Exec/Rescaled`](Ttc/Exec/Rescaled.lean), finding 20), under a **constructed**
inscribed ball that is not `alg:prec`'s maximal one
([`Exec/Inscribed`](Ttc/Exec/Inscribed.lean)), on the **cleaned** formula
`Ttc.cleanForm atoms φ` ([`Exec/CleanInput`](Ttc/Exec/CleanInput.lean); this last one
is benign — `Ttc.sol_cleanForm` is an exact set equality). `AUDIT.md` §1g is the
place that spells out what each cost.

`Ttc.TtcProb.volume_estimate` ([`Ttc/Estimate.lean`](Ttc/Estimate.lean)) does not,
and still exists: it quantifies over a **59-field `Ttc.TtcProb`**, out of which
`ε`, `δ`, `φ`, the parameter block, the probability space and both oracles are all
*read*. A field is an assumption a reader cannot see from the statement, so for
that theorem the honest summary is "proved, over a hypothesis bundle", not "proved
about the algorithm's inputs". It keeps its exact statement, unchanged, because
everything downstream is built on it.

`Ttc.ttc_volume_final` does. It is stated over `(atoms, φ, ε, δ)`, both halves in
one conjunction, with no bundle quantified over, no oracle binder and no polytope
description, and its accuracy conclusion is a clean `1 − δ`. Three differences from
the target display above survive, and none of them is cosmetic:

* the probability is an `∫⁻ … ∂(MonteCarlo.coins n)` over the joint law of the run
  and the constructed volume oracle's coins, not a single `P.Pr` (finding 13a);
* `hP` runs the algorithm at the internal `δ₀ = 4δ/5`, so the clean `1 − δ` is
  bought by repricing — see the opening section for what that costs;
* `hlen` and `big` remain, and `big` is a genuine regime condition on the instance.

`Ttc.ttc_volume_endToEnd` is the intermediate: same shape, but it carries a linear
description of the input polytopes (`Jt`, `Am`, `bv`, `hdil`, `rfac`, `hr1`,
`hcard`, `Dm`, `hDbody`) alongside the input conditions and concludes
`1 − δ − δ/4`.

| Gap | Where it stands |
| --- | --- |
| the probability space is constructed, not a field | **done.** [`Ttc/Exec/Canonical.lean`](Ttc/Exec/Canonical.lean): `Ttc.canonicalTtcProb` takes the 48 arguments that genuinely have to be supplied and fills in the other **eleven** fields by construction (`Ω`, `mΩ`, `μ`, `isProb`, `O`, `toTraj`, `toTraj_meas`, `law_eq`, `oracle_eq`, `M`, `M_eq`). `Ttc.Box.boxProb_eq_canonical` checks by `rfl` that the existing witness goes through it |
| the parameter block is computed, not a field | **done.** [`Ttc/Exec/Params.lean`](Ttc/Exec/Params.lean): `Ttc.ttcParams` builds `Params` from the DNF, the dimension and `(ε, δ)`, and discharges all five tie-back fields (`eps_eq`, `delta_eq`, `dim_eq` by `rfl`, `cubes_le`/`facets_le` by `le_refl`) |
| inputs are the algorithm's inputs; no bundle quantified over; both halves in one conjunction | **done, in four steps.** [`Ttc/Exec/Endgoal.lean`](Ttc/Exec/Endgoal.lean) states `Ttc.ttc_volume` over `(atoms, φ, ε, δ)` with the space, parameters, `ρ` and `L` **constructed** and every residual obligation a visible `∀`-binder; [`Ttc/Exec/EndToEnd.lean`](Ttc/Exec/EndToEnd.lean) removes all eleven oracle binders; [`Ttc/Exec/CanonPolytope.lean`](Ttc/Exec/CanonPolytope.lean) removes the polytope description; [`Ttc/Exec/Final.lean`](Ttc/Exec/Final.lean) reprices the budget to a clean `1 − δ`. What is left in `Ttc.ttc_volume_final`'s type is inputs, input conditions, `hlen` and `big` — read the type, not this table |
| the polytope description is constructed, not assumed | **done.** [`Ttc/Exec/CanonPolytope.lean`](Ttc/Exec/CanonPolytope.lean): `Ttc.canon_body_eq_smul_region` is an *equality*, so `hdil`, `hDbody`, `hcard` and the rest all follow from `M_eq`, `isPositive`, `hbdd` and `hr` with no slack |
| the guarantee is a clean `1 − δ` | **done, by repricing, not by a better estimate.** [`Ttc/Exec/Budget.lean`](Ttc/Exec/Budget.lean) and [`Ttc/Exec/Final.lean`](Ttc/Exec/Final.lean) run the algorithm at `δ₀ = 4δ/5`; cost is `5/4` on the Monte-Carlo sample count and an additive `O(1/ε²)` on `Thresh` |
| the statement lives in `Model/`, over `(M, φ, ε, δ)`, with no oracle and no precision among the inputs | **done, and machine-checked.** [`Ttc/Model/Theorem.lean`](Ttc/Model/Theorem.lean) states `Ttc.ttc_volume_estimate` — **13 explicit binders (15 raw): four inputs, seven conditions on them, and the two per-call cost constants `cVol`/`cSample`** — with the oracle bundle the closed term `Ttc.algOracles` (`Model/Pseudocode`) and every precision `P.precision gammaHat` = `GetPrecision`'s output. Its whole definitional closure is inside `Model/`, enforced by `#modelClosureOfType`. The bundle version, whose type names the *assumed* `T.O` and `T.ρ`, moved to [`Ttc/Estimate.lean`](Ttc/Estimate.lean) |
| the hypothesis list shrinks to genuine input conditions | **done down to three, and all three are now costed.** Seven binders came off in [`Ttc/Exec/Inputs.lean`](Ttc/Exec/Inputs.lean) (`M`, `M_eq`, the converter and its two properties, `hm`, `hr`, `P`, `hP`, `hlen`); then `hvol` came off by **amending the algorithm** with a dilation ([`Ttc/Exec/Rescaled.lean`](Ttc/Exec/Rescaled.lean)), the four inscribed-ball binders by constructing *some* ball ([`Ttc/Exec/Inscribed.lean`](Ttc/Exec/Inscribed.lean)), and `hcoeff` by running on the cleaned formula ([`Ttc/Exec/CleanInput.lean`](Ttc/Exec/CleanInput.lean)). What remains is `hφ`, `hbdd`, `hint`: `hbdd` is *necessary* (finding 16); `hint` is **proved not derivable** ([`Ttc.hint_not_derivable`](Ttc/Exec/Degenerate.lean)); `hφ` and `hbdd` are **independent both ways** ([`Ttc/Findings/Independence.lean`](Ttc/Findings/Independence.lean)) and `hφ` is removable only at a stated price ([`Ttc/Findings/OpenHalfspace.lean`](Ttc/Findings/OpenHalfspace.lean)) |
| `Model/ProblemSetting` shrinks; the proof becomes a one-liner | **done for both, but read what it cost.** `Model/ProblemSetting` is 60 lines (two definitions, no hypothesis bundle; nfalean's is 53) and `Model/Theorem`'s proof is three lines applying two named lemmas. `Ttc.TtcProb` still has its 59 fields and is still what the capstone is assembled from — it moved to `Ttc/TtcProb.lean`, it did not shrink |
| the *efficiency* half | **not attempted.** Both constructed oracles are exponential in `n`; see [Scope](#scope-stated-precisely) |

All of them are **on the build path**: `Ttc.lean` imports `Ttc.Exec.Endgoal`,
`Ttc.Exec.EndToEnd`, `Ttc.Exec.Budget`, `Ttc.Exec.CanonPolytope` and
`Ttc.Exec.Final`, so a bare `lake build` compiles them and `import Ttc` puts
`Ttc.ttc_volume`, `Ttc.ttc_volume_endToEnd`, `Ttc.ttc_volume_clean`,
`Ttc.ttc_volume_endToEnd_canon` and `Ttc.ttc_volume_final` in scope. (This has
changed twice: earlier versions of this page said `Ttc.lean` did not import
`Ttc.Model.Endgoal`, and later ones said `Ttc.Exec.CanonPolytope` was not built at
all. Check `Ttc.lean`'s import list rather than this sentence.)

The runtime half of the conjunction also exists in isolated form:
[`Ttc.TtcProb.runtime`](Ttc/Estimate.lean) proves the paper's own accounting
(one `Vol_ED` call plus at most `Thresh` samples per cube, over `numCubes` cubes)
— see [Scope](#scope-stated-precisely) for exactly what it does and does not
claim.

## Build

```bash
lake exe cache get     # do not compile Mathlib from source
lake build             # builds both libraries: Ttc and Arlib
```

Pinned to `leanprover/lean4:v4.32.0` and Mathlib `v4.32.0`
(`lean-toolchain`, `lakefile.toml`). `lakefile.toml` declares **two** libraries,
`Ttc` and `Arlib`, both in `defaultTargets`; `Arlib`'s glob is
`["Arlib", "Arlib.+"]`, so every file under `Arlib/` is a build target whether or
not an area root imports it.

> This checkout reuses a sibling project's Mathlib package directory via a
> symlink at `.lake/packages` (see `CLAUDE.md` §13). If you clone it standalone,
> delete that symlink and run `lake update && lake exe cache get`.

## Verifying the claim

`#print axioms` is authoritative — `grep` is not (`sorry` elaborates to the
`sorryAx` axiom, and only `#print axioms` walks the transitive dependency tree).

```lean
import Ttc
#print axioms Ttc.TtcProb.volume_estimate
-- 'Ttc.TtcProb.volume_estimate' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
```

The declarations worth checking individually — the headline, the statements that
used to be assumed fields, and the non-degenerate witness — all return exactly
those three:

```lean
#print axioms Ttc.TtcProb.volume_estimate    -- thm:volumettc
#print axioms Ttc.TtcProb.numlattice         -- ex-field
#print axioms Ttc.TtcProb.numlattice_union   -- ex-field, statement verbatim
#print axioms Ttc.TtcProb.samp_unif          -- ex-field: eq:almostuniform
#print axioms Ttc.TtcProb.theta_lo           -- ex-field: the paper's Invariant
#print axioms Ttc.TtcProb.theta_hi           -- ex-field
#print axioms Ttc.TtcProb.volED_hi           -- ex-field: Vol_ED's accuracy
#print axioms Ttc.TtcProb.thresh_pos
#print axioms Ttc.TtcProb.vol_lt_two_total
#print axioms Ttc.TtcProb.runtime            -- thm:runtime, as the paper charges it
#print axioms Ttc.Box.boxProb                -- the non-degenerate witness
#print axioms Ttc.Box.nonempty_ttcProb
#print axioms Arlib.KV97.theorem2
```

The **oracle-free capstone and everything it is assembled from** check the same
way, and `import Ttc` reaches all of them (`Ttc.lean` imports `Model.Endgoal`,
`Exec.VolDischarge`, `Exec.EndToEnd`, `Exec.Budget`, `Exec.CanonPolytope`,
`Exec.Final`, `Sampler.Rates`, `Sampler.Construct`, `Volume.MonteCarlo`,
`Witness.BoxSharp` and `Witness.TwoCube`):

```lean
#print axioms Ttc.ttc_volume_final                             -- THE result: no oracle,
                                                               -- no polytope description, 1 − δ
#print axioms Ttc.ttc_volume_endToEnd_canon                    -- polytope description removed
#print axioms Ttc.canon_body_eq_smul_region                    -- the crux: body = s • region
#print axioms Ttc.ttc_volume_clean                             -- 1 − δ, by repricing at 4δ/5
#print axioms Ttc.ttc_volume_endToEnd_delta                    -- legacy alias for the above
#print axioms Ttc.ttc_volume_endToEnd                          -- no oracle binder at all
#print axioms Ttc.ttc_volume_endToEnd_ofSampler                -- sampler still a binder
#print axioms Ttc.ttc_volume_monteCarlo                        -- Vol_ED removed
#print axioms Ttc.ttc_volume_rates                             -- θ, theta_eq, gen_mem removed
#print axioms Ttc.ttc_volume                                   -- the Endgoal restatement
#print axioms Ttc.VolumeAlgorithm.monteCarlo                   -- the volume oracle, constructed
#print axioms Ttc.e2eSampler                                   -- the sampler, constructed
#print axioms Ttc.Box.ttc_volume_clean_box_at                  -- the clean statement, instantiated
#print axioms Ttc.Box.clean_box_at_nine_tenths                 -- (1/3, 9/10): bound 1/10 > 0,
                                                               -- where the old budget was −1/8
#print axioms Ttc.Box.old_budget_vacuous_at_nine_tenths        -- that comparison, in the library
#print axioms Ttc.Box.exists_two_ttc_volume_clean_instances    -- (1/3,9/10) and (1/2,1/4)
#print axioms Ttc.Box.ttc_volume_endToEnd_box_at               -- one rung lower, instantiated
#print axioms Ttc.Box.exists_two_ttc_volume_endToEnd_instances -- two instances, bounds 3/8 and 11/16
#print axioms Ttc.TwoCube.ttc_volume_final_two_cube            -- ttc_volume_final ITSELF,
                                                               -- on a TWO-cube DNF
#print axioms Ttc.TwoCube.ttc_volume_final_two_cube_at         -- (1/3,9/10) and (1/2,1/4):
                                                               -- bounds 1/10 and 3/4, both > 0
#print axioms Ttc.TwoCube.card_toDNF_eq_two                    -- the DNF has EXACTLY two cubes
#print axioms Ttc.TwoCube.sol_eq_union_two                     -- Sol(F) = two disjoint regions
#print axioms Ttc.TwoCube.cenT_left_ne_right                   -- the two ball centres differ
#print axioms Ttc.TwoCube.min_qT_le_ratesT                     -- big at m = 2: the case split
#print axioms Ttc.TwoCube.twoProb_pos_ne_top_at_nine_tenths    -- not toReal ⊤ = 0
```

All 28 declarations of [`Ttc/Exec/EndToEnd.lean`](Ttc/Exec/EndToEnd.lean) return
exactly `[propext, Classical.choice, Quot.sound]`; the file ends with a block of
`#print axioms` commands that re-checks this on every build.

The remaining newer results check the same way (`import Ttc` for the first two,
`import Arlib` for the rest):

```lean
#print axioms Ttc.volume_estimate_joint                        -- 1 − δ − δ/4, jointly
#print axioms Ttc.VolumeAlgorithm.cousinsVempala               -- the construction, debt in its type
#print axioms Arlib.MarkovChains.cheeger                       -- Φ²/2 ≤ gap ≤ 2Φ
#print axioms Arlib.MarkovChains.mixesWithin_of_conductance
#print axioms Arlib.MarkovChains.conductance_ballWalk_ge
#print axioms Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope
#print axioms Arlib.uniformOn_iso_of_convex                    -- note: `Arlib.`, not `Arlib.Convexity.`
#print axioms Arlib.brunn_minkowski_sharp
#print axioms Arlib.GaussianCooling.zLogconcaveHypothesis_indicator
```

### The full sweep

The claim is that **no declaration in either library** depends on anything but
those three axioms, and this is the check — run over the compiled environment, so
it is complete, where the older `grep | sed` recipe silently missed everything
declared inside a `namespace`. It must report `offenders: []`:

```lean
import Ttc
import Arlib
open Lean in
run_cmd do
  let env ← getEnv
  let ok : NameSet := (∅ : NameSet)
    |>.insert ``propext |>.insert ``Classical.choice |>.insert ``Quot.sound
  let mut count : Nat := 0        -- the ascription matters; `0` alone unifies wrong
  let mut bad : Array Name := #[]
  for (c, _) in env.constants.toList do
    if c.isInternal then continue
    let s := c.toString
    unless s.startsWith "Ttc." || s.startsWith "Arlib." do continue
    count := count + 1
    for a in (← collectAxioms c) do
      unless ok.contains a do bad := bad.push c
  logInfo m!"checked {count} declarations; offenders: {bad}"
```

`lake env lean` that file; `offenders` must be `#[]`. The two imports now do cover
everything `lake build` compiles — `Ttc.lean` imports `Ttc.Model.Endgoal`,
`Ttc.Exec.EndToEnd`, `Ttc.Exec.CanonPolytope` and `Ttc.Exec.Final`, and
`Arlib/Convexity.lean` imports `LocalizationLimit` and `DyerFrieze`, all of which
earlier versions of this page said were unreachable.
**The orphan probe currently reports nothing: every `.lean` file under `Ttc/` is
imported and built.** `Ttc/Exec/CanonicalPolytope.lean` — a second, independent
derivation of the same elimination that earlier revisions of this page described
as an orphan, then as permanent parallel debt — has been **deleted**. The two were
compared first, and they did not disagree: identical binder lists, identical
conclusions, the same `rfac` and `Dm`, except that `CanonPolytope`'s crux holds for
*every* `s > 0` where the other held only at `s = latticeScale ρ`. So the headline
was already proved from the more general of the two. Its one real asset, the
non-vacuity chain, was ported first and survives as
`Ttc.Box.exists_two_ttc_volume_endToEnd_canon_instances`. The general hazard the old text pointed
at is real and still worth stating: the `Ttc` library has no glob (only `Arlib`
does), so any file under `Ttc/` that nothing imports is **never compiled**, and a
green `lake build` says nothing whatever about it. **Nothing an unbuilt file
contains may be cited as proved**; build it by name if you want it swept. (Note the
two names differ by four letters and the `Canon` one *is* built; earlier revisions
of this page said the opposite, when the roles were reversed. Re-run the orphan
probe in [`AUDIT.md`](AUDIT.md) §5 rather than trusting this sentence.)
(Per-profile counts are deliberately not tabulated here: the declaration set
changes with every landed lemma and the numbers go stale. Re-derive them with the
sweep.)

### The dependency walk

Which results the headline *actually reaches* is a different question from which
files it imports, and only the walk settles it:

```lean
import Ttc
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
  for t in [`Arlib.KV97.theorem2, `Arlib.KV97.ratio_bounds_tuned_sharp,
            `Ttc.almostUniform_of_kv97_density, `Ttc.escape_of_mem_body,
            `Ttc.TtcProb.samp_unif, `Ttc.TtcProb.theta_lo, `Ttc.TtcProb.theta_hi,
            `Ttc.traj_numlattice_le, `Ttc.trajLaw, `Ttc.TtcProb.numlattice,
            `Ttc.TtcProb.numlattice_union, `Ttc.exists_epoch,
            `Ttc.TtcProb.thresh_pos, `Ttc.numlattice_failure_le,
            `Ttc.TtcProb.volED_hi] do
    Lean.logInfo m!"{t} reached: {seen.contains t}"
```

All of those come back `true`. Several names worth knowing come back **`false`**,
and that is correct rather than a defect:

* `Arlib.KV97.cor_linf_tuned` — the abstract theorem goes through the sharper
  `ratio_bounds_tuned_sharp` instead;
* `Ttc.TtcProb.ofReal_volSol` and everything else in
  [`Ttc/Volume/VolSolCheck.lean`](Ttc/Volume/VolSolCheck.lean) — that file is an
  *audit companion*: it checks what the symbol `volSol` means and that the
  theorem is not vacuous, which is a statement about the statement, not a step
  in the proof;
* `Ttc.volume_estimate_joint` — it *consumes* `Ttc.TtcProb.volume_estimate`
  rather than feeding it (finding 13a);
* `Ttc.VolumeAlgorithm.cousinsVempala` — the Cousins–Vempala route is still not
  discharged and nothing depends on it.

`Arlib.MarkovChains.cheeger` and `Arlib.brunn_minkowski_sharp` also come back
`false` **from `Ttc.TtcProb.volume_estimate`**, and that is right: the abstract
theorem takes both oracles as fields, so it reaches neither. **Re-run the same
walk from `Ttc.ttc_volume_endToEnd` and the picture is different.** Replace the
seed with `` `Ttc.ttc_volume_endToEnd `` and check

```lean
  for t in [`Ttc.ttc_volume_monteCarlo, `Ttc.kv97SamplerOfBody,
            `Ttc.VolumeAlgorithm.monteCarlo,
            `Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope,
            `Arlib.uniformOn_iso_of_convex] do
```

All five come back `true`. So the chain isoperimetry → conductance → Cheeger →
`L²` → mixing → `law_tv` → sampler → capstone is genuinely load-bearing on that
route, not merely imported. (`Arlib.uniformOn_iso_of_convex` lives in the `Arlib`
namespace, not `Arlib.Convexity` — a walk that spells it the other way silently
reports `false`.)

Add any of these to the `for t in [...]` list to re-check.

### Cheap greps

```bash
# `-w` matters (a docstring saying "admits a median" is not an `admit`);
# the second grep drops docstrings that *talk about* sorries, always in backticks
grep -rnwE "sorry|admit|native_decide|sorryAx" Ttc.lean Ttc/ Arlib.lean Arlib/ \
  | grep -vE '`(sorry|sorryAx|admit|native_decide)`'
grep -rnE "^axiom " Ttc.lean Ttc/ Arlib.lean Arlib/

# the staging-area rule (see below)
grep -rn "^import Ttc" Arlib/
```

The second and third return nothing. **The first returns exactly two lines, and
both are English prose, not Lean:** `Ttc/Exec/Coverage.lean` and
`Ttc/Exec/Endgoal.lean` each contain the sentence "`CLAUDE.md` §4 does not admit
an unchecked proof". `-w` was chosen to stop `admits` matching and does not stop
the bare verb; the backtick filter does not fire because the word is unquoted
prose. Earlier revisions of this page said "all three return nothing", which was
true when they said it. Read the two hits rather than tightening the pattern until
they vanish — `#print axioms` and the full sweep above are the authoritative
checks, and both are clean.

## Module map

A small **audit surface** (`Ttc/Model/`'s four files, plus `Volume/VolSolCheck`)
plus the proofs it rests on, one directory per object of the paper it discharges.
To check *what is claimed* you read only `Model/`, and this is now machine-checked
for the headline: `#modelClosureOfType Ttc.ttc_volume_estimate`
([`Ttc/Audit/ClosureCheck.lean`](Ttc/Audit/ClosureCheck.lean)) fails the build if
any constant the statement unfolds to is defined outside `Model/`. **What that cost
is the thing to know**: the names carrying the strongest assumptions —
[`Arlib.KV97.inflated`](Arlib/Lattice/KV97/Inflate.lean),
[`Arlib.TVLe`](Arlib/Probability/TV.lean),
[`Arlib.uniformOn`](Arlib/Probability/UniformOn.lean), the ball-walk mixing stack —
did not go away; `Model/Prelude` now imports four `Arlib.*` modules and reaches
them. They still have to be followed out. See [`AUDIT.md`](AUDIT.md) §4.
For the oracle-free capstone add the *type* of `Ttc.ttc_volume` in
`Exec/Endgoal.lean`, of `Ttc.ttc_volume_endToEnd` in `Exec/EndToEnd.lean` and of
`Ttc.ttc_volume_final` in `Exec/Final.lean`.

Every file below exists on disk. **The list is not exhaustive**: `Ttc/` is
109 files (~32k lines) and `Arlib/` is 63 (~40k), and a good number of modules —
chiefly `Ttc/Exec/`, `Ttc/Monadic/`, `Arlib/MarkovChains/Continuous/` and
`Arlib/Convexity/GaussianCooling/` — have landed without an entry here. Re-run
`find Ttc Arlib -name '*.lean'` and diff against this list before trusting it.

```
Ttc.lean                    -- imports every module under Ttc/, and carries the
                            --   layout docstring (per-directory file counts)
Ttc/
  Model/                    -- THE AUDIT SURFACE — read this and stop (4 files)
    Prelude.lean            -- the vocabulary: ℝⁿ, formula syntax/semantics, the Params
                            --   block, and — since the closure check went live — the
                            --   run's coin laws, the constructed sampler's law and the
                            --   canonicalisation data. Imports Arlib: reading Model/
                            --   no longer means reading only Model/
    ProblemSetting.lean     -- the PROBLEM only: volSol (= Vol(F)) and relErr
                            --   (= the (1±ε) interval). Two definitions, no assumption
    Pseudocode.lean         -- alg:ttc line by line; ttcAlgOutput, ttcRun, and ttc,
                            --   the algorithm's own law on (estimate, cost)
    Theorem.lean            -- thm:volumettc + thm:runtime: ONE theorem,
                            --   Ttc.ttc_volume_estimate, both conjuncts over one run
                            --   of Ttc.ttc
  TtcProb.lean              -- THE ABSTRACT INTERFACE: structure TtcProb, 59 fields —
                            --   every global assumption. Not the audit surface; the
                            --   headline quantifies over inputs, not over this
  Access.lean               -- defs that READ a TtcProb (D, numCubes, cubeAt, volEvent);
                            --   assume nothing of it
  Estimate.lean             -- TtcProb.volume_estimate: the bundle-level theorem, whose
                            --   type names the ASSUMED T.O and T.ρ
  Dnf.lean                  -- Ttc.toDNF is a CORRECT ToDNF: toDNF_isDNFOf and
                            --   toDNF_isPositive (how the witness discharges isDNF /
                            --   isPositive; the fields themselves remain, since toDNF
                            --   is a parameter of TtcProb)
  Invariants.lean           -- structural facts about the modelled loop: the two exit
                            --   levels, and what 𝒳 can contain
  Runtime.lean              -- thm:runtime: Terminates, and runCost_le — the paper's own
                            --   accounting, with its two gaps stated. (runCost and
                            --   stepCost themselves are in Model/Pseudocode, since the
                            --   headline's cost conjunct is stated over them)
  Capstone.lean             -- the two chains combining lem:lattice with lem:numlattice;
                            --   TtcProb.sol_eq_union (thm:decomposition for the bundle)
  Constants/                -- what the algorithm's constants buy
    Arith.lean              -- claim:helper and every ε/η inequality
    Parameters.lean         -- what ε', κ, γ are chosen to satisfy
  Rounding/                 -- claim:cl, over the rounding that realises it
    Hoeffding.lean          -- claim:cl's concentration core (Hoeffding at the paper's κ)
    Tent.lean               -- the displacement density 1−|u| — now a pure RE-EXPORT of
                            --   Arlib/Lattice/Rounding/Tent.lean
    TentSum.lean            -- ∑_{m∈ℤ} tent(u−m) = 1, and the n-fold partition of unity
    PiLintegral.lean        -- a product of withDensity measures is a withDensity product
    ProdKernel.lean         -- prodKernel: the kernel ∏ᵢ tent(pᵢ−xᵢ); double stochasticity
    ProdLaw.lean            -- its displacement law is a product ⇒ claim:cl (a) discharged
    RoundLaw.lean           -- the law of rnd p on ℤⁿ (the fixed-p side, for (b))
    RoundMoments.lean       -- that law is two-point ⇒ bounded, mean zero, independent
    Cl.lean                 -- claim:cl (a),(b),(c) over an abstract rounding kernel
    ClB.lean                -- claim:cl (b) discharged: the Q''-direction covering + averaging
    ArlibBridge.lean        -- OFF THE PATH: which Ttc/Rounding files have been re-based
                            --   onto Arlib and which cannot be, with rfl-checked aliases
  Nonconv/                  -- lem:nonconv
    Geometry.lean           -- facet systems; which facet attains k
    BallFacet.lean          -- inscribed ball ↔ facet form; finiteness of Q ∩ ℤⁿ; ℤⁿ ↪ ℝⁿ
    FacetOfDNF.lean         -- the facet system of a positive-literal DNF; Q = Sol(F)
    Recentred.lean          -- cl:recenter, the shell bound (instantiated), lem:nonconv
                            --   without a common ball
    Core.lean               -- lem:nonconv skeleton + the summation steps consuming claim:cl
    Assembled.lean          -- lem:nonconv over an actual facet system, nothing assumed
  Lattice/                  -- thm:decomposition and lem:lattice
    Decomposition.lean      -- thm:decomposition; convexity of a cube's region
    Transport.lean          -- lem:lattice: transport ℤⁿ ↔ 𝕃ⁿ = 10⁻ᵖ·ℤⁿ
    Assembled.lean          -- lem:lattice for Sol(F); where GetPrecision becomes load-bearing
    PerCube.lean            -- lem:lattice PER POLYTOPE (analysis.tex:271), via the
                            --   singleton DNF [i]; TtcProb.lattice_cube_lo/hi, and
                            --   TtcProb.theta_window_cube with its hypotheses discharged
  Process/                  -- lem:process, lem:chernoff, and the level process
    Poisson.lean            -- lem:process: Poisson splitting
    PoissonLaws.lean        -- lem:process as an identity of measures: splitting, thinning
    Chernoff.lean           -- lem:chernoff: the Poisson tail bound, from the MGF up
    Thinning.lean           -- Poisson thinning as a kernel, and on a whole count vector
    SketchProcess.lean      -- the level-j process; Err and Noise branches; the δ budget
    Sketch.lean             -- lem:numlattice's epoch skeleton
  Coupling/                 -- the run realises the family; lem:numlattice
    Family.lean             -- the coupled level family 𝒳ⱼ, its law, and the oracle
                            --   bundle that reads a trajectory (trajOracles)
    Run.lean                -- the run IS the family: |𝒳| = ∑ₛ ω(J)ₛ pathwise, the
                            --   halving triggers, and lem:numlattice's bound proved
    Transfer.lean           -- that bound transported to an arbitrary Ω/μ/O, and
                            --   TtcProb.numlattice_union — the ex-field, as a theorem;
                            --   also exists_epoch (j* is constructed, not assumed),
                            --   TtcProb.thresh_pos, TtcProb.vol_lt_two_total, and the
                            --   ex-fields cover_all, θ_nonneg, θ_pos as theorems
    NumLattice.lean         -- lem:numlattice as a theorem, from the epoch covering
    Product.lean            -- TtcProb.volume_estimate over the JOINT randomness of
                            --   run and volume oracle, at 1 − δ − δ/4 (finding 13a).
                            --   The shape Exec/VolDischarge follows.
                            --   Two forms: an iterated integral, and a single sample
                            --   point of the composition-product μ_volAlg ⊗ₘ κ
  Sampler/                  -- GenerateSamples: eq:almostuniform, PROVED
    Contract.lean           -- Ttc.AlmostUniform (= eq:almostuniform), and theta_window:
                            --   almost-uniformity + Vol_ED + lem:lattice ⇒ the Invariant
    Bridge.lean             -- the join: Arlib.KV97's ℤⁿ statement transported to 𝕃ⁿ,
                            --   escape_of_mem_body (KV97 Thm 2's escape hypothesis,
                            --   discharged), and the ex-fields samp_unif, theta_lo,
                            --   theta_hi recovered as theorems
    Construct.lean          -- a KV97Sampler whose law_tv is a THEOREM: contLaw is the
                            --   lazy ball walk on the inflated polytope from a warm
                            --   start, and law_tv is mixesWithin_lazy_ballWalk_polytope
                            --   at tolerance ε'/(4·Vol(P')). Geometry (diameter,
                            --   inscribed ball) and the warm start are explicit named
                            --   hypotheses, not fields and not axioms
    Rates.lean              -- ttc_volume_rates: the level-0 rates θ CONSTRUCTED
                            --   (Ttc.rates, via thm:decomposition and a classical choice
                            --   of cube), so θ, theta_eq and gen_mem stop being binders;
                            --   rates_pos rules out the collapsed θ ≡ 0
  Volume/                   -- Vol_ED, and what volSol means
    Bridge.lean             -- everything PROVED about Vol_ED: the VolumeAlgorithm.exact
                            --   non-vacuity witness, the roundBody rescaling that
                            --   discharges Theorem 1.1's "contains the unit ball"
                            --   hypothesis, the union bound over the m calls
                            --   (volGood_prob_budget), and the former field volED_hi
                            --   recovered as a theorem
    MonteCarlo.lean         -- VolumeAlgorithm.monteCarlo: the volume oracle CONSTRUCTED,
                            --   with NO hypotheses — hit-and-miss Monte Carlo, coins an
                            --   infinitePi of uniforms on the unit ball, correct by
                            --   Chebyshev. est_ne_volume shows it is not the exact
                            --   oracle in disguise; est_meas holds for non-measurable K
                            --   via the measurable hull. Sample count EXPONENTIAL in n;
                            --   emphatically NOT Cousins–Vempala Theorem 1.1
    CousinsVempala.lean     -- OFF THE PATH: Cousins–Vempala §5.2 (telescoping product,
                            --   Chebyshev, median boost, the hot end of the chain) proved
                            --   unconditionally, and VolumeAlgorithm.cousinsVempala — a
                            --   complete construction of Vol_ED's contract whose
                            --   remaining debt is four named hypotheses in its own type.
                            --   STILL UNDISCHARGED; MonteCarlo.lean fills the volAlg
                            --   field by a different, exponential route, which is not a
                            --   proof of CV Theorem 1.1. See "the volume oracle" below
    VolSolCheck.lean        -- OFF THE PATH: the audit surface for the symbol volSol —
                            --   an independent Bool-valued evaluator for BForm.holds,
                            --   the ENNReal.toReal ⊤ = 0 hazard exhibited
                            --   (volSol M .tt = 0) and then closed (ofReal_volSol)
  Witness/                  -- non-vacuity
    Box.lean                -- the box [0,c]ⁿ: its atoms, cube, DNF, formula, inscribed
                            --   ball, finite volume, and lattice count ≥ cⁿ
    BoxProb.lean            -- Box.boxProb: the non-degenerate TtcProb built on it,
                            --   including a genuine KV97Sampler for the box, and
                            --   Box.nonempty_ttcProb
    BoxSharp.lean           -- the same box at ε < 1 and δ < 1: Box.ttc_volume_box_at at
                            --   EVERY (ε,δ) ∈ (0,1]², and exists_two_ttc_volume_instances.
                            --   Closes a real defect — the old witness sat at ε = δ = 1,
                            --   where the accuracy conjunct reads 0 ≤ (…).toReal and is
                            --   true of every measure (ttc_volume_box_accuracy_is_trivial)
    TwoCube.lean            -- the witness whose DNF has TWO cubes: two disjoint boxes
                            --   [0,c]ⁿ and [lo,lo+c]ⁿ, c = max 1 Thresh(ε,4δ/5) and
                            --   lo = (⌈c·10^ρ⌉₊+1)/10^ρ > c a lattice multiple. It
                            --   instantiates ttc_volume_final ITSELF (the only witness
                            --   that does), at every (ε,δ) ∈ (0,1]², every binder
                            --   discharged including big. card_toDNF_eq_two is an
                            --   EQUALITY to 2; sol_eq_union_two gives two distinct,
                            --   nonempty, DISJOINT regions; cenT_left_ne_right shows the
                            --   two ball centres differ. big needed a new argument:
                            --   min_qT_le_ratesT bounds every rate by min(q₁,q₂) and
                            --   CASE-SPLITS on cubeAt s, since the box's N = L route
                            --   holds only at one cube; volume_sbx is the exact volume
                            --   cⁿ of the shifted box, which the Box files lacked.
                            --   ttc_volume_final_two_cube_at: (1/3,9/10) and (1/2,1/4),
                            --   bounds 1/10 and 3/4, both > 0 IN the statement.
                            --   NOT proved: volSol = Vol₁ + Vol₂ (disjointness is
                            --   proved; additivity is not, and is not needed)
  Exec/                     -- the oracle-free capstone, and its plumbing
    Params.lean             -- ttcParams: the parameter block COMPUTED from (D, n, ε, δ)
    Canonical.lean          -- canonicalTtcProb: the probability space CONSTRUCTED, not
                            --   assumed; Box.boxProb_eq_canonical checks it by rfl
    Geometry.lean           -- the inscribed ball, volume_ne_top and the lattice
                            --   enumeration, constructed from the input conditions
    Coverage.lean           -- the coverage test constructed, and shown harmless: any
                            --   admissible pair is the classical one where the run
                            --   looks at it
    VolDischarge.lean       -- ttc_volume_monteCarlo: ttc_volume with all SIX Vol_ED
                            --   binders gone — volAlg constructed, vol = mcVol,
                            --   volED_eq/vol_pos proved, volCoins INTEGRATED OUT against
                            --   MonteCarlo.coins, volCoins_good AVERAGED OUT at ≥ 1 − δ/4.
                            --   That is where the guarantee becomes 1 − δ − δ/4
    EndToEnd.lean           -- ttc_volume_endToEnd: the capstone with NO oracle binder at
                            --   all (Vol_ED, the rates and the sampler all gone), and
                            --   ttc_volume_endToEnd_ofSampler, the intermediate that
                            --   still binds sampD/sampler. Non-vacuity:
                            --   Box.ttc_volume_endToEnd_box_at at every (ε,δ) ∈ (0,1]²
                            --   and Box.exists_two_ttc_volume_endToEnd_instances at
                            --   (1/2,1/2) and (1/4,1/4), bounds 3/8 and 11/16, both > 0
    Budget.lean             -- ttc_volume_clean: ttc_volume_endToEnd run at the internal
                            --   δ₀ = 4δ/5, so the conclusion is 1 − δ in the USER's δ.
                            --   A repricing, not a better analysis — the parameter block,
                            --   Thresh and runCost are those at 4δ/5, the Monte-Carlo
                            --   sample count is 5/4 higher, and Thresh grows ADDITIVELY
                            --   (log(30/δ) vs log(24/δ)). ttc_volume_endToEnd_delta is a
                            --   legacy alias for it. Non-vacuity: Box.ttc_volume_clean_box_at
                            --   at every (ε,δ) ∈ (0,1]², Box.clean_box_at_nine_tenths at
                            --   (1/3, 9/10) with bound 1/10 > 0 — where the old budget was
                            --   −1/8 (Box.old_budget_vacuous_at_nine_tenths) — and
                            --   Box.exists_two_ttc_volume_clean_instances for the pair.
                            --   Box.cleanProb/cleanAcc NAME that integral and assert
                            --   nothing; Box.cleanProb_def proves the identification by rfl
    CanonPolytope.lean      -- ttc_volume_endToEnd_canon: ttc_volume_endToEnd minus its nine
                            --   polytope-description binders (ten with [Fintype Jt]). The
                            --   crux is canon_body_eq_smul_region, an EQUALITY
                            --   body (canonAm …) (canonBv …) = s • region …, strictly
                            --   stronger than the ⊆ hdil asked for — which is why hDbody
                            --   becomes derivable. hcard holds with equality, so no slack
                            --   enters Params.gamma/Params.thresh. Built, and imported by
                            --   Ttc.lean
    Final.lean              -- ttc_volume_final: THE result. CanonPolytope's statement at
                            --   δ₀ = 4δ/5, so: no oracle, no polytope description, clean
                            --   1 − δ, 26 explicit binders (28 raw), all of them inputs.
                            --   Read this file's module docstring for which δ is the
                            --   user's and which the internal one
  Findings/                 -- OFF THE PATH TO THE THEOREM: the formalisation
                            --   refereeing the paper. Imported by Ttc.lean so they
                            --   are compiled, but nothing the headline or its
                            --   non-vacuity witness depends on imports them
    Repair.lean             -- lem:nonconv at internal parameter θ = η/2
    CubeLattice.lean        -- lem:lattice in the paper's per-polytope form
    Independence.lean       -- hφ and hbdd are independent BOTH WAYS:
                            --   exists_isBounded_not_isPositive (bounded [-1,1] with a
                            --   genuine negation) and exists_isPositive_not_isBounded
                            --   (plus a non-degenerate half-space version). Neither
                            --   headline binder can replace the other
    OpenHalfspace.lean      -- what removing hφ would cost. The volume cannot tell an
                            --   open half-space from its closure
                            --   (volume_sol_openAtomSet_eq) but the LATTICE COUNT can
                            --   (exists_latticeCount_ne_of_open, at every precision),
                            --   and hbdd stops transferring
                            --   (exists_isBounded_region_not_isBounded_posify).
                            --   A costing, not a removal

Arlib.lean                  -- SECOND LIBRARY: the staging area (see below)
Arlib/
  Probability.lean          -- area root
  Probability/
    TV.lean                 -- TVLe: total variation in bounded-predicate form, and the
                            --   transfer |∫f dμ − ∫f dν| ≤ ε for 0 ≤ f ≤ 1
    Rejection.lean          -- conditioning; (1−θ)/V ≤ wᵢ ≤ 1/V ⇒ (1−θ)/N ≤ wᵢ/∑w ≤ (1+2θ)/N
    SubgaussianTail.lean    -- Pr[⟨A,Y⟩ ≥ κ‖A‖] ≤ exp(−κ²/2), and the union bound
    UniformOn.lean          -- the uniform measure on a body (an alias for condOn), and
                            --   its integral API — what a TV statement consumes
  Lattice.lean              -- area root
  Lattice/
    Basic.lean              -- ℤⁿ, 𝕃ⁿ = c⁻¹ℤⁿ, and the dilation bijection between them
    Rounding/               -- randomized rounding, project-independent
      Tent.lean             -- the displacement density 1−|u| (Ttc/Rounding/Tent re-exports it)
      RoundLaw.lean         -- its law on ℤⁿ: two-point, mean zero, independent
      ProdKernel.lean       -- ∏ᵢ tent(pᵢ−xᵢ), and ∫_{ℝⁿ} ∏ tent = 1
      KernelIntegral.lean   -- ∫_S ∏tent ≤ 1 and = 1 − escape: Thm 2's two halves
      ContTent.lean         -- the CONTINUOUS tent product on ℝⁿ, its independence,
                            --   and ∫_T ∏tent = Pr[x+Y ∈ T] — discharges the escape
    KV97/                   -- Kannan–Vempala, "Sampling Lattice Points" (STOC '97)
      Defs.lean             -- κ = c+√(2 log r), the loss, and c = √(2 log(4/ε))
      Inflate.lean          -- P' = {Ax ≤ b+κ‖A‖}, Vol(P') ≤ (1+κ/γ)ⁿVol(P)
      Escape.lean           -- Pr[x+Y ∉ P'] ≤ r·exp(−κ²/2) ≤ exp(−c²/2)
      Theorem2.lean         -- THEOREM 2, unconditional (theorem2_of_body)
      Corollary.lean        -- cor:linf = eq:almostuniform (see finding §4g),
                            --   and the sharp form ratio_bounds_tuned_sharp
      Lemma1.lean           -- acceptance probability ≥ 9/(20e); and the identification
                            --   of `acceptance` with a probability, which needs three
                            --   hypotheses (finding 18)
  Convexity.lean            -- area root
  Convexity/
    Polytope.lean           -- {x : Ax ≤ b}, its inflation, and Vol(P′) ≤ (1+κ/γ)ⁿVol(P)
    LogConcave.lean         -- LogConcaveOn, closure properties, ↔ ConcaveOn (log ∘ f)
    PrekopaLeindler.lean    -- 1-D Brunn–Minkowski, and 1-D PRÉKOPA–LEINDLER (proved)
    PrekopaLeindlerN.lean   -- PRÉKOPA–LEINDLER in ℝⁿ, and the MULTIPLICATIVE
                            --   Brunn–Minkowski (proved); the induction runs in the
                            --   ℝ≥0∞ formulation
    BrunnSharp.lean         -- the SHARP (1/n-concave) Brunn–Minkowski for arbitrary
                            --   measurable sets, and Brunn's theorem in sharp form
                            --   (brunn_slice_sharp, brunn_slice_concaveOn)
    Localization.lean       -- what Prékopa–Leindler unlocks: marginals of log-concave
                            --   functions, convolution, Prékopa/Borell, Brunn's theorem
    LocalizationLemma.lean  -- WORK IN PROGRESS towards Lovász–Simonovits localization:
                            --   concave ⇒ log-concave, and the needle weight
    LocalizationLimit.lean  -- Blaschke selection for convex
                            --   bodies, concavity survives Hausdorff limits, and a
                            --   CONVERSE to Brunn showing the limit profile need not be
                            --   affine. The Localization Lemma stays unproved+unassumed.
                            --   (Now imported by Arlib/Convexity.lean, so `import Arlib`
                            --   does reach it; earlier this page said otherwise)
    Isoperimetry.lean       -- log-concave measures, set distance, scale invariance;
                            --   the isoperimetric inequality itself is NOT proved
    DyerFrieze.lean         -- IN FLIGHT (now imported by Arlib/Convexity.lean):
                            --   towards the Dyer–Frieze / Lovász–Simonovits
                            --   isoperimetric inequality. The one-dimensional case in full
                            --   (dyerFrieze_dim_one), the free-segment lemma, the
                            --   proportional halfspace cut, and the induction step
                            --   (dyerFrieze_step). The inequality itself is still NOT
                            --   proved and NOT assumed — the cut does not lower dimension,
                            --   so closing the loop needs the Localization Lemma.
                            --   Build it by name before trusting any of this
    GaussianCooling/
      Estimator.lean        -- lem:exp-bd, lem:fn-indep, the product estimator, and the
                            --   median boost at the O(log 1/p) rate
      Variance.lean         -- Cousins–Vempala §5.1 ported in full: the moment identities,
                            --   Brascamp–Lieb on a needle (proved), Lemmas 5.5–5.10.
                            --   TWO INPUTS ASSUMED, as explicit Prop hypotheses (never
                            --   axioms): LocalizationHypothesis and ZLogconcaveHypothesis
      ZLogconcave.lean      -- ZLogconcaveHypothesis DISCHARGED for f = c·1_K, K convex and
                            --   measurable (paper Lemma 5.9), via the marginal theorem
                            --   after x = y/A; so Lemma 5.10 is unconditional for a body.
                            --   ALSO records that the predicate is FALSE for general
                            --   log-concave f (f x = e^{−x}, fails by ≈1.93).
                            --   LocalizationHypothesis is still assumed
  MarkovChains.lean         -- area root
  MarkovChains/Continuous/
    Conductance.lean        -- flow, reversibility, conductance, + a non-vacuity witness
    Warmness.lean           -- step/iterate, warmness propagation, TV data processing
    MixingFromConductance.lean -- mixing time from geometric decay; Dirichlet form
    BallWalk.lean           -- the ball walk as a Markov kernel, reversible w.r.t. the
                            --   uniform measure on K. No conductance bound is claimed
    Cheeger.lean            -- the L² layer: real Dirichlet form, variance, spectral gap;
                            --   the co-area formula, L¹/L² isoperimetry, medians — and
                            --   CHEEGER'S INEQUALITY, BOTH DIRECTIONS: Φ²/2 ≤ gap ≤ 2Φ
                            --   (sq_conductance_div_two_le_spectralGap, cheeger), under
                            --   (rayleighSet P pi).Nonempty. Tight two-point witness
    L2Mixing.lean           -- gap ⇒ TV: swap-invariance of pi ⊗ₘ P, the L² contraction,
                            --   the χ²→TV comparison, and mixesWithin_of_conductance —
                            --   the mixing time from a conductance bound. Introduces
                            --   HasNonnegSpectrum, which the PLAIN ball walk lacks
    BallWalkConductance.lean -- ball-intersection geometry, the one-step overlap bound,
                            --   separation, the laziness bridge (lazy, hasNonnegSpectrum_
                            --   lazy), the non-vacuity witness ofReal_le_ell_unitBall,
                            --   conductance_ballWalk_ge, and the composed chain
                            --   mixesWithin_lazy_ballWalk / theorem2_of_lazy_ballWalk.
                            --   Isoperimetry is an INLINE explicit hypothesis throughout;
                            --   the only proved θ is 2⁻ⁿ, so the certified step count is
                            --   EXPONENTIAL in n — this is not a poly-time sampler
    PointwiseMixing.lean    -- WHY TV ⇒ pointwise is impossible, and why the ball walk
                            --   admits no uniform minorisation (finding 17)
    PointwiseRoute.lean     -- the route that does work: an additive TV error IS a
                            --   relative error at tolerance θ/Vol(P′), and mixing time
                            --   is logarithmic in the tolerance
```

### What the KV97 development establishes

`Arlib/Lattice/KV97/` formalises Kannan–Vempala's *Sampling Lattice Points* — the
paper `GenerateSamples` is cited to. It is **on the headline's dependency path**
(via `Ttc/Sampler/Bridge.lean`), and it is audited separately in
[`AUDIT-KV97.md`](AUDIT-KV97.md), which records **discrepancies with the printed
paper**, three of them consequential:

* the escape exponent is `e^{−c²/2}`, not the printed `2e^{−c²}` (§4a);
* `cor:linf`'s `ε` is stated relatively but derived additively, so `theorem2`'s
  hypothesis must be *pointwise* almost-uniformity, not total variation (§4b);
* **`cor:linf`'s upper bound is false for `ε > (7−√33)/2 ≈ 0.628`** (§4g) — at
  `ε = 1` the true constant is `20/9`, not `2`. `TTC` uses `ε' = ε/12 ≤ 1/12`, so
  its own use is provably inside the valid range
  ([`Ttc.TtcProb.epsPrime_le_five_eighths`](Ttc/Sampler/Bridge.lean)).

Theorem 2's escape-mass hypothesis is **not** assumed here:
`Arlib.Lattice.Rounding.setIntegral_prodTent_compl_inflate_le_exp` proves it, and
[`Ttc.escape_of_mem_body`](Ttc/Sampler/Bridge.lean) is the discharge, so
`Arlib.KV97.theorem2_of_body` is unconditional.

`Arlib/Lattice/KV97/Lemma1.lean` (the acceptance probability of the rejection
step, `≥ 9/(20e)`, better than the paper's `1/8`) is **not** on the headline's
path: it is about the sampler's *efficiency*, which is out of scope.

### What the convexity and Markov-chain stack now establishes

None of this is on `Ttc.TtcProb.volume_estimate`'s dependency path — that theorem
takes both oracles as fields. **Part of it is now on
`Ttc.ttc_volume_endToEnd`'s**: the walk from the capstone reaches
`Arlib.uniformOn_iso_of_convex` and
`Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope`, and through the latter
the conductance/Cheeger/`L²` chain, because that is what proves the sampler's
`law_tv`. What is *not* reached is the Cousins–Vempala volume route
(`VolumeAlgorithm.cousinsVempala`, the Gaussian-cooling files) — the capstone's
volume oracle is the unrelated Monte-Carlo construction. Each result below is
stated with the caveat that makes it honest — read the caveats, not the headlines.

**Cheeger's inequality, both directions.**
[`Arlib.MarkovChains.sq_conductance_div_two_le_spectralGap`](Arlib/MarkovChains/Continuous/Cheeger.lean)
is the *hard* direction, `Φ²/2 ≤ gap`, and
[`Arlib.MarkovChains.cheeger`](Arlib/MarkovChains/Continuous/Cheeger.lean) packages
both as `Φ²/2 ≤ gap ≤ 2Φ`. Proved, axiom-clean, for a reversible kernel on a
probability space. The ingredients — a one-dimensional layer-cake identity, the
co-area formula, the `L¹` and `L²` isoperimetric inequalities *for the chain*, a
median, Cauchy–Schwarz — are each proved in the file; Mathlib v4.32 has none of
them.

*Caveat.* Both directions carry `(rayleighSet P pi).Nonempty` — some `L²`
function has nonzero variance. That is **forced**, not decoration: `spectralGap`
is an `sInf` over `ℝ`, and `sInf ∅ = 0`, so on a space where every `L²` function
is a.e. constant the gap is the junk value `0` while `Φ` need not be. The
hypothesis mentions neither the conductance nor any isoperimetric constant, and
`rayleighSet_const_piHalf_nonempty` exhibits a chain satisfying it, on which the
hard direction reads `1/8 ≤ 1`.

**Sharp Brunn–Minkowski.**
[`Arlib.brunn_minkowski_sharp`](Arlib/Convexity/BrunnSharp.lean) is the
`1/n`-concave form
`λ·|A|^{1/n} + (1−λ)·|B|^{1/n} ≤ |λA + (1−λ)B|^{1/n}`, for **arbitrary measurable
`A`, `B` in `ℝⁿ`** — no convexity, no compactness, no finiteness, and the
Minkowski sum need not be measurable (`volume` is used as an outer measure on the
right). It upgrades the multiplicative form of
[`PrekopaLeindlerN`](Arlib/Convexity/PrekopaLeindlerN.lean), and yields Brunn's
theorem in sharp form (`brunn_slice_sharp`, `brunn_slice_concaveOn`).

*Caveat, and it is a real one.* `A.Nonempty` and `B.Nonempty` are **required, and
the sharp inequality is false without them**: at `A = ∅`, `B` the unit cube,
`λ = 1/2`, the right-hand side is `0` and the left is `1/2`. The multiplicative
(log-concave) form had no such hypothesis, because `|∅|^λ = 0` kills its left-hand
side. This is exactly where the sharp form is stronger and more delicate, and a
reader who transplants the log-concave statement's hypotheses gets a false
theorem. (The `A = ∅` counterexample is in that file's docstring, not a Lean
theorem; the *hypotheses* are of course in the type.)

**A conductance bound for the ball walk.**
[`Arlib.MarkovChains.conductance_ballWalk_ge`](Arlib/MarkovChains/Continuous/BallWalkConductance.lean)
proves `Φ(ball walk on K with δ-steps) ≥ min(θ/16, κ·θ²·δ/(64n))`. The geometry it
rests on — the midpoint ball inside the intersection of two `δ`-balls, the
one-step overlap bound, the separation it forces, and the flow accounting behind
the paper's three-way partition — is proved unconditionally.

*Caveat 1, now largely lifted: the isoperimetric inequality is an inline
hypothesis of this theorem — and it is **proved elsewhere in the tree**.* It is
written out as an explicit `∀`-binder `hiso` in the theorem's type — not a `def`,
not a `structure` field, not a named `Prop` — so a reader of the type sees exactly
what is assumed, and `κ` is universally quantified, so a caller who proves the
inequality gets the bound at their own constant.

[`Arlib/Convexity/IsoBall.lean`](Arlib/Convexity/IsoBall.lean) supplies such a
caller, unconditionally: `uniformOn_iso_unitBall` at `κ = (1/2)ⁿ⁺¹` for the
Euclidean unit ball, and `uniformOn_iso_of_convex` at `κ = 2⁻ⁿ/D` for **every**
bounded convex body. Both are theorems with no hypotheses beyond the ones in their
types, and the file declares no `def`, `structure`, `class` or `Prop` at all. The
proof is an elementary chord argument (a free interval on each chord `a → b` from
`exists_gap_of_separated`, integrated over `A × B` by Tonelli, each half bounded
by re-slicing the same set the other way) — it deliberately does **not** touch the
blocked limiting argument, trading the dimension-free `2/D` for `2⁻ⁿ/D`.

[`Arlib/MarkovChains/Continuous/UnitBallMixing.lean`](Arlib/MarkovChains/Continuous/UnitBallMixing.lean)
composes it through the rest of the stack:
`exists_unconditional_mixing_unitBall` is the first statement here where
isoperimetry, the local-conductance floor, Cheeger, the `L²` decay and the
total-variation bound are all *discharged at once* rather than assumed — and the
target is `Arlib.uniformOn volume (ball 0 1)`, which `isReversible_ballWalk` makes
the walk's **exact** stationary measure, so there is no bias term in the
conclusion.

**The cost, which must be quoted alongside the result.** `κ = 2⁻⁽ⁿ⁺¹⁾` is
exponentially small in the dimension, so the conductance bound and the mixing time
it feeds are exponentially large. **This is not a polynomial-time sampler.** What
it settles is that the four theorems compose and that their joint hypotheses are
satisfiable by a real body — which a sharp constant *assumed* for all bodies
cannot settle. A polynomial constant still needs the localization route below.
[`Arlib/Convexity/DyerFrieze.lean`](Arlib/Convexity/DyerFrieze.lean) is the attack
on it: the **one-dimensional case in full** (`dyerFrieze_dim_one`), the
free-segment lemma, the proportional halfspace cut
(`exists_halfSpace_proportional`, which replaces the usual Borsuk–Ulam appeal) and
the induction step (`dyerFrieze_step`). But the cut is lossless *without* lowering
dimension, so closing the loop needs the limit passage — i.e. the Localization
Lemma — and that is still unproved and unassumed.

That route has since been **reduced to a single statement**, and two things
previously believed to block it do not.
[`Arlib/Convexity/PositionalCut.lean`](Arlib/Convexity/PositionalCut.lean):
bisection with positional control is *not* a blocker — `exists_side_extent_halved`
is three lines, because the two sides' extents sum to the whole, so the smaller is
at most half regardless of where the cut landed. And thinning transversely to a
needle is *achievable*: `transverse_thin_chain_gapBox` exhibits an explicit chain
doing it, every cut two-sided, converging in Hausdorff distance to an honest
needle. What is genuinely impossible is thinning the **separating** direction —
`not_two_sided_of_sign_separated` — and that is the direction the needle runs
along, so nothing is lost. The whole remaining difficulty is (P1): for a general
configuration, exhibit a transverse direction and level whose two sides both carry
positive `g`- and `h`-mass. That is **weaker than the two-measure ham-sandwich**
usually invoked — only positivity of both masses on both sides, not exact
bisection of either — so Borsuk–Ulam may still be avoidable, as it already was in
`exists_halfSpace_proportional`. That file declares no `Prop`
asserting an isoperimetric inequality. **It is in flight**: green and `sorry`-free
at the last check, but being extended, so it may not compile at any given moment;
run `lake build Arlib.Convexity.DyerFrieze` before relying on it. (`import Arlib`
*does* reach it now — `Arlib/Convexity.lean` imports it — which is a change from
what earlier versions of this page said.)

*Caveat 2: the constant is a factor `√n` worse than the paper's.*
Cousins–Vempala's `thm:speedyconductance` gets separation `δ/√n` from the ball-cap
estimate of [KLS95, Lemma 3.5]; Mathlib has no such estimate, so the elementary
midpoint bound is used instead and delivers `θδ/n`. The gap is in the geometry,
not in the Markov-chain argument, and everything downstream inherits it.

*Caveat 3: the speediness hypothesis `hell` is forced, and the paper's `θ = 3/4`
reading of it is vacuous.* `hell : ∀ x ∈ K, θ ≤ ell K δ x` is a uniform lower
bound on the local conductance. Some such hypothesis is unavoidable for the
*plain* ball walk: near a boundary point a supporting hyperplane forces `ℓ ≤ 1/2`,
so no body with boundary satisfies `ℓ ≥ 3/4` everywhere and the paper's
`SpeedyPoints` threshold is unsatisfiable as a *uniform* bound. Cousins–Vempala
sidestep this by analysing the **speedy walk**, whose stationary density is
proportional to `ℓ`; that walk is not built in this library. Hence the
`θ`-parameterised statement, and hence the witness
[`ofReal_le_ell_unitBall`](Arlib/MarkovChains/Continuous/BallWalkConductance.lean)
(`ℓ ≥ 2⁻ⁿ` on the unit ball for `0 < δ ≤ 1`), which is what keeps `hell` from
being vacuous. (The `θ = 3/4` unsatisfiability is argued in that file's
docstrings; it is not itself a Lean theorem.)

**Spectral gap ⇒ total-variation mixing.**
[`Arlib.MarkovChains.mixesWithin_of_conductance`](Arlib/MarkovChains/Continuous/L2Mixing.lean)
discharges the `hdecay` obligation that
`mixesWithin_of_conductance_decay` used to leave to its caller: `O(φ⁻² log(M/ε))`
steps of a reversible chain with conductance `≥ φ` from an `M`-warm start land
within total variation `ε`. The route is Cheeger's hard direction, the `L²`
contraction `Var(Tᵗf) ≤ (1−gap)^{2t} Var(f)`, and the `χ²`→TV comparison; the
linchpin is `map_swap_compProd_of_isReversible`, detailed balance promoted from
rectangles to all of `pi ⊗ₘ P`.

*Caveat: `HasNonnegSpectrum` is a new hypothesis, and the plain ball walk does not
have it.* The `L²` contraction is **false** without it — the deterministic
two-cycle on `Bool` is reversible with `gap = 2` and does not contract at all —
and the ball walk's proposal operator is convolution with a ball indicator, whose
Fourier transform changes sign. (Both of those are the modules' stated reasons,
not Lean theorems; what *is* machine-checked is that every theorem in `L2Mixing`
carries `HasNonnegSpectrum` as a hypothesis and that the lazy chain satisfies it.)
So laziness is required, not cosmetic: `lazy P x = (P x + δ_x)/2` supplies it
(`hasNonnegSpectrum_lazy`, `isReversible_and_hasNonnegSpectrum_lazy_ballWalk`), at
the documented price that laziness exactly halves every set's conductance
(`conductanceOn_lazy`). `HasNonnegSpectrum` is a property of the *kernel* — it
mentions no conductance, gap or mixing rate — and `hasNonnegSpectrum_const` plus
`exists_hasNonnegSpectrum_and_conductance` show the whole hypothesis bundle is
simultaneously satisfiable.

**The whole chain, in one theorem — and what it is now a sampler for.**
[`Arlib.MarkovChains.mixesWithin_lazy_ballWalk`](Arlib/MarkovChains/Continuous/BallWalkConductance.lean)
composes every link above: geometry + isoperimetry ⇒ conductance
(`conductance_ballWalk_ge`), laziness at an exact factor `2` (`conductance_lazy`)
plus the spectral hypothesis (`hasNonnegSpectrum_lazy`), Cheeger's hard direction,
the `L²` decay, and a step count — the lazy `δ`-ball walk on `K` from an `M`-warm
start mixes to total variation `eps` in
`conductanceMixingTime M (min(θ/32, κθ²δ/(128n))) eps` steps. And
[`theorem2_of_lazy_ballWalk`](Arlib/MarkovChains/Continuous/BallWalkConductance.lean)
carries that all the way to the window KV97 Theorem 2 consumes. Every input with
content — `hiso`, `hell`, `hesc`, `hwarm` — is an inline binder;
`mixesWithin_lazy_ballWalk_unitBall` checks the bundle is jointly satisfiable
rather than vacuously composed, discharging every hypothesis concretely on the
unit ball **except `hiso`**, which it still carries. (Two of the file's docstrings
call that witness `exists_mixesWithin_lazy_ballWalk_unitBall`; no such declaration
exists — the name above is the real one.)

**And there is now an unconditional corollary for a polytope**, which is what the
project actually consumes:
[`Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope`](Arlib/MarkovChains/Continuous/ConvexBodyMixing.lean)
carries **no** isoperimetric hypothesis and **no** local-conductance floor — the
first is supplied internally by `Arlib.uniformOn_iso_of_convex`, the second by
`le_ell_of_convex_of_ball_subset` — leaving only geometry (a diameter bound, an
inscribed ball), a warm start and the step count in its type. Its target is the
walk's own stationary measure, so the conclusion carries no bias term.
[`Ttc/Sampler/Construct.lean`](Ttc/Sampler/Construct.lean) instantiates it at
`eps = ε'/(4·Vol(P′))` and gets a `Ttc.KV97Sampler` whose `law_tv` is a theorem.
`Arlib.MarkovChains.exists_unconditional_mixing_polytope` is its non-vacuity
witness (the cube `[−1,1]ⁿ`), stated so the polytope cannot be degenerate.

*Caveat, and it is the decisive one.* **This is not a polynomial-time sampler, and
must not be read as one.** Beyond the `√n` geometric loss above, the isoperimetric
constant that is actually *proved* — `κ = 2⁻ⁿ/D` in `uniformOn_iso_of_convex` — and
the only proved speediness witness — `θ = 2⁻ⁿ` (`ofReal_le_ell_unitBall`) — are
both exponentially small in the dimension. Since the conductance is
`min(θ/32, κθ²δ/(128n))` and the step count is `O(φ⁻² log(M/eps))`, **the step
count this chain certifies is exponential in `n`**. A polynomial bound needs a
dimension-free isoperimetric constant, i.e. the Localization Lemma (unproved and
unassumed here); the *speedy walk* is built
([`SpeedyWalk.lean`](Arlib/MarkovChains/Continuous/SpeedyWalk.lean)) and has the
conductance bound one wants, but its stationary bias does not decay with time, so
it is not usable at the lattice-counting tolerance — see finding 19.

**`ZLogconcaveHypothesis`, and where it is false.**
[`ZLogconcave.lean`](Arlib/Convexity/GaussianCooling/ZLogconcave.lean) discharges
Cousins–Vempala's Lemma 5.9 for `f = c·1_K` with `K` convex and measurable — no
boundedness, roundness or `0 ∈ K` — via the change of variables `x = y/A` and
Prékopa's marginal theorem, making Lemma 5.10
(`fixed_var_bound_indicator`, `fixed_var_bound_ratio_indicator`) unconditional for
a convex body.

*Caveat: the predicate as stated in `Variance.lean` quantifies over an arbitrary
`f`, and it is* **false for general log-concave `f`.** At `n = 1`, `f x = e^{−x}`:
`log z(A) = c + (3/2)log A + 1/(2A)` is strictly *convex* for `A < 2/3`, and at
`a = 1/10`, `b = 1/5` the hypothesis fails by a factor `≈ 1.93`. The obstruction is
structural — the proof needs `(A, y) ↦ f(y/A)` jointly log-concave, and a
`0`-homogeneous convex function is constant — so up to a constant factor,
indicators of convex sets are *exactly* the `f` for which the route works.
`fixed_var_bound` and `fixed_var_bound_ratio` remain sound as stated (they take
`ZLogconcaveHypothesis f` as a hypothesis), but that hypothesis must never be read
as "true for every log-concave `f`". (The counterexample is worked out in that
file's docstring, closed-form and checked numerically; it is not itself a Lean
theorem.) `LocalizationHypothesis` is untouched and still assumed.

**The *Cousins–Vempala* volume oracle is still not constructible — but a volume
oracle is.** These are two different claims and the page used to run them
together. The `volAlg` field is inhabited unconditionally by
[`Ttc.VolumeAlgorithm.monteCarlo`](Ttc/Volume/MonteCarlo.lean) (see
[the volume oracle](#assumed-about-the-algorithms-oracles) below), which is
hit-and-miss Monte Carlo at an exponential sample count and is *not* a proof of CV
Theorem 1.1. What follows is about the CV route, which remains open.

[`Ttc.VolumeAlgorithm.cousinsVempala`](Ttc/Volume/CousinsVempala.lean) is a genuine,
complete construction of `Ttc.VolumeAlgorithm` — every field discharged — built on
`VolumeAlgorithm.ofRuns` (the median boost) from Cousins–Vempala §5.2, which is
proved here unconditionally: the telescoping product, Chebyshev in relative-error
form, the product estimator's accuracy, the `4/5 → 1−p` median boost at the
`O(log 1/p)` rate, and the hot end `e^{−R²/(2s)}·Vol(K) ≤ G(s) ≤ Vol(K)`.

*Caveat 1:* four of its arguments are the residual debt, spelled out inline in its
type rather than hidden: `hphase_mean` (each phase's score is unbiased for
`G(σᵢ₊₁²)/G(σᵢ²)`) — **this is the sampler**, blocked on isoperimetry ⇒
conductance ⇒ mixing; `hphase_var` (§5.1, *available* as
`fixed_var_bound_ratio_indicator`, but only at an exact sample, so it too is
consumed through the sampler); `hphase_indep`; and `hchain_end`.

*Caveat 2: the hypothesis bundle now has a non-vacuity witness, and it is worth
being precise about what the witness shows.*
`Ttc.VolumeAlgorithm.cousinsVempalaWitness` (and
`cousinsVempalaBiasedWitness` for the biased-endpoint branch) instantiates every
argument of the construction and proves every hypothesis, so the bundle is
**satisfiable** — `cousinsVempala` is a theorem about something rather than
vacuously quantified. But the instantiation is deliberately degenerate: `Ω = Unit`,
`μ = dirac ()`, one phase, a deterministic score, variance budget `κ = 0`, and
`cousinsVempalaWitness_est` is `rfl` to `(volume K).toReal` — **it is
`VolumeAlgorithm.exact` factored through §5.2's median-of-products.** So it
certifies that the hypotheses are *consistent*; it does **not** show that the
paper's Gaussian schedule satisfies them, and it supplies no volume algorithm you
did not already have. `cousinsVempala` remains a statement of what is still to be
supplied.

*Caveat 3:* §5.2's approximations are idealized to equalities in the main
construction — `hphase_mean` asks for an *exactly* unbiased phase estimator and
`hchain_end` for an *exact* endpoint, where the real algorithm has a
nearly-uniform sampler and a last Gaussian that is only nearly the volume. The
endpoint half of that is relaxed: `G_indicator_mem_relErr`,
`run_relErr_four_fifths_biasedEnd`, `gaussianCooling_accuracy_biasedEnd` and
`VolumeAlgorithm.cousinsVempalaOfBiasedEnd` carry the endpoint bias through
explicitly. The *sampler* half is not relaxed, and relaxing it needs the
total-variation bookkeeping of [`Arlib.Probability.TV`](Arlib/Probability/TV.lean).

### The `Arlib/` staging area

`Arlib/` is a **second Lake library** in this repo holding material with no
kr-25-ssm content — randomized rounding, lattice counting, total variation,
convexity, Markov-chain conductance and mixing. It exists because the shared
library [`arlib`](https://github.com/meelgroup/arlib) is pinned to Lean/Mathlib
**v4.15.0** while this project is on **v4.32.0**, so the two cannot be
path-dependencies of each other today. Writing the general material here under
`Arlib.*` namespaces makes the eventual port a `git mv`.

One rule keeps that promise, and it is worth re-checking after any refactor:

```bash
grep -rn "^import Ttc" Arlib/     # must return nothing
```

`Ttc/**` may import both. **Part of `Arlib/` is on `Ttc.TtcProb.volume_estimate`'s
dependency path** — `Lattice/Basic`, `Lattice/Rounding/*`,
`Lattice/KV97/{Defs, Inflate, Escape, Theorem2, Corollary}`, `Convexity/Polytope`,
`Probability/Rejection` and `Probability/SubgaussianTail` are all reached from it.
**And much of the rest is now on `Ttc.ttc_volume_endToEnd`'s** — `Probability/TV`
and `Probability/UniformOn` (the sampler's `law_tv` is stated with `Arlib.TVLe`
against `Arlib.uniformOn`), `Convexity/IsoBall` (`uniformOn_iso_of_convex`) and
the `MarkovChains/` mixing chain up to
`mixesWithin_lazy_ballWalk_polytope`. What remains foundation-only is the
Cousins–Vempala volume route (`Convexity/GaussianCooling/`, the localization
files) and `KV97/Lemma1`
([`END-TO-END-PLAN.md`](END-TO-END-PLAN.md), [`AUDIT-KV97.md`](AUDIT-KV97.md)).

**Known duplication, to be resolved.** `Ttc/Rounding/Tent.lean` is now a pure
re-export of `Arlib/Lattice/Rounding/Tent.lean` (each `Ttc.*` name is a `rfl`
alias for the `Arlib` constant, checked mechanically by `example`s at the end of
[`Ttc/Rounding/ArlibBridge.lean`](Ttc/Rounding/ArlibBridge.lean)). The rest of
`Arlib/Lattice/Rounding/` still *duplicates* `Ttc/Rounding/{RoundLaw,
RoundMoments, ProdKernel, PiLintegral, TentSum}.lean` rather than replacing it:
the `Ttc/` copies are stated in terms of the project-specific
`Ttc.RoundingKernel` abstraction and `Ttc.Model.Prelude`, reached via
`Ttc.Rounding.Cl`, while the `Arlib` versions were rebuilt on a Mathlib-only
dependency chain with different statements. Collapsing them needs
`RoundingKernel` itself to move to `Arlib` first. `ArlibBridge.lean` is the map;
until the refactor happens both copies are maintained and both are green.

`Ttc/Lattice/PerCube.lean` and `Ttc/Findings/CubeLattice.lean` also overlap —
both give `lem:lattice` per polytope. `PerCube` is the one on the path (its
`TtcProb`-level form matches `Sampler/Contract`'s hypothesis shape); see
[`END-TO-END-PLAN.md`](END-TO-END-PLAN.md) "Known duplication / debt".

### How the tree is kept minimal

"Everything else is on the path" is a checkable claim, not an assertion. Two
sweeps keep it honest, and both are cheap to re-run.

**Files.** Take the transitive import closure of the roots — the abstract theorem
`Ttc.Model.Theorem`, the non-vacuity witness `Ttc.Witness.BoxProb`, the
oracle-free capstone `Ttc.Exec.EndToEnd` and its repricing `Ttc.Exec.Budget` — and
compare it with the files on disk:

```bash
cd lean && python3 - <<'EOF'
import os, re
mods = {}
for dp, _, fs in os.walk('Ttc'):
    for f in fs:
        if f.endswith('.lean'):
            p = os.path.join(dp, f)
            mods[p[:-5].replace('/', '.')] = [
                i for i in re.findall(r'^import\s+(\S+)', open(p).read(), re.M)
                if i.startswith('Ttc')]
def closure(seeds):
    seen, stack = set(), list(seeds)
    while stack:
        m = stack.pop()
        if m not in seen:
            seen.add(m); stack += mods.get(m, [])
    return seen
need = closure(['Ttc.Model.Theorem', 'Ttc.Witness.Headline',
                'Ttc.Witness.BoxProb', 'Ttc.Exec.Final'])
print(sorted(set(mods) - need))
EOF
```

It currently prints **fourteen** modules, and each is deliberate:

```
Ttc.Audit.ClosureCheck                               -- the audit-surface probes THEMSELVES;
                                                     --   they check the statement, so nothing
                                                     --   the statement proves may depend on them
Ttc.Findings.Repair                                  -- refereeing the paper (findings 2, 5, and
Ttc.Findings.Independence                            --   the hφ/hbdd independence, and what the
Ttc.Findings.OpenHalfspace                           --   printed algorithm does on a small body).
Ttc.Findings.SmallBody                               --   Off the path BY DESIGN
Ttc.Rounding.ArlibBridge                             -- documentation / audit companion
Ttc.Volume.CousinsVempala                            -- the CV route, still undischarged
Ttc.Volume.CVInstantiate                             --   and the six of its fourteen hypotheses
                                                     --   that Arlib already discharges
Ttc.Exec.Budget                                      -- ttc_volume_clean: the same repricing
                                                     --   one rung lower, so Final does not
                                                     --   route through it
Ttc.Exec.BddPrep                                     -- the agreement lemma at the preprocessed
                                                     --   formula, kept after the proof binders
                                                     --   came off ttcAlgOutput/ttcRun
Ttc.Exec.OracleFree                                  -- ttcProbOfInputs: the TtcProb built
                                                     --   with no oracle argument; a witness
                                                     --   that the bundle's oracle fields are
                                                     --   instantiable, not a step of the proof
Ttc.Exec.Statement                                   -- ttc_volume_stmt: the guarantee for the
                                                     --   UNdeduplicated run. A sibling of
                                                     --   ttc_volume_inputs, not a predecessor;
                                                     --   neither implies the other
Ttc.Exec.Regime                                      -- big_not_derivable: an independence
                                                     --   proof ABOUT the headline, so nothing
                                                     --   the headline proves can depend on it
Ttc.Witness.FullTwoCube                              -- ttc_volume_estimate's OWN non-vacuity
                                                     --   witness. See the note below: it is
                                                     --   off-path only because the seed list
                                                     --   does not name it
```

**One of those fourteen is an artefact of the seed list, not a finding.**
`Ttc.Witness.FullTwoCube` is the non-vacuity witness for the headline
`Ttc.ttc_volume_estimate` itself; it imports `Model/Theorem` rather than being
imported by it, so no choice of downstream root reaches it. Add it to `need`'s
seeds if you want the check to mean "nothing unreachable **and** every witness
accounted for". Anything else in the list is a file no one needs.

**Note that an import-closure hit is not a dependency-walk hit**: `Volume/VolSolCheck`
is *imported* by `Exec/Endgoal` but its declarations are still not *used* by any
proof (see [the dependency walk](#the-dependency-walk)).

All fourteen are imported by `Ttc.lean` and so are compiled by `lake build`. The
hazard to keep in mind is structural rather than current: since the `Ttc` library
has no glob, a file under `Ttc/` that nothing imports is not compiled at all, so
the sweep below is what covers it, not the build. Nothing the sweep would flag
under `Arlib/` has that problem —
the `Arlib` glob compiles every file there regardless of what the area roots
import.

**Declarations.** A declaration whose name occurs nowhere else — in code, in a
docstring, or in `README.md`/`AUDIT.md` — is either dead or undocumented, and
either way wants attention. Instances are exempt (typeclass inference finds them
without naming them), as is anything carrying an attribute. The sweep that found
the last round is recorded in the git history; deleting a declaration it flags and
rebuilding is the authoritative check, and that is how the current tree was
pruned: 32 declarations and one file (`CountVector.lean`, superseded by the
pathwise coupling) went, and `lake build` stayed green.

**Reading order for an auditor: `Model/`, in this order, then stop.**
[`Model/Prelude`](Ttc/Model/Prelude.lean) fixes what every name means, including
`Vol(F)` and the `(1±ε)` interval.
[`Model/Pseudocode`](Ttc/Model/Pseudocode.lean) is the code — read it against
`sections/algo.tex`. [`Model/ProblemSetting`](Ttc/Model/ProblemSetting.lean) is the
problem: what `Vol(F)` is and what `(1±ε)` means. The hypothesis bundle
[`Ttc.TtcProb`](Ttc/TtcProb.lean) — **every hypothesis the abstract result rests
on**, as fields — is one directory up.
[`Model/Theorem`](Ttc/Model/Theorem.lean) states what is proved, over `TTC`'s own
inputs and with no oracle or precision among them.
Anything you still doubt is a named lemma in one of the proof directories.

| Surface module | Contains | Status |
| --- | --- | --- |
| [`Model/Prelude.lean`](Ttc/Model/Prelude.lean) | the vocabulary: `Ttc.Space n`, `BForm`/`Lit`/`Cube`/`DNF`, `sol`, `region`, `Ttc.toDNF`, the lattices, and `Ttc.Params` (`η`, `ε'`, `δ'`, `Thresh`, `γ`, and `precision` = `GetPrecision`) | definitions only. `volSol`/`relErr` are in `Model/ProblemSetting`; `roundBody` moved to `Volume/Oracle`, being that oracle's normalisation rather than the paper's vocabulary |
| [`Model/Pseudocode.lean`](Ttc/Model/Pseudocode.lean) | `SketchState`, `Oracles`, `dropCovered`, `haltLevel`, `absorbLevel`, `step`, `run`, `ttcAlgOutput`, `ttcRun` | modelled; see caveats |
| [`Model/ProblemSetting.lean`](Ttc/Model/ProblemSetting.lean) | **the problem only**: `volSol` (= `Vol(F)`, what `alg:ttc` estimates) and `relErr` (the `(1±ε)` interval). 60 lines, no hypothesis bundle — the analogue of `nfalean/ApproxNFA/Model/ProblemSetting.lean` (53 lines) | what is estimated, and what "approximately" means |
| [`Ttc/Volume/Oracle.lean`](Ttc/Volume/Oracle.lean) | `VolumeAlgorithm` (Cousins–Vempala Thm 1.1), `volGood` | `Vol_ED`'s interface — **another paper's** assumption bundle, so not part of this paper's problem setting |
| [`Ttc/Sampler/Interface.lean`](Ttc/Sampler/Interface.lean) | `KV97Sampler` (**15** fields — 14 named plus the `[fintypeJ : Fintype J]` instance, which is what `Lean.getStructureFields` counts and what `AUDIT.md` §2 reports) | `GenerateSamples`' interface, likewise another paper's |
| [`Ttc/TtcProb.lean`](Ttc/TtcProb.lean) | `ttcOutput` (the run as a random variable over an abstract `Ω`), `TtcProb` (**59** fields — count re-checked with `Lean.getStructureFields`, which is authoritative; a hand count of the source undercounts) | the abstract interface: the complete list of assumptions |
| [`Model/Theorem.lean`](Ttc/Model/Theorem.lean) | [**`Ttc.ttc_volume_estimate`**](Ttc/Model/Theorem.lean): `thm:volumettc` **and** `thm:runtime` as one conjunction over `TTC`'s own inputs — `atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos` (the **eleven** the docstrings count) plus the two per-call cost constants `cVol cSample`, so 13 explicit and 15 raw. No volume hypothesis, no inscribed-ball data, no degeneracy hypothesis, no `hbdd`, no interpretation, no parameter block, no converter, **no oracle** (the bundle is the closed term `Ttc.algOracles`, `Model/Pseudocode`) and **no precision** (every occurrence is `P.precision gammaHat`, `GetPrecision`'s output) | the statement layer: one theorem, both conjuncts over one run of `Ttc.ttc`; the proof rewrites by `ttc_eq_ttcPairLaw` and applies two named lemmas. **It is the guarantee for the *amended* algorithm** — with the dilation line, on the cleaned formula, under a constructed (not maximal) ball. `AUDIT.md` §1g |
| [`Ttc/Estimate.lean`](Ttc/Estimate.lean) | [**`TtcProb.volume_estimate`**](Ttc/Estimate.lean) (`Pr ≥ 1−δ`) and `TtcProb.runtime`, the bundle versions — their types name the *assumed* `T.O` and `T.ρ` | proved from the `TtcProb` fields. Moved out of `Model/Theorem` for that reason; still load-bearing (`Coupling/Product` consumes it) |
| [`Exec/Statement.lean`](Ttc/Exec/Statement.lean) | `Ttc.ttc_volume_stmt`: `ttc_volume_final` with the converter pinned to `Ttc.toDNF`, 24 explicit binders; plus `Ttc.toDNF_length_gt_card_cubes`, which proves `hlen` is *not* derivable | a **sibling**, not a predecessor: it is the guarantee for the *undeduplicated* run, so `Ttc.ttc_volume_inputs` does not imply it |
| [`Exec/CubeBounds.lean`](Ttc/Exec/CubeBounds.lean) | `Ttc.one_le_card_cubes_of_isPositive` (`hm` from `hφ`) and `Ttc.one_le_card_facets_of_isBounded` (`hr` from `hbdd`, via `region [] = univ` being unbounded) | two former binders, discharged |
| [`Exec/Dedup.lean`](Ttc/Exec/Dedup.lean) | `Ttc.toDNFd`, the duplicate-free DNF, with `mem_toDNFd`, `toDNFd_isDNFOf`, `toDNFd_isPositive` and `length_toDNFd_le_card` (an **equality**) | `hlen`, discharged — at the cost of a smaller `m`, hence a larger `deltaPrime` |
| [`Exec/Inputs.lean`](Ttc/Exec/Inputs.lean) | **`Ttc.ttc_volume_inputs`** (`ttc_volume_final` with `M`/`M_eq`, the converter and its two properties, `hm`, `hr`, `P`/`hP` and `hlen` discharged — **17 explicit binders**) and **`Ttc.ttc_volume_vol`**, the same with `big` replaced by `hvol : Thresh/4 ≤ Vol(F)` | two intermediate rungs, **no longer the strongest**: `hvol` is discharged one rung up in `Exec/Rescaled`. Read their *types* |
| [`Exec/Regime.lean`](Ttc/Exec/Regime.lean) | `Ttc.Box.big_not_derivable` (an explicit counterexample), `big_of_thresh_le_volume`, `thresh_le_volume_of_big`, `sum_rates_box_window` | **`big` is independent, proved.** No `def`/`structure`/`class` in the file at all |
| [`Witness/Inputs.lean`](Ttc/Witness/Inputs.lean) | `Ttc.TwoCube.ttc_volume_inputs_two_cube`, the two-cube hypotheses transported to `Ttc.toDNFd`, and `toDNFd_twoForm` | non-vacuity for the 17-binder statement |
| [`Exec/RegimeSum.lean`](Ttc/Exec/RegimeSum.lean) | `Ttc.rate_ge_pointwise` — every enumerated lattice point contributes `≥ (1−ε')²(1−η)/10^{ρn}`, **pointwise, no fiber counting** — and its sum | the crux of making `big` a theorem |
| [`Exec/RegimeCube.lean`](Ttc/Exec/RegimeCube.lean) | `Ttc.lattice_cube_of_dnf`: `lem:lattice` per cube over plain data (the bundle version being `TtcProb.lattice_cube_lo`) | one of the two per-cube inputs |
| [`Exec/RegimeInputs.lean`](Ttc/Exec/RegimeInputs.lean) | `Ttc.e2eSampD_almostUniform`: `eq:almostuniform` for the capstone's own sampler at every cube, **with no nonemptiness hypothesis** (`exists_intLattice_mem_ball`); `Ttc.mcVol_ge` | the other per-cube input |
| [`Exec/RegimeMain.lean`](Ttc/Exec/RegimeMain.lean) | **`Ttc.big_of_volume`**: the regime condition **proved** from `Thresh/4 ≤ Vol(Sol F)` | what turns `big` from a binder into a theorem |
| [`Witness/TwoCubeVol.lean`](Ttc/Witness/TwoCubeVol.lean) | `Ttc.TwoCube.two_cube_thresh_le_volSol`: the two-cube instance meets `hvol`, because it sizes its boxes at `max 1 Thresh` | non-vacuity of the volume hypothesis |
| [`Exec/Scale.lean`](Ttc/Exec/Scale.lean) | `Ttc.scaleAtoms` and the dilation algebra: `sol`, `region`, `volSol`, boundedness and the inscribed ball all transport, `volSol` scaling by `cⁿ` | the input dilation |
| [`Exec/ScaleFactor.lean`](Ttc/Exec/ScaleFactor.lean) | `Ttc.scaleFactor = max 1 (Thresh/(Vₙ·γ̂ⁿ))` — computable from `γ̂` and `n`, **no knowledge of `Vol`** — and `thresh_le_scaled_ball_volume` | how far to dilate |
| [`Exec/Inscribed.lean`](Ttc/Exec/Inscribed.lean) | `Ttc.cenOf`/`Ttc.gammaOf`: `GetPrecision`'s ball, constructed. `ball_subset_cenOf` is **unconditional**; only positivity needs `hint` | `alg:prec` line 86, minus the optimality claim |
| [`Exec/Rescaled.lean`](Ttc/Exec/Rescaled.lean) | **`Ttc.ttc_volume_rescaled`** (16 binders, no volume hypothesis — `Ttc.hvol_scaled` discharges `hvol` by the dilation) and **`Ttc.ttc_volume_full`** (13, no ball data); also `Ttc.autoCen`/`Ttc.autoGamma`, the ball the headline actually uses | **an amendment to `alg:ttc`, not a sharper analysis.** The printed algorithm returns `0` on a body of volume `10⁻⁶` and is *wrong* there — finding 20 |
| [`Exec/Cleanup.lean`](Ttc/Exec/Cleanup.lean) | `Ttc.cleanDNF` / `Ttc.cleanForm`: zero-normal atoms constant-folded away (`Set.univ` literals deleted, `∅` cubes dropped), so `Ttc.coeff_ne_zero_toDNFd_cleanForm` holds outright. `Ttc.not_isDNFOf_cleanDNF` is why the *formula* has to move with the DNF | **benign**: `Ttc.sol_cleanForm` is an **exact set equality**, so the body measured is literally unchanged and nothing is post-processed |
| [`Exec/CleanInput.lean`](Ttc/Exec/CleanInput.lean) | **`Ttc.ttc_volume_cleanInput`** (12 binders — `hcoeff` gone, nothing added): `ttc_volume_full` run on `Ttc.cleanForm atoms φ`, with `Ttc.cleanBdd`, `Ttc.cleanInt` and `Ttc.volSol_cleanForm` transporting the hypotheses and the target | **the rung the headline restates.** `hcoeff`, discharged; the accuracy conclusion is still about the **original** `volSol (atomSet atoms) φ` |
| [`Exec/Degenerate.lean`](Ttc/Exec/Degenerate.lean) | **`Ttc.hint_not_derivable`**: `(x ≤ 0 ∧ −x ≤ 0) ∨ (x ≤ 1 ∧ −x ≤ 1)` satisfies `hφ`, `hbdd`, `hcoeff` and `0 < Vol(F)` while `hint` fails; plus `Ttc.volume_biUnion_nondegenCubes` (pruning is invisible to the volume) and `Ttc.not_isDNFOf_nondegenCubes_degForm` (but destroys `IsDNFOf`) | **a negative result.** `hint` is a genuine condition on the input; the null-set repair is blocked because `lem:lattice` counts lattice points, which are themselves null |
| [`Findings/Independence.lean`](Ttc/Findings/Independence.lean) | `Ttc.Independence.exists_isBounded_not_isPositive` and `…exists_isPositive_not_isBounded` (plus a non-degenerate half-space version of the latter) | **`hφ` and `hbdd` are independent both ways.** Neither can be dropped in favour of the other. No claim that the pair is weakest |
| [`Findings/OpenHalfspace.lean`](Ttc/Findings/OpenHalfspace.lean) | what removing `hφ` would cost: `Ttc.volume_sol_openAtomSet_eq` (the volume cannot tell open from closed), `Ttc.exists_latticeCount_ne_of_open` (the **lattice count can**, at every precision), `Ttc.exists_isBounded_region_not_isBounded_posify` (`hbdd` stops transferring) | a costing, **not** a removal: bounded refactor, two extra hypotheses, and the run would count the lattice points of a provably different set. Nothing here is imported by the capstone |
| [`Witness/FullTwoCube.lean`](Ttc/Witness/FullTwoCube.lean) | `Ttc.TwoCube.ttc_volume_estimate_two_cube_full` and `…_full_at`: non-vacuity at the headline's **eleven** binders (`cVol`/`cSample` stay universally quantified), bounds `1/10` and `3/4` positive inside the statement; `hint` from `Ttc.TwoCube.interior_region_nonempty_two_d` | **non-vacuity of the current headline.** The run is on the *dilated* body of the *cleaned* formula under the *constructed* ball |
| [`Witness/Headline.lean`](Ttc/Witness/Headline.lean) | `Ttc.TwoCube.ttc_volume_estimate_two_cube` and `…_at`, with the bounds `1/10` and `3/4` proved positive **inside** the statement | non-vacuity for [`Ttc.ttc_volume_inputs`](Ttc/Exec/Inputs.lean) — **two rungs down, not the current headline**; the file says so itself. Use `Witness/FullTwoCube` for the headline |
| [`Volume/VolSolCheck.lean`](Ttc/Volume/VolSolCheck.lean) | what `volSol` is a volume *of*: an independent `Bool` evaluator, the LRA form, measurability, and the `toReal ⊤` hazard | the audit surface for one symbol |
| [`Exec/Endgoal.lean`](Ttc/Exec/Endgoal.lean) | `Ttc.ttc_volume`: the same two theorems restated over `(atoms, φ, ε, δ)`, space and parameters constructed, obligations as visible binders | a restatement, built by `lake build`. Read its *type* if you care about the capstone; it is not where the assumptions are enumerated |
| [`Exec/EndToEnd.lean`](Ttc/Exec/EndToEnd.lean) | `Ttc.ttc_volume_endToEnd`: the same statement with every oracle binder removed, at `1 − δ − δ/4` | an intermediate step. Its *type* is the honest statement of what is assumed on that route — read it, not this table |
| [`Exec/CanonPolytope.lean`](Ttc/Exec/CanonPolytope.lean) | `Ttc.ttc_volume_endToEnd_canon`: the same, with the nine polytope-description binders discharged; `Ttc.canon_body_eq_smul_region` is the crux, and it is an **equality** | an intermediate step |
| [`Exec/Budget.lean`](Ttc/Exec/Budget.lean) | `Ttc.ttc_volume_clean` (alias `ttc_volume_endToEnd_delta`): `ttc_volume_endToEnd` at the internal `δ₀ = 4δ/5`, so the conclusion is `1 − δ`; plus the box witnesses at `(1/3, 9/10)` and `(1/2, 1/4)` | a repricing, and where the non-vacuity witnesses for the clean budget live |
| [`Exec/Final.lean`](Ttc/Exec/Final.lean) | **`Ttc.ttc_volume_final`**: no oracle, no polytope description, clean `1 − δ`, 26 explicit binders, all inputs | **the strongest result.** Read its *type*, and its module docstring for which `δ` is which |

### What `Ttc/Model/Pseudocode.lean` does and does not do

It is a line-by-line model of `alg:ttc` lines 22–46: the state `(X, level)` with
`p = 2^(−level)`, the order of operations, both `while` guards, the coverage
filter, and the output `|X|/p`. Read it beside the pseudocode; the module
docstring carries the line-by-line table and the four numbered deviations.

Four external calls are **fields of `Ttc.Oracles`** rather than definitions —
`Vol_ED` (`vol`), the Poisson draw (`pois`), `GenerateSamples` (`gen`), and the
fair-coin thinning (`thin`). So the state evolution is deterministic *given the
oracle's answers*, and all the randomness sits at that boundary. That is
deliberate, and it is what makes the coupling constructible:
[`Ttc.trajOracles`](Ttc/Coupling/Family.lean) inhabits the bundle with oracles
that read a trajectory of the level family, and the run driven by *those* is
provably the family ([`Ttc.card_run_eq_sum_traj`](Ttc/Coupling/Run.lean)). What
the bundle itself constrains is only the *shape* of the calls plus two contracts
below; what the draws are *distributed* like is said by the `law_eq`/`oracle_eq`
fields of `Ttc.TtcProb`, which name the coupled family directly.

**Two contracts were missing and are now stated.** `thin` returns a
*sub-multiset* (`Ttc.Oracles.thin_le`), not merely one of no greater
cardinality — the loop deletes elements, it never invents them; and
`GenerateSamples` returns points of `P(cᵢ) ∩ 𝕃ⁿ`
([`TtcProb.gen_mem`](Ttc/TtcProb.lean)), where before only the
*count* was fixed (`Ttc.Oracles.gen_card`). Both are needed before `𝒳` can be
treated as a count vector over a fixed finite set, which
[`TtcProb.run_state_mem`](Ttc/Lattice/Assembled.lean) now proves.

**Every randomised call is indexed by the level.** `Ttc.SketchState` carries the
level `j` with `p = 2^(−j)` rather than `p` itself, and `thin`, `pois` and `gen`
take it as an argument. The pseudocode has no such index; it is here because
without it the model *cannot express what the algorithm does*. An unindexed
`halve : Multiset → Multiset` is a function, so applying it twice to the same
multiset gives the same answer — once a thinning happens to be a no-op (which has
probability `2^(−|X|) > 0`), every later thinning of that multiset is forced to be
the same no-op and `𝒳` can never shrink again, which is not the algorithm's
behaviour. Indexing fixes that, and it is also what lets a distributional
hypothesis speak of the level-`j` process: `Err(j)` and `Nois(j)` are events about
that index, and `thin j₀ j'` reads off the survivors at level `j'` in one call
rather than iterating a coin (`Model/Pseudocode`, deviation (c)).

The precision `ρ` is threaded properly: `GenerateSamples` is
`gen : ι → ℕ → ℕ → ℤ → Multiset (Space n)`, `ρ` is fixed before the loop
(`alg:ttc` line 17) and passed at every call, and the `rho_eq` field of
`Ttc.TtcProb` pins it to `⌈log₁₀(γ/γ̂)⌉` (`alg:prec` line 91). The LP computing
`γ̂` is still not modelled — `gammaHat` is an input.

Both `while` loops are modelled as **exit levels**, not recursions and not fuelled
iterations (`Model/Pseudocode`, deviation (a)):
[`haltLevel`](Ttc/Model/Pseudocode.lean) and
[`absorbLevel`](Ttc/Model/Pseudocode.lean) are the least level at or above the
current one at which the loop's guard fails, an `sInf` over `ℕ`, and the step
jumps straight there. Termination is therefore neither claimed nor needed for the
accuracy theorem — which matters, because the second loop has none to give: it
exits when repeated thinning brings `Nᵢ + |X|` under `Thresh`, which happens only
with high probability. On a run where it never exits the `sInf` is over an empty
set, `Nat.sInf` returns `0`, and the loop simply does not move (deviation (b));
nothing depends on that corner, because every consequence drawn from an exit level
has the form "every level strictly below it had the guard true", which is then
vacuous. (`Ttc.TtcProb.runtime` *does* need the loops to exit, and says so — see
[Scope](#scope-stated-precisely).)

What is proved is structural, and lives in
[`Invariants.lean`](Ttc/Invariants.lean) rather than in `Model/` — the level
never rewinds (`Ttc.le_haltLevel`, `Ttc.le_absorbLevel`,
`Ttc.le_step_level`), every level a loop passed through had its guard true
(`Ttc.lt_haltLevel`, `Ttc.lt_absorbLevel`), the filter and the thinning only
remove points (`Ttc.card_dropCovered_le`, `Ttc.card_thin_le`).

### The output, and what is assumed about it

A completed formalisation of an algorithm carries **two** models — a
paper-faithful transcription, and the operational one the analysis actually
reasons about — joined by a *proved* bridge saying they compute the same thing.
That bridge is what puts the operational model outside the trusted base.

This development needs no such bridge, because it has only the transcription.
[`Ttc.ttcOutput`](Ttc/TtcProb.lean) *is* `Ttc.run` on the cubes
`ToDNF` returns for the input formula, with the oracles drawn at a sample point —
so it takes what `TTC(F, ε, δ)` takes, and the headline measures the algorithm
directly:

```lean
noncomputable def Ttc.ttcOutput (P : Params) (O : Ω → Oracles n (Cube A))
    (toDNF : BForm A → DNF A) (ρ : ℤ) (φ : BForm A) (ω : Ω) : ℝ :=
  run P (O ω) ρ (toDNF φ)
```

`lem:numlattice` itself is **not** assumed any more: it is
[`Ttc.TtcProb.numlattice`](Ttc/Coupling/NumLattice.lean), a theorem about that
same output. Nor is the epoch covering it is derived from: that used to be a
`numlattice_union` field, and is now
[`Ttc.TtcProb.numlattice_union`](Ttc/Coupling/Transfer.lean), a theorem with the
deleted field's statement verbatim:

```lean
theorem Ttc.TtcProb.numlattice_union (T : TtcProb A n) :
    ∃ (jstar : ℕ) (lamStar : ℝ),
      (1 - T.P.epsPrime) * T.P.thresh / 8 ≤ lamStar ∧
      (T.μ {ω | ¬ ((1 - T.ε/2) * T.L ≤ ttcOutput T.P T.O T.toDNF T.ρ T.φ ω ∧
                 ttcOutput T.P T.O T.toDNF T.ρ T.φ ω ≤ (1 + T.ε/2) * T.L)}).toReal
        ≤ (∑ t ∈ Finset.range jstar,
              2 * Real.exp (-(T.P.epsPrime ^ 2 * (lamStar * 2 ^ t) / 3)))
            + T.P.m * Real.exp (-(T.P.thresh / 6)) + T.δ / 2
```

That the three terms total at most `δ`, at the algorithm's own `Thresh` and `δ'`,
is [`Ttc.numlattice_failure_le`](Ttc/Process/SketchProcess.lean); the per-epoch
sizes are [`levelLaw_err_le`](Ttc/Process/SketchProcess.lean) and
[`levelLaw_noise_le`](Ttc/Process/SketchProcess.lean). So the headline needs
**no side hypothesis**. And `L` is no longer a bare real: the field `L_eq` pins
it to [`normalisedCount M φ ρ`](Ttc/Lattice/Decomposition.lean)
`= |Sol(F) ∩ 𝕃ⁿ|/10^(ρn)`, the actual lattice count of the actual solution set —
which is what makes `lem:lattice` a theorem about it rather than an assumption.
The fields `ptE_mem`/`ptE_onto` then make `ptE` a bijection onto `Sol(F) ∩ 𝕃ⁿ`, so
`Lidx` is that count too ([`TtcProb.Lidx_eq`](Ttc/Coupling/Transfer.lean)) rather
than a free choice.

What the proof of `numlattice_union` consumes are the **sampler fields**. It is
[`Ttc.numlattice_union_of_model`](Ttc/Coupling/Transfer.lean) applied to them: the
run's failure event is the `toTraj`-preimage of the trajectory-space one
(`oracle_eq`), `Measure.le_map_apply` pushes its measure forward along `law_eq`,
and [`Ttc.traj_numlattice_le`](Ttc/Coupling/Run.lean) bounds it there. The
accuracy window comes from the *proved* `theta_lo`/`theta_hi` through
[`Ttc.window_of_two_sided`](Ttc/Coupling/Transfer.lean) — four factors,
`(1±ε')` for the concentration, `(1±ε')` for `Vol_ED`, `(1±ε')` for the sampler
and `(1±η)` for `lem:lattice`, which is why the window is `ε/2` and not the
pre-`eq:sampler` `ε/3`. The epoch index `j*` the bound is stated at is **not**
taken from the instance: it is produced by
[`Ttc.exists_epoch`](Ttc/Coupling/Transfer.lean) from `big` and
[`Ttc.TtcProb.thresh_pos`](Ttc/Coupling/Transfer.lean), and the first-loop cut-off
it needs at that index comes from `vol_pos` and
[`Ttc.TtcProb.vol_lt_two_total`](Ttc/Coupling/Transfer.lean) through
[`Ttc.rate_small_of_epoch`](Ttc/Coupling/Transfer.lean).

The structure is inhabited **non-degenerately**
([`Ttc.Box.nonempty_ttcProb`](Ttc/Witness/BoxProb.lean), witness
[`Ttc.Box.boxProb`](Ttc/Witness/BoxProb.lean)): the box `[0,c]ⁿ` with
`c ≥ Thresh`, sampled by the coupled family. Its solution set is nonempty, its
`L` is at least `cⁿ ≥ Thresh`, and its `numlattice_union` obligation is
discharged **by proof**, not by an empty failure event. Since the sampler became a
`KV97Sampler`, the witness also has to *build* that construction for the box, and
it does: the dilated box's facet normals are unit vectors and the inflation
`κ = √(2 log 48) + √(2 log r) > 1` exceeds the rounding radius, so every
enumerated point's tent sits entirely inside the inflated body
([`Ttc.Box.setIntegral_prodTent_bxInflated`](Ttc/Witness/BoxProb.lean)), each
unnormalised weight is exactly `1`, and the rejection-normalised law is *exactly*
uniform — `eq:almostuniform` attained with no error to spend. Had the inflation
been smaller than the rounding radius the box would **not** have discharged
`sampD_eq`. The old degenerate witness `Ttc.trivialProb` has been deleted: with
`D = []` it forces `Lidx = 0` and so `∑θ = 0`, which contradicts `big` — via the
now-*derived* [`TtcProb.theta_pos`](Ttc/Coupling/Transfer.lean), which gets
`0 < ∑θ` out of `big` and `thresh_pos` rather than assuming it.

## Paper ↔ Lean map

Keyed by `\label`, not by number — numbers shift whenever a `\begin{lemma}` is
added or uncommented. (At the time of writing the counter runs
`thm:decomposition` = Lemma 1, `lem:chernoff` = 2, `lem:process` = 3,
`lem:integerlattice` = 4, `lem:nonconv` = 5, `claim:cl` = 6, `lem:lattice` = 7,
`lem:numlattice` = 8; `claim:helper` = Claim 1. Note `claim:cl` uses a `lemma`
environment, so it renders as a *Lemma*, not a Claim.)

Declaration names are given without line numbers on purpose: the tree moves fast
enough that anchors were wrong more often than right. Every name below is
`grep`-able, and every one was checked to exist against the compiled environment.

| `\label` | Statement | Lean | Status |
| --- | --- | --- | --- |
| `thm:decompose` | decomposition takes exponential time | — | out of scope (runtime of the decomposition) |
| `thm:runtime` | `O(mn⁴)` runtime | [`Ttc.runCost`, `Ttc.runCost_le`](Ttc/Runtime.lean), [`Ttc.TtcProb.runtime`](Ttc/Estimate.lean) | **the paper's own accounting, proved** — under `Ttc.Terminates`, and charging only what the paper charges. See [Scope](#scope-stated-precisely) |
| `thm:decomposition` | `⋃ᵢ P(cᵢ) = Sol(F)` | [`sol_eq_iUnion_region`](Ttc/Lattice/Decomposition.lean), `region_subset_sol`, `sol_subset_iUnion_region`; for the bundle [`TtcProb.sol_eq_union`](Ttc/Capstone.lean) | **proved** |
| `lem:chernoff` | Poisson tail bound (Soos et al.) | [`poisson_tail`](Ttc/Process/Chernoff.lean), `poisson_lower_tail`, `poisson_tail_two_sided`; engine `mgf_poissonMeasure`, `bennett_le` | **proved** — no longer external |
| ↳ its two uses | `Pr[N > Thresh] ≤ e^(−Thresh/6)` and `Pr[\|N−λ\| ≥ ε'λ] ≤ 2e^(−ε'²λ/3)` | [`poisson_overflow`, `poisson_relative`](Ttc/Process/Chernoff.lean) | **proved** — both constants confirmed exact |
| `lem:process` | three sampling procedures are equivalent | [`poisson_splitting`, `poisson_splitting_paper`, `rate_mem_interval`](Ttc/Process/Poisson.lean) | **proved** |
| `lem:integerlattice` | KV97 Thm 3, single polytope | — | external; superseded by `lem:nonconv` |
| `lem:nonconv` | `vol Q ∈ [(1−η)\|Q∩ℤⁿ\|, (1+η)\|Q∩ℤⁿ\|]` | skeleton [`nonconv_lower`, `nonconv_upper_deflated`, `nonconv_upper_repaired`](Ttc/Nonconv/Core.lean); geometry [`FacetSystem.inflated_subset_smul_deflated`, `volume_inflated_le`](Ttc/Nonconv/Geometry.lean) | proved from `claim:cl` — **see findings 1 & 2** |
| ↳ repaired | same statement, internal `θ = η/2` | [`nonconv_repaired`, `repair_upper_arith`, `repair_lower_arith`](Ttc/Findings/Repair.lean) | **proved** |
| ↳ shell bound, instantiated | `vol Q' ≤ (1+m(K−1))·vol Q` and `vol Q ≤ (1+m(K−1))·vol Q''` | [`piece_inflated_subset_homothety_zero`, `volume_shell_le`, `FacetSystem.volume_body_inflated_le`, `FacetSystem.volume_body_deflated_le`](Ttc/Nonconv/Recentred.lean) | **proved** — both sides; `shell_bound`'s three hypotheses discharged from geometry |
| ↳ `Q = Sol(F)` | the facet system of a positive DNF | [`facetSystem`, `region_eq_piece`, `body_eq_sol`](Ttc/Nonconv/FacetOfDNF.lean) | **proved** for `DNF.IsPositive` — see finding 5 |
| ↳ without common ball | per-polytope homothety + shell bound | [`piece_inflated_subset_homothety`, `volume_piece_inflated_le`, `body_subset_union_shells`, `shell_bound`](Ttc/Nonconv/Recentred.lean) | **proved** |
| ↳ **assembled, nothing assumed** | `lem:nonconv` for an actual facet system against its own `\|Q∩ℤⁿ\|` | [`FacetSystem.nonconv_of_ball`, `card_le_of_claim_a`, `deflated_le_card`, `nonconv_recentred_general`](Ttc/Nonconv/Assembled.lean) | **proved** from the ball hypothesis alone |
| ↳ `Q ∩ ℤⁿ` is finite | not assumed — it follows from `claim:cl`(a) | [`finite_of_forall_finset_card_le`, `ncard_inter_intLattice`](Ttc/Nonconv/BallFacet.lean) | **proved** |
| ↳ inscribed ball ↔ facet form | `B(cᵢ,γ) ⊆ Pᵢ  ⟺  γ‖A_ij‖ ≤ b_ij − A_ij·cᵢ` | [`FacetSystem.ball_subset_piece`, `FacetSystem.facet_of_ball_subset`](Ttc/Nonconv/BallFacet.lean) | **proved** both ways |
| `claim:cl` | rounding hits/misses `Q` w.p. `1 ± η/2` | **all three discharged for the actual rounding** — (a) [`prodKernel_claim_cl_a`](Ttc/Rounding/ProdLaw.lean), (b) [`prodKernel_claim_cl_b`](Ttc/Rounding/ClB.lean), (c) [`claim_cl_c`](Ttc/Rounding/Cl.lean), over [`prodKernel`](Ttc/Rounding/ProdKernel.lean); core [`rounding_tail_bound`](Ttc/Rounding/Hoeffding.lean) | **proved**, no residual hypothesis — see finding 3 |
| ↳ the rounding itself | `rnd p = ⌊p⌋ + Bernoulli(p−⌊p⌋)`, coordinatewise | density [`tent`](Arlib/Lattice/Rounding/Tent.lean) (re-exported as `Ttc.tent`), kernel [`prodKernel`](Ttc/Rounding/ProdKernel.lean), normalisation `integral_prod_tent` | **constructed** — the paper only cites KV97 |
| ↳ (a)/(c), the `p`-side | independence of the displacement's coordinates | [`iIndepFun_disp`, `ae_disp_mem_Icc`, `integral_disp_eq_zero`, `prodKernel_escape_bound`](Ttc/Rounding/ProdLaw.lean) | **proved** |
| ↳ (b), the `z`-side | the law of `rnd p` on `ℤⁿ` is a two-point product | [`roundLaw`](Ttc/Rounding/RoundLaw.lean), [`tentInt_eq_two_point`, `integral_tentInt_disp`, `iIndepFun_latDisp`](Ttc/Rounding/RoundMoments.lean), [`roundLaw_escape_bound`](Ttc/Rounding/ClB.lean) | **proved**; the crossing uses `−A_j` ([`cover_of_notMem_body_deflated`](Ttc/Rounding/ClB.lean)) |
| `claim:helper` | `kⁿ ≤ (1+η/4)/(1−η/4)` | [`claim_helper`, `claim_helper_of`, `exp_two_mul_le_div`](Ttc/Constants/Arith.lean) | **proved** — see finding 4 |
| `lem:lattice` | `Vol(F) ∈ (1±η)·\|Sol(F) ∩ 𝕃ⁿ\|/10^(ρn)` | [`lattice_of_dnf`](Ttc/Lattice/Assembled.lean), and for the problem instance [`TtcProb.lattice_lo`/`lattice_hi`](Ttc/Lattice/Assembled.lean) | **proved** — formerly two fields of `TtcProb` |
| ↳ per polytope (`analysis.tex:271`) | the same, for one `P(cᵢ)` | [`TtcProb.lattice_cube_lo`/`lattice_cube_hi`](Ttc/Lattice/PerCube.lean), via the singleton DNF `[i]` (`cubeForm`, `singleton_isDNFOf`, `sol_cubeForm`, `card_facetIndex_singleton_le`) | **proved**, no hypothesis added — this is what discharged `theta_window_cube`'s `hlatLo`/`hlatHi` |
| ↳ transport `ℤⁿ ↔ 𝕃ⁿ = 10⁻ᵖ·ℤⁿ` | | [`lattice_of_scaled`, `ncard_inter_lattice_smul`, `volume_smul_body`, `lattice_bounds`](Ttc/Lattice/Transport.lean) | **proved** |
| `lem:numlattice` | sketch output within `(1±ε/2)` w.p. `1−δ` | [`TtcProb.numlattice`](Ttc/Coupling/NumLattice.lean), from `TtcProb.numlattice_union` plus [`numlattice_failure_le`](Ttc/Process/SketchProcess.lean); skeleton [`epoch_series_le`, `err_sum_le_delta`, `noise_bound_le_delta`, `numlattice_failure_bound`, `sketch_interval`, `sketch_window`](Ttc/Process/Sketch.lean) | **theorem** — and so is the epoch covering it consumes, [`TtcProb.numlattice_union`](Ttc/Coupling/Transfer.lean) |
| ↳ **the covering, from the sampler description** | the ex-field, proved: transport the coupled-run bound to an arbitrary `Ω`/`μ`/`O` | [`numlattice_union_of_model`, `numlattice_union_of_traj`, `window_of_two_sided`, `window_of_exact`, `exists_epoch`, `rate_small_of_epoch`, `TtcProb.thresh_pos`, `TtcProb.vol_lt_two_total`](Ttc/Coupling/Transfer.lean) | **proved** — this is what deleted the last assumed probability field, and then the assumed epoch index too |
| ↳ the coupled level family | `𝒳ⱼ` for **all** `j` on one space, nested thinning from level `0` | [`famCount`, `famLaw`, `map_trajLaw_eval`](Ttc/Coupling/Family.lean) with `trajLaw`, nesting [`trajLaw_ae_nested`](Ttc/Coupling/Run.lean) | **constructed** — the object finding 15 says the paper never builds |
| ↳ the coupling to the run | the oracles read the family; `\|𝒳\| = ∑ₛ ω(J)ₛ` **pathwise** | [`trajOracles`](Ttc/Coupling/Family.lean), [`CoupledAt`, `coupledAt_step`, `coupledAt_foldl`, `card_run_eq_sum_traj`, `run_eq_traj`](Ttc/Coupling/Run.lean) | **proved** — equality of random variables, not of laws |
| ↳ the halving trigger | every level the run crosses had a large rate or an overflow | [`card_add_pois_le`, `step_trigger`, `foldl_trigger`, `level_cap_subset`](Ttc/Coupling/Run.lean), [`lt_haltLevel`, `lt_absorbLevel`](Ttc/Invariants.lean) | **proved** — what bounds `Pr[⋃_{j≥j*} Nois(j)]` |
| ↳ **`lem:numlattice` for the coupled run** | the paper's three-term bound, for `Ttc.run` driven by the family | [`traj_numlattice_le`, `traj_failure_le`, `trajLaw_err_le`, `trajLaw_noise_le`, `epoch_reindex`, `totalRate_reindex`](Ttc/Coupling/Run.lean) | **proved**, nothing probabilistic assumed — and with a *smaller* right-hand side than the paper's (no `+ δ/2`) |
| ↳ the non-degenerate witness | the box `[0,c]ⁿ`, `c ≥ Thresh`, sampled by the coupled family, with a genuine `KV97Sampler` | [`Box.boxProb`, `Box.nonempty_ttcProb`, `Box.smp`, `Box.setIntegral_prodTent_bxInflated`](Ttc/Witness/BoxProb.lean); geometry [`boxAtoms`, `boxCube`, `boxDNF`, `boxForm`, `sol_boxForm`, `normalisedCount_box_ge`](Ttc/Witness/Box.lean) | **constructed** — replaces the deleted `trivialProb` |
| `eq:almostuniform` / `eq:sampler` (`related.tex:21`) | `GenerateSamples`' law is pointwise within `(1±ε')` of uniform on `P(cᵢ) ∩ 𝕃ⁿ` | [`Ttc.AlmostUniform`](Ttc/Sampler/Contract.lean); [`TtcProb.samp_unif`](Ttc/Sampler/Bridge.lean) via `almostUniform_of_kv97_density`, `almostUniform_transport`, `escape_of_mem_body`; from [`Arlib.KV97.theorem2`](Arlib/Lattice/KV97/Theorem2.lean) and [`ratio_bounds_tuned_sharp`](Arlib/Lattice/KV97/Corollary.lean) | **proved** — formerly a field. The remaining input is the *construction* `sampler : KV97Sampler`, whose one quantitative field is `law_tv` (a total-variation bound at `ε'/(4·Vol(P′))`, not the old pointwise `density_au`). On the capstone's route `sampler` is no longer an input either: [`Ttc.e2eSampler`](Ttc/Exec/EndToEnd.lean) builds it from the lazy ball walk and **proves** `law_tv` |
| the Invariant (`analysis.tex:265`) | `(1−ε')²(1−η)/10^(ρn) ≤ θ s ≤ (1+ε')²(1+η)/10^(ρn)` | [`TtcProb.theta_lo`/`theta_hi`](Ttc/Sampler/Bridge.lean), from [`TtcProb.theta_window_cube`](Ttc/Lattice/PerCube.lean) and [`theta_window`](Ttc/Sampler/Contract.lean) | **proved** — formerly two fields, statements byte-identical |
| `alg:ttc` line 18 (`ε' ← ε/12`) | | [`sketch_interval`](Ttc/Process/Sketch.lean), [`Params.epsPrime_window`](Ttc/Constants/Parameters.lean) | constant **verified** |
| `alg:ttc` line 18 (`δ' ← δ/(4m)`) | the `Vol_ED` failure budget | [`Params.deltaPrime`](Ttc/Model/Prelude.lean), [`Params.vol_failure_eq`, `numlattice_failure_bound_with_vol`](Ttc/Process/Sketch.lean) | **verified** — and the union bound the paper omits is now **proved**: [`measure_volGood_ge`, `TtcProb.volGood_prob_budget`](Ttc/Volume/Bridge.lean); see finding 13 |
| `alg:ttc` line 24 (`Vol_ED(P(cᵢ), ε', δ')`) | Cousins–Vempala Theorem 1.1 (`vol3_journal.tex:144`) | [`VolumeAlgorithm`](Ttc/Volume/Oracle.lean) (the contract), [`VolumeAlgorithm.monteCarlo`](Ttc/Volume/MonteCarlo.lean) (**constructed**, no hypotheses), [`VolumeAlgorithm.of_ball`](Ttc/Volume/Bridge.lean) (rounding bridge, **proved**), [`TtcProb.volED_hi`/`volED_lo`](Ttc/Volume/Bridge.lean) (**proved**, formerly a field) | **no longer assumed**: `VolumeAlgorithm.monteCarlo` inhabits the contract unconditionally, and `Ttc.ttc_volume_monteCarlo` removes all six `Vol_ED` binders from the capstone at a cost of `δ/4`. But that is hit-and-miss Monte Carlo, **exponential in `n`** — it is *not* a proof of CV Theorem 1.1. The CV route ([`Ttc/Volume/CousinsVempala.lean`](Ttc/Volume/CousinsVempala.lean) = §5.2 plus a construction, `Arlib/Convexity/GaussianCooling/` = §5.1) is **still undischarged**: the construction's sampler-side arguments are open and its non-vacuity witness is `VolumeAlgorithm.exact` in disguise |
| `alg:ttc` line 20 (`Thresh`) | | [`err_sum_le_delta`, `noise_bound_le_delta`](Ttc/Process/Sketch.lean) | both branches **verified** |
| `alg:ttc` line 17 (`η ← ε/8`) | | [`Params.eta`](Ttc/Model/Prelude.lean) | definition |
| `κ` (`lem:nonconv`) | `√(2log(8/η)) + √(2log r)` | [`Params.kappa`, `kappa_le`](Ttc/Constants/Parameters.lean) — deliberately *not* in `Model/Prelude`: `κ` is `lem:nonconv`'s constant, appears in no line of `alg:ttc`, and is outside the headline's definitional closure | **proved** `κ ≤ 2√(log(8r/η))` |
| ↳ deflated shell factor | `(1 + κ/(γ−κ))ⁿ ≤ 1 + η/(8m)` | [`kappa_le_gamma_half`, `shell_factor_bound_deflated`](Ttc/Constants/Parameters.lean) | **proved** — the deflated companion of `shell_factor_bound` |
| ↳ dilation of a facet system | `c·{x \| f x ≤ b} = {y \| f y ≤ c·b}` | [`FacetSystem.scale`, `scale_body_zero`](Ttc/Nonconv/Recentred.lean) | **proved** — connects `body_eq_sol` to `lem:lattice`'s dilate |
| `γ` / `κ/γ ≤ η/(32mn)` | the shell bound's input | [`Params.gamma`](Ttc/Model/Prelude.lean), [`kappa_div_gamma_le`, `shell_factor_bound`](Ttc/Constants/Parameters.lean) | **proved** — see finding 2 |
| `alg:ttc` line 16 (`ToDNF`) | circuit AllSAT | [`Ttc.toDNF`](Ttc/Model/Prelude.lean), [`toDNF_isDNFOf`, `toDNF_isPositive`](Ttc/Dnf.lean) | a **correct** converter is exhibited, so the `isDNF`/`isPositive` fields are satisfiable by a real procedure — but they remain fields, because `toDNF` is a parameter of `TtcProb` and the paper's AllSAT returns a different (smaller) DNF |
| `alg:ttc` lines 22–46 (main loop) | the sketch loop itself | [`run`, `step`, `absorbLevel`, `haltLevel`](Ttc/Model/Pseudocode.lean) | modelled over an oracle bundle; both `while` loops as exit levels |
| ↳ the output as a random variable | `run` on `ToDNF(F)`, oracles drawn at `ω` | [`ttcOutput`](Ttc/TtcProb.lean) | definition |
| `thm:volumettc` | `Pr[ output ∈ (1±ε)·Vol(F) ] ≥ 1−δ` | [`TtcProb.volume_estimate`](Ttc/Estimate.lean) | **proved** from the [`TtcProb`](Ttc/TtcProb.lean) fields |
| `alg:prec` (`GetPrecision`) | `ρ ← ⌈log₁₀(γ/γ̂)⌉` ([`Params.precision`](Ttc/Model/Prelude.lean), used via `TtcProb.rho_eq`) | **load-bearing**: [`gamma_le_latticeScale_mul`](Ttc/Lattice/Assembled.lean) is what makes the *dilated* polytopes contain a ball of radius `γ`, which is what the shell bound needs; also [`ball_radius_scales`](Ttc/Lattice/Transport.lean), [`gamma_half_le`, `precision_increase_le_one`](Ttc/Findings/Repair.lean), [`gamma_scale_cost`](Ttc/Nonconv/Recentred.lean) | mathematical content **proved**; LP implementation not modelled |

Results with no counterpart in the paper, produced by the formalisation:

| Lean | What it establishes |
| --- | --- |
| [`convex_region`, `convex_litSet`](Ttc/Lattice/Decomposition.lean) | each cube's region is convex — and *not* closed (finding 5) |
| [`ratio_antitone`, `facet_ratio_fails`](Ttc/Nonconv/Geometry.lean) | `k` is attained at the facet **nearest** the origin, so the ball hypothesis is needed at every facet (finding 2) |
| [`claim12_factor_le`](Ttc/Nonconv/Core.lean) | the `claim:helper` factor is `≤ 5/3` on `0 < η ≤ 1` |
| [`Box.boxProb`, `Box.nonempty_ttcProb`](Ttc/Witness/BoxProb.lean) | the hypothesis bundle is inhabited **non-degenerately**, so `thm:volumettc` is not vacuous; see [`AUDIT.md`](AUDIT.md) §3 |
| [`box_lattice_card_ge`, `normalisedCount_box_ge`](Ttc/Witness/Box.lean) | the witness's normalised lattice count is at least `cⁿ`, at *every* precision — what lets `c` be chosen from `Thresh` |
| [`trajOracles`](Ttc/Coupling/Family.lean) + [`card_run_eq_sum_traj`](Ttc/Coupling/Run.lean) | the coupling finding 15 says `lem:numlattice`'s proof needs and the paper never constructs |
| [`traj_numlattice_le`](Ttc/Coupling/Run.lean) | `lem:numlattice`'s bound for the coupled run, with no probabilistic hypothesis |
| [`numlattice_union_of_model`](Ttc/Coupling/Transfer.lean) | that bound transported to an arbitrary probability space that *is* the family |
| [`exists_epoch`](Ttc/Coupling/Transfer.lean) | the epoch window `[(1−ε')·Thresh/8, Thresh/2]` has ratio ≥ 4, so a power of two always lands in it — `j*` need not be handed to the proof |
| [`TtcProb.thresh_pos`](Ttc/Coupling/Transfer.lean) | `Thresh > 0`, from `alg:ttc` line 20's own formula: `δ ≤ 1` forces `log(24/δ) ≥ log 24 > 0`, and `ε' = ε/12 ∈ (0, 1/12]` keeps `(1−ε')ε'²` positive. The paper leaves it implicit |
| [`TtcProb.vol_lt_two_total`](Ttc/Coupling/Transfer.lean) | a cube's volume estimate is under twice the total rate — what makes the first loop's cut-off derivable, so `rate_small` need not be assumed |
| [`Ttc.escape_of_mem_body`](Ttc/Sampler/Bridge.lean) | KV97 Theorem 2's escape-mass hypothesis, discharged for every lattice point of the dilated body |
| [`Ttc.almostUniform_transport`](Ttc/Sampler/Bridge.lean) | `eq:almostuniform` moves `ℤⁿ → 𝕃ⁿ` at the *same* `ε` — the paper asserts this ("neither side changes"), and here it is proved |
| [`Ttc.VolSolCheck.volSol_tt_eq_zero`](Ttc/Volume/VolSolCheck.lean) + [`TtcProb.ofReal_volSol`](Ttc/Volume/VolSolCheck.lean) | the `ENNReal.toReal ⊤ = 0` hazard, exhibited and then closed (finding 16) |
| [`Arlib.MarkovChains.not_exists_pointwiseClose_of_tvLe`](Arlib/MarkovChains/Continuous/PointwiseMixing.lean) | mixing in total variation **never** implies a pointwise density bound (finding 17) |
| [`Arlib.prekopa_leindler_pi`, `Arlib.brunn_minkowski_pi`](Arlib/Convexity/PrekopaLeindlerN.lean) | Prékopa–Leindler and (multiplicative) Brunn–Minkowski in `ℝⁿ`, which Mathlib v4.32 does not have |
| [`Arlib.brunn_minkowski_sharp`, `Arlib.brunn_slice_concaveOn`](Arlib/Convexity/BrunnSharp.lean) | the **sharp** `1/n`-concave Brunn–Minkowski for arbitrary measurable sets, and Brunn's theorem — with section-nonemptiness genuinely required (the sharp form is false without it) |
| [`Arlib.MarkovChains.cheeger`](Arlib/MarkovChains/Continuous/Cheeger.lean) | **Cheeger's inequality, both directions**, `Φ²/2 ≤ gap ≤ 2Φ`, for a reversible kernel — hard direction included, under `(rayleighSet …).Nonempty` |
| [`Arlib.MarkovChains.mixesWithin_of_conductance`](Arlib/MarkovChains/Continuous/L2Mixing.lean) | conductance ⇒ an explicit TV mixing time, via the `L²` contraction — needs `HasNonnegSpectrum`, which the plain ball walk lacks |
| [`Arlib.MarkovChains.conductance_ballWalk_ge`](Arlib/MarkovChains/Continuous/BallWalkConductance.lean) | a conductance bound for the ball walk from an **inline** isoperimetric hypothesis, at a constant `√n` worse than Cousins–Vempala's |
| [`Arlib.MarkovChains.mixesWithin_lazy_ballWalk`, `theorem2_of_lazy_ballWalk`](Arlib/MarkovChains/Continuous/BallWalkConductance.lean) | isoperimetry ⇒ conductance ⇒ Cheeger ⇒ `L²` decay ⇒ TV mixing ⇒ KV97 Theorem 2's window, composed. **Not a poly-time sampler**: the only proved `θ` is `2⁻ⁿ`, so the certified step count is exponential in `n` |
| [`Arlib.GaussianCooling.zLogconcaveHypothesis_indicator`](Arlib/Convexity/GaussianCooling/ZLogconcave.lean) | Cousins–Vempala's Lemma 5.9 for indicators of convex sets — together with the counterexample showing it is *false* for general log-concave `f` |
| [`Arlib.exists_convex_slice_profile_not_affine`](Arlib/Convexity/LocalizationLimit.lean) | sharp Brunn does **not** pin a localisation limit profile to an affine function — a converse that narrows what still has to be proved for the Localization Lemma |
| [`Ttc.volume_estimate_joint`, `Ttc.volume_estimate_joint_compProd`](Ttc/Coupling/Product.lean) | `TtcProb.volume_estimate` at `1 − δ − δ/4` over the **joint** randomness of run and volume oracle (finding 13a) |
| [`Ttc.CV.prod_relErr_ge`, `Ttc.CV.median_relErr_ge`](Ttc/Volume/CousinsVempala.lean) | Cousins–Vempala §5.2's product estimator and median boost, proved unconditionally |
| [`Arlib.uniformOn_iso_unitBall`, `Arlib.uniformOn_iso_of_convex`](Arlib/Convexity/IsoBall.lean) | an isoperimetric inequality for the uniform measure on **every** bounded convex body, unconditionally, at `κ = 2⁻ⁿ/D` — exponentially worse than the sharp constant, but proved rather than assumed, which is what makes the mixing chain unconditional |
| [`Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope`](Arlib/MarkovChains/Continuous/ConvexBodyMixing.lean) | the whole mixing chain for a polytope with **no** isoperimetric hypothesis and **no** local-conductance floor — target the walk's own stationary measure, so no bias term. Step count still exponential in `n` |
| [`Ttc.VolumeAlgorithm.monteCarlo`, `Ttc.MonteCarlo.est_ne_volume`](Ttc/Volume/MonteCarlo.lean) | the `Vol_ED` contract **inhabited with no hypotheses**, by hit-and-miss Monte Carlo — and shown not to be the exact oracle in disguise. Sample count exponential in `n`; **not** Cousins–Vempala Theorem 1.1 |
| [`Ttc.e2eSampler`](Ttc/Exec/EndToEnd.lean), [`Ttc.kv97SamplerOfBallWalk`](Ttc/Sampler/Construct.lean) | a `KV97Sampler` whose quantitative field `law_tv` is a **theorem** about a lazy ball-walk iterate, not a hypothesis. It is *not* proved that the finite-time iterate differs from `uniformOn` on the inflated body |
| `Ttc.rates`, [`Ttc.theta_eq_rates`, `Ttc.rates_pos`](Ttc/Sampler/Rates.lean) | the level-`0` rates constructed from `sampD` and `vol` via `thm:decomposition`, with the collapsed `θ ≡ 0` ruled out |
| [`Ttc.ttc_volume_endToEnd`](Ttc/Exec/EndToEnd.lean), [`Ttc.Box.exists_two_ttc_volume_endToEnd_instances`](Ttc/Exec/EndToEnd.lean) | `thm:volumettc` over the algorithm's own inputs with **no oracle binder**, at `1 − δ − δ/4`, plus two structurally different instances with bounds `3/8` and `11/16` proved positive |
| [`Ttc.canon_body_eq_smul_region`, `Ttc.ttc_volume_endToEnd_canon`](Ttc/Exec/CanonPolytope.lean) | the canonical linear system read off `atoms` cuts out the dilated region **exactly** — an equality, not the inclusion `hdil` asked for — which is what makes all nine polytope-description binders (and in particular `hDbody`) discharge with no slack |
| [`Ttc.ttc_volume_final`](Ttc/Exec/Final.lean) | **the strongest result**: `thm:volumettc` over `(atoms, φ, ε, δ)` and input conditions alone — no oracle, no polytope description, clean `1 − δ`. The clean budget is a **repricing** at `δ₀ = 4δ/5`, costing `5/4` on the Monte-Carlo sample count and an additive `O(1/ε²)` on `Thresh` |
| [`Ttc.Box.clean_box_at_nine_tenths`, `Ttc.Box.old_budget_vacuous_at_nine_tenths`, `Ttc.Box.exists_two_ttc_volume_clean_instances`](Ttc/Exec/Budget.lean) | non-vacuity **in the regime the old budget could not reach**: at `(ε,δ) = (1/3, 9/10)` the bound is `1/10`, proved `> 0`, where `1 − δ − δ/4 = −1/8` said nothing — the comparison itself is in the library, not only in prose |
| [`Ttc.TwoCube.ttc_volume_final_two_cube`, `ttc_volume_final_two_cube_at`, `card_toDNF_eq_two`, `sol_eq_union_two`, `cenT_left_ne_right`, `min_qT_le_ratesT`, `volume_sbx`](Ttc/Witness/TwoCube.lean) | non-vacuity **for `ttc_volume_final` itself**, on a DNF with **two** cubes — two disjoint boxes, every binder discharged including `big`, at every `(ε,δ) ∈ (0,1]²` and at the numeral pairs `(1/3, 9/10)` and `(1/2, 1/4)` with bounds `1/10` and `3/4` proved `> 0`. It is the only witness for the strongest statement; before it there was none. `card_toDNF_eq_two` is an equality, `sol_eq_union_two` gives two distinct nonempty disjoint regions and `cenT_left_ne_right` two distinct ball centres — none of which the one-cube box exercises. `big` required the new `min(q₁,q₂)` argument (`min_qT_le_ratesT` case-splits on `cubeAt s`), since the box's route needs `N = L`. **Not** proved: `volSol = Vol₁ + Vol₂` |
| [`Ttc.Box.ttc_volume_box_accuracy_is_trivial`](Ttc/Witness/BoxSharp.lean) | that a non-vacuity witness at `ε = δ = 1` certifies **nothing about the conclusion** — the accuracy conjunct there is `0 ≤ (…).toReal`, provable without mentioning the algorithm. Which is why `BoxSharp` re-does the witness at `ε, δ < 1` |
| [`Arlib.dyerFrieze_dim_one`, `Arlib.exists_halfSpace_proportional`, `Arlib.dyerFrieze_step`](Arlib/Convexity/DyerFrieze.lean) | the one-dimensional isoperimetric inequality in full, a proportional halfspace cut in place of Borsuk–Ulam, and the induction step — the inequality itself still unproved and unassumed. **IN FLIGHT**: this file was green and `sorry`-free at the last check but is being extended, so `lake build Arlib.Convexity.DyerFrieze` before relying on it |

`Ttc.lean` re-exports every module under `Ttc/`, so `import Ttc` and a bare
`lake build` expose `Ttc.TtcProb.volume_estimate`, `Ttc.ttc_volume`,
`Ttc.ttc_volume_endToEnd`, `Ttc.ttc_volume_endToEnd_canon`,
`Ttc.ttc_volume_clean` (= `Ttc.ttc_volume_endToEnd_delta`)
and `Ttc.ttc_volume_final` alike. Because the
`Ttc` library has no glob, that re-export is load-bearing: a module dropped from
this list would stop being compiled rather than merely stop being visible.
`Arlib.lean` re-exports the four
area roots, which now do cover every `Arlib/` module (including
`LocalizationLimit` and `DyerFrieze`, which earlier versions of this page said
they did not). If a name is missing, check the relevant area root rather than
assuming it is gone: the lakefile's glob (`["Arlib", "Arlib.+"]`) *builds* every
file whether or not a root imports it, so a green build is not by itself evidence
that `import Arlib` reaches it.

## The two headline theorems

There are two — an abstract one over a hypothesis bundle, and an oracle-free one
over the algorithm's inputs — and conflating them is the easiest way to overstate
this work. (The oracle-free one now exists in four versions, of which
`Ttc.ttc_volume_final` is the strongest; they are laid out below.)

**The abstract one** is over the hypothesis bundle. It concludes a clean `1 − δ`
and it is what all the analysis is proved into:

```lean
theorem Ttc.TtcProb.volume_estimate (T : TtcProb A n) :
    1 - T.δ ≤
      (T.μ {ω | ttcOutput T.P T.O T.toDNF T.ρ T.φ ω
        ∈ relErr T.ε (volSol T.M T.φ)}).toReal
```

`ttcOutput` is `Ttc.run` — the transcription of `alg:ttc` — with the oracles
drawn at `ω`, so the measured quantity is the algorithm's own output.
`volSol M φ = (volume (sol M φ)).toReal` is the **Lebesgue volume of the solution
set of the actual SMT(LRA) formula** — not a surrogate. That the set in question
is exactly the union of the polytopes the algorithm enumerates is
`Ttc.TtcProb.sol_eq_union` (`thm:decomposition`), so the object the algorithm
targets and the object the theorem bounds coincide. What `volSol` *is* — down to
an independently written `Bool`-valued evaluator for the formula semantics — is
checked in [`Ttc/Volume/VolSolCheck.lean`](Ttc/Volume/VolSolCheck.lean).

**Non-vacuity.** `Ttc.TtcProb` is inhabited by
[`Ttc.Box.boxProb`](Ttc/Witness/BoxProb.lean)
([`Ttc.Box.nonempty_ttcProb`](Ttc/Witness/BoxProb.lean)), the box `[0,c]ⁿ`
with `c ≥ Thresh` sampled by the coupled family — so the theorem is not
vacuously quantified, and not by a degenerate instance either; see
[`AUDIT.md`](AUDIT.md) §3. It is also not vacuous in the subtler `toReal ⊤ = 0`
sense: see finding 16.

**The oracle-free one** is
[`Ttc.ttc_volume_final`](Ttc/Exec/Final.lean). It quantifies over no bundle, binds
no oracle and binds no polytope description; it takes `(atoms, φ, ε, δ)`, the
input conditions, `hlen` and `big` — 26 explicit binders — and concludes **both**
halves: accuracy at a clean `1 − δ`, over the joint law of the run and the
constructed volume oracle's coins, and the charged running-time bound. Read its
type; it is long, and that is the point — every residual obligation is visible in
it rather than hidden in a field. Read the module docstring too, for which `δ` is
the user's and which the internal `4δ/5`.

Its three predecessors are the honest intermediate steps, not rival headlines:
[`Ttc.ttc_volume_endToEnd`](Ttc/Exec/EndToEnd.lean) (still binds the polytope
description; `1 − δ − δ/4`),
[`Ttc.ttc_volume_endToEnd_canon`](Ttc/Exec/CanonPolytope.lean) (description gone;
`1 − δ − δ/4`) and [`Ttc.ttc_volume_clean`](Ttc/Exec/Budget.lean) (description
still there; `1 − δ`).

**Non-vacuity for `ttc_volume_final` itself** is
[`Ttc.TwoCube.ttc_volume_final_two_cube`](Ttc/Witness/TwoCube.lean): the theorem
instantiated at every `(ε, δ) ∈ (0,1]²` on a **two-cube** DNF — two disjoint boxes
— with every binder discharged, `big` included, and
`Ttc.TwoCube.ttc_volume_final_two_cube_at` giving `(1/3, 9/10)` and `(1/2, 1/4)`
with bounds `1/10` and `3/4` proved `> 0` in the statement. It is the **only**
witness that applies `ttc_volume_final`; the box witnesses below are about the
intermediates. See the opening section for what arity two exercises and what it
still does not prove (`volSol = Vol₁ + Vol₂` is not proved).

The intermediates are checked the same way, at one cube:
`Ttc.Box.ttc_volume_clean_box_at` puts the clean statement on the box at
every `(ε, δ) ∈ (0,1]²` (by repricing the `ttc_volume_endToEnd` box instance, not
by applying `ttc_volume_clean`), `Ttc.Box.exists_two_ttc_volume_clean_instances` gives
`(1/3, 9/10)` and `(1/2, 1/4)` with strictly positive bounds `1/10` and `3/4`, and
`Ttc.Box.clean_box_prob_pos_ne_top_at_nine_tenths` rules out the
`ENNReal.toReal ⊤ = 0` reading. One rung lower,
`Ttc.Box.ttc_volume_endToEnd_box_at` and
`Ttc.Box.exists_two_ttc_volume_endToEnd_instances` do the same at `(1/2,1/2)` and
`(1/4,1/4)` with bounds `3/8` and `11/16`, `Ttc.Box.bxRates_pos` rules out the
collapsed `θ ≡ 0` that would satisfy `theta_eq` vacuously, and
`Ttc.Box.endToEnd_box_lintegral_pos_ne_top` closes the `toReal ⊤` reading there.
Compare [`Ttc/Witness/BoxSharp.lean`](Ttc/Witness/BoxSharp.lean), which exists
because the *previous* witness sat at `ε = δ = 1`, where the accuracy conjunct
degenerates to `0 ≤ (…).toReal` — true of every measure, and certifying nothing.

**Every witness in the last paragraph is the same single-cube box, and the
`ttc_volume_final` witness above is not.** At the box, `m = 1`, so the union bound
over cubes and `lem:numlattice`'s multi-cube content are exercised there by
nothing; `Ttc.TwoCube` exercises them at `m = 2`, on the strongest statement. See
the opening section.

## What is assumed

This section is about `Ttc.TtcProb`, the **abstract** hypothesis bundle. It is
still the right place to read what the analysis rests on, but it is no longer the
last word on what the *development* assumes: `Ttc.ttc_volume_endToEnd` constructs
every oracle field below, so on that route none of them is an input. Read this to
understand the analysis; read the capstone's type to see what is assumed.

`Ttc.TtcProb` has **59 fields**. They fall into four groups, and it is worth
being blunt about which is which.

1. **Structure, not assumption** — `ε`, `δ` and their range; `atoms`, `M`, `φ`,
   `toDNF`; `Ω`, `mΩ`, `μ`, `isProb`; `P`, `ρ`, `L`; `Lidx`, `ptE`, `θ`, `vol`,
   `sampD`, `cover`, `memPt`, `toTraj`, `O`, `cen`, `gammaHat`, `volCoins`. These
   name the objects the rest of the fields talk about; on their own they assume
   nothing, and each is pinned by an equation elsewhere in the list.
2. **Assumed of the input** — checkable of a formula before `TTC` runs.
3. **Assumed of the external oracles** — this is what is left of the two oracles,
   and it is not nothing.
4. **Proved, and formerly assumed** — listed for the record, because knowing what
   *used* to be a field is how a reader calibrates the rest.

### Proved, and previously assumed

* **`lem:lattice`** — [`TtcProb.lattice_lo`/`lattice_hi`](Ttc/Lattice/Assembled.lean),
  and per polytope [`lattice_cube_lo`/`lattice_cube_hi`](Ttc/Lattice/PerCube.lean).
* **`lem:numlattice` and its epoch covering** —
  [`TtcProb.numlattice`](Ttc/Coupling/NumLattice.lean),
  [`TtcProb.numlattice_union`](Ttc/Coupling/Transfer.lean).
* **`eq:almostuniform` and the paper's Invariant** —
  [`TtcProb.samp_unif`](Ttc/Sampler/Bridge.lean),
  [`theta_lo`/`theta_hi`](Ttc/Sampler/Bridge.lean).
* **`Vol_ED`'s deterministic accuracy** —
  [`TtcProb.volED_hi`/`volED_lo`](Ttc/Volume/Bridge.lean).
* **The epoch index and its window** (five fields) — `Ttc.exists_epoch`,
  `Ttc.rate_small_of_epoch`, `TtcProb.thresh_pos`, `TtcProb.vol_lt_two_total`.
* **`vol_eq`, `cover_all`, `θ_nonneg`, `θ_pos`, `rate_eq_L`** — all former fields,
  all now theorems or consequences:
  [`TtcProb.cover_all`, `theta_nonneg`, `theta_pos`, `sum_theta_lo`,
  `sum_theta_hi`, `Lidx_eq`, `L_eq_Lidx`](Ttc/Coupling/Transfer.lean). `vol` is
  pinned by `volED_eq` (it *is* `Vol_ED`'s output) rather than by an assumed sum
  identity, and `rate_eq_L` is replaced by the *two-sided* window the proved
  Invariant gives, so an instance no longer has to claim the rates are exactly the
  lattice count.

With `lem:lattice` proved, `claim:cl` and `lem:nonconv` are discharged end to end:

* **`claim:cl`, all three parts, for a concrete rounding.** The paper cites `rnd`
  to KV97 without a construction; we supply the standard one — independent
  coordinatewise rounding `xₖ = ⌊pₖ⌋ + Bernoulli(pₖ − ⌊pₖ⌋)`, whose displacement
  density is the tent `1−|u|` — and prove every property the analysis uses.
  Reading it in the `p` variable gives double stochasticity
  (`integral_prod_tent`) and parts **(a)** (`prodKernel_claim_cl_a`) and **(c)**
  (`claim_cl_c`); reading the *same* kernel in the lattice variable gives the law
  of `rnd p` on `ℤⁿ` (`roundLaw`), which is a two-point product
  (`tentInt_eq_two_point`) — hence bounded, mean-zero (`integral_tentInt_disp`)
  and independent (`iIndepFun_latDisp`), so Hoeffding applies on that side too and
  yields **(b)** (`prodKernel_claim_cl_b`). The geometry differs between the two
  directions: in (a) the escaping point crosses a facet outward, in (b) inward, so
  (b) applies the tail bound to `−A_j` (`cover_of_notMem_body_deflated`).
* **`lem:nonconv` over an actual facet system**
  ([`FacetSystem.nonconv_of_ball`](Ttc/Nonconv/Assembled.lean)) — no free reals,
  no abstract kernel. Its one hypothesis is the paper's: each `Pᵢ` contains an
  `ℓ₂`-ball of radius `γ` about its own centre.
* **Finiteness of `Q ∩ ℤⁿ` is not assumed.** It follows from `claim:cl`(a), which
  bounds `|T|` for *every* finite `T ⊆ Q ∩ ℤⁿ`
  ([`finite_of_forall_finset_card_le`](Ttc/Nonconv/BallFacet.lean)).
* **`GetPrecision` became load-bearing.** `ρ = ⌈log₁₀(γ/γ̂)⌉` is exactly what makes
  the dilated polytopes contain a ball of radius `γ`
  ([`gamma_le_latticeScale_mul`](Ttc/Lattice/Assembled.lean)), which is what the
  shell bound stands on.

### Assumed about the input

Fields of [`Ttc.TtcProb`](Ttc/TtcProb.lean), all of them hypotheses
`lem:nonconv` needs and the paper states (or silently uses). None says anything
about the algorithm's behaviour.

| Field | Assumption |
| --- | --- |
| `M_eq` | the atoms really are linear constraints `A x ≤ b` — the formula is in the LRA fragment |
| `isPositive` | no literal of the DNF is negated, so each `P(cᵢ)` is *closed* (finding 5). [`Ttc.toDNF_isPositive`](Ttc/Dnf.lean) derives it from a negation-free input formula |
| `isDNF` | `ToDNF`/AllSAT is correct. [`Ttc.toDNF_isDNFOf`](Ttc/Dnf.lean) exhibits a converter that satisfies it, so the assumption is not vacuous — but the field stays, because `toDNF` is a parameter |
| `ball_subset`, `hgammaHat` | each `P(cᵢ)` contains an `ℓ₂`-ball of radius `γ̂ > 0` about `cen i` — the paper's own hypothesis, with the common-centre gap of finding 2 removed |
| `volume_ne_top` | each `P(cᵢ)` has finite volume — the one hypothesis with no counterpart at all in the paper (finding 10), and also what stops the headline being vacuous (finding 16) |
| `normal_ne_zero` | every facet has a nonzero normal vector — implicit in the paper, and false only for a degenerate "constraint" `0 ≤ b` |
| `cubes_le`, `facets_le` | `m` and `r` really do bound the number of cubes and of facets |
| `eps_eq`, `delta_eq`, `dim_eq` | the parameter block is the one for *this* `ε`, *this* `δ` and *this* dimension |
| `rho_eq` | `ρ` is `GetPrecision`'s output for this `γ̂` |
| `L_eq`, `ptE_mem`, `ptE_onto`, `ptE_inj`, `memPt_eq`, `cover_eq` | `L` and `Lidx` are the actual lattice count, `ptE` enumerates the actual lattice points bijectively, and the coverage tests are the geometric ones — definitions, pinned |

### Assumed about the algorithm's oracles

This is the residue **of `Ttc.TtcProb`**, and it is where an implementer's
obligations live. Every row below except `law_eq`/`oracle_eq` is *constructed*
rather than assumed on the capstone's route — the "How strong" column says which
construction, and [`Exec/EndToEnd`](Ttc/Exec/EndToEnd.lean) is where they are all
supplied at once. `law_eq` and `oracle_eq` do not disappear so much as change
form: the capstone builds a run whose randomness *is* the coupled family, which is
a construction, not evidence that a shipped implementation matches it.

| Field(s) | Oracle | What it says | How strong |
| --- | --- | --- | --- |
| **`law_eq`** | the run's randomness | `μ.map toTraj = trajLaw θ` — the randomness **is** the coupled level family | **the strongest field in the development.** Not "the draws are Poisson"; "the draws are *this construction*" |
| **`oracle_eq`** | the run's randomness | `O ω = trajOracles ptE_inj vol cover memPt (toTraj ω)` — the oracles answer by reading that trajectory | pins `O` completely; also what makes `vol` deterministic (see finding 13a) |
| `toTraj`, `toTraj_meas` | | each `ω` reads as a trajectory `ℕ → Fin Lidx → ℕ`, measurably | structure |
| **`sampler`** (14 subfields) | `GenerateSamples` | the discrete law `sampD` is the rejection-normalised randomized rounding of a continuous draw from the inflated dilate `10^ρ·P(cᵢ)` | a **description**, except for `law_tv`: the continuous law is within total variation `ε'/(4·Vol(P′))` of uniform on the inflated polytope. That one is quantitative — and it is now **constructed and proved**, `Ttc.e2eSampler` with `law_tv` from `mixesWithin_lazy_ballWalk_polytope`. What an implementer owes is the *identification* of the shipped sampler with that lazy ball walk, not an inequality |
| `theta_eq` | `GenerateSamples` | each lattice point's level-`0` rate is the sampler's mass there times the volume estimate of the cube it was drawn from | a description of `alg:ttc` lines 43–46; **constructed** by `Ttc.rates` (`Sampler/Rates`), so it is not a binder of the capstone |
| `gen_mem` | `GenerateSamples` | the points returned really are lattice points of `P(cᵢ)` | `Ttc.Oracles` fixes only *how many*; this fixes *where*. Not distributional; **proved** by `Ttc.gen_mem_of_geometry` from the input conditions |
| **`volAlg`** | `Vol_ED` | it is *a* volume algorithm meeting `VolumeAlgorithm n` | **no longer an assumption.** `Ttc.VolumeAlgorithm.monteCarlo : (n : ℕ) → VolumeAlgorithm n` is a total function with no hypotheses, so the field can always be filled. It is **not** Cousins–Vempala Theorem 1.1 — see below |
| `volCoins`, `volED_eq` | `Vol_ED` | `vol i = γ̂ⁿ · volAlg.est (roundBody …) ε' δ' volCoins` — the run's estimates *are* Theorem 1.1's output on the normalised body | transcription of `alg:ttc` line 24; the `γ̂ⁿ` rescaling is the **proved** `VolumeAlgorithm.of_ball`. In the capstone `volCoins` is **integrated out** against `Ttc.MonteCarlo.coins` and `volED_eq` is the theorem `Ttc.mcVol_eq` |
| **`volCoins_good`** | `Vol_ED` | the `m` calls all landed in their good event | a field here, but its probability is *proved* (`volGood_prob_budget`, `≥ 1 − δ/4`). In the capstone it is **averaged out** rather than assumed — which is exactly what costs the `δ/4`. See finding 13a |
| `vol_pos` | the instance | `0 < vol i` for every cube of the DNF | with the derived `vol_lt_two_total` it is what replaced `rate_small`; **proved** in the capstone as `Ttc.mcVol_pos` |
| **`big`** | the instance | `(1−ε')·Thresh/8 ≤ ∑θ` — the instance is large enough for the sketch to be worth running | a genuine assumption, but the paper's own regime; the box witness arranges it by choosing the side from `Thresh` (`Ttc.Box.epsPrime_thresh_le_volume`, since the box's `∑θ` is `Vol(box)` rather than `L`). At **two** cubes that route fails — it needs `N = L` — and `Ttc.TwoCube.big_two` replaces it with a `min(q₁,q₂)` bound that case-splits on which cube the point came from (`Ttc.TwoCube.min_qT_le_ratesT`) |

**The volume oracle is constructed.** `volAlg` was assumed for the whole of this
project's life. It no longer is:
[`Ttc.VolumeAlgorithm.monteCarlo`](Ttc/Volume/MonteCarlo.lean) is a term of
`Ttc.VolumeAlgorithm n` for every `n`, taking **no hypotheses at all**, and
`#print axioms` on it is `[propext, Classical.choice, Quot.sound]`.

It is plain hit-and-miss Monte Carlo: coins are the countable product
(`Measure.infinitePi`) of the uniform law on the unit ball — `K`-independent, as
they must be, since `Ω` and `μ` are fixed before `K` is seen — rescaled by a radius
`R` manufactured from exactly the three facts `correct` supplies, and `correct`
follows from Chebyshev on i.i.d. Bernoulli`(vol K / vol B(0,R))`.

Two things make it honest rather than a restatement of the placeholder it replaces:

* **`est` is not the true volume.** `Ttc.MonteCarlo.est_ne_volume` exhibits `K, ε,
  p, ω` satisfying *every* hypothesis of `correct` where the estimate differs from
  `(volume K).toReal`. This is the check that the previous witness,
  `cousinsVempalaWitness`, fails: its `est` is `rfl`-equal to the true volume — the
  exact oracle in disguise.
* **`est_meas` holds for every `K`, including non-measurable ones.** Mathlib gives
  convex sets only `NullMeasurableSet`, so a naive count is not measurable. The
  estimator is defined through the measurable hull `toMeasurable volume K`, and
  `Ttc.MonteCarlo.volume_hull_inter_ball` shows the hull intersected back with the
  enclosing ball has *exactly* `volume K` — an identity, not an a.e. argument.

**What this does and does not buy.** `VolumeAlgorithm` carries **no complexity
field** — only `est`, `est_meas`, `correct` — which is precisely why an
exponential-time algorithm satisfies it; the sample count here is `Θ(Rⁿ/ε²p)`.
So this discharges the *existence* of the oracle, not the efficiency claim.
`volCoins_good` is a hypothesis of `Ttc.ttc_volume` about specific coins;
[`Ttc.ttc_volume_monteCarlo`](Ttc/Exec/VolDischarge.lean) removes it by
integrating the coins out against `Ttc.MonteCarlo.coins` and paying `δ/4` for the
event `Ttc.mcGood` (`Ttc.measure_mcGood_ge`), which is where the capstone's
`1 − δ − δ/4` comes from.

Note too that `VolumeAlgorithm.correct` is **strictly stronger** than
Cousins–Vempala Theorem 1.1, which additionally assumes `E_K(‖X‖²) = O(n)`. So a
complete formalisation of Theorem 1.1 would *not* by itself have discharged this
field — one would still owe the rounding/isotropic-position algorithm. Gaussian
cooling remains blocked for an unrelated reason recorded in
[`CV-ROADMAP.md`](CV-ROADMAP.md) §0: its `hphase_mean` is an *equality* of
expectations, which no MCMC sampler can satisfy.

**Almost-uniform sampling, and why two-sidedness matters.** `GenerateSamples` does
not have to return exactly uniform lattice points: `eq:almostuniform` asks only
that `(1−ε')/|P(cᵢ) ∩ 𝕃ⁿ| ≤ D(x) ≤ (1+ε')/|P(cᵢ) ∩ 𝕃ⁿ|` pointwise, and that is now
*proved* rather than assumed. The whole of that lands in one place — the extra
`(1±ε')` factor in `theta_lo`/`theta_hi` — because the model carries a **per-point**
rate `θ s` rather than a single rate, which is exactly what a non-uniform sampler
produces. Three knock-on constants moved with it: `lem:numlattice`'s window is
`(1±ε/2)` (three `(1±ε')` factors and one `(1±η)` no longer fit in `ε/3` — the
first-order term alone is `3/8`), `δ' = δ/(4m)` leaves room for the sampler's own
failure event beside `Vol_ED`'s, and `Thresh`'s second branch carries `15`.

The two-sidedness is **not** decorative. A one-sided `D(x) ≤ (1+ε')/|·|` gives
only `D(A) ≥ |A|/|P ∩ 𝕃ⁿ| − ε'` for a region `A` — an *additive* loss, vacuous
when `A` is the sliver of `P(cᵢ)` no later cube covers, which is precisely the
mass the estimate accumulates. It would leave `theta_lo` unprovable, and with it
the lower half of the headline.

**How honest is the current trade?** It is a real reduction, and it is not zero.

* *Real*: nothing among the sampler fields mentions `ε`, `δ`, accuracy, or a
  failure probability except `law_tv` (and that is about the *continuous* draw,
  one step upstream of the algorithm) — and `law_tv` is itself now proved for the
  constructed sampler. Everything quantitative — the per-epoch `Err` estimate, the
  `Noise` overflow, the epoch series, the `Vol_ED` budget, `eq:almostuniform`, the
  Invariant, the `1 − δ` — is **derived**. Previously the conclusions of the
  paper's two hardest lemmas were inputs.
* *Not zero*: `law_eq` and `oracle_eq` name one specific construction and assert
  the implementation is it. Whether a real `TTC` implementation matches is a
  modelling judgement no machine check can settle, and constructing an instance
  that satisfies them does not settle it either. `big` is a genuine assumption.
  Both constructed oracles are exponential in the dimension. And the sampler's
  quantitative hypothesis has changed shape twice (`samp_unif` → `density_au` →
  `law_tv`) on different objects, so the successive bundles are **incomparable**,
  not nested; see [`END-TO-END-PLAN.md`](END-TO-END-PLAN.md).
* Also note the sampling interface is **level-aware** where the paper's is not
  (`pois` and `gen` receive the cube and level). That deviation is what makes the
  coupling constructible at all; see [`AUDIT.md`](AUDIT.md) §1 and finding 15.

*Proved*, and no longer merely cited:

* **`lem:chernoff` itself** ([`Process/Chernoff`](Ttc/Process/Chernoff.lean)),
  which the paper takes from Soos et al. and Mathlib does not carry. Built from
  the ground up: the Poisson moment generating function
  `E[e^{tN}] = exp(λ(eᵗ−1))` (`Ttc.mgf_poissonMeasure`), the Chernoff bound at
  the optimal `t = log(1+ζ/λ)` giving Bennett's form (`Ttc.poisson_bennett`),
  and the scalar step `h(u) ≥ u²/(2+u)` (`Ttc.bennett_le`) that turns Bennett
  into the paper's `exp(−ζ²/(2λ+ζ))` — plus the lower tail
  (`Ttc.poisson_lower_tail`) and the two-sided form
  (`Ttc.poisson_tail_two_sided`).
* **Both of the paper's uses of it**, with the constants confirmed exact:
  `Pr[N > Thresh] ≤ e^(−Thresh/6)` when the rate is at most `Thresh/2`
  (`Ttc.poisson_overflow`), and `Pr[|N−λ| ≥ ε'λ] ≤ 2e^(−ε'²λ/3)`
  (`Ttc.poisson_relative`).
* Its engine `lem:process` (Poisson splitting, `Ttc.poisson_splitting`); the
  whole epoch union-bound skeleton — the doubly-exponential series
  `∑ 2e^{−a·2ᵗ} ≤ 4e^{−a}` (`Ttc.epoch_series_le`), the `Err` branch
  (`Ttc.err_sum_le_delta`), the `Noise` branch (`Ttc.noise_bound_le_delta`),
  their combination (`Ttc.numlattice_failure_bound`); the interval arithmetic
  behind `ε' = ε/12` (`Ttc.sketch_interval`, `Ttc.sketch_window`,
  `Ttc.Params.epsPrime_window`); and the `Vol_ED` failure budget the paper omits
  (`Ttc.Params.vol_failure_eq`, `Ttc.numlattice_failure_bound_with_vol`; finding 13).
* **Kannan–Vempala's Theorem 2 and the `ε ≤ 5/8` form of `cor:linf`**
  (`Arlib.KV97.theorem2_of_body`, `Arlib.KV97.ratio_bounds_tuned_sharp`), which is
  what makes `eq:almostuniform` a theorem here.

*How the probabilistic model got built.* Every estimate the proof invokes is a
theorem, and they are composed into a statement about `Ttc.run` — first for the
run driven by the *coupled family*, and then, via the sampler fields, for the
arbitrary `Ω`/`μ`/`O` a `Ttc.TtcProb` carries. All four of the original obstacles
are cleared:

1. ~~`Ttc.Oracles` cannot express independence.~~ **Fixed.** Oracle calls are now
   indexed by the level (and the cube), so "the draws at distinct levels are
   independent" is statable, and `Err(j)`/`Nois(j)` are events about that index.
   This also repaired a real distributional defect in the old model — see
   [the `Pseudocode` notes](#what-ttcmodelpseudocodelean-does-and-does-not-do).
2. ~~`lem:process` is only a pmf identity.~~ **Fixed.**
   [`Ttc.countLaw_eq_pi`](Ttc/Process/PoissonLaws.lean) proves it as an identity
   of *measures*, which yields independence of the cell counts
   (`iIndepFun_countLaw`), Poisson thinning (`poisson_thinning`) and
   superposition (`poisson_add`) — exactly the three operations the loop performs
   on the invariant.
3. ~~The number of halvings is a stopping time.~~ **Resolved, and it turned up a
   genuine error** — see finding 14. Conditioning on the rate is not merely hard,
   it is *wrong*; the invariant has to be read non-adaptively. The level-`j`
   process ([`Ttc.levelLaw`](Ttc/Process/SketchProcess.lean)) is that reading, and
   **both branch estimates and the whole `δ` budget are proved over it**:
   `levelLaw_err_le`, `err_branch_sum`, `levelLaw_noise_le`, assembled in
   `numlattice_failure_le` — the paper's `δ/6 + δ/6 + δ/2 ≤ δ`, with the
   algorithm's own `Thresh` and `δ'`.
4. ~~The coupling is missing.~~ **Built.** On the event that the run stops at
   level `J`, the run's final `𝒳` must *be* the level-`J` process. It now is,
   pathwise: [`Ttc.trajOracles`](Ttc/Coupling/Family.lean) is an `Ttc.Oracles`
   bundle that answers every call by reading a trajectory `ω` of the family, and
   [`Ttc.card_run_eq_sum_traj`](Ttc/Coupling/Run.lean) proves `|𝒳| = ∑ₛ ω(J)ₛ` on
   every nested trajectory — [`run_eq_traj`](Ttc/Coupling/Run.lean) turns that
   into `|𝒳|/p = 2^J·∑ₛ ω(J)ₛ`, the output itself. See finding 15 for the details;
   the structural half that made it possible was the two missing contracts, both
   added: `Ttc.Oracles.thin_le` (thinning returns a *sub*-multiset, not merely a
   smaller one) and `TtcProb.gen_mem`. Together they give
   [`TtcProb.run_state_mem`](Ttc/Lattice/Assembled.lean): the run's `𝒳` never
   leaves `Sol(F) ∩ 𝕃ⁿ`, so it *is* a count vector over a fixed finite set.

   The **two operations on the invariant** are proved, in the exact form the
   induction consumes:
   * *thinning* (line 33/40's `halve`) —
     [`pi_poisson_bind_binomial_half`](Ttc/Process/Thinning.lean): a product of
     `Pois(θᵢ)` binomially thinned coordinatewise is a product of `Pois(θᵢ/2)`.
     In **kernel** form (`Measure.bind`), not as a marginal, since that is what a
     loop step actually does. Needs Tonelli for a finite product of series in
     `ℝ≥0∞`, which Mathlib lacks — `tsum_pi_prod`;
   * *block replacement* (`dropCovered` then `GenerateSamples`) —
     [`pi_poisson_replace`](Ttc/Process/Thinning.lean).

   And a simplification worth recording: because `dropCovered` deletes **every**
   point of `P(cᵢ)` before `gen` re-adds them, each point's count comes from
   exactly one insertion — *the last cube containing it*. The invariant therefore
   never needs Poisson **superposition**, only these two operations.

   The **past-measurability layer** is not needed at all, and this is a
   consequence of the level indexing. Every randomised call reads the level it is
   made at, and the level only ever increases
   ([`le_step_level`](Ttc/Invariants.lean)), so the run's state is a read-off of
   one level-indexed family rather than a history of draws. The independence the
   argument uses is the independence *across levels* built into
   `Ttc.trajLaw`, not an ordering fact about a draw
   counter. (An earlier version carried a `clock` field and a window-congruence
   layer for exactly this purpose; both are gone.)

5. **And the bound itself is proved for the coupled run.**
   [`Ttc.traj_numlattice_le`](Ttc/Coupling/Run.lean) bounds
   ```
   Pr[ ¬( (1−ε/2)·L ≤ run P (trajOracles …) ρ l ≤ (1+ε/2)·L ) ]
   ```
   by `∑_{t<j*} 2exp(−ε'²·λ*·2ᵗ/3) + exp(−Thresh/6)` — the paper's expression,
   and in fact **smaller than the paper's**: the covering statement carries an
   extra `+ δ/2` and a factor `m` on the overflow term that the proof does not
   need. Its hypotheses are `hlo`/`hhi` (the window relating `∑θ` to `L`),
   `hsmall` and `hrate` (conditions on `Thresh` and `vol`), and `hall`/`hcov` (the
   cubes cover every lattice point, and the oracle's coverage test agrees with
   cube membership). **No probability claim is assumed.** The pieces are
   `traj_failure_le` (the epoch union bound), `trajLaw_err_le` and
   `trajLaw_noise_le` (the level estimates transported to the trajectory space
   along `map_trajLaw_eval`), `level_cap_subset` (reaching `j*` forces an
   overflow), and `trajLaw_ae_nested` (nestedness, the one hypothesis every
   pathwise result carries, holds almost surely).

6. **And the field is gone.** `traj_numlattice_le` is about the trajectory model —
   `trajLaw θ` on `ℕ → (Fin L → ℕ)`, with the oracles `trajOracles` — whereas
   `Ttc.TtcProb` carries an arbitrary `Ω`, `μ` and `O`. The sampler fields close
   that gap, and [`Ttc.numlattice_union_of_model`](Ttc/Coupling/Transfer.lean) is
   the transport: the failure event is the `toTraj`-preimage of the
   trajectory-space one (by `oracle_eq`), `Measure.le_map_apply` bounds its
   measure by the pushforward, and `law_eq` identifies that pushforward as
   `trajLaw θ`. (No measurability of the failure event is needed — the inequality
   only runs one way.)

**No termination hypothesis is needed for the accuracy theorem.** Both `while`
loops are modelled as exit levels, so one might expect the result to need to know
that the second loop actually exits; it does not. The coupling makes the output a
function of whatever level the run reached, and the `hsmall` hypothesis — no
cube's rate still triggers the first loop at level `j*−1` — does the work the
paper leaves to termination. That hypothesis used to be the `rate_small` field; it
is now *derived*, from `vol_pos` and `TtcProb.vol_lt_two_total` via
`Ttc.rate_small_of_epoch`. The paper addresses none of this. (`Ttc.TtcProb.runtime`
*does* need termination, as `Ttc.Terminates`, and says so.)

**These proofs confirm the algorithm's constants.** `ε' ← ε/12` (`alg:ttc` line
18) is exactly what makes the two-sided `(1±ε')` losses fit inside `(1±ε/2)`; each
branch of `Thresh` (line 20) is exactly what makes its failure branch `δ/6`
(total `δ/3`, so there is slack); `γ` is exactly what makes `κ/γ ≤ η/(32mn)` —
with no slack at all, which is why `γ` and `κ` must use the same logarithm
argument (`Ttc.Params.kappa_div_gamma_le`, `Ttc.Params.shell_factor_bound`); and
`ρ ← ⌈log₁₀(γ/γ̂)⌉` is exactly what lifts the input's inscribed radius `γ̂` to the
`γ` the shell bound needs, after dilating to `ℤⁿ`
(`Ttc.gamma_le_latticeScale_mul`).

## Scope, stated precisely

* **This is an accuracy guarantee. The runtime half is *the paper's own
  accounting*, not an FPRAS claim.** [`Ttc.TtcProb.runtime`](Ttc/Estimate.lean)
  proves `runCost ≤ numCubes · (cVol + cSample · Thresh)` — one iteration per cube
  of the DNF, one `Vol_ED` call and at most `Thresh` samples each — and
  instantiating `cVol`, `cSample` at
  the paper's `O(n⁴)`, `O(n³)` gives `thm:runtime` verbatim. Two things it does
  *not* do, both also true of the paper:
  * the two `while` loops' thinning and Poisson work is **not charged**; the paper
    calls it dominated, and "dominated" is not a theorem here or there, because
    the number of those calls is exactly the quantity with no deterministic bound;
  * it assumes the loops exit (`Ttc.Terminates`), which is not provable
    **pointwise** — the real loop exits only with high probability. It *is* provable
    almost surely, and that is what the statement-layer headline
    `Ttc.ttc_volume_estimate` now uses: `Ttc.ae_ttcLaw_ttcTerminates` discharges the
    guard, so that theorem's cost conjunct carries **no termination hypothesis** at
    all. The price is a factor of at most 2 on the threshold term (a sum where the
    guarded bound has a `max`); the sharper guarded forms are kept alongside and are
    incomparable with it.

  `thm:decompose` (the exponential cost of the decomposition itself) is **not**
  formalised at all. The capstone's second conjunct is *the same* charged cost —
  removing the oracles changed nothing about running time, and both constructed
  oracles (`VolumeAlgorithm.monteCarlo`, the lazy ball walk) are **exponential in
  the dimension**. "Unconditional" and "efficient" are independent claims and only
  the first is established.
* **The `δ` is derived, end to end.** `Ttc.TtcProb.volume_estimate` really does
  conclude `Pr[ output ∈ (1±ε)·Vol(F) ] ≥ 1 − δ`: `Ttc.TtcProb.numlattice` gives
  `Pr[ output ∈ (1±ε/2)·L ] ≥ 1 − δ` — *proved* — and the deterministic chain
  shows the first event *contains* the second, so measure monotonicity carries the
  bound. **What the chain rests on is the oracle descriptions**, not a probability
  bound: if the implemented sampler is not `Ttc.trajOracles` reading
  `Ttc.trajLaw`, the theorem says nothing about it. The capstone concludes
  `1 − δ − δ/4` instead, because the volume oracle's coins are integrated out
  rather than conditioned on; `Ttc.ttc_volume_clean` and `Ttc.ttc_volume_final`
  recover `1 − δ` by running at the internal `δ₀ = 4δ/5`, at strictly more work —
  `5/4` on the Monte-Carlo sample count, an additive `O(1/ε²)` on `Thresh`.
* **`GetPrecision` is not verified as an algorithm.** Its *mathematical
  content* — that dilation scales inscribed-ball radii (`Ttc.ball_radius_scales`)
  and volumes (`Ttc.volume_smul_body`), and that the resulting `γ` satisfies
  `claim:helper` (`Ttc.claim_helper`) — is proved; the LP-based implementation is
  not modelled.
* **`Arlib/Convexity/GaussianCooling/` is not a proof of `Vol_ED`.** It ports
  Cousins–Vempala §5.1 (the variance analysis), which is one section of the proof
  of Theorem 1.1. It carried two of its own explicit hypotheses; one of them,
  `ZLogconcaveHypothesis`, is now **discharged** for a convex body
  (`Arlib/Convexity/GaussianCooling/ZLogconcave.lean`) — but it is **false for
  general log-concave `f`**, so it must not be read as a general fact; and
  `LocalizationHypothesis` (the Lovász–Simonovits Localization Lemma) is still
  assumed — as a `Prop` argument of the theorems that need it, never as an
  `axiom`. Nothing there discharges `volAlg`.
* **The *Cousins–Vempala* volume oracle is not constructible today, and this is
  not a matter of wiring.**
  [`Ttc/Volume/CousinsVempala.lean`](Ttc/Volume/CousinsVempala.lean)
  proves §5.2 unconditionally and *constructs* a `Ttc.VolumeAlgorithm`
  (`VolumeAlgorithm.cousinsVempala`), but four of the construction's arguments —
  chiefly `hphase_mean` — can only come from a sampler. Its hypothesis bundle *is*
  now witnessed (`cousinsVempalaWitness`), but the witness is
  `VolumeAlgorithm.exact` in disguise — it shows the hypotheses are consistent,
  not that the paper's schedule meets them. What *does* fill the `volAlg` field is
  the unrelated `VolumeAlgorithm.monteCarlo`, at an exponential sample count. See
  [the caveats above](#what-the-convexity-and-markov-chain-stack-now-establishes).
* **The ball-walk mixing stack now does produce a sampler — an exponential-time
  one.** `Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope` is
  **unconditional** in the two places this used to break: it assumes no
  isoperimetric inequality (supplied internally by `Arlib.uniformOn_iso_of_convex`,
  proved at `κ = 2⁻ⁿ/D` for every bounded convex body) and no local-conductance
  floor (supplied by `le_ell_of_convex_of_ball_subset`). Its target is the walk's
  own stationary measure, so there is no bias term. That is what
  [`Ttc/Sampler/Construct.lean`](Ttc/Sampler/Construct.lean) turns into a
  `KV97Sampler` with `law_tv` proved. **It is not a polynomial-time sampler**: the
  proved isoperimetric constant is exponentially small in `n`, so the certified
  step count is exponential in `n`. A polynomial constant needs the localization
  route, which is still open, or the speedy walk, whose stationary bias does not
  decay (finding 19). Each link also carries a caveat that changes what it is
  worth (`(rayleighSet …).Nonempty`; `HasNonnegSpectrum`, which the *plain* ball
  walk lacks, hence the laziness; a `√n` loss against Cousins–Vempala's constant);
  they are set out in
  [What the convexity and Markov-chain stack now establishes](#what-the-convexity-and-markov-chain-stack-now-establishes).
* **It is not proved that the sampler's finite-time iterate differs from the
  uniform law.** The constructed `contLaw` is a lazy ball-walk iterate from a warm
  start, and what is proved of it is a total-variation bound. Whether it is
  *strictly* different from `Arlib.uniformOn volume P′` at finite time would need
  an `L²`/aperiodicity argument that is not in the development. This does not
  weaken `law_tv`; it means the non-degeneracy of the sampler is not certified.

## Findings: the formalisation as a referee

Formalising forced hypotheses the paper does not state. Line references are to
the **current** working tree; statuses reflect edits already applied to
`sections/analysis.tex`. Findings about *Kannan–Vempala* rather than about this
paper are collected in [`AUDIT-KV97.md`](AUDIT-KV97.md) §4 and summarised
[above](#what-the-kv97-development-establishes); findings 16–18 below are the ones
that changed what this development can claim.

### 1. Genuine error — `lem:nonconv`'s upper bound. *Partially fixed; residual gap.*

**Originally:** the chain ended `… ≤ |Q∩ℤⁿ|/vol Q`, justified by "the last
inequality follows from `Q ⊆ Q''`". But `Q''` is the family **deflated** by
`κ‖A_ij‖` (`analysis.tex:140`), so `Q'' ⊆ Q` — the opposite containment.

**Now:** the chain correctly ends `= |Q∩ℤⁿ|/vol Q''` and the false justification
is gone. What remains is the final step at **`analysis.tex:222`**:

> "And using `vol Q ≤ vol Q' ≤ kⁿ vol Q'' ≤ ((1+η/4)/(1−η/4))·vol Q''` gives
> `vol Q ≤ (1+η)|Q∩ℤⁿ|`."

This still does not follow. Combined with `vol Q'' ≤ |Q∩ℤⁿ|/(1−η/2)` it needs

`(1+η/4) / ((1−η/4)(1−η/2)) ≤ 1+η`,

and `(1+η/4) − (1+η)(1−η/4)(1−η/2) = η²(5−η)/8 > 0` for every `η ∈ (0,1]` — so
the inequality fails throughout the range. At `η = 1` the chain gives `3.33·N`,
not `2·N`.

**The fix** (proved, `Ttc/Findings/Repair.lean`): run the construction with internal
parameter `θ = η/2`. Then the stated conclusion holds verbatim:

```lean
theorem Ttc.nonconv_repaired (hη : 0 < η) (hη1 : η ≤ 1) (hN : 0 ≤ N)
    (hA  : (1 - η/4) * N      ≤ volQ')                -- claim:cl(a)   at η/2
    (hBC : (1 - η/4) * volQ'' ≤ N)                    -- claim:cl(b,c) at η/2
    (hK  : volQ' ≤ ((1 + η/8) / (1 - η/8)) * volQ'')  -- claim:helper  at η/2
    (hsub : volQ'' ≤ volQ) (hsup : volQ ≤ volQ') :
    (1 - η) * N ≤ volQ ∧ volQ ≤ (1 + η) * N
```

Enabling inequalities: `1 + η/8 ≤ (1+η)(1−η/8)(1−η/4)` (`repair_upper_arith`)
and `(1−η)(1+η/8) ≤ (1−η/8)(1−η/4)` (`repair_lower_arith`).

**Cost: ≤ one decimal digit.** `γ` goes from `(16n/η)√(log(4r/η))` to
`(32n/η)√(log(8r/η))`, and `γ(η/2) ≤ 3γ(η)` (`gamma_half_le`); since
`log₁₀ 3 < 1`, `ρ` rises by at most one (`precision_increase_le_one`).

**Still to change:** `sections/algo.tex:86` (`γ ← (16n/η)√(log(4r/η))` →
`γ ← (32n/η)√(log(8r/η))`) and the hypothesis at `analysis.tex:122`.

### 2. Genuine gap — the inscribed ball must be about a *common* centre. *Solved.*

`sections/analysis.tex:212`: from "each `P_i` contains an `ℓ₂`-ball of radius at
least `γ`" the paper concludes `b_ij ≥ γ‖A_ij‖`. That needs the ball centred at
the **origin** — a ball at `c` only gives `b_ij − A_ij c ≥ γ‖A_ij‖` — and since
`p ↦ p/k` is a homothety about the origin, a *union* needs one common centre for
all `P_i`. That is strictly stronger than the stated hypothesis and is
unsatisfiable when the DNF cubes' polytopes are disjoint.

Two sub-slips in the same sentence: "for the pair `i,j` at which `k` is attained"
— the bound is needed at **every** facet, and in fact `k` is attained at the facet
*nearest* the origin, since `t ↦ (t+κ)/(t−κ)` is decreasing (`ratio_antitone`);
a single facet with `b < γw` breaks the step (`facet_ratio_fails`). And
"`A_ij p ≤ b'_ij` for all `i,j`" — `p ∈ Q'` only gives membership in *some* `P'_i`.

**Resolution** (proved, `Ttc/Nonconv/Recentred.lean`) — the assumption is *removed*, not
assumed away:

1. Use `AffineMap.homothety cᵢ k` about each polytope's **own** centre
   (`piece_inflated_subset_homothety`, `volume_piece_inflated_le`). No relation
   between the `cᵢ` is needed.
2. Compare *shells*, not bodies: `Q' ⊆ Q ∪ ⋃ᵢ (P'ᵢ \ Pᵢ)`
   (`body_subset_union_shells`), giving `vol Q' ≤ (1 + m(kⁿ−1))·vol Q`
   (`shell_bound`).

Cost: the internal parameter must be `θ ∼ η/m`, so `γ` grows by `O(m²)`
(`gamma_scale_cost`) and `ρ` by `O(log m)` digits — benign, since `ρ` enters only
as a coordinate bit-length. *Caveat:* the `m` is not shown to be necessary; the
shell union bound is visibly loose when the `Pᵢ` nest.

### 3. Genuine error — a missing square in `claim:cl`'s Azuma exponent

`sections/analysis.tex:177` (now an active proof, no longer commented) displays

> `Pr(A_ij Y ≥ κ) ≤ 2 exp(−κ²‖A_ij‖ / (2 ∑_{k'} |A_ijk'|²))`.

Since `∑_{k'} |A_ijk'|² = ‖A_ij‖²`, the exponent as written is `−κ²/(2‖A_ij‖)`,
which is not scale-invariant — rescaling a facet's `(A_ij, b_ij)` changes it
though the event does not — and does not yield the claimed `η/(2r)`. The
numerator needs `‖A_ij‖²`.

With the square restored, Hoeffding gives exactly the right thing for the event
`A_ij·Y ≥ κ‖A_ij‖`:

```lean
theorem Ttc.rounding_tail_bound … :
    μ.real {ω | κ * coeffNorm A ≤ ∑ k, A k * Y k ω} ≤ Real.exp (-κ ^ 2 / 2)
```

At the paper's `κ = √(2 log(4/η)) + √(2 log r)` this is `≤ η/(4r)`
(`rounding_tail_bound_kappa`), so the union bound over `r` facets gives `η/4` —
inside the `η/2` needed. **The claim is true as used; only the exponent is wrong.**

Two further slips in the same line: the event is `A_ij Y ≥ κ‖A_ij‖` but the
display writes `Pr(A_ij Y ≥ κ)`; and `|Z_k − Z_{k−1}| ≤ A_ijk` should be
`≤ |A_ijk|`. The leading factor `2` is also unnecessary (the event is one-sided)
— that is where the slack between `η/4` and `η/2` comes from.

*(The earlier mismatch between `Y ∈ [−1,1]ⁿ` and a side-1 cube `C(x)` is now
fixed — `analysis.tex:171` says side length 2.)*

### 4. Boundary imprecision — `claim:helper` is false at `n = 0`

Statement at `sections/analysis.tex:216` ("For `n ∈ ℕ`"); the proof at
`sections/proof-appendix.tex:139` displays `((n + η/8)/(n − η/8))ⁿ`, whose base is
**negative** at `n = 0`, and `proof-appendix.tex:143` ("since `η < n` …") silently
assumes `n ≥ 1`. Harmless — `n` is the ambient dimension — but unstated. Carried
explicitly as `1 ≤ n` in `Ttc.claim_helper`.

### 5. Fine, implicit — negative literals give *open* half-spaces

`sections/algo.tex:51` says a cube's conjunction "defines a (possibly empty)
convex polytope". A negated atom `¬(A_ij x ≤ b_ij)` denotes the **open**
half-space `{x | b_ij < A_ij x}`. The region is convex (`Ttc.convex_region`,
proved) but in general **not closed**, hence not a polytope in the standard
`Ax ≤ b` sense that `lem:integerlattice` (KV97, Theorem 3) is stated for.

For the **volume** side this is harmless — the boundary is Lebesgue-null, so
`vol P(c)` is unaffected. But `lem:nonconv` and `lem:lattice` also count **lattice
points**, and the boundary is exactly where a set and its closure differ for
counting: in one dimension, `¬(x ≤ 0)` denotes `{x | 0 < x}`, whose closure gains
the lattice point `0`, and on the fine lattice `𝕃ⁿ = 10^(−ρ)·ℤⁿ` a facet
hyperplane can carry many such points. Since `L` is *defined* as
`|Q ∩ 𝕃ⁿ|/10^(ρn)`, "volumes agree so nothing breaks" covers only half the claim.

This is why [`Ttc.facetSystem`](Ttc/Nonconv/FacetOfDNF.lean) is built only for
DNFs whose literals are all positive (`Ttc.DNF.IsPositive`,
[`Model/Prelude`](Ttc/Model/Prelude.lean)): a `Ttc.FacetSystem.piece` is an
intersection of closed half-spaces, so no facet system can denote a region with a
negated atom.

### 6. Fine, implicit — `thm:decomposition`'s soundness argument is misphrased

`sections/analysis.tex:71`: "By construction, we have `ℓ_ij ⊨ F_dnf`. Therefore,
by the property of Boolean abstraction, if `⋀ M(ℓ_ij)` can be satisfied, then `F`
is satisfied." An individual literal does not entail the DNF, and the direction
needed is that the *cube* entails the formula. The correct sufficient hypothesis
is that DNF and formula agree on every Boolean assignment (`Ttc.IsDNFOf`) — what a
correct AllSAT/`ToDNF` delivers. Under it both inclusions are one line
(`region_subset_sol`, `sol_subset_iUnion_region`).

### 7. Fine, implicit — two side conditions are unnecessary

`Ttc.lower_combine` (`(1−ε/2)/(1+ε/8) ≥ 1−ε`) and `Ttc.nonconv_lower_arith`
(`((1−η/4)/(1+η/4))(1−η/2) ≥ 1−η`) hold for **all** positive `ε`, `η`; the
paper's `≤ 1` side conditions are not needed.

### 8. Presentational — `lem:process`'s first display conflates `ζ` and `ζᵢ`

`sections/proof-appendix.tex:99` derives the single-coordinate case treating `ζ`
as one scalar shared by all elements, then reintroduces per-element `ζᵢ` at
`proof-appendix.tex:112`. Only the second computation is needed.
`Ttc.poisson_splitting` proves the general statement (arbitrary probability
vector `q`), strictly stronger than either display; neither `η`-closeness nor
`α|S| ≤ sz ≤ β|S|` is needed for the *identity* — they only place the resulting
rate in the required interval (`Ttc.rate_mem_interval`).

### 9. Editorial — duplicated sentence

`sections/analysis.tex:222` contains the sentence "Using Claim …, we can upper
bound `vol Q'` … we have `vol Q ≥ (1−η)|Q ∩ ℤⁿ|`." **twice**, verbatim, before the
final clause. Introduced by a recent edit.

### 10. Genuine gap — `lem:nonconv` needs each `Pᵢ` to have finite volume

Nowhere does the paper require the polytopes to be bounded, and `lem:nonconv` is
**false** without something in that direction: a half-space contains an inscribed
ball of every radius, has infinite volume, and contains infinitely many lattice
points, so `vol Q ∈ [(1−η)|Q∩ℤⁿ|, (1+η)|Q∩ℤⁿ|]` degenerates to `∞ ∈ [∞, ∞]` at
best and, with Lean's `Set.ncard`-of-an-infinite-set convention, to `∞ ≤ 0` at
worst. Both summation steps also divide by `vol Q'` and `vol Q''`, which must
therefore be finite and nonzero.

Carried explicitly as `volume_ne_top`. It is the one hypothesis here with no
counterpart at all in the paper. (Positivity is *not* assumed: it follows from the
inscribed ball, via
[`FacetSystem.volume_piece_pos`](Ttc/Nonconv/Assembled.lean).) It is also what
closes finding 16.

### 11. Fine, implicit — a facet needs a nonzero normal, and finiteness of `Q ∩ ℤⁿ` needs an argument

Two more things the proof uses without saying so.

* **`A_ij ≠ 0`.** The Azuma/Hoeffding step divides by `‖A_ij‖`, and the crossing
  event `A_ij·Y ≥ κ‖A_ij‖` is *certain* when `A_ij = 0`, so the tail bound is
  false for a degenerate "constraint" `0 ≤ b`. Carried as `normal_ne_zero`.
* **`|Q ∩ ℤⁿ|` is a finite number.** The paper writes it throughout without
  remark. It is *not* assumed here: `claim:cl`(a) bounds `|T|` for every finite
  `T ⊆ Q ∩ ℤⁿ` by `vol Q'/(1−θ/2)`, and a set all of whose finite subsets have
  bounded cardinality is finite
  ([`finite_of_forall_finset_card_le`](Ttc/Nonconv/BallFacet.lean)). So the
  gap is real but self-closing.

### 12. Fine, implicit — the deflated shell loses twice what the inflated one does

The shell argument is run once and applied in both directions, as if the inflated
and deflated bodies cost the same factor. They do not: the deflated side compares
against a ball of radius `γ − κ`, not `γ`, so its factor is `(1 + κ/(γ−κ))ⁿ`
rather than `(1 + κ/γ)ⁿ` — a factor `2` worse once `κ ≤ γ/2`
([`Ttc.Params.shell_factor_bound`](Ttc/Constants/Parameters.lean) gives
`1 + η/(16m)`, [`shell_factor_bound_deflated`](Ttc/Constants/Parameters.lean)
only `1 + η/(8m)`).

Harmless — the two-sided bound still closes with the two losses kept apart
([`nonconv_recentred_general`](Ttc/Nonconv/Assembled.lean): the lower bound
consumes only the inflated loss and the upper bound only the deflated one) — but
a proof that equalises them silently is off by a factor of two.

### 14. Genuine error — the sketch invariant is false if read as conditioning

`sections/analysis.tex:262` states the invariant as

> "For any `i ∈ [m]` and `j ≥ 0` the multiset `𝒳⁽ⁱ⁾ⱼ` contains `k` copies of each
> lattice point inside `S⁽ⁱ⁾`, where `k` is drawn from `Pois(p̃ⱼ)`"

with `𝒳⁽ⁱ⁾ⱼ` defined at `analysis.tex:259` as "the state of `𝒳` after consuming
`Pⁱ` **when the value of `p` is `1/2ʲ`**". Read literally — conditioning on the
rate being `2^(−j)` — this is **false**. Halting is a stopping time, and
conditioning on it distorts the law.

**Counterexample.** Two lattice points, rule "while `|𝒳| > 1`, halve", starting
from both present. Conditioned on stopping at `p = ½` (i.e. one halving
sufficed), the state is `Bernoulli(½)²` conditioned on `|𝒳| ≤ 1`: it puts mass
`0` on both points surviving, where the claimed product law puts `¼`. The same
happens for Poisson counts.

**The proof still works, but only under the other reading.** What the union bound
actually uses is `Pr[Nois(j) ∧ Err(j)] ≤ Pr[Err(j)]` — the conditioning is
*discarded*, so `Err(j)` only ever needs to be an unconditional event about the
**non-adaptive** level-`j` process, in which every lattice point independently
carries `Pois(θ/2ʲ)` copies whether or not the run stops there. That is how it is
formalised here ([`Ttc.levelLaw`](Ttc/Process/SketchProcess.lean)), and both
branch estimates are proved over it (`levelLaw_err_le`, `levelLaw_noise_le`).

So the defect is in the *statement* of the invariant, not in the result — but a
reader who takes the invariant at face value is proving something false.

### 15. Genuine gap — `Err(j)` is not a well-defined event. *Repaired here: the coupling is now constructed.*

This is the sharper form of finding 14. It is a defect in the paper, and the
repair is a construction rather than a rewording — that construction now exists
in this development.

`analysis.tex:277` defines the two events

> `Nois(j)`: after consuming the last polytope `Pᵐ`, the value of `p` is `1/2ʲ`;
> `Err(j)`: at the end of the algorithm `𝒳⁽ᵐ⁾ⱼ ∉ [(1−ε')p̃ⱼ|Q∩𝕃ⁿ|, (1+ε')p̃ⱼ|Q∩𝕃ⁿ|]`

and then bounds `∑_{j<j*} Pr[Err(j)] + Pr[⋃_{j≥j*} Nois(j)]`. For that sum to
mean anything, **`Err(j)` must be an event for every `j`** — but `𝒳⁽ᵐ⁾ⱼ` is
defined as the state "when `p` is `1/2ʲ`", and the run has exactly *one* final
rate. On any given execution `𝒳⁽ᵐ⁾ⱼ` exists for one `j` only; for the others the
event has no referent. Reading it instead as *conditioned* on `Nois(j)` is
finding 14, and false.

**What is needed, and what the paper never constructs**, is a family `𝒳ⱼ` defined
*simultaneously for all `j`* on one probability space, such that

* each `𝒳ⱼ` has the level-`j` law (`Ttc.levelLaw`), and
* the run's final state equals `𝒳_J` where `J` is its actual stopping level.

**Both halves are now proved.** The family is
[`Ttc.famCount`](Ttc/Coupling/Family.lean): a level-`0` count `A s` per lattice
point, plus a fair coin per (point, *rank*, level), thinned recursively. Indexing
the coins by rank among the current survivors rather than by original copy is what
makes the recursion implementable from a count alone — which is all the `halve`
oracle gets to see. Its law is `Ttc.trajLaw`, a
measure on whole trajectories `ℕ → (Fin L → ℕ)` built by iterating `thinKernel`,
and its marginals are right:

* `Ttc.map_trajLaw_eval` — coordinate `j` of a trajectory carries exactly
  `Ttc.levelLaw θ j`, so *every* branch estimate already proved for a single level
  transports to an event of one measure (`trajLaw_err_le`, `trajLaw_noise_le`).
  Underneath is [`chainLaw_eq_levelLaw`](Ttc/Process/SketchProcess.lean): nested
  thinning from level `0` reproduces `levelLaw θ j` at every `j`.
* `Ttc.trajLaw_ae_nested` — thinning only removes copies, so `ω(j+1)ₛ ≤ ω(j)ₛ`
  almost surely. Every pathwise result below is stated for nested trajectories;
  this is where that hypothesis is discharged.

The second half — the *coupling to the run* — is
[`Ttc.trajOracles`](Ttc/Coupling/Family.lean): an honest `Ttc.Oracles` bundle,
satisfying both of the interface's contracts, whose `thin` returns the family's
next level, whose `pois` returns the family's total over the cube, and whose `gen`
returns the family restricted to the cube. (`gen` must return exactly `N` points
for *every* `N`, so it has a never-taken filler branch — the run only ever passes
it the `N` that `pois` produced — which is what discharges `gen_card`
unconditionally; see `Ttc.padPoint`.) Driving the real `Ttc.run` off that bundle,

* [`Ttc.CoupledAt`](Ttc/Coupling/Run.lean) — the state holds the family's counts
  at the current level, at the points seen so far and nowhere else — is preserved
  by every operation of the loop (`coupledAt_thin`, `coupledAt_dropCovered`,
  `coupledAt_step`, `coupledAt_foldl`) — one lemma per operation, with no
  induction over loop iterations, because both loops are a single jump to their
  exit level;
* so [`Ttc.card_run_eq_sum_traj`](Ttc/Coupling/Run.lean) gives `|𝒳| = ∑ₛ ω(J)ₛ`
  **pathwise**, at the run's own stopping level `J`, on every nested trajectory,
  and `run_eq_traj` gives the output itself as `2^J · ∑ₛ ω(J)ₛ`.

That is equality of *random variables*, not of laws — which is the point:
`lem:process` supplies only equality in law, and the union bound needs the run
and the level process to agree on each path. The halving triggers close the other
branch: every level the run crosses had either a cube whose rate was still large
or a family total above `Thresh` (`foldl_trigger`), so reaching the cap `j*`
forces an overflow (`level_cap_subset`) — which is what `Pr[⋃_{j≥j*} Nois(j)]`
was supposed to mean. Assembling,
[`Ttc.traj_numlattice_le`](Ttc/Coupling/Run.lean) proves `lem:numlattice`'s bound
outright for the coupled run, with a *smaller* right-hand side than the paper's.

The paper cites `lem:process` for the *equivalence* of its three procedures but
never builds the coupled family, and without it the union bound has nothing to
range over. So `lem:numlattice`'s proof as written is not merely imprecise: the
object its main estimate is about does not exist.

**And the repair is wired into the headline.** `traj_numlattice_le` is about the
trajectory model specifically, while `Ttc.TtcProb` carries an arbitrary `Ω`, `μ`
and `O`; the sampler fields identify the two, and
[`Ttc.numlattice_union_of_model`](Ttc/Coupling/Transfer.lean) transports the bound
across. The `numlattice_union` field is **deleted**; the same statement is now a
theorem. A transitive dependency walk from `Ttc.TtcProb.volume_estimate` reaches
`Ttc.traj_numlattice_le` and `Ttc.trajLaw` (see
[Verifying the claim](#the-dependency-walk)). What remains is the modelling
judgement the fields encode, not a missing estimate.

### 13. Genuine gap — the `Vol_ED` failures are never union-bounded

`alg:ttc` line 18 sets `δ' ← δ/(4m)` and line 24 calls `Vol_ED(P(cᵢ), ε', δ')`
once per polytope, so the `m` calls fail with total probability up to `δ/2`. The
proof of `lem:numlattice` uses their output as if it were exact —
`analysis.tex:269`: "by the accuracy guarantee of `Vol_ED`, the call returns `t`
such that `t ∈ [(1−ε')vol Pⁱ, (1+ε')vol Pⁱ]`" — and then bounds only
`δ/6 + δ/6`. The `δ/2` never enters the union bound.

**It is harmless, but only because of the slack**: `δ/4 + δ/4 + δ/6 + δ/6 = 5δ/6
≤ δ` ([`Ttc.numlattice_failure_bound_with_vol`](Ttc/Process/Sketch.lean), with
[`Ttc.Params.vol_failure_eq`](Ttc/Process/Sketch.lean) showing `m·δ' = δ/4` for
each of the two oracle families). Had `Thresh` been chosen to make each branch
`δ/2` rather than `δ/6`, the stated conclusion would be false. `δ'` was also
missing from the parameter block entirely; it is now
[`Ttc.Params.deltaPrime`](Ttc/Model/Prelude.lean).

**The missing union bound is now supplied.** Since `Vol_ED`'s contract became
Cousins–Vempala Theorem 1.1 (`Ttc.VolumeAlgorithm`), the `m` calls can be charged
properly: [`Ttc.measure_volGood_ge`](Ttc/Volume/Bridge.lean) is the union bound
over the calls, and [`Ttc.TtcProb.volGood_prob_budget`](Ttc/Volume/Bridge.lean)
instantiates it at `δ' = δ/(4m)` to give `1 − δ/4` — landing inside the share
[`Ttc.numlattice_failure_le`](Ttc/Process/SketchProcess.lean) already reserved. So
on this side the estimate the paper skips is proved, not assumed; what it is
proved *about* is the run's assumption `volCoins_good`, not the run's own
randomness (see finding 13a).

### 13a. What is still assumed about `Vol_ED`

`Ttc.TtcProb.vol` is deterministic by construction — `oracle_eq` binds it outside
the sample point — so the development conditions on `Vol_ED` having succeeded
(`volCoins_good`) rather than integrating over its coins. The probability of that
condition is proved (`volGood_prob_budget`), and the headline
`Ttc.TtcProb.volume_estimate` still reads `1 − δ` over the *run's* randomness at
a fixed good `volCoins`.

**The joint form is now proved, additively, alongside it.**
[`Ttc/Coupling/Product.lean`](Ttc/Coupling/Product.lean) gives `1 − δ − δ/4` over
the randomness of *both* oracle and run, in two forms:
[`Ttc.volume_estimate_joint`](Ttc/Coupling/Product.lean) as an iterated integral
`∫⁻ c, trajLaw (θ c) (…) ∂volAlg.μ`, and
[`Ttc.volume_estimate_joint_compProd`](Ttc/Coupling/Product.lean) as a single
sample point of a single space. The route is: transport `volume_estimate` onto the
constructed trajectory space (`TtcProb.volume_estimate_traj`, spending
`law_eq`/`oracle_eq` through `Measure.le_map_apply`, so no measurability of the
success set is needed); an abstract union bound
(`Ttc.toReal_lintegral_ge_of_cond`); and, at every good coin,
`Ttc.canonicalTtcProb` to build a genuine `Ttc.TtcProb` on that space. Nothing in
`Coupling/{Family,Run,Transfer}`, `Model/ProblemSetting`, `Model/Theorem` or
`Witness/BoxProb` is touched, and `Ttc.TtcProb.volume_estimate` keeps its exact
statement and axiom profile.

**Three caveats, all of which matter.**

* **The joint law is a composition-product, not a product.** It is emphatically
  *not* `T.μ.prod T.volAlg.μ`: the run's law `trajLaw θ` is a *function of the
  coins* (`theta_eq` ties `θ s` to `vol i`, `volED_eq` ties `vol i` to the
  oracle's estimate at the coins), so the second marginal moves with the first
  coordinate. The right object is `volAlg.μ ⊗ₘ κ` with `κ c = trajLaw (θ c)` —
  coins first, then the run they drive.
* **The bound is vacuous for `δ > 4/5`.** `1 − δ − δ/4 ≤ 0` there, and `TtcProb`'s
  `hδ0`/`hδ1` give only `0 < δ ≤ 1`. The theorems hold for every `δ ∈ (0,1]` and
  are simply uninformative above `4/5`; that is stated rather than patched. The
  same `δ/4` is what `Ttc.ttc_volume_endToEnd` concludes at, and
  [`Ttc.ttc_volume_clean`](Ttc/Exec/Budget.lean) /
  [`Ttc.ttc_volume_final`](Ttc/Exec/Final.lean) only *reprice* it — running at the
  internal `δ₀ = 4δ/5` so the user's number is the delivered one — which does not
  improve the analysis and does cost `5/4` in Monte-Carlo samples and an additive
  `O(1/ε²)` in `Thresh`. `Ttc.Box.old_budget_vacuous_at_nine_tenths` records the
  `δ = 9/10` comparison (`−1/8` versus `1/10`) as a lemma rather than as prose.
* **The single-sample-point form costs one extra hypothesis, and it is visible.**
  `volume_estimate_joint_compProd` takes the kernel `κ` and `hκ : ∀ c, κ c =
  trajLaw (θ c)` as binders, i.e. it assumes `c ↦ trajLaw (θ c)` is *measurable*
  in `c` — a regularity condition on the map, not a probabilistic claim, and what
  a joint space costs, since without it `volAlg.μ ⊗ₘ κ` does not exist. It is not
  vacuous: `Ttc.kernelOfDiscrete` supplies it for any discrete coin space, in
  particular for `Ttc.VolumeAlgorithm.exact`, whose coin space is `Unit`.

What is *not* done: `Ttc.TtcProb.volume_estimate` itself has not been restated
jointly, and `volCoins_good` is still a field of `TtcProb`. What **is** done is
downstream: [`Ttc.ttc_volume_monteCarlo`](Ttc/Exec/VolDischarge.lean) follows this
file's shape with the oracle *constructed* rather than assumed, integrating
`Ttc.MonteCarlo.coins` out and averaging `volCoins_good` out on `Ttc.mcGood`
(`Ttc.measure_mcGood_ge`), so on the capstone's route neither is a hypothesis. See
[`CV-ROADMAP.md`](CV-ROADMAP.md) §6.

### 16. Genuine hazard in the *statement* — `ENNReal.toReal ⊤ = 0`. *Closed.*

Not a defect in the paper, but in what a Lean formalisation can silently claim,
and it is the kind of thing `#print axioms` cannot see. `Ttc.volSol M φ` is
`(volume (sol M φ)).toReal`, and Mathlib's `ENNReal.toReal ⊤ = 0`. So if `Sol(F)`
had infinite volume, the headline would read "the output is within `(1±ε)` of
`0`" — true, and vacuous.

The hazard is real and exhibited, not hypothetical:
[`Ttc.VolSolCheck.volSol_tt_eq_zero`](Ttc/Volume/VolSolCheck.lean) proves
`volSol M .tt = 0` for every interpretation `M` in dimension `n ≥ 1`, even though
`Sol(⊤) = ℝⁿ`.

What rules it out for an actual `Ttc.TtcProb` is the field `volume_ne_top`
(finding 10), which asserts finiteness of each `region M c` **separately** — not
of `sol M φ`. That this suffices is
[`Ttc.VolSolCheck.volume_sol_ne_top`](Ttc/Volume/VolSolCheck.lean): a DNF is a
`List`, hence finite, and measures are countably subadditive (no measurability
needed). The consequence worth quoting is
[`Ttc.TtcProb.ofReal_volSol`](Ttc/Volume/VolSolCheck.lean): under that hypothesis
`volSol` loses no information, `ENNReal.ofReal (volSol M φ) = volume (sol M φ)`.

The same file also cross-checks the *semantics* rather than the plumbing:
`Ttc.BForm.holds` is a `Prop`-valued recursion and nothing forces it to be the
usual truth tables, so `Ttc.VolSolCheck.evalBool` re-implements it as an
independent `Bool`-valued evaluator and `sol_eq_evalBool` / `volSol_eq_lra`
identify the two.

### 17. Total variation → pointwise is **provably unbridgeable**, and the ball walk has no uniform minorisation

This one killed a plan rather than a proof, and it is machine-checked
([`Arlib/MarkovChains/Continuous/PointwiseMixing.lean`](Arlib/MarkovChains/Continuous/PointwiseMixing.lean),
axiom-clean).

`AUDIT-KV97.md` §4b establishes that Kannan–Vempala's Theorem 2 needs a
**pointwise** `(1±ε)` density hypothesis, not a total-variation one: a TV
hypothesis buys only an *additive* error, and summing over the `N` lattice points
contributes `N·ε`. The plan of record was to obtain the pointwise hypothesis by
running the ball walk until it mixed. That cannot work:

* `not_exists_pointwiseClose_of_tvLe` — for **every** TV tolerance `δ ≠ 0` there
  is **no** `ε` whatsoever making `TVLe μ ν δ → PointwiseClose μ ν ε`, `ε = ⊤`
  included;
* `exists_tvLe_not_pointwiseClose` — even restricted to `μ ≪ ν`, two probability
  measures at TV `≤ δ` can have density ratio `1/δ`. So the failure is not an
  artefact of demanding a density; it is the *ratio* that TV does not control;
* `not_uniformMinorisation_of_unreachable` plus ball-walk locality — one step of
  `ballWalk K δ` from `x` is supported in `ball x δ ∪ {x}`, so for any `K` of
  diameter `> δ` **no uniform minorisation constant exists**. This is *locality*,
  a separate and worse obstruction than the `ℓ(x) → 0` boundary degeneracy that
  Cousins–Vempala's speedy walk repairs; restricting to speedy points fixes the
  holding probability and does **not** fix locality.

A candidate replacement is worked out in
[`PointwiseRoute.lean`](Arlib/MarkovChains/Continuous/PointwiseRoute.lean): an
additive error `ε` **is** a relative error `ε·V`, so a TV tolerance of
`θ/Vol(P')` — not `θ` — delivers the window Theorem 2 needs, and mixing time is
*logarithmic* in the tolerance, so the price is a factor `O(n · bits)` in the step
count. That file also records a second obstruction neither the audit nor
`PointwiseMixing` had noticed: a ball-walk law started at a point keeps an atom
forever, and one atom destroys pointwise closeness for every `ε` at every finite
time — so for the actual chain from the actual start the pointwise hypothesis is
not merely hard to obtain, it is *false*.

**Status: acted on.** The replacement was carried out. `contDensity`, `density_au`
and `density_int` are **no longer fields** of `Ttc.KV97Sampler`; it now carries a
law and a total-variation bound (`contLaw`, `isProbContLaw`, `contVol`,
`contVol_pos`, `contVol_eq`, `law_tv`). The pointwise route is retained in
`PointwiseRoute.lean` as the *consumer* of a TV hypothesis, not as a hypothesis of
its own.

Two consequences worth stating, both machine-checked:

* the TV formulation is **strictly more permissive**, not merely different.
  `Arlib.TVWitness.exists_nondegenerate_theorem2_of_tvLe_witness`
  ([`TVWitness.lean`](Arlib/MarkovChains/Continuous/TVWitness.lean)) inhabits the
  whole hypothesis bundle at *strictly positive* TV — so the bundle is not
  vacuous — and the same witness proves
  `∀ ε, ¬ PointwiseClose μ (uniformOn volume S) ε`. The law that satisfies the TV
  route is exactly the atom-carrying shape the pointwise route provably cannot
  describe. A second witness, `boxDensityLaw`, is absolutely continuous, so the
  inhabitation does not depend on the atom either;
* the earlier `AUDIT-KV97.md` §4b conclusion — that TV *cannot* suffice — was
  **wrong**, and is retracted there. TV suffices at tolerance `θ/V`, and mixing
  time is logarithmic in the tolerance. What is *not* fixed by this is finding 19.

**And the route has since been walked.** `law_tv` is no longer a hypothesis
anywhere on the capstone's path: [`Ttc/Sampler/Construct.lean`](Ttc/Sampler/Construct.lean)
builds `contLaw` as a lazy ball-walk iterate on the inflated polytope and proves
`law_tv` at exactly the `ε'/(4·Vol(P′))` tolerance this finding identified, from
`Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope`. The price is the one
finding 19 predicted for any route that keeps a *uniform* stationary measure: an
exponentially small isoperimetric constant, hence an exponential step count. So
this finding is **closed as stated** — the pointwise route is dead and the TV
route works — while the efficiency question it opened is not.

### 18. Fine, implicit — `Arlib.KV97.acceptance` is not a probability without three hypotheses

The equation `Pr[rnd p ∈ P] = ∑_{x ∈ P∩ℤⁿ} Pr[rnd p = x] = acceptance pt w`
appears in the prose of Kannan–Vempala's Lemma 1 and in the original docstring of
`Arlib.KV97.acceptance`, which named **one** hypothesis. Proving it needed
**three**, and `Arlib.KV97.acceptance_eq_measure_apply` now states and uses all
of them ([`Arlib/Lattice/KV97/Lemma1.lean`](Arlib/Lattice/KV97/Lemma1.lean)):

* **`pt` is injective** — a repeated point is counted twice by the sum and once by
  the event. Not a technicality:
  `Arlib.KV97.measure_range_lt_acceptance_of_not_injective` exhibits a probability
  measure and a two-element constant `pt` with mass `1` but `acceptance = 2`;
* **`pt` is exhaustive** (`P ∩ ℤⁿ = Set.range pt`) — otherwise the sum misses mass
  the event contains. The bounds of the lemma never need this, which is why it
  went unnoticed;
* **the law is carried by the lattice** (`μ (ℤⁿ)ᶜ = 0`) — otherwise the event
  contains non-lattice mass no singleton accounts for. Free for the rounding law.

Plus a fourth, technical: each point mass must be finite (`μ {pt i} ≠ ⊤`), since
`ENNReal.toReal ⊤ = 0` again. **Consequence for the audit:** the non-vacuity
witness `Arlib.KV97.exp_neg_one_le_acceptance_cube` takes `pt` *constant*, so for
that witness `acceptance` is **not** a probability — it witnesses that the
hypothesis bundle of the numeric bounds is inhabited, and nothing more.

### 19. The speedy walk's stationary bias does **not** decay with time

Not a finding about the paper — a finding about this development's own plan, and
the reason the sampling oracle cannot be discharged *efficiently*. (It **is**
discharged: [`Ttc/Sampler/Construct.lean`](Ttc/Sampler/Construct.lean) uses the
lazy **ball** walk, whose stationary measure is exactly uniform, and pays this
finding's price as an exponential step count rather than as a bias.)
Machine-checked in
[`SpeedyToUniform.lean`](Arlib/MarkovChains/Continuous/SpeedyToUniform.lean) and
[`HoldingTime.lean`](Arlib/MarkovChains/Continuous/HoldingTime.lean).

Cousins–Vempala's *speedy walk* has the conductance bound one wants
(`conductance_speedyWalk_ge`, with **no** local-conductance hypothesis), but its
stationary measure is `ellProb` — density proportional to the local conductance
`ℓ` — not the uniform measure. `tvLe_ellProb_uniformOn` bridges the two at cost
`s/(1-s)` under `IsSmooth K δ s`.

That cost is a bias **in a fixed measure**: running longer does not reduce it.
Only shrinking `δ` does, and `δ` enters the step count as `δ⁻²`. Kannan–Vempala
Theorem 2 needs total variation below `θ/V` with `V = Vol(P')` exponentially large
in the bit-length, so the bias forces `δ ≲ θ/(nV)` and the composed step count
becomes polynomial in `V` — i.e. **exponential in the input size**. The *mixing*
half of the same tolerance costs only `log V`
(`conductanceMixingTime_inv_volume_le`); it is the bias alone that is fatal. So
`mixesWithin_lazy_speedyWalk_uniformOn` is a genuine uniform sampler at **fixed**
tolerance and is not usable at the lattice-counting tolerance. Both caveats are in
the theorems' own docstrings.

The natural repair — bound the ball walk's conductance below, since
`isReversible_ballWalk` makes its stationary measure *exactly* uniform — is
**refuted, and the refutation is now formal**.
`conductanceOn_ballWalk_mul_volume_inter` proves the *equality*

`Φ_ball(A) · vol(A ∩ K) = Φ_speedy(A) · ellMeasure(A)`,

so the loss is exactly the average of `ℓ` over `A`, and
`conductanceOn_ballWalk_le_conductanceOn_speedyWalk` shows the inequality only ever
goes the useless way. `IsSmooth` bounds the average of `ℓ` over `K`, not over every
`A`, and a set hugging the boundary has small average `ℓ`. A global floor on `ℓ` is
exponentially bad (`ℓ ≥ 2⁻ⁿ` is the best uniform bound on the unit ball).

What *is* established, unconditionally, is the exact time-change identity
`ellMeasure_withDensity_inv_ell`:

`(ellMeasure K δ).withDensity (fun x => (ℓ x)⁻¹) = volume.restrict K`,

the measure-level statement that (density ∝ `ℓ`) × (mean holding time `1/ℓ`) is
uniform exactly, with no error term and no smoothness hypothesis. Turning it into a
mixing-time statement needs the *trajectory*-level fact that the holding times are
conditionally independent `Geom(ℓ(Yᵢ))` given the jump chain. Mathlib has the raw
material (`Kernel.traj`, Ionescu–Tulcea) but nothing here builds a trajectory
measure for these kernels; that is the open step.

---

### 20. Genuine gap — `lem:numlattice`'s proof is vacuous when `Vol(Sol F) < Thresh/4`

*Found by the formalisation, and machine-checked:*
[`Ttc.Box.big_not_derivable`](Ttc/Exec/Regime.lean).

`sections/analysis.tex:284` defines `j*` as the smallest `j` with
`1/(2^j·10^{ρn}) < Θ/(4|S^{(m)}|)`, and splits the failure probability as

```
Pr[⋃ⱼ (Nois(j) ∧ Err(j)) | Good]  ≤  Σ_{j=0}^{j*−1} Pr[Err(j) | Good]  +  Pr[⋃_{j≥j*} Nois(j) | Good]
```

The bound on the second term at `analysis.tex:289` argues that `⋃_{j≥j*} Nois(j)`
"occurs if `p` decreases from `1/2^{j*−1}` to `1/2^{j*}`", and the bound on the
first uses the displayed inequality at `analysis.tex:295`,
`Λ_{j*−1} > (1−ε')Θ/8`. **Both presuppose `j* ≥ 1`, which the paper never states.**

At `j* = 0` the split degenerates: the first sum is empty (`= 0`), and the second
is `Pr[⋃_{j≥0} Nois(j)]`, which is the **sure event** — `p` always ends at `1/2^j`
for some `j ≥ 0` — so the displayed bound reads `≤ 1` and certifies nothing. There
is no `j* − 1 = −1` level for the paper's argument to run at.

**When does it happen?** `j* = 0` ⟺ `|S^{(m)}|/10^{ρn} < Θ/4` ⟺, by `lem:lattice`,
`Vol(Sol F) ≲ Θ/4`. And **refining the precision does not escape it**: `ρ`
multiplies the lattice-point count by `10^{ρn}` and divides each point's Poisson
rate by the same factor, so the total rate `Λ₀` is `Vol(Sol F)` up to `(1±ε')²`,
independent of `ρ`. That cancellation is
[`Ttc.Box.sum_rates_box_window`](Ttc/Exec/Regime.lean); the resulting independence
of the hypothesis is [`Ttc.Box.big_not_derivable`](Ttc/Exec/Regime.lean), which
exhibits a box satisfying every other hypothesis of the headline while the
inequality at `analysis.tex:295` fails.

**The excluded regime is not a corner.** `Θ = max(24 ln(24/δ)/((1−ε')ε'²),
15(ln(6/δ)+ln m))` with `ε' = ε/12`, so at `ε = δ = 0.1, m = 1` the guarantee needs
`Vol(Sol F) ≳ 4.8 × 10⁵`; at `ε = 1, δ = 0.1` it still needs `≳ 5 × 10³`.

**Corrected form — and the corrected algorithm is now implemented, not merely
stated.** Two fixes were needed, and only the second makes the theorem
unconditional; **both are machine-checked and on the build path.**

1. *State the condition.* `lem:numlattice` holds as stated with the added hypothesis
   `Θ/4 ≤ Vol(Sol F)` (equivalently `j* ≥ 1`), and
   [`Ttc.big_of_volume`](Ttc/Exec/RegimeMain.lean) derives `analysis.tex:295` from it.
   That is the rung [`Ttc.ttc_volume_vol`](Ttc/Exec/Inputs.lean) sits at, carrying
   `hvol : Thresh/4 ≤ Vol(F)` as a hypothesis.
2. *Remove it, by amending the algorithm — done.* The condition cannot be dropped
   from `alg:ttc` **as printed** — `p ← 1` and only halves, so the sketch is
   `Poisson(Λ)` with `Λ ≤ Vol(Sol F)`, and on a body of volume `10⁻⁶` the algorithm
   draws `Pois(10⁻⁶)` points and returns `0`. So the algorithm gains one line, and
   the formalisation now **runs it**: the input is dilated by
   [`Ttc.runScale`](Ttc/Exec/Rescaled.lean) `= max 1 (Θ/(Vₙ·γ̂ⁿ))`
   ([`Ttc.scaleFactor`](Ttc/Exec/ScaleFactor.lean)), the run happens on
   [`Ttc.scaledAtoms`](Ttc/Exec/Rescaled.lean), and the estimate is divided by `cⁿ`
   inside the conclusion. `Vol(c·S) = cⁿ·Vol(S)` exactly
   ([`Ttc.volSol_scaleAtoms`](Ttc/Exec/Scale.lean)); `c` is computable from `γ̂` and
   `n` alone, with **no knowledge of `Vol`**, and the parameter block does not move
   ([`Ttc.inputParams_scaleAtoms`](Ttc/Exec/Rescaled.lean), by `rfl`), so there is no
   circularity and nothing is assumed. The hypothesis is then *discharged*
   ([`Ttc.hvol_scaled`](Ttc/Exec/Rescaled.lean)), giving
   [`Ttc.ttc_volume_rescaled`](Ttc/Exec/Rescaled.lean) with no volume hypothesis at
   all, and [`Ttc.ttc_volume_estimate`](Ttc/Model/Theorem.lean) inherits it.

**The paper needs that line, and "false" is now a theorem rather than an argument.**
[`Ttc.SmallBody.small_box_refutes_final_accuracy`](Ttc/Findings/SmallBody.lean) negates
the accuracy conjunct of [`Ttc.ttc_volume_final`](Ttc/Exec/Final.lean) itself — the
`MonteCarlo.coins` integral — at an explicit small box, for `δ ∈ (0, 5/6)`, at a **good**
coin of the constructed volume oracle, so it is not an artefact of a bad volume estimate.
`Ttc.SmallBody.final_accuracy_shape` is the lookalike guard: it *proves* the very
proposition that is negated, from `Ttc.Box.ttc_volume_final_at_box`, with `big` as its
only hypothesis — so the refuted statement really is the capstone's, and `big` is the
only thing standing between `ttc_volume_final` and a contradiction.

The chain is: `p ← 1` and only halves (`Ttc.SmallBody.p_run_le_one`), so on a small body
the sketch never leaves level `0` and is empty with probability `e^(−Λ)`
(`Ttc.SmallBody.trajLaw_level_zero`, an exact computation, not a bound); an empty sketch
outputs `0` (`run_eq_zero_of_card_eq_zero`); and `0 ∉ (1 ± ε)·V` for `V > 0`, `ε < 1`
(`output_zero_not_mem_relErr`).

*Scope, stated precisely.* The coins-integrated refutation covers `δ ∈ (0, 5/6)` — the
development supplies only `Pr[volume oracle fails] ≤ δ/5`, so beating `1 − δ` needs
`6δ/5 < 1`; nothing is claimed on `[5/6, 1)`. The **per-coin** refutation
(`small_box_refutes_accuracy`) has no such restriction. Both are about the *modelled*
run, so they inherit `Model/Pseudocode`'s four documented deviations, and `thm:runtime`'s
`runCost` conjunct is untouched. Correspondingly,
`Ttc.ttc_volume_estimate` is unconditional **for the amended algorithm** and says
nothing about the printed one on a small body. Do not quote it as a guarantee for
`alg:ttc` as printed.


**The main result stands.** Finding 1 changes constants, not the shape of the
theorem, and finding 2 is now closed by a different proof; finding 3 is a typo in
an exponent whose corrected form is stronger than needed; finding 14 is a false
*statement* of a true step; findings 10 and 13 are gaps the paper genuinely needs
closing (one by an added hypothesis, one absorbed by existing slack); 4–9, 11, 12
and 18 are presentational or self-closing; 16 is closed; 13a's remaining step is
now taken, additively, by [`Coupling/Product`](Ttc/Coupling/Product.lean).
**Finding 15 is the one
that needed a construction, and it has one**: the coupled family and its pathwise
identification with the run are built here
([`Coupling/Family`](Ttc/Coupling/Family.lean),
[`Coupling/Run`](Ttc/Coupling/Run.lean)), `lem:numlattice`'s bound is proved for
the run they drive, and [`Coupling/Transfer`](Ttc/Coupling/Transfer.lean)
transports it to any problem instance whose randomness *is* that construction.
**Finding 17 is closed too**: the pointwise route it killed was replaced by the
total-variation one, `density_au` by `law_tv`, and `law_tv` is now *proved* for a
constructed lazy ball-walk sampler — so the sampling oracle is discharged, not
merely reduced.

**Finding 19 is what remains open; finding 20 is a genuine gap in the paper that
the development has closed by *changing the algorithm*.** Finding 20's gap is real —
`lem:numlattice`'s proof certifies nothing when `Vol(Sol F) < Thresh/4`, and the
counterexample [`Ttc.Box.big_not_derivable`](Ttc/Exec/Regime.lean) is machine-checked.
The development no longer carries the missing hypothesis: it dilates the input
([`Ttc/Exec/Rescaled.lean`](Ttc/Exec/Rescaled.lean)) and discharges it. **That is an
amendment to `alg:ttc`, not a proof of the paper's step** — as printed the algorithm
is *wrong* in that regime, and nothing here says otherwise.

**Finding 19 is an efficiency finding.** Both
constructed oracles — hit-and-miss Monte Carlo for `Vol_ED`, the lazy ball walk
for `GenerateSamples` — are **exponential in the dimension**, and no polynomial
route is proved: that needs the Localization Lemma (still unproved and unassumed)
or a speedy walk whose stationary bias does not decay. `thm:runtime` beyond the
paper's own charged accounting remains out of scope. The development establishes
that the analysis holds unconditionally, not that the algorithm is fast.
