# Formalizing Cousins–Vempala Theorem 1.1 — what it would take

> **`gaussian-cooling-vempala` is no longer a submodule of this repository.** It
> was never a build dependency — `lakefile.toml` requires only Mathlib, and every
> `GaussianCooling` import in this project is `Arlib.Convexity.GaussianCooling.*`,
> in-repo under [`Arlib/Convexity/GaussianCooling/`](Arlib/Convexity/GaussianCooling/).
> The submodule was the *source* the §5.1 material was ported from, and that port
> has happened, so it was removed and the checkout relocated to
> `../gaussian-cooling-vempala` (a sibling directory, with its uncommitted work
> intact). Paths of the form `../gaussian-cooling-vempala/…` below refer to that
> checkout; if you do not have it, they are citations you can skip — nothing here
> depends on them.

Scope note for `Ttc`: `Ttc.TtcProb` carries `volAlg : VolumeAlgorithm n`, an
assumption that `Vol_ED` is accurate. (An older revision of this line named
`Ttc.TtcProb.volED_hi`; that is **no longer a field** — it came back as a theorem,
see §6.) The intended discharge was Cousins–Vempala Theorem 1.1
(`../gaussian-cooling-vempala/vol3_journal.tex:144`):

> There is an algorithm that, for any `ε > 0`, `p > 0` and convex body `K` in `ℝⁿ`
> that contains the unit ball and has `E_K(‖X‖²) = O(n)`, with probability `1 − p`,
> approximates the volume of `K` within relative error `ε`, with complexity
> `O*(n³)` in the membership oracle model.

That theorem is **not** formalized in the sibling `gaussian-cooling-vempala` checkout,
and this file records honestly what closing the gap involves. The statement is
now written in Lean as `Ttc.VolumeAlgorithm` (`Ttc/Volume/Oracle.lean`) so that
a future formalization plugs in without touching the rest of `Ttc`.

---

## 0′. Status, 2026-08-11 — supersedes §0 on the CV side

§0 below is still correct about `Ttc`: the volume oracle is discharged by
hit-and-miss Monte Carlo, the capstone does not wait on Cousins–Vempala, and the
price is **exponential in `n`**. What §0 says about *this* file's subject —
"`Ttc/Volume/CousinsVempala.lean` is exactly where it was" — is no longer true.
Here is the state, and it is deliberately unflattering.

### The headline is unchanged, and will stay unchanged until two things happen

`cVol = O(n⁴)` **cannot** be substituted into `Ttc/Model/Theorem.lean`. Two
independent things block it, and closing either alone changes nothing:

1. **`thm:iso`'s inputs — now one, not four.**
   `Arlib/Convexity/SharpIsoperimetry.lean` proves `gaussianRestricted_isoperimetry`
   at exactly `d/σ` — the sharp constant — from four residual binders `hloc`,
   `hcombinatorial`, `h1d1`, `h1d2`. Three of those are now discharged outright, and
   `Arlib.gaussianRestricted_isoperimetry_concave`
   (`Arlib/Convexity/SharpIsoperimetryConcave.lean`) carries **`hloc` alone**.
   They were always hypotheses, never axioms, and every file involved is axiom-clean;
   but a theorem with an open binder still proves nothing about any algorithm, so the
   headline does not move until `hloc` closes.

   The cost of the third discharge belongs with the statement: `(1d-2)` is available
   at `1/(2√3) ≈ 0.289`, not the paper's `ln 2 ≈ 0.693`, so the metric branch of the
   separation hypothesis reads `2√3·d ≤ ‖u−v‖` rather than `d/ln 2 ≤ ‖u−v‖` — a
   threshold larger by `2√3·ln 2 ≈ 2.401`. The conclusion `d/σ` is unchanged. When
   `thm:iso` is eventually wired into `conductance_speedyGaussian_ge`'s `hiso`, that
   factor propagates into the conductance constant and must be quoted there too.
2. **`Ttc/Model/Pseudocode.lean` instantiates `Vol_ED` as `Ttc.mcVol`.** Even a
   finished CV would have to be swapped in there. Substituting `O(n⁴)` today
   would assert what the formalisation currently *refutes*.

### The critical path, and where each link stands

`thm:iso` (tex:467) ← Localization + `hcombinatorial` (tex:497) + (1d-1)
(tex:498) + (1d-2) (tex:501) → `thm:speedyconductance` (tex:624) → `thm:volume`.

| Link | State |
|---|---|
| `thm:speedyconductance` | **proved** from `hiso`+`hoverlap` (`SpeedyConductanceSharp.lean`), polynomial constant `δ log 2/(640 σ √n)` |
| Localization (A),(B) | proved — `LocalizationAffine`, `LocalizationTransverse` |
| Localization (D) chain closedness | **closed** — `LocalizationClosed.lean` |
| Localization (E) slab rigidity | **closed** — `NeedleSlab{,Affine,Chain}.lean` |
| Localization (C) lower semicontinuity | open; the general-position form asks for *bounded continuous* integrands |
| Localization (F) transport + nondegeneracy | open, both as explicit hypotheses |
| `hcombinatorial` unmixed half | **closed** — `IntervalReduction.lean` |
| `hcombinatorial` interleaved half | **closed** — `Arlib.oneDim_partition` (`LogisticIso.lean`), for arbitrary measurable partitions, no side condition |
| (1d-1) | **closed for concave profiles** — `Arlib.kls38_concave` (`KLS97Lemma38.lean`), at the paper's `4√n`; `kls38_affine` recovers the printed form |
| (1d-2) | **closed**, at `1/(2√3)` rather than the paper's `ln 2` — `Arlib.oneDim_isoperimetry_gaussianFactor_unconditional`, on `Arlib.brascampLieb_oneDim` |
| `hoverlap` at separation `δ/√n` | **the `√n` is closed unconditionally** — `ell_le_speedyWalk_add_speedyWalk_compl_sqrt` (`SpeedyOverlap.lean`); `cor:overlap` itself still needs KLS95 Lemma 3.5, see below |

The concave-vs-affine gap was the structural one, and it is now **resolved by
restatement rather than by upgrade**. The localization stack delivers `W` with
`W^(1/m)` **concave** (`W = ℓ^m`, `ℓ` concave), while `hloc` as stated — following
the paper — asks for an **affine** profile `(c₀ + c₁t)^(n−1)`. The upgrade is not
available: `Arlib.exists_convex_slice_profile_not_affine` (`LocalizationLimit.lean`)
refutes it. So `hloc` was restated in concave form and (1d-1) reproved there —
`Arlib.kls38_concave` uses concavity only, and
`Arlib.gaussianRestricted_isoperimetry_concave`'s `hloc` binder asks for
`ConcaveOn ℝ (Set.Icc α β) l` in place of the affine witness. Affineness no longer
bites anywhere on the critical path.

**What now separates `hloc` from the localization output** is shape, not
mathematics — three deltas, all inside the binder:

* localization gives `ConcaveOn ℝ (Set.Ioo 0 1) (W ^ (1/m))`, `hloc` wants it on a
  closed `Set.Icc α β` (an endpoint extension; the endpoints are null, so no integral
  moves);
* localization's axis `b + t•v` is normalised by `φ v = 1`, while `hloc` needs
  arclength `‖e‖ = 1` — forced downstream, because it is what makes the needle's
  Gaussian carry the *same* `σ` as the ambient one (`Arlib.gaussian_needleMap`);
* localization states full-line integrals, `hloc` interval and set integrals.

None of these is a mathematical obstruction. The genuine residuals remain
localization's own **(C)** and **(F)**, and (C) bites here specifically because
`g₁ = 1_{S₁}h − A·h` is built from an **indicator of a measurable set**, hence is
not continuous — which is exactly the hypothesis (C) is about.

### Nine findings against the Cousins–Vempala paper

Five are statements **false as printed**, not imprecision.

1. **(1d-2) is false as literally printed** without the variance-1 normalisation.
   Counterexample `w ≡ 1` on `[0,L]`, false for `L ≥ 13`.
2. **`thm:iso`'s density branch is missing a `σ`** — a dimensional error.
3. **tex:497's interval claim is false by counterexample.** "By a standard
   combinatorial argument we can assume the `Zᵢ` are intervals" is not a
   reduction; the *inequality* holds for general measurable partitions, but the
   `Zᵢ` may not be taken to be intervals.
4. **tex:497 stays false even after the missing separation hypothesis is
   restored** — `Arlib.hside_not_implied` (`IntervalReduction.lean`) exhibits
   machine-checked data satisfying every hypothesis with `Z₁` on **both** sides
   of `Z₂`: `D ≡ 1` on `[0,1]`, `Z₁ = [0.1,0.4] ∪ [0.6,0.9]`, `Z₂ = (0.45,0.5)`,
   `c = 5/22`.
5. **`thm:speedyconductance`'s `1/20` thresholds must be `1/40`** — the paper's
   contradiction never closes as printed.
6. tex:660's `π(S₁)` should be `π(S)`.
7. `lem:starting-gauss`'s `e²` should be `e^{1/2}` — a sharpening, in the
   paper's favour.
8. A units/dimensional clash in (1d-2).
9. **The terminal-phase second-moment bound is false unconditionally** —
   `Arlib.terminal_sq_moment_unbounded` (`TerminalPhase.lean`). It is true under
   flatness (`coolLaw_sq_moment_le_terminal`), which is what the construction now
   assumes.

### And a finding against the *schedule*, not the paper

`Arlib.geomSchedule_total_cooling_lt` (`PhaseSchedule.lean`): a fixed-rate
`α = 1/n` schedule that meets the per-phase variance budget cools by a factor
**less than `11/10`** — i.e. it does not anneal at all. Consequently
`Ttc.CV.cold_start_mem_relErr_of_fixedRate_fields` shows the fixed-rate
construction's *first telescope factor alone* already estimates `Vol K` to within
`11/(5n)`. The general-`α` schedule (`coolPhases`/`coolRate`) does anneal
(`Ttc.CV.cool_schedule_anneals`, total cooling `≥ e^L`), but annealing is not
free: enlarging `m` to buy cooling tightens the per-phase budget `κ/m` by the
same factor, and the crossover against `11/(5n)` sits at
`e^{2L} ≳ 17.6·L²/κ²` — essentially dimension-free
(`Ttc.CV.cold_start_exponent_ge_of_coolRate`).

**No running-time claim is made anywhere in the CV development.** A polynomial
phase count is not a polynomial algorithm; the per-phase sampling cost is
untouched, and `hTV` — the sampler — remains the only mathematical debt of
`Ttc/Volume/CousinsVempala.lean`'s constructions.

---

## 0. Status, 2026-08-08 — read this before the sections below

**Read (0) first: this roadmap is no longer on the critical path.**

Four things in this file are now out of date, three of them in ways that
**understate** what is proved.

**(0) The volume oracle has been discharged — by a different route.**
`Ttc.VolumeAlgorithm` is no longer an assumption of the development's strongest
statement, which is now **`Ttc.ttc_volume_final` (`Ttc/Exec/Final.lean`)**.
`Ttc.VolumeAlgorithm.monteCarlo` (`Ttc/Volume/MonteCarlo.lean`) *is* a
`VolumeAlgorithm n`, constructed — hit-and-miss Monte Carlo, not Gaussian cooling
— and `Ttc.ttc_volume_monteCarlo` (`Ttc/Exec/VolDischarge.lean`) removes
`volAlg`, `volCoins`, `volED_eq`, `volCoins_good`, `vol` and `vol_pos` from the
capstone's binder list, integrating the oracle's coins out against
`Ttc.MonteCarlo.coins` and charging its failure event `δ/4`, so the guarantee
reads `1 − δ − δ/4`. `Ttc.ttc_volume_endToEnd` (`Ttc/Exec/EndToEnd.lean`)
composes that with the constructed rates and a constructed ball-walk sampler and
carries **no oracle binder at all**;
`Ttc.ttc_volume_endToEnd_canon` (`Ttc/Exec/CanonPolytope.lean`) then removes the
polytope-description binders too — **ten raw, i.e. nine explicit plus the
`[Fintype Jt]` instance**; both counts appear in these documents, so read which
convention is in force (the note in `Ttc/Exec/Endgoal.lean` fixes it) — via the
*equality*
`Ttc.canon_body_eq_smul_region`; and `Ttc.ttc_volume_final` instantiates that at the
internal failure parameter `δ₀ = 4δ/5`, where `1 − δ₀ − δ₀/4 = 1 − δ`, so the
guarantee is a clean `1 − δ` in the user's `δ` over 26 explicit binders, all of them
inputs. See `AUDIT.md` §1c and §1d.

**Read the clean `1 − δ` as a repricing, not a strengthening.** No step of the
analysis improves; the algorithm is simply run at a tighter internal confidence, and
the difference is charged to the run: the Monte-Carlo sample count per polytope goes
up by a factor `5/4` (25 %) and `P.thresh` grows *additively* (`log(30/δ)` versus
`log(24/δ)`). What it buys is that the statement is informative on all of
`δ ∈ (0,1)` rather than only `δ ∈ (0, 4/5)`.

**And that statement now has a non-vacuity witness of its own.**
`Ttc.TwoCube.ttc_volume_final_two_cube` (`Ttc/Witness/TwoCube.lean`) instantiates
`Ttc.ttc_volume_final` **itself**, at every `(ε, δ) ∈ (0,1]²`, on a DNF with **two**
cubes — two disjoint boxes — with every binder discharged including `big`, plus the
numeral pairs `(1/3, 9/10)` and `(1/2, 1/4)` at bounds `1/10` and `3/4` proved `> 0`
in the statement. Before it, the strongest statement in the development had no
witness at all. Its volume estimates are `Ttc.VolumeAlgorithm.monteCarlo`'s own
output, so it exercises the *exponential* construction — twice per run, once per
cube — and it says nothing whatever about `Ttc.VolumeAlgorithm.cousinsVempala`,
which remains undischarged and is reached by no capstone. See `AUDIT.md` §3g.

**So: Phases 4–5 of this roadmap — §5's steps 3 through 6, the conductance /
mixing-time / isoperimetry / telescoping-estimator stack that leads to Theorem
1.1 — are no longer blocking anything.** The `Ttc` capstone does not wait on them.

**Two things that does *not* mean, and both matter more than the first.**

1. **It is not done.** `Ttc/Volume/CousinsVempala.lean` is exactly where it was:
   `Ttc.VolumeAlgorithm.cousinsVempala` is an *assembly towards* Theorem 1.1 whose
   only witnesses (`cousinsVempalaWitness`, `cousinsVempalaBiasedWitness`) have an
   `est` field that is `rfl`-equal to `(volume K).toReal` — the exact oracle in
   disguise — over `Ω = Unit`, one phase, `κ = 0`. **Nothing in this file has been
   discharged.** `Ttc.VolumeAlgorithm.cousinsVempala` is not reached by
   `Ttc.ttc_volume_endToEnd`, and so not by `Ttc.ttc_volume_final` either
   (`AUDIT.md` §5's walk reports `false`); it was *bypassed*, not proved. Nothing in
   the chain up to `ttc_volume_final` changes this: removing binders and repricing
   `δ` neither touch the volume oracle's construction.
2. **The route that replaced it is exponential in the dimension.** Hit-and-miss
   Monte Carlo needs exponentially many samples in `n`, and the ball walk's step
   count is exponential too (it inherits `κ = 2⁻ⁿ/D` from
   `Arlib/Convexity/IsoBall.lean`). Cousins–Vempala's whole point is the `O*(n³)`
   complexity, and **that** is what is still missing. What changed is that the
   missing thing is now a *complexity* claim rather than a *correctness* one — the
   development is unconditional and exponential, where before it was conditional
   and silent about cost. Anyone quoting "the volume oracle is discharged" without
   the second half is overstating the result.

**(i) Isoperimetry is no longer missing.** §3's gap table and §2a's "Assumed"
column both say so; both are stale. `Arlib/Convexity/IsoBall.lean` proves it
unconditionally — `uniformOn_iso_unitBall` at `κ = (1/2)ⁿ⁺¹` for the Euclidean
unit ball, and `uniformOn_iso_of_convex` at `κ = 2⁻ⁿ/D` for **every** bounded
convex body. No `def`, no `structure`, no `Prop`: every declaration in that file
is a theorem. In particular the submodule's `IsoInput`/`OneDimIso` predicates —
which assume their own conclusion, and are the reason the submodule's result is
worthless — are no longer the only route.

`Arlib/MarkovChains/Continuous/UnitBallMixing.lean` composes it through the whole
stack: `exists_unconditional_mixing_unitBall` discharges isoperimetry, the
local-conductance floor, Cheeger, the `L²` decay and the total-variation bound
*simultaneously*, with the warm start discharged by the stationary measure itself.

**The cost, which must always be quoted with it:** `κ` is exponentially small in
`n`, so the mixing time is exponential. **Not a polynomial-time algorithm.** A
polynomial constant still needs the localization route, whose sole remaining
obstruction is (P1) in `Arlib/Convexity/PositionalCut.lean` — and that file also
shows two things previously believed to block localization do not (bisection with
positional control is three lines; transverse thinning is achievable and executed
end-to-end on concrete data).

**(ii) The crux may never have been blocked for the case that matters.** The
recorded blocker was `ZLogconcaveHypothesis`, which is **false** for general
log-concave `f` (machine-checked counterexample at `f x = e^{-x}`, failing by
≈1.93, in `Arlib/Convexity/GaussianCooling/ZLogconcave.lean`). But the volume
algorithm's `f` is the **indicator of the convex body**, and
`zLogconcaveHypothesis_indicator` proves the hypothesis for exactly that case.
How far the variance chain then goes through unconditionally is under
investigation.

**(iii) A structural dependency this file does not record.** §6 claims the
`Ttc`-side work "does not depend on any of the above". At the level of the volume
algorithm's *hypotheses* that is right — `cousinsVempala` takes them as a flat
list, so `reps`/`varBudget`, the cooling chain, the independence/median plumbing
and the variance bound are four genuinely parallel packages. But the per-phase
estimator `W` and its unbiasedness `hphase_mean` require **sampling the phase-`i`
Gaussian restricted to `K`**. So the **volume oracle depends on the sampling
oracle**, and no amount of parallelism removes that edge.

**What is still true and load-bearing, restated.** An earlier revision of this
paragraph said "`Ttc.VolumeAlgorithm` is not constructible today". **That is now
false** — `Ttc.VolumeAlgorithm.monteCarlo` constructs one, assuming nothing, and
`Ttc.MonteCarlo.monteCarlo_est_ne_volume` proves it is *not* the exact oracle in disguise.
What remains true is the sentence with "Cousins–Vempala" put back in:
`Ttc.VolumeAlgorithm.cousinsVempala` is not constructible today. Its witnesses,
`cousinsVempalaWitness` and `cousinsVempalaBiasedWitness`, have an `est` field that
is `rfl`-equal to `(volume K).toReal` — the exact oracle in disguise — and the run
plumbing sits over `Unit`, where independence is vacuous by subsingleton. Neither
is progress, and both must be replaced rather than dressed up. The difference the
Monte-Carlo construction makes is that this is no longer the *only* way to obtain a
`VolumeAlgorithm`; it is still the only way to obtain a **polynomial-time** one.

---

## 1. What the submodule has today

`../gaussian-cooling-vempala/lean` is 3904 lines. §5.1 — the accelerated-cooling variance
bound — is proved end to end; §3, §4 and §5.2 now carry *interface* layers on top of it
(see §2a below):

| Result | File | Paper |
|---|---|---|
| `expect_ratio` — `E[Y] = G(b)/G(a)` | `Ratio.lean:94` | eq. at `:1078` |
| `expect_ratio_sq` — `E[Y²] = G(c)/G(a)` | `Ratio.lean:110` | eq. at `:1086` |
| `variance_ratio` | `Ratio.lean:135` | §5.1 |
| `lc_variance_bound` — `≤ exp(2R²α²/σ²)` | `Main.lean:52` | Lemma 5.8 |
| `fast_var_bound` — `≤ 1 + σ²/(C²n)` | `Main.lean:74` | Claim 5.11 |
| `fixed_var_bound` — `≤ 1 + 2/n` | `FixedRate.lean` | Lemma 5.10 |
| `filter_accept_ge`, `warm_start_accelerated` | `Sampling.lean` | Lemmas 4.2, 4.8 |
| `J_var_le`, `brascampLieb` — `J₂J₀ − J₁² ≤ (σ²/x)J₀²` | `Needle.lean:270`, `VDeriv.lean:115` | Theorem 4.1 |

**Two** cited results enter as hypotheses rather than theorems:
`LocalizationInput` (`Localization.lean:177`) and `ZLogconcave`
(`FixedRate.lean:110`).

The third, **Brascamp–Lieb (paper Theorem 4.1), is now proved**. The paper cites
[BL76] for the variance of the needle distribution, but the needle is
one-dimensional and its weight `s(x,t) = e^{γt}e^{-t²x/(2σ²)}` has a linear
logarithmic derivative in `t`, so one integration by parts suffices: applying the
fundamental theorem of calculus to `g(t) = (tJ₀ − J₁)s(x,t)` gives
`J₀² − (x/σ²)(J₂J₀ − J₁²) = g(u) − g(ℓ)`, where the exponential tilt cancels and
the boundary terms are nonnegative because the mean `J₁/J₀` lies in `[ℓ,u]`.
`variance_bound` and `lc_variance_bound` no longer carry the hypothesis, so the
accelerated variance bound now rests on the Localization Lemma alone.

**These are lemmas used inside the proof of Theorem 1.1, not Theorem 1.1.**
Nothing in the tree mentions the Lebesgue volume of the body, a success
probability, or an estimator. Greps for `∏`/`Finset.prod`, `chebyshev`, `median`,
`IndepFun` over that tree all return empty.

## 2. What is missing, by paper section

Theorem 1.1's proof runs through §3 (Isoperimetry), §4 (Sampling), and §5.2
(Proof of the main theorem). The headline results of §3 and §4 remain **assumed**; what
changed is that they are now *stated in Lean* rather than absent, and the parts of §4 and
§5.2 that Mathlib can support are proved (see §2a).

| Paper | tex lines | Content | Blocker |
|---|---|---|---|
| §3 Isoperimetry (`:404–508`) | ~105 | isoperimetric inequality for logconcave densities | no logconcavity or isoperimetry in Mathlib |
| §4.1 Conductance (`:514–746`) | ~230 | conductance of the ball walk, `thm:ball-walk` | **no conductance, no mixing time, no continuous-state Markov chain convergence in Mathlib** |
| §4.2 Warm start (`:747–826`) | ~80 | `M(Q₀,Q)` warmness propagation | needs §4.1 |
| §4.3 Wasted steps (`:827–937`) | ~110 | speedy walk accounting | needs §4.1 |
| §4.4 Speedy→target (`:938–1002`) | ~65 | mapping speedy to target distribution | needs §4.1 |
| §4.5 Sampling theorems (`:1003–1053`) | ~50 | `thm:sampling`, `thm:gauss-sampling` | needs §4.1–4.4 — **now stated** as `UniformSampler`/`GaussianSampler` |
| §5.2 Main theorem (`:1316–1611`) | ~295 | telescoping `W₁…W_m`, accuracy, median boost | needs §5.1 + §4 — **median boost and `lem:exp-bd`/`lem:fn-indep` now proved**; `lem:accuracy` still needs `lem:delta-ind` from §4 |

**The "Blocker" column names libraries, and most of them now exist** — in `Arlib/`,
not in Mathlib. Isoperimetry, conductance, Cheeger and conductance ⇒ mixing are all
proved (§3's third column). What is *not* closed is the quantitative content that
makes Theorem 1.1 worth having: every constant in the `Arlib` stack is exponential
in `n`, so the blocker for these rows has moved from "no library" to "no polynomial
constant".

The §5.2 proof ends at `:1588–1604`: the product estimator, a `4/5` success
probability, an `O(1)`-restart argument converting *expected* ball-walk steps
into a fixed count, `lem:accuracy`, and finally *"boost this probability of
failure to `1−p` by … repeating the algorithm `log 1/p` times and returning the
median."* **That last clause is where the `δ'` of `Vol_ED` comes from**, and none
of it exists in Lean.

## 3. Mathlib v4.32 gap analysis

Checked against `.lake/packages/mathlib` at `v4.32.0`. **Read the second column
together with the third**: this table was written when "not in Mathlib" and "not
available to us" were the same statement, and they no longer are — most of these
have since been built in `Arlib/`. What the "no"s now measure is upstreaming debt,
not a blocker.

| Needed | In Mathlib? | In `Arlib/`? |
|---|---|---|
| Prékopa–Leindler | **no** — zero hits | **yes, proved.** 1-D `prekopa_leindler_one_dim` (`Convexity/PrekopaLeindler.lean`) and `ℝⁿ` `prekopa_leindler_pi` (`Convexity/PrekopaLeindlerN.lean`) |
| Brunn–Minkowski | **no** — the only hit is a bibliography line, `Analysis/Convex/Intrinsic.lean:40` | **yes, proved** in sharp form — `brunn_minkowski_sharp` (`Convexity/BrunnSharp.lean`) |
| Logconcavity (as a defined notion) | **no** | **yes** — `LogConcaveOn`/`IsLogConcave` with closure properties (`Convexity/LogConcave.lean`) |
| Isoperimetric inequality | **no** | **yes, proved** unconditionally in `Convexity/IsoBall.lean` (`κ = 2⁻ⁿ/D` for every bounded convex body). See §0(i) for the exponential-constant caveat |
| Conductance | **no** | **yes** — defined, with the Metropolis filter, ball walk and speedy walk as genuine Markov kernels (`MarkovChains/Continuous/Conductance.lean`) |
| Cheeger's inequality | **no** | **yes, both directions**, including the hard one — `cheeger` (`MarkovChains/Continuous/Cheeger.lean`), via the co-area formula, `L¹` isoperimetry and medians, none of which Mathlib has |
| Mixing time / convergence rate | **no** | **yes** — conductance ⇒ geometric `L²` decay ⇒ TV mixing (`MarkovChains/Continuous/MixingFromConductance.lean`, `L2Mixing.lean`), composed end to end in `ConvexBodyMixing.lean`. This is what discharges the sampler's `law_tv` in `Ttc` |
| `ZLogconcaveHypothesis` | n/a | **for the case that matters, yes** — false for general logconcave `f` (machine-checked counterexample), **true** for convex-body indicators: `zLogconcaveHypothesis_indicator` (`Convexity/GaussianCooling/ZLogconcave.lean`). See §0(ii) |
| Total variation distance (as a probability-measure API) | **no** — only signed-measure Jordan decomposition | **yes, proved** — `Probability/TV.lean`; roadmap step 2 below is done, modulo the data-processing inequality |
| Markov kernels, invariance, irreducibility | yes — `Probability/Kernel/{Defs,Invariance,Irreducible}.lean` | — |
| Ergodic theory (qualitative) | yes — `Dynamics/Ergodic/` | — |

**None of this makes Theorem 1.1 closer to formalized.** Every "yes" above is a
*correctness* ingredient, and each carries an exponential constant (§0(i), §0(2));
the `O*(n³)` complexity that is Cousins–Vempala's actual content is untouched.

## 2a. The interface layers (added after the table above)

> **This table is superseded and kept only for the lesson in its "Assumed"
> column.** Every predicate it names — `IsoInput`, `OneDimIso`,
> `MixingFromConductance`, `SpeedyConductance`, `BallWalkMixing`,
> `UniformSampler`, `GaussianSampler` — has since been **deleted**, not
> discharged: `grep` finds no declaration of any of them anywhere in `Arlib/`.
> They were replaced by theorems with the same content and no hypothesis, which is
> what §3's third column now records. `Arlib/Convexity/Isoperimetry.lean` says so
> in its own docstring: "Deliberately **absent**: any `def IsoInput …` /
> `def OneDimIso …` predicate whose name …".

| File | Proved | Assumed (at the time of writing; now none of these exist) |
|---|---|---|
| `Isoperimetry.lean` | logconcavity closure, `π_h`, `d_f`, set distance, scale-invariance, and `separated_speedy`/`iso_speedy` — the specialization §4 consumes | `IsoInput` (`thm:iso`), `OneDimIso` (`lem:1d-iso`) — **both assumed their own conclusion; superseded by `Arlib/Convexity/IsoBall.lean`, which assumes nothing.** See §0(i) |
| `TV.lean` | **everything** — a total-variation API for probability measures (symmetry, triangle, `≤ 1`, `tv = 0 ↔ equal`, the chain bound), warmness and its propagation | nothing |
| `Conductance.lean` | conductance; the Metropolis filter, ball walk and speedy walk as genuine Markov kernels | `MixingFromConductance`, `SpeedyConductance`, `BallWalkMixing`, `UniformSampler`, `GaussianSampler` |
| `GaussianCooling/MedianBoost.lean` and `GaussianCooling/Chernoff.lean` | `lem:exp-bd`, `lem:fn-indep`, and the median boost — at the **`O(log 1/p)`** rate, via Hoeffding (`Chernoff.lean`) | nothing |

Two caveats an auditor should not skip — the first is **why the whole
assume-a-theorem-as-a-predicate approach was abandoned**, and it generalizes:

* **`IsoInput`'s non-vacuity witnesses were all degenerate** (`d ≤ 0`, an empty part, or
  `f ≡ 0`). The predicate was inhabited, but nothing showed it held where its conclusion has
  content. Same status as `LocalizationInput` — that is the honest limit of assuming a
  theorem as a predicate, and it means "not vacuous" is weaker than it sounds.
* ~~**The median boost runs at the Chebyshev rate**, `O(1/p)`, where the paper claims
  `O(log 1/p)`.~~ **Obsolete — withdrawn.** Two things changed. The submodule itself closed
  it in `GaussianCooling/Chernoff.lean`, which this roadmap never mentioned; and Mathlib
  v4.32 now carries the whole sub-Gaussian/Hoeffding stack
  (`Probability.Moments.SubGaussian`), so the port gets the exponential rate for free.
  `Arlib.GaussianCooling.majority_repetitions_suffice`
  (`Arlib/Convexity/GaussianCooling/Estimator.lean`) proves failure `≤ p` for
  `r ≥ log(1/p)/(2(q−½)²)`. The Chebyshev version is kept alongside it because its
  hypotheses are weaker — pairwise rather than full independence.

* **Two corrections to this roadmap's own bookkeeping**, found while porting:
  1. **There is no `Estimator.lean` in the submodule.** The rows above named one; the file
     on disk is `GaussianCooling/MedianBoost.lean`. Its own header still says the material
     "lives in `Estimator.lean`", so it was renamed and the docs were not updated.
  2. **`MedianBoost.lean:11` cites four lemmas that do not exist.** It says the
     "telescoping-product and variance-accounting half — `ratio`, `prod_ratio`,
     `avg_sq_le`, `prod_sq_div_le` — lives in `Estimator.lean`." A grep over every `.lean`
     file in that checkout finds **none of the four**. That half of §5.2 was never written.
     It has now been written fresh, in `Arlib/Convexity/GaussianCooling/Estimator.lean`
     (`integral_prod_eq_prod_integral'`, `integral_prod_sq`, `prod_sq_div_le`,
     `prod_sq_div_le_exp`).

     **Correction to the correction (2026-08-11).** That replacement list was itself
     incomplete, and this roadmap overstated what had been recovered. Of the four cited
     names, `prod_sq_div_le` is genuinely there, and the telescoping pair `ratio` /
     `prod_ratio` exists under other names (`Ttc.CV.prod_range_ratio` / `prod_fin_ratio`,
     `Ttc/Volume/CousinsVempala.lean:361,373`). But **`avg_sq_le` — the averaging lemma —
     is not in the replacement list and did not exist anywhere in the repo.** That is not
     a naming discrepancy: nothing in `Arlib/` or `Ttc/` related the second moment of an
     empirical mean of `k` scores to the second moment of one score, which is precisely
     the bridge from §5.1's per-sample `c = 1 + 2/n` to §5.2's per-phase `1 + κ/m`.
     First proved as `Ttc.CVEst.avgOf_sq_moment_le` (`Ttc/Volume/CVEstimator.lean`), with
     `avgOf_sq_moment_le_budget` giving the sample count `k ≥ (c − 1)·m/κ` that buys the
     budget. **That sample count is the file's cost and is worse than the paper's** — the
     assembly needs `Θ(n·L⁴·log(1/p)/κ³)` samples in total, so `CVEstimator.lean`
     establishes *accuracy*, never `O*(n³)`.

So §4 was never "apply a Mathlib theorem." It was **build the library first**:
continuous-state-space Markov chain theory with quantitative convergence, and
convex-geometry foundations (Prékopa–Leindler at minimum), none of which exists in
Mathlib in any form. **That library has since largely been built** — see §3's
third column — so the sentence to carry forward is not "these are absent" but
"these are ours to maintain, and none of them is upstream."

`ZLogconcave` in particular is no longer blocked by Prékopa–Leindler's absence:
Prékopa–Leindler is proved (1-D and `ℝⁿ`), and for the case the volume algorithm
actually needs — the indicator of a convex body — `zLogconcaveHypothesis_indicator`
proves the hypothesis outright. It remains **false** for general logconcave `f`,
with a machine-checked counterexample; see §0(ii).

## 4. Effort

The submodule spent **1516 Lean lines on 262 tex lines** of §5.1 — a ~6:1 ratio,
on the *easiest* kind of content (real analysis, well supported by Mathlib), and
still left two inputs assumed (three, before Brascamp–Lieb was discharged).

Theorem 1.1 additionally needs ~945 tex lines of materially harder content, most
of it resting on libraries that must be written from scratch. A 6:1 ratio is a
floor, not an estimate; for library-less material the realistic multiplier is
several times that, before counting the Mathlib contributions themselves.

For calibration, single-theorem formalization projects of this shape —
sphere eversion, PFR, the ongoing FLT effort — have run from many person-months
to multiple person-years with teams, and each had more existing library support
than continuous-state mixing times do.

**This is a research programme, not a task.** It should be scoped as its own
project with its own repo, not as a step inside the `Ttc` development.

## 5. Suggested order, if pursued

> **Nothing in this list blocks the `Ttc` capstone any more.** See §0(0): steps
> **3–6** are the Phase-4/Phase-5 stack, and the Monte-Carlo route has already
> removed the volume oracle from `Ttc.ttc_volume_endToEnd`, and hence from
> `Ttc.ttc_volume_final`, without them. Pursue
> them for the `O*(n³)` complexity, which is the thing they still uniquely buy —
> not for correctness, which no longer waits on them. Steps 1–2 remain worth doing
> on their own merits, and step 7 is now the *only* step whose motivation has
> changed materially: instantiating `Ttc.VolumeAlgorithm` with a genuine
> Cousins–Vempala oracle would be a **replacement** of a working construction, not
> the filling of a hole.

1. **Prékopa–Leindler → Mathlib.** Unblocks `ZLogconcave` immediately, which is a
   self-contained win inside the existing submodule and removes one of its two
   remaining assumed inputs. (The third, Brascamp–Lieb, is already discharged —
   see §1.) There is no shortcut: `ZLogconcave` amounts to log-concavity of
   `a ↦ γₙ(√a·K)`, i.e. log-concavity of Gaussian measure, which is a
   Prékopa–Leindler corollary.
2. ~~**A TV-distance API for probability measures → Mathlib.**~~ **Done** — `TV.lean` in
   the submodule proves it (definition, symmetry, triangle, `≤ 1`, `tv = 0 ↔ equal`, the
   chain/union bound over phases, warmness and its propagation). The one missing piece is
   the data-processing inequality `tv (μ.bind κ) (ν.bind κ) ≤ tv μ ν`. Worth upstreaming.
3. **Conductance and a Cheeger-type bound for reversible kernels on general state
   spaces.** The large piece. Independently valuable to Mathlib.
4. **§3 isoperimetry** for logconcave densities, on top of 1–3.
5. **§4** ball walk, warm start, wasted steps, speedy walk.
6. ~~**§5.2** telescoping estimator, Chebyshev, median amplification → Theorem 1.1.~~
   **Done** — and this row was stale twice over. The telescope, the per-ratio Chebyshev
   and the median amplification all live in `Ttc/Volume/CousinsVempala.lean`
   (`prod_range_ratio`, `measure_notMem_relErr_le:333`, `median_relErr_ge:498`); the
   `k`-sample Chebyshev, the error composition across phases, the averaging bridge and
   the assembly are `Ttc/Volume/CVEstimator.lean`. What remains is *not* §5.2: it is
   `hsampler` (a sampler delivering the phase ratios) and `hend` (the last Gaussian
   equals the volume). §0′ supersedes §0 but never came back to correct this section.
7. **Instantiate `Ttc.VolumeAlgorithm`** and rewire `Ttc` (see §6 below).

Steps 1–2 are worth doing regardless of whether the rest is attempted.

## 6. The `Ttc`-side work, which does not depend on any of the above

Independent of the formalization above, `Ttc` can be brought to the point where
Theorem 1.1 is the *only* thing left to supply. **Every bullet in this section is
now `Done`, and the section has been overtaken**: rather than stopping at "Theorem
1.1 is the only thing left", the development supplied a *different*
`VolumeAlgorithm` (§0(0)) and removed the binder outright. Theorem 1.1 is
consequently not "the only thing left to supply" — it is not needed for
correctness at all, only for complexity.

- **Done** — `Ttc.VolumeAlgorithm` (`Ttc/Volume/Oracle.lean`) states Theorem 1.1
  in Lean, with a non-vacuity witness (`VolumeAlgorithm.exact`) and the halves the
  Invariant consumes (`upper`, `lower`).
- **Done** — the **rounding bridge**. Theorem 1.1 needs `K ⊇ B(0,1)`; `TtcProb`
  supplies `ball_subset : Metric.ball (cen i) gammaHat ⊆ region M i`
  (`Ttc/Volume/Oracle.lean`). `Ttc.roundBody` is the change of
  variable `y ↦ γ̂⁻¹·(y − cen i)`; `ball_subset_roundBody`, `convex_roundBody`
  and `volume_roundBody_ne_top` discharge Theorem 1.1's three hypotheses for its
  image, and `VolumeAlgorithm.of_ball` transports the `(1 ± ε)` conclusion back
  by `γ̂ⁿ`. Every hypothesis comes from a field `TtcProb` already has, so **no new
  assumption is introduced**. Relative error is scale-invariant
  (`mem_relErr_smul`), so the bridge costs nothing in accuracy.
- **Done** — `TtcProb.volED_hi` is gone as a field. `Ttc.TtcProb` now carries
  `volAlg : VolumeAlgorithm n` (Theorem 1.1 itself), `volCoins` (the coins the
  `m` calls consumed), `volED_eq` (that `vol` *is* those calls' output, rescaled
  by the rounding bridge) and `volCoins_good` (that the coins landed in the good
  event). `volED_hi` came back as a **theorem** with its statement unchanged, so
  nothing downstream moved, and `volED_lo` came free — Theorem 1.1 is two-sided
  where the old field was not.

- **Done** — the union bound the paper omits (README finding 13).
  `Ttc.measure_volGood_ge` (`Ttc/Volume/Bridge.lean`) charges the `m` calls to
  `m·δ'`, and `TtcProb.volGood_prob_budget` instantiates it at
  `δ' = δ/(4m)` for `1 − δ/4`. That lands inside the slot the arithmetic already
  reserved: `numlattice_failure_le` (`Process/SketchProcess.lean:246`) carries
  `hvol : volSum ≤ δ/2`, and `Params.vol_failure_eq` (`Process/Sketch.lean:159`)
  — previously dead code — is now what proves the fit. `measure_volGood_ge`
  needed one addition to the interface: `VolumeAlgorithm.est_meas`, since without
  measurability the *complement* of the good event has no upper bound.

- **Done** — integrating `Vol_ED`'s randomness into the headline. This bullet used
  to read "to do, and harder than it looks"; it is closed.
  `Ttc.ttc_volume_monteCarlo` (`Ttc/Exec/VolDischarge.lean`) concludes
  `1 − δ − δ/4` over the **joint** randomness: the conclusion is an
  `∫⁻ c … ∂(Ttc.MonteCarlo.coins n)`, so `volCoins` is integrated out rather than
  fixed at a good value, and `volCoins_good` is averaged out against
  `Ttc.mcGood` at probability `≥ 1 − δ/4` (`Ttc.measure_mcGood_ge`).

  *How the obstacle below was avoided.* It was not solved — it was **routed
  around**. The refactor described next (making `vol : Ω → Cube A → ℝ`) was never
  done, and neither was the recommended `TtcProb` split. Instead the work moved off
  `TtcProb` entirely and onto the binder-form statement `Ttc.ttc_volume`, where
  "identical except in one field" is expressible for free because the fields are
  `∀`-binders: the coin is simply another binder to integrate over. That is the
  practical argument for the `Exec/Endgoal.lean` restatement, and it is worth
  recording because the obstacle as stated below is real and still unsolved *for
  `TtcProb`*.

  Net effect on the binder list: `Ttc.ttc_volume`'s **36** explicit binders become
  **31**, with one binder added (`hlen`, that the main loop runs at most `P.m`
  times). Above `δ = 4/5` the bound `1 − δ − δ/4` is not positive and the statement
  is uninformative; that corner is not patched here.
  `Ttc.ttc_volume_clean` (`Ttc/Exec/Budget.lean`; `ttc_volume_endToEnd_delta` is a
  legacy `alias` for it) restates the budget in the user's `δ`, and
  `Ttc.ttc_volume_final` (`Ttc/Exec/Final.lean`) does the same with the polytope
  description also removed — **26** explicit binders, all of them inputs. Both do it
  by *repricing* at `δ₀ = 4δ/5`, at a `5/4` increase in Monte-Carlo samples and an
  additive `O(1/ε²)` increase in `Thresh`.

  *The obstacle, as it stood — still accurate about `TtcProb`.*
  `TtcProb.vol : Cube A → ℝ` is deterministic **by
  construction**: `oracle_eq : ∀ ω, O ω = trajOracles ptE_inj vol cover memPt
  (toTraj ω)` (`Model/ProblemSetting.lean`) binds `vol` *outside* the `ω`, so
  the entire pathwise coupling of `Coupling/{Family,Run,Transfer}.lean` is built
  on the volume estimates being fixed reals rather than random variables. Making
  `Vol_ED` randomized means `vol : Ω → Cube A → ℝ`, which changes `trajOracles`
  and every lemma downstream of it — a refactor of the load-bearing construction,
  not a field swap.

  The cheaper alternative is to leave `vol` deterministic and compose the two
  statements on a product space: "at a good `volCoins`, the estimate is good with
  probability `1 − δ`" (`TtcProb.volume_estimate`, what exists today) together
  with "`volCoins` is good with probability `1 − δ/4`"
  (`TtcProb.volGood_prob_budget`, which now exists too). Both halves are in
  place; what is missing is a way to say "the same run with a different
  `volCoins`" — a bundled `TtcProb` cannot express "identical except in one
  field", so this needs either a family `V.Ω → TtcProb A n` with the shared data
  factored out, or `TtcProb` split into a `volCoins`-free part and a wrapper.
  That is the recommended route, and it is the last step.
