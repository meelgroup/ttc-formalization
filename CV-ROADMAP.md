# Formalizing Cousins–Vempala Theorem 1.1 — what it would take

Scope note for `Ttc`: `Ttc.TtcProb` carries `volAlg : VolumeAlgorithm n`, an
assumption that `Vol_ED` is accurate. (An older revision of this line named
`Ttc.TtcProb.volED_hi`; that is **no longer a field** — it came back as a theorem,
see §6.) The intended discharge was Cousins–Vempala Theorem 1.1
(`gaussian-cooling-vempala/vol3_journal.tex:144`):

> There is an algorithm that, for any `ε > 0`, `p > 0` and convex body `K` in `ℝⁿ`
> that contains the unit ball and has `E_K(‖X‖²) = O(n)`, with probability `1 − p`,
> approximates the volume of `K` within relative error `ε`, with complexity
> `O*(n³)` in the membership oracle model.

That theorem is **not** formalized in the `gaussian-cooling-vempala` submodule,
and this file records honestly what closing the gap involves. The statement is
now written in Lean as `Ttc.VolumeAlgorithm` (`Ttc/Model/ProblemSetting.lean`) so that
a future formalization plugs in without touching the rest of `Ttc`.

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

`gaussian-cooling-vempala/lean` is 3904 lines. §5.1 — the accelerated-cooling variance
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

The §5.2 proof ends at `:1588–1604`: the product estimator, a `4/5` success
probability, an `O(1)`-restart argument converting *expected* ball-walk steps
into a fixed count, `lem:accuracy`, and finally *"boost this probability of
failure to `1−p` by … repeating the algorithm `log 1/p` times and returning the
median."* **That last clause is where the `δ'` of `Vol_ED` comes from**, and none
of it exists in Lean.

## 3. Mathlib v4.32 gap analysis

Checked against `.lake/packages/mathlib` at `v4.32.0`:

| Needed | In Mathlib? |
|---|---|
| Prékopa–Leindler | **no** — zero hits |
| Brunn–Minkowski | **no** — the only hit is a bibliography line, `Analysis/Convex/Intrinsic.lean:40` |
| Logconcavity (as a defined notion) | **no** |
| Isoperimetric inequality | **no** in Mathlib — but *proved here*, unconditionally, in `Arlib/Convexity/IsoBall.lean` (`κ = 2⁻ⁿ/D` for every bounded convex body). See §0(i) for the exponential-constant caveat |
| Conductance | **no** |
| Mixing time / convergence rate | **no** |
| Total variation distance (as a probability-measure API) | **no** — only signed-measure Jordan decomposition. *Now supplied by the submodule's `TV.lean`, proved; roadmap step 2 below is done, modulo the data-processing inequality* |
| Markov kernels, invariance, irreducibility | yes — `Probability/Kernel/{Defs,Invariance,Irreducible}.lean` |
| Ergodic theory (qualitative) | yes — `Dynamics/Ergodic/` |

## 2a. The interface layers (added after the table above)

| File | Proved | Assumed |
|---|---|---|
| `Isoperimetry.lean` | logconcavity closure, `π_h`, `d_f`, set distance, scale-invariance, and `separated_speedy`/`iso_speedy` — the specialization §4 consumes | `IsoInput` (`thm:iso`), `OneDimIso` (`lem:1d-iso`) — **both assume their own conclusion; superseded by `Arlib/Convexity/IsoBall.lean`, which assumes nothing.** See §0(i) |
| `TV.lean` | **everything** — a total-variation API for probability measures (symmetry, triangle, `≤ 1`, `tv = 0 ↔ equal`, the chain bound), warmness and its propagation | nothing |
| `Conductance.lean` | conductance; the Metropolis filter, ball walk and speedy walk as genuine Markov kernels | `MixingFromConductance`, `SpeedyConductance`, `BallWalkMixing`, `UniformSampler`, `GaussianSampler` |
| `GaussianCooling/MedianBoost.lean` and `GaussianCooling/Chernoff.lean` | `lem:exp-bd`, `lem:fn-indep`, and the median boost — at the **`O(log 1/p)`** rate, via Hoeffding (`Chernoff.lean`) | nothing |

Two caveats an auditor should not skip:

* **`IsoInput`'s non-vacuity witnesses are all degenerate** (`d ≤ 0`, an empty part, or
  `f ≡ 0`). The predicate is inhabited, but nothing shows it holds where its conclusion has
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

So §4 is not "apply a Mathlib theorem." It is **build the library first**:
continuous-state-space Markov chain theory with quantitative convergence, which
does not exist in Mathlib in any form. §3 likewise needs convex-geometry
foundations (Prékopa–Leindler at minimum) that are absent.

Note that Prékopa–Leindler's absence also means `ZLogconcave` — one of the
submodule's two remaining assumed inputs — cannot be discharged today either, as its own
README already states.

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
6. **§5.2** telescoping estimator, Chebyshev, median amplification → Theorem 1.1.
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

- **Done** — `Ttc.VolumeAlgorithm` (`Ttc/Model/ProblemSetting.lean`) states Theorem 1.1
  in Lean, with a non-vacuity witness (`VolumeAlgorithm.exact`) and the halves the
  Invariant consumes (`upper`, `lower`).
- **Done** — the **rounding bridge**. Theorem 1.1 needs `K ⊇ B(0,1)`; `TtcProb`
  supplies `ball_subset : Metric.ball (cen i) gammaHat ⊆ region M i`
  (`Ttc/Model/ProblemSetting.lean:114`). `Ttc.roundBody` is the change of
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
