# Formalizing Cousins–Vempala Theorem 1.1 — what it would take

Scope note for `Ttc`: `Ttc.TtcProb.volED_hi` assumes `Vol_ED`'s accuracy. The
intended discharge is Cousins–Vempala Theorem 1.1
(`gaussian-cooling-vempala/vol3_journal.tex:144`):

> There is an algorithm that, for any `ε > 0`, `p > 0` and convex body `K` in `ℝⁿ`
> that contains the unit ball and has `E_K(‖X‖²) = O(n)`, with probability `1 − p`,
> approximates the volume of `K` within relative error `ε`, with complexity
> `O*(n³)` in the membership oracle model.

That theorem is **not** formalized in the `gaussian-cooling-vempala` submodule,
and this file records honestly what closing the gap involves. The statement is
now written in Lean as `Ttc.VolumeAlgorithm` (`Ttc/Model/VolOracle.lean`) so that
a future formalization plugs in without touching the rest of `Ttc`.

---

## 1. What the submodule has today

`gaussian-cooling-vempala/lean` is 1516 lines proving §5.1 of the paper — the
accelerated-cooling variance bound — end to end:

| Result | File | Paper |
|---|---|---|
| `expect_ratio` — `E[Y] = G(b)/G(a)` | `Ratio.lean:94` | eq. at `:1078` |
| `expect_ratio_sq` — `E[Y²] = G(c)/G(a)` | `Ratio.lean:110` | eq. at `:1086` |
| `variance_ratio` | `Ratio.lean:135` | §5.1 |
| `lc_variance_bound` — `≤ exp(2R²α²/σ²)` | `Main.lean:52` | Lemma 5.8 |
| `fast_var_bound` — `≤ 1 + σ²/(C²n)` | `Main.lean:74` | Claim 5.11 |
| `fixed_var_bound` — `≤ 1 + 2/n` | `FixedRate.lean` | Lemma 5.10 |
| `filter_accept_ge`, `warm_start_accelerated` | `Sampling.lean` | Lemmas 4.2, 4.8 |

Three cited results enter as hypotheses rather than theorems: `BrascampLieb`
(`VDeriv.lean:100`), `LocalizationInput` (`Localization.lean:178`),
`ZLogconcave` (`FixedRate.lean:110`).

**These are lemmas used inside the proof of Theorem 1.1, not Theorem 1.1.**
Nothing in the tree mentions the Lebesgue volume of the body, a success
probability, or an estimator. Greps for `∏`/`Finset.prod`, `chebyshev`, `median`,
`IndepFun` over that tree all return empty.

## 2. What is missing, by paper section

Theorem 1.1's proof runs through §3 (Isoperimetry), §4 (Sampling), and §5.2
(Proof of the main theorem). None of it is formalized.

| Paper | tex lines | Content | Blocker |
|---|---|---|---|
| §3 Isoperimetry (`:404–508`) | ~105 | isoperimetric inequality for logconcave densities | no logconcavity or isoperimetry in Mathlib |
| §4.1 Conductance (`:514–746`) | ~230 | conductance of the ball walk, `thm:ball-walk` | **no conductance, no mixing time, no continuous-state Markov chain convergence in Mathlib** |
| §4.2 Warm start (`:747–826`) | ~80 | `M(Q₀,Q)` warmness propagation | needs §4.1 |
| §4.3 Wasted steps (`:827–937`) | ~110 | speedy walk accounting | needs §4.1 |
| §4.4 Speedy→target (`:938–1002`) | ~65 | mapping speedy to target distribution | needs §4.1 |
| §4.5 Sampling theorems (`:1003–1053`) | ~50 | `thm:sampling`, `thm:gauss-sampling` | needs §4.1–4.4 |
| §5.2 Main theorem (`:1316–1611`) | ~295 | telescoping `W₁…W_m`, accuracy, median boost | needs §5.1 + §4 |

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
| Isoperimetric inequality | **no** |
| Conductance | **no** |
| Mixing time / convergence rate | **no** |
| Total variation distance (as a probability-measure API) | **no** — only signed-measure Jordan decomposition |
| Markov kernels, invariance, irreducibility | yes — `Probability/Kernel/{Defs,Invariance,Irreducible}.lean` |
| Ergodic theory (qualitative) | yes — `Dynamics/Ergodic/` |

So §4 is not "apply a Mathlib theorem." It is **build the library first**:
continuous-state-space Markov chain theory with quantitative convergence, which
does not exist in Mathlib in any form. §3 likewise needs convex-geometry
foundations (Prékopa–Leindler at minimum) that are absent.

Note that Prékopa–Leindler's absence also means `ZLogconcave` — one of the
submodule's three assumed inputs — cannot be discharged today either, as its own
README already states.

## 4. Effort

The submodule spent **1516 Lean lines on 262 tex lines** of §5.1 — a ~6:1 ratio,
on the *easiest* kind of content (real analysis, well supported by Mathlib), and
still left three inputs assumed.

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

1. **Prékopa–Leindler → Mathlib.** Unblocks `ZLogconcave` immediately, which is a
   self-contained win inside the existing submodule and removes one of its three
   assumed inputs.
2. **A TV-distance API for probability measures → Mathlib.** Prerequisite for
   anything quantitative about mixing; small and independently useful.
3. **Conductance and a Cheeger-type bound for reversible kernels on general state
   spaces.** The large piece. Independently valuable to Mathlib.
4. **§3 isoperimetry** for logconcave densities, on top of 1–3.
5. **§4** ball walk, warm start, wasted steps, speedy walk.
6. **§5.2** telescoping estimator, Chebyshev, median amplification → Theorem 1.1.
7. **Instantiate `Ttc.VolumeAlgorithm`** and rewire `Ttc` (see §6 below).

Steps 1–2 are worth doing regardless of whether the rest is attempted.

## 6. The `Ttc`-side work, which does not depend on any of the above

Independent of the formalization above, `Ttc` can be brought to the point where
Theorem 1.1 is the *only* thing left to supply:

- **Done** — `Ttc.VolumeAlgorithm` (`Ttc/Model/VolOracle.lean`) states Theorem 1.1
  in Lean, with a non-vacuity witness (`VolumeAlgorithm.exact`) and the halves the
  Invariant consumes (`upper`, `lower`).
- **To do** — replace `TtcProb.volED_hi` by a `VolumeAlgorithm` field. This
  changes the field from a *deterministic* bound (which asserts `Vol_ED` never
  fails, strictly stronger than the paper) to a `1 − δ'` bound, and requires
  `Model/Theorem.lean`'s union bound to spend the `δ/2` that
  `Params.vol_failure_eq` (`Ttc/Process/Sketch.lean:159`) already computes and
  currently leaves unused.
- **To do** — the **rounding bridge**. Theorem 1.1 needs `K ⊇ B(0,1)`; `TtcProb`
  supplies `ball_subset : Metric.ball (cen i) gammaHat ⊆ region M i`
  (`Ttc/Model/ProblemSetting.lean:112`). Scaling by `γ̂` and translating by
  `cen i` bridges this, using `Measure.addHaar_smul` and translation invariance;
  relative error is scale-invariant, so the `(1 ± ε)` conclusion transports.
  This is ordinary Mathlib work and is the natural next increment.
