# End-to-end formalisation of TTC by discharging its oracles

> **Superseded as the live plan (2026-08-17) by [`RUNTIME-ENDGAME.md`](RUNTIME-ENDGAME.md).**
> Phases 0–5 below are done or dead, and the accuracy half of `thm:volumettc` is
> finished. The remaining work is the runtime half, and it is scoped there. Keep this
> file for history.

## THE ENDGOAL — read this first

Everything below serves one target: **the capstone must take the algorithm's own
inputs.** The template is
`/home/devel/Documents/nfalean/ApproxNFA/Model/Theorem.lean:99`
(`ApproxNFA.approxNFA_countNFA`), and it is to be followed *exactly*:

```lean
theorem ttc_volume (M : A → Set (Space n)) (φ : BForm A) (ε δ : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    <only genuine input conditions on (M, φ)> :
    (1 - δ ≤ (ttcExec M φ ε δ).P.Pr
       (fun ω => pseudocodeOutput M φ ε δ ω ∈ relErr ε (volSol M φ)))
    ∧ <the runtime half>
```

Contrast with what we have today:

```lean
theorem Ttc.TtcProb.volume_estimate (T : TtcProb A n) :
    1 - T.δ ≤ (T.μ {ω | ttcOutput T.P T.O T.toDNF T.ρ T.φ ω
                        ∈ relErr T.ε (volSol T.M T.φ)}).toReal
```

`ε`, `δ`, `φ`, the probability space and the parameter block are all read *out of a
59-field structure that also assumes both oracles work*. The seven gaps:

1. **Inputs are the algorithm's inputs.** `TTC(F, ε, δ)` (`alg:ttc` line 1) ⟹ the
   capstone quantifies over `φ, ε, δ`, not over a `TtcProb` that presupposes them.
2. **No hypothesis bundle is quantified over.** nfalean's only hypotheses are the
   parameter range; its README says outright "there are **no hypotheses on `A`**".
   Each of our 59 fields must become either a construction or a *named, visible*
   input hypothesis. A field is an assumption a reader cannot see from the statement.
3. **The probability space is constructed.** `countNFAExec A n ε δ`
   (`Algorithm/Faithful.lean:415`) is built from the inputs; our `Ω, mΩ, μ, isProb`
   are fields.
4. **The parameters are computed.** `countNFAParams A n ε δ` (`:396`) computes the
   whole block from exactly the inputs; our `P : Params` and `ρ` are free fields, so
   `alg:ttc` lines 12–14 are currently assumed rather than evaluated.
5. **`Model/ProblemSetting.lean` shrinks to the problem.** nfalean's is **53 lines**
   — `nfaLangCount`, `relErr`, one Mathlib cross-check, *no structure*. Ours must
   reduce to `volSol` + `relErr` + cross-check; `TtcProb` leaves `Model/`.
6. **The proof is a one-liner.** Today's `volume_estimate` becomes the internal
   abstract theorem; `ttc_volume` applies it to the constructed `ttcExec`.
7. **Both halves in one conjunction**, accuracy and runtime, both over the
   transcription.

**Why the oracle work comes first, and is not optional:** step 2 is impossible
while `samp_unif`, `volAlg`, `volCoins_good`, `law_eq`, `oracle_eq` are fields — a
*constructed* `ttcExec` has no way to supply them, so they must already be theorems.
Discharging the oracles is the precondition for the restatement, not a parallel
track.

## STATUS

| Phase | State |
| --- | --- |
| **0 — `Model/` back to four files** | **done.** `Model/VolOracle.lean` deleted; proofs → `Ttc/Volume/Bridge.lean`. Axioms unchanged. |
| **1 — ArLib staging lib** | **done.** Second Lake lib, four area roots wired, `grep -rn "^import Ttc" Arlib/` empty. |
| **2 — KV97** | **COMPLETE for the agreed scope.** Theorem 2 proved unconditionally (`theorem2_of_body`); `cor:linf` proved (`cor_linf_tuned`, with finding §4g); Lemma 1 proved at `9/(20e)`, better than the paper's `1/8` (§4h); Theorem 1's correctness content is those two. Running time out of scope. |
| 3 — discharge sampling oracle | **KV97 is now LOAD-BEARING** (dependency walk re-run and verified by the parent, not relayed): `Arlib.KV97.theorem2 : true`, `Ttc.almostUniform_of_kv97_density : true`, `Ttc.escape_of_mem_body : true`. `samp_unif` is **no longer a field** — it is a theorem in `Ttc/Sampler/Bridge.lean` with a byte-identical statement, so `theta_lo`/`theta_hi`/`theta_window_cube` and `Coupling/Transfer` are untouched. The escape mass is *derived*, not assumed. What replaces `samp_unif` is the field `sampler : KV97Sampler …` (**14 fields**, down from 18, and mostly *descriptive* — which polytope, which normalisation — plus one quantitative hypothesis `density_au` on the **continuous** draw at `ε'/4`). The four enumeration fields `idx`/`fintypeIdx`/`nonemptyIdx`/`enum` were **proved redundant and removed**: they are derived from `dilate_intLattice_finite`/`_nonempty`, with `sampD_eq`'s rejection sum restated as a `finsum` so no `Fintype` is needed at all. `dilate_eq` was also weakened from an equality to the `⊆` the proof actually uses. |
| 4 — ball-walk mixing stack | **THE ROUTE OF RECORD IS DEAD — see below.** Proved: 1-D and ℝⁿ Prékopa–Leindler, Brunn–Minkowski, Prékopa/Borell, log-concave marginals and convolutions, Brunn's theorem, conductance ⟹ explicit mixing time, the ball walk as a genuine reversible Markov kernel, and Cheeger's inequality in **both** directions. **Cheeger's hard direction is now proved** — `Arlib.MarkovChains.sq_conductance_div_two_le_spectralGap` (`Cheeger.lean:1584`), packaged with the easy direction as `Arlib.MarkovChains.cheeger` (`:1593`); the row above claiming otherwise was stale. Isoperimetry is proved at the **weak** constant for the uniform measure *and* for the Gaussian-restricted measure (`GaussianCooling/Unblock.lean:597` `exists_uniformOn_gaussian_iso_of_convex`, in the exact shape `conductance_ballWalk_ge` consumes); the **sharp** constant remains open, and is what the paper's `O*(n³)` needs. ~~**The single unproved object on the critical path is a Markov kernel stationary for the Gaussian-restricted density `∝ 1_K·e^{−‖x‖²/(2s)}`** — the Metropolis filter of the paper's Figure 2 is not built anywhere~~ — **STALE, corrected 2026-08-12.** The kernel **is** built: `Arlib.MarkovChains.metropolisGaussian` (`MetropolisGaussian.lean:444`), with `Arlib.MarkovChains.isReversible_metropolisGaussian` (`:586`) proving it reversible for exactly `Arlib.uniformOn (volume.withDensity (gaussianWeight σ²)) K`, and `Arlib.MarkovChains.conductance_metropolisGaussian_sharp_ge` (`MetropolisConductanceSharp.lean:431`) giving it `Φ ≥ δ·log 2/(640·σ·n)` at a **constant** acceptance floor `a = e^{−(2Rδ+δ²)/(2σ²)}`, which is `≥ e^{−1/8} ≈ 0.88` in the Cousins–Vempala regime — not the exponentially small constant of `conductance_metropolisGaussian_ge`. **What this does *not* upgrade, and the row's verdict is unchanged:** `hiso` (CV's `thm:iso`) is still an explicit hypothesis of that theorem and is unproved in this repository, and so is the local-conductance floor `hfloor`/`hell`, which is a real restriction on `K` and is **not** removable — `hoverlap` is outright false without it. It is not a mixing-time bound and may not be quoted as one. The docstring at `GaussianCooling/Unblock.lean:77-83` still asserts "no such kernel is built in this library" and is recorded as stale in `AUDIT.md` §0d. (`BallWalk.lean:24` is **not** stale: it says the filter is not applied *in that file*, which is correct — it is the unweighted ball walk.) **Second correction, 2026-08-12: "the route of record is dead" is now too strong for the *uniform* target.** `Arlib.MarkovChains.mixesWithin_lazy_speedyWalk_uniformOn_sharp` (`UniformSamplerSharp.lean`) is a uniform sampler on a convex body at `O(n⁴·D²·log(1+D)/ρ²)` steps with **no** isoperimetry, warmness, smoothness or comparability binder — all three inputs of `mixesWithin_lazy_speedyWalk_uniformOn` are discharged (`hiso` at the dimension-free `κ = 1/(8R)`, `Convexity/LogConcaveIso.lean`; `hwarm` from the samplable unit-ball start, `WarmEllProb.lean`; `hsmooth` from `EllFloor.lean`/`SmoothSqrt.lean`), and `le_conductanceS_lazy_ballWalk_of_ball_subset` (`BallWalkTransfer.lean:479`) gives the **ball** walk a polynomial `s`-conductance on the exact kernel `Ttc.ballWalkLaw` iterates. **What is unchanged:** CV's `thm:iso` sharp constant and `hphase_mean`/`hphase_var` are untouched — ~~none of it targets the *Gaussian-restricted* measure~~ **corrected the same day**: `Arlib.MarkovChains.speedyMetropolisGaussian` (`Continuous/SpeedyGaussian.lean`) *is* a Markov kernel reversible for the density `ℓ·e^{−‖x‖²/(2s)}` on `K` (`isReversible_speedyMetropolisGaussian`, needing only `MeasurableSet K`), with a witness proving `0 < P₀({0}ᶜ) < 1` so the filter demonstrably rejects. But it is **a kernel and a reversibility proof only** — no conductance, no mixing, no gap; `AUDIT.md` §0g lists the three obligations (`hoverlap` with an acceptance floor, the `hpi` density bridge, `hiso` wiring) that stand between it and any bound; the cost is polynomial in `1/ρ`, not `log(1/ρ)`, so `README.md` §19's fatal bias finding stands verbatim; and **no `Ttc/` declaration consumes any of it** — see `AUDIT.md` §0g. |
| 5 — discharge volume oracle | **CV §5.1 ported in full** (`Arlib/Convexity/GaussianCooling/Variance.lean`, 63 declarations, Brascamp–Lieb a genuine port). **`ZLogconcaveHypothesis` is now DISCHARGED** for `f = c·1_K` with `K` convex and measurable (`Arlib/Convexity/GaussianCooling/ZLogconcave.lean`), giving unconditional `fixed_var_bound_indicator` / `fixed_var_bound_ratio_indicator` — which is the instance a volume oracle for a convex body actually needs. **But it is FALSE for general log-concave `f`**: at `n = 1`, `f x = e^{-x}`, `log z` is strictly convex for `A < 2/3` and the hypothesis fails by a factor ≈ 1.93. The obstruction is structural — the proof needs `(A,y) ↦ f(y/A)` jointly log-concave, and a 0-homogeneous convex function is constant — so up to a constant factor, indicators of convex sets are *exactly* the `f` that work. `Variance.lean:1287`'s docstring must not be read as claiming the general case. One assumed input remains: `LocalizationHypothesis`. `Estimator` runs at `O(log 1/p)`; the roadmap's `O(1/p)` caveat is withdrawn. |

**Both oracles are now discharged, by construction, and the plan above predates
that.** `Ttc.VolumeAlgorithm.monteCarlo` (`Ttc/Volume/MonteCarlo.lean`) is a
`VolumeAlgorithm n` with no hypotheses, and `Ttc.kv97SamplerOfBody`
(`Ttc/Sampler/Construct.lean`) is a `KV97Sampler` whose `law_tv` field is a
*theorem*, proved from the ball walk's mixing time. `Ttc.ttc_volume_final`
(`Ttc/Exec/Final.lean`) binds **no oracle of any kind**. What is left of this
section's account is the two things that did *not* change:

* `volAlg`, `volCoins_good` and `gen_mem` are still **fields of `Ttc.TtcProb`** —
  the bundle-level theorem still quantifies over them; it is the input-level
  capstones that construct them away.
* **Both constructions are exponential in `n`** (Monte-Carlo sample count, ball-walk
  step count). "Discharged" means unconditional, not efficient; `thm:runtime` is
  out of scope throughout. Quoting the first half without the second overstates the
  result.

The sampling-oracle reduction recorded above still holds and is what made this
possible: `samp_unif` moved from *field* to *theorem*, and the whole discrete
`(1 ± ε')` claim — rounding loss, rejection loss, escape tail, union bound over
facets — is proved rather than assumed.

> **Honest caveat on the exchange.** `samp_unif` (a quantitative `(1±ε')` bound on
> a *discrete* law) was traded for `density_au` (a quantitative `(1±ε'/4)` bound on
> a *continuous* density) plus structural description. That is the right direction
> — the continuous guarantee is the one the literature actually supplies — but the
> two bundles are **incomparable**, not a strict logical weakening, and an
> implementer must now hit a four-times-tighter target on the continuous side.

## ⚠ The TV → pointwise gap is provably unbridgeable by mixing

This invalidates the Phase 4 plan as written, and it is machine-checked
(`Arlib/MarkovChains/Continuous/PointwiseMixing.lean`, axiom-clean):

* `not_exists_pointwiseClose_of_tvLe` — for **every** TV tolerance `δ ≠ 0` there is
  **no** `ε` whatsoever making `TVLe μ ν δ → PointwiseClose μ ν ε`.
* `exists_tvLe_not_pointwiseClose` — even restricted to `μ ≪ ν`, two probability
  measures at TV `≤ δ` can have density ratio `1/δ`. So the failure is not an
  artefact of demanding a density; it is the *ratio* that TV does not control.
* `not_uniformMinorisation_of_unreachable` + ball-walk locality — one step of
  `ballWalk K δ` from `x` is supported in `ball x δ ∪ {x}`, so for any `K` of
  diameter `> δ` **no uniform minorisation constant exists**. This is *locality*,
  a separate and worse obstruction than the `ℓ(x) → 0` boundary degeneracy that
  Cousins–Vempala's speedy walk repairs. Restricting to speedy points fixes the
  holding probability and does **not** fix locality.

Since AUDIT-KV97 §4b establishes that Theorem 2 needs a **pointwise** hypothesis,
"run the ball walk until it mixes in TV" cannot deliver it. Three candidate
replacement routes are under evaluation (local Harnack/smoothing; rejection
against an exactly-known proposal, which is what the box witness already does;
or re-deriving Thm 2 for an additive error, which §4b argues is impossible).

### Findings so far (all in `AUDIT-KV97.md` §4)

* **§4a — the exponent is wrong by a factor of 2**, settled by proof: the paper's inflation `κ = c + √(2 log r)` yields `exp(−c²/2)`, not the printed `2e^{−c²}`. `Defs.lean` was corrected to match what is provable.
* **§4b — `ε` is stated relatively but derived additively.** A total-variation hypothesis cannot support the corollary; `theorem2` therefore takes a **pointwise** `(1±ε)` density hypothesis. Consequence: the continuous sampler must be almost-uniform pointwise, not merely mixed — strictly harder than the roadmap assumed.
* **§4c — Theorem 2's escape mass** was an explicit hypothesis; **now discharged**, so `Arlib.KV97.theorem2_of_body` is unconditional.
* **§4g — `cor:linf`'s upper bound is FALSE for `ε > (7−√33)/2 ≈ 0.628`**, a direct consequence of §4b. At `ε = 1` the true constant is `20/9 = 2.22…` against the paper's `2` (machine-checked). The paper's constant is recovered verbatim for `ε ≤ 5/8`. **`TTC` uses `ε' = ε/12 ≤ 1/12`, so the main result is unaffected** — what is wrong is the generality of the printed corollary, not the instance used here.
* **1-D Prékopa–Leindler needs a normalisation hypothesis** the standard statement omits; there is a counterexample (`f = 0`, `g = 1_[0,1]`). Eliminated in the final theorem by rescaling.
* **`Ttc/Findings/CubeLattice.lean` seeded every cube-formula with a spurious tautology** — `a ∨ ¬a` at a caller-supplied atom `a`, justified by a docstring claiming "`Ttc.BForm` has no `true` constructor". `BForm.tt` **does** exist (`Model/Prelude.lean`), so the seed was unnecessary — and not merely cosmetic: it made those lemmas inapplicable when the atom type is empty, and forced callers to invent an atom. **Resolved**: the seed parameter is gone and `Ttc.lattice_of_cube` is correspondingly stronger.

### Known duplication / debt

* `Arlib/Lattice/Rounding/` duplicated `Ttc/Rounding/`; `Tent.lean` is now a re-export (`export Arlib.Lattice.Rounding (...)`, definitionally identical), the rest still duplicated because `Ttc/Rounding/ProdKernel.lean` imports `Ttc.Rounding.Cl` → `Ttc.Model.Prelude`. Map in `Ttc/Rounding/ArlibBridge.lean`.
* `Warmness.lean` and `MixingFromConductance.lean` were written in parallel and both defined `MixesWithin`; merged onto Warmness's canonical chain layer.
* **`Ttc/Lattice/PerCube.lean` duplicates `Ttc/Findings/CubeLattice.lean`.** The per-cube `lem:lattice` already existed as `Ttc.lattice_of_cube`; it was re-derived because a stale report claimed it did not, and the claim was relayed without checking. The new one is kept because it is seed-atom-free (above) and because its `TtcProb`-level form (`lattice_cube_lo`/`hi`) matches `Ttc/Sampler/Contract.lean`'s hypothesis shape exactly. The helper layer is namespaced `Ttc.PosCube` so both coexist; `CubeLattice.lean` should be re-based onto it and its duplicate helpers deleted.

---

## Context

`kr-25-ssm/lean` (the `Ttc` library, ~32k lines across 109 files, `sorry`-free,
axioms `[propext, Classical.choice, Quot.sound]`) proves `thm:volumettc`:

```lean
theorem Ttc.TtcProb.volume_estimate (T : TtcProb A n) :
    1 - T.δ ≤ (T.μ {ω | ttcOutput T.P T.O T.toDNF T.ρ T.φ ω
                        ∈ relErr T.ε (volSol T.M T.φ)}).toReal
```

Everything *quantitative* is derived. What this theorem still **assumes** is a
description of the two external oracles, carried as fields of `Ttc.TtcProb` (since
moved out of `Model/`, to `Ttc/TtcProb.lean`):

| Oracle | `alg:ttc` | Assumed as |
|---|---|---|
| `GenerateSamples(P(cᵢ), Nᵢ, ρ, ε', δ')` | line 43 | `sampler : KV97Sampler …` + `gen_mem` (`theta_lo`/`theta_hi` are now theorems) |
| `Vol_ED(P(cᵢ), ε', δ')` | line 24 | `volAlg : VolumeAlgorithm n` (Cousins–Vempala Thm 1.1) + `volCoins_good` |

The goal was to **remove those assumptions** — sampling oracle first, then volume
oracle — so the headline rests only on Mathlib. Both reduce to the *same* missing
object: a continuous almost-uniform sampler on a convex body, so one stack
discharges both. **That goal has been met at the input level** (see the STATUS
note above): the capstone chain ending in `Ttc.ttc_volume_final` constructs both
oracles and binds neither. The bundle-level `Ttc.TtcProb.volume_estimate` still
quantifies over them, which is why the table above is still the right reading of
*this* theorem.

A second, smaller goal: `AUDIT.md:9` claims `Ttc/Model/` is **four files**, while
`Model/` held five. **Done** — see the status table.

### The mathematical route (already written down in the paper)

`sections/proof-appendix.tex:149–181` — "Realizing an Almost Uniform Sampler" —
gives the whole chain:

1. **`claim:linf` = KV97 Theorem 2.** Draw `p` from a density on the *inflated*
   polytope `P' = {x : Ax ≤ b + (c + √(2 log r))‖A‖}` close to uniform. Then for
   every `x ∈ P ∩ ℤⁿ`, `Pr[rnd p = x]` is pinned near `1/Vol(P')`.

   **As printed, this is wrong in two ways, both now settled by proof** — see the
   findings above and `AUDIT-KV97.md` §4a/§4b. The provable statement, and what
   `Arlib.KV97.theorem2` says, is
   `(1−ε)(1−E)/Vol(P') ≤ Pr[rnd p = x] ≤ (1+ε)/Vol(P')`
   with a **pointwise** `(1±ε)` density hypothesis (not total variation) and
   escape mass `E ≤ exp(−c²/2)` (not `2e^{−c²}`).
2. **`cor:linf`.** Take `c = cOf ε = √(2·log(4/ε))` and a pointwise deviation of
   `ε/4`; reject until `rnd p ∈ P`. The conditional law is then within a
   multiplicative factor of uniform on `P ∩ ℤⁿ`.
   **This is `eq:almostuniform`** (`sections/related.tex:21`) — i.e. exactly
   `theta_lo`/`theta_hi`.
3. Transport ℤⁿ → `𝕃ⁿ = 10^(−ρ)·ℤⁿ` along the dilation `φ` of `lem:lattice`.

KV97 = **Kannan & Vempala, "Sampling Lattice Points", STOC '97**
(`258533.258665.pdf`, DOI 10.1145/258533.258665). Confirmed by OCR extraction;
the PDF has a text layer but no `pdftotext` on this box — see *Reading the PDF*
below.

### Decisions taken (do not relitigate)

* **KV97 scope**: Theorems 1 & 2 and Lemma 1 only. Theorem 3 is `lem:lattice`,
  already proved (`Ttc/Lattice/Assembled.lean:222,227`). §3 (contingency tables,
  integral flows, b-matchings) and Theorem 4 (NP-hardness) are **out of scope**.
* **ArLib**: `arlib` is pinned to Lean/Mathlib **v4.15.0**; this repo is
  **v4.32.0**. They cannot be path-dependencies today. General material is
  therefore **staged in-repo** as a second Lake lib under `Arlib.*` namespaces,
  so the eventual port is a `git mv`.
* **Continuous sampler**: *construct* it, don't assume it. Build the
  isoperimetry → conductance → mixing stack for the **ball walk** (matches
  Cousins–Vempala §4.1 and the kernels already stated in
  `../gaussian-cooling-vempala/lean/Conductance.lean`).
* **Ordering**: the KV97 chain lands **first**, against an almost-uniform draw as
  a hypothesis, so the sampling oracle discharges early. The mixing stack lands
  underneath and removes that hypothesis later. (Note §4b: the hypothesis the
  chain needs is *pointwise* almost-uniformity, which a mixing bound alone does
  not give — that is extra work the original plan did not foresee.)

---

## Architecture

```
lean/
  lakefile.toml            # + second lean_lib "Arlib"
  Arlib.lean               # staging root — Mathlib-only deps
  Arlib/                   # GENERAL. No `Ttc.*` import, ever.
    Probability/TV.lean
    Probability/Rejection.lean
    Lattice/Rounding/…     # moved out of Ttc/Rounding
    Lattice/KV97/…         # new: Thm 2, Lemma 1, Thm 1, cor:linf
    Convexity/…            # logconcavity, Prékopa–Leindler, isoperimetry
    MarkovChains/Continuous/…  # conductance, mixing, ball walk, sampler
  Ttc.lean
  Ttc/                     # kr-25-ssm SPECIFIC only
    Model/{Prelude,Pseudocode,ProblemSetting,Theorem}.lean   # exactly 4
    Sampler/…              # new: wire cor:linf into TtcProb
    Volume/Bridge.lean     # new: proofs evicted from Model/VolOracle
    …existing dirs unchanged
```

**Hard rule, enforced by a grep in CI-style check:** no file under `Arlib/` may
import `Ttc.*`. `Ttc/**` may import both.

**Namespace rule:** staged files use `Arlib.<Area>` namespaces, Apache-2.0
header, mathlib-style docstrings — i.e. arlib's own conventions, so the port
into `arlib/Arlib/` is mechanical.

---

## Phase 0 — Model/ back to four files (small, do first)

`Ttc/Model/VolOracle.lean` is deleted. Its contents split three ways:

| From `VolOracle.lean` | To | Why |
|---|---|---|
| `roundBody` (`:163`) | `Ttc/Volume/Oracle.lean` | it is `Vol_ED`'s normalisation, not vocabulary of the paper's problem. (It went to `Model/Prelude` first; moved on when `Model/` was trimmed to the nfalean brevity.) |
| `structure VolumeAlgorithm` (`:79`) | `Model/ProblemSetting.lean`, above `TtcProb` | it is an assumption bundle; ProblemSetting's charter is "everything assumed" |
| `VolumeAlgorithm.exact` (`:115`), `ball_subset_roundBody`, `convex_roundBody`, `volume_roundBody`, `volume_roundBody_ne_top`, `toReal_volume_eq`, `mem_relErr_smul`, `of_ball`, `volGood`, `measurableSet_good`, `measure_bad_le`, `measure_volGood_ge` | **new** `Ttc/Volume/Bridge.lean` | proofs |

Also evict from `Model/ProblemSetting.lean` into `Ttc/Volume/Bridge.lean` the
theorems currently sitting after the structure — `volED_hi`, `volED_lo`,
`deltaPrime_pos`, `deltaPrime_lt_one`, `volCoins_mem_volEvent`, `volGood_prob`,
`volGood_prob_budget` (`:275–351`). Keep only the structure and the trivial
defs `D`, `numCubes`, `cubeAt`, `volEvent`. This makes `AUDIT.md`'s claim
("four files, no proofs worth the name") true rather than aspirational.

`Ttc/Volume/Bridge.lean` imports `Ttc.Model.ProblemSetting` and
`Ttc.Lattice.Decomposition` (for `convex_region`). Update `Ttc.lean` and every
`import Ttc.Model.VolOracle`.

**Gate:** `lake build` green, `#print axioms Ttc.TtcProb.volume_estimate`
unchanged, zero `sorry` warnings.

---

## Phase 1 — Stand up the ArLib staging lib

1. `lean/lakefile.toml`: add
   ```toml
   [[lean_lib]]
   name = "Arlib"
   ```
   and `defaultTargets = ["Ttc", "Arlib"]`.
2. `lean/Arlib.lean` — root re-exporting area roots (arlib convention).
3. **Move, renamespace `Ttc` → `Arlib.Lattice.Rounding`, and re-export** the
   genuinely general rounding files. They are pure randomized-rounding theory
   with no kr-25 content, and KV97 Thm 2 needs them:

   | Current | Staged as | Content |
   |---|---|---|
   | `Ttc/Rounding/Tent.lean` | `Arlib/Lattice/Rounding/Tent.lean` | tent density `1−\|u\|`, integral 1, mean 0, support `[−1,1]` |
   | `Ttc/Rounding/RoundLaw.lean` | `…/RoundLaw.lean` | `tentInt`, `roundLaw p` on `ℤⁿ` |
   | `Ttc/Rounding/RoundMoments.lean` | `…/RoundMoments.lean` | two-point law, bounded, mean-zero, `iIndepFun_latDisp` |
   | `Ttc/Rounding/PiLintegral.lean` | `…/PiLintegral.lean` | product-measure integral plumbing |
   | `Ttc/Rounding/ProdKernel.lean` | `…/ProdKernel.lean` | `integral_prod_tent` (double stochasticity), `roundBox`, `prodKernel` |
   | `Ttc/Rounding/ProdLaw.lean` | `…/ProdLaw.lean` | the displacement law on `ℝⁿ` |
   | `Ttc/Rounding/Hoeffding.lean` | `Arlib/Probability/SubgaussianTail.lean` | `rounding_tail_bound` (`Pr[A·Y ≥ κ‖A‖] ≤ e^{−κ²/2}`), `rounding_union_bound` |

   **Stay in `Ttc/`:** `Rounding/Cl.lean` and `Rounding/ClB.lean` — they are
   about `claim:cl` over `Ttc.FacetSystem`, i.e. kr-25-specific.

   Keep `Ttc.`-named `abbrev`s (or `export`) at the old paths for one commit so
   the ~40 downstream references don't have to change in the same step.

4. `Arlib/Probability/TV.lean` — the `TVLe μ ν ε` predicate and its API
   (symmetry, triangle, `≤ 1`, `tv = 0 ↔ equal`, chain bound, and the transfer
   `μ S ≤ ν S + ε`). **Port from** `../gaussian-cooling-vempala/lean/TV.lean`
   (proved, nothing assumed) and/or
   `/home/devel/Documents/arlib/Arlib/MarkovChains/Continuous/TotalVariation.lean`
   (`Arlib.Kernel.TVLe.measure_le_add`). Both are v4.15; expect light porting.

5. `Arlib/Probability/Rejection.lean` — conditioning and rejection sampling:
   `Pr[X = x ∣ X ∈ S] = Pr[X=x]/Pr[X∈S]`, positivity of the acceptance
   probability ⟹ the loop terminates a.s., and the two-sided quotient bound
   `1/(1−θ) ≤ 1 + 2θ` for `θ ≤ ½`. Reuse
   `arlib/Arlib/Approximation/RejectionCollect.lean` and
   `Arlib/Probability/Conditioning.lean` as sources.

**Gate:** `lake build` green for both libs; `grep -rn "import Ttc" Arlib/`
returns nothing.

---

## Phase 2 — KV97 Theorem 2, Lemma 1, Theorem 1

New directory `Arlib/Lattice/KV97/`. Land **one named theorem at a time**,
rebuilding green after each (CLAUDE.md §3).

### 2.1 `Inflate.lean` — the inflated polytope
`P' = {x : Ax ≤ b + κ‖A‖}` for `κ = c + √(2 log r)`, where `r` is KV97's
*"maximum number of facets meeting any unit cube `C(z,1)`"* — **note this is not
`m`**; the paper's `r` (`Ttc.Params.r`, `facets_le`) is the total facet count,
which upper-bounds it. State it with KV97's `r` and specialise.
Volume bound `Vol(P') ≤ (1 + κ/γ)ⁿ·Vol(P)` when `P ⊇ B(·,γ)`: **reuse**
`Ttc.FacetSystem.volume_body_inflated_le` (`Ttc/Nonconv/Recentred.lean:418`)
and `piece_inflated_subset_homothety` (`:69`) — generalise them out of
`FacetSystem` into `Arlib` while moving.

### 2.2 `Theorem2.lean` — **the crux** (CLAUDE.md §2)
```
Given ν a probability measure on P' with TVLe ν (uniform P') ε,
for every x ∈ P ∩ ℤⁿ:
  (1 − 2·r·e^{−κ²/2} − ε)/Vol(P') ≤ (ν.bind roundLaw) {x} ≤ 1/Vol(P')
```
Proof skeleton, each step a named lemma:
* `Pr[rnd p = x ∣ p] = ∏ᵢ tent(pᵢ − xᵢ)` — `Arlib.Lattice.Rounding.prodKernel`.
* Upper bound: `∫_{ℝⁿ} ∏ tent = 1` — `integral_prod_tent` (already proved).
* TV step: integrand in `[0,1]`, so swapping `ν` for uniform costs `≤ ε` —
  `Arlib.Probability.TVLe.measure_le_add`.
* Lower bound: `Pr[x + Y ∉ P'] ≤ r·e^{−κ²/2}` by the sub-Gaussian tail applied
  per facet plus a union bound — **`rounding_tail_bound_kappa`
  (`Hoeffding.lean:130`) and `rounding_union_bound` (`:163`) are already proved
  and are exactly this.** KV97 uses Azuma over the martingale
  `Zⱼ = Σ_{k≤j} A_{ik}Y_k`; the staged Hoeffding lemma is the same bound with a
  better constant.

> **Paper-bug watch (CLAUDE.md §5).** README finding 3 already records a
> *missing square* in `claim:cl`'s Azuma exponent. KV97's own Theorem 2 as
> printed reads `1 − 2e^{−c}` where the martingale argument gives `e^{−c²/2}`
> per facet. Record every such discrepancy in `AUDIT-KV97.md` with the
> corrected form; do **not** silently prove the paper's version.

### 2.3 `Lemma1.lean` — acceptance probability
`bᵢ ≥ 8n√(log r)·‖Aᵢ‖ ⟹ Pr[rnd p ∈ P] ≥ 1/8`. Uses 2.2 summed over the `N`
lattice points plus the `Vol(P') ≤ (1+κ/γ)ⁿ Vol(P)` bound of 2.1 and
`lem:nonconv`'s `Vol(P) ≤ (1+η)N`.

### 2.4 `Theorem1.lean` + `Corollary.lean` — the sampler, and `eq:almostuniform`
`Theorem1`: the rejection loop's output law is `roundLaw` conditioned on
`rnd p ∈ P` (`Arlib.Probability.Rejection`).
`Corollary` (= paper's `cor:linf`): with `c = √(log(8/ε))` so `2e^{−c²} = ε/4`,
and TV `ε/4`, get `θ = ε/2 ≤ ½` and
```
(1−ε)/N ≤ Pr[out = x] ≤ (1+ε)/N   for every x ∈ P ∩ ℤⁿ.
```

### 2.5 `FineLattice.lean`
Transport along `x ↦ 10^ρ·x`: `P ∩ 𝕃ⁿ ≃ (10^ρ·P) ∩ ℤⁿ`. Both sides of
`eq:almostuniform` are normalised by the count, so the statement is invariant.
Reuse `Ttc.fineLattice`/`Ttc.latticeScale` (`Model/Prelude.lean`) — generalise
into `Arlib/Lattice/Basic.lean` while moving.

**Gate:** `#print axioms Arlib.Lattice.KV97.corollary` clean; `AUDIT-KV97.md`
written (see below).

---

## Phase 3 — Discharge the sampling oracle

New `Ttc/Sampler/`:

* `Contract.lean` — `Ttc.AlmostUniform D S ε`, the `eq:almostuniform` predicate
  over `P(cᵢ) ∩ 𝕃ⁿ`, and `Ttc.almostUniform_of_kv97`: it holds for the sampler
  `Arlib.Lattice.KV97.corollary` builds, given `ball_subset`/`rho_eq`.
* `Discharge.lean` — derive `theta_lo` and `theta_hi` from
  `AlmostUniform` + `lem:lattice` (`Ttc.TtcProb.lattice_lo/hi`) + `Vol_ED`'s
  two-sided `volED_lo`/`volED_hi`. This is the `(1±ε')²(1±η)` window: one
  `(1±ε')` from the sampler, one from `Vol_ED`, `(1±η)` from `lem:lattice`.
  `gen_mem` follows from `cor:linf`'s support being `P(cᵢ) ∩ 𝕃ⁿ`.

Then **delete `theta_lo`, `theta_hi`, `gen_mem` as fields of `TtcProb`** and
re-add them as theorems with identical statements (the pattern already used for
`numlattice_union` and `rate_small`). Replace them with the strictly weaker
field: the sampler's continuous draw is TV-`ε'/4`-close to uniform on `P'`.

**Gate:** `Ttc.Box.boxProb` still discharges every field (the witness will now
need to exhibit a TV-close continuous draw — the exact uniform measure works,
`TVLe μ μ 0`); `#print axioms Ttc.TtcProb.volume_estimate` unchanged; the
dependency-walk probe in `AUDIT.md` §5 reports the new theorems as reached.

---

## Phase 4 — The ball-walk mixing stack (the long pole)

> **Read this phase as the plan it was, not as outstanding work.** Its correctness
> content has landed: Prékopa–Leindler (1-D and `ℝⁿ`), Brunn–Minkowski, logconcavity,
> the isoperimetric inequality, conductance, Cheeger in **both** directions, and
> conductance ⇒ TV mixing are all proved in `Arlib/` — `CV-ROADMAP.md` §3's third
> column is the current inventory, and every `IsoInput`/`MixingFromConductance`-style
> assumed predicate named below has been **deleted**, not merely discharged. What did
> *not* land is the constant: everything runs at `κ = 2⁻ⁿ/D`, so the stack is
> exponential in `n`. The file list below is kept because it is the decomposition that
> worked.

This is what removes the last hypothesis of Phase 3 **and** discharges
`VolumeAlgorithm`. Mathlib v4.32 has *none* of it: no Prékopa–Leindler, no
Brunn–Minkowski, no logconcavity, no isoperimetric inequality, no conductance, no
mixing time, no continuous-state quantitative convergence. Budget accordingly; this
phase is measured in months, not days.

`Arlib/Convexity/`
* `LogConcave.lean` — logconcave functions/measures, closure properties. Port
  from `arlib/Arlib/Convexity/LogConcave.lean` (v4.15) and
  `../gaussian-cooling-vempala/lean/Isoperimetry.lean`.
* `PrekopaLeindler.lean` — **the crux of this phase.** Everything above needs
  it; nothing in Mathlib supplies it. Do the 1-D case first, then induct.
* `Isoperimetry.lean` — isoperimetric inequality for logconcave densities
  (CV §3). `../gaussian-cooling-vempala/lean/Isoperimetry.lean` has the
  specialisation §4 consumes but **assumes** `IsoInput`/`OneDimIso`; those are
  the two predicates this file must turn into theorems.

`Arlib/MarkovChains/Continuous/`
* `Conductance.lean` — conductance of a kernel w.r.t. its stationary measure.
  `../gaussian-cooling-vempala/lean/Conductance.lean` already builds the Metropolis
  filter, ball walk and speedy walk as genuine Markov kernels — **reuse those**;
  what it assumes (`MixingFromConductance`, `SpeedyConductance`,
  `BallWalkMixing`) is what to prove.
* `MixingFromConductance.lean` — Cheeger/Lovász–Simonovits: conductance `φ`
  ⟹ TV decay `≤ M(1−φ²/2)ᵗ` from an `M`-warm start.
* `BallWalk.lean` — the ball walk's conductance from isoperimetry (CV §4.1).
* `Warmness.lean` — `M(Q₀,Q)` propagation (CV §4.2). `TV.lean` already proves
  warmness and its propagation.
* `UniformSampler.lean` — **the payoff**: `∀ ε > 0, ∃ t, TVLe (ballWalk^t μ₀)
  (uniform K) ε` for convex `K` with an inscribed ball. This is the object
  Phase 3's residual field asks for.

**Gate:** Phase 3's TV field becomes a theorem; it is deleted from `TtcProb`.

---

## Phase 5 — Discharge the volume oracle

With Phase 4 landed, `VolumeAlgorithm` becomes constructible:
* `Arlib/Convexity/GaussianCooling/` — port the **proved** §5.1 material from
  `../gaussian-cooling-vempala/lean`: `Ratio.lean` (`expect_ratio`,
  `expect_ratio_sq`, `variance_ratio`), `Main.lean` (`lc_variance_bound`,
  `fast_var_bound`), `FixedRate.lean`, `Needle.lean`/`VDeriv.lean`
  (Brascamp–Lieb, **already proved there**), `Estimator.lean` (`lem:exp-bd`,
  `lem:fn-indep`, median boost — proved).
* Two residual inputs there must be closed: `LocalizationInput`
  (`Localization.lean:177`) and `ZLogconcave` (`FixedRate.lean:110`) — the
  latter needs Prékopa–Leindler, i.e. Phase 4.1.
* CV §5.2: telescoping `W₁…W_m`, `lem:accuracy`, the `4/5`→`1−p` median boost.
  Note `Estimator.lean`'s boost currently runs at the **Chebyshev** rate
  `O(1/p)`, not the paper's `O(log 1/p)`; the `1−p` conclusion is unaffected but
  record it in the audit.
* Then `Ttc.VolumeAlgorithm.cousinsVempala : VolumeAlgorithm n`, and
  `volAlg`/`volCoins_good` stop being fields.

---

## Phase 6 — Remaining assumptions

After 3 and 5, what is left in `TtcProb` is `law_eq`/`oracle_eq` (the sampler
*is* `trajOracles` over `trajLaw`) and the input hypotheses. Two known items,
both already documented:

* **README finding 13a** — the headline reads `1 − δ` over the run's randomness
  at a fixed good `volCoins`, not `1 − δ − δ/4` over the joint randomness.
  Composing the two on a product space is a refactor of `Coupling/{Family,Run,
  Transfer}`. Fix it once `volAlg` is constructed, since the coins stop being a
  free parameter.
* **README finding 5** — `isPositive` excludes negated atoms (open half-spaces).
  Genuine restriction; `lem:lattice` is proved for positive DNFs only. Either
  extend to open half-spaces or keep and state it plainly.

---

## Audit surface (CLAUDE.md §11 — not optional)

* **`lean/AUDIT-KV97.md`** (new, required by the prompt). Same four-check shape
  as `AUDIT.md`, for the KV97 development alone:
  1. capstone = `Arlib.Lattice.KV97.corollary`, read its *type*; is it
     `eq:almostuniform` over the real `P ∩ 𝕃ⁿ`?
  2. hypothesis fields of the KV97 interface + where each is discharged;
  3. non-vacuity witness — a box/simplex with an explicit TV-0 uniform draw;
  4. semantic `def`s: every `def` whose *name* promises an identity carries a
     proving lemma (`roundLaw`, `inflate`, `acceptLaw`, …).
  Plus a **discrepancy table**: KV97 as printed vs. what is provable (start with
  the Azuma exponent; expect more — the OCR text is in the scratchpad).
* **`lean/AUDIT.md`** — update: Model is four files again; `theta_lo`/`theta_hi`/
  `gen_mem` move from the field table to the proved list; the
  `Ttc.TtcProb.volume_estimate` dependency-walk probe in §5 gains the new names.
* **`lean/README.md`** — refresh the module map and "What is assumed" **at least
  every ~30 min of active work** (CLAUDE.md §12). A stale README overstates.
* **`lean/CV-ROADMAP.md`** — Phases 4–5 are its plan; keep it in sync.

---

## Working notes

**Reading the PDF.** No `pdftotext`/`pdftoppm`/`mutool`/`pypdf` on this box. The
OCR text layer extracts with a ~30-line Python script (zlib-inflate every
`stream`, then pull `(...) Tj` / `[...] TJ` operands). Output is already at
`<scratchpad>/kv97.txt`. It is **OCR-noisy** ("polytopea", "ia"→"is",
`1-ze-c` for `1−2re^{−c²/2}`), so *never* transcribe a formula from it — derive
the statement and check it against `sections/proof-appendix.tex:153`, which
states `claim:linf` cleanly.

**Agent discipline** (CLAUDE.md §7): one agent per file, disjoint file sets,
brief with the *exact* theorem statement + the exact lemma names available +
step-by-step strategy. Verify every claimed green yourself — rebuild and
`#print axioms`. Sequence the linchpin definitions (Phase 1 staging, 2.1
`Inflate`) before fanning out.

**Order of attack inside a phase**: crux first (2.2 `Theorem2`, 4.1
`PrekopaLeindler`), then the bookkeeping collapses.

---

## Verification

After every phase:

```bash
cd lean
lake exe cache get && lake build          # zero "declaration uses 'sorry'"
grep -rn "sorry\|admit\|native_decide\|sorryAx\|^axiom " Ttc.lean Ttc/ Arlib.lean Arlib/ \
  | grep -v '`sorry`'                      # expect nothing
grep -rn "^import Ttc" Arlib/              # expect nothing — the staging rule
```

```lean
import Ttc
#print axioms Ttc.TtcProb.volume_estimate   -- [propext, Classical.choice, Quot.sound]
#print axioms Arlib.Lattice.KV97.theorem2
#print axioms Arlib.Lattice.KV97.corollary
#print axioms Ttc.TtcProb.theta_lo          -- Phase 3: was a field, now a theorem
#print axioms Ttc.Box.nonempty_ttcProb      -- non-vacuity survives every field change
```

Re-run the transitive dependency walk from `AUDIT.md` §5 (it walks
`getUsedConstantsAsSet` from the capstone) and confirm the new KV97 results come
back `true` — an import only says a file is *visible*, not that anything in it
is *used*. That check is what settles "the headline actually rests on this".

**Phase-completion definition:** a field deleted from `Ttc.TtcProb` and re-added
as a theorem with the *identical* statement, with the witness `Ttc.Box.boxProb`
still discharging everything and the axiom profile unchanged.
