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

## 0⁗. Status, 2026-08-12 (later) — supersedes §0‴ and §0′ on `thm:iso`, and the headline still does not move

Read this whole section or none of it. It contains the largest single advance this
file has ever recorded and the sharpest negative, and they are about the same
theorem.

### 1. `thm:iso` is PROVED — unconditionally, for the density the algorithm uses

The critical-path table below has said for months that `thm:iso` waits on `hloc`,
and that `hloc` waits on localization residuals (C) and (F). **That is no longer the
route.** `Arlib/Convexity/IsoOpenClosed.lean` and `Arlib/Convexity/IsoIndicator.lean`
prove `thm:iso` with **no localization binder of any kind**, by going round the
localization stack rather than through it:

* `Arlib.gaussianRestricted_isoperimetry_openClosed` (`IsoOpenClosed.lean:854`) — for
  a general `h = f·e^{−‖x‖²/2σ²}` with `f` log-concave. Price, in the file's own
  words: `S₁, S₂` **open**, `S₃` **closed**, `h` **continuous and bounded** (plus
  integrable). Threshold `2√3·d`.
* `Arlib.gaussianIndicator_isoperimetry_measurable` (`IsoIndicator.lean:476`) — for
  the **indicator** density `1_K·γ_{σ²}` with `S₁ S₂ S₃` merely **measurable**. Two
  more hypotheses: `hRσ : √3·R ≤ 2σ√n` and `hK0 : volume K ≠ 0`.

**What unlocked it was the `(1d-2)` constant**, and that is the entry of §0‴/§0′ that
this section most directly supersedes. `Arlib/Convexity/OneDimSharp.lean` proves
`(1d-2)` at **`√(2/π) ≈ 0.7979`** (`oneDim_isoperimetry_gaussianFactor_sharp`,
`:518`), which **clears the paper's `ln 2 ≈ 0.6931`**
(`log_two_le_sqrt_two_div_pi`, `:554`, the machine-checked `≤`; the strict `>` is
docstring arithmetic and is not needed). So the whole downstream stack runs at the
paper's own `ln 2`, and the `2√3·ln 2 ≈ 2.401` threshold penalty recorded at
`§0′` blocker 1 and in the `(1d-2)` row of the critical-path table is **gone**.

The payoff is two declarations, both in `OneDimSharp.lean`:

* `Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo` (`:1040`) — the `hiso` binder of
  `Arlib.MarkovChains.conductance_metropolisGaussian_sharp_sqrt_ge`
  (`MarkovChains/Continuous/MetropolisOverlapSqrt.lean:284-295`) **character for
  character**, proved;
* `Arlib.conductance_metropolisGaussian_sharp_sqrt_ge_of_convex` (`:1073`) — that
  conductance bound with `hiso` gone, adding only `hRσ`.

And §0‴'s "named missing piece" — a **Metropolis** overlap lemma at `δ/√n` — landed
the same day: `Arlib.MarkovChains.metropolisGaussian_overlap_sqrt_of_convex`
(`MetropolisOverlapSqrt.lean:164`), constant `20`, needing no `ℓ`-comparability.
On top of both, `MixingSqrt.lean` does the `Φ⁻²` arithmetic and
`MetropolisMixingUncond.lean` states the lazy Metropolis mixing bound with **no
isoperimetry hypothesis**: `4·5120²·n²·(log M + 2·log(1/ε))/(log 2)² + 1` steps
suffice.

**Scope it exactly.** "`hiso` discharged" covers **one** binder. Still carried,
unproved: `conductance_metropolisGaussian_sharp_ge`'s (the `δ/n` version,
`MetropolisConductanceSharp.lean:438` — no `_of_convex` variant exists) and the
entire speedy-walk family (`SpeedyWalk.lean:976, 1210, 1322`;
`SpeedyToUniform.lean:230, 278`; `OverlapSqrt.lean:680`;
`SpeedyConductanceSharp.lean:333`), whose density is `1_K·ℓ` rather than `1_K·γ_σ`.
And "unconditional" mixing means "no `hiso` binder" and nothing more: `hell`,
`hfloor`, `hRσ`, the geometry and the warm start all remain, and the **plain-chain**
variants still carry an unproved `hpsd : HasNonnegSpectrum`.

### 2. And the runtime did not move, because a *floor* replaced the isoperimetry

`Arlib/MarkovChains/Continuous/EllFloor.lean`. The Metropolis conductance and mixing
theorems carry, besides the now-discharged `hiso`, a **pointwise local-conductance
floor**:

```
hell   : ∀ x ∈ K, ofReal θ ≤ ell K δ x
hfloor : 1 ≤ 20 · e^{−(2Rδ+δ²)/(2σ²)} · (1/4) · θ
```

`hfloor` forces `θ ≥ 1/5`. A `k`-fold corner forces `ell ≤ 2⁻ᵏ` **at every step
size** (`two_pow_card_mul_ell_le_one`, `:244`; the proof is the coordinate-reflection
group, with no convexity or measurability used). The cube `[-1,1]ⁿ` has an `n`-fold
corner and **contains the unit ball**, so it is in the class the Gaussian-cooling
consumer quantifies over (`Ttc/Volume/CVInstantiate.lean:148,153`). Hence

* `metropolis_ell_floor_unsatisfiable_on_cube` (`:402`) — for `n ≥ 3`, `hell` and
  `hfloor` (the `1/4` shape) together imply `False`;
* `metropolis_ell_floor_dim_unsatisfiable_on_cube` (`:483`) — the same for the
  `(1−1/n)ⁿ` shape, at `n ≥ 5`;
* `exists_convex_body_meeting_all_but_ell_floor` (`:417`) — the attribution: at
  `σ = 1`, `δ = 1/(8√n)`, `R = √n` the cube meets **every other** binder, `hRσ` and
  `ball 0 1 ⊆ K` included.

**Do not write "`hell` is unsatisfiable"** — it is satisfiable alone, including
non-trivially (`le_ell_of_ball_subset_of_radius`, `:498`, at `θ = (1/(1+2R))ⁿ`).
What is proved is that `hell ∧ hfloor` are contradictory there. And this refutes
nothing: `conductance_metropolisGaussian_sharp_sqrt_ge_of_convex` is **true**; it is
**vacuous** on the body the oracle needs. What survives is the *average* — every
convex `K ⊇ B(0,1)` is `(δ, 1 − (1−δ)ⁿ)`-smooth (`isSmooth_of_ball_subset`, `:549`),
and `IsSmooth` is blind to the corner where the infimum collapses.

**So the honest one-line status of the CV side is now:** the deep probability
obstruction is gone, and what stands between this repository and a polynomial-time
volume oracle is (i) a sampler that exists, (ii) a conductance route whose
hypotheses hold on cornered bodies — the speedy walk is the candidate and its own
`hiso` is open — and (iii) the fact that `Ttc.VolumeAlgorithm`
(`Ttc/Volume/Oracle.lean:70-93`) has **no complexity field at all**, so no
instantiation of it can state a running time, let alone prove one. (iii) is a design
decision, not a proof problem.

### 3. `hphase_mean` was rewired, and it changed which debts are routeless

`Ttc.ttc_runtime_mn4` now runs `Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMean`
(`Ttc/Volume/CVInstantiate.lean:458`), whose `hphase_mean` is the **interval**
`∫ g dν ∈ (1 ± ε/(2(2+ε)m))·(chain(i+1)/chain(i))` rather than the equation
`Ttc.cvVolAlg` still carries. The reason the equation had to go is machine-checked:
`Arlib.GaussianCooling.exists_tvLe_coolLaw_integral_phaseScore_ne`
(`GaussianCooling/PhaseMeanRoute.lean:518`) exhibits, at every `ε ∈ (0,1]`, a law
within TV `ε` of `coolLaw` whose phase-score integral is exactly
`(1−ε)·(chain(i+1)/chain(i))` — the relative error **is** the TV error, so no mixing
bound short of exact sampling can deliver the equality. (That theorem refutes the
*implication*, not the equation: the equation holds exactly at `coolLaw`.)

The join that makes any of this compose is
`Arlib.GaussianCooling.coolLaw_eq_uniformOn_gaussianWeight`
(`PhaseMeanRoute.lean:216`): `coolLaw` **is** the stationary law of §1's mixing
bound, unconditionally.

The price: `hphase_var` had to be **strengthened** to
`Arlib.GaussianCooling.varBudget (ε/2)`. That it is forced is a docstring argument
resting on `exp_varBudget` (`GaussianCooling/Schedule.lean:186`), not a theorem.
The residual-hypothesis count of the capstone is **unchanged at 38**; what changed is
that the routeless subset went from six to five. `AUDIT.md` §0a is the ledger.

Two routes to the interval hypothesis now exist and neither is walked:
**Route A** (`GaussianCooling/PhaseMeanApprox.lean`) derives it from a TV bound plus
a slack condition, `hiso`-free, at a cost whose machine-checked content is one log
identity (`log_one_div_tvBudget_exp`, `:433`) — the reading that the `R²/(2σᵢ²)` term
costs the exponent is arithmetic in the docstring, not a theorem. **Route B**
(`GaussianCooling/CouplingRoute.lean`, `CouplingRouteUncond.lean`) transfers the
success probability across the TV gap instead, on `Arlib.Probability.TVTensor`'s
tensorization, and has a **complete chain-layer witness**
(`exists_couplingRoute_chain_witness`, `CouplingRouteUncond.lean:256`) — at a trivial
estimator (`V ≡ 1`, `q = 1`, `n = 2`, `K = B(0,1) ⊆ ℝ²`).

⚠ **The composed layer, `Ttc/Volume/CouplingAccuracy.lean`, has no non-vacuity
witness at all**, and the file says so itself (`:89`). Its concrete success
probability is `q = 1 − p` from `Ttc.CVEst.volume_accuracy_of_samples`
(`Ttc/Volume/CVEstimator.lean:582`) — note the namespace is `Ttc.CVEst`, not
`Ttc.CV`. Its `k ≥ 2` caveat is live: `RunSpace E r m` has one coordinate per
(run, phase), so the "`k` independent samples per phase" reading needs `k = 1`.

### 4. Four more findings against the paper — and one the formalisation retracts

See §0‴′ (a subsection of §0″ below), which appends findings **10–13** to the nine
recorded in §0′, and note in particular
that the `tν` vs `2kmν` "discrepancy" is **not** an error and is not recorded.

---

## 0‴. Status, 2026-08-12 — supersedes §0′ on two links

Two links of the critical-path table moved, and neither moves the runtime. Read
both entries whole; each is a case where the encouraging half is the half that
gets quoted.

### 1. KLS95 Lemma 3.5 and `cor:overlap` reach `δ/√n` — the `√n` is real, `n⁴` is not

**What is proved.** `Arlib.MarkovChains.kls_lemma35_at_sep_sqrt_dim`
(`Arlib/MarkovChains/Continuous/LensMin.lean:423`) proves the **`min` form** of
KLS95 Lemma 3.5 at separation `δ/√n`, constant `1/40`, carrying **exactly** the
paper's hypotheses — `2 ≤ n`, `Convex ℝ K`, `u, v ∈ K`, `0 < δ`, `‖u−v‖ ≤ δ/√n`.
No measurability of `K` (convex sets are null-measurable), no floor on `ℓ`, no
`d_ℓ` comparability. `kls_lemma35_at_sep_sqrt_dim_sharp`
(`OverlapSqrt.lean:364`) sharpens the constant to `1/8` by replacing
`inv_twenty_le_one_sub_inv_pow`'s `1/20` with the sharp uniform bound
`(1 − 1/n)ⁿ ≥ 1/4`. `overlap_speedyWalk_sqrt_of_ell_comparable`
(`OverlapSqrt.lean:527`) then reaches `cor:overlap` at `δ/√n` at constant `12`,
which composes with the `20` that `conductance_speedyGaussian_ge` demands;
`conductance_speedyGaussian_ge_of_ell_comparable` (`:669`) is the composition.

**The mechanism**, since this closed a gap the repository had documented as needing
"a genuinely different argument": pair a point *behind* `u` with a point *ahead of*
`v`. The two sign conditions cancel the `t`-linear terms — `‖(x−u) + (v−u)‖² ≤ δ² +
t²` — so the midpoint's excess over `δ` is **quadratic**, `t²/(4δ)`, i.e. `δ/(4n)`
at `t = δ/√n`, where a bare triangle inequality gives only `δ/(2√n)`. An excess of
`δ/(4n)` is what a `(1 − 1/n)` homothety absorbs at constant cost; a `δ/√n` excess
is not. Then Brunn–Minkowski. `midpoint_mem_ball_inter` (`LensMin.lean:109`) is the
crux. **No polar decomposition is used**, which is what `SpeedyOverlap.lean`'s
docstring claimed the argument needed.

**What the `√n` is worth — and why the obvious comparison gets it backwards.**
`Arlib/MarkovChains/Continuous/DeltaCap.lean` exists to answer exactly this, in
three layers.

*Layer 1.* Taken each at its own maximal `δ`, the two bounds agree:

| theorem | cap on `δ` | conductance bound | at its own maximal `δ` |
| --- | --- | --- | --- |
| `conductance_speedyWalk_ge_of_convex` (`StarPolar.lean:626`) | `δ ≤ σ/8` | `δ·log2/(640·σ·n)` | `log2/(5120·n)` |
| `conductance_speedyGaussian_ge_of_ell_comparable` (`OverlapSqrt.lean:658`) | `δ ≤ σ/(8√n)` | `δ·log2/(640·σ·√n)` | `log2/(5120·n)` |

This is a **theorem**, `sup_bounds_agree_at_own_caps` (`DeltaCap.lean:357`), and it
makes the `√n` look illusory.

*Layer 2 — the appearance is an artifact, and the `√n` is real.* The `δ` of
`conductance_speedyGaussian_ge` (`SpeedyConductanceSharp.lean:320`) is an
**isoperimetric scale**, not a step size: that theorem takes the kernel as a
parameter independent of its own `δ`. The two rows are **one theorem at two
parameterizations** — `StarPolar.lean:664–666` instantiates it at `δ_abs := δ/√n`
with kernel `speedyWalk K δ` (`speedyGaussian_reparam_cap`,
`speedyGaussian_reparam_conclusion`), `OverlapSqrt.lean:690` at `δ_abs := δ` with the
*same* kernel. **Neither shrank any cap**; both inherited `hδσ` from the abstract
theorem. What differs is only which overlap lemma each can supply. Consequently:

* at one and the same kernel step, the new bound is exactly `√n` times the old —
  `speedy_sqrt_gain` (`:299`);
* the operative step is set by the **Metropolis acceptance floor**, not by these
  caps: `metropolis_hfloor_forces_step_cap` (`:132`) shows `hfloor` forces
  `δ ≤ (ln 20)·σ/√n ≈ 3σ/√n` once `σ√n ≤ R`. At the nominal `δ = σ/8` the acceptance
  factor is `e^{−√n/8}` (`acceptance_floor_at_step_sigma_div_eight`) — exponentially
  small, and no `θ ≤ 1` compensates; at `δ ≤ σ/(8√n)` it is `≥ e^{−1/4}`
  (`acceptance_factor_ge_of_step_le`). So `σ/√n` is the right scale;
* at that operative step: `Φ ≥ log2/(5120·n^{3/2})` (old,
  `speedy_old_bound_at_operative_step`) against `Φ ≥ log2/(5120·n)` (new,
  `speedy_new_bound_at_operative_step`) — a genuine factor `√n` in `Φ`, hence `n` in
  the step count `1/Φ²`.

**The step-size cap is not the obstruction**, and no document should say the `√n`
cancels.

*Layer 3 — `n⁴` still does not follow*, for two reasons that are hypotheses rather
than caps (`DeltaCap.lean` §4):

⚠ **Both bullets were true when written and both were overtaken later the same day
— read §0⁗ with them.**

* ~~**the `δ/√n` overlap lemma exists only for the *unfiltered* speedy walk.**~~
  `metropolisGaussian_overlap_of_convex` (`MetropolisConductanceSharp.lean:238`)
  concludes only at separation `δ/n`, which is why the sharp Metropolis theorem lands
  on `δ·log2/(640σn)`. ~~A Metropolis overlap lemma at `δ/√n` is the named missing
  piece~~ — **it landed**: `metropolisGaussian_overlap_sqrt_of_convex`
  (`MetropolisOverlapSqrt.lean:164`), constant `20`, needing no `ℓ`-comparability but
  needing `hell` + `hfloor` instead;
* ~~**`hcomp` and `hiso` remain hypotheses**~~ — `hcomp` does, for the **speedy**
  route (next bullets). `hiso` **does not**, for the filtered route:
  `Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo` (`Convexity/OneDimSharp.lean:1040`)
  proves it character for character. What blocks `n⁴` instead is `EllFloor.lean`'s
  negative on the `hell`/`hfloor` pair. §0⁗.

`OverlapSqrt.lean`'s §"No rate claim", `LensMin.lean`'s §"What is *not* done here"
and `DeltaCap.lean`'s closing line all say the same thing: nothing in any of them
asserts, or may be quoted as asserting, a polynomial mixing time.

*A side finding, not a blocker.* `DeltaCap.lean` §3 shows `hδσ`'s own `√n` is
removable — its real content is the dimension-free `16·(ln 2)·δ ≤ σ`, so the honest
cap is `σ/(16 ln 2) ≈ σ/11.09` and `δ ≤ σ/8` genuinely fails
(`not_isoStep_quarter_at_sigma_div_eight`). The file **deliberately does not**
re-prove `conductance_speedyGaussian_ge` with the weaker binder, which would mean
editing a file it does not own, and no declaration in it claims the relaxed theorem.
It is not needed either: the operative step `Θ(σ/√n)` is well inside the existing cap.

**Three things that are still open or still hypotheses.**

* **`ℓ`-comparability, `d_ℓ(u,v) < 1/3`, is load-bearing.** It is Cousins–Vempala's
  own hypothesis, and it is what the `√n` costs:
  `exists_ell_not_comparable_at_sqrt_dim_counterexample` (`OverlapSqrt.lean:816`)
  re-derives the known `δ/√n` counterexample (`n = 23409`, `K = apexConeBody u v`)
  and proves it violates comparability at `d_ℓ > 0.95`, against a hypothesis that
  permits `1/3`. The counterexample is **not** contradicted by anything here.
* **`lem:f-dist` (`vol3_journal.tex:548`) is not proved.** Cousins–Vempala do not
  assume `d_ℓ < 1/3`; they *derive* it from `cor:overlap`'s own `d_h(u,v) < 1/4` at
  `h = f·ℓ`, via a Gaussian-ratio estimate the paper states only "for `n` large
  enough" and whose arithmetic is tight (`(3/4)/1.1 = 0.6818 > 2/3`). Formalising it
  would turn `hcomp` from a hypothesis into a consequence.
  `ell_le_of_densDist_ell_lt` (`OverlapSqrt.lean:599`) is the second half of the
  bridge and exists already.
* **The `max` form is false**, by `Arlib.MarkovChains.exists_halfspace_max_lt`. The
  argument pairs the *backward* half of one lens with the *forward* half of the
  other, so it can only conclude about the smaller of the two — the `min` is
  essential, not a convenience.

### 2. Localization residual (C) is an obstruction; (F) is closed

`Arlib/Convexity/LocalizationMeasurable.lean` settles both.

**(F) — closed.** `Arlib.exists_needle_of_compact_convex` (`:226`) is the
composition nothing had assembled: `exists_flat_cut_chain_collinear_compact_ge`
(`LocalizationClosed.lean:219`) turns a compact convex body into a chain, the needle
theorems turn a chain into a needle, and no single entry point took a body to a
needle. `v ≠ 0` is recovered along the way — it was available one level down (`φ v =
1`, `NeedleSlabAffine.lean:227`) and *discarded* by a `-` pattern in
`NeedleSlabChain.lean:288`; the composition is a replay that keeps it, weakened to
`v ≠ 0`, which is all that survives transport to `EuclideanSpace` and is exactly
what `hLoc` asks for. `exists_needle_of_compact_convex_witness` (`:266`) meets every
hypothesis at once on the closed unit ball.

**(C) — an obstruction, and this is the finding.** Two theorems, both about the
hyperplane `{x | ⟪e_j, x⟫ = 0}`, which is Lebesgue-null and contains the whole
coordinate axis `t ↦ t • e_i` for `i ≠ j`:

* `Arlib.exists_null_measurableSet_needleIntegral_eq_one` (`:442`) — a measurable
  `S` with `volume S = 0`, hence `∫_T 1_S = 0` for **every** `T`, together with a
  needle `(b, v)` with `v ≠ 0` and a profile `W` meeting every clause `hLoc` imposes
  on it, for which the needle integral `∫ W · 1_S ∘ needleMap b v` equals `1`.
  Modifying an integrand on a null set leaves every hypothesis of the Localization
  Lemma untouched and moves its conclusion by `1`. **Therefore no argument that
  controls `1_{S₁}` only through its almost-everywhere class — `L¹` density, Lusin,
  Vitali–Carathéodory, in-measure approximation — can produce `hLoc`.**
* `Arlib.exists_transverse_oscillation_eq_one` (`:550`) — for that same `S` and
  **every** body of positive volume, however thin, some point has transverse
  oscillation exactly `1`. The moduli `δ k` of `exists_tendsto_transverse_modulus`
  (`LocalizationTransverse.lean:112`) are therefore `≥ 1` at every stage of every
  chain of positive-volume bodies and do not tend to `0`. That lemma is the *unique*
  place the localisation limit passage consumes continuity — it is a uniform
  transverse-oscillation bound, not a dominated-convergence hypothesis — and it
  fails for indicators by a fixed constant. **So weakening `Continuous` to
  `Measurable` is closed too.**

**`hLoc` is NOT claimed false.** A needle is a null set, and Fubini forbids a null
set meeting every line in positive length, so an integrand cannot be arranged to
defeat *every* needle. What is proved is that the two routes available to this
repository are closed, and that `Arlib.Convexity.LocalizationLSC`'s boundary — `S`
open for the positivity slot, an unremovable `η`-slack for the equality slot — is
where the approximation route genuinely stops. Anyone attacking `hLoc` should start
from a route these two theorems do not cover.

The file contains **no** `def`, `structure`, `class` or named `Prop` — only theorems
proved outright — and no theorem in it takes the Localization Lemma, the
isoperimetric inequality or Dyer–Frieze as a hypothesis.

---

## 0″. Paper errors found by the formalization, 2026-08-11

`CLAUDE.md` §5: wherever Lean forced a hypothesis the source does not state, that
is a signal of a gap. This session produced five, across **both** target papers.
Each is machine-checked or carries an explicit counterexample; each is recorded
at its declaration, not only here.

**Lovász–Vempala, *Hit-and-Run from a Corner*:**

1. **Theorem 2.1 is FALSE as stated.** *(the big one)* Its hypothesis constrains
   `h` only on chords through **cross pairs**, while its conclusion integrates `h`
   over all of `K`. For `n ≥ 2` that union of chords can miss a positive-measure
   set. Counterexample at `n = 2`, `K = [0,1]²`, `S₁ = [0,1/8]²`,
   `S₂ = [7/8,1]×[0,1/8]`: every cross-chord point has `x₁ ≤ 7/24 < 1/3`, so
   `N = K ∩ {x₁ > 1/3}` (measure `2/3`) meets no cross chord, and `h = M·1_N`
   satisfies every hypothesis for all `M ≥ 0` while the conclusion fails for
   `M > 96`. Geometric core proved as `Arlib.chord_le_of_corner_boxes`;
   full formalization of the refutation is in progress.
   *Where the paper breaks:* §2 bounds `M_ab ≤ 1/3` from the hypothesis at a cross
   pair **on the needle**; localization forces the needle to meet `S₁`, but nothing
   forces it to meet `S₂`, and on such a needle there is no cross pair.
   *Consequence:* `Arlib.MarkovChains.conductance_hitAndRun_ge`'s guarantee is
   **empty** at `K = [0,4]²` and generically for `n ≥ 2`.
   *The repair costs nothing:* add the global `∀ x ∈ K, h x ≤ 1/3` — exactly what
   the paper's own §4 application verifies ("Clearly `h(x) ≤ 1/3`").

2. **The `10¹⁰` step-count constant does not follow from the paper's own
   Theorem 4.2.** Thm 4.2 gives `Φ ≥ 1/(2²⁴nD)` at inradius 1; scaling by `r` with
   `D ≤ 2R` gives `Φ ≥ r/(2²⁵nR)`; LS93 Cor 1.5 then needs
   `m ≳ 2⁵¹·n²(R²/r²)·ln(…)`, and `2⁵¹ ≈ 2.25×10¹⁵` — a factor `≈ 2×10⁵` above
   `10¹⁰`. §5 writes only "`C n²R²/r² ln(M/ε)`, `C` a constant", so the gap is
   invisible in the text. **The theorem is true with a larger constant.** The
   proved shape is `Arlib.MarkovChains.lvThreshold = 2⁵⁶n²(R²/r²)log(8M/ε²)`.

3. **§5 applies LS93 Cor 1.5 to *non-lazy* hit-and-run** with no laziness or
   spectral hypothesis. Counterexample: the swap kernel `P x = δ(¬x)` on `Bool` is
   reversible with conductance exactly `1` and `δ_true` is 2-warm, yet
   `d_TV = 1/2` forever while `√2·2^{-t} → 0` — failing already at `t = 2`.

4. **Cor 1.5 in `s`-conductance form is false on spaces with atoms** (scope error
   in reference [11]); harmless for hit-and-run, which is atomless, but it made a
   first draft of our own `s`-conductance theorem vacuous until repaired.

**Cousins–Vempala:** ~~the `(1d-2)` constant is provable at `1/(2√3) ≈ 0.289`, not
the paper's `ln 2 ≈ 0.693`, so the separation threshold grows by
`2√3·ln 2 ≈ 2.401`; see §0′.~~ **Superseded 2026-08-12 (later), see §0⁗.** It was
true of the route available when it was written (`ConcaveProfileIso.lean`, which
correctly calls the shortfall *slack in that argument, not an error in the paper*).
`Arlib/Convexity/OneDimSharp.lean` now proves `(1d-2)` at `√(2/π) ≈ 0.798`, which
**clears** `ln 2`, and the threshold penalty is gone. Kept here rather than deleted:
the finding list is append-only.

**And two of this repository's own docstrings were refuted:**

* `HitAndRunConductance.lean:39–60` called `hIso` "the genuine open gap" needing
  **Borsuk–Ulam**. Stale: `Arlib.exists_flat_cut_zero_pos` already takes arbitrary
  *signed* integrands, and the equality form bisects `g₁` alone by one-parameter
  IVT. The real residuals were (C) and (F). ~~both closed this session~~ —
  **corrected 2026-08-12, and this sentence was itself wrong when written.**
  **(F) is closed** (`Arlib.exists_needle_of_compact_convex`,
  `Convexity/LocalizationMeasurable.lean:226`). **(C) is an obstruction, not a
  gap** — see §0‴ below and `AUDIT.md` §0b. Neither statement below in the
  critical-path table said so; both are now corrected there.
* `SpeedyOverlap.lean` said polar decomposition about an interior point is
  something "Mathlib does not support today". False twice over: Mathlib has it,
  **and this repo already wraps it** at an arbitrary centre
  (`Arlib.MarkovChains.lintegral_polar_at`, `HitAndRun.lean:479`). It was also
  unnecessary — KLS 3.5 needs only `n`-homogeneity.
* Separately, `LocalizationAssembly.lean:195` pointed at
  `EuclideanSpace.volume_preserving_measurableEquiv`, **which does not exist** in
  this Mathlib.

### 0‴′. Four more against Cousins–Vempala, 2026-08-12 — and one retraction

Appended to the nine of §0′ ("Nine findings against the Cousins–Vempala paper") as
**10–13**; recorded here because §0″ is this file's paper-errors section. Every line reference below is to
`1409.6011/vol3_journal.tex` in this checkout and was re-derived from the `.tex`,
not from a summary. `\draftfalse` is set at `:38`, so `\ifdraft` bodies *are* in the
compiled paper; `\iffalse` bodies are not, and `\killtext` (`:7`) gobbles an older
duplicate of `lem:overlap`/`thm:speedyconductance` at `:667-745`.

10. **The derivation of `lem:1d-iso` — the source of the `ln 2` in `thm:iso` — sits
    inside an `\iffalse` block and is invisible in the compiled paper.** The lemma
    is `:439-444`; the block is `:446-465` and contains exactly its
    `\begin{proof}…\end{proof}`. It is the *only* `\iffalse` in the file, and
    `\ref{lem:1d-iso}` is cited exactly once, at `:506`. Two honest qualifications:
    the lemma is attributed (`\cite{KLS95}`), so suppressing a derivation is
    editorially defensible; and only `:448-455` proves the lemma — `:457-463`
    derives a different, `min`-form conclusion using an undeclared constant `c`.
    The bite is the step `E_f(‖x‖) ≤ √(E_f(‖x‖²)) = 1` at `:454`, which is what
    converts KLS95 Thm 5.1's `ln2/E_f(‖x‖)` into a flat `ln 2` and which quietly
    needs the second moment to be about the **origin**, not the mean. A reader of
    the printed paper sees `\iso = ln 2` with no derivation at all.
11. **The reduction at `:504-506` discards the Gaussian, and is both harder and
    weaker than necessary for the class it is applied to.** The Gaussian factor
    `γ((1−t)a+tb)` is used once — to make Brascamp–Lieb (`:407-416`) applicable and
    get `Var ≤ 1` — and from the word "Now" onward the argument is about an
    arbitrary isotropic log-concave function via `lem:1d-iso`, which knows nothing
    about `γ`. **Harder**: the route needs Brascamp–Lieb, *plus* an unproved and
    unstated rescaling claim ("by scaling down to increase the variance to exactly
    1, the isoperimetric coefficient can only go down" — one clause carrying the
    whole quantitative content of the step), *plus* KLS95 Theorem 5.1 through
    finding 10's suppressed lemma. **Weaker**:
    `Arlib.oneDim_isoperimetry_gaussianFactor_sharp`
    (`Arlib/Convexity/OneDimSharp.lean:518`) keeps the Gaussian and gets
    `√(2/π) ≈ 0.798` in three lines using **no** Brascamp–Lieb, **no** Hensley bound
    and **no** variance hypothesis — better than the paper's `ln 2 ≈ 0.693`.
    ⚠ **This is not an error in the paper.** `ln 2` is a true, weaker constant on
    their route. It is a route that is heavier and lossier than the class requires.
    (An earlier reading of this finding, dated by the `1/(2√3)` route, judged
    "weaker" false; `OneDimSharp` reversed it. §0″'s Cousins–Vempala bullet carries
    the same correction.)
12. **A truncation discrepancy the paper never reconciles, and it does not
    telescope.** The sampler's target is the Gaussian *restricted to*
    `K ∩ 4σ_i√n Bₙ` (`:228` in the algorithm, `:195` in `thm:ball-walk`; the
    truncation is not optional — `thm:speedyconductance` `:625` and `lem:filter`
    `:536` both require it). Every quantity in the volume analysis is over **all of
    `K`**: `f` (`:316-319`), `F(σ²)` (`:323`), `μ_i` (`:325`), `R_i` (`:1386`),
    `lem:fixed-var-bound` (`:1354`). `:1439` then asserts that each `Y_j^i` has
    expectation `E(W̄_i)`, i.e. the untruncated `R_i`. Two distinct defects: (a) each
    phase clips a Gaussian tail of mass `e^{−Ω(n)}` that is never stated or bounded
    anywhere; (b) **the radius `4σ_i√n` changes with the phase**, so the truncated
    ratios have mismatched domains and **do not telescope** to `F(∞)/F(σ_0²)`, which
    is what the estimate at `:243` needs. The loudest instance is a theorem at odds
    with its own proof: `thm:gauss-sampling` (`:181`) claims TV `ε` to the Gaussian
    restricted to `K` — **no ball** — and its proof (`:1017-1028`) establishes this
    by citing `thm:ball-walk`, whose target has the ball, without mentioning the
    difference. Nothing in the file bridges it.
13. **`eq:var-bound` (`:1442`; block `:1440-1443`) is written as an equality that
    assumes exact *within-phase* pairwise independence, which the paper elsewhere
    denies.** The arithmetic of the inequality is correct; the defect is the
    preceding equality at `:1441`, whose cross term `k_i(k_i−1)R_i²` is
    `Σ_{j≠l} E(Y_j)E(Y_l)`. The paper states the opposite twice — `:1454` ("Suppose
    that we had independence between samples…"), `:1479` ("However, subsequent
    samples are dependent…") — and the repair it then performs (`V_i`, `U_i`,
    `:1489-1592`, `lem:delta-ind`(c) at `:1487`) corrects only the dependence
    **across phases**. The `k` points of one phase come from a single ball-walk
    trajectory (`:224`), and `Y_j^i` is unbounded, so `lem:cov-bd` does not apply to
    it without the truncation the paper introduces only for the cross-phase terms.
    `eq:var-bound` is the sole input to `:1538`, on which the whole `U_i` argument
    rests. *Minor, same neighbourhood:* the union bound at `:1588` should read
    `3m/α`, not `3k/α` (it is over `i = 1…m`); harmless, since `α ≥ 4m/ε` is
    imposed separately at `:1561`. And `:1426` defines the samples as `X_j^i` while
    `:1430` writes `X_i^j`.

**Retracted before it was recorded — the `tν` vs `2kmν` "loss" is not one.**
`:1430` proves the coupling at `1 − tν` where `t` is the total sample count, and
`:1588` invokes it as `1 − 2kmν`. Since `t = m(k+1) ≤ 2km` for `k ≥ 1`, the
invocation is a factor-`≈2` **conservative** restatement of the paper's own lemma —
slack in the safe direction, not a factor lost. The coupling cost the paper actually
pays for dependence is priced separately and consistently at `3kmν` (`:1487`,
`:1493`). Recorded here only so the next pass does not re-raise it.

For reference, the headline is Theorem 1.1 at `:144-150`, complexity
`O(n³/ε² · log²n · log²(1/ε) · log²(n/ε) · log(1/p)) = O*(n³)`.

---

## 0′. Status, 2026-08-11 — supersedes §0 on the CV side

§0 below is still correct about `Ttc`: the volume oracle is discharged by
hit-and-miss Monte Carlo, the capstone does not wait on Cousins–Vempala, and the
price is **exponential in `n`**. What §0 says about *this* file's subject —
"`Ttc/Volume/CousinsVempala.lean` is exactly where it was" — is no longer true.
Here is the state, and it is deliberately unflattering.

### The headline is unchanged, and will stay unchanged until two things happen

> ⚠ **Overtaken by events, 2026-08-12 — and read the correction, not the
> headline.** This subsection used to open: "`cVol = O(n⁴)` **cannot** be
> substituted into `Ttc/Model/Theorem.lean`." That is no longer the state, and
> saying so plainly matters more than the two blockers below, which still stand.
>
> **What changed.** `Ttc.ttc` is now a four-ary `def` whose *definition* charges two
> **fixed** per-call prices, `Ttc.cvVolPriceAt` and `Ttc.hrSampPriceAt`, so
> `Ttc.ttc_volume_estimate`'s running-time conjunct does read `m·n⁴·(…)`. That is
> **legal arithmetic and a modelling choice** — `cVol`/`cSample` are unit
> multipliers in `Ttc.stepCost`, so *any* pair of naturals yields a bound of that
> shape, and at `0` the charged cost is identically `0`. And separately,
> `Ttc.ttc_runtime_mn4` (`Ttc/Exec/RuntimeMN4.lean`) states accuracy **and** an
> `m·n⁴` charged cost over `Ttc.ttcPoly`, a run that genuinely executes the
> Cousins–Vempala and hit-and-run oracles — under **38 named residual hypotheses**,
> ~~**six**~~ **five** of which have no route to a proof anywhere in this repository
> (`hphase_mean` left that list on 2026-08-12 — §0⁗ §3 and `AUDIT.md` §0a; the count
> of residual hypotheses is unchanged at 38).
>
> **What did *not* change, and is the whole point.** Neither statement proves that
> `TTC` runs in `O(m·n⁴)`. Blocker 2 below is still literally true of `Ttc.ttc`:
> its bundle is `Ttc.algOracles` over `Ttc.mcVol`, and the prices *that* run can be
> shown to pay are exponential. ~~Blocker 1 is untouched: `hloc` still blocks
> `thm:iso`~~ — **superseded 2026-08-12 (later): `thm:iso` is proved and `hloc` is
> not on its route at all (§0⁗ §1).** `hloc` remains open and §0‴ still correctly
> records that the a.e.-approximation route to it is an **obstruction**, not
> unfinished work; it is simply no longer what blocks the isoperimetric inequality.
> What blocks the runtime instead is §0⁗ §2's local-conductance floor.
>
> So the precise replacement for the old sentence is: **the `n⁴` shape has been
> written into the statement at fixed prices; what remains unproved is that the
> algorithm pays it.** `AUDIT.md` §1e's box and §0a are the audit surface for that
> distinction.

The two blockers, unchanged in substance:

1. **`thm:iso`'s inputs — now one, not four.**
   `Arlib/Convexity/SharpIsoperimetry.lean` proves `gaussianRestricted_isoperimetry`
   at exactly `d/σ` — the sharp constant — from four residual binders `hloc`,
   `hcombinatorial`, `h1d1`, `h1d2`. Three of those are now discharged outright, and
   `Arlib.gaussianRestricted_isoperimetry_concave`
   (`Arlib/Convexity/SharpIsoperimetryConcave.lean`) carries **`hloc` alone**.
   They were always hypotheses, never axioms, and every file involved is axiom-clean;
   but a theorem with an open binder still proves nothing about any algorithm, so the
   headline does not move until `hloc` closes. **Overtaken 2026-08-12 (later):**
   `Arlib.gaussianRestricted_isoperimetry_openClosed`
   (`Convexity/IsoOpenClosed.lean:854`) and
   `Arlib.gaussianIndicator_isoperimetry_measurable` (`Convexity/IsoIndicator.lean:476`)
   prove `thm:iso` **with no `hloc` and no localization binder of any kind**, at the
   price of open/closed parts and continuity/boundedness in the first case, and of
   `hRσ` plus `volume K ≠ 0` in the second. The headline still does not move, but for a
   different reason — §0⁗ §2.

   ~~The cost of the third discharge belongs with the statement:~~ **Closed 2026-08-12
   (later); `(1d-2)` is now available at `√(2/π) ≈ 0.798`, which clears `ln 2`, and the
   paragraph below is superseded — see §0⁗ §1.** ~~`(1d-2)` is available
   at `1/(2√3) ≈ 0.289`, not the paper's `ln 2 ≈ 0.693`, so the metric branch of the
   separation hypothesis reads `2√3·d ≤ ‖u−v‖` rather than `d/ln 2 ≤ ‖u−v‖` — a
   threshold larger by `2√3·ln 2 ≈ 2.401`. The conclusion `d/σ` is unchanged. When
   `thm:iso` is eventually wired into `conductance_speedyGaussian_ge`'s `hiso`, that
   factor propagates into the conductance constant and must be quoted there too.~~
2. **`Ttc/Model/Pseudocode.lean` instantiates `Vol_ED` as `Ttc.mcVol`.** Even a
   finished CV would have to be swapped in there. **Still true**, and it is why the
   headline's fixed `n⁴` charge is a modelling choice rather than a costing of the
   run: reading it as a claim about `Ttc.algOracles` would assert what the
   formalisation refutes. The swap *has* been performed, in a separate program:
   `Ttc.ttcPoly` (`Ttc/Exec/PolyRun.lean`), which is what `Ttc.ttc_runtime_mn4`
   speaks about — at the price of 38 residual hypotheses.

### The critical path, and where each link stands

`thm:iso` (tex:467) ← Localization + `hcombinatorial` (tex:497) + (1d-1)
(tex:498) + (1d-2) (tex:501) → `thm:speedyconductance` (tex:624) → `thm:volume`.

| Link | State |
|---|---|
| `thm:speedyconductance` | **proved** from `hiso`+`hoverlap` (`SpeedyConductanceSharp.lean`), polynomial constant `δ log 2/(640 σ √n)`. **Its `hiso` is for the density `1_K·ℓ` and is NOT the one §0⁗ discharges** — that one is for `1_K·γ_σ`, the Metropolis-filtered walk's law. `EllLogConcave.lean` records two obstructions to bridging them, both narrative rather than proved |
| Localization (A),(B) | proved — `LocalizationAffine`, `LocalizationTransverse` |
| Localization (D) chain closedness | **closed** — `LocalizationClosed.lean` |
| Localization (E) slab rigidity | **closed** — `NeedleSlab{,Affine,Chain}.lean` |
| Localization (C) lower semicontinuity — **no longer on the critical path to `thm:iso`** (§0⁗ §1), still open in itself | **an OBSTRUCTION, not an open problem** (2026-08-12) — `Convexity/LocalizationMeasurable.lean`. `exists_null_measurableSet_needleIntegral_eq_one` (`:442`) kills every a.e.-based route; `exists_transverse_oscillation_eq_one` (`:550`) kills weakening `Continuous` to `Measurable`. `hLoc` is **not** claimed false; the two routes available here are closed. §0‴ |
| Localization (F) transport + nondegeneracy — likewise off the `thm:iso` path | **CLOSED** (2026-08-12) — `Arlib.exists_needle_of_compact_convex` (`LocalizationMeasurable.lean:226`), the missing composition body ⟶ chain ⟶ needle, with `v ≠ 0` kept; witness `exists_needle_of_compact_convex_witness` (`:266`) |
| `hcombinatorial` unmixed half | **closed** — `IntervalReduction.lean` |
| `hcombinatorial` interleaved half | **closed** — `Arlib.oneDim_partition` (`LogisticIso.lean`), for arbitrary measurable partitions, no side condition |
| (1d-1) | **closed for concave profiles** — `Arlib.kls38_concave` (`KLS97Lemma38.lean`), at the paper's `4√n`; `kls38_affine` recovers the printed form |
| (1d-2) | **CLOSED AT `√(2/π) ≈ 0.798`, which BEATS the paper's `ln 2 ≈ 0.693`** (2026-08-12, later) — `Arlib.oneDim_isoperimetry_gaussianFactor_sharp` (`Convexity/OneDimSharp.lean:518`), weakened to `ln 2` by `oneDim_isoperimetry_gaussianFactor_logTwo` (`:572`) along the machine-checked `log_two_le_sqrt_two_div_pi` (`:554`). ~~closed at `1/(2√3)` — `Arlib.oneDim_isoperimetry_gaussianFactor_unconditional`, on `Arlib.brascampLieb_oneDim`~~, which was a factor `2.401` short and is superseded. **This row was the whole gap**: the separation threshold in `thm:iso` is `d/c` for the `(1d-2)` constant `c`, and the consumer writes `d/ln 2`. §0⁗ |
| `hoverlap` at separation `δ/√n` | **`cor:overlap` at `δ/√n` is now PROVED, under `ℓ`-comparability** (2026-08-12) — `overlap_speedyWalk_sqrt_of_ell_comparable` (`OverlapSqrt.lean:527`) at constant `12`, from KLS95 Lemma 3.5 at `δ/√n` (`kls_lemma35_at_sep_sqrt_dim`, `LensMin.lean:423`, `min` form, no hypothesis beyond the paper's). The comparability hypothesis `d_ℓ(u,v) < 1/3` is Cousins–Vempala's own but is **load-bearing**: `exists_ell_not_comparable_at_sqrt_dim_counterexample` shows the known `δ/√n` counterexample survives by violating it at `d_ℓ > 0.95`, and `lem:f-dist` — which would derive it from `d_h < 1/4` — is **not proved**. ⚠ **The `√n` is real at a fixed kernel step, but `n⁴` does not follow.** ~~the blocker is a missing *Metropolis* overlap lemma at `δ/√n`, plus `hcomp`/`hiso`, not a step-size cap~~ — **superseded 2026-08-12 (later):** the Metropolis overlap lemma at `δ/√n` landed (`metropolisGaussian_overlap_sqrt_of_convex`, `MetropolisOverlapSqrt.lean:164`) and `hiso` is discharged for its conductance corollary (`OneDimSharp.lean:1040`). `hcomp` still binds the **speedy** route, and the new blocker is the local-conductance floor. See §0‴ **and §0⁗** |
| KLS95 Lemma 3.5 at `δ/√n` | **CLOSED, `min` form** — `kls_lemma35_at_sep_sqrt_dim` at `1/40`, sharpened to `1/8` by `kls_lemma35_at_sep_sqrt_dim_sharp` (`OverlapSqrt.lean:364`) and to **`1/4`** by `kls_lemma35_at_sep_sqrt_dim_quarter` (`LensSharp.lean:569`), all three at identical binders. The **`max` form is FALSE** (`exists_halfspace_max_lt`), so the `min` is essential, not a convenience. `1/(e+1)` is **neither achieved nor refuted** — the `0.2555` ceiling argument in `LensSharp.lean:88-104` is unformalised prose about that proof skeleton |
| `thm:iso` — continuous case | **CLOSED, UNCONDITIONALLY** (2026-08-12, later) — `Arlib.gaussianRestricted_isoperimetry_openClosed` (`Convexity/IsoOpenClosed.lean:854`), no localization binder. Price: `S₁,S₂` open, `S₃` closed, `h` continuous, bounded and integrable; threshold `2√3·d`. §0⁗ |
| `thm:iso` — indicator density, measurable parts | **CLOSED** — `Arlib.gaussianIndicator_isoperimetry_measurable` (`Convexity/IsoIndicator.lean:476`), `S₁ S₂ S₃` merely measurable, for `1_K·γ_{σ²}`. Two extra hypotheses: `hRσ : √3·R ≤ 2σ√n` and `volume K ≠ 0`. §0⁗ |
| `hiso` for the **Metropolis** conductance bound | **DISCHARGED** — `Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo` (`Convexity/OneDimSharp.lean:1040`) is that binder character for character; `conductance_metropolisGaussian_sharp_sqrt_ge_of_convex` (`:1073`) is the corollary, adding only `hRσ`. **Covers exactly one binder** — the `δ/n` version and the whole speedy family still carry theirs |
| Metropolis `cor:overlap` at `δ/√n` | **CLOSED** — `metropolisGaussian_overlap_sqrt_of_convex` (`Continuous/MetropolisOverlapSqrt.lean:164`), constant `20`. Needs no `ℓ`-comparability; needs `hell` + `hfloor` instead |
| Metropolis mixing, isoperimetry-free | **CLOSED** — `mixesWithin_lazy_metropolisGaussian_at_operative_step_of_convex` (`Continuous/MetropolisMixingUncond.lean:130`): `4·5120²·n²·(log M + 2 log(1/ε))/(log 2)² + 1` steps suffice. "Unconditional" = no `hiso`; `hell`, `hfloor`, `hRσ`, geometry and warm start remain, and the plain-chain variants still carry `hpsd` |
| **the `hell`/`hfloor` pair, on the oracle's class** | ⚠ **REFUTED — this is the new blocker.** `metropolis_ell_floor_unsatisfiable_on_cube` (`Continuous/EllFloor.lean:402`): for `n ≥ 3` no `θ` satisfies both on `[-1,1]ⁿ`, at any step size; `:483` is the `(1−1/n)ⁿ` shape at `n ≥ 5`; `:417` attributes the failure to the floor alone. The cube contains the unit ball, so it is in the consumer's class. Not a refutation of the conductance theorem — a proof that it is **vacuous** where the oracle needs it. What survives is the average: `isSmooth_of_ball_subset` (`:549`) |

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
| §4.2 Warm start (`:747–826`) | ~80 | `M(Q₀,Q)` warmness propagation | **the phase-to-phase step is now PROVED** — `Arlib.GaussianCooling.isWarm_coolLaw_succ_exp` (`Convexity/GaussianCooling/WarmChain.lean`): each cooling phase is **`e`-warm** for the next, free of `n`, under `σ²ᵢ₊₁ ≤ (1 + 2/n)σ²ᵢ`, in the sup-ratio sense `Arlib.IsWarm` uses. Crux `chain_succ_le_pow_mul` (`Z(i+1) ≤ λⁿZ(i)`) is the rescaling `x ↦ λx`, shorter and slightly more general (star-shapedness about `0`) than the paper's polar/cone argument. ⚠ This is the *warmness* half only: `hphase_mean`/`hphase_var` and §4.1's conductance are untouched, and `Warmness.lean` records the paper's own `(1−1/n)^{−n/2} ≤ √e` step (`vol3_journal.tex:787`) as **false for every `n ≥ 2`** — the lemma is true, the displayed computation is not |
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
