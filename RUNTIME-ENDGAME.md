# TTC end-to-end: where we are, and the immediate work

> ## ⚠ Current state, 2026-08-19 — read this before the body
>
> The repository has **one algorithm and one theorem**, both at the oracles the paper
> specifies.
>
> * **`Ttc.ttc atoms φ ε δ`** (`lean/Ttc/Model/Theorem.lean`) is the law of one run at
>   Cousins–Vempala Gaussian cooling for volume
>   (`TtcSlowRuntimePerPhase.slowPerPhaseImplementation.algorithm n`) and the hit-and-run /
>   ball-walk hybrid for sampling (`canonicalCappedPolyHybridPlugin`).  A draw
>   `r : ℝ × ℝ≥0∞` is one execution: `r.1` the estimate, `r.2` the membership queries spent.
>   It is total, via a junk branch off the side condition `Ttc.TtcInputs`.
> * **`Ttc.ttc_volume`** is the only theorem in that file: accuracy in the probability monad
>   (`1 - δ ≤ Pr[r ← ttc …; r.1 ∈ relErr ε (volSol …)]`) and **expected** query cost
>   (`∫⁻ r, r.2 ≤ volume envelope + sampler envelope`), ten binders, axioms
>   `[propext, Classical.choice, Quot.sound]`.
>
> **Deleted, not weakened:** the reference-oracle chain — hit-and-miss Monte Carlo for volume,
> the lazy ball walk charged at a fixed per-call price for sampling — together with
> `Exec/{PricedHeadline,SamplePrice,TheoremPoly,RuntimeMN4,SampPricePoly,SpeedySamplerChain,
> OperationalSpeedySamplerAudit}` and `Witness/FixedPriceTwoCube`.  There are no price binders
> anywhere and nothing is charged at a number it is not proved to pay.
>
> **Four things to carry into the body, which predates this change:**
>
> 1. **The cost conjunct is an expectation in membership-query units**, at `Õ(m·n⁴·ρ⁶/ε²)` —
>    *not* the paper's `O(m·n⁵·ρ²·r_max)`, and not in the same units until the `⌈n·rfac⌉₊`
>    charge of `ttc_volume_runtime_perPhase_ops` is applied.  See `PLAN-SHAPE.md` §5 and
>    `PAPER-CLAIMS.md`.
> 2. **It is not uniform in the dimension.**  At `1100 ≤ n` the sampler is hit-and-run.  For
>    `21 ≤ n < 1100` it is the ball walk, with `4 ^ n` — bounded, so a constant rather than an
>    asymptotic obstruction, but an astronomical one.  This is now machine-checked, not
>    asserted: `#inClosure Ttc.mixSteps in Ttc.ttc` in `Ttc/Audit/ClosureCheck.lean` fails the
>    build if the ball walk ever silently leaves.  `PLAN-SPHERECAP.md` scopes the one lemma
>    that removes it.
> 3. **The four-file audit surface no longer covers the headline, deliberately.**  Naming the
>    constructed oracles reaches 637 constants across 108 modules.  What is still checked, and
>    still fails the build on drift, is `#modelClosure Ttc.ttcAlgOutput` — the *specification*.
>    A reader checking what the algorithm *is* need not leave `Model/`; a reader checking what
>    was proved about *running* it must read the construction.  `Ttc/Audit/ClosureCheck.lean`
>    argues the trade in place.
> 4. **Non-vacuity, both new and both required reading (`CLAUDE.md` §11).**
>    `Ttc.EnvelopeFinite.ttc_volume_bound_ne_top` proves the cost bound is not `⊤` — in
>    `ℝ≥0∞` it would otherwise hold of every run — and `Ttc/Witness/FullTwoCube.lean` exhibits
>    data meeting all ten binders at `n = 21`.
>
> **`Ttc.ttc` is defined in `Model/Theorem`, not `Model/Pseudocode`.**  `Ttc/Exec/` imports
> `Pseudocode` (it is built against `algIndex`, `algAtoms`, `algBlock`), so `Pseudocode` cannot
> name the construction without a cycle.  `Pseudocode` states `alg:ttc` with the oracle bundle
> as an argument and chooses no oracle; `Theorem`, the only `Model/` file downstream of the
> construction, fills it in.
>
> **Everything below this box predates 2026-08-19.**  It names declarations that no longer
> exist — `ttc_volume_estimate` and its `_parametric` / `_quartic` variants, `ttcCharged`,
> `ttcRun`, `algOracles`, `cvVolPriceAt`, `hrSampPriceAt` — and describes an architecture with
> two headlines and two oracle pairs.  Read it as the record of how the development got here,
> not as a description of what is in it.  The `.lean` docstrings *were* brought up to date and
> are the current source of truth.



Written 2026-08-17 against the working tree at `3ad3afd` + three uncommitted files
(`CVSlowCanonicalPositivePathFactorization`, `CVSlowCanonicalUniformParameters`,
`CVSlowCanonicalStreamOperational`, all imported by `Ttc.lean`, all built green:
`lake build` on those three returns 3901 jobs, exit 0, axioms
`[propext, Classical.choice, Quot.sound]`).

This supersedes `END-TO-END-PLAN.md` as the *live* plan. That document's Phases 0–5 are
either done or dead; its value now is history. `AUDIT.md` §0f's "what remains" list is
also stale in its top item — see §1 below.

---

## 0. The two halves of the paper, and their status

| Paper | Lean | Status |
|---|---|---|
| `thm:volumettc` (accuracy) | `Ttc.ttc_volume_estimate_accounted` (`Ttc/Model/Theorem.lean:208`) | **DONE, unconditional.** Over TTC's own inputs `(atoms, φ, ε, δ)`; residual input conditions are only `hφ : φ.IsPositive` and `hpos : 0 < volSol`. Both oracles constructed, neither assumed. |
| `thm:runtime` (`O(m n⁵ ρ² r_max)`) | `Ttc.TTCUnconditionalExplicitRuntime.ttc_volume_estimate_operational_sourceSharp_fullTrajectory_cvShapeRuntime` (`:582`) and `Ttc.CVCappedRadialLogInterface.ttc_volume_estimate_of_cvCappedRadialLogExpectedImplementation` (`:79`) | **One hypothesis left**, plus a shape gap. See §1–§3. |
| `thm:decompose` (exponential decomposition) | — | **not formalised at all**, and not planned. |

The accuracy half is finished mathematics. Everything below is the runtime half.

### The single remaining mathematical obligation

Both runtime capstones are conditional on exactly one thing, and it is the same thing:

> **Cousins–Vempala Theorem 1.1 as a one-run certificate** — for each input
> `a = (K, ε, p)` with `K` convex, `B(0,1) ⊆ K`, `vol K < ∞`, a law on runs with
> (i) `E[cost] ≤ (the declared query budget)` and (ii) `Pr[value ∈ (1±ε)·vol K] ≥ 4/5`.

Packaged as `Ttc.CVSourcePolynomialCutoffCapstone.SourcePublicOneRunCertificates`
(`Ttc/Exec/CVSourcePolynomialCutoffCapstone.lean:307`, five fields) or, in the
reference-TV form the construction actually targets,
`Ttc.CVRadialLogEnvelope.RadialLogSourcePublicReferenceTVCertificates`
(`Ttc/Exec/CVRadialLogEnvelope.lean:471`, seven fields — same content plus a `path_tv`
at `1/40` against a retained reference law).

`TTCUnconditionalExplicitRuntime.lean:490` states this in its own docstring: *"The only
non-input premise is the volume oracle's common-law certificate; once CV Theorem 1.1
supplies that construction, this statement becomes the direct unconditional TTC
capstone."* That is accurate.

**The sampling oracle is already closed.** `canonicalCappedPolyHybridPlugin` takes no
sampler certificate; the per-endpoint price is `canonicalHybridSamplerQueryBound`
(`TTCSourceSharpOperationalFinal.lean:335`), whose step count is
`Ttc.hybridTransitionBound` (`Ttc/Sampler/ConstructHybridUncond.lean:199`) —
`2^66·n²·R²/r²·log(8M/ε²)` on the hit-and-run branch, with a `lowDimBallWalkEnvelope`
fallback below `n = 1100`. So `AUDIT.md` §0f item 1 ("sampler existence… everything
else reduces to this") is **stale**: the sampler exists, and the remaining item is the
volume oracle. `HitAndRunTheorem11Input` is no longer on the critical path.

---

## 1. The construction chain, top to bottom

Reading upward from the capstone, each arrow is an existing named declaration:

```
Ttc.CVCappedRadialLogInterface.ttc_volume_estimate_of_cvCappedRadialLogExpectedImplementation
  ↑  CVCappedRadialLogExpectedImplementation                        [NO INHABITANT — the goal]
  ↑  cvCappedRadialLogExpectedImplementationOfReferenceTVFamily     (CVCappedRadialLogExpectedImplementation.lean:60)
  ↑  RadialLogSourcePublicReferenceTVCertificates                    [∀ n]
  ↑  radialLogSourcePublicReferenceTVCertificates_of_operationalColdHotAudit  (CVGaussianHybridWeightedCertificate.lean:1518)
  ↑  operationalColdHotRadialAuditOfOneRunCertificates                        (:1497)
  ↑  ∀ a, ∃ reference, SourceReferenceTVOneRunCertificate …          [∀ input]
  ↑  exists_sourceReferenceTVOneRunCertificate_slowCanonical_of_weightedData
       (Ttc/Exec/CVSlowCanonicalRobustCertificate.lean:160)          ← THE FRONTIER
```

The frontier theorem is proved and axiom-clean. **It is consumed by nothing.** It has
~28 binders, and discharging them is the whole of the immediate work. The last three
weeks of `CVSlow*` files have been peeling them off one at a time.

The `n < 21` branch is already handled: `sourceExpectedAlgorithmWithExactBelowTwentyOne`
(`CVSourceDimensionGuardTwentyOne.lean:20`) splices in
`ExpectedQueryVolumeAlgorithm.exactExpected` at zero declared query cost, and the
capstone carries `hn : 21 ≤ n` accordingly. Nothing to do there.

---

## 2. ⚠ A shape mismatch the docs do not flag

`CVSlowCanonicalRuntimeComparison.slowCanonicalRetainedScalar_ennreal_le_publicShape`
(`:179`) proves the slow schedule's aggregate scalar is bounded by

```
cvSlowCanonicalCappedRadialShape n m k R2 eps p s0 N
  = cvCappedRadialLogComplexityShapeClipped n R2 eps p
      * max 1 (slowCanonicalRetainedRealEnvelope n m k eps √R2 s0 N)
```

but `CVCappedRadialLogExpectedImplementation.expectedBound_le` demands
`≤ runtimeConstant * cvCappedRadialLogComplexityShapeClipped n R2 eps p`
with `runtimeConstant : Real` **fixed, independent of `n, m, k, R2, ε`**. The budget it
ultimately has to fit inside is Cousins–Vempala's Theorem 1.1 shape verbatim
(`sourceOneRunQueryEnvelope`, `CVSourcePolynomialCutoffCapstone.lean:50`):

```
runtimeConstant · max(R²n², n³)/ε² · log²n · log²(1/ε) · log²(n/ε)
```

— note it mentions neither `m` nor `k`. The slow overhead
`slowCanonicalRetainedRealEnvelope` is `k·m·10·retryEnvelope·deadlineEnvelope·2e`, and
`deadlineEnvelope` carries `slowCanonicalGeometryEnvelope n m k eps N`. So absorbing it
means proving that the *phase count* `m` times the *stream count* `k` times the
per-phase deadline fits under the `n³/ε²·polylog` already in the budget — with the phase
count itself `n`-dependent (`slowOperationalPhases n N`), that is prima facie a strict
loss, and the construction did not attempt it: `slowCanonicalRetainedScalar_le_publicShape`
states the bound *as* shape × overhead, and the file's docstring says why —
*"the uniformly slow schedule is a correctness route, not the faster CV schedule from
the paper."* Bounding the overhead by a constant is therefore an inequality someone would
have to prove, not a wiring step, and the exponent arithmetic says it is false.

So the chain in §1 **does not close as drawn**. One of two repairs is needed, and this
choice should be made before any more binder work:

* **(2a) A slow-shape interface — cheap, honest, weaker.** Mirror
  `CVCappedRadialLogInterface` at `cvSlowCanonicalCappedRadialShape`: a new
  `CVSlowCappedRadialLogExpectedImplementation`, its `ofExpectedBound` constructor, and
  a transport theorem `ttc_volume_estimate_of_cvSlowCapped…`. Roughly the same size as
  `CVCappedRadialLogExpectedImplementation.lean` + `CVCappedRadialLogInterface.lean`
  (~200 lines total), and it makes the resulting TTC runtime bound *polynomial but
  visibly worse than the paper's*.
* **(2b) Speed the schedule up to the CV rate.** Replace the uniformly slow schedule
  with the geometric one, so the overhead collapses into a constant. This is real
  mathematics (the per-phase deadlines have to shrink), and it is what the paper's
  exponents actually need.

Recommendation: **do (2a) first** — it turns "conditional on an uninhabited structure"
into "unconditional, at a stated worse exponent", which is the first genuinely
end-to-end runtime statement this repository would have. Then attempt (2b) as a
sharpening. Doing (2b) first risks another month with nothing closed.

---

## 2b. PROGRESS — what landed on 2026-08-17

Option (2a) was taken, and generalised: rather than cloning the interface at one more fixed
shape, the **shape, the admissibility predicate and the per-call declared radius are now all
parameters**. Every file below is `lake build` green and axiom-clean at
`[propext, Classical.choice, Quot.sound]`.

| File | What it gives |
| --- | --- |
| `Ttc/Exec/CVShapedExpectedImplementation.lean` | `CVShapedExpectedImplementation Adm shape`, and the TTC transport `ttc_volume_estimate_of_cvShapedExpectedImplementationAt` at an arbitrary shape, admissibility predicate and per-call declared radius `R2j`. `ofCapped` shows the existing capped interface is the instance at `(cvAdm, cvCappedRadialLogComplexityShapeClipped)`, so nothing was forked. |
| `Ttc/Exec/CVEffectiveSourceReferenceFamily.lean` | `EffectiveSourcePublicReferenceTVCertificates` — the radial-log certificate family with the per-input **effective runtime constant** freed from `radialLogEffectiveRuntime`. `cvShapedExpectedImplementationOfEffectiveFamily` turns any overhead envelope `OV ≥ 1` into an implementation at shape `cvComplexityShapeClipped · OV`. `ofRadialLog` shows this strictly generalises. |
| `Ttc/Exec/CVEffectiveTotalise.lean` | `effectiveSourcePublicReferenceTVCertificates_of_valid` — certificates on *valid* inputs only suffice; degenerate inputs get a point mass, zero cost, zero value. This step was missing entirely, and without it the existing radial-log audit constructor is uninhabitable (it demands a `4/5` accuracy certificate on non-convex bodies). |
| `Ttc/Exec/CVSlowCanonicalAccuracyBudget.lean` | `hbeta`, `haccuracyBudget`, `hbetaDef` discharged; `slowAccuracyRequested_le_of_half` gives the internal-`eps` → target-`eps` conversion. |
| `Ttc/Exec/CVSlowCanonicalHopAssembly.lean` | `exists_slowCanonicalHop_literal` — `hop`/`hVliteral`/`htau`/`hmixError` with all twelve factorization binders gone. |
| `Ttc/Exec/CVSlowCanonicalMomentBinders.lean` | `hWint`/`hW2int`/`hWEpos`/`hrawSecond`/`hfactor0`/`hphaseMoment`/`hprefix`, plus `htailBudget`. See the two findings below. |
| `Ttc/Exec/TtcRadialGeometry.lean` | `ttcRadialR`/`ttcRadialN` and the three interface conditions; plus `cvSecondMoment_le_sq_of_subset_closedBall` and the bound at TTC's literal call body. |
| `Ttc/Exec/TtcCallBodyBounded.lean` | `callRadius`, `callBody_subset_closedBall`, `cvAdmBounded_callBody`. |
| `Ttc/Exec/TtcCallBallAdmissible.lean` | `cvAdmBall_callBody` — the `hadm` binder at the quantitative predicate, with the declared radius the *containment* radius rather than the second moment. |

### Two findings that changed the construction

* **`slowUniformC = 4` was not derivable and is now `2`.** The R-aware joint tail floor's
  branch `1/(6·exp(R²/2s₀))` yields `floor·(exp(R²/2σᵢ)·15) ≤ 5/2`, while
  `phaseMomentSlackSeven` at `C = c` needs `((7−c)/2)·ratio²`. At `c = 4` that is
  `(3/2)·ratio² < 5/2`, so `htailBudget` fails; at `c = 2` it is exactly `(5/2)·ratio²`,
  which is what `slowCanonicalJointTailFloor_moment_le` proves. Found by discharging the
  binder, not by inspection.
* **The frontier's four moment binders are `∀ j`, but the analysis only gives `∀ j ≤ m`.**
  At `j > m` the phase family is not the constant `1` — `coolRatio_of_ge` makes it the
  *indicator of `interior K`* at the time-`j` state — so `hWEpos` becomes a positive-mass
  claim. The fix under way is to close the tail indices from stationarity of the schedule
  past the active range, not to weaken the frontier.

### Second round — the frontier's binders are now all derivable

| File | What it gives |
| --- | --- |
| `Ttc/Exec/CVSourceReferenceWeaken.lean` | `SourceReferenceTVOneRunCertificate.weaken_of_subset` and the budget-monotonicity lemmas in `rc`, `R`, `eps`. Needed because the producer's certificate parameters and the consumer's differ in every slot. |
| `Ttc/Exec/CVSlowEffectiveOverhead.lean` | `slowOverhead`, `slowEffective`, `slowOverhead_mono`, and **`slowCanonical_hscalar`** — the cost binder, discharged. The `eps = 0` and `n = 0` degenerate branches are closed by explicit lemmas, not excluded by side conditions. |
| `Ttc/Exec/CVSlowCanonicalTailPhases.lean` | The `j > m` indices, closing the `∀ j` gap for **all five** affected binders. |
| `Ttc/Exec/CVSlowOneRunValid.lean` | `exists_slowOneRunCertificate_canonical` — the frontier instantiated at the canonical choices. Everything is discharged except the five moment binders (now supplied by the file above) and the cost binders. |
| `Ttc/Exec/TtcCircumRadius.lean` | `circumR` and `circumR_sq_le_of_cvAdmBall` — see the finding below. |

### Three more findings

* **The radial parameter must be the circumradius.** Two obligations pull opposite ways:
  the interface needs `(radialR K)² ≤ R2` (small), the frontier needs `K ⊆ closedBall 0 R`
  at `R = radialR K` and its cost budget is *increasing* in `R` (large). A second-moment
  radius fails the second — a body of finite volume and finite second moment need not be
  bounded. `Metric.diam K` fails the first: `K ⊆ closedBall 0 r` gives only `diam K ≤ 2r`,
  hence `(diam K)² ≤ 4·R2`. The circumradius `sup{‖x‖ : x ∈ K}` satisfies both on the nose.
* **The declared radius should be the containment radius, not the second moment.**
  `CVAdmissible K R2` only asks that `R2` bound the second moment *from above*, so declaring
  the larger radius is legal, and it makes the per-cube envelope read outer-radius² — the
  paper's own `ρᵢ`, rather than a global normalisation.
* **The tail indices closed by an exact identity, not an approximation.** Past the active
  range the slow canonical schedule is literally `Kernel.const _ (slowStationaryTail …)`,
  and `slowStationaryTail` puts the *score* coordinate at the origin. Since `ball 0 1 ⊆ K`
  gives `0 ∈ interior K`, the tail indicator is `1` almost surely — no measure-theoretic
  bridge and no quantitative mass bound were needed. The clipped family is `1` there too,
  because `correctedAlpha m eps ≥ 100000` makes the clip inactive.

### The generic half is DONE — `Ttc.TtcShapedRuntime.ttc_runtime_of_effectiveCertificates`

`Ttc/Exec/TtcShapedRuntimeFromCertificates.lean`, axiom-clean at
`[propext, Classical.choice, Quot.sound]`. It proves TTC's accuracy **and** query-cost
bound, both over one law, from nothing but:

* an overhead envelope `OV ≥ 1`;
* a per-input effective constant dominated by it on `cvAdmBall` bodies;
* **per-input one-run reference-TV certificates on the valid inputs only.**

It mentions no schedule, no Gaussian cooling, no phase count. Everything between the
construction and the capstone — totalising over degenerate inputs, the expected-query
oracle, the confidence amplification, the per-cube sum, the transport to TTC's own law — is
discharged inside it. The declared radii are per-cube outer radii, so the envelope reads
the paper's per-polytope `Rᵢ/γᵢ` rather than a global normalisation.

**What remains is exactly one obligation**: instantiate its `H` binder from
`Ttc.CVSlowOneRunValid.exists_slowOneRunCertificate_canonical`.

### Third round — the cost side, and three constant repairs

The cost binders `hsteps`/`hretries`/`hscalar` needed three separate repairs, each found by
*computing* rather than by inspection. None was visible from the statements.

1. **`slowUniformC = 4` → `2`.** The R-aware joint tail floor's branch yields
   `floor·(exp(R²/2σᵢ)·15) ≤ 5/2`, while `phaseMomentSlackSeven` at `C = c` needs
   `((7−c)/2)·ratio²`. At `c = 4` that is `(3/2)·ratio² < 5/2` — not derivable. At `c = 2` it
   is exactly `(5/2)·ratio²`.
2. **Share floor `2/33` → `1/18`** (`Ttc/Exec/CVSlowUniformShareBounds.lean`). The existing
   caps were proved at `relativePhaseSlack … (fun _ ↦ 3)`, giving share `2r²/(33·e^{2x})`;
   the frontier's `hslackDef`/`hboundDef` *force* the Uniform pair, whose share is
   `r²/(18·e^{2x})`. Since `2/33 > 1/18`, the old floor was not below the share the theorem
   needs, so `hsteps`/`hretries` had no provider at the forced parameters. The new floor
   closes exactly, with no slop.
3. **The cap argument triple is shifted three ways** from the overhead's. Reading the
   producer's binders: the caps must be taken at `(m + 1, correctedRuntimeSamples m epsP,
   epsP / 2)`. None of the three shifts absorbs by monotonicity in the useful direction —
   phase-count and accuracy shifts both make the cap *larger*. Closed by the `Q` layer in
   `Ttc/Exec/CVSlowEffectiveOverhead.lean` (`slowUniform_hscalarQ_circumR`), whose caps sit
   at exactly that triple.

Two further pieces the assembly needs, both landed:

* `Ttc/Exec/CVBudgetEpsAbsorb.lean` — the budget is *decreasing* in the accuracy slot, so
  moving from the realised accuracy to the requested one runs against monotonicity. Because
  the construction is run at half the target, the realised accuracy is `≥ eps/2`, and the
  loss is the absolute constant **64** (`4·(1+log 2)⁴ ≤ 64`).
* `Ttc/Exec/CVSlowAccuracyStrict.lean` — `requested < 1` does **not** follow from
  `requested ≤ epsIn` at `epsIn = 1`; the half-accuracy run buys `≤ 11/16·epsIn`.

### Closing the exponent gap — three levers, all three answered (2026-08-17, later)

The capstone below is unconditional but its envelope carries the uniformly slow schedule's
overhead. Three levers were investigated; each produced a machine-checked result, and two
of them corrected a *lossy bound* rather than trading one design for another.

**Lever 3 — the score transport bound was loose by a factor `n` in the exponent.**
`coolRatio i x = coolWeight (i+1) x / coolWeight i x = exp(‖x‖²/2·(1/σᵢ − 1/σᵢ₊₁))`, which at
rate `1/n` is `exp(‖x‖²/(2σᵢ(n+1)))`. The development's
`phaseScoreTransportBoundSqSeven R σ i = exp(R²/(2σᵢ))²·15` **drops the `1/(n+1)` entirely** —
at the cold end `exp(16nR²)` against a truth of `exp(8R²)`.
`Ttc/Exec/CVSharpScoreTransport.lean` proves the sharp bound and carries it to the share
floor: `1/(18·e^{16nR²}) → 1/(18·e^{16R²})`, the `n` gone from the exponent and the floor now
`n`-free. Consequence: `q² = 16 + 64R²/n`, so the truncation radius is `O(1)` for `n ≳ R²`
rather than `Θ(R)`.
*Care taken:* the sharp bound is genuinely **false at the terminal phase** (`coolWeight m σ m = 1`,
so the ratio really is `exp(‖x‖²/(2σᵢ))`); `coolRatio_le_of_last_of_sq_le` handles it separately
(`R² ≤ σᵢ ⟹ ratio ≤ e^{1/2}`, and `e < 15`), so the sharp *value* dominates at every phase.

**Lever 2 — the warmness recursion is genuine; its *bound* was not.**
The hypothesis that the compounding is an accounting artifact is **false at the kernel level**:
the phase kernel keeps accepted samples and refreshes only the unresolved branch, so warmness is
inherited by running the chain. `CVWarmBudgetRecurrence.lean:13-15` records a prior author
rejecting exactly that inference. An unconditional refresh would discard every accepted sample
and the schedule would never advance.
But `recursiveWarmBudget_le_product` bounds an **affine** recurrence `W_{i+1} = a_i W_i + f_i` by a
**product** `W₀·∏(a_j+f_j)`, pushing the refresh normaliser `F` inside the phase product. Solving
the affine recurrence directly gives `W_i ≤ A^i·(W₀ + i·F)` — **`F` paid once, not `m` times**.
`Ttc/Exec/CVRefreshWarmRoute.lean`: payload `m·(n·log 4R + 1/(32s₀))` → `m·log A + log(m+1) +
1/(32s₀) + n·log 4R`. Honest caveat, encoded in `log_slowWarmBudget_toReal_le_min`: the new
envelope is *worse* at small `i`, so both are kept.

**Lever 1 — the cooling rate was never pinned by the variance.**
`phaseVarBudget n α = (n+1)·α²/(1−α²)` (`IndicatorVariance.lean:151`) is `Θ(n·α²)`, not `Θ(n·α)`.
At `α = 1/√n` it is exactly `(n+1)/(n−1) ≤ 3` — a constant — and `variance_le_exp_indicator`
requires only `0 ≤ α < 1`. `Ttc/Exec/CVFastRateSchedule.lean` proves the phase count
`< 2√n·log(N/s₀) + 1` against the slow route's matching lower bound `≥ n·log(N/s₀)`, so
`Θ(n log)` → `Θ(√n log)`, both sides machine-checked.
*The honest accounting:* under exact provisioning the total `m·k` is **rate-invariant** — cutting
`m` by `√n` raises the per-phase budget from `1/(n−1)` to `≈1`, so `k` rises by `√n`. The win is
confined to costs that multiply `m` but not `m·k` (deadline payload, retry cap, refresh). But the
repo's *current* `correctedRuntimeSamples m eps = ⌈10⁵(m+1)/ε²⌉+1` is `k ∝ m`, over-provisioned by
`n` at rate `1/n` and exactly right at `1/√n`, so keeping it gives `m·k = Θ(n²L²/ε²) → Θ(nL²/ε²)`
— an `n`-fold improvement **in the proved bound**.

#### Making them operative — outcome per lever

* **Lever 2 — OPERATIVE.** `Ttc/Exec/CVSlowRefreshSteps.lean` builds the refresh analogue of
  `CVSlowActualSteps`, and `Ttc/Exec/TtcSlowRuntimeUnconditional.lean` now consumes
  `slowMinStepsEnvelope = min (slowActualStepsEnvelope …) (slowRefreshStepsEnvelope …)` via
  `slowCanonicalSteps_min_le`. The capstone is **still unconditional and still axiom-clean** at
  the improved envelope.
  *Why `min` and not the refresh form outright:* the refresh envelope does **not** dominate
  unconditionally. Writing `A = (slowAcceptedCap L).toReal` and `F = (slowFallbackEnvelope …).toReal`,
  refresh ≤ product iff `(m+1)·Aᵐ·F ≤ (A+F)ᵐ`, which **fails at `m = 0` and `m = 1`** (at `m = 1` it
  demands `2AF ≤ A+F`, false for all `A,F ≥ 1` bar `A = F = 1`, and `A ≥ 32e` whenever `L ≥ 1`). It
  holds in the operative regime where `F = e^{1/(32s₀)}(4 max 1 R)ⁿ` is exponential in `n`. The
  `min` is unconditionally at least as good as the status quo and needs no extra hypothesis.
* **Lever 1 — NOT WORTH DOING, and now machine-checked why.** The rate is not pinned by the
  variance but by the **warm-factor layer**: `acceleratedSeedWarmFactor n (1+α) = 2·√(1+α)ⁿ`, and
  the `2e` bound everything depends on requires `r ≤ 1/n`, discharged by `le_rfl` at two call
  sites. `Ttc/Exec/CVRateGenericSchedule.lean` proves the lower bound
  `2·exp(nα/4) ≤ acceleratedSeedWarmFactor n (1+α)` and that the `2e` bound is **false** at
  `α = 1/√n` for `n ≥ 17`. Combining with the phase count, the trade-off cancels exactly:
  `m · log(warm) ≈ (L/α)·(nα/4) = nL/4` — **rate-invariant**. So `α = 1/n` is not an unexamined
  conservative choice; it is the point where `(1+α)ⁿ = O(1)`, and the schedule is already at the
  right operating point. The audit also found the chain is ~40% parametric in `sigmaSq` and most
  pinned lemmas need only positivity/monotonicity, so a rate change *would* be a re-instantiation —
  it simply buys nothing.
* **A finding that redirects the effort:** the exponential-in-`n` factors in `slowUniformBoundSq`
  and the share floors come from the **initial variance** `s₀ = 1/(16n)`, not from the rate.
  Changing `α` neither helps nor hurts there. `s₀`, not the cooling rate, is the thing to attack —
  and lever 3 attacks exactly that term.

**Lever 3 is not operative yet.** The frontier's `hboundDef`
(`CVSlowCanonicalRobustCertificate.lean:193`) hard-codes the loose transport bound;
`CVSlowActualSteps` consumes the product warm envelope; and the slow chain is instantiated at
rate `1/n`. All three landed results are drop-in shaped, and the blocking work is re-deriving
`operational_slowCanonical_phaseScore_factorSeven` at the sharp bound (with a case split at
`i+1 = m`) and re-instantiating the phase-moment lemmas at the new rate.

### The proved complexity, and what each lever moves (2026-08-17)

**No `O(·)` theorem exists in the repository.** The machine-checked bound is the explicit
expression below; the asymptotic column is hand arithmetic on machine-checked definitions and
should be read as such.

Per cube the bound is `800 · cvComplexityShapeClipped n ρ²ⱼ ε' δ' · slowUncOV n ρ²ⱼ ε' δ'`, summed
over the DNF, plus `∑ᵢ polyGoodRateCapᵢ · canonicalHybridSamplerQueryBoundᵢ`. Writing
`L := log(16nρ²)` and `mφ ≈ nL`, `k ≈ nL/ε²`:

```
overhead  =  k · mφ · 10 · Lenv · Tenv · 2e
```

| stage | `Lenv` | `Tenv` | overhead | total |
|---|---|---|---|---|
| before lever 2 | `nρ²` | `n⁴ρ⁴` | `n⁷L²ρ⁶/ε²` | `Õ(m n⁹ρ⁸/ε⁴)` |
| lever 2 (was operative until P1) | `nρ²` | `n⁴ρ⁴` | `n⁷L²ρ⁶/ε²` | `Õ(m n⁹ρ⁸/ε⁴)` |
| + P1 sharp (wired) | `ρ²` | `n³ρ⁴` | `n⁵L²ρ⁶/ε²` | `Õ(m n⁷ρ⁸/ε⁴)` |
| **+ P2 per-phase (wired)** | `ρ²` | `n³ρ⁴` | `n⁴L²ρ⁶/ε²` | `Õ(m n⁶ρ⁸/ε⁴)` |
| **+ shape factor removed (wired, operative, 2026-08-19)** | `ρ²` | `n³ρ⁴` | `n⁴L²ρ⁶/ε²` | `Õ(m n⁴ρ⁶/ε²)` |

### The shape factor is gone (2026-08-19, commit `8a917c2`)

The per-cube bound was `800 · cvComplexityShapeClipped n ρ²ⱼ ε' δ' · slowPerPhaseOV n ρ²ⱼ ε' δ'`.
The first factor was **never earned**.  What every discharge site proves is
`expected queries ≤ OV`; the shape was appended by
`Ttc.CVSlowEffectiveOverhead.le_sourceOneRunQueryEnvelope_of_le`, whose entire content was
`le_mul_of_one_le_right` at `1 ≤ cvBaseClipped`.  That lemma is now closed by `le_rfl`, and
the shape in `Ttc.TtcShapedRuntime.shapeOf` is the confidence factor `max 1 (log (1/p))`
alone — which *is* earned, by repeated runs.  See `PLAN-SHAPE.md`.

So the removed factor is exactly `cvComplexityShapeClipped ≈ n²ρ²/ε²·log⁶`, and the ledger
reads

```
Õ(m n⁶ρ⁸/ε⁴)  ⟶  Õ(m n⁴ρ⁶/ε²)
```

**State this only as a factor removal.**  The units are unchanged, so the ratio is exact.

### Units audit (done 2026-08-19, `PLAN-SHAPE.md` §5)

Two findings, and the second is the important one.

1. **The licensed comparison.**  The paper counts *time* with the facet count `r` inside each
   per-cube price, at `n·r` operations per membership query.  Our volume term counts
   *membership queries*.  Converting at `n·r_max`:

   | | volume term, in time |
   |---|---|
   | ours | `Õ(m·n⁵·ρ⁶·r_max/ε²)` |
   | paper `thm:runtime` | `O(m·n⁵·ρ²·r_max)` |

   **`n` matches at `n⁵`; we are `ρ⁴` above.**  Every "one factor `n` short of the paper"
   statement in this file predates this and compared a query count to a time — all stale.

2. **The summands were in different units; this is now fixed.**  The volume envelope excludes
   the facet factor (queries) while `canonicalCappedSampleQueryEnvelope` includes it
   (`hybridStepInspectionBound n rfac = rfac/2` counts *facet inspections*), so the
   unweighted `∫⁻ r.2` counted nothing.  `ttc_volume_runtime_perPhase_ops` (commit `68592ae`)
   charges both at `⌈n·rfac⌉₊`, which dominates a membership query and a facet inspection
   alike, giving a bound in one unit.  It is a **costing convention** — the paper's own — not
   a theorem about a machine; see `PLAN-SHAPE.md` §5.6.

   ⚠ **The total previously stated here — `Õ(m·n⁵·ρ⁶·r_max/ε²)`, "`ρ⁴` above the paper" —
   is WITHDRAWN (2026-08-19).**  It rested on hand arithmetic for the sampler half that
   dropped `Ttc.lowDimBallWalkEnvelope`, an additive term of `hybridTransitionBound` that is
   constant in `n` but polynomial in `ρ` of degree ≈ 4400 with a `4^1099` constant, and that
   also treated `log Mw` as `O(1)` when `Ttc.ttcSampWarm` is a volume ratio and
   `log Mw = Θ(n log ρ)`.  See `PLAN-SHAPE.md` §5.7.

   What survives: polynomiality, and the `n`-exponent at fixed `ρ` (the dropped term is
   constant in `n`, so the volume half still governs it).  What dies: every `ρ`-exponent and
   every `ρ`-comparison with the paper.

### P1 is OPERATIVE as of 2026-08-18

`Ttc.TtcSlowRuntimeSharp.ttc_volume_runtime_sharp`
(`Ttc/Exec/TtcSlowRuntimeSharp.lean:621`), registered in `Ttc.lean`, `lake build Ttc`
green at **9462 jobs**, `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

Independently verified by elaborating the type (not by trusting the agent's transcription):
the binders are exactly `atoms phi eps delta` plus `h_eps_pos h_eps_le _ _ hn hphi hvol`
— no oracle, certificate, implementation, or cost-side binder — and
`TtcSlowRuntimeSharp.slowSharpImplementation` appears with **no arguments**, i.e. it is a
closed term. So this is a second unconditional capstone, at the sharp share floor.

What is machine-checked about the improvement, stated precisely: the agent proved
`CVSharpSlowSteps.slowSharpStepsEnvelope_le_min` and
`CVSharpUniformParameters.slowSharpRetriesCap_le_slowUniformRetriesCap`, both **conditional
on `2 ≤ n` and `1 ≤ R`**, and both merely *cited* in the capstone docstring rather than used
in its proof. The `n²` reading comes from the share-floor exponent going `8nR² → 8R²`; that
is **not** formalised as a numeric factor anywhere. Do not write "we proved a factor `n²`"
— write "we proved sharp ≤ loose, and the exponent drop is `8nR² → 8R²`".

Deviation worth recording: the truncation radius is *not* sharpened (the sharp route touches
slack and transport bound only), so `slowSharpQ` does not exist — the file reuses
`TtcSlowRuntimeUnconditional.slowUncQ`, and the `64 * (max 1 eps)^2 * sourceLogFactor n ^ 2`
prefix is verbatim, machine-confirmed by an `hrw … := rfl`.

`CVSlowTotalFamilies.slowLaw` could **not** be reused: it writes `slowUniformSlack` (`…/2`)
and `slowUniformBoundSq` inside the `slowCanonicalCostedActiveSchedule` term, and the sharp
certificate is about the same term at `slowSharpSlack` (`…/6`) and `slowSharpBoundSq`. Those
are genuinely different terms, so the law layer is mirrored locally in `TtcSlowRuntimeSharp`
(`slowSharpLaw`, `slowSharpLaw_of_valid`, `slowSharpFinalLaw`, and the two kernel instances).
Everything else — `slowOmega`, `slowCost`, `slowValue`, the `clipInput` family — is reused
verbatim. **Any future P2 capstone will hit the same wall and must mirror the law again.**

**Second correction, 2026-08-18.** The P2 row was first written as `n³L²ρ⁶/ε²` / `Õ(m n⁵ρ⁸/ε⁴)`,
crediting P2 with a factor `n²`. It is `n¹`. P2 divides the *stream count* `k` by `n` and nothing
else: its second effect — raising `blockShare` by `n/6` — is invisible, because the share floor is
`min (blockShare) (exponential branch)` and the exponential branch `≈ e^{−16ρ²}` is the active one
by an astronomical margin. So the honest ledger is

```
overhead = k · mφ · 10 · Lenv · Tenv · 2e
baseline    (nL/ε²)·(nL)·(nρ²)·(n⁴ρ⁴) = n⁷L²ρ⁶/ε²   ⟹ Õ(m n⁹ρ⁸/ε⁴)
+ P1        (nL/ε²)·(nL)·( ρ²)·(n³ρ⁴) = n⁵L²ρ⁶/ε²   ⟹ Õ(m n⁷ρ⁸/ε⁴)
+ P1 + P2   ( L/ε²)·(nL)·( ρ²)·(n³ρ⁴) = n⁴L²ρ⁶/ε²   ⟹ Õ(m n⁶ρ⁸/ε⁴)
```

**Consequence, stated plainly: P1 + P2 do NOT reach the paper's `n⁵`.** They land at `n⁶`, one
factor `n` short. Earlier claims in this file and in conversation that the `n` exponent would match
after P1 and P2 were wrong.

Where the residual `n` lives: `Tenv ∝ n³`, from `σ_m·n/δ_Q²` with `δ_Q = 1/(2n)` pinned by the
ell-Gaussian tilt bound, multiplied by `mφ = nL`. That is the same `δ_Q` branch identified as **P4**
below. So closing the last `n` and the last `ρ²` are the *same* obstruction — the `radiusQDelta`
`min` resolving to `1/(2n)` rather than `√σ/(max 8 (2q)√n)` — and it is research, not engineering.

**Correction to an earlier figure in this file's history:** the total was once quoted as
`Õ(m n⁹ρ¹⁰/ε⁴)`. The `ρ` exponent is **8**, not 10 — one `ρ²` was double-counted by carrying the
deadline payload factor twice. The `n` exponents and every gain figure are unaffected.

**Lever 2's honest qualification.** It cut `Wlog` by `n`, but the payload is `Wlog + Elog` and
`Elog ≈ nρ²` already dominated at large `ρ`. So the win is a full factor `n` in the *moderate-ρ*
regime and essentially nothing at large `ρ` — which is exactly why P1, which attacks `Elog`,
matters.

**What P1 does and does not move.** Three factors of `n` drop — `Lenv`, the deadline payload, and
`Tenv` through it. The truncation radius `q` is **not** improved: it comes from
`slowCanonicalJointTailFloor`'s R-aware branch `1/(6·e^{8nρ²})`, a *different* object from the share
floor, which P1 deliberately left untouched. `q` enters only as `log F`, paid once, so the effect is
minor.

Against the paper's `O(m n⁵ ρ² r_max)`: after P1 and P2 the `n` exponent matches, and the residual
is `ρ⁶`. Of that, `ρ⁴` is proved **structural** to this sampler's TV accounting
(`Ttc/Exec/CVRetryDeadlineSplit.lean`, a lower bound), and one `ρ²` is recoverable on the cost side
by the L²(π) route planned below.

### PLAN — the L²(π) route to one more `ρ²` (2026-08-17)

`Ttc/Exec/CVRetryDeadlineSplit.lean` proves the `ρ⁴` in `retries × deadline` is **structural to
the TV accounting** (a machine-checked *lower* bound, `log_ratio_sq_le_scoreAwareRetries_mul_payload`).
But it also found that the `L` in the **cost** is loose for an independent reason, and that one is
recoverable. This is the plan for it.

#### The loss site, exactly

`Ttc.FiniteContinuingRetryExpectedCost.lintegral_accumulatedCost_embeddedMarginal`
(`Ttc/Exec/FiniteContinuingRetryExpectedCost.lean:139`) is an **exact identity**

```
∫⁻ accumulatedCost ∂(embeddedMarginal … L) = ∑_{j<L} ∫⁻ candidateMean j ∂(runningCurrent … j)
```

and `…_le` (`:147`) bounds each summand by `Arlib.MarkovChains.lintegral_le_of_isWarm`, i.e.
`∫f dμⱼ ≤ M·∫f dπ ≤ M·T`, **discarding the survival mass `sⱼ := runningCurrentⱼ(univ)`**. Summing
gives `L·M·T`. Since `∑ⱼ sⱼ = O(1)` (geometric decay, `ContinuingRejectionSelective.badWeights_add_survival_le_eta_add_pow`),
the truth is `O(M·T)`. The gap is the factor `L ≈ ρ²`.

**Why first-moment warmness cannot recover it** (already established): from `μ ≤ M·π` and
`μ(univ) = s` alone, `∫f dμ ≤ s·M·∫f dπ` is **false** — take `μ = M·(π|_T)` with `π(T) = s/M` and
`f = 1_T`: LHS `= s`, RHS `= s²`.

#### Route A — try this first; it may make L² unnecessary

If `candidateMean` is bounded **pointwise** by the round's deadline `T`, then no warmness and no
Cauchy–Schwarz are needed at all:

```
∫⁻ candidateMean j ∂μⱼ ≤ T · μⱼ(univ) = T · sⱼ      ⟹     ∑ⱼ ≤ T · ∑ⱼ sⱼ = O(T)
```

**The decision question:** is `roundCost` bounded per round? `candidateMean candidate roundCost j x
= ∫⁻ c, roundCost c ∂(candidate j x)`. If the walk runs a *fixed* number of steps per round, yes,
and Route A is a few lines. If the cost is a random **time change** — the speedy walk's ball-walk
step count, `≈ steps/ℓ(x)`, unbounded as `ℓ(x) → 0` — then no, and that is precisely why
`lintegral_le_of_isWarm` was used. Check `Ttc.ConcreteHybridExpectedQuerySampler.hybridStepInspectionBound`
and the `roundCost` actually supplied by the hybrid sampler **before** doing any L² work.

Note `Arlib.MarkovChains.acceptance_floor_le_speedyMetropolisMove`
(`Arlib/MarkovChains/Continuous/WastedStepsGaussian.lean:375`) already proves an acceptance floor
for the Gaussian speedy walk. If that floor gives `ℓ ≥ c > 0` on the relevant set, `candidateMean`
is bounded and **Route A wins outright**.

#### Route B — the L²(π) bound, if Route A fails

The correct substitute for `lintegral_le_of_isWarm`, in Cauchy–Schwarz form (stated squared so no
`ENNReal` square roots are needed):

```lean
theorem sq_lintegral_le_of_isWarm_survival
    {E : Type*} [MeasurableSpace E] {μ π : Measure E} [SigmaFinite π] [SigmaFinite μ]
    {M : ENNReal} (hwarm : IsWarm M μ π) (hM : M ≠ ⊤)
    {f : E → ENNReal} (hf : Measurable f) :
    (∫⁻ x, f x ∂μ) ^ 2 ≤ (∫⁻ x, (f x) ^ 2 ∂π) * (M * μ Set.univ)
```

Proof, all ingredients in Mathlib:
1. `IsWarm M μ π` gives `μ ≤ M • π`, hence `μ ≪ π`; let `g := μ.rnDeriv π` and
   `μ = π.withDensity g` (`withDensity_rnDeriv_eq`).
2. `g ≤ M` π-a.e., from `μ ≤ M • π`.
3. `∫⁻ f dμ = ∫⁻ f·g dπ` (`lintegral_withDensity_eq_lintegral_mul`).
4. Hölder at `p = q = 2` (`ENNReal.lintegral_mul_le_Lp_mul_Lq`): `(∫ fg)² ≤ (∫f²)(∫g²)`.
5. `∫ g² dπ ≤ M·∫ g dπ = M·μ(univ)`, by step 2.

Then the two supporting pieces:

```lean
theorem sum_sqrt_survival_le                      -- ∑ⱼ √sⱼ = O(1)
    (hs : ∀ j, j < L → s j ≤ eta + r ^ j) (hr : r < 1) :
    ∑ j ∈ Finset.range L, Real.sqrt (s j).toReal ≤
      (L : Real) * Real.sqrt eta.toReal + 1 / (1 - Real.sqrt r)
```
— at `η ≈ share` and `L = 16⌈log₂(1/share)⌉` the term `L·√η ≈ log(1/share)·√share` is bounded by an
absolute constant, so the whole sum is `O(1)`. Prove that as `mul_sqrt_log_inv_le` separately;
it is where the win is actually banked.

```lean
theorem lintegral_accumulatedCost_le_l2 … :
    ∫⁻ accumulatedCost ∂(embeddedMarginal … L) ≤
      (∑ j ∈ Finset.range L, Real.sqrt ((M * s j).toReal)) *
        Real.sqrt (∫⁻ x, (candidateMean … j x) ^ 2 ∂pi).toReal
```

#### The genuinely new mathematical content

`∫⁻ (candidateMean)² dπ` — a **second-moment** bound on the per-state expected query count of the
lazy speedy walk under its stationary measure. The repo has only the first moment
(`Arlib/MarkovChains/Continuous/WastedSteps.lean`: `E_x[exit time] = 1/ℓ(x)` and the averaged
`3·∑ ≤ 10·t·M`). Concretely this is `∫ ℓ^{-2} dπ`, where the existing bound is on `∫ ℓ^{-1} dπ`.
**If the acceptance floor of `WastedStepsGaussian.lean:375` gives a uniform `ℓ ≥ c`, this is
`≤ c^{-2}` and free — which again collapses to Route A.**

#### Ordering, and what it buys

1. Decide Route A vs B by reading the hybrid sampler's `roundCost` (cheap, decides everything).
2. Route A: the `T·sⱼ` bound + `∑ⱼ sⱼ = O(1)`. Removes `hwarm` from the cost lemma entirely.
3. Route B if needed: `sq_lintegral_le_of_isWarm_survival`, `sum_sqrt_survival_le`, then `∫ℓ^{-2}dπ`.
4. Rewire `slowUniformRetainedRealEnvelope` (`CVSlowEffectiveOverhead.lean:873`), which is
   `k·m·10·retryEnv·deadlineEnv·2e`, dropping the `retryEnv` factor; then `slowUncTenv` and the
   capstone.

Payoff: one factor `L ≈ ρ²` off the total. Restated at the current operative baseline
(P1 + P2 both wired, 2026-08-18): `Õ(m n⁶ρ⁸/ε⁴) → Õ(m n⁶ρ⁶/ε⁴)`. It does **not** touch the
TV-side `ρ⁴` lower bound, which stands. With P4 closed as tight and the KLS question
dissolved (see AUDIT.md §0g), **this is the only priced reduction still standing.**

### ✅ THE RUNTIME CAPSTONE IS UNCONDITIONAL (2026-08-17)

`Ttc.TtcSlowRuntimeUnconditional.ttc_volume_runtime_unconditional`
(`Ttc/Exec/TtcSlowRuntimeUnconditional.lean`). Verified by reading the elaborated type, not
by relaying a report — its binders are exactly

```
{A} {n} (atoms) (phi) (eps delta : ℝ)
  0 < eps,  eps ≤ 1,  0 < delta,  delta ≤ 1,  21 ≤ n,  phi.IsPositive,  0 < volSol …
```

and **nothing else**: no oracle, no certificate, no implementation, no cost-side binder.
`slowUncImplementation` is a closed term. `#print axioms` gives
`[propext, Classical.choice, Quot.sound]`. Whole library green, zero `declaration uses 'sorry'`.

Both conjuncts are about one law: accuracy `1 − δ`, and the run's own integrated query cost
bounded by the per-cube sum of `cvComplexityShapeClipped · slowUncOV` at each cube's
**interior circumradius squared**, plus the sampling envelope.

#### The two decisions that made it close

* **`cvAdmCircum`** — pin the declared radius to `(circumR (interior K))²` rather than
  letting it be any upper bound. Legitimate because `CVAdmissible` only wants an upper bound
  on the second moment, and `cvSecondMoment K = cvSecondMoment (interior K) ≤ (circumR (interior K))²`
  for convex `K`. Effect: `hrad` and `heff` become `le_refl`, so the envelope's monotonicity
  in `R2` — where the phase count sits *inside a logarithm and also multiplies it* — never
  has to be proved.
* **`ttc_runtime_of_effectiveCertificatesGen`** — the runtime theorem generic in the
  admissibility predicate and the radial parameter, so the above is expressible.

#### What this is NOT

The proved envelope is `cvComplexityShapeClipped · slowUncOV` with
`slowUncOV = 64·(max 1 ε)²·log²n · slowActualOverhead`, and `slowActualOverhead` carries the
uniformly slow schedule's compounding-warmness overhead. It is an **explicit polynomial**,
and it is **not** the paper's `O(m·n⁵·ρ²·r_max)` exponents. §4 below is unchanged and still
governs what may be claimed.

### Superseded: the conditional capstone and the obligation it carried

`Ttc.TtcSlowRuntimeFinal.ttc_volume_runtime_slow` (`Ttc/Exec/TtcSlowRuntimeFinal.lean`) is
the runtime capstone: inputs `(atoms, φ, ε, δ)`, conditions `0 < ε ≤ 1`, `0 < δ ≤ 1`,
`21 ≤ n`, `φ.IsPositive`, `0 < volSol`, **no oracle, certificate or implementation binder**
— and one residual hypothesis, `SlowCostSideHypothesis`. Axiom-clean at
`[propext, Classical.choice, Quot.sound]`.

Everything else is discharged: the whole generic half, the producer at canonical parameters,
all seven moment binders, `hexact`, `hretries`, `hscalar`, the accuracy weakening, the
budget absorption, the interior bridge and the dimension splice.

#### The gap, stated exactly

**The frontier's `hsteps` binder has never had a provider, in any file.** The two functions
differ in exactly one argument:

```
slowCanonicalSteps initialWarm n q s0 K retries η ζ i _   -- the frontier's LHS
  = adjustableSpeedyDeadline n (radiusQDelta n q σᵢ) σᵢ
      ((2 * slowWarmBudget initialWarm n q s0 K retries i) / η i)   ← ACTUAL warm
      (ζ i)

slowScoreAwareSteps n m k q eps slack boundSq i _         -- what every cap bounds
  = adjustableSpeedyDeadline n (radiusQDelta n q σᵢ) σᵢ
      (slowReferenceWarm / scoreAwareEta m k eps slack boundSq i)   ← REFERENCE warm
      (scoreAwareZeta m k eps slack boundSq i)
```

Both `Ttc.CVSlowCanonicalDeadlineCost.slowScoreAwareSteps_canonical_active_le` and the new
`Ttc.CVSlowUniformShareBounds.slowScoreAwareSteps_uniform_active_le` bound the *reference*
form. The deadline the schedule actually selects is driven by
`slowWarmBudget = recursiveWarmBudget initialWarm (slowAcceptedFactor retries) (slowFallbackFactor n q s0 K)`,
the **recursively compounding actual-path warmness** — and a grep for any theorem bounding
`slowWarmBudget` returns nothing.

This is precisely the distinction `Ttc/Model/Theorem.lean`'s docstring already names: *"the
possibly compounding actual-path warm budget selects the mixing deadline, while the expected
query cost is evaluated on the exact retained reference law and therefore does not inherit
that multiplicative budget."* The cost side was built against the reference law; the
deadline side was not, and nothing joins them.

#### CLOSING IT — the mathematics is done (2026-08-17, later)

The compounding is real but survivable, exactly as `AUDIT.md` §0n predicted, and for the
reason it gave: the deadline consumes the warmness only through `log M`, so a *product*
bound becomes an *additive* one.

| File | What it gives |
| --- | --- |
| `Ttc/Exec/CVSlowWarmBudgetBound.lean` | **The missing bound**, in uniform-power form: `slowWarmBudget … i ≤ slowReferenceWarm · B^i` and `log(…) ≤ log(2e) + i·log B`, at `B = max 1 (L·32e) + hotRefreshWarmEnvelope n (q√σ_m√n) s₀`. The per-phase-sum fallback was not needed. |
| `Ttc/Exec/CVSpeedyDeadlineMono.lean` | A bound on `log M` drives `adjustableSpeedyDeadline`. The existing `adjustableSpeedyDeadline_le_ceil_of_expression_le` was directly reusable, so this is thin. |
| `Ttc/Exec/CVSlowActualDeadline.lean` | `slowCanonicalSteps_le_ceil_of_log_le` — **the bridge that had no provider**. |
| `Ttc/Exec/CVSlowActualCostEnvelope.lean` | The cost layer at *real* envelopes `(Lenv, Tenv)` rather than an opaque `T : Nat`, since the budget inequality needs a real bound. |

Why it stays polynomial: the fallback factor is bounded by
`exp(1/(32s))·(4·max 1 R)^n` — exponential in `n` — but only its **logarithm** enters, as
`n·log(4 max 1 R) + 1/(32s)`, and at `s₀ = 1/(16n)` the second term is `n/2`. The uniform
envelope needs the two arguments bounded in *opposite* directions: the containment radius
`q√σ_j√n` grows along the schedule (bound at the terminal `σ_m`), while `exp(1/(32s))`
shrinks in `s` (bound at `s₀`).

**One correction the elaborator caught.** The deadline expression was first written with a
single share term. `slowCanonicalSteps` has *two* distinct share slots — `etaShare i`
divides the warm budget inside `M`, while `zetaShare i` is `adjustableSpeedyDeadline`'s own
`eta` parameter. Conflating them is a type error. Since `zeta = share/32` and `eta = share`
are numerically close, an informal argument would have glossed it.

#### What would close it — the original analysis, kept for the record

The machinery exists and is simply not connected to `slowWarmBudget`:

* `Ttc.CVWarmBudgetRecurrence.recursiveWarmBudget_le_product` (`:77`),
  `recursiveWarmBudget_toReal_le_product` (`:112`),
  `log_recursiveWarmBudget_toReal_le_sum` (`:134`);
* `Ttc.CVColdActualWarmReferenceCostArithmetic.recursiveWarmBudget_cold_le_linear_pow`
  (`:487`) and `log_recursiveWarmBudget_coldPrefix_le_quadratic` (`:661`).

The route: bound `slowAcceptedFactor retries` and `slowFallbackFactor n q s0 K` per phase,
apply the product bound, then push through monotonicity of `adjustableSpeedyDeadline` in its
warm argument. That is a genuine piece of mathematics — the compounding is real and the
bound must be shown polynomial — not a wiring step, and it is the honest remaining content
of the runtime claim.

`Ttc.TtcSlowRuntimeFinal.slowCostSideRealised_of_deadlineCapped` reduces the residual to the
narrowest form: bounding that one selected deadline on the active phases.

### Still open on the critical path

`Ttc/Exec/CVSlowEffectiveOverhead.lean` (the overhead envelope `OV` and the `hscalar`
discharge), `Ttc/Exec/CVSourceReferenceWeaken.lean` (the certificate-parameter weakening),
`Ttc/Exec/CVSlowCanonicalTailPhases.lean` (the `j > m` indices), and then the final
assembly. `Arlib.GaussianCooling.chain_end` settles the terminal identification
`chain m σsq K m = (volume K).toReal` exactly, with no side conditions, so no accuracy
budget is lost there.

## 3. The immediate work, as named lemmas

All of this lives in new files under `Ttc/Exec/`; one file per item, one agent per file,
build green after each (CLAUDE.md §3, §7).

### A. Discharge the frontier theorem's binders

The binders of `exists_sourceReferenceTVOneRunCertificate_slowCanonical_of_weightedData`,
grouped, with the existing lemma that closes each. Items marked **OPEN** have no
discharging lemma yet and are the actual work.

| Binders | Discharged by |
|---|---|
| `hqRAware`, `hslackDef`, `hboundDef`, `hC1`, `hC7`, `hrad`, `hmeanTailFloor`, `hmeanTailBudget` | `CVSlowCanonicalUniformParameters.slowUniformParameters_valid` (`:158`) — **landed, uncommitted**. Needs only to be applied. |
| `hop` (`IndependentStreamOperational …`), `hVliteral`, `htau`, `hmixError` | `CVSlowCanonicalStreamOperational` (uncommitted) + `CVSlowCanonicalClippedFactorization.slowClipped_streamOperational_statistics` (`:164`) + `CVSlowRadiusQCanonicalOperational.seedProjectedOperational_slowRadiusQ_scoreAware`. **OPEN**: one assembly lemma producing `hop` with `htau`/`hmixError` in the *exact* forms the frontier binder writes. |
| `hWint`, `hW2int`, `hWEpos`, `hrawSecond`, `hfactor0`, `hphaseMoment` | `CVSlowCanonicalPhaseMomentPackage.operational_slowCanonical_clippedMoment_bundle_upto` (`:708`), fed by `CVSlowCanonicalMomentInstantiation.slowCanonical_htargetTV` (`:42`, uncommitted) through `operational_positiveStreamMean_upto_of_targetTV` (`:471`). **OPEN**: the wiring lemma; the analysis is done. |
| `hprefix : ∀ i ≤ m, prefixMomentRatio factor i ≤ 1 + ε²/6250` | `CVWeightedOperationalProductArithmetic.prefixMomentRatio_phaseVar_eps_slack_le` (`:155`). **OPEN**: an arithmetic lemma checking the uniform slack choice of `slowUniformParameters_valid` lands under `ε²/6250`. Pure inequality work; likely the cheapest OPEN item and a good first one. |
| `hbetaDef`, `haccuracyBudget`, `beta`, `requested` | **OPEN**: pure arithmetic. Pick `beta := m/(2·correctedAlpha m ε) + scoreAwareMeanGamma m k ε + product`, then `requested := ε + beta + ε·beta`; prove `requested < 1` in the operating regime. No mathematics, but the regime condition must be stated, not assumed. |
| `T`, `L`, `hsteps`, `hretries`, `hscalar` | `CVSlowCanonicalRuntimeComparison.slowCanonicalRetainedScalar_ennreal_le_publicShape` (`:179`) + `CVSlowCanonicalDeadlineCost`. **OPEN**, and blocked on §2: `hscalar` demands `≤ sourceOneRunQueryBudget runtimeConstant n R requested`, and what is proved is `≤ cvSlowCanonicalCappedRadialShape`. Resolve §2 first. |
| `m`, `k`, `hm`, `hk` | **OPEN**: `m := slowOperationalPhases n N` (`CVSlowSourceReferenceCertificate.lean:452`) and a choice of stream count `k`; `k` is forced by the `1/40` TV budget through `slowPhaseError_sum_le_one_fortieth` (`:455`). |
| `hK`, `hKc`, `hball`, `hfin`, `hKR`, `R` | **OPEN**: instantiate at TTC's actual per-cube bodies. `hKR : K ⊆ closedBall 0 R` and the `radialR` argument must be filled from `Ttc/Exec/Inscribed.lean` and `Ttc/Exec/Geometry.lean` — this is workstream B, §3.B. |

**Suggested order** (cheapest-first, each independently landable):
`hprefix` → `hbetaDef`/`haccuracyBudget` → moment wiring → `hop` assembly → `m`/`k` →
(§2 decision) → `hscalar`.

### B. The geometry instantiation — `radialR` at TTC's own polytopes

`radialR : Set (Space n) → Real` is a free function argument all the way up the chain,
and the capstone needs `hrad : ∀ K R2, CVAdmissible K R2 → (radialR K)^2 ≤ R2`
(`CVSourceDimensionGuardTwentyOne.lean:49`). TTC's bodies are
`roundBody (algCen atoms φ ε δ …)` — the normalised per-cube polytopes.

**OPEN**, one lemma: define `ttcRadialR` from the constructed inscribed ball
(`Ttc/Exec/Inscribed.lean`) and the outer radius, and prove the `CVAdmissible` bound.
This is independent of everything in A and can run in parallel from today.

### C. The assembly, once A and B land

Three short files, mechanical:

1. `∀ n ≥ 21, ∀ a, ∃ reference, SourceReferenceTVOneRunCertificate …` — the frontier
   theorem applied at the choices of A.
2. `radialLogSourcePublicReferenceTVCertificates_of_operationalColdHotAudit ∘
   operationalColdHotRadialAuditOfOneRunCertificates` — already written, just applied.
3. The inhabitant, at whichever interface §2 selects, then
   `ttc_volume_estimate_of_cvCappedRadialLogExpectedImplementation` (or its slow-shape
   twin) applied to it. **This is the theorem that makes TTC's runtime unconditional.**

---

## 4. What will *not* be claimable even after all of the above

State these in the paper and the README before quoting any runtime result. Each is a
positive finding, not unfinished bookkeeping.

1. **The provable shape is not the printed shape.** What lands is
   `m · (capped radial-log CV shape + rate threshold · endpoint cap)`, where the capped
   shape is `cvComplexityShapeClipped · (log R)² · n` (`CVHotRefreshHonestRuntime`), and
   under route (2a) there is a further explicit slow-schedule factor. `Model/Theorem.lean`
   already records that **no universal constant** bounds the concrete schedule by the
   `log R`-free expression for unrestricted `R`. `thm:runtime` as printed therefore needs
   either an explicit `O*` reading that admits polylog-in-`R` factors, or a radius
   normalisation hypothesis. `Ttc/Exec/TTCRuntimePaperArithmetic.lean` machine-checks the
   paper's *own* arithmetic (`m·r_max·(n³ρ²∨n⁴)/ε² + n⁵ρ²·Thresh`), and
   `TTCOperationalPaperBridge.lean` reduces the comparison to three local inequalities
   which its docstring states **cannot hold uniformly**. This is a paper correction, not
   a Lean gap.
2. **Step count is not running time.** The path-level time change `ω_t = Y_{N_t}` needs
   the strong Markov property for `Kernel.trajMeasure`; `grep -rn StrongMarkov` over
   Mathlib v4.32 returns nothing (`AUDIT.md` §0p). Cousins–Vempala have the same gap and
   identify the two definitionally. Either adopt their convention explicitly or do not
   say "running time".
3. **The `n < 1100` sampler constant.** `hybridTransitionBound` is polynomial only above
   `n = 1100`; below it the ball-walk fallback is exponential in a bounded `n`, hence
   formally a constant — an astronomically large one. Honest, but must be stated.
4. **`thm:decompose` is unformalised**, so the exponential cost of the decomposition
   itself is outside every theorem here. The `m` in every bound is a free input.
5. **Two input conditions survive** on the accuracy half: `hφ : φ.IsPositive`
   (positive DNF only — `lem:lattice` is proved there and `Ttc/Findings/OpenHalfspace.lean`
   prices the extension) and `hpos : 0 < volSol`.
6. **`LocalizationHypothesis` is still assumed** in `Arlib/Convexity/GaussianCooling/Variance.lean:1095`
   for *general* log-concave `f`. It is **not** on this critical path: the indicator case
   the volume oracle needs is unconditional (`IndicatorVariance.variance_le_exp_indicator`,
   docstring: "No `ZLogconcaveHypothesis` and no `LocalizationHypothesis`"). On the
   `thm:iso` side, `Arlib.hloc_of_localization` (`HlocFromLocalization.lean:676`) is a
   **shape bridge, not a discharge**: it takes the Localization Lemma `hLoc` as an
   explicit hypothesis and converts its needle into the form `thm:iso` consumes. The
   Localization Lemma itself remains assumed there. This does not affect the plan — the
   frontier theorem of §1 is already proved, so whatever isoperimetry it consumed it
   already has — but the sentence must not be read as "localization is done".

---

## 5. Gates

After each landed item, unchanged from `CLAUDE.md` §4:

```bash
cd lean && lake build                    # zero "declaration uses 'sorry'"
grep -rn "sorry\|admit\|native_decide\|sorryAx\|^axiom " Ttc.lean Ttc/ Arlib.lean Arlib/
grep -rn "^import Ttc" Arlib/            # expect nothing
```

and `#print axioms` on the item, expecting `[propext, Classical.choice, Quot.sound]`.

The completion gate for this whole document is one line:

```lean
#print axioms Ttc.CVCappedRadialLogInterface.ttc_volume_estimate_of_cvCappedRadialLogExpectedImplementation
-- applied at a closed inhabitant, with no `I : CV…Implementation` binder left
```
