# TTC end-to-end: where we are, and the immediate work

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
