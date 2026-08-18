# The `retryEnv` lever: routes, what is dead, and the route that is live

Written 2026-08-18, after the P2 capstone landed at `Õ(m n⁶ρ⁸/ε⁴)`.
Supersedes the "PLAN — the L²(π) route to one more `ρ²`" section of `RUNTIME-ENDGAME.md`,
whose Route A is **dead** and whose Route B reduces to a quantity nobody in the literature
bounds. Everything below was checked against source, not against that plan's prose.

## 0. The loss site, restated exactly

`Ttc.FiniteContinuingRetryExpectedCost.lintegral_accumulatedCost_embeddedMarginal`
(`:95`) is an exact identity,

```
∫⁻ accumulatedCost ∂(embeddedMarginal … L)  =  ∑_{j<L} ∫⁻ candidateMean j ∂(runningCurrent … j)
```

and `…_le` (`:139`) bounds each summand with
`Arlib.MarkovChains.lintegral_le_of_isWarm`, i.e. `∫f dμⱼ ≤ M·∫f dπ`, **discarding the
survival mass `sⱼ := runningCurrentⱼ(univ)`**. Summing gives `L·M·T`; the truth is `O(M·T)`
because `∑ⱼ sⱼ = O(1)` by geometric decay. The gap is one factor `Lenv = ρ²`.

In the current ledger (`RUNTIME-ENDGAME.md`), `overhead = k·mφ·10·Lenv·Tenv·2e` with
`(L/ε²)·(nL)·(ρ²)·(n³ρ⁴)`, so removing the `Lenv = ρ²` is worth exactly `ρ⁸ → ρ⁶`.

## 1. Route A is DEAD — verified from the definitions

The plan asked: is `roundCost` bounded pointwise? It is not.

* `roundQueryCost` is `RawGaussianLazyStoppedExecution.actualMembershipQueryCount t`, which is
  `SequentialCost.totalCost t omega = ∑_{i<t} (omega (i+1)).1` — a sum of `t` per-step costs.
* The per-step cost is `Arlib.MarkovChains.properProposalWaitCost`
  (`Arlib/MarkovChains/Continuous/ProperProposalCostedRestart.lean:25`), defined as the
  **tail-sum realization of a geometric waiting time**: the number of ordinary proposal
  transitions before the first proper proposal.

So the cost is exactly the random time change the plan feared, with mean `1/ℓ(x)` and no
pointwise bound. `T·sⱼ` is unavailable.

### The plan's escape hatch does not exist — a conflation, recorded

`RUNTIME-ENDGAME.md` claimed: "if `acceptance_floor_le_speedyMetropolisMove`
(`WastedStepsGaussian.lean:375`) gives `ℓ ≥ c > 0` on the relevant set, **Route A wins
outright**." That is wrong on its own terms:

* the floor bounds `speedyMetropolisMove`, the **Metropolis acceptance factor**
  `exp(−(2Rδ+δ²)/(2s))`, not the local conductance `ℓ`;
* it *assumes* `hstuck : volume (ball x δ ∩ K) ≠ 0` — i.e. it takes `ℓ(x) > 0` as input
  rather than bounding it below;
* and `ℓ → 0` at sharp corners is a genuine feature of ball walks, not an artefact.
  `Arlib/MarkovChains/Continuous/BallWalkConductance.lean:74-77` already says so, and its
  only pointwise witness `ofReal_le_ell_unitBall` is `2⁻ⁿ` **on the unit ball**.

## 2. The "mass-scaled warmness" idea is DEAD — already refuted in-repo

Tempting: `hwarm` is threaded as one uniform `M` for every `j`
(`CVColdOperationalKernel.isWarm_runningCurrent_coldGaussian`, discharged at `:513` with
`IsWarm.refl` and `M := 1`), so why not prove `IsWarm (sⱼ·M) μⱼ π` and let `∑ⱼ sⱼ = O(1)`
do the work? Because warmness is a statement about the **density**, not the mass, and the
counterexample is the one already recorded in `RUNTIME-ENDGAME.md`: `μ = M·(π|_T)` with
`π(T) = s/M` has mass `s` and density `M`, not `M·s`.

## 3. Route B reduces, exactly, to one quantity — and it is the quantity the speedy walk exists to avoid

The operative reference law is `ellGaussianProb K δ σ²`, i.e.
`(volume.restrict K).withDensity (ℓ·γ_σ)` normalised by `Z := ∫_K ℓ·γ_σ`
(`SpeedyGaussian.lean:290`, `:463`). So for the second moment the `ℓ`-weighting collapses one
power:

```
∫ ℓ⁻² d(ellGaussianProb K δ σ²)  =  (∫_K ℓ⁻¹ dγ_σ) / (∫_K ℓ dγ_σ)   =:  Q
```

exactly mirroring the proved first-moment identity
`Arlib.MarkovChains.lintegral_inv_ell_ellProb` (`WastedSteps.lean:222`), which collapses to
`vol K / ∫_K ℓ = 1/λ` and is *trivial* for the same reason.

**Q is the quantity the speedy walk was invented to avoid.** The first moment of `ℓ⁻¹` under
the `ℓ`-weighted law is a zeroth moment under Lebesgue; the second moment is a *first* moment
of `ℓ⁻¹` under Lebesgue, which the averaged hypothesis `λ ≤ (∫_K ℓ)/vol K` does not control —
it is a first-moment hypothesis on `ℓ`, and says nothing about `∫ℓ⁻¹`. This is precisely the
obstruction `HoldingTime.lean:87-97` already records for the ball walk's conductance.

Do not build Route B before pricing Q.

## 4. ROUTE C — the live route. Hölder at `p = 1 + α`, and it needs no second moment

Replace `∫f dμⱼ ≤ M∫f dπ` by Hölder against the warm density `gⱼ := dμⱼ/dπ ≤ M`:

```
∫ f dμⱼ  =  ∫ f·gⱼ dπ  ≤  ‖f‖_{L^p(π)} · ‖gⱼ‖_{L^{p'}(π)},     ‖gⱼ‖_{p'} ≤ M^{1/p}·sⱼ^{1/p'}
```

using `∫gⱼ^{p'} dπ ≤ M^{p'-1}∫gⱼ dπ = M^{p'-1}·sⱼ`. Summing:

```
∑ⱼ ∫f dμⱼ  ≤  ‖f‖_{L^p(π)} · M^{1/p} · ∑ⱼ sⱼ^{1/p'}
```

**The `f` factor.** `f = candidateMeanⱼ = ∑_{i<T} P^i w` with `w ≈ ℓ⁻¹` the one-step mean
wait. `ellGaussianProb` is invariant for `speedyMetropolisGaussian`
(`SpeedyGaussian.lean:484`, `Kernel.Invariant`), so `P` is an `L^p(π)` contraction and
Minkowski gives `‖f‖_p ≤ T·‖w‖_p = T·(∫ℓ^{-p}dπ)^{1/p}`. And again the weighting collapses:

```
∫ ℓ^{-p} dπ  =  (∫_K ℓ^{-α} dγ_σ)/Z         for p = 1 + α
```

— an `α`-th moment, not a first moment, of `ℓ⁻¹` under `γ`. **That is the whole point:
choosing `α` small makes the unbounded quantity of §3 disappear.**

**The `α`-th moment is bounded by an elementary convexity estimate — LANDED.**
`Arlib/MarkovChains/Continuous/LocalConductanceMoment.lean`, 21 theorems, zero `sorry`, all
`[propext, Classical.choice, Quot.sound]`. Three corrections to the sketch that was here
first, each of which made the Lean easier or the constant better:

1. **A ball, not a cone.** For `u := d(x, ∂K') ≤ δ` we have `ball x u ⊆ K'` and so
   `ell(x) ≥ (u/δ)^n` by plain ball-volume monotonicity
   (`ofReal_div_pow_le_ell_of_ball_subset`) — no cone geometry, no `ball 0 1 ⊆ K` in that
   lemma at all, and no measurability of `K`. The exponent is `n` rather than the cone's
   `n-1`, which only moves `α` from `1/(2(n-1))` to `1/(2n)`.
2. **The layer bound is `θ^{1/n}` with prefactor `nδ ≤ 1/2`.** `(1-λ)•K' ⊆ {u ≥ λ}` by
   convexity (`ball_subset_of_mem_smul_of_convex` — the only place `ball 0 1 ⊆ K` is used),
   and the shell `K' \ (1-λ)•K'` carries at most `1 - (1-λ)^n ≤ nλ` of the weight
   (`measure_lt_ell_le_mul`). At `λ = δ·θ^{1/n}` and `δ ≤ 1/(2n)` the tail is `θ^{1/n}/2`.
3. **The dyadic base is `2^n`, and that is the whole trick.** At base `2^n` the *crude*
   per-band bound `mu(A_k) ≤ mu{ell < 2^{-nk}}` already sums to an absolute constant, so
   there is no Abel summation and no layer-cake machinery — the pointwise inequality
   `rpow_neg_le_add_tsum_indicator` plus `lintegral_tsum` is the entire proof. **At base `2`
   the same argument loses a factor `n`**, which would have made the whole lever a wash;
   this was worth getting right.

The result is `lintegral_ell_rpow_neg_le`:

```
∫_K ell^{-1/(2n)} dmu  ≤  6 · mu K
```

for convex `K ⊇ ball 0 1` and `δ ≤ 1/(2n)`. The weight enters only through `MeasureShrinks
mu K`, an inline hypothesis saying that shrinking toward the origin costs at most the
Jacobian.

**The weight hypothesis is discharged, twice.** The first draft of this plan proved the
layer bound for *Lebesgue* and then asserted it for `γ_σ` — a claim whose sketch proved
something else, exactly the failure mode `AUDIT.md` §11 is about. What is actually proved:
`measureShrinks_volume` (Lebesgue, with equality, from `addHaar_smul`) and
`measureShrinks_withDensity` (any weight non-decreasing under shrinking, via the
change-of-variables `lintegral_smul_set_eq`), and `gaussianWeight_le_smul` supplies the
Gaussian instance because `‖c•x‖ ≤ ‖x‖`. The usable form is
`lintegral_ell_rpow_neg_gaussian_le`, with every hypothesis discharged, and
`exists_localConductanceMoment_witness` exhibits the unit ball at `δ = 1/(2n)` satisfying
every guard simultaneously with the weighted measure positive and finite.

**The `sⱼ` factor.** With `sⱼ ≤ η + rʲ`
(`ContinuingRejectionSelective.badWeights_add_survival_le_eta_add_pow`),

```
∑ⱼ sⱼ^{1/p'}  ≤  L·η^{1/p'} + 1/(1 − r^{1/p'})  ≈  L·η^{1/(2n)} + 2n/log(1/r)
```

and `η ≈ share ≈ e^{−cρ²}`, so `η^{1/(2n)} = e^{−cρ²/(2n)}`.

**`r` is a threaded binder, not a constant of the development** — checked at the source.
`badWeights_add_survival_le_eta_add_pow` (`Ttc/Volume/ContinuingRejectionSelective.lean:146`)
takes `r` with `hcontract : ∀ j, eta ≤ s j → s (j+1) ≤ r * s j`, and every call site receives
it from `hreject` further up. So the new lemmas keep `r` as a binder too — the repo's own
idiom — and inherit whatever the chain supplies. Note that `retriesCap = 16 ·
explicitDyadicTailIndex(share)` forces `r ≤ 2^{-1/16}` for the existing TV budget to close at
all, so `1/(1 − r^{1/p'}) = O(p')` is not in doubt; but nothing new depends on pinning it.

### What Route C buys, stated honestly

`Lenv` goes from `ρ²` to `min(ρ², O(n))` — the `min`, because the existing bound is not
discarded, both hold, and we may take whichever is smaller. So

```
now  Õ(m n⁶ ρ⁸ / ε⁴)      →      Õ(m · n⁶ · ρ⁶ · min(ρ², n) / ε⁴)
```

* strictly better whenever `ρ² > n`, which is the regime the paper's `r_max` tracks;
* never worse, since the `min` retains the current bound;
* at worst `Õ(m n⁷ρ⁶/ε⁴)` — i.e. it trades one `ρ²` for one `n` in the worst case.

**It is not a free `ρ²`.** Anyone quoting this lever as "one factor `ρ²` off the total" — as
`RUNTIME-ENDGAME.md` did — is quoting the payoff without its price. The price is the
Hölder conjugate `p' ≈ 2n`, and it is intrinsic: it comes from `ℓ ≳ (u/δ)^{n-1}`, i.e. from
the fact that local conductance really can be exponentially small in `n` at a sharp corner.

### Where a genuinely free `ρ²` would have to come from

`p' = O(1)` — hence `Lenv = O(1)` and a clean `ρ⁸ → ρ⁶` — requires the tail exponent in
`γ({ℓ<θ}) ≲ θ^β` to be `β = Ω(1)` rather than `β = 1/(n-1)`. That is a statement about how
much of a convex body sits near a *sharp* corner as opposed to a *flat* face, and for the
bodies TTC actually calls on (`callBody`, boxes cut by the DNF) it may be far better than the
general convex bound. **That is the one open geometric question in this lever, and it is
worth asking before settling for the `min`.**

## 5. Build order — status

1. ✅ `ofReal_div_pow_le_ell_of_ball_subset` — the ball estimate. *(A ball, not a cone.)*
2. ✅ `measure_lt_ell_le_mul` — the layer bound, weight-generic via `MeasureShrinks`.
3. ✅ `lintegral_ell_rpow_neg_le` — `∫_K ell^{-1/(2n)} dmu ≤ 6·mu K`, and
   `lintegral_ell_rpow_neg_gaussian_le` / `exists_localConductanceMoment_witness` discharging
   and witnessing the weight hypothesis.
4. ✅ `lintegral_ell_rpow_neg_ellGaussianProb_le` — the bridge to the speedy walk's own
   reference law, stated *relative to its first moment* so the normalisation cancels.
5. ✅ `lintegral_le_of_isWarm_holder`, `sum_rpow_le_of_le_add_pow`,
   `sum_lintegral_le_of_isWarm_holder` — the lever, abstractly
   (`Arlib/MarkovChains/Continuous/WarmHolder.lean`). Plus `rpow_lintegral_le_lintegral_rpow`
   (Jensen) and `lintegral_rpow_sum_le` (Minkowski).
6. ✅ `Ttc.CVHolderRetryCost.lintegral_stepCost_rpow_le` — **`∫ ((ell·acc)⁻¹)^{1+1/(2n)} dπ ≤
   80`, an absolute constant.** This is the `L^p(π)` hypothesis the lever needs, and it is
   the whole content of the route: at `p = 1` the same integral is the *existing* `10/3`, and
   the fractional moment says the `p`-th costs only a bounded factor more.
7. ⬜ **The retry-cost lemma** — apply `sum_lintegral_le_of_isWarm_holder` to
   `lintegral_accumulatedCost_embeddedMarginal`'s exact identity. Two obstacles, both known:
   * `candidateMeanⱼ` is a `t`-step mean, so its `L^p(π)` norm needs Minkowski over kernel
     iterates plus invariance (`Kernel.Invariant (lazy (speedyMetropolisGaussian …))
     (ellGaussianProb …)`, already proved at `SpeedyGaussian.lean:484`); Jensen and Minkowski
     are in place for this.
   * `lintegral_lazyProperTotalCost_le_half_exitMeanSum` carries `[IsProbabilityMeasure mu]`
     while `runningCurrentⱼ` is **unnormalised** with mass `sⱼ`. Normalising at `νⱼ := sⱼ⁻¹ •
     μⱼ` and warmness `M/sⱼ` lands at the same `M^{1/p}·sⱼ^{1/q}`, since
     `sⱼ·(M/sⱼ)^{1/p} = M^{1/p}·sⱼ^{1/q}`; it needs `iterate P (c • μ) = c • iterate P μ`.
8. ⬜ Rewire `slowUniformRetainedRealEnvelope` (`CVSlowEffectiveOverhead.lean:873`), then
   `perPhaseLenv`, then a **fourth capstone**.

**Where the honest stopping point is.** Steps 1–6 are the mathematics, and they are done and
axiom-clean. Steps 7–8 are the engineering, and step 8 is the known long pole: the recorded
warning in `RUNTIME-ENDGAME.md` — *any* new capstone must mirror the law layer again — applies,
and this one additionally threads `η`, `r` and the survival hypothesis to call sites that today
receive only `hwarm`. Until step 8 lands, **the operative complexity is unchanged at
`Õ(m n⁶ρ⁸/ε⁴)`**: Arlib and the cost lemma certify mathematics, not TTC's runtime.
