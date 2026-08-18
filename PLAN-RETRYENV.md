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

**The `α`-th moment is bounded by an elementary convexity estimate.** For convex `K'` with
`ball 0 1 ⊆ K'`, `x ∈ K'`, and `u := d(x, ∂K')`:

* `conv({x} ∪ ball 0 1) ⊆ K'`, and `K' ⊇ ball x u`, so `ball x δ ∩ K'` contains a cone of
  height `~δ` on a base of radius `~u`, giving `ℓ(x) ≳ (u/δ)^{n-1}/n`;
* `(1-λ)K' ⊆ {u ≥ λ}` (since `(1-λ)K' + λ·ball 0 1 ⊆ K'`), so
  `vol{u < λ} ≤ (1-(1-λ)ⁿ)·vol K' ≤ nλ·vol K'`.

Together: `γ({ℓ < θ})/γ(K') ≲ nδ·(nθ)^{1/(n-1)}`, and with `δ ≤ 1/(2n)` the prefactor is
`≤ 1/2`. Integrating the tail,

```
∫ ℓ^{-α} dγ/γ(K')  ≤  1 + A·α(n-1)/(1 − α(n-1))       for α(n-1) < 1
```

so **`α := 1/(2(n-1))` gives an absolute constant**, and hence `p' = 1/α + 1 = 2n − 1`.

**The `sⱼ` factor.** With `sⱼ ≤ η + rʲ`
(`ContinuingRejectionSelective.badWeights_add_survival_le_eta_add_pow`),

```
∑ⱼ sⱼ^{1/p'}  ≤  L·η^{1/p'} + 1/(1 − r^{1/p'})  ≈  L·η^{1/(2n)} + 2n/(1−r)
```

and `η ≈ share ≈ e^{−cρ²}`, so `η^{1/(2n)} = e^{−cρ²/(2n)}`.

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

## 5. Build order

1. `ell_ge_of_dist_boundary` — the cone estimate `ℓ(x) ≥ c·(u/δ)^{n-1}/n`. New; elementary.
2. `volume_lt_dist_boundary_le` — `vol{u < λ} ≤ nλ·vol K'` from `(1-λ)K' ⊆ {u ≥ λ}`.
3. `lintegral_ell_rpow_neg_le` — the `α`-th moment bound, `α = 1/(2(n-1))`.
4. `lintegral_le_of_isWarm_holder` — Hölder replacement for `lintegral_le_of_isWarm`, in
   `Arlib/MarkovChains/Continuous/`; Mathlib's `ENNReal.lintegral_mul_le_Lp_mul_Lq`.
5. `sum_survival_rpow_le` — `∑ⱼ sⱼ^{1/p'} ≤ L·η^{1/p'} + 1/(1−r^{1/p'})`.
6. `lintegral_accumulatedCost_embeddedMarginal_le_holder` — the replacement for `…_le`.
7. Rewire `slowUniformRetainedRealEnvelope` (`CVSlowEffectiveOverhead.lean:873`), then
   `perPhaseLenv`, then the capstone.

Steps 1–3 are the crux and are self-contained: if the cone estimate does not formalise, the
route dies there and nothing downstream is wasted.
