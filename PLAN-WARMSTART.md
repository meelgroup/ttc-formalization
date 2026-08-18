# Scope: a replacement warm start that does not route through `ell ≡ 1`

The specification, from `AUDIT.md` §0g: deliver an `O(1)` warm constant for the phase-to-phase
start **without** using `ell ≡ 1` on a shrunken body.  That is what pins `δ = Θ(1/n)`, and
`δ = Θ(1/n)` is what costs the factor `n` between our `Õ(m n⁶ρ⁸/ε⁴)` and the paper's `n⁵`.

Written 2026-08-18 from the source.

## 0. Why `ell ≡ 1` is there at all — the diagnosis that suggests the fix

The chain currently starts phase `i+1` from **`condOn (coolLaw i) (c·K)`**: the previous
phase's law, which is an `ell`-*free* truncated Gaussian, conditioned onto the shrunken body.
Its target is `ellGaussianProb K δ σ²`, whose density carries the extra factor `ell`
(`WarmSpeedy.lean:59`, `:69–75`).

So the transfer is between an `ell`-free law and an `ell`-weighted one, and the whole job of
the shrunken body is to force `ell ≡ 1` on the support so the mismatch costs nothing —
`isWarm_ellGaussianProb_of_supported_on_shrunken` is advertised as "*with the same
constant*" for exactly that reason.  Without it the sup-ratio really is unbounded
(`exists_supported_on_shrunken_not_isWarm`).

**The mismatch is the problem, not the bound.**  If *both* ends of the transfer are
`ell`-weighted, `ell` cancels in the density ratio and no shrunken body is needed.

## 1. The proposal: transfer `ellGaussianProb i → ellGaussianProb (i+1)`

```
d(ellGaussianProb K δᵢ σᵢ²)      ell_{δᵢ}(x) · γ_{σᵢ}(x) / Zᵢ        ell_{δᵢ}(x)   γ_{σᵢ}(x)   Zᵢ₊₁
──────────────────────────── =  ──────────────────────────────  =  ─────────── · ───────── · ────
d(ellGaussianProb K δᵢ₊₁ σᵢ₊₁²)  ell_{δᵢ₊₁}(x) · γ_{σᵢ₊₁}(x) / Zᵢ₊₁   ell_{δᵢ₊₁}(x)  γ_{σᵢ₊₁}(x)   Zᵢ
```

Three factors, each of which must be `O(1)`.

### (a) The `ell` ratio — `O(1)`, and the lemma is two lines

The two `ell`s are at *different* `δ`, since `δ = radiusQDelta n q σ²` moves with the phase, so
they do not cancel identically.  They are nonetheless comparable, by pure monotonicity:

```
ell K δ x  =  vol(B(x,δ) ∩ K) / vol(B(x,δ))
           ≥  vol(B(x,δ') ∩ K) / ((δ/δ')ⁿ · vol(B(x,δ')))          for δ' ≤ δ
           =  (δ'/δ)ⁿ · ell K δ' x
```

— the numerator is monotone in `δ` and the denominator scales by `(δ/δ')ⁿ`.  **This is a
strictly easier lemma than `ofReal_div_pow_le_ell_of_ball_subset`, which is already proved**
(`LocalConductanceMoment.lean`), and it needs no convexity.

And the constant is `O(1)` because the cooling schedule is slow.  `PhaseSchedule.lean:150–160`:
`σᵢ₊₁² = σᵢ²(1 + α)` with `α = coolRate ≈ κ/(4(n+1)L) = Θ(1/(nL))`.  At branch A's
`δ = √(σ²)/(max 8 (2q) · √n)`,

```
(δᵢ₊₁/δᵢ)ⁿ = (1 + α)^{n/2} = exp(Θ(1/L)) = Θ(1).
```

**The `ell` mismatch across one cooling step costs an absolute constant.**  This is the
load-bearing observation, and it is the reason the proposal is worth doing.

### (b) The Gaussian ratio — existing

`γ_{σᵢ}/γ_{σᵢ₊₁}` at one cooling step is the standard Gaussian-cooling bound the development
already proves; it is where the `2e` in `isWarm_condOn_coolLaw_ellGaussianProb` comes from.

### (c) The normaliser ratio `Zᵢ₊₁/Zᵢ` — needs a lemma, expected `O(1)`

`Z = ∫_K ell·γ`.  Both factors move by `O(1)` per step by (a) and (b), so `Z` does too; but it
is an integral ratio, not a pointwise one, and it deserves its own statement.

## 2. The composition obstacle, and why it is already solved

The chain does not *have* `ellGaussianProb i` at phase `i+1`; it has the sampler's output,
which is only `TVLe`-close to it.  Warmness does not transport across TV — that is
`not_exists_isWarm_transport_of_tvLe_reference`
(`Arlib/Convexity/GaussianCooling/WarmTransportExperiment.lean`), a machine-checked no-go from
this development.

But warmness **never needs to be transported**.  The same file proves

```
tvLe_iterate_of_isWarm_source :
  (∀ ρ, IsWarm M ρ π → TVLe (iterate P ρ t) π ζ) → IsWarm M ν₀ π → TVLe μ ν₀ ε
    → TVLe (iterate P μ t) π (ε + ζ)
```

— run the mixing chain against the law that *is* warm and pay the gap **additively**.  The
earlier `IsWarm` experiment found this device sufficient at all 13 uses of the equality it was
meant to replace, and found the residual blocker to be exactly the *second*, independent use of
`ell ≡ 1` at `isWarm_ellGaussianProb_of_supported_on_shrunken`.  **This proposal removes that
second use**, which is precisely what the experiment identified as the thing standing in the
way.

## 3. What this buys, and what it does not

Removing `ell ≡ 1` removes the constraint `δ ≤ 1 − c` with `c = 1 − Θ(1/n)`, hence permits
branch A, hence `Tenv : n³ → n²`, hence

```
Õ( m · n⁶ · ρ⁸ / ε⁴ )   →   Õ( m · n⁵ · ρ⁸ / ε⁴ )
```

matching the paper's `n` exponent.  It does **not** touch the `ρ` exponent: `ρ⁴` of the `ρ⁸` is
a proved *lower* bound on this sampler's TV accounting (`CVRetryDeadlineSplit`), and one `ρ²`
is the `retryEnv` lever, already proved as mathematics (`PLAN-RETRYENV.md`) and awaiting its
rewire.

## 4. Order of work, cheapest decisive step first

1. **`ell_mono_ratio`** — `(δ'/δ)ⁿ · ell K δ' x ≤ ell K δ x` for `δ' ≤ δ`.  Two lines, no
   hypotheses beyond `0 < δ'`.  Do it first: it is the load-bearing new fact and it is nearly
   free.
2. **`ell_ratio_le_of_coolStep`** — instantiate (1) at `δᵢ₊₁/δᵢ = √(1+α)` and bound
   `(1+α)^{n/2} ≤ e^{1/2}` from `coolRate`'s definition.  Small.
3. **`isWarm_ellGaussianProb_succ`** — the (a)·(b)·(c) product, at an explicit `O(1)` constant.
   This is the replacement for `isWarm_condOn_coolLaw_ellGaussianProb`, and (c) is the only
   part needing genuinely new work.
4. **Re-thread the phase chain** through `tvLe_iterate_of_isWarm_source` instead of the
   `condOn (coolLaw i) (c·K)` start.  This is the large edit; `WarmSpeedy.lean`'s scope note
   ("composing across phases … is not done here") marks exactly the seam.
5. **Only then** move `radiusQDelta` to branch A and re-derive `Tenv`.

**Honest status of the estimate.**  Steps 1–2 are certain.  Step 3(c) is expected but unproved.
Step 4 is the long pole and touches the accuracy/TV budget, which this document has *not*
checked — the additive `ε` from `tvLe_iterate_of_isWarm_source` has to fit inside the existing
per-phase budget, and whether it does is the first thing that could kill the route.
