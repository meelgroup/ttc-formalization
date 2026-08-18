# Scope: the KLS97 average-deficit bound — the one missing input, and the whole `n`

**Superseded first draft.**  This file previously proposed replacing the phase-to-phase warm
start with an `ell`-weighted-to-`ell`-weighted transfer, on the theory that `ell ≡ 1` on a
shrunken body was our own device.  **That was wrong, and reading Cousins–Vempala settles it.**
The shrunken body *is* in the paper; what is ours is the *pointwise* way we establish the
conductance deficit on it.  The correct scope is below.

## 0. What the paper actually proves

Cousins–Vempala `lem:map-speedy-to-ball` (`1409.6011/vol3_journal.tex:942`) maps the speedy
walk's law `∝ ℓ·f` to the target `∝ f` by rejection at shrink factor `c = 1 − 1/(2n)` — the
same `c` we use — under the step-size hypothesis

```
δ  ≤  min{σ,1} / (8 √(n log(n/ε)))                     ← branch A
```

and it imports exactly two facts, cited as "[18]":

1. `Q̂(cK) ≥ 1/2`;
2. `∫_{μ_L ∩ cK} (1 − ℓ(x)) dx  ≤  ε · vol(μ_L ∩ cK)` — the **average** conductance deficit
   over the shrunken body is small.

(`Arlib/MarkovChains/Continuous/KLS97Shell.lean` already records that CV's citation is to the
wrong paper: [18] is KLS *1995*, which has no ball walk; the machinery is in KLS **1997**,
RSA 11, whose theorem numbers match.)

## 1. What we prove instead, and exactly what it costs

`KLS97Shell.lean` proves **both facts outright**, with no external input — but only because it
works at `δ ≤ 1 − c = 1/(2n)`, where the one-line convexity argument gives

```
x ∈ cK,  δ ≤ 1 − c   ⟹   ball x δ ⊆ K   ⟹   ℓ(x) = 1
```

i.e. fact 2 **pointwise, at `ε = 0`** (`ell_eq_one_on_shrunken`,
`lintegral_one_sub_ell_shrunken_eq_zero`), and fact 1 from the volume ratio
`(1−1/(2n))ⁿ ≥ 1/2` (`half_le_one_sub_inv_two_mul_pow`, `half_le_speedy_shrunken`).

That file's own docstring states the price, and it is precisely the gap this project has been
chasing:

> "Cousins–Vempala run at `δ ≤ min{σ,1}/(8√(n log(n/ε)))`, which is much *larger* than
> `1/(2n)` … in that regime the deficit does not vanish and the KLS97 average-deficit bound is
> genuinely needed.  What the regime here costs is a worse exponent, not polynomiality: …
> at `δ = Θ(1/n)` it reads `O(σ²n³·log(M/ε))` instead of `O(σ²n²·log(M/ε))`."

**So the entire `n⁶` vs the paper's `n⁵` is this one substitution**, and it was recorded in the
development before any of the present analysis.  The independent derivation in `AUDIT.md`
§0g — branch A ⟶ `δ` ⟶ shrunken body ⟶ warm constant in the cost — lands on the same
statement from the other end, which is a consistency check and nothing more.

## 2. The deliverable

Formalize **KLS97 fact 2 in its averaged form**:

```
theorem lintegral_one_sub_ell_shrunken_le
    (hK : convex, B_n ⊆ K)  (hδ : δ ≤ min σ 1 / (8 * √(n * log (n/ε))))
    (hL : Convex ℝ μ_L) :
    ∫⁻ x in μ_L ∩ (1 − 1/(2n)) • K, (1 − ell K δ x)  ≤  ofReal ε * volume (μ_L ∩ (1−1/(2n)) • K)
```

with fact 1 (`Q̂(cK) ≥ 1/2`) re-derived at the same `δ`, and then `radiusQDelta`'s `min`
resolved to branch A downstream.

## 3. Honest assessment of difficulty

This is a **genuine convex-geometry theorem from KLS97**, not bookkeeping.  What makes it hard
is what makes it true: at `δ = Θ(σ/√(n log))` the shrunken body's boundary layer is *thick*, so
`1 − ℓ` is **not** pointwise small — the estimate is available only after integrating, and only
because a convex body has little mass near a sharp corner.  The crude tail bound this
development already has,

```
measure_lt_ell_le_mul :  mu {x ∈ K | ell < (λ/δ)ⁿ} ≤ ofReal (n·λ) · mu K
```

(`LocalConductanceMoment.lean`, proved this session) integrates to `avg(1 − ℓ) ≲ nδ`, which at
branch A's `δ` is `≈ σ√n/8` — **vacuous**.  So the existing machinery does not reach it, and
the gap is not a matter of assembling what is here.

What *is* here and relevant: `ell` monotonicity in the step
(`ofReal_div_pow_mul_ell_le_ell`, proved this session), the layer bound and its
`MeasureShrinks` abstraction, `avgLocalConductance` / `IsSmooth`
(`BallWalk.lean:463`), and `SmoothSqrt.lean`'s `volume_shell_le`.  None of these is the KLS97
estimate, and none of them combines to it.

## 4. Recommendation

Treat this as **one named external theorem to be formalized**, in the same category as
`hIso`/localization — a piece of published convex geometry the development depends on and does
not yet have — rather than as an engineering task.  Do not attempt it as a variation on the
existing layer bound; the regimes are different and the existing bound is provably too weak
there.

Until it lands, `Õ(m n⁶ρ⁸/ε⁴)` is the honest figure, and the reason it is `n⁶` and not `n⁵` is
one lemma, precisely identified.
