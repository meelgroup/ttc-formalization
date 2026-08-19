# `unifSphere_cap_le` below dimension 1100 — the one lemma that removes the hole

**Target.**  `Arlib.MarkovChains.unifSphere_cap_le` currently carries `1100 ≤ n`.  Prove it at
`n ≥ 21` (TTC's own floor), or at any threshold `≤ 21`.

**Payoff.**  It is the *only* thing standing between the development and a uniformly
polynomial sampler.  `Ttc.kv97HybridSteps` branches at `1100`; above it the walk is
hit-and-run with the polynomial bound, below it the lazy ball walk, whose `Ttc.mixStepsBound`
carries `4^n · ((γ+Dm)/γ)^(4n)`.  TTC's capstone admits `21 ≤ n`, so today the proved bound is
astronomical on `21 ≤ n < 1100` — a constant, since `n` is bounded there, but a constant of
size `4^1099`.  Lowering the threshold deletes the low branch, deletes
`Ttc.lowDimBallWalkEnvelope`, and makes the sampler `n²ρ²·log(8Mw/ε²)` at every dimension the
capstone admits.

Secondary payoff: the cap constant improves from `9/25 = 0.36` toward the sharp
`2(1−Φ(1)) = 0.31731…`, and Lemma 4.1's constant from `1 − 1/8000` toward `1 − 1/1892.8`.

## 1.  The statement is not the problem — the proof is

`Arlib/MarkovChains/Continuous/SphereCap.lean` says so itself (`:59`):

> **The threshold is `n ≥ 1100`, and it is an artifact of the method, not of the statement.**
> The estimate `σ ≤ 0.36` is in fact true from about `n = 8` on (the true value is `0.363` at
> `n = 6` and `0.351` at `n = 8`), and `q₂ < 3/8` from `n = 5` on; for `n ≤ 4` it is false
> (`q₂ ≥ 0.391`), so *some* dimension hypothesis is mandatory.  What forces `1100` here is that
> the Chernoff piece decays like `0.994ⁿ`, and `c` cannot be pushed towards `1` without
> inflating it.

So a dimension hypothesis is unavoidable — `q₂(2) = 1/2`, `q₂(3) = 0.4226…` — but `n ≥ 21` is
far above where the statement becomes true.

## 2.  Retuning the union bound is RULED OUT, not merely hard

The proof bounds the Gaussian mass of the cone `{∑ xᵢ² < (m+1)x₀²}` by
`{|x₀| ≥ c}` ∪ `{the remaining m coordinates are atypically small}`, the second by a Chernoff
estimate at rate `λ`.  With `m = n − 1` the two contributions are

```
2(1 − Φ(c))        and        [ (1/√(2λ+1)) · e^{λc²} ]^m
```

**Optimising over `λ`** gives `λ* = (1/c² − 1)/2`, at which the Chernoff base is exactly

```
f(c) = c · e^{(1−c²)/2}
```

(At `c = 23/25` this is `0.9934` — the `0.994ⁿ` the file quotes, so the shipped constants are
already `λ`-optimal.)  `f` is increasing on `(0,1)`, so lowering `c` buys decay at the cost of
the tail.  Minimising `g(c) = 2(1−Φ(c)) + f(c)^m` at `m = 20`:

| `c` | `2(1−Φ(c))` | `f(c)^20` | total |
|---|---|---|---|
| 0.92 | 0.358 | 0.876 | 1.233 |
| 0.70 | 0.484 | 0.135 | 0.619 |
| **0.62** | 0.535 | 0.033 | **0.568** |
| 0.50 | 0.617 | 0.002 | 0.619 |

**The best achievable bound at `n = 21` is ≈ 0.57, against a target of `9/25 = 0.36`.**  No
`(c, λ)` works.  Running the same optimisation the other way: to reach `0.36` one needs
`2(1−Φ(c)) < 0.36`, hence `c > 0.916`, at which `f = 0.9928` and `m ≳ 835` — which is where
`1100` comes from.

**Corollary: weakening the target does not rescue it either.**  The true value at `n = 21` is
≈ 0.33 and the union bound gives ≈ 0.57; any target the union bound can meet at `n = 21` is
one the downstream conductance argument cannot use.

## 3.  The route: the exact density

`P(|⟨θ,ŵ⟩| > t)` for `θ` uniform on `S^{n−1}` is

```
( ∫_t^1 (1−s²)^{(n−3)/2} ds ) / ( ∫_0^1 (1−s²)^{(n−3)/2} ds )
```

and the claim is that this is `≤ 9/25` at `t = 1/√n`, for `n ≥ 5`.  Equivalently, in the
Gaussian picture the file already works in: `⟨θ,ŵ⟩ =_d X₁/‖X‖` for `X ~ N(0, Iₙ)`, so

```
P(|⟨θ,ŵ⟩| > 1/√n) = P(n·X₁² > ‖X‖²) = P(B > 1/n),   B = X₁²/‖X‖² ~ Beta(1/2, (n−1)/2).
```

### What Mathlib has, and the one thing it does not

* ✔ `Mathlib/Probability/Distributions/Beta.lean` — `betaPDF`, normalisation, `lintegral_betaPDF_eq_one`.
* ✔ `Mathlib/Probability/Distributions/Gamma.lean`.
* ✔ `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean` — the radial/sphere disintegration.
* ✘ **No bridge.**  There is no "`X ~ Γ(a)`, `Y ~ Γ(b)` independent ⟹ `X/(X+Y) ~ Beta(a,b)`",
  and no sphere marginal density.  **This is the work.**  The estimate afterwards is routine
  calculus on an incomplete Beta ratio.

### Two ways to build the bridge

1. **Gamma → Beta.**  `X₁² ~ Γ(1/2, 2)` and `∑_{i≥2} Xᵢ² ~ Γ((n−1)/2, 2)`, independent; then
   `X₁²/‖X‖² ~ Beta(1/2,(n−1)/2)`.  Needs the change of variables `(u,v) ↦ (u+v, u/(u+v))` and
   independence of the coordinate blocks.
2. **Sphere marginal directly**, via `HaarToSphere` — push `unifSphere` forward along
   `θ ↦ ⟨θ,ŵ⟩` and identify the density as `∝ (1−t²)^{(n−3)/2}`.

Route 1 is the more mechanical of the two and reuses more of Mathlib.

## 4.  Non-goals

* **Do not attempt a sharper union bound.**  §2 rules it out at the required threshold; a
  reviewer who tries will rediscover the table.
* **Do not weaken the downstream target to fit.**  Same reason.
* This lemma is about the *sampler*.  It does not touch the `ρ⁶` in the volume overhead
  (`lem:variance-bound`, `PLAN-SHAPE.md` §5) nor the step size (`PLAN-WARMSTART.md`).

## 5.  Definition of done

* `unifSphere_cap_le` at `n ≥ 21` or lower, axiom-clean.
* `Ttc.hybridTransitionBound`'s low branch deleted and `Ttc.kv97HybridSteps` un-branched, or
  the branch kept with the low side unreachable at `21 ≤ n`.
* `Ttc/Exec/SamplerEnvelopeShape.lean`'s `…_of_low` family retired — their hypothesis becomes
  unsatisfiable, which is the point.
* `Ttc.lowDimBallWalkEnvelope` unused and removable.
