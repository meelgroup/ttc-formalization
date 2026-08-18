# The KLS97 shrunken-body deficit bound at branch-A `δ` — what it actually takes

**Status: third draft.  The two earlier drafts are both superseded, and the second one was
wrong in the direction that matters.**  This draft is written against the primary source
(`vol5.pdf` = Kannan–Lovász–Simonovits, *Random walks and an `O*(n⁵)` volume algorithm for
convex bodies*, RSA 11 (1997)), not against Cousins–Vempala's citation of it.

## 0.  Correction to the second draft

The second draft (commit `8c00b74`) concluded:

> Treat this as **one named external theorem to be formalized**, in the same category as
> `hIso`/localization … rather than as an engineering task.

**That is wrong.**  It was inferred from Cousins–Vempala's *citation*, which points at KLS
1995 (the localization paper) and quotes an averaged deficit bound with no theorem number.
Reading KLS97 itself shows the imported statement is **Theorem 4.16**, and its proof is
three lines of elementary convex geometry that use **no isoperimetry, no localization, and
no integral geometry**.  In particular it does *not* go through KLS97's Lemma 4.3 /
Corollaries 4.4–4.6 (the surface/volume route).  Those exist in the paper and are used
elsewhere, but they are **not** what `lem:map-speedy-to-ball` needs, and the surface-area
route should not be resurrected — see §5.

## 1.  The statement, quoted

KLS97 **Theorem 4.16**:

> Assume that `|P − Q̂|_tv ≤ ε`, `B ⊆ K`, and `δ ≤ 1/√(8n ln(n/ε))`.  Then the distribution
> `P'` of the point `v` returned by Algorithm 4.15 satisfies `|P' − Q|_tv < 10ε`.  The
> expected number of calls on Algorithm A is at most 2.

This *is* Cousins–Vempala's `lem:map-speedy-to-ball` (`1409.6011/vol3_journal.tex:942`),
including the `10ε` and the "constant number of samples in expectation".  The two facts CV
quote as inputs are established *inside* KLS97's proof of 4.16, not imported into it.

The proof's own words, with `c = 1 − 1/(2n)` and `B' = δB`:

> We start by estimating the average local conductance on `cK`.  We have
> `vol(B')·∫_{cK}(1−ℓ(x))dx = vol₂ₙ({(x,y) ∈ ℝ²ⁿ : x ∈ cK, y ∉ K, ‖x−y‖ ≤ δ})`.
> Let `t > 0`.  For each `y ∉ (1+t)K`, we have that there is a tangent hyperplane to
> `(1+t)K` separating `y`, and the parallel tangent hyperplane to `cK` is at least (in
> perpendicular distance) `1 − c + t` away (since `B ⊆ K`).  So we get, by Lemma 2.9, that
> `vol((y+B') ∩ (cK)) ≤ e^{−n(1−c+t)²/(2δ²)}·vol(B') ≤ e^{−1/(8nδ²)}·e^{−t/(2δ²)}·vol(B')`.
> The volume of `(1+t+dt)K ∖ (1+t)K` is `n(1+t)^{n−1}vol(K)dt`, which is at most
> `n·e^{nt}·vol(K)dt`, and so by integrating with respect to `t`, we get
> `∫_{cK}(1−ℓ(x))dx ≤ vol(K)·½·e^{−1/(8nδ²)} < ε·vol(cK)`.  Hence it follows that
> `Q̂(cK) > ½`.

(The OCR of the displayed constant reads `e^{−1/(8n²)}`; the `δ` is lost in extraction —
`1/(8nδ²)` is what the hypothesis `δ ≤ 1/√(8n ln(n/ε))` is calibrated to make `≥ ln(n/ε)`.)

And KLS97 **Lemma 2.9**, the only external input:

> Let `H` be a halfspace in `ℝⁿ` not containing the center of the unit ball `B`.  If the
> distance of `H` from the center is `1/√n < t ≤ 1`, then
> `(1/(10t√n)) ≤ vol(H ∩ B)/vol(B) < (1/(t√n))(1−t²)^{(n+1)/2} < e^{−nt²/2}`.

Only the `< e^{−nt²/2}` half is consumed.

## 2.  Inventory — five items

### (1) The cap bound — *cheap*, and cheaper than KLS's own statement

We need only `vol(B(0,δ) ∩ {z : ⟨u,z⟩ ≥ s})/vol(B(0,δ)) ≤ e^{−n s²/(2δ²)}` for `‖u‖ = 1`.
Two lines, no one-dimensional integral, no `(1−t²)^{(n+1)/2}`:

> for `‖z‖ ≤ 1` and `⟨u,z⟩ ≥ t`:  `‖z − t·u‖² = ‖z‖² − 2t⟨u,z⟩ + t² ≤ 1 − 2t² + t² = 1 − t²`.

So the cap is contained in `B(t·u, √(1−t²))`, and the ratio is at most
`(1−t²)^{n/2} ≤ e^{−nt²/2}` by `1 − x ≤ e^{−x}`.  Scaling `δ` in and out is
`Measure.addHaar_ball` / the same `addHaar_smul` already used by `MeasureShrinks`.

Note this proves the *sharp* form KLS state as "well-known" without their `1/(t√n)` factor,
and with no lower bound on `t` (their `t > 1/√n` restriction is only needed for the *lower*
bound, which we do not use).

### (2) The separation step — support functions

For `x ∈ cK`, `y ∉ (1+t)K`, `B(0,1) ⊆ K`, and `K` convex:  Hahn–Banach gives a unit `u` with
`⟨u,y⟩ ≥ h_{(1+t)K}(u) = (1+t)·h_K(u)`, while `⟨u,x⟩ ≤ h_{cK}(u) = c·h_K(u)`.  Hence

    ⟨u, y − x⟩ ≥ (1 + t − c)·h_K(u) ≥ 1 + t − c = t + 1/(2n),

the last step because `B(0,1) ⊆ K ⟹ h_K ≥ 1`.  So `(y + δB) ∩ cK` is inside a cap of
`y + δB` at height `s = t + 1/(2n)`, and (1) applies.  Then

    n(t + 1/(2n))²/(2δ²) ≥ n·(2t/(2n) + 1/(4n²))/(2δ²) = t/(2δ²) + 1/(8nδ²).   ✓

### (3) The dilate layer-cake — the Minkowski gauge

`∫_{ℝⁿ∖K} F(g_K(y)) dy = ∫_1^∞ F(s)·n s^{n−1}·vol(K) ds`, where `g_K` is the gauge of `K`.
This is exactly `vol({g_K ≤ s}) = vol(sK) = sⁿ·vol(K)` — the same `n`-homogeneity that
`Arlib.MarkovChains.MeasureShrinks` and `Measure.addHaar_smul` already carry — turned into a
pushforward density.  With `F(s) = e^{−(s−1)/(2δ²)}` and `(1+t)^{n−1} ≤ e^{nt}`:

    ∫_0^∞ n e^{nt} e^{−t/(2δ²)} dt = n/(1/(2δ²) − n),    valid when 2nδ² < 1.

### (4) The arithmetic

At `δ² ≤ 1/(8n ln(n/ε))` and `ε ≤ 1/10`: `ln(n/ε) ≥ ln 10 > 2`, so `1/(2δ²) ≥ 4n ln(n/ε) ≥ 8n`
and the factor in (3) is `≤ 1/7`; and `e^{−1/(8nδ²)} ≤ e^{−ln(n/ε)} = ε/n`.  Therefore

    ∫_{cK} (1 − ℓ) ≤ (1/7)·(ε/n)·vol(K) ≤ (2/7)·(ε/n)·vol(cK) ≤ ε·vol(cK),

using `vol(cK) = cⁿ vol(K) ≥ vol(K)/2`, which is **already proved** as
`Arlib.MarkovChains.half_le_one_sub_inv_two_mul_pow`.

### (5) The Gaussian weight — **this is the one genuinely open lemma**

Items (1)–(4) prove the **uniform** statement.  What Cousins–Vempala consume, and what our
`half_le_speedy_shrunken` is stated for, is the **Gaussian-weighted** deficit
`∫_{cK}(1−ℓ(x))·f(x)dx ≤ ε·∫_{cK} f`.

CV get there by a level-set decomposition (`vol3_journal.tex:956–963`), applying the KLS
bound to each `μ_L = {f ≥ L} = K ∩ B(0,R_L)`.  **As written that display does not follow**:
KLS applied to the body `μ_L` covers the domain `c·μ_L`, but CV's domain is `μ_L ∩ cK`, and
`μ_L ∩ cK ⊄ c·μ_L`.  The remainder is `cK ∩ (B_{R_L} ∖ B_{cR_L})` and neither paper bounds
it.  Two ways to close it, both real work:

* **(5a) Direct weighted layer-cake — preferred.**  Run (3) against `μ_f` instead of Lebesgue.
  This works because a centred Gaussian is radially decreasing, so `f((1+t)x) ≤ f(x)` and
  hence `μ_f((1+t)K) ≤ (1+t)ⁿ·μ_f(K)` — the exact mirror of the existing
  `gaussianWeight_le_smul` used to discharge `MeasureShrinks` for the Gaussian in
  `LocalConductanceMoment.lean`.  The new cost is on the `x`-side of the Tonelli: the cap
  bound is stated for `y`, but the weight sits on `x`, and `‖x − y‖ ≤ δ` gives
  `f(x)/f(y) = exp((2⟨y, y−x⟩ − ‖y−x‖²)/(2σ²)) ≤ exp(‖y‖δ/σ²)`.  Absorbing that into `f`
  replaces the radius `r` by `r − δ` in the Gaussian, and the resulting mass ratio is
  `≈ (1 + δ/(σ√n))^{n−1} ≈ e^{δ√n/σ}`.  **So (5a) needs exactly `δ ≲ σ/√n`** — which is
  precisely what branch A supplies (`δ ≤ min{σ,1}/(8√(n log(n/ε)))`), with the `√log` to
  spare.  Verify this side condition against the per-phase `σ` before building on it.
* **(5b) Level sets with the annulus remainder.**  Recurses to the same integral with
  `f(x/c)`; converges only after absorbing an extra factor into `ε`, i.e. at a slightly
  smaller `δ`.  Fallback only.

Item (5) is the one to scope first.  It is where this development's §11 failure mode lives:
the step that reads as bookkeeping is the step that is actually unproved.

## 3.  What already exists

| Need | Have |
|---|---|
| `cⁿ ≥ 1/2` at `c = 1 − 1/(2n)` | `half_le_one_sub_inv_two_mul_pow` ✔ |
| `n`-homogeneity of Lebesgue under `s • K` | `MeasureShrinks`, `addHaar_smul` ✔ |
| Gaussian version of the same | `gaussianWeight_le_smul` ✔ |
| `ell` as `vol(K ∩ ball x δ)/vol(ball x δ)` | `ell`, `ell_mul_volume_ball` ✔ |
| Ball/halfspace volume plumbing | `SphereCap.lean`, `EuclideanMeasureSlicing.lean` — survey before rebuilding |
| The deficit bound itself | **nothing** — `lintegral_one_sub_ell_shrunken_eq_zero` is the `ε = 0`, `δ ≤ 1/(2n)` case |

## 4.  Downstream — do **not** promise `n⁵` off this plan

`ell_eq_one_on_shrunken` is load-bearing in seven files: `MapSpeedyToTarget`, `WarmSpeedy`,
`SpeedyExactOnShrunken`, `LambdaFromShrunken`, `WastedStepsGaussian`, `ColdPhaseRegime`,
`SamplerStepCount`.  Several consume it as a **rewrite** (`rw [ell_eq_one_on_shrunken …,
one_mul]`), i.e. as the *equation* `ℓ = 1`, not as an inequality.  An `ε`-version is not a
drop-in for any of those; each site needs its own error term threaded through.  Audit that
before the exponent is claimed anywhere.

One thing that *does* dissolve: the branch-A blocker recorded in `AUDIT.md` — that warmness
`M` enters the query cost multiplicatively and the pointwise route would inflate it by
`(δ/λ)ⁿ` — was an artefact of reaching branch A through `ofReal_div_pow_le_ell`.  Theorem
4.16 never asks for a pointwise `ℓ` bound, so it never pays that factor.

## 5.  The route not to take

KLS97 §4.2 also contains an averaged conductance bound, and it is tempting because it looks
like the "average deficit" phrase CV use:

* **Lemma 4.3** — for `L ⊆ ∂K` measurable, the `2n`-measure of `{(x,y) : x ∈ K, y ∉ K,
  ‖x−y‖ ≤ δ, [x,y] ∩ L ≠ ∅}` is at most `δ·vol_{n−1}(L)·κ_{n−1}/((n+1)κ_n)·vol(δB)`.
* **Corollary 4.5** — `λ ≥ 1 − (δ/(2√n))·vol_{n−1}(∂K)/vol(K)`.
* **Corollary 4.6** — if `K` contains a ball of radius `r`, `λ ≥ 1 − δ√n/(2r)`.

This is **not** the input to `lem:map-speedy-to-ball`, and it is far more expensive to
formalize.  KLS's proof of 4.3 is "it suffices to prove the assertion for the case when `L`
is infinitesimally small… the measure is maximized when the surface of `K` is a hyperplane…
by a direct computation" — a genuine hand-wave.  A rigorous route needs Cauchy's projection
formula (`E_u[vol_{n−1}(π_{u^⊥}K)] = (κ_{n−1}/(nκ_n))·vol_{n−1}(∂K)`) plus the cone bound
`vol(K) ≥ (r/n)·vol_{n−1}(∂K)`; the `√n` lives entirely in `κ_{n−1}/(nκ_n) ≈ 1/√(2πn)` and
cannot be got by any per-direction argument.  Our existing layer bound
(`measure_lt_ell_le_mul`, giving `avg(1−ℓ) ≲ nδ`) is exactly the per-direction version, and
is `√n` weaker for that reason.

Where Corollaries 4.5/4.6 *are* needed is a separate, much smaller obligation: CV's
`vol3_journal.tex:1013` wants `λ ≥ 1/2` over all of `K` at branch-A `δ` to convert speedy
steps into ball-walk steps.  That does **not** need them either —

    ∫_K (1 − ℓ) ≤ ∫_{cK}(1 − ℓ) + vol(K ∖ cK) ≤ ε·vol(cK) + (1 − cⁿ)·vol(K),

and `cⁿ(1−ε) ≥ 0.54` at the standing hypothesis `21 ≤ n`.  One line, from (1)–(4).
