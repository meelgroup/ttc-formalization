# Audit of `thm:runtime` and its appendix proof

Read against `sections/analysis.tex` (`thm:runtime`, lines 53–65) and
`sections/proof-appendix.tex` (`claim:linf`/`cor:linf`, lines 153–197; `claim:vol`/`cor:vol`,
lines 198–224).

**Summary.**  The combination step — from the two per-cube prices to `O(m n⁵ ρ² r_max)` — is
sound, and is the part this repository machine-checks
(`Ttc.TTCRuntimePaperArithmetic.paperRuntimeEnvelope_le_quintic`).  The risk is concentrated
in the two corollaries.  One of them has a **proof step that does not hold**, though its
conclusion is true and one line away.  Two suppressions are undeclared or unargued.

## 1.  `cor:vol`'s proof has an invalid step.  The result is true; the argument is not

The proof bounds the second moment of the rescaled polytope `P* = P/γ ⊆ B(R/γ)` by

```
E_{P*}[‖X‖²] = (1/vol P*) ∫_{P*} ‖x‖² dx  ≤  (1/vol P*) ∫_{B(R/γ)} ‖x‖² dx  =  O((R/γ)²)
```

The inequality is fine (nonnegative integrand, larger domain).  **The final equality is not.**

```
(1/vol P*) ∫_{B(R/γ)} ‖x‖² dx  =  (vol B(R/γ) / vol P*) · (n/(n+2)) · (R/γ)²
```

and all that is known about the normaliser is `B(1) ⊆ P*`, so `vol B(R/γ)/vol P*` may be as
large as `(R/γ)ⁿ`.  What the displayed chain actually yields is `O((R/γ)^{n+2})` —
**exponential in `n`**, which would not merely weaken `cor:vol` but destroy it, since
`claim:vol`'s complexity is linear in the second moment.

**The conclusion is nevertheless correct, and needs no integral comparison at all:**
`P* ⊆ B(R/γ)` gives `‖x‖₂ ≤ R/γ` *pointwise* on `P*`, hence `E_{P*}[‖X‖²] ≤ (R/γ)²`
immediately.  One line replaces the three-step display.

This is a presentation defect, not a hole in the result.  But as written the step is not
valid, and a reader checking it will stop there.

## 2.  The volume line of `thm:runtime` multiplies by `n·r` without saying so

`cor:vol` delivers `max(R²n²/γ², n³)/ε² · (logs)` — and that is a count of **membership-oracle
calls**, because `claim:vol` is Cousins–Vempala Theorem 1.1, stated in the membership-oracle
model.  `thm:runtime`'s proof then charges the volume computation

```
O( max(n³R²/γ², n⁴)/ε² · r )   time
```

i.e. `cor:vol`'s count times `n · r`.  That conversion is *correct* — one membership test on
`Ax ≤ b` is `r` rows of `n`-dimensional dot product — and it is exactly what `cor:linf` states
for its own steps ("each step costing `O(n·r)` arithmetic operations").  But `cor:vol` never
states it, so on the volume line both the `n` and the `r` appear at the point of use with no
supporting statement.

## 3.  `log R` is suppressed but is not on the declared list

`cor:linf` concludes `O(n⁴ (R²/γ²) log R)` steps.  `thm:runtime`'s proof uses
`O(n⁵ r R²/γ²)` per sample — the `log R` is gone.  The theorem declares that `O(·)` suppresses
"factors that are polynomial in `1/ε`, poly-logarithmic in `1/δ`, `m`, `n`, and warm-starting
costs for sampling".  `R` is an input-dependent radius and appears in none of those.

## 4.  `claim:vol` quotes Cousins–Vempala one log factor short

`claim:vol` states the complexity as

```
max(R²n², n³)/ε² · log²n · log²(1/ε) · log(n/ε) · log(1/δ)
```

Cousins–Vempala's Theorem 1.1 (arXiv:1409.6011 `thm:volume`) reads `… log²(n/ε) …` — squared.
The quotation drops one power, which makes the cited result *stronger* than its source rather
than weaker.  Immaterial to the headline (all logs are suppressed there), but it is an
over-quotation, not a conservative simplification.

## 5.  The warm start is declared-suppressed, and that is doing real work

`cor:linf` realises the sampling oracle by hit-and-run, citing Theorem 1.1 of LV04 for
`O(n³ (R²/γ²) log(1/ν))` steps, with a footnote: *"Where `O(·)` hides the dependence of warm
start."*  `thm:runtime` then declares warm-starting costs suppressed.

Two things are unargued:

* **Where the warm start comes from.**  TTC draws up to `Threshold` samples per polytope,
  across `m` polytopes.  The usual device — reuse the previous sample as the next start — needs
  an argument, and interacts with the independence the estimator wants.  Nothing in the
  appendix supplies one.
* **Whether suppressing it is safe.**  If the warm-start parameter `M` enters the mixing bound
  only inside a logarithm, a cold `M ≈ ρⁿ` contributes `log M = Θ(n log ρ)`, which is the same
  order as the `n log(2R)` the proof already carries in `log(1/ν)` — so it would be absorbed.
  If it enters multiplicatively, it would not be.  **The paper does not say which**, and the
  footnote's phrasing ("dependence of warm start") does not settle it.

This is the same gap the formalization independently hit: `Ttc.ttcSampWarm` is a volume ratio,
so `log Mw = Θ(n log ρ)` (`PLAN-SHAPE.md` §5.7(b)).

## 6.  What is sound

The step most likely to be doubted — collapsing

```
m · r_max · ( max(n³R²/γ², n⁴)/ε²  +  n⁵ R²/γ² · Threshold )   ⟶   O(m n⁵ ρ² r_max)
```

— is correct, and is machine-checked here as
`Ttc.TTCRuntimePaperArithmetic.paperRuntimeEnvelope_le_quintic`, with `ε⁻²` and `Threshold`
left visible rather than hidden.  Both branches of the volume maximum are `≤ n⁵ρ²`, and the
sampling term is already in that shape.

`thm:decompose` is also honest about the elephant: `m` itself can be exponential in the number
of variables, so "polynomial" here means polynomial in `n` and `m`, not in the input formula.
