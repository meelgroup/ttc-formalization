# Scope: carrying the proved `n⁶` bound onto `Ttc.ttc`

What it would take for `Ttc.ttc_volume`'s cost conjunct (`Ttc/Model/Theorem.lean`) to state a
bound that is *proved* for the oracle the algorithm actually runs, instead of a *declared*
per-call price.  Written 2026-08-18 from the source, not estimated.

## 0. The headline finding: the shape is not the obstacle

`Ttc.ttc_volume_estimate_parametric` (`Ttc/Exec/PricedHeadline.lean:121`) already proves, for
**every** `cVol cSample : ℕ`,

```
All[r ← ttcCharged atoms φ ε δ cVol cSample;
    (r.2 : ℝ) ≤ m · (cVol + cSample · (Θ + 1))]
```

and `Ttc.ttc = ttcCharged … (cvVolPriceAt …) (hrSampPriceAt …)` **by `rfl`**
(`Ttc.ttc_def`, `Model/Pseudocode.lean:923`).  So the cost conjunct is price-parametric
already: nothing about `m · (cVol + cSample·Θ)` has to change.  **The entire question is what
justifies the number substituted for `cVol`.**

Today that number is `Ttc.cvVolPriceAt` (`Model/Pseudocode.lean:848`) — a *declared* constant
of Gaussian-cooling shape (`coolPhases`, `lsThreshold`).  Nothing proves the constructed
volume subroutine costs it.  That is the whole of §1e's accounting defect, in one line.

## 1. What the capstone gives, and how it is shaped

`ttc_volume_runtime_perPhase` bounds

```
∫⁻ r, r.2 ∂canonicalFullOperationalLaw V P
    ≤ shapedVolumeQueryEnvelopeAt I atoms φ ε δ (fun j ↦ circumR (interior (callBody … j))²)
      + canonicalCappedSampleQueryEnvelope atoms φ ε δ
```

and `shapedVolumeQueryEnvelopeAt` (`CVShapedExpectedImplementation.lean:266`) is literally

```
∑ j : Fin (toDNFd (preprocess atoms φ)).length,
    ofReal (I.runtimeConstant * shape n (R2j j) ε' δ')
```

— a sum over **the same `m` cubes** the `ttcCharged` bound multiplies by.  The two statements
are therefore already index-aligned.  Three differences remain, in increasing order of cost.

## 2. The three gaps

### (a) Per-cube vs uniform — easy

The capstone charges cube `j` at its own `circumR(interior (callBody … j))²`; `m · cVol`
charges every cube the same.  Collapsing `∑_j shape(ρ_j²)` to `m · shape(ρ_max²)` is
monotonicity in `R2`, and `slowActualOverhead`/`shape` already have the `mono_R2` lemmas
(`CVSlowActualCostEnvelope.lean:135`).  **This is where the paper's `r_max` enters**, and it
is the expected and honest place for it.

### (b) Expectation vs almost-sure — the crux, and it is mathematical

`ttcCharged`'s conjunct is `All[…]`, i.e. `∀ᵐ`; the capstone's is `∫⁻`, an expectation.  An
expectation bound does not give an almost-sure one, and here it genuinely cannot: the real
per-step cost is `Arlib.MarkovChains.properProposalWaitCost`
(`ProperProposalCostedRestart.lean:25`), a **tail-sum geometric waiting time**, unbounded on
every path space where the walk can stall.  This is the same fact that killed Route A of the
`retryEnv` lever (`PLAN-RETRYENV.md` §1).  So at the true oracle cost there is **no finite
`cVol` for which `All[…]` holds**, and the choice is forced:

1. **Restate the cost conjunct as an expectation** — `∫⁻ r, r.2 ∂ttc … ≤ …`.  Honest, and it
   matches what is proved; but it changes the main theorem's shape, and `All[…]` with no
   termination hypothesis is currently one of its selling points.
2. **Use the cap.**  The construction is already *capped* —
   `canonicalCappedPolyHybridPlugin`, `canonicalCappedSampleQueryEnvelope`.  If the capped run
   has a deterministic worst-case query count (the cap), then `All[…]` survives at
   `cVol := that cap`, with the overflow event's probability absorbed into the `δ` budget the
   capping already spends.  **Whether the cap is a hard bound on the recorded cost, or only a
   deadline whose overshoot is bounded in probability, is the single question to settle first
   — it decides between (1) and (2), and it is a cheap read of
   `TTCSourceSharpOperationalFinal`.**

### (c) Identifying the two laws — the long pole, but no longer blocked

`ttcCharged` *charges a number*; `canonicalFullOperationalLaw V P` *runs the oracle*.  Bridging
them is the `CVCappedRadialLogInterface` work that `Ttc/Model/Theorem.lean`'s predecessor
described as needing "a closed inhabitant of that structure", which did not then exist.

**That blocker is gone**: `TtcSlowRuntimePerPhase.slowPerPhaseImplementation` is exactly such a
closed inhabitant, with no oracle, certificate, implementation or cost-side binder.  What
remains is the identification itself — showing the accuracy-bearing law of `Ttc.ttc` and the
cost-bearing operational law are the same law, or that the former is dominated by the latter.

## 3. What the result would be — and it is a *worse* exponent

Stated plainly, because it is the opposite of what "get `n⁶` into the main theorem" sounds
like:

| | `cVol` | volume term |
|---|---|---|
| today (declared) | `cvVolPriceAt` | `m · n⁴ · volFac` |
| after the accounting step (proved) | CV shape × `slowPerPhaseOV` | `Õ(m · n⁶ · ρ⁸ / ε⁴)` |

The exponent goes **`n⁴ → n⁶`**.  The gain is not a smaller bound; it is that the bound becomes
*true of the algorithm's own oracle* rather than of a price nobody proved it pays.  Anyone
reading the `n⁴` today as a runtime result is reading it wrong, and the accounting step is what
makes the number mean what it appears to mean.

## 4. Order of work

1. **Decide (b)** — read `TTCSourceSharpOperationalFinal` for whether the cap bounds the
   recorded cost pathwise.  Cheap, and it determines the shape of everything downstream.
2. **(a)** — collapse the per-cube sum to `m · shape(ρ_max²)` by `mono_R2`.  Small.
3. **(c)** — the law identification.  This is the long pole and deserves its own session.
4. Re-instantiate `ttc_volume`'s `cVol` and update `Ttc/Model/Theorem.lean`'s docstring.

**Until (c) lands, `Ttc/Model/Theorem.lean` should keep saying what it says now**: the cost
conjunct is at fixed prices this run is not proved to pay, and the proved polynomial bound is
`ttc_volume_runtime_perPhase`, about the operational law.  Those two sentences are the honest
state of the repository and they are already in the file.
