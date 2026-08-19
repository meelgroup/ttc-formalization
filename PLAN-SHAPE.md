# Divergence 1: the Cousins–Vempala shape factor is a `1 ≤ x` weakening

**STATUS: DONE — commit `8a917c2`, 2026-08-19.**  `Õ(m n⁶ρ⁸/ε⁴) → Õ(m n⁴ρ⁶/ε²)`.
§2 and §7 below record how it was actually resolved.

**What this proposes.** Delete a factor of `n²ρ²/ε²·log⁶` from the proved runtime bound by
changing one definition.  No new mathematics.  The factor is not earned by any argument: it
is introduced by `le_mul_of_one_le_right` in a single lemma, and every structural use of it
downstream is a weakening that becomes trivial once it is gone.

This is **independent of `PLAN-WARMSTART`** (different layers: `Ttc/Exec` cost envelopes here,
`Arlib` + `radiusQDelta` consumers there) and should land first — it is cheaper, worth more,
and it changes what the KLS97 item is worth.

## 1.  The finding

`Ttc/Exec/CVSourcePolynomialCutoffCapstone.lean:50`:

```lean
noncomputable def sourceOneRunQueryEnvelope (runtimeConstant : Real) (n : Nat) (R eps : Real) : Real :=
  runtimeConstant * (max (R ^ 2 * (n : Real) ^ 2) ((n : Real) ^ 3) / eps ^ 2 *
    sourceLogFactor n ^ 2 * sourceLogFactor (1 / eps) ^ 2 * sourceLogFactor ((n : Real) / eps) ^ 2)
```

`Ttc/Exec/CVSlowEffectiveOverhead.lean:346`:

```lean
theorem le_sourceOneRunQueryEnvelope_of_le … (hrc : 0 ≤ rc) : rc ≤ sourceOneRunQueryEnvelope rc n R eps := by
  unfold sourceOneRunQueryEnvelope
  exact le_mul_of_one_le_right hrc (one_le_sourceOneRunCore n hn heps heps1)
```

And the discharge, at `Ttc/Exec/TtcSlowRuntimePerPhase.lean:355` (**the operative route**):

```lean
have hover : (k:ℝ) * (m:ℝ) * (10 * L * T * (2 * exp 1)) ≤ slowPerPhaseOverhead n R2 epsP p Lenv Tenv
have hcore : slowPerPhaseOverhead … ≤ sourceOneRunQueryEnvelope (slowPerPhaseOverhead …) n R requested
exact ENNReal.ofReal_le_ofReal (hover.trans hcore)
```

**What is actually proved is `expected queries ≤ OV`.**  The Cousins–Vempala shape is then
appended by `hcore`, whose whole content is `1 ≤ cvBaseClipped`.  It is a monotonicity step,
not an estimate.

The factor survives to the headline because
`Ttc/Exec/TtcShapedRuntimeFromCertificates.lean:63` carries it into the shape:

```lean
noncomputable def shapeOf (OV) : ComplexityShape :=
  fun n R2 eps p ↦ cvComplexityShapeClipped n R2 eps p * OV n R2 eps p
```

## 2.  Go / no-go — the only thing that can kill this

The in-place edit is sound **iff every** site discharging a `sourceOneRunQueryBudget`
obligation has the `cost ≤ OV`, then `OV ≤ OV·B` shape — i.e. **no site uses the shape's
`n³/ε²·log⁶` headroom to swallow a real cost**.  If one does, that route's `OV` must grow and
the ledger below changes.  **Verify all of these before editing anything.**

| site | resolved |
|---|---|
| `TtcSlowRuntimePerPhase:355` (`slowPerPhase_hscalar`) — **the operative capstone** | ✅ read before editing; the two-step shape |
| `CVSlowEffectiveOverhead:529` (`slowCanonical_hscalar`) | ✅ read before editing; the two-step shape |
| all remaining sites | ✅ resolved **by the compiler**, see below |

**How the matrix was actually completed: build-as-oracle.**  Reading ten more files would have
been slower and less reliable than making the edit and letting Lean decide — a site that needs
the shape's headroom cannot typecheck without it.  Only **three** files failed the first build
(`CVSourceTheorem11Arithmetic`, `CVColdHotReferenceCost`, `TTCOperationalPaperBridge`), and
five more surfaced as the fixes propagated.  Every one of them was a weakening that collapsed —
`_eps_absorb` to `rc ≤ 64·rc`, `clip_eps` to `rc ≤ rc·(max 1 eps)²·log²n`, the three
`CVSourceReferenceWeaken` monotonicity lemmas to `le_rfl`, `_le_of_sq_le` to
`one_le_cvBaseClipped` — **except one.**

### The one red entry, and why it did not stop the edit

`doubledEstimator_coldHotPhaseSum_le_sourceBudget` (`CVColdHotReferenceCost`) and its
`innerHundred` twin genuinely spend the shape's `1/ε²`:

```
2·k·∑means ≤ 2·(weightedSampleNumerator/ε²)·∑means = (2·num·∑means)/ε² ≤ core/ε² = envelope
```

with `k = estimatorSamples ≈ num/ε²` — the estimator's own sample count, paid for by a factor
nobody was charging for.  That is a real cost, not bookkeeping.

It did not stop the edit because **the cold/hot route is dead**:
`exists_sourceReferenceTVOneRunCertificate_of_coldHotSeedPhases` has no consumers at all —
only a `#print axioms`.  So the repair is to make that route pay its own sample count: the six
`hcoldHotShape` binders across `CVColdHotReferenceCost` and `CVGaussianHybridWeightedCertificate`
now carry the `/ eps ^ 2` themselves.  **Had this route been on the operative path, the edit
would have stopped here and `slowPerPhaseOV` would have had to grow instead.**


## 3.  What the structural uses become

Every use that touches the internals is a weakening in the direction that survives.

* `le_sourceOneRunQueryEnvelope_of_le` — statement survives as `rc ≤ rc`; **its proof breaks**
  (`le_mul_of_one_le_right` has no `mul` to apply to).  Becomes `le_refl`.
* `sourceOneRunQueryEnvelope_le_of_sq_le` (monotone in the radius) — becomes `rc ≤ rc·B(R2)`,
  which is `one_le_cvBaseClipped`.  Statement unchanged.
* `sourceOneRunQueryEnvelope_eps_absorb` / `sourceOneRunQueryBudget_absorb`
  (`CVBudgetEpsAbsorb`) — currently a real computation (`A/e² ≤ 4A/eps²` plus log growth);
  becomes `rc ≤ 64·rc`.  Statement unchanged.  ⚠ This is where the `64` in `slowPerPhaseOV`
  comes from; check that the `e` vs `eps` obligation does not migrate into `OV` — the
  certificate's `eps` slot is `a.2.1`, the same `eps` `effective` is evaluated at, so it
  should not, but confirm.
* `sourceOneRunQueryEnvelope_clip_eps` (`TtcSlowRuntimeFinal:~120`) — currently a genuine
  two-branch computation; becomes `rc ≤ rc·(max 1 eps)²·sourceLogFactor n ²`.  Statement
  unchanged.  **Note the consequence**: this lemma is the origin of the
  `64·(max 1 eps)²·sourceLogFactor n ²` prefix in `slowPerPhaseOVGen`.  With the shape gone
  that inflation is no longer needed, so a follow-up can drop a further `log²n`.  Not
  required for the main saving; record it, do not bundle it.
* `sourceAmplifiedQueryEnvelope` (`CVSourcePolynomialCutoffCapstone:193`) is
  `(8·log(1/p) + 2)·(20·(oneRun + 1))`.  The `log(1/p)` **is earned** — it is confidence
  amplification by repeated runs — and must be kept.

## 4.  The edit

1. **Rename and redefine.**  ⚠ **Decision taken 2026-08-19: the name stays, and here is why.**
   What `CLAUDE.md` §13 forbids is a name that asserts something false.  The *docstring* did —
   it read "the paper's one-run membership-query shape" — and it was rewritten.  The *name* did
   not: `sourceOneRunQueryEnvelope` says "an envelope on one run's queries", which is exactly
   what `rc` now is, and was also true before.  A ~91-occurrence sed rename would have produced
   a large diff for no gain in honesty.  The vestigial `(n, R, eps)` slots are retained so that
   no consumer signature changes, and the docstring says so.
2. **New arithmetic lemma** replacing `sourceAmplifiedQueryEnvelope_le_cvComplexityShapeClipped`:
   `sourceAmplifiedQueryEnvelope rc n R eps p ≤ (200·(rc+1)) · max 1 (Real.log (1/p))`.
   The proof is that lemma's existing `calc` with `B` deleted.  Keep the old lemma too — it is
   still true and is the paper-contract comparison.
3. **`cvShapedExpectedImplementationOfEffectiveFamily`** (`CVEffectiveSourceReferenceFamily:247`)
   at shape `fun n R2 eps p ↦ max 1 (Real.log (1/p)) * OV n R2 eps p`, constant `400·(rc+1)`
   unchanged.
4. **`shapeOf OV := fun n R2 eps p ↦ max 1 (Real.log (1/p)) * OV n R2 eps p`.**  All four
   capstones (`slowUncOV`, `slowSharpOV`, `slowFinalOV`, `slowPerPhaseOV`) inherit
   automatically — they are each `shapeOf X`.

### Not deleted

`Ttc.cvComplexityShapeClipped`, `Ttc.CVTheorem11Implementation` and
`CVShapedExpectedImplementation.ofCapped` stay.  They are the **paper-contract layer** — what
`CVSlowCanonicalRuntimeComparison` compares against — and the point of this change is that we
stop pretending to *meet* that contract with an overhead when what we have is a bound.

### Two objects not yet resolved — decide scope explicitly

* `sourceOneRunQueryCore` (`CVColdHotReferenceCost:294`) — a **separate** definition, the same
  expression without the `/eps²`.  Local to that file.  In scope only if that file is on the
  operative path.
* `sourceRadialLogOneRunQueryEnvelope` / `…Budget` (`CVRadialLogEnvelope:41,45`) — a parallel
  budget family behind `ofCapped`/`CVCappedRadialLogExpectedImplementation`.  Determine whether
  it carries the same weakening, and whether it is on the operative path at all.

## 5.  Ledger — and a units audit that must accompany it

Per cube, `800 · cvComplexityShapeClipped n ρ²ⱼ ε' δ' · slowPerPhaseOV n ρ²ⱼ ε' δ'`
becomes `800 · max 1 (log(1/δ')) · slowPerPhaseOV n ρ²ⱼ ε' δ'`:

```
Õ(m · n⁶ · ρ⁸ / ε⁴)   ⟶   Õ(m · n⁴ · ρ⁶ / ε²)
```

**That is below the paper's `n⁵` in the `n` exponent, and that is a reason for suspicion, not
celebration.**  `RUNTIME-ENDGAME.md` has miscredited a factor twice already (§"Second
correction, 2026-08-18").  Before any such number is written anywhere:

1. **Redo the comparison in matched units.**  Our `cost` counts what
   `SourceReferenceTVOneRunCertificate.reference_expected_queries` counts — expected
   *membership queries*.  The paper's `O(m·n⁵·ρ²·r_max)` carries `r_max` as an explicit
   operations factor, and `AUDIT.md`'s own decomposition of the paper
   (`m·r_max·(n³ρ²∨n⁴)/ε² + n⁵ρ²·Thresh`) is the comparable form.  A query count and an
   operation count are not the same exponent.
2. **Do not reuse the "one factor `n` short of the paper" framing.**  That narrative was
   computed with the shape artifact in it and goes stale with this fix.

### A correction this forces

`AUDIT.md`'s section *"The `n⁴` vs `n⁶` exponent gap is SETTLED: it is the walk step size, and
it is forced"* becomes **wrong as stated**.  The gap was the step size **times this
weakening**.  When this lands, that section must be superseded in the same explicit way
`PLAN-WARMSTART` marks its own superseded drafts — not quietly edited.

`PLAN-WARMSTART`'s payoff line must also be recomputed afterwards: the KLS97 item is worth a
factor `n` off whatever the ledger reads *after* this change.

## 6.  Verified facts this plan may assert

* The cutoff is relative — `sourceReferenceCutoff = 40·(budget + 1)`
  (`CVSourceReferenceTVCapstone:26`), and `sourceReferenceCutoff_ratio` is `budget/cutoff ≤ 1/40`.
  Shrinking the budget does not break the timeout/Markov argument.
* The sampler-side summand carries **no** shape:
  `canonicalCappedSampleQueryEnvelope = ∑ᵢ polyGoodRateCapᵢ · canonicalHybridSamplerQueryBoundᵢ`
  (`TTCSourceSharpOperationalFinal:462`).  This change does not touch it.
* The capstone's statement *text* is stable: `shapedVolumeQueryEnvelopeAt` is abstract in `I`
  and its shape, so only `I`'s type and the bound's value change.

## 7.  Checklist

- [x] Complete the §2 matrix — by build-as-oracle; one red entry found and handled (§2).
- [x] Decide the rename (§4.1) — **name stays**, reasoning recorded there.
- [x] Decide scope for `sourceOneRunQueryCore` and the radial-log family — `sourceOneRunQueryCore`
      kept unchanged (it is a standalone shaped quantity `CVHotRefreshHonestRuntime` compares
      against); the radial-log envelope was made lean in step, so
      `sourceOneRunQueryEnvelope_effective_eq_radialLog` still holds.
- [x] Make the edit; `lake build Ttc` green at **9467 jobs**; `#print axioms` clean on all four
      capstones; no `sorryAx` anywhere in the build log.
- [x] Re-elaborate `ttc_volume_runtime_perPhase`'s type independently — binders unchanged
      (`atoms phi eps delta` + the same seven conditions), `slowPerPhaseImplementation` still a
      closed term, and `#print shapeOf` confirms `cvConfidenceShape * OV`.
- [x] Re-run the four closure audits — all pass, counts unchanged (109 / 157 / 208 / 212).
- [x] Update `RUNTIME-ENDGAME.md`'s ledger table and supersede `AUDIT.md` §"SETTLED".
- [x] Recompute `PLAN-WARMSTART`'s payoff line.
- [ ] **The units audit of §5 — still not done.**  Until it is, no comparison between this
      bound and the paper's `O(m·n⁵·ρ²·r_max)` may be stated anywhere.
- [ ] The free `log²n`: `clip_eps` is the origin of the `64·(max 1 eps)²·sourceLogFactor n ²`
      prefix in the four `OV`s, and with the shape gone that inflation buys nothing.  Recorded
      in its docstring; deliberately not bundled.
