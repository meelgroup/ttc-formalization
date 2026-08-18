/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.TtcSlowRuntimePerPhase

/-!
# The main theorem

One theorem: **`Ttc.ttc_volume_runtime`** — TTC's accuracy and query cost, unconditionally,
both conjuncts about the same run.

## Why this module exists rather than `Ttc/Model/Theorem.lean`

`Ttc/Model/Theorem.lean` sits **below** the runtime capstone in the import graph:

```
Ttc.Exec.TtcSlowRuntimeSharp → … → Ttc.Exec.VolPriceCVAlg
    → Ttc.Audit.ClosureCheck / Ttc.Witness.FullTwoCube → Ttc.Model.Theorem
```

so it cannot import `Ttc.Exec.TtcSlowRuntimePerPhase` — the attempt closes a cycle, exactly
as that file's own docstring warns.  The main theorem therefore lives here, above everything
it speaks about.

## What it says

* **Accuracy.**  `P[ output ∈ (1 ± ε)·Vol(F) ] ≥ 1 − δ`, at the user's own `Vol(F)`.
* **Query cost.**  The law's expected recorded query count is at most the per-cube sum of
  `cvComplexityShapeClipped · slowPerPhaseOV`, each cube taken at **its own interior
  circumradius squared**, plus the capped sampling envelope.

Both are about `canonicalFullOperationalLaw V P`, the law that actually executes the volume
subroutine `slowPerPhaseImplementation.algorithm n`, built from the slow canonical
Gaussian-cooling construction at the combined P1 + P2 slack, transport, stream-count and
truncation-radius choice.

## What is unconditional about it

There is **no oracle binder, no certificate binder, no implementation binder and no
cost-side binder**.  `slowPerPhaseImplementation` is a closed term: it appears in the
statement with no arguments.  The only hypotheses are on TTC's own inputs — `0 < ε`,
`ε ≤ 1`, `0 < δ`, `δ ≤ 1`, `21 ≤ n`, `φ.IsPositive`, `0 < volSol …`.

## The complexity this states

Charged-cost, per polytope, with `ρ` the aspect ratio and `L = log(16nρ²)` absorbed into `Õ`:

```
overhead = k · mφ · 10 · Lenv · Tenv · 2e
         = (L/ε²) · (nL) · (ρ²) · (n³ρ⁴)  =  n⁴L²ρ⁶/ε²
```

giving

```
                    Õ( m · n⁶ · ρ⁸ / ε⁴ )
```

It is **not** the paper's `O(m · n⁵ · ρ² · r_max)`, and no constant here pretends to be one:
what is proved is a bound at this explicit shape.  The gap, and every route examined for
closing it, are recorded in `AUDIT.md` §0g and `PLAN-RETRYENV.md`.

**This is a charged-cost statement, not a wall-clock one.**  `Ttc.VolumeAlgorithm` has no
complexity field; all charging happens outside it, in `Ttc.ttcPolyCost`.

## Relation to the legacy statement-layer theorems

`Ttc.ttc_volume_estimate` and `Ttc.ttc_volume_estimate_accounted` (`Ttc/Model/Theorem.lean`)
are about the pseudocode object `Ttc.ttc` rather than about a law that executes the
constructed oracle, and their runtime halves are strictly weaker than the above: the first is
guarded by two binders nothing in this repository proves (`M ≤ (2R)ⁿ` and `2⁻ⁿ ≤ ε'`) and
prices a run that does not execute the oracles being priced; the second charges at prices that
are exponential.  They are kept because they are the only statements about `Ttc.ttc` itself
and because four modules are structurally layered beneath them, **not** because either adds
anything to this theorem.
-/

namespace Ttc

/-- **TTC's accuracy and query cost, unconditionally.**

`TTC` is run on `F = (atoms, φ)` at accuracy `ε` and confidence `δ`, and both conjuncts speak
about the same law.  The statement, written out:

```
∀ {A} {n} (atoms : A → LinAtom n) (phi : BForm A) (eps delta : ℝ),
  0 < eps → eps ≤ 1 → 0 < delta → delta ≤ 1 → 21 ≤ n → phi.IsPositive →
  0 < volSol (atomSet atoms) phi →
    let deltaRun := 4 * delta / 5
    let I := slowPerPhaseImplementation          -- closed term, no arguments
    let V := I.algorithm n
    let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V …
    (1 - delta ≤ (canonicalFullOperationalLaw V P).real
       {r | r.1 ∈ relErr eps (volSol (atomSet atoms) phi)})              -- accuracy
    ∧
    (∫⁻ r, r.2 ∂canonicalFullOperationalLaw V P ≤
       shapedVolumeQueryEnvelopeAt I atoms phi eps deltaRun
         (fun j ↦ circumR (interior (callBody atoms phi eps deltaRun j)) ^ 2)
       + canonicalCappedSampleQueryEnvelope atoms phi eps deltaRun)      -- query cost
```

In `Õ` terms the cost conjunct is `Õ(m · n⁶ · ρ⁸ / ε⁴)`.

Stated as an alias of the capstone rather than re-typed, so that the type here is the
capstone's type **by construction** and cannot drift from what is actually proved. -/
alias ttc_volume_runtime := TtcSlowRuntimePerPhase.ttc_volume_runtime_perPhase

-- The statement, re-derived at elaboration time.
#check @ttc_volume_runtime

#print axioms ttc_volume_runtime

end Ttc
