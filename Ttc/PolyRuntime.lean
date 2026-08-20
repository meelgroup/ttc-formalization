import Ttc.Model.Theorem
import Ttc.Exec.SamplerPolyEnvelope

namespace Ttc.PolyRuntime

open MeasureTheory
open Ttc.TTCSourceSharpOperationalFinal Ttc.ConcreteHybridCanonicalOwnerPoly
open Ttc.SamplerPolyEnvelope Ttc.TTCUnconditionalExplicitRuntime
open scoped ENNReal BigOperators Classical

variable {A : Type*} {n : ℕ}

set_option maxHeartbeats 2000000 in
/-- **`Ttc.ttc`'s expected query cost, with the sampler half in closed polynomial form.**

`Ttc.ttc_volume` bounds the cost by `shapedVolumeQueryEnvelopeAt … + canonicalCappedSampleQueryEnvelope …`.
The second summand is replaced here by an explicit polynomial in the run's own inputs:

```
m · threshold · 8·( (2⁶⁶·n²·ρ²·L + 1) · (r/2) + 1 )
```

with `ρ² = Ttc.SamplerPolyEnvelope.sampRhoSq` and `L = Ttc.SamplerPolyEnvelope.sampLog` the
run's own radius ratio and warm-start logarithm, each a `Finset.sup` over the cubes — the move
the paper makes when it replaces every `R_i/γ_i` by `ρ`, taken at the run's own geometry
rather than at a supplied binder.  **The binder list is exactly `Ttc.ttc_volume`'s.**

⚠ **`m · threshold · …` is not a polynomial bound.**  `threshold` is
`Ttc.canonicalRateThreshold`, the sampler's endpoint **count**, and it is the *dilated* cube
volume `Ttc.algScale ^ n · Vol`.  What this theorem replaces by a polynomial is the
per-endpoint factor, which carried `4 ^ n · (radius ratio) ^ (4 n)` below dimension 1100 until
2026-08-19.  The `n`-th root added to `Ttc.scaleFactor` on 2026-08-20 collapses the count from
`(Thresh/Vₙγ̂ⁿ) ^ n · Vol` to `Thresh · Vol/(Vₙγ̂ⁿ)`; the surviving body-to-inscribed-ball
ratio is exponential in `n` and is the next thing in the way.

⚠ **The volume half is deliberately left as the shaped envelope.**  Collapsing
`Ttc.CVShaped.shapedVolumeQueryEnvelopeAt` to a polynomial is the unsettled `ρ`-exponent
question of `lean/PLAN-SHAPE.md` §5, and a statement is only as honest as its softest half. -/
theorem ttc_cost_le_volume_add_poly
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hn : 21 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    (∫⁻ r, r.2 ∂Ttc.ttc atoms φ ε δ) ≤
      Ttc.CVShaped.shapedVolumeQueryEnvelopeAt
          Ttc.TtcSlowRuntimePerPhase.slowPerPhaseImplementation atoms φ ε (4 * δ / 5)
          (fun j ↦ (Ttc.TtcCircumRadius.circumR (interior
            (Ttc.TTCCVExpectedImplementation.callBody atoms φ ε (4 * δ / 5) j))) ^ 2)
        + ((toDNFd (preprocess atoms φ)).length : ℝ≥0∞) *
            (canonicalRateThreshold atoms φ ε (4 * δ / 5) *
              (8 * (ENNReal.ofReal (sampPolyT atoms φ ε (4 * δ / 5)) *
                Ttc.ConcreteHybridExpectedQuerySampler.hybridStepInspectionBound n
                  (Nat.card (Ttc.FacetIndex (D atoms φ))) + 1))) := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have h1 := (Ttc.ttc_volume atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos).2
  have h2 := canonicalCappedSampleQueryEnvelope_le_poly hn atoms φ ε (4 * δ / 5)
    hε0 hε1 hn1 hφ hpos
  refine h1.trans ?_
  gcongr

#print axioms ttc_cost_le_volume_add_poly

end Ttc.PolyRuntime
