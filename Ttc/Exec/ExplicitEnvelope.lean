/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.SamplerPolyEnvelope
import Ttc.Exec.TtcSlowRuntimePerPhase

/-!
# The runtime envelope's factors, in closed form

`Ttc.ttc_volume`'s cost conjunct used to name two functions —
`Ttc.CVShaped.shapedVolumeQueryEnvelopeAt` and
`Ttc.TTCSourceSharpOperationalFinal.canonicalCappedSampleQueryEnvelope` — and leave the
reader to chase them through a dozen files.  This file computes every factor of both, so the
capstone can carry the expression itself.

Everything here is an **equality** (or, for the rate threshold, the one inequality
`Ttc.canonicalRateThreshold_le_closed` that was already proved): nothing is estimated, so
nothing is lost by reading the capstone instead of the definitions.

## The one thing that is not a polynomial

`Ttc.canonicalClosedRateThreshold` — the sampler's endpoint **count** — is
`(1 + ε') · qⁿ · Vol(Sol F)` with `q = Ttc.algScale`, and `Ttc.algScale_pow_eq` puts
`qⁿ = max 1 (Thresh/(Vₙ γ̂ⁿ))` in closed form.  So the count is
`Thresh · Vol(Sol F)/(Vₙ γ̂ⁿ)`, a body-to-inscribed-ball volume ratio, exponential in `n`
in the worst case.  Writing it out is the point: the name `canonicalRateThreshold` hid it.
-/

namespace Ttc.ExplicitEnvelope

open MeasureTheory Set
open Ttc.CVShaped Ttc.TtcSlowRuntimePerPhase Ttc.TTCCVExpectedImplementation
open Ttc.CVSlowEffectiveOverhead Ttc.CVSlowActualCostEnvelope
open Ttc.CVSourceTheorem11Arithmetic Ttc.CVSourcePolynomialCutoffCapstone
open Ttc.TTCUnconditionalExplicitRuntime Ttc.TTCSourceSharpOperationalFinal
open Ttc.ConcreteHybridCanonicalOwnerPoly Ttc.SamplerPolyEnvelope
open scoped ENNReal BigOperators Classical

variable {A : Type*} {n : ℕ}

/-! ## The parameter block's four derived numbers -/

/-- **`δ'`** — `Ttc.Params.deltaPrime` at the block the run reads, `δ_blk/(4m)` with
`δ_blk = 4δ/5` and `m` the number of cubes. -/
theorem algBlock_deltaPrime_eq (atoms : A → LinAtom n) (φ : BForm A) (ε d : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < Ttc.volSol (Ttc.atomSet atoms) φ) :
    (Ttc.algBlock atoms φ ε d).deltaPrime
      = 4 * d / 5 / (4 * ((Ttc.toDNFd (Ttc.preprocess atoms φ)).length : ℝ)) := by
  have hm : (Ttc.algBlock atoms φ ε d).m
      = (Ttc.toDNFd (Ttc.preprocess atoms φ)).length :=
    Ttc.ttcBlock_m atoms φ ε d hε0 hε1 hn hφ hpos
  have hd : (Ttc.algBlock atoms φ ε d).δ = 4 * d / 5 :=
    Ttc.ttcBlock_delta atoms φ ε d hε0 hε1 hn hφ hpos
  unfold Ttc.Params.deltaPrime
  rw [hm, hd]

/-- **`Thresh`** — `alg:ttc` line 20 at the block the run reads. -/
theorem algBlock_thresh_eq (atoms : A → LinAtom n) (φ : BForm A) (ε d : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < Ttc.volSol (Ttc.atomSet atoms) φ) :
    (Ttc.algBlock atoms φ ε d).thresh
      = max (24 * Real.log (24 / (4 * d / 5)) / ((1 - ε / 12) * (ε / 12) ^ 2))
          (15 * (Real.log (6 / (4 * d / 5))
            + Real.log ((Ttc.toDNFd (Ttc.preprocess atoms φ)).length : ℝ))) := by
  have hm : (Ttc.algBlock atoms φ ε d).m
      = (Ttc.toDNFd (Ttc.preprocess atoms φ)).length :=
    Ttc.ttcBlock_m atoms φ ε d hε0 hε1 hn hφ hpos
  have hd : (Ttc.algBlock atoms φ ε d).δ = 4 * d / 5 :=
    Ttc.ttcBlock_delta atoms φ ε d hε0 hε1 hn hφ hpos
  have he : (Ttc.algBlock atoms φ ε d).epsPrime = ε / 12 :=
    Ttc.algBlock_epsPrime_eq atoms φ ε d hε0 hε1 hn hφ hpos
  unfold Ttc.Params.thresh
  rw [hm, hd, he]

/-- **`qⁿ`** — the dilation raised to the power line A13 divides by, in closed form.  This is
`Ttc.scaleFactor_pow` at the run's own block and inscribed radius; it is an equality only
because `Ttc.scaleFactor` takes the `n`-th root (2026-08-20). -/
theorem algScale_pow_eq (hn : n ≠ 0) (atoms : A → LinAtom n) (φ : BForm A) (ε d : ℝ) :
    Ttc.algScale atoms φ ε d ^ n
      = max 1 ((Ttc.algBlock atoms φ ε d).thresh /
          (Ttc.unitBallVol n * Ttc.autoGamma atoms (Ttc.preprocess atoms φ) ^ n)) :=
  Ttc.scaleFactor_pow n hn (Ttc.algBlock atoms φ ε d)
    (Ttc.autoGamma atoms (Ttc.preprocess atoms φ))

/-! ## The volume half -/

/-- **The implementation's runtime constant is `800`** — `400 · (rc + 1)` at the `rc = 1`
that `Ttc.TtcShapedRuntime.implementationOfEffectiveCertificatesGen` supplies. -/
theorem slowPerPhase_runtimeConstant :
    slowPerPhaseImplementation.runtimeConstant = (800 : ℝ) := by
  show (400 : ℝ) * (1 + 1) = 800
  norm_num

/-- **The Cousins–Vempala volume envelope, written out.**

`shapeOf slowPerPhaseOV` is `cvConfidenceShape · slowPerPhaseOV`, and every layer beneath —
`slowPerPhaseOVGen`, `sourceLogFactor`, `slowPerPhaseOverhead`,
`slowActualRetainedRealEnvelope` — is definitional unfolding.  The four leaves that remain
named (`perPhaseStreamsP`, `slowPhasesP`, `perPhaseLenv`, `perPhaseTenv`) are the per-phase
schedule's own counts and envelopes; reducing *those* to closed polynomials in the radius
ratio is the open question of `lean/PLAN-SHAPE.md` §5. -/
theorem shapedVolumeQueryEnvelopeAt_eq (atoms : A → LinAtom n) (φ : BForm A) (ε d : ℝ)
    (R2j : Fin (Ttc.toDNFd (Ttc.preprocess atoms φ)).length → ℝ) :
    shapedVolumeQueryEnvelopeAt slowPerPhaseImplementation atoms φ ε d R2j
      = ∑ j : Fin (Ttc.toDNFd (Ttc.preprocess atoms φ)).length,
          ENNReal.ofReal
            (800 * (max 1 (Real.log (1 / (Ttc.algBlock atoms φ ε d).deltaPrime)) *
              (64 * max 1 ((Ttc.algBlock atoms φ ε d).epsPrime) ^ 2 *
                max 1 (Real.log n) ^ 2 *
                max 1 ((perPhaseStreamsP n (R2j j)
                        (min ((Ttc.algBlock atoms φ ε d).epsPrime) 1 / 2) : ℝ) *
                  ((slowPhasesP n (R2j j) + 1 : ℕ) : ℝ) * 10 *
                  perPhaseLenv n (R2j j)
                    (min ((Ttc.algBlock atoms φ ε d).epsPrime) 1 / 2) *
                  perPhaseTenv n (R2j j)
                    (min ((Ttc.algBlock atoms φ ε d).epsPrime) 1 / 2) *
                  (2 * Real.exp 1))))) := by
  unfold shapedVolumeQueryEnvelopeAt
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [slowPerPhase_runtimeConstant]
  rfl

#print axioms algBlock_deltaPrime_eq
#print axioms algBlock_thresh_eq
#print axioms algScale_pow_eq
#print axioms slowPerPhase_runtimeConstant
#print axioms shapedVolumeQueryEnvelopeAt_eq

/-! ## The sampler half -/

/-- **The endpoint count, written out.**  `Ttc.canonicalClosedRateThreshold` at the run's own
`ε'` and `qⁿ`.  This is the factor that is *not* a polynomial: `max 1 (Thresh/(Vₙγ̂ⁿ))` times
`Vol(Sol F)` is `Thresh` times a body-to-inscribed-ball volume ratio. -/
theorem canonicalClosedRateThreshold_eq (hnz : n ≠ 0) (atoms : A → LinAtom n) (φ : BForm A)
    (ε d : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < Ttc.volSol (Ttc.atomSet atoms) φ) :
    canonicalClosedRateThreshold atoms φ ε d
      = ENNReal.ofReal ((1 + ε / 12) *
          (max 1 ((Ttc.algBlock atoms φ ε d).thresh /
              (Ttc.unitBallVol n * Ttc.autoGamma atoms (Ttc.preprocess atoms φ) ^ n)) *
            Ttc.volSol (Ttc.atomSet atoms) φ)) := by
  unfold canonicalClosedRateThreshold
  rw [Ttc.algBlock_epsPrime_eq atoms φ ε d hε0 hε1 hn hφ hpos,
    algScale_pow_eq hnz atoms φ ε d]

/-- **The per-endpoint polynomial, written out.**  `Ttc.SamplerPolyEnvelope.sampPolyT` with
its two suprema inlined; by `rfl`. -/
theorem sampPolyT_eq (atoms : A → LinAtom n) (φ : BForm A) (ε d : ℝ) :
    sampPolyT atoms φ ε d
      = 2 ^ 66 * (n : ℝ) ^ 2 *
          max 0 (⨆ i : CubeIndex atoms φ,
            (canonicalHybridOuterRadius atoms φ ε d i) ^ 2 /
              (canonicalHybridInnerRadius atoms φ ε d i) ^ 2) *
          max 0 (⨆ i : CubeIndex atoms φ,
            Real.log (8 * canonicalHybridWarm atoms φ ε d i /
              (Ttc.ttcSampTol atoms φ ε d i) ^ 2)) + 1 := rfl

/-- **The whole sampler envelope, with every factor explicit.**

`m · (1+ε/12)·max 1 (Thresh/(Vₙγ̂ⁿ))·Vol(Sol F) · 8·((2⁶⁶n²ρ²L + 1)·(r/2) + 1)`.

The first three factors are the endpoint **count** and the last is the cost of **one**
endpoint.  Only the last is a polynomial in `n`; see the module docstring. -/
theorem canonicalCappedSampleQueryEnvelope_le_explicit (hn21 : 21 ≤ n)
    (atoms : A → LinAtom n) (φ : BForm A) (ε d : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < Ttc.volSol (Ttc.atomSet atoms) φ) :
    canonicalCappedSampleQueryEnvelope atoms φ ε d ≤
      ((Ttc.toDNFd (Ttc.preprocess atoms φ)).length : ℝ≥0∞) *
        (ENNReal.ofReal ((1 + ε / 12) *
            (max 1 ((Ttc.algBlock atoms φ ε d).thresh /
                (Ttc.unitBallVol n * Ttc.autoGamma atoms (Ttc.preprocess atoms φ) ^ n)) *
              Ttc.volSol (Ttc.atomSet atoms) φ)) *
          (8 * (ENNReal.ofReal
              (2 ^ 66 * (n : ℝ) ^ 2 *
                  max 0 (⨆ i : CubeIndex atoms φ,
                    (canonicalHybridOuterRadius atoms φ ε d i) ^ 2 /
                      (canonicalHybridInnerRadius atoms φ ε d i) ^ 2) *
                  max 0 (⨆ i : CubeIndex atoms φ,
                    Real.log (8 * canonicalHybridWarm atoms φ ε d i /
                      (Ttc.ttcSampTol atoms φ ε d i) ^ 2)) + 1) *
              ((2 : ℝ≥0∞)⁻¹ * (Nat.card (Ttc.FacetIndex (D atoms φ)) : ℝ≥0∞)) + 1))) := by
  have hnz : n ≠ 0 := by omega
  have h1 := canonicalCappedSampleQueryEnvelope_le_poly hn21 atoms φ ε d hε0 hε1 hn hφ hpos
  refine h1.trans ?_
  have hstep : Ttc.ConcreteHybridExpectedQuerySampler.hybridStepInspectionBound n
      (Nat.card (Ttc.FacetIndex (D atoms φ)))
      = (2 : ℝ≥0∞)⁻¹ * (Nat.card (Ttc.FacetIndex (D atoms φ)) : ℝ≥0∞) := if_pos hn21
  rw [hstep, ← sampPolyT_eq atoms φ ε d]
  gcongr
  refine (canonicalRateThreshold_le_closed atoms φ ε d hε0 hε1 hn hφ hpos).trans ?_
  rw [canonicalClosedRateThreshold_eq hnz atoms φ ε d hε0 hε1 hn hφ hpos]

#print axioms canonicalClosedRateThreshold_eq
#print axioms canonicalCappedSampleQueryEnvelope_le_explicit

/-! ## The same numbers at the capstone's own `δ`-slot

`Ttc.ttc_volume` runs the envelopes at `d := 4δ/5`, so the block's own `δ` is `16δ/25`.
These are the two lemmas above with that substitution carried out. -/

/-- **`1/δ'` at the capstone's slot** — `25m/(4δ)`.  (The `m = 0` case is not excluded: both
sides are then `0`, by `x / 0 = 0`.) -/
theorem one_div_algBlock_deltaPrime_eq_at (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < Ttc.volSol (Ttc.atomSet atoms) φ) :
    1 / (Ttc.algBlock atoms φ ε (4 * δ / 5)).deltaPrime
      = 25 * ((Ttc.toDNFd (Ttc.preprocess atoms φ)).length : ℝ) / (4 * δ) := by
  rw [algBlock_deltaPrime_eq atoms φ ε (4 * δ / 5) hε0 hε1 hn hφ hpos]
  rcases eq_or_ne ((Ttc.toDNFd (Ttc.preprocess atoms φ)).length : ℝ) 0 with h | h
  · rw [h]; norm_num
  · field_simp; ring

/-- **`Thresh` at the capstone's slot** — `alg:ttc` line 20 with `δ_blk = 16δ/25` and
`ε' = ε/12` substituted. -/
theorem algBlock_thresh_eq_at (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < Ttc.volSol (Ttc.atomSet atoms) φ) :
    (Ttc.algBlock atoms φ ε (4 * δ / 5)).thresh
      = max (24 * Real.log (75 / (2 * δ)) / ((1 - ε / 12) * (ε / 12) ^ 2))
          (15 * (Real.log (75 / (8 * δ))
            + Real.log ((Ttc.toDNFd (Ttc.preprocess atoms φ)).length : ℝ))) := by
  rw [algBlock_thresh_eq atoms φ ε (4 * δ / 5) hε0 hε1 hn hφ hpos]
  have h1 : (24 : ℝ) / (4 * (4 * δ / 5) / 5) = 75 / (2 * δ) := by
    field_simp; ring
  have h2 : (6 : ℝ) / (4 * (4 * δ / 5) / 5) = 75 / (8 * δ) := by
    field_simp; ring
  rw [h1, h2]

#print axioms one_div_algBlock_deltaPrime_eq_at
#print axioms algBlock_thresh_eq_at

end Ttc.ExplicitEnvelope
