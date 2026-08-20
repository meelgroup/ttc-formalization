/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.ElemCostIntegral
import Ttc.Exec.ExplicitEnvelope

/-!
# The two run parameters, and the volume half in closed form

`Ttc.ttc`'s cost coordinate is `Ttc.elemFullCost` at two numbers the run supplies: the
facet count `r` of `Ttc.memCost`, and the walk length `Tw` one generated sample costs.
Both are defined here rather than in `Model/Theorem` so that the capstone file holds only
the algorithm and the theorem.

`volBound_le_explicit` is the volume half of the cost bound, written out: the oracle's own
certified envelope, transported to the explicit sum of `Ttc/Exec/ExplicitEnvelope.lean`.
It is stated here for the same reason.
-/

namespace Ttc.TtcSwitchSupport

open MeasureTheory Set
open Ttc.TtcSlowRuntimePerPhase Ttc.SamplerPolyEnvelope
open Ttc.ConcreteHybridCanonicalOwnerPoly
open Ttc.CVShaped Ttc.TTCCVExpectedImplementation Ttc.TtcCircumRadius
open Ttc.CVSlowEffectiveOverhead Ttc.ExplicitEnvelope
open scoped ENNReal BigOperators Classical

variable {A : Type*} {n : ℕ}

/-- **The facet count of the run's polytopes** — the `r` of `Ttc.memCost n r`, and the
only place the facet count enters the cost model. -/
noncomputable def ttcFacets (atoms : A → Ttc.LinAtom n) (φ : Ttc.BForm A) : ℕ :=
  Nat.card (Ttc.FacetIndex (D atoms φ))

/-- **The walk length one generated sample costs** — the `Tw` of `Ttc.sampleCost n r Tw`.

This is a *configuration* of the run, not a bound on it: the sampler is run for this many
hit-and-run steps per endpoint.  `Ttc.SamplerPolyEnvelope.sampPolyT` is
`2 ^ 66 · n² · ρ² · L + 1` at the run's own radius ratio and warm-start logarithm. -/
noncomputable def ttcWalk (atoms : A → Ttc.LinAtom n) (φ : Ttc.BForm A) (ε δ : ℝ) : ℕ :=
  ⌈sampPolyT atoms φ ε (4 * δ / 5)⌉₊

theorem volBound_le_explicit (atoms : A → Ttc.LinAtom n) (φ : Ttc.BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn1 : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < Ttc.volSol (Ttc.atomSet atoms) φ) :
    Ttc.ttcPolyVolumeQueryBound atoms φ ε (4 * δ / 5)
        (slowPerPhaseImplementation.algorithm n)
      ≤ ∑ j : Fin (Ttc.toDNFd (Ttc.preprocess atoms φ)).length,
          ENNReal.ofReal
            (800 *
              (max 1 (Real.log (25 * ((Ttc.toDNFd (Ttc.preprocess atoms φ)).length : ℝ) /
                  (4 * δ))) *
                (64 * max 1 (ε / 12) ^ 2 * max 1 (Real.log n) ^ 2 *
                  max 1
                    ((perPhaseStreamsP n
                        (circumR (interior (callBody atoms φ ε (4 * δ / 5) j)) ^ 2)
                        (min (ε / 12) 1 / 2) : ℝ) *
                      ((slowPhasesP n
                        (circumR (interior (callBody atoms φ ε (4 * δ / 5) j)) ^ 2)
                          + 1 : ℕ) : ℝ) * 10 *
                      perPhaseLenv n
                        (circumR (interior (callBody atoms φ ε (4 * δ / 5) j)) ^ 2)
                        (min (ε / 12) 1 / 2) *
                      perPhaseTenv n
                        (circumR (interior (callBody atoms φ ε (4 * δ / 5) j)) ^ 2)
                        (min (ε / 12) 1 / 2) *
                      (2 * Real.exp 1))))) := by
  have hd0 : (0 : ℝ) < 4 * δ / 5 := by linarith
  have hd1 : 4 * δ / 5 ≤ 1 := by linarith
  refine le_trans (Ttc.CVShaped.ttcPolyVolumeQueryBound_le_shapedVolumeQueryEnvelopeAt
    slowPerPhaseImplementation atoms φ ε (4 * δ / 5)
    (fun j ↦ circumR (interior (callBody atoms φ ε (4 * δ / 5) j)) ^ 2)
    hε0 hε1 hd0 hd1 hn1 hφ hpos
    (fun j ↦ Ttc.TtcCallCircumAdmissible.cvAdmCircum_callBody atoms φ ε (4 * δ / 5)
        hε0 hε1 hn1 hφ hpos j)) (le_of_eq ?_)
  rw [shapedVolumeQueryEnvelopeAt_eq atoms φ ε (4 * δ / 5)
      (fun j ↦ circumR (interior (callBody atoms φ ε (4 * δ / 5) j)) ^ 2),
    one_div_algBlock_deltaPrime_eq_at atoms φ ε δ hε0 hε1 hδ0 hn1 hφ hpos,
    Ttc.algBlock_epsPrime_eq atoms φ ε (4 * δ / 5) hε0 hε1 hn1 hφ hpos]


#print axioms volBound_le_explicit

end Ttc.TtcSwitchSupport
