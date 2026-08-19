/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.TtcSlowRuntimePerPhase

/-!
# The runtime envelope is a number, not `⊤`

`Ttc.ttc_volume`'s cost conjunct reads `∫⁻ r, r.2 ∂ttc … ≤ B`, in `ℝ≥0∞`.  In `ℝ≥0∞` that
inequality is **vacuously true when `B = ⊤`** — every extended nonnegative real is at most
`⊤` — so a cost bound is worth exactly nothing until its right-hand side is known finite.
This file proves it is.

Each of the two summands is a finite sum of manifestly finite terms:

* `Ttc.CVShaped.shapedVolumeQueryEnvelopeAt` is `∑ j, ENNReal.ofReal (…)`, and
  `ENNReal.ofReal` never takes the value `⊤`;
* `Ttc.TTCSourceSharpOperationalFinal.canonicalCappedSampleQueryEnvelope` is
  `∑ i, (rate : ℝ≥0∞) * bound i` with the rate an `NNReal` coercion and the bound
  `8 * (ENNReal.ofReal (…) * hybridStepInspectionBound … + 1)`, whose inspection factor is
  `2⁻¹ * facetCount` or `2⁻¹`.

Nothing here bounds the envelope by anything small — the numbers involved are astronomical
below dimension 1100 (see `Ttc/Exec/SamplerEnvelopeShape.lean`).  Finiteness is the weakest
possible statement in this direction, and it is the one the cost conjunct needs in order to
say anything at all (`CLAUDE.md` §11).
-/

namespace Ttc.EnvelopeFinite

open scoped ENNReal Classical
open MeasureTheory
open Ttc.TTCSourceSharpOperationalFinal Ttc.CVShaped
open Ttc.ConcreteHybridExpectedQuerySampler Ttc.ConcreteHybridCanonicalOwnerPoly

variable {A : Type*} {n : ℕ}

/-- **The per-step facet-inspection factor is finite.**  It is `2⁻¹ * facetCount` above
dimension 1100 and `2⁻¹` below; neither branch is `⊤`. -/
theorem hybridStepInspectionBound_ne_top (n facetCount : ℕ) :
    hybridStepInspectionBound n facetCount ≠ ⊤ := by
  unfold hybridStepInspectionBound
  split
  · exact ENNReal.mul_ne_top (by simp) (by simp)
  · simp

/-- **The per-cube sampler query bound is finite.** -/
theorem canonicalHybridSamplerQueryBound_ne_top
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : ℝ) (i : CubeIndex atoms phi) :
    canonicalHybridSamplerQueryBound atoms phi eps delta i ≠ ⊤ := by
  unfold canonicalHybridSamplerQueryBound
  refine ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.2 ⟨?_, by simp⟩)
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hybridStepInspectionBound_ne_top _ _)

/-- **The sampler envelope is finite** — a finite sum over the cubes of a finite rate times
a finite per-cube bound. -/
theorem canonicalCappedSampleQueryEnvelope_ne_top
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : ℝ) :
    canonicalCappedSampleQueryEnvelope atoms phi eps delta ≠ ⊤ := by
  unfold canonicalCappedSampleQueryEnvelope
  refine (ENNReal.sum_lt_top.2 fun i _ ↦ ?_).ne
  exact lt_top_iff_ne_top.2
    (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (canonicalHybridSamplerQueryBound_ne_top atoms phi eps delta i))

/-- **The volume envelope is finite** — a finite sum of `ENNReal.ofReal`s. -/
theorem shapedVolumeQueryEnvelopeAt_ne_top {Adm : AdmissiblePredicate}
    {shape : ComplexityShape} (I : CVShapedExpectedImplementation Adm shape)
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : ℝ)
    (R2j : Fin (toDNFd (preprocess atoms phi)).length → ℝ) :
    shapedVolumeQueryEnvelopeAt I atoms phi eps delta R2j ≠ ⊤ := by
  unfold shapedVolumeQueryEnvelopeAt
  exact (ENNReal.sum_lt_top.2 fun j _ ↦ ENNReal.ofReal_lt_top).ne

/-- **`Ttc.ttc_volume`'s cost bound is a number.**  The sum of the two envelopes, at the
run's own geometry, is not `⊤` — so the cost conjunct constrains the run rather than
holding vacuously. -/
theorem ttc_volume_bound_ne_top
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : ℝ) :
    shapedVolumeQueryEnvelopeAt Ttc.TtcSlowRuntimePerPhase.slowPerPhaseImplementation
        atoms phi eps delta
        (fun j ↦ (Ttc.TtcCircumRadius.circumR (interior
          (Ttc.TTCCVExpectedImplementation.callBody atoms phi eps delta j))) ^ 2)
      + canonicalCappedSampleQueryEnvelope atoms phi eps delta ≠ ⊤ :=
  ENNReal.add_ne_top.2
    ⟨shapedVolumeQueryEnvelopeAt_ne_top _ atoms phi eps delta _,
      canonicalCappedSampleQueryEnvelope_ne_top atoms phi eps delta⟩

#print axioms ttc_volume_bound_ne_top

end Ttc.EnvelopeFinite
