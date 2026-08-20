/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.TtcSlowRuntimePerPhase

/-!
# Three of `Ttc.ttc_volume`'s four per-phase leaves, written out

`Ttc.ttc_volume`'s volume half is a sum over cubes of an expression naming four
Cousins–Vempala cooling-schedule quantities.  Three of them are *closed*: they unfold to
arithmetic in `n`, `R²` and `ε` with no further schedule vocabulary.  This file does the
unfolding, so a referee can read the bound without chasing definitions.

* `slowPhasesP_eq` — the cooling phase count, `⌈log(16n·max 1 R²)/log(1+1/n)⌉₊ + 1`.
  Polynomial in `n`, **logarithmic** in `R²`.
* `perPhaseStreamsP_eq` — the per-phase stream count, `⌈100000(m+n)/(nε²)⌉₊ + 1`.
* `perPhaseLenv_eq` — the retry cap, `16·⌈log₂(1/shareFloor)⌉₊` with the share floor
  written out.  Note `B = exp(8·(√R²)²)` occurs only *inside* the `log₂`, so the
  `e^{8R²}` never escapes a logarithm: `log₂(B²) = 16R²/log 2`.

The fourth leaf, `Ttc.TtcSlowRuntimePerPhase.perPhaseTenv`, is **not** here.  It is
`slowActualDeadlineExpression` — the per-phase mixing deadline — and reducing it is
`lean/PLAN-SHAPE.md` §5, a question about the Cousins–Vempala analysis rather than a
substitution.
-/

namespace Ttc.PerPhaseLeavesExplicit

open Ttc.TtcSlowRuntimePerPhase Ttc.CVSlowEffectiveOverhead Ttc.CVPerPhaseSamples
open Ttc.CVPerPhaseFrontier Ttc.CVGaussianBlockRetryParameters Ttc.CVCorrected
open Ttc.CVHybridSchedule Ttc.CVSlowFullBodySourceSchedule
open Ttc.CVSlowSourceReferenceCertificate Ttc.CVAdaptive

/-- **The cooling phase count, in closed form.** -/
theorem slowPhasesP_eq (n : ℕ) (hn : 1 ≤ n) (R2 : ℝ) :
    slowPhasesP n R2
      = ⌈max 0 (Real.log (16 * (n : ℝ) * max 1 R2)) / Real.log (1 + 1 / (n : ℝ))⌉₊ + 1 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hN : (0 : ℝ) < max 1 R2 := lt_of_lt_of_le one_pos (le_max_left _ _)
  have harg : (1 : ℝ) / (1 / (16 * (n : ℝ)) / max 1 R2) = 16 * (n : ℝ) * max 1 R2 := by
    rw [one_div_div]
    field_simp
  unfold slowPhasesP slowPhases slowOperationalPhases slowSourcePhases coldPhases
    slowSourceInitialVariance
  rw [harg]

/-- **The per-phase stream count, in closed form.** -/
theorem perPhaseStreamsP_eq (n : ℕ) (R2 eps : ℝ) :
    perPhaseStreamsP n R2 eps
      = ⌈100000 * (((slowPhasesP n R2 : ℕ) : ℝ) + (n : ℝ)) / ((n : ℝ) * eps ^ 2)⌉₊ + 1 := by
  unfold perPhaseStreamsP perPhaseRuntimeSamples
  rfl

/-- **The retry cap, in closed form.**  `B = exp(8·(√R²)²)` sits inside the `log₂`. -/
theorem perPhaseLenv_eq (n : ℕ) (R2 epsP : ℝ) :
    perPhaseLenv n R2 epsP
      = (16 * ⌈Real.logb 2 (1 /
          min (correctedNu (slowPhasesP n R2 + 1) (epsP / 2) /
                (8 * ((((perPhaseStreamsP n R2 epsP : ℕ) : ℝ)) + 1)))
              (2 / ((54 * (n : ℝ) + 144) * Real.exp (8 * Real.sqrt R2 ^ 2) ^ 2)))⌉₊ : ℕ) := by
  unfold perPhaseLenv perPhaseRetriesCapAt perPhaseRetriesCapGen explicitDyadicTailIndex
    perPhaseShareFloorGen blockShare
  norm_num

#print axioms slowPhasesP_eq
#print axioms perPhaseStreamsP_eq
#print axioms perPhaseLenv_eq

end Ttc.PerPhaseLeavesExplicit
