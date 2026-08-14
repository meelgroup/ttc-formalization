/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVCorrectedRuntime
import Ttc.Volume.CVLogarithmicAdjustableRadius

/-!
# Corrected CV accounting with a logarithmic truncation radius

This instantiates the corrected source-regime accounting with the radius

`q² = 4 + 4 log (20 A) / n`,

where `A = (m+1)k` is the number of sampler calls in one estimator run.  Unlike the earlier
linear selector `q = 20A+3`, this preserves the source's polylogarithmic overhead.  The
confidence repetition count is deliberately absent from `A` and remains the separate
leading `log (1/p)` factor.

As in `CVCorrectedRuntime`, the result is deterministic proposal accounting; attaching it
to a membership-query random variable still requires the operational sequential execution.
-/

namespace Ttc.CVCorrectedRuntime

open Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open Ttc.CV.Adaptive Ttc.CVAdaptive

/-- The logarithmic truncation radius for one corrected estimator run. -/
noncomputable def correctedLogarithmicQ (n m k : Nat) : Real :=
  logarithmicAdaptiveRadiusQ n (runwiseSamplerCalls m k) (1 / 20)

theorem correctedLogarithmicQ_sq {n m k : Nat} (hn : 1 <= n) (hk : 0 < k) :
    correctedLogarithmicQ n m k ^ 2 =
      4 + 4 * Real.log (20 * runwiseSamplerCalls m k) / (n : Real) := by
  have hA : 0 < runwiseSamplerCalls m k := by
    unfold runwiseSamplerCalls
    positivity
  have hbA : (1 / 20 : Real) <= runwiseSamplerCalls m k := by
    have hAone : (1 : Real) <= runwiseSamplerCalls m k := by
      unfold runwiseSamplerCalls
      norm_num
      exact_mod_cast Nat.mul_pos (Nat.succ_pos m) hk
    linarith
  unfold correctedLogarithmicQ
  rw [logarithmicAdaptiveRadiusQ_sq hn (by norm_num) hbA]
  congr 3
  field_simp

/-- The logarithmic radius satisfies the full accumulated one-run tail budget. -/
theorem correctedLogarithmicQ_tailFits {n m k : Nat} (hn : 1 <= n) (hk : 0 < k) :
    AdjustableRadiusTailFits n (runwiseSamplerCalls m k) (1 / 20)
      (correctedLogarithmicQ n m k) := by
  have hA : 0 < runwiseSamplerCalls m k := by
    unfold runwiseSamplerCalls
    positivity
  have hbA : (1 / 20 : Real) <= runwiseSamplerCalls m k := by
    have hAone : (1 : Real) <= runwiseSamplerCalls m k := by
      unfold runwiseSamplerCalls
      norm_num
      exact_mod_cast Nat.mul_pos (Nat.succ_pos m) hk
    linarith
  exact logarithmicAdaptiveRadiusQ_tailFits hn hA (by norm_num) hbA

/-- The corrected source accounting instantiated with the logarithmic fitting radius.
Together with `correctedLogarithmicQ_sq`, the only radius overhead is
`4 + 4 log (20 (m+1)k) / n`. -/
theorem corrected_adaptive_source_accounting_logarithmic_le_envelope
    {n : Nat} {C eps p : Real} (hn : 1 <= n) (hC : 0 < C)
    (heps : 0 < eps) (hp : 0 < p) (hp1 : p < 1)
    (hsource : (1 / 2 : Real) ^ n <= eps / 4) :
    let s0 := polynomialEndpointSigmaSq n (eps / 4)
    let J := adaptiveTerminalChunk (C ^ 2 * n) s0
    let m := terminalPhaseCount n C s0
    let k := correctedRuntimeSamples m eps
    let r := concreteRunwiseReps p
    let q := correctedLogarithmicQ n m k
    AdjustableRadiusTailFits n (runwiseSamplerCalls m k) (1 / 20) q ∧
      adaptiveSourceProposalAccounting n (C ^ 2 * n) s0 J k r q <=
        correctedSourceProposalEnvelope n C eps p q := by
  dsimp only
  let s0 := polynomialEndpointSigmaSq n (eps / 4)
  let J := adaptiveTerminalChunk (C ^ 2 * n) s0
  let m := terminalPhaseCount n C s0
  let k := correctedRuntimeSamples m eps
  let r := concreteRunwiseReps p
  let q := correctedLogarithmicQ n m k
  have hk : 0 < k := correctedRuntimeSamples_pos m eps
  constructor
  · simpa only [q] using correctedLogarithmicQ_tailFits hn hk
  · have haccount := corrected_adaptive_source_accounting_le_envelope
      (q := q) hn hC heps hp hp1 hsource
    simpa only [s0, J, m, k, r] using haccount

#print axioms correctedLogarithmicQ_sq
#print axioms correctedLogarithmicQ_tailFits
#print axioms corrected_adaptive_source_accounting_logarithmic_le_envelope

end Ttc.CVCorrectedRuntime
