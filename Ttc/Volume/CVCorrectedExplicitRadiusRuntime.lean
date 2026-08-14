/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVCorrectedRuntime
import Ttc.Volume.CVExplicitAdjustableRadius

/-!
# Corrected source accounting with an explicit adjustable radius

The radius budget counts one independently restarted estimator run:
`A = (m+1) * correctedRuntimeSamples m eps`.  Confidence repetitions are not included in
`A`; they appear separately as the `log(1/p)` factor in the source accounting envelope.

Everything in this file is deterministic parameter accounting.  It does not identify the
accounting functional with an execution-cost random variable.
-/

namespace Ttc.CVCorrectedRuntime

open MeasureTheory
open Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open Ttc.CV.Adaptive Ttc.CVAdaptive

noncomputable def correctedPhasePoly (n : Nat) (C : Real) : Real :=
  80 * C ^ 2 * (n : Real) ^ 2 + 3

noncomputable def correctedSamplePoly (n : Nat) (C eps : Real) : Real :=
  100000 * correctedPhasePoly n C / eps ^ 2 + 2

noncomputable def correctedCallPoly (n : Nat) (C eps : Real) : Real :=
  correctedPhasePoly n C * correctedSamplePoly n C eps

noncomputable def correctedExplicitQPoly (n : Nat) (C eps : Real) : Real :=
  20 * correctedCallPoly n C eps + 3

/-- The complete explicit proposal envelope after substituting the polynomial radius. -/
noncomputable def correctedExplicitSourceProposalEnvelope
    (n : Nat) (C eps p : Real) : Real :=
  correctedSourceProposalEnvelope n C eps p (correctedExplicitQPoly n C eps)

private theorem corrected_source_phase_sample_bounds
    {n : Nat} {C eps : Real} (hn : 1 <= n) (hC : 0 < C) (heps : 0 < eps)
    (hsource : (1 / 2 : Real) ^ n <= eps / 4) :
    let s0 := polynomialEndpointSigmaSq n (eps / 4)
    let m := terminalPhaseCount n C s0
    let k := correctedRuntimeSamples m eps
    ((m + 1 : Nat) : Real) < correctedPhasePoly n C ∧
      (k : Real) < correctedSamplePoly n C eps := by
  dsimp only
  let s0 := polynomialEndpointSigmaSq n (eps / 4)
  let m := terminalPhaseCount n C s0
  let k := correctedRuntimeSamples m eps
  have hm := concrete_source_phaseCount_lt hn hC hsource
  have hkRaw := correctedRuntimeSamples_cast_lt (m := m) heps
  have he2 : 0 < eps ^ 2 := sq_pos_of_pos heps
  have hdiv : 100000 * ((m : Real) + 1) / eps ^ 2 <
      100000 * correctedPhasePoly n C / eps ^ 2 := by
    apply div_lt_div_of_pos_right _ he2
    apply mul_lt_mul_of_pos_left _ (by norm_num)
    simpa only [Nat.cast_add, Nat.cast_one, correctedPhasePoly] using hm
  constructor
  · simpa only [correctedPhasePoly] using hm
  · dsimp [k, correctedSamplePoly]
    linarith

/-- The exact one-run coordinate count is bounded by an explicit polynomial. -/
theorem corrected_runwise_calls_lt_poly
    {n : Nat} {C eps : Real} (hn : 1 <= n) (hC : 0 < C) (heps : 0 < eps)
    (hsource : (1 / 2 : Real) ^ n <= eps / 4) :
    let s0 := polynomialEndpointSigmaSq n (eps / 4)
    let m := terminalPhaseCount n C s0
    let k := correctedRuntimeSamples m eps
    runwiseSamplerCalls m k < correctedCallPoly n C eps := by
  dsimp only
  let s0 := polynomialEndpointSigmaSq n (eps / 4)
  let m := terminalPhaseCount n C s0
  let k := correctedRuntimeSamples m eps
  have hb := corrected_source_phase_sample_bounds hn hC heps hsource
  have hphase0 : 0 <= ((m + 1 : Nat) : Real) := by positivity
  have hsample0 : 0 <= (k : Real) := by positivity
  have hsamplePos : 0 < (k : Real) := by
    exact_mod_cast correctedRuntimeSamples_pos m eps
  have hphaseP : 0 < correctedPhasePoly n C := by
    unfold correctedPhasePoly
    positivity
  have hsampleP : 0 < correctedSamplePoly n C eps := by
    unfold correctedSamplePoly
    positivity
  have hphase : (m : Real) + 1 < correctedPhasePoly n C := by
    simpa only [Nat.cast_add, Nat.cast_one] using hb.1
  unfold runwiseSamplerCalls correctedCallPoly
  norm_num
  exact mul_lt_mul hphase hb.2.le hsamplePos hphaseP.le

/-- The explicit fitting radius is itself polynomial in `n,C,1/eps`. -/
theorem corrected_explicit_radius_lt_poly
    {n : Nat} {C eps : Real} (hn : 1 <= n) (hC : 0 < C) (heps : 0 < eps)
    (hsource : (1 / 2 : Real) ^ n <= eps / 4) :
    let s0 := polynomialEndpointSigmaSq n (eps / 4)
    let m := terminalPhaseCount n C s0
    let k := correctedRuntimeSamples m eps
    explicitAdaptiveRadiusQ (runwiseSamplerCalls m k) (1 / 20) <
      correctedExplicitQPoly n C eps := by
  dsimp only
  have hA := corrected_runwise_calls_lt_poly hn hC heps hsource
  rw [explicitAdaptiveRadiusQ_one_div_twenty]
  unfold correctedExplicitQPoly
  linarith

/-- The explicit corrected radius satisfies the adjustable tail certificate. -/
theorem corrected_explicit_radius_tailFits
    {n : Nat} {C eps : Real} (hn : 1 <= n) :
    let s0 := polynomialEndpointSigmaSq n (eps / 4)
    let m := terminalPhaseCount n C s0
    let k := correctedRuntimeSamples m eps
    AdjustableRadiusTailFits n (runwiseSamplerCalls m k) (1 / 20)
      (explicitAdaptiveRadiusQ (runwiseSamplerCalls m k) (1 / 20)) := by
  dsimp only
  apply explicitAdaptiveRadiusQ_tailFits hn
  · unfold runwiseSamplerCalls
    positivity
  · norm_num

/-- Monotonicity of the deterministic source envelope in a nonnegative radius. -/
theorem correctedSourceProposalEnvelope_mono_q
    {n : Nat} {C eps p q Q : Real} (hp : 0 < p) (hp1 : p < 1)
    (hq0 : 0 <= q) (hqQ : q <= Q) :
    correctedSourceProposalEnvelope n C eps p q <=
      correctedSourceProposalEnvelope n C eps p Q := by
  unfold correctedSourceProposalEnvelope
  have hsq : q ^ 2 <= Q ^ 2 := by nlinarith
  have hn0 : 0 <= (n : Real) := by positivity
  have hN0 : 0 <= C ^ 2 * (n : Real) := by positivity
  have hJ0 : 0 <= 16 * C ^ 2 * (n : Real) ^ 2 + 2 := by positivity
  have houter1 : 0 <= 25 / 2 * Real.log (1 / p) + 2 := by
    have hlog : 0 <= Real.log (1 / p) := Real.log_nonneg (by
      rw [le_div_iff₀ hp]
      linarith)
    positivity
  have houter2 : 0 <= 100000 * (80 * C ^ 2 * (n : Real) ^ 2 + 3) / eps ^ 2 + 2 := by
    by_cases he : eps = 0
    · simp [he]
    · positivity
  gcongr

/-- Corrected source proposal accounting with the explicit fitting radius, bounded by a
fully displayed polynomial/rational-logarithmic expression in `n,C,1/eps,log(1/p)`.

The call count used to choose `q` is exactly `(m+1)*k` for one independently restarted run.
The repetition count remains the separate leading `log(1/p)` factor.
-/
theorem corrected_adaptive_source_accounting_explicit_le_envelope
    {n : Nat} {C eps p : Real} (hn : 1 <= n) (hC : 0 < C)
    (heps : 0 < eps) (hp : 0 < p) (hp1 : p < 1)
    (hsource : (1 / 2 : Real) ^ n <= eps / 4) :
    let s0 := polynomialEndpointSigmaSq n (eps / 4)
    let J := adaptiveTerminalChunk (C ^ 2 * n) s0
    let m := terminalPhaseCount n C s0
    let k := correctedRuntimeSamples m eps
    let r := concreteRunwiseReps p
    let A := runwiseSamplerCalls m k
    let q := explicitAdaptiveRadiusQ A (1 / 20)
    adaptiveSourceProposalAccounting n (C ^ 2 * n) s0 J k r q <=
      correctedExplicitSourceProposalEnvelope n C eps p := by
  dsimp only
  let s0 := polynomialEndpointSigmaSq n (eps / 4)
  let J := adaptiveTerminalChunk (C ^ 2 * n) s0
  let m := terminalPhaseCount n C s0
  let k := correctedRuntimeSamples m eps
  let r := concreteRunwiseReps p
  let A := runwiseSamplerCalls m k
  let q := explicitAdaptiveRadiusQ A (1 / 20)
  have haccount := corrected_adaptive_source_accounting_le_envelope
    (q := q) hn hC heps hp hp1 hsource
  have hq := corrected_explicit_radius_lt_poly hn hC heps hsource
  have haccount' : adaptiveSourceProposalAccounting n (C ^ 2 * n) s0 J k r q <=
      correctedSourceProposalEnvelope n C eps p q := by
    simpa only [s0, J, m, k, r] using haccount
  have hq' : q < correctedExplicitQPoly n C eps := by
    simpa only [q, A, s0, m, k] using hq
  have hq0 : 0 <= q := by
    dsimp [q, A]
    rw [explicitAdaptiveRadiusQ_one_div_twenty]
    unfold runwiseSamplerCalls
    positivity
  have hmono := correctedSourceProposalEnvelope_mono_q
    (n := n) (C := C) (eps := eps) (p := p) (q := q)
    (Q := correctedExplicitQPoly n C eps) hp hp1 hq0 hq'.le
  exact haccount'.trans (by
    simpa only [correctedExplicitSourceProposalEnvelope] using hmono)

/-! ## Accounting versus execution

The theorem above bounds `adaptiveSourceProposalAccounting`, a deterministic functional of
the declared schedule.  It does **not** assert that an operational kernel execution has this
cost or expectation.  Such an execution theorem still requires the trajectory/cost
composition interface described by `CVCorrectedRuntime`.
-/

end Ttc.CVCorrectedRuntime

#print axioms Ttc.CVCorrectedRuntime.corrected_runwise_calls_lt_poly
#print axioms Ttc.CVCorrectedRuntime.corrected_explicit_radius_lt_poly
#print axioms Ttc.CVCorrectedRuntime.corrected_explicit_radius_tailFits
#print axioms Ttc.CVCorrectedRuntime.correctedSourceProposalEnvelope_mono_q
#print axioms Ttc.CVCorrectedRuntime.corrected_adaptive_source_accounting_explicit_le_envelope
