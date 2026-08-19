/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Ttc.Exec.TTCUnconditionalExplicitRuntime

/-!
# The shape of the sampler query envelope, machine-checked

`Ttc.TTCUnconditionalExplicitRuntime.canonicalCappedSampleQueryEnvelope_le_explicitCaps`
already reduces the sampler sum, with no premises, to

    (cube count) · canonicalRateThreshold · canonicalEndpointInspectionCap.

What was missing — and what `lean/PLAN-SHAPE.md` §5.7 records was got *wrong* by hand — is the
size of the endpoint cap.  This file supplies the part of that which is pure arithmetic.

## The point of the file

`Ttc.hybridTransitionBound` is **not** its high-dimensional summand.  Its definition
(`Ttc/Sampler/ConstructHybridUncond.lean:199`) is

    max 0 (2^66 · n^2 · Rout^2 / rin^2 · log (8·Mw/eps^2))  +  1  +  lowDimBallWalkEnvelope …

and the third summand is added **unconditionally**: it is a uniform envelope covering both the
hit-and-run branch (`1100 ≤ n`) and the ball-walk branch, not a term that switches off in high
dimension.  `Ttc.lowDimBallWalkEnvelope` sums `Ttc.mixStepsBound k` over `k < 1100`, and
`mixStepsBound` carries `4^k` and `((γ+Dm)/γ)^(4k)`.  So the envelope contains a term that is
**constant in `n` but polynomial in the radius ratio of degree ≈ 4400, with a `4^1099`
constant**.

`Ttc.SamplerEnvelopeShape.lowDimBallWalkEnvelope_le` below makes that visible as a checked
inequality rather than a reading of a definition.  It is deliberately not asymptotic notation:
the constants are the point.

## What is **not** here

No bound of the form `canonicalHybridSamplerQueryBound ≤ rMax · n^5 · rho^2`.  That is the
premise `hprice` of
`Ttc.TTCOperationalPaperBridge.canonicalCappedSampleQueryEnvelope_le_paperSampling_of_cube`,
and **this development cannot discharge it at large radius ratio** — the low-dimensional term
above exceeds it.  See `AUDIT.md` and `PLAN-SHAPE.md` §5.7.
-/

namespace Ttc.SamplerEnvelopeShape

open scoped BigOperators

/-- **`Ttc.mixStepsBound` is monotone in the dimension slot.**

Every `k`-dependent factor — `4^k`, `k^2`, `A^(2k)`, `A^(4k)` at `A = (γ+Dm)/γ` — is monotone
once `1 ≤ A`, which holds because `Dm ≥ 0 < γ`.  The leading logarithmic factor is
nonnegative because `1 ≤ Mw` and `eps ≤ 1`. -/
theorem mixStepsBound_mono_dim
    {k l : Nat} (hkl : k ≤ l) {γ Dm dl Mw eps : Real}
    (hγ : 0 < γ) (hDm : 0 ≤ Dm) (hMw : 1 ≤ Mw)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    Ttc.mixStepsBound k γ Dm dl Mw eps ≤ Ttc.mixStepsBound l γ Dm dl Mw eps := by
  have hA : (1 : Real) ≤ (γ + Dm) / γ := by
    rw [le_div_iff₀ hγ]
    linarith
  have hlogM : (0 : Real) ≤ Real.log Mw := Real.log_nonneg hMw
  have hlogE : (0 : Real) ≤ Real.log (1 / eps) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ heps]
    linarith
  have hcoef : (0 : Real) ≤ Real.log Mw + 2 * Real.log (1 / eps) := by linarith
  have hkl2 : 2 * k ≤ 2 * l := by omega
  have hkl4 : 4 * k ≤ 4 * l := by omega
  have hksq : ((k : Real)) ^ 2 ≤ ((l : Real)) ^ 2 := by
    have : (k : Real) ≤ (l : Real) := by exact_mod_cast hkl
    nlinarith [Nat.cast_nonneg (α := Real) k]
  have hfour : (4 : Real) ^ k ≤ (4 : Real) ^ l :=
    pow_le_pow_right₀ (by norm_num) hkl
  have hA2 : ((γ + Dm) / γ) ^ (2 * k) ≤ ((γ + Dm) / γ) ^ (2 * l) :=
    pow_le_pow_right₀ hA hkl2
  have hA4 : ((γ + Dm) / γ) ^ (4 * k) ≤ ((γ + Dm) / γ) ^ (4 * l) :=
    pow_le_pow_right₀ hA hkl4
  have hD : (0 : Real) ≤ Dm ^ 2 / dl ^ 2 := by positivity
  unfold Ttc.mixStepsBound
  have hinner :
      1024 * ((γ + Dm) / γ) ^ (2 * k)
          + 16384 * 4 ^ k * (k : Real) ^ 2 * Dm ^ 2 / dl ^ 2 * ((γ + Dm) / γ) ^ (4 * k)
        ≤ 1024 * ((γ + Dm) / γ) ^ (2 * l)
          + 16384 * 4 ^ l * (l : Real) ^ 2 * Dm ^ 2 / dl ^ 2 * ((γ + Dm) / γ) ^ (4 * l) := by
    have h4pos : (0 : Real) ≤ (4 : Real) ^ k := by positivity
    have hApos2 : (0 : Real) ≤ ((γ + Dm) / γ) ^ (2 * k) := by positivity
    have hApos4 : (0 : Real) ≤ ((γ + Dm) / γ) ^ (4 * k) := by positivity
    gcongr
  nlinarith [hinner, hcoef]

/-- **The low-dimensional envelope, capped at its largest summand.**

`Ttc.lowDimBallWalkEnvelope` is a sum of `1100` terms, each monotone in its dimension index, so
it is at most `1100` copies of the term at `k = 1099`.

⚠ **Read the right-hand side.**  `Ttc.mixStepsBound 1099 rin (2·Rout) δ Mw eps` carries
`16384 · 4^1099 · 1099^2 · (2·Rout)^2/δ^2 · ((rin + 2·Rout)/rin)^4396`.  With
`(rin + 2·Rout)/rin` the radius ratio, this is a term of degree ≈ 4400 in that ratio and a
constant of size `4^1099`.  It is **constant in the dimension `n`**, which is why the ambient
`n`-exponent is unaffected — and why it is invisible to any accounting that looks only at `n`. -/
theorem lowDimBallWalkEnvelope_le
    {rin Rout δ Mw eps : Real}
    (hrin : 0 < rin) (hRout : 0 ≤ Rout) (hMw : 1 ≤ Mw)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    Ttc.lowDimBallWalkEnvelope rin Rout δ Mw eps ≤
      1100 * max 0 (Ttc.mixStepsBound 1099 rin (2 * Rout) δ Mw eps) := by
  have hDm : (0 : Real) ≤ 2 * Rout := by linarith
  unfold Ttc.lowDimBallWalkEnvelope
  calc
    ∑ k ∈ Finset.range 1100, max 0 (Ttc.mixStepsBound k rin (2 * Rout) δ Mw eps)
        ≤ ∑ _k ∈ Finset.range 1100,
            max 0 (Ttc.mixStepsBound 1099 rin (2 * Rout) δ Mw eps) := by
          refine Finset.sum_le_sum ?_
          intro k hk
          have hk' : k ≤ 1099 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          exact max_le_max le_rfl
            (mixStepsBound_mono_dim hk' hrin hDm hMw heps heps1)
    _ = 1100 * max 0 (Ttc.mixStepsBound 1099 rin (2 * Rout) δ Mw eps) := by
          rw [Finset.sum_const, Finset.card_range]
          norm_num

/-- **The transition bound, decomposed.** -/
theorem hybridTransitionBound_le
    {n : Nat} {rin Rout δ Mw eps : Real}
    (hrin : 0 < rin) (hRout : 0 ≤ Rout) (hMw : 1 ≤ Mw)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    Ttc.hybridTransitionBound n rin Rout δ Mw eps ≤
      max 0 (2 ^ 66 * (n : Real) ^ 2 * Rout ^ 2 / rin ^ 2 *
          Real.log (8 * Mw / eps ^ 2)) + 1
        + 1100 * max 0 (Ttc.mixStepsBound 1099 rin (2 * Rout) δ Mw eps) := by
  have h := lowDimBallWalkEnvelope_le (rin := rin) (Rout := Rout) (δ := δ)
    (Mw := Mw) (eps := eps) hrin hRout hMw heps heps1
  unfold Ttc.hybridTransitionBound
  linarith

/-- **The low-dimensional term is really inside the transition bound — a LOWER bound.**

This is the substantive half.  `hybridTransitionBound_le` is an upper bound, and an upper
bound can always be loose: on its own it would leave open whether the `4^1099 · ρ^4396` term is
an artefact of careless bounding.  It is not.  `Ttc.lowDimBallWalkEnvelope` is a sum of
nonnegative terms, so it dominates its own `k = 1099` summand, and the other two summands of
`Ttc.hybridTransitionBound` are nonnegative.

**No hypotheses at all** — in particular this holds at `1100 ≤ n`, where the walk being priced
is hit-and-run and the low-dimensional ball-walk term is pure overhead.  No sharpening of the
*analysis* removes it: it is in the definition of the envelope.  Only changing
`Ttc.hybridTransitionBound` itself — branching on `1100 ≤ n` instead of adding a uniform
envelope — would. -/
theorem mixStepsBound_1099_le_hybridTransitionBound
    {n : Nat} {rin Rout δ Mw eps : Real} :
    max 0 (Ttc.mixStepsBound 1099 rin (2 * Rout) δ Mw eps)
      ≤ Ttc.hybridTransitionBound n rin Rout δ Mw eps := by
  have hmem : (1099 : Nat) ∈ Finset.range 1100 := Finset.mem_range.2 (by norm_num)
  have hsingle :
      max 0 (Ttc.mixStepsBound 1099 rin (2 * Rout) δ Mw eps)
        ≤ ∑ k ∈ Finset.range 1100,
            max 0 (Ttc.mixStepsBound k rin (2 * Rout) δ Mw eps) :=
    Finset.single_le_sum
      (f := fun k ↦ max 0 (Ttc.mixStepsBound k rin (2 * Rout) δ Mw eps))
      (fun i _ ↦ le_max_left _ _) hmem
  have h0 : (0 : Real) ≤
      max 0 (2 ^ 66 * (n : Real) ^ 2 * Rout ^ 2 / rin ^ 2 *
        Real.log (8 * Mw / eps ^ 2)) := le_max_left _ _
  unfold Ttc.hybridTransitionBound Ttc.lowDimBallWalkEnvelope
  linarith

#print axioms hybridTransitionBound_le
#print axioms mixStepsBound_1099_le_hybridTransitionBound
/-! ## Step 4 — transfer to the per-cube sampler bound

`Ttc.TTCSourceSharpOperationalFinal.canonicalHybridSamplerQueryBound` is
`8 · (ofReal (hybridTransitionBound …) · inspections + 1)`, which is monotone in the
transition bound.  So §3 transfers verbatim. -/

/-- Monotonicity of the per-cube sampler bound's shape in its transition slot. -/
theorem samplerShape_mono {T T' : Real} (h : T ≤ T') (w : ENNReal) :
    8 * (ENNReal.ofReal T * w + 1) ≤ 8 * (ENNReal.ofReal T' * w + 1) := by
  gcongr

/-- **The low-dimensional term survives into the per-cube sampler bound — LOWER bound.**

The composite `8 · (ofReal T · w + 1)` is monotone in `T`, and
`mixStepsBound_1099_le_hybridTransitionBound` needs no hypotheses, so the astronomical
low-dimensional term is present in the *actual* per-cube envelope at every dimension and every
cube.  It is not an artefact of the way the sum over cubes is bounded. -/
theorem samplerShape_lowDim_le
    {n : Nat} {rin Rout δ Mw eps : Real} (w : ENNReal) :
    8 * (ENNReal.ofReal (max 0 (Ttc.mixStepsBound 1099 rin (2 * Rout) δ Mw eps)) * w + 1)
      ≤ 8 * (ENNReal.ofReal (Ttc.hybridTransitionBound n rin Rout δ Mw eps) * w + 1) :=
  samplerShape_mono (mixStepsBound_1099_le_hybridTransitionBound) w

/-- **The decomposition, transferred — UPPER bound.** -/
theorem samplerShape_le_decomposed
    {n : Nat} {rin Rout δ Mw eps : Real} (w : ENNReal)
    (hrin : 0 < rin) (hRout : 0 ≤ Rout) (hMw : 1 ≤ Mw)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    8 * (ENNReal.ofReal (Ttc.hybridTransitionBound n rin Rout δ Mw eps) * w + 1)
      ≤ 8 * (ENNReal.ofReal
            (max 0 (2 ^ 66 * (n : Real) ^ 2 * Rout ^ 2 / rin ^ 2 *
                Real.log (8 * Mw / eps ^ 2)) + 1
              + 1100 * max 0 (Ttc.mixStepsBound 1099 rin (2 * Rout) δ Mw eps)) * w + 1) :=
  samplerShape_mono (hybridTransitionBound_le hrin hRout hMw heps heps1) w

#print axioms samplerShape_lowDim_le
#print axioms samplerShape_le_decomposed

/-! ## Step 4b — the per-cube bound at the run's own parameters

The `nu` slot of `Ttc.TTCSourceSharpOperationalFinal.canonicalHybridSamplerQueryBound` is
written inline in that definition.  `Ttc.ttcSampTol_pos` / `Ttc.ttcSampTol_le_one` are stated
about `Ttc.ttcSampTol`, and `TTCSourceSharpOperationalFinal` identifies the two by rewriting
`(algBlock …).r` to `Ttc.canonRfac (D atoms phi)` (see that file, lines 425–458).  Rather than
repeat that identification here, this statement takes the `nu` slot and its two range facts as
explicit binders: `hshape` says what the per-cube bound is at that `nu`, and the caller
discharges it exactly as `TTCSourceSharpOperationalFinal` does. -/
theorem canonicalHybridSamplerQueryBound_le_decomposed
    {n : Nat}
    {B : ENNReal} {w : ENNReal} {rin Rout δ Mw nu : Real}
    (hshape : B = 8 * (ENNReal.ofReal (Ttc.hybridTransitionBound n rin Rout δ Mw nu) * w + 1))
    (hrin : 0 < rin) (hRout : 0 ≤ Rout) (hMw : 1 ≤ Mw)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) :
    B ≤ 8 * (ENNReal.ofReal
          (max 0 (2 ^ 66 * (n : Real) ^ 2 * Rout ^ 2 / rin ^ 2 *
              Real.log (8 * Mw / nu ^ 2)) + 1
            + 1100 * max 0 (Ttc.mixStepsBound 1099 rin (2 * Rout) δ Mw nu)) * w + 1) := by
  rw [hshape]
  exact samplerShape_le_decomposed w hrin hRout hMw hnu hnu1

/-- **The low-dimensional term is in the per-cube bound — LOWER, and hypothesis-free apart
from the shape equation.** -/
theorem lowDim_le_canonicalHybridSamplerQueryBound
    {n : Nat}
    {B : ENNReal} {w : ENNReal} {rin Rout δ Mw nu : Real}
    (hshape : B = 8 * (ENNReal.ofReal (Ttc.hybridTransitionBound n rin Rout δ Mw nu) * w + 1)) :
    8 * (ENNReal.ofReal (max 0 (Ttc.mixStepsBound 1099 rin (2 * Rout) δ Mw nu)) * w + 1) ≤ B := by
  rw [hshape]
  exact samplerShape_lowDim_le w

#print axioms canonicalHybridSamplerQueryBound_le_decomposed
#print axioms lowDim_le_canonicalHybridSamplerQueryBound

#print axioms mixStepsBound_mono_dim
#print axioms lowDimBallWalkEnvelope_le

end Ttc.SamplerEnvelopeShape
