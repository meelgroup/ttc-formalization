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

## The point of the file, and what has changed twice under it

⚠ **Read this section as history.**  When it was written, `Ttc.hybridTransitionBound` added
`Ttc.lowDimBallWalkEnvelope` **unconditionally** — a uniform envelope covering both branches,
summing `Ttc.mixStepsBound k` over every `k < 1100`, so the bound contained a term of degree
≈ 4400 in the radius ratio with a `4^1099` constant *even where the walk being priced was
hit-and-run*.  The lemmas below were written to make that visible as a checked inequality
rather than a reading of a definition, and the lower bounds are what proved it was real.

Two changes since, both on 2026-08-19:

1. `Ttc.hybridTransitionBound` now **branches** rather than adding a uniform envelope, so each
   branch prices its own walk and nothing else.
2. The branch point moved from `1100` to `21`, because the spherical-cap estimate
   `Arlib.MarkovChains.unifSphere_cap_le` now holds from `n ≥ 21`.

Together those mean the ball-walk term is gone from every dimension TTC's capstone admits.
The lemmas below still hold and are still worth keeping — `lowDimBallWalkEnvelope_le` and the
`_of_low` family now describe the `n < 21` branch, which no theorem in this development
reaches — but the *finding* they were written to record no longer applies to the run.

## What is **not** here — and is now next door

This section used to read: "No bound of the form
`canonicalHybridSamplerQueryBound ≤ rMax · n^5 · rho^2` … **this development cannot discharge
it at large radius ratio** — the low-dimensional term above exceeds it."

That was true and is no longer.  With the branch at `21` the low-dimensional term is not in
the bound at any dimension the capstone admits, and
`Ttc/Exec/SamplerPolyEnvelope.lean` supplies the polynomial: per cube
`canonicalHybridSamplerQueryBound ≤ 8·((2⁶⁶·n²·ρ²·L + 1)·w + 1)`, and summed,
`canonicalCappedSampleQueryEnvelope_le_poly` — with `ρ²` and `L` `Finset.sup`s over the run's
own cubes, so no geometry binder.  What is still *not* anywhere is a polynomial form for the
**volume** half; that is `PLAN-SHAPE.md` §5's unsettled `ρ` exponent.
-/

namespace Ttc.SamplerEnvelopeShape

open MeasureTheory Set
open Ttc.TTCSourceSharpOperationalFinal
open Ttc.ConcreteHybridCanonicalOwnerPoly
open Ttc.TTCUnconditionalExplicitRuntime
open scoped ENNReal BigOperators Classical

variable {A : Type*}

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
`16384 · 4^20 · 20^2 · (2·Rout)^2/δ^2 · ((rin + 2·Rout)/rin)^80` (it was `4^1099 … ^4396`
until the threshold moved from `1100` to `21` on 2026-08-19).  With
`(rin + 2·Rout)/rin` the radius ratio, this is a term of degree ≈ 4400 in that ratio and a
constant of size `4^1099`.  It is **constant in the dimension `n`**, which is why the ambient
`n`-exponent is unaffected — and why it is invisible to any accounting that looks only at `n`. -/
theorem lowDimBallWalkEnvelope_le
    {rin Rout δ Mw eps : Real}
    (hrin : 0 < rin) (hRout : 0 ≤ Rout) (hMw : 1 ≤ Mw)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    Ttc.lowDimBallWalkEnvelope rin Rout δ Mw eps ≤
      21 * max 0 (Ttc.mixStepsBound 20 rin (2 * Rout) δ Mw eps) := by
  have hDm : (0 : Real) ≤ 2 * Rout := by linarith
  unfold Ttc.lowDimBallWalkEnvelope
  calc
    ∑ k ∈ Finset.range 21, max 0 (Ttc.mixStepsBound k rin (2 * Rout) δ Mw eps)
        ≤ ∑ _k ∈ Finset.range 21,
            max 0 (Ttc.mixStepsBound 20 rin (2 * Rout) δ Mw eps) := by
          refine Finset.sum_le_sum ?_
          intro k hk
          have hk' : k ≤ 20 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          exact max_le_max le_rfl
            (mixStepsBound_mono_dim hk' hrin hDm hMw heps heps1)
    _ = 21 * max 0 (Ttc.mixStepsBound 20 rin (2 * Rout) δ Mw eps) := by
          rw [Finset.sum_const, Finset.card_range]
          norm_num

/-! ### The two branches

`Ttc.hybridTransitionBound` branches on `21 ≤ n` exactly as `Ttc.kv97HybridSteps` does, so
each branch is an *equality*, not merely a bound. -/

/-- **High branch: the hit-and-run polynomial, and nothing else.**

⚠ Until 2026-08-19 the bound added `Ttc.lowDimBallWalkEnvelope` here too — a term of order
`4^1099 · (radius ratio)^4396`, pure overhead at a dimension where the walk being priced is
hit-and-run.  This equality is what replaces the old decomposition inequality. -/
theorem hybridTransitionBound_of_high
    {n : Nat} (hn : 21 ≤ n) (rin Rout δ Mw eps : Real) :
    Ttc.hybridTransitionBound n rin Rout δ Mw eps
      = max 0 (2 ^ 66 * (n : Real) ^ 2 * Rout ^ 2 / rin ^ 2 *
          Real.log (8 * Mw / eps ^ 2)) + 1 := by
  unfold Ttc.hybridTransitionBound
  rw [if_pos hn]

/-- **Low branch: the ball walk's own bound at dimension `n`.** -/
theorem hybridTransitionBound_of_low
    {n : Nat} (hn : ¬ 21 ≤ n) (rin Rout δ Mw eps : Real) :
    Ttc.hybridTransitionBound n rin Rout δ Mw eps
      = max 0 (Ttc.mixStepsBound n rin (2 * Rout) δ Mw eps) + 1 := by
  unfold Ttc.hybridTransitionBound
  rw [if_neg hn]

/-- **On the low branch the bound is at least the ball walk's own cost — a LOWER bound.**

This is what remains of the old `mixStepsBound_1099_le_hybridTransitionBound`, which asserted
the low-dimensional term at *every* dimension and is false since the branching fix.

Restricted to `n < 1100` it is still true, and now says something different and still worth
knowing: `Ttc.mixStepsBound n` is `4^n · ((γ+Dm)/γ)^(4n)`-shaped, so on that branch the bound
grows exponentially **in the dimension** — and that is the ball walk's genuine cost at
dimension `n`, not an artefact of the envelope.  `n` is bounded there, so this is a constant
rather than an asymptotic obstruction; but the constant at `n = 1099` is astronomical, and
TTC's capstone admits `21 ≤ n`.

Removing it means establishing hit-and-run below dimension `1100`.  The threshold is an
artefact of `Arlib.MarkovChains.unifSphere_cap_le`'s union bound, not of its statement — see
that file, and `lean/PLAN-SPHERECAP.md`. -/
theorem mixStepsBound_le_hybridTransitionBound_of_low
    {n : Nat} (hn : ¬ 21 ≤ n) {rin Rout δ Mw eps : Real} :
    max 0 (Ttc.mixStepsBound n rin (2 * Rout) δ Mw eps)
      ≤ Ttc.hybridTransitionBound n rin Rout δ Mw eps := by
  rw [hybridTransitionBound_of_low hn]
  linarith

#print axioms hybridTransitionBound_of_high
#print axioms hybridTransitionBound_of_low
#print axioms mixStepsBound_le_hybridTransitionBound_of_low
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
    {n : Nat} (hn : ¬ 21 ≤ n) {rin Rout δ Mw eps : Real} (w : ENNReal) :
    8 * (ENNReal.ofReal (max 0 (Ttc.mixStepsBound n rin (2 * Rout) δ Mw eps)) * w + 1)
      ≤ 8 * (ENNReal.ofReal (Ttc.hybridTransitionBound n rin Rout δ Mw eps) * w + 1) :=
  samplerShape_mono (mixStepsBound_le_hybridTransitionBound_of_low hn) w

/-- **The decomposition, transferred — UPPER bound.** -/
theorem samplerShape_eq_of_high
    {n : Nat} (hn : 21 ≤ n) {rin Rout δ Mw eps : Real} (w : ENNReal) :
    8 * (ENNReal.ofReal (Ttc.hybridTransitionBound n rin Rout δ Mw eps) * w + 1)
      = 8 * (ENNReal.ofReal
            (max 0 (2 ^ 66 * (n : Real) ^ 2 * Rout ^ 2 / rin ^ 2 *
                Real.log (8 * Mw / eps ^ 2)) + 1) * w + 1) := by
  rw [hybridTransitionBound_of_high hn]

#print axioms samplerShape_lowDim_le
#print axioms samplerShape_eq_of_high

/-! ## Step 4b — the per-cube bound at the run's own parameters

The `nu` slot of `Ttc.TTCSourceSharpOperationalFinal.canonicalHybridSamplerQueryBound` is
written inline in that definition.  `Ttc.ttcSampTol_pos` / `Ttc.ttcSampTol_le_one` are stated
about `Ttc.ttcSampTol`, and `TTCSourceSharpOperationalFinal` identifies the two by rewriting
`(algBlock …).r` to `Ttc.canonRfac (D atoms phi)` (see that file, lines 425–458).  Rather than
repeat that identification here, this statement takes the `nu` slot and its two range facts as
explicit binders: `hshape` says what the per-cube bound is at that `nu`, and the caller
discharges it exactly as `TTCSourceSharpOperationalFinal` does. -/
theorem canonicalHybridSamplerQueryBound_eq_of_high
    {n : Nat} (hn : 21 ≤ n)
    {B : ENNReal} {w : ENNReal} {rin Rout δ Mw nu : Real}
    (hshape : B = 8 * (ENNReal.ofReal (Ttc.hybridTransitionBound n rin Rout δ Mw nu) * w + 1)) :
    B = 8 * (ENNReal.ofReal
          (max 0 (2 ^ 66 * (n : Real) ^ 2 * Rout ^ 2 / rin ^ 2 *
              Real.log (8 * Mw / nu ^ 2)) + 1) * w + 1) := by
  rw [hshape]
  exact samplerShape_eq_of_high hn w

/-- **The low-dimensional term is in the per-cube bound — LOWER, and hypothesis-free apart
from the shape equation.** -/
theorem lowDim_le_canonicalHybridSamplerQueryBound
    {n : Nat} (hn : ¬ 21 ≤ n)
    {B : ENNReal} {w : ENNReal} {rin Rout δ Mw nu : Real}
    (hshape : B = 8 * (ENNReal.ofReal (Ttc.hybridTransitionBound n rin Rout δ Mw nu) * w + 1)) :
    8 * (ENNReal.ofReal (max 0 (Ttc.mixStepsBound n rin (2 * Rout) δ Mw nu)) * w + 1) ≤ B := by
  rw [hshape]
  exact samplerShape_lowDim_le hn w

#print axioms canonicalHybridSamplerQueryBound_eq_of_high
#print axioms lowDim_le_canonicalHybridSamplerQueryBound

/-! ## Step 4c — the per-cube bound at the run's own parameters, discharged

The `nu` slot is written inline in `canonicalHybridSamplerQueryBound`.  Rather than transcribe
it, the existential below lets unification supply it (`rfl`), leaving exactly the two goals
`0 < nu` and `nu ≤ 1` at the inline term — which are the goals
`Ttc.TTCSourceSharpOperationalFinal` already discharges (its lines 425–458) by rewriting
`(algBlock …).r` to `Ttc.canonRfac (D atoms phi)` and appealing to `Ttc.ttcSampTol_pos` /
`Ttc.ttcSampTol_le_one`. -/
set_option maxHeartbeats 4000000 in
theorem exists_canonicalHybridSamplerQueryBound_shape
    {n : Nat} (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < Ttc.volSol (Ttc.atomSet atoms) phi)
    (i : CubeIndex atoms phi) :
    ∃ (nu : Real) (w : ENNReal),
      canonicalHybridSamplerQueryBound atoms phi eps delta i
        = 8 * (ENNReal.ofReal (Ttc.hybridTransitionBound n
              (canonicalHybridInnerRadius atoms phi eps delta i)
              (canonicalHybridOuterRadius atoms phi eps delta i)
              (canonicalHybridStep atoms phi eps delta i)
              (canonicalHybridWarm atoms phi eps delta i) nu) * w + 1)
        ∧ 0 < nu ∧ nu ≤ 1 := by
  refine ⟨_, _, rfl, ?_, ?_⟩
  · have hPr : (Ttc.algBlock atoms phi eps delta).r =
        (Nat.card (Ttc.FacetIndex (Ttc.ConcreteHybridCanonicalOwnerPoly.D atoms phi)) : Real) :=
      Ttc.ttcBlock_r atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol
    have hrf : (Ttc.algBlock atoms phi eps delta).r =
        Ttc.canonRfac (Ttc.ConcreteHybridCanonicalOwnerPoly.D atoms phi) := by rw [hPr, Ttc.canonRfac]
    rw [hrf]
    change 0 < Ttc.ttcSampTol atoms phi eps delta i
    exact Ttc.ttcSampTol_pos atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol i
  · have hPr : (Ttc.algBlock atoms phi eps delta).r =
        (Nat.card (Ttc.FacetIndex (Ttc.ConcreteHybridCanonicalOwnerPoly.D atoms phi)) : Real) :=
      Ttc.ttcBlock_r atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol
    have hrf : (Ttc.algBlock atoms phi eps delta).r =
        Ttc.canonRfac (Ttc.ConcreteHybridCanonicalOwnerPoly.D atoms phi) := by rw [hPr, Ttc.canonRfac]
    rw [hrf]
    change Ttc.ttcSampTol atoms phi eps delta i ≤ 1
    exact Ttc.ttcSampTol_le_one atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol i

#print axioms exists_canonicalHybridSamplerQueryBound_shape

/-! ## Step 3 — the sup over cubes, and the sum

`Ttc.TTCUnconditionalExplicitRuntime.canonicalCappedSampleQueryEnvelope_le_explicitCaps`
already reduces the sum to `(cube count) · rateThreshold · endpointCap`, with no premises.
`endpointCap` is a `Finset.sup`, so a bound uniform in the cube closes it. -/

/-- **The whole sampler envelope, closed at a uniform per-cube bound.**

`T` must be uniform over cubes.  That is the same move the paper makes when it replaces every
`R_i/γ_i` by `ρ` and every `r_i` by `r_max` (`sections/analysis.tex`, proof of `thm:runtime`),
so it is the right shape — but it is a hypothesis here, not something discharged. -/
theorem canonicalCappedSampleQueryEnvelope_le_uniform
    {n : Nat} (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    {T : Real} {w : ENNReal}
    (hT : ∀ i : CubeIndex atoms phi,
      canonicalHybridSamplerQueryBound atoms phi eps delta i
        ≤ 8 * (ENNReal.ofReal T * w + 1)) :
    canonicalCappedSampleQueryEnvelope atoms phi eps delta ≤
      ((Ttc.toDNFd (Ttc.preprocess atoms phi)).length : ENNReal) *
        (canonicalRateThreshold atoms phi eps delta * (8 * (ENNReal.ofReal T * w + 1))) := by
  refine (canonicalCappedSampleQueryEnvelope_le_explicitCaps atoms phi eps delta).trans ?_
  gcongr
  unfold canonicalEndpointInspectionCap
  exact Finset.sup_le fun i _ ↦ hT i

/-- **Every cube's contribution is under the whole envelope.**

With `lowDim_le_canonicalHybridSamplerQueryBound` this carries the low-dimensional term all the
way to the top-level sampler envelope, not merely to the per-cube bound: the sum is over
nonnegative terms, so it dominates any one of them. -/
theorem cube_le_canonicalCappedSampleQueryEnvelope
    {n : Nat} (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (i : CubeIndex atoms phi) :
    (polyGoodRateCap atoms phi eps delta i : ENNReal) *
        canonicalHybridSamplerQueryBound atoms phi eps delta i
      ≤ canonicalCappedSampleQueryEnvelope atoms phi eps delta := by
  unfold canonicalCappedSampleQueryEnvelope
  exact Finset.single_le_sum (f := fun j ↦
      (polyGoodRateCap atoms phi eps delta j : ENNReal) *
        canonicalHybridSamplerQueryBound atoms phi eps delta j)
    (fun j _ ↦ by simp) (Finset.mem_univ i)

#print axioms canonicalCappedSampleQueryEnvelope_le_uniform
#print axioms cube_le_canonicalCappedSampleQueryEnvelope

#print axioms mixStepsBound_mono_dim
#print axioms lowDimBallWalkEnvelope_le

end Ttc.SamplerEnvelopeShape
