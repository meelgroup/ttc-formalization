import Ttc.Exec.SamplerEnvelopeShape

namespace Ttc.SamplerPolyEnvelope

open MeasureTheory Set
open Ttc.TTCSourceSharpOperationalFinal
open Ttc.ConcreteHybridCanonicalOwnerPoly
open Ttc.TTCUnconditionalExplicitRuntime
open Ttc.SamplerEnvelopeShape
open scoped ENNReal BigOperators Classical

variable {A : Type*} {n : Nat}

/-- **The per-cube shape with the tolerance slot named.**

`Ttc.SamplerEnvelopeShape.exists_canonicalHybridSamplerQueryBound_shape` leaves `nu`
existentially bound, which is enough to *decompose* the bound but not to *bound* it: the
`log (8·Mw/nu²)` factor blows up as `nu → 0`, so a uniform estimate needs to know which `nu`.
This is the same equation with `nu` pinned to `Ttc.ttcSampTol`. -/
theorem canonicalHybridSamplerQueryBound_eq_at_tol
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < Ttc.volSol (Ttc.atomSet atoms) phi)
    (i : CubeIndex atoms phi) :
    canonicalHybridSamplerQueryBound atoms phi eps delta i
      = 8 * (ENNReal.ofReal (Ttc.hybridTransitionBound n
            (canonicalHybridInnerRadius atoms phi eps delta i)
            (canonicalHybridOuterRadius atoms phi eps delta i)
            (canonicalHybridStep atoms phi eps delta i)
            (canonicalHybridWarm atoms phi eps delta i)
            (Ttc.ttcSampTol atoms phi eps delta i)) *
          Ttc.ConcreteHybridExpectedQuerySampler.hybridStepInspectionBound n
            (Nat.card (Ttc.FacetIndex (D atoms phi))) + 1) := by
  have hPr : (Ttc.algBlock atoms phi eps delta).r =
      (Nat.card (Ttc.FacetIndex (D atoms phi)) : Real) :=
    Ttc.ttcBlock_r atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol
  have hrf : (Ttc.algBlock atoms phi eps delta).r =
      Ttc.canonRfac (D atoms phi) := by rw [hPr, Ttc.canonRfac]
  unfold canonicalHybridSamplerQueryBound
  rw [hrf]
  rfl


/-! ## The run's own uniform geometry

The paper replaces every `R_i/γ_i` by `ρ` and every `r_i` by `r_max`
(`sections/analysis.tex`, proof of `thm:runtime`).  These two definitions are that move, taken
at the run's own per-cube geometry rather than at a supplied binder: a `Finset.sup` over the
cubes, so nothing is assumed and the bound below carries no geometry hypothesis. -/

/-- **The run's own squared radius ratio, maximised over cubes.**

A `⨆` over the run's own cubes, clamped at `0` so that it is usable as an upper bound in a
product with no side condition.  This is the move the paper makes when it replaces every
`R_i/γ_i` by a single `ρ` (`sections/analysis.tex`, proof of `thm:runtime`), taken at the
run's own geometry rather than at a supplied binder. -/
noncomputable def sampRhoSq (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real) : Real :=
  max 0 (⨆ i : CubeIndex atoms phi,
    (canonicalHybridOuterRadius atoms phi eps delta i) ^ 2 /
      (canonicalHybridInnerRadius atoms phi eps delta i) ^ 2)

/-- **The run's own warm-start logarithm, maximised over cubes.** -/
noncomputable def sampLog (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real) : Real :=
  max 0 (⨆ i : CubeIndex atoms phi,
    Real.log (8 * canonicalHybridWarm atoms phi eps delta i /
      (Ttc.ttcSampTol atoms phi eps delta i) ^ 2))

theorem sampRhoSq_nonneg (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real) :
    0 ≤ sampRhoSq atoms phi eps delta := le_max_left _ _

theorem sampLog_nonneg (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real) :
    0 ≤ sampLog atoms phi eps delta := le_max_left _ _

theorem le_sampRhoSq (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (i : CubeIndex atoms phi) :
    (canonicalHybridOuterRadius atoms phi eps delta i) ^ 2 /
        (canonicalHybridInnerRadius atoms phi eps delta i) ^ 2
      ≤ sampRhoSq atoms phi eps delta := by
  unfold sampRhoSq
  refine le_trans (le_ciSup (f := fun i : CubeIndex atoms phi =>
    (canonicalHybridOuterRadius atoms phi eps delta i) ^ 2 /
      (canonicalHybridInnerRadius atoms phi eps delta i) ^ 2)
    (Set.finite_range _).bddAbove i) (le_max_right _ _)

theorem le_sampLog (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (i : CubeIndex atoms phi) :
    Real.log (8 * canonicalHybridWarm atoms phi eps delta i /
        (Ttc.ttcSampTol atoms phi eps delta i) ^ 2)
      ≤ sampLog atoms phi eps delta := by
  unfold sampLog
  refine le_trans (le_ciSup (f := fun i : CubeIndex atoms phi =>
    Real.log (8 * canonicalHybridWarm atoms phi eps delta i /
      (Ttc.ttcSampTol atoms phi eps delta i) ^ 2))
    (Set.finite_range _).bddAbove i) (le_max_right _ _)

/-! ## The transition bound is polynomial -/

/-- **At `21 ≤ n` the transition bound is `2⁶⁶·n²·ρ²·L + 1` and nothing else.**

This is the statement `Ttc/Exec/SamplerEnvelopeShape.lean`'s "What is **not** here" section
said the development could not supply.  It could not, while the threshold was `1100`: below it
the bound was `Ttc.mixStepsBound n`, carrying `4^n` and a `(radius ratio)^(4n)`.  The
spherical-cap estimate now holds from `n ≥ 21`, so the hit-and-run branch covers every
dimension TTC's capstone admits and the bound is a polynomial. -/
theorem hybridTransitionBound_le_poly {n : Nat} (hn : 21 ≤ n)
    {rin Rout deltaStep Mw nu rho L : Real}
    (hrho : Rout ^ 2 / rin ^ 2 ≤ rho) (hrho0 : 0 ≤ rho)
    (hL : Real.log (8 * Mw / nu ^ 2) ≤ L) (hL0 : 0 ≤ L) :
    Ttc.hybridTransitionBound n rin Rout deltaStep Mw nu
      ≤ 2 ^ 66 * (n : Real) ^ 2 * rho * L + 1 := by
  rw [hybridTransitionBound_of_high hn]
  set C : Real := 2 ^ 66 * (n : Real) ^ 2 with hC
  have hC0 : (0 : Real) ≤ C := by rw [hC]; positivity
  have hq0 : (0 : Real) ≤ Rout ^ 2 / rin ^ 2 := by positivity
  have hprod : Rout ^ 2 / rin ^ 2 * Real.log (8 * Mw / nu ^ 2) ≤ rho * L := by
    rcases le_or_gt (Real.log (8 * Mw / nu ^ 2)) 0 with hb | hb
    · nlinarith [mul_nonneg hrho0 hL0]
    · nlinarith
  have hmax : max 0 (C * Rout ^ 2 / rin ^ 2 * Real.log (8 * Mw / nu ^ 2)) ≤ C * (rho * L) := by
    refine max_le (mul_nonneg hC0 (mul_nonneg hrho0 hL0)) ?_
    have hrw : C * Rout ^ 2 / rin ^ 2 * Real.log (8 * Mw / nu ^ 2)
        = C * (Rout ^ 2 / rin ^ 2 * Real.log (8 * Mw / nu ^ 2)) := by ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_left hprod hC0
  have hgoal : C * (rho * L) = 2 ^ 66 * (n : Real) ^ 2 * rho * L := by rw [hC]; ring
  linarith [hmax, hgoal.le, hgoal.ge]


/-- **The run's own polynomial transition bound**, with no geometry binder: the two uniform
quantities are `Finset.sup`s over the run's own cubes. -/
noncomputable def sampPolyT (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real) : Real :=
  2 ^ 66 * (n : Real) ^ 2 * sampRhoSq atoms phi eps delta *
    sampLog atoms phi eps delta + 1

/-- **Every cube's sampler bound is under the polynomial.** -/
theorem canonicalHybridSamplerQueryBound_le_poly {n : Nat} (hn21 : 21 ≤ n)
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < Ttc.volSol (Ttc.atomSet atoms) phi)
    (i : CubeIndex atoms phi) :
    canonicalHybridSamplerQueryBound atoms phi eps delta i
      ≤ 8 * (ENNReal.ofReal (sampPolyT atoms phi eps delta) *
          Ttc.ConcreteHybridExpectedQuerySampler.hybridStepInspectionBound n
            (Nat.card (Ttc.FacetIndex (D atoms phi))) + 1) := by
  rw [canonicalHybridSamplerQueryBound_eq_at_tol atoms phi eps delta
    h_eps_pos h_eps_le hn hphi hvol i]
  gcongr
  unfold sampPolyT
  exact hybridTransitionBound_le_poly hn21
    (le_sampRhoSq atoms phi eps delta i) (sampRhoSq_nonneg atoms phi eps delta)
    (le_sampLog atoms phi eps delta i) (sampLog_nonneg atoms phi eps delta)

/-- **The sampler envelope with its per-endpoint factor in closed polynomial form.**

`m · threshold · 8·((2⁶⁶·n²·ρ²·L + 1)·(r/2) + 1)` — every factor an explicit function of the
run's own inputs, and **no hypothesis beyond the ones `Ttc.ttc_volume` already carries**.

⚠ **This is not a polynomial bound on the sampler envelope.**  What is polynomial is the
`8·((2⁶⁶n²ρ²L + 1)(r/2) + 1)` factor — the cost of *one* endpoint.  `threshold` is
`Ttc.canonicalRateThreshold`, the endpoint **count**, and it is the dilated cube volume:
`Ttc.algScale ^ n · Vol`, which even after the 2026-08-20 `n`-th root in `Ttc.scaleFactor`
retains an exponential body-to-inscribed-ball ratio.  The statement below is exact about
which factor moved.

⚠ This also closes the *sampler* half only.  The volume half — `shapedVolumeQueryEnvelopeAt`
— is not reduced to a polynomial here and should not be: its `ρ` exponent is the unsettled
question `lean/PLAN-SHAPE.md` §5 records, and gluing an unsettled volume reduction onto a
settled sampler one would make the whole statement as soft as its softest half. -/
theorem canonicalCappedSampleQueryEnvelope_le_poly {n : Nat} (hn21 : 21 ≤ n)
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < Ttc.volSol (Ttc.atomSet atoms) phi) :
    canonicalCappedSampleQueryEnvelope atoms phi eps delta ≤
      ((Ttc.toDNFd (Ttc.preprocess atoms phi)).length : ENNReal) *
        (canonicalRateThreshold atoms phi eps delta *
          (8 * (ENNReal.ofReal (sampPolyT atoms phi eps delta) *
            Ttc.ConcreteHybridExpectedQuerySampler.hybridStepInspectionBound n
              (Nat.card (Ttc.FacetIndex (D atoms phi))) + 1))) :=
  canonicalCappedSampleQueryEnvelope_le_uniform atoms phi eps delta
    (fun i => canonicalHybridSamplerQueryBound_le_poly hn21 atoms phi eps delta
      h_eps_pos h_eps_le hn hphi hvol i)

#print axioms canonicalHybridSamplerQueryBound_eq_at_tol
#print axioms hybridTransitionBound_le_poly
#print axioms canonicalCappedSampleQueryEnvelope_le_poly

end Ttc.SamplerPolyEnvelope
