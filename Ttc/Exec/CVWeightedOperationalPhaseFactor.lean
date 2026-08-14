import Ttc.Exec.CVGaussianFactorSevenAssembly

set_option autoImplicit false

/-!
# Phase-dependent operational moment factors

The source-sharp exact estimator uses a different relative second-moment factor in each
cooling phase.  Operational TV transport need not replace all of them by the uniform
factor `8` or `9`: an arbitrarily assigned nonnegative slack `s i` gives the factor
`C i + s i`, provided the phase TV error pays exactly the displayed bounded-score
transport inequality.

After averaging `k` independent scalar paths, the resulting empirical factor is

`1 + (C i + s i - 1) / k`.

This is the factor consumed by the weighted-prefix recursion in
`CVSourceSampleCountAudit`.  Thus the phase sampler already supplies the correct
*shape* for a source-sharp repair.  What remains analytic is choosing the TV errors and
clipping level so that the product of these phase-dependent factors (including clipping
inflation) stays in the source budget; no new execution-law representation is needed.
-/

namespace Ttc.CVWeightedOperationalPhaseFactor

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.GaussianCooling
open Ttc.CVIndependentStreamMoments
open Ttc.CVGaussianFactorSevenAssembly
open scoped ENNReal

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- TV transport preserves the exact phase factor up to an explicitly allocated additive
slack.  This is the phase-dependent specialization of the existing generic factor
transport theorem. -/
theorem operational_phaseScore_sq_moment_le_exact_add_slack
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {chainLength : Nat} {sigmaSq : Nat → Real} {i : Nat}
    {K : Set (State n)} {X : Omega → State n} {e : ENNReal}
    (hsigma : ∀ j, 0 < sigmaSq j) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : Real} (hKR : K ⊆ closedBall (0 : State n) R)
    (hX : Measurable X)
    (hTV : TVLe (Measure.map X mu) (coolLaw chainLength sigmaSq K i) e)
    (he : e ≠ ⊤) {C slack : Real} (hC0 : 0 ≤ C) (hslack0 : 0 ≤ slack)
    (hexact :
      ∫ x, phaseScore chainLength sigmaSq (interior K) i x ^ 2
          ∂(coolLaw chainLength sigmaSq K i) ≤
        C * (∫ x, phaseScore chainLength sigmaSq (interior K) i x
          ∂(coolLaw chainLength sigmaSq K i)) ^ 2)
    (htransport : e.toReal *
        (Real.exp (R ^ 2 / (2 * sigmaSq i)) ^ 2 *
          (1 + 2 * (C + slack))) ≤
      slack *
        (chain chainLength sigmaSq K (i + 1) /
          chain chainLength sigmaSq K i) ^ 2) :
    ∫ omega, phaseScore chainLength sigmaSq (interior K) i (X omega) ^ 2 ∂mu ≤
      (C + slack) * (∫ omega,
        phaseScore chainLength sigmaSq (interior K) i (X omega) ∂mu) ^ 2 := by
  apply operational_phaseScore_sq_moment_le_factor hsigma hKc hball hfin hKR hX
    hTV he hC0 (by linarith) hexact
  simpa only [add_sub_cancel_left] using htransport

/-- A scalar operational factor `C + slack` becomes the phase-dependent empirical factor
`1 + (C + slack - 1)/k` after taking `k` independent samples. -/
theorem scalar_exact_add_slack_to_streamAverage
    {Path : Type*} [MeasurableSpace Path]
    {k : Nat} (hk : 0 < k) (mu : Measure Path) [IsProbabilityMeasure mu]
    {g : Path → Real} (hg : Measurable g) (hL2 : MemLp g 2 mu)
    {C slack : Real}
    (hsq : ∫ x, (g x) ^ 2 ∂mu ≤
      (C + slack) * (∫ x, g x ∂mu) ^ 2) :
    ∫ omega, (streamAverage (k := k) g omega) ^ 2
        ∂(independentStreamLaw mu) ≤
      (1 + (C + slack - 1) / (k : Real)) *
        (∫ omega, streamAverage (k := k) g omega
          ∂(independentStreamLaw mu)) ^ 2 := by
  have hmean := integral_streamAverage hk mu hg (hL2.integrable one_le_two)
  rw [hmean]
  exact integral_streamAverage_sq_le hk mu hg hL2 rfl hsq

#print axioms operational_phaseScore_sq_moment_le_exact_add_slack
#print axioms scalar_exact_add_slack_to_streamAverage

end Ttc.CVWeightedOperationalPhaseFactor
