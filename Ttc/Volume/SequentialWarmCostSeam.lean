/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Convexity.GaussianCooling.WarmSpeedy
import Arlib.MarkovChains.Continuous.WastedStepsGaussian

/-!
# The exact sequential warm-start cost seam

The source-faithful next-phase start is the previous exact cooling law conditioned on the
shrunken body.  It is `2e`-warm for the next speedy Gaussian stationary law.  Consequently
the Gaussian wasted-step estimate pays the constant `2e`, rather than the exponential
independent-restart constant.

This file deliberately stops at the exact-law seam.  Two further facts are not available:

* the operational previous output is only `TVLe`-close to `coolLaw`; `TVLe` does not imply
  the measure domination `IsWarm` requires;
* carrying actual samples along `k` Markov streams makes different phase vectors dependent,
  whereas `Ttc.CVEst.CoordinateIndep` requires `iIndepFun` of those phase vectors.

Thus this theorem closes the ordinary-step cost calculation once an exact sequential start
is supplied, but does not silently treat an approximate output as exact or independent.
-/

namespace Ttc.CVSequential

open MeasureTheory Metric Set
open Arlib Arlib.GaussianCooling
open scoped ENNReal Pointwise

variable {n m : Nat}

/-- The exact source-faithful start of phase `i+1`: reject an exact phase-`i` draw until it
lies in the standard shrunken body. -/
noncomputable def exactSequentialStart (sigmaSq : Nat -> Real)
    (K : Set (EuclSpace n)) (i : Nat) : Measure (EuclSpace n) :=
  Arlib.condOn (coolLaw m sigmaSq K i)
    ((1 - 1 / (2 * (n : Real))) • K)

/-- Exact consecutive-phase starts have the dimension-free warmness constant `2e`. -/
theorem isWarm_exactSequentialStart (hn : 1 <= n) {sigmaSq : Nat -> Real}
    (hsigma : forall j, 0 < sigmaSq j)
    {K : Set (EuclSpace n)} (hKm : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m) {cc : Real} (hcc1 : 1 <= cc)
    (hcc : cc <= 1 + 2 / (n : Real))
    (hsched : sigmaSq (i + 1) = cc * sigmaSq i)
    {delta : Real} (hdelta : 0 < delta) (hdeltan : delta <= 1 / (2 * (n : Real))) :
    IsWarm (ENNReal.ofReal (2 * Real.exp 1))
      (exactSequentialStart (m := m) sigmaSq K i)
      (Arlib.MarkovChains.ellGaussianProb K delta (sigmaSq (i + 1))) := by
  exact Arlib.GaussianCooling.isWarm_condOn_coolLaw_ellGaussianProb hn hsigma hKm hKc
    hball hfin hi hcc1 hcc hsched hdelta hdeltan

/-- The Gaussian wasted-step bound for the exact sequential start.  Its right side contains
the constant `2e`, not a phase-index-dependent or dimension-exponential warmness factor. -/
theorem mul_sum_lintegral_sequentialStart_le
    (hn : 1 <= n) {sigmaSq : Nat -> Real} (hsigma : forall j, 0 < sigmaSq j)
    {K : Set (EuclSpace n)} (hKm : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m) {cc : Real} (hcc1 : 1 <= cc)
    (hcc : cc <= 1 + 2 / (n : Real))
    (hsched : sigmaSq (i + 1) = cc * sigmaSq i)
    {delta : Real} (hdelta : 0 < delta) (hdeltan : delta <= 1 / (2 * (n : Real)))
    {s : Real} (hs : 0 < s) (hnext : sigmaSq (i + 1) = s)
    {R : Real} (hR : 0 <= R) (hKR : forall x, x ∈ K -> ‖x‖ <= R)
    (hZ0 : Arlib.MarkovChains.ellGaussianMeasure K delta s Set.univ ≠ 0)
    (hZtop : Arlib.MarkovChains.ellGaussianMeasure K delta s Set.univ ≠ ⊤)
    {lam : ENNReal}
    (hlam : lam * (∫⁻ x in K, Arlib.MarkovChains.gaussianWeight s x) <=
      Arlib.MarkovChains.ellGaussianMeasure K delta s Set.univ)
    (mSteps : Nat) :
    ENNReal.ofReal (Real.exp (-(2 * R * delta + delta ^ 2) / (2 * s))) * lam *
        ∑ j ∈ Finset.range mSteps,
          ∫⁻ x, (Arlib.MarkovChains.ell K delta x *
            Arlib.MarkovChains.speedyMetropolisMove K delta s x)⁻¹
            ∂(Arlib.MarkovChains.iterate
              (Arlib.MarkovChains.speedyMetropolisGaussian K delta s)
              (exactSequentialStart (m := m) sigmaSq K i) j)
      <= (mSteps : ENNReal) * ENNReal.ofReal (2 * Real.exp 1) := by
  have hwarm := isWarm_exactSequentialStart hn hsigma hKm hKc hball hfin hi hcc1 hcc
    hsched hdelta hdeltan
  rw [hnext] at hwarm
  exact Arlib.MarkovChains.mul_sum_lintegral_inv_ell_mul_move_iterate_speedyMetropolisGaussian_le
      hKm hdelta hs hR hKR hZ0 hZtop hlam hwarm mSteps

/-- Any law definitionally identified with the exact sequential start inherits the constant
warmness seam.  This is the exact equality obligation an operational construction would
have to discharge; a `TVLe` premise is intentionally not substituted for it. -/
theorem isWarm_of_eq_exactSequentialStart
    (hn : 1 <= n) {sigmaSq : Nat -> Real} (hsigma : forall j, 0 < sigmaSq j)
    {K : Set (EuclSpace n)} (hKm : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m) {cc : Real} (hcc1 : 1 <= cc)
    (hcc : cc <= 1 + 2 / (n : Real))
    (hsched : sigmaSq (i + 1) = cc * sigmaSq i)
    {delta : Real} (hdelta : 0 < delta) (hdeltan : delta <= 1 / (2 * (n : Real)))
    {mu : Measure (EuclSpace n)}
    (hmu : mu = exactSequentialStart (m := m) sigmaSq K i) :
    IsWarm (ENNReal.ofReal (2 * Real.exp 1)) mu
      (Arlib.MarkovChains.ellGaussianProb K delta (sigmaSq (i + 1))) := by
  rw [hmu]
  exact isWarm_exactSequentialStart hn hsigma hKm hKc hball hfin hi hcc1 hcc hsched
    hdelta hdeltan

end Ttc.CVSequential

#print axioms Ttc.CVSequential.isWarm_exactSequentialStart
#print axioms Ttc.CVSequential.mul_sum_lintegral_sequentialStart_le
#print axioms Ttc.CVSequential.isWarm_of_eq_exactSequentialStart
