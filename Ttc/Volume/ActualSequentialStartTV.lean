/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.SequentialWarmCostSeam
import Arlib.Convexity.GaussianCooling.PhaseInduction

/-!
# TV control of the operational next-phase start

An approximate phase output need not be warm.  The volume algorithm first conditions it on
the shrunken body.  The corresponding exact cooling law gives that body mass at least one
half, so conditioning inflates the previous TV error by at most eight.  The resulting law
is therefore close to the exact `2e`-warm start, which is sufficient for timeout transfer.
-/

namespace Ttc.CVSequential

open MeasureTheory Metric Set
open Arlib Arlib.GaussianCooling
open scoped ENNReal Pointwise

variable {n m : Nat}

/-- Conditioning an approximate phase law on the shrunken body stays within `8 eps` of the
exact sequential start.  The body is explicit because operational callers normally run on
a truncated convex body rather than `univ`. -/
theorem tvLe_condOn_exactSequentialStart
    (hn : 1 <= n) {sigmaSq : Nat -> Real} (hsigma : forall j, 0 < sigmaSq j)
    {K : Set (EuclSpace n)} (hKm : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i < m)
    {mu : Measure (EuclSpace n)} [IsProbabilityMeasure mu]
    {eps : ENNReal} (htv : TVLe mu (coolLaw m sigmaSq K i) eps) :
    TVLe
      (Arlib.condOn mu ((1 - 1 / (2 * (n : Real))) • K))
      (exactSequentialStart (m := m) sigmaSq K i)
      (8 * eps) := by
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hnR1 : (1 : Real) <= (n : Real) := by exact_mod_cast hn
  have hc0 : (0 : Real) < 1 - 1 / (2 * (n : Real)) := by
    have : 1 / (2 * (n : Real)) <= 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hA : MeasurableSet ((1 - 1 / (2 * (n : Real))) • K) := by
    exact Arlib.MarkovChains.measurableSet_smul_set hKm hc0.ne'
  letI : IsProbabilityMeasure (coolLaw m sigmaSq K i) :=
    coolLaw_isProbabilityMeasure hsigma hball hfin i
  have hhalf : ENNReal.ofReal (1 / 2 : Real) <=
      coolLaw m sigmaSq K i ((1 - 1 / (2 * (n : Real))) • K) :=
    half_le_coolLaw_smul_set hn hsigma hKm hKc hball hfin hi
  simpa only [exactSequentialStart] using Arlib.tvLe_condOn_half htv hA hhalf

#print axioms tvLe_condOn_exactSequentialStart

end Ttc.CVSequential
