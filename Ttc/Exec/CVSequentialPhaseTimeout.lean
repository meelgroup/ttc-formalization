/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.AdjustableSequentialTimeout
import Ttc.Volume.ActualSequentialStartTV

/-!
# Source-faithful sequential Gaussian phase with a proposal timeout

This theorem composes the two facts needed to keep the Cousins--Vempala execution
polynomial without pretending that a TV-close law is warm:

1. condition the actual preceding phase output on the shrunken body; this is within
   `8 eps` of the corresponding exact conditioned cooling law;
2. the exact conditioned law is `2e`-warm, so the adjustable lazy walk has bounded
   expected proposal count; transfer a finite timeout event back to the actual start.
-/

namespace Ttc.CVSequential

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.GaussianCooling Arlib.MarkovChains
open Ttc.LazyProperCost
open scoped ENNReal Pointwise

variable {n m : Nat}

/-- One sequential phase exceeds its ordinary-proposal cutoff with probability bounded by
the ideal warm-start Markov term plus the previous phase's conditioning-amplified TV error. -/
theorem sequentialPhase_timeout_le
    (hn : 2 <= n) {sigmaSq : Nat -> Real} (hsigma : forall j, 0 < sigmaSq j)
    {K : Set (EuclSpace n)} (hKm : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m)
    {cc : Real} (hcc1 : 1 <= cc) (hcc : cc <= 1 + 2 / (n : Real))
    (hsched : sigmaSq (i + 1) = cc * sigmaSq i)
    {phaseOut : Measure (EuclSpace n)} [IsProbabilityMeasure phaseOut]
    {eps : ENNReal} (htv : TVLe phaseOut (coolLaw m sigmaSq K i) eps)
    (heps : eps <= ENNReal.ofReal (1 / 4 : Real))
    {q delta sigma R : Real} (hq : 1 < q) (hdelta : 0 < delta) (hsigmaR : 0 < sigma)
    (hdeltan : delta <= 1 / (2 * (n : Real)))
    (hdeltaq : delta <= sigma / (max 8 (2 * q) * Real.sqrt n))
    (hnext : sigmaSq (i + 1) = sigma ^ 2)
    (hR : 0 <= R) (hRsigma : R <= q * sigma * Real.sqrt n)
    (hKR : forall x, x ∈ K -> ‖x‖ <= R)
    (t : Nat) {L : ENNReal} (hL0 : L ≠ 0) (hLtop : L ≠ ⊤) :
    lazyProperExecution K hKm delta (sigma ^ 2)
        (Arlib.condOn phaseOut ((1 - 1 / (2 * (n : Real))) • K))
        {omega | L <= Ttc.SequentialCost.totalCost t omega} <=
      (10 * ((t : ENNReal) * ENNReal.ofReal (2 * Real.exp 1)) / 6) / L + 8 * eps := by
  have hn1 : 1 <= n := by omega
  have hc0 : (0 : Real) < 1 - 1 / (2 * (n : Real)) := by
    have hnR : (1 : Real) <= (n : Real) := by exact_mod_cast hn1
    have : 1 / (2 * (n : Real)) <= 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  let A : Set (EuclSpace n) := (1 - 1 / (2 * (n : Real))) • K
  have hAm : MeasurableSet A :=
    Arlib.MarkovChains.measurableSet_smul_set hKm hc0.ne'
  letI : IsProbabilityMeasure (coolLaw m sigmaSq K i) :=
    coolLaw_isProbabilityMeasure hsigma hball hfin i
  have hhalf : ENNReal.ofReal (1 / 2 : Real) <= coolLaw m sigmaSq K i A := by
    exact half_le_coolLaw_smul_set hn1 hsigma hKm hKc hball hfin
      (Nat.lt_of_succ_lt hi)
  have hquarter : ENNReal.ofReal (1 / 4 : Real) <= phaseOut A :=
    Arlib.quarter_le_of_tvLe htv hAm hhalf heps
  have hquarterPos : (0 : ENNReal) < ENNReal.ofReal (1 / 4 : Real) := by norm_num
  letI : IsProbabilityMeasure (Arlib.condOn phaseOut A) :=
    Arlib.isProbabilityMeasure_condOn _ (lt_of_lt_of_le hquarterPos hquarter).ne'
      (measure_ne_top _ _)
  have hhalfPos : (0 : ENNReal) < ENNReal.ofReal (1 / 2 : Real) := by norm_num
  letI : IsProbabilityMeasure (exactSequentialStart (m := m) sigmaSq K i) :=
    Arlib.isProbabilityMeasure_condOn _ (lt_of_lt_of_le hhalfPos hhalf).ne'
      (measure_ne_top _ _)
  have hstartTV : TVLe (Arlib.condOn phaseOut A)
      (exactSequentialStart (m := m) sigmaSq K i) (8 * eps) := by
    simpa only [A] using tvLe_condOn_exactSequentialStart hn1 hsigma hKm hKc hball hfin
      (Nat.lt_of_succ_lt hi) htv
  have hwarm : IsWarm (ENNReal.ofReal (2 * Real.exp 1))
      (exactSequentialStart (m := m) sigmaSq K i)
      (ellGaussianProb K delta (sigma ^ 2)) := by
    have h := isWarm_exactSequentialStart hn1 hsigma hKm hKc hball hfin hi hcc1 hcc
      hsched hdelta hdeltan
    rwa [hnext] at h
  exact Ttc.AdjustableLazyProperCost.lazyProper_timeout_le_of_tvLe_adjustable
    hn hq hKm hKc hball hdelta hsigmaR hdeltan hdeltaq hR hRsigma hKR
    hstartTV hwarm t hL0 hLtop

#print axioms sequentialPhase_timeout_le

end Ttc.CVSequential
