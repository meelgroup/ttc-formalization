/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.SequentialExecutionKernel
import Ttc.Exec.AdjustableLazyProperProposalCost

/-!
# Adjustable lazy-walk timeout from a TV-close operational start

The ideal start is warm and therefore has a controlled expected number of ordinary
proposals.  The operational start need only be TV-close to it.  Applying the full path
experiment as a heterogeneous kernel and then Markov's inequality gives a finite timeout
with an additive TV penalty.  No invalid `TVLe -> IsWarm` inference occurs.
-/

namespace Ttc.AdjustableLazyProperCost

open MeasureTheory ProbabilityTheory Set
open Arlib Arlib.MarkovChains
open Ttc.LazyProperCost
open scoped ENNReal

variable {n : Nat}

/-- The proposal-count timeout theorem for an actual law close to an ideal warm law. -/
theorem lazyProper_timeout_le_of_tvLe_adjustable
    (hn : 2 <= n) {q : Real} (hq : 1 < q)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : Metric.ball (0 : State n) 1 ⊆ K)
    {delta sigma R : Real} (hdelta : 0 < delta) (hsigma : 0 < sigma)
    (hdeltan : delta <= 1 / (2 * (n : Real)))
    (hdeltaq : delta <= sigma / (max 8 (2 * q) * Real.sqrt n))
    (hR : 0 <= R) (hRsigma : R <= q * sigma * Real.sqrt n)
    (hKR : forall x, x ∈ K -> ‖x‖ <= R)
    {M eps : ENNReal} {actual ideal : Measure (State n)}
    [IsProbabilityMeasure actual] [IsProbabilityMeasure ideal]
    (htv : TVLe actual ideal eps)
    (hwarm : IsWarm M ideal (ellGaussianProb K delta (sigma ^ 2)))
    (t : Nat) {L : ENNReal} (hL0 : L ≠ 0) (hLtop : L ≠ ⊤) :
    lazyProperExecution K hK delta (sigma ^ 2) actual
        {omega | L <= Ttc.SequentialCost.totalCost t omega} <=
      (10 * ((t : ENNReal) * M) / 6) / L + eps := by
  have hcost := six_mul_lintegral_lazyProperTotalCost_le_ten_mul_adjustable
    hn hq hK hKc hball hdelta hsigma hdeltan hdeltaq hR hRsigma hKR hwarm t
  have hmean :
      (∫⁻ omega, Ttc.SequentialCost.totalCost t omega
        ∂lazyProperExecution K hK delta (sigma ^ 2) ideal) <=
        10 * ((t : ENNReal) * M) / 6 := by
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl (by norm_num : (6 : ENNReal) ≠ 0))
      (Or.inl (by norm_num : (6 : ENNReal) ≠ ⊤))).2
    simpa [mul_comm] using hcost
  exact Ttc.SequentialCost.totalCost_timeout_le_of_tvLe
    (Ttc.LazyProperCost.lazyProperSchedule K hK delta (sigma ^ 2))
    htv t hL0 hLtop (by simpa [Ttc.LazyProperCost.lazyProperExecution] using hmean)

#print axioms lazyProper_timeout_le_of_tvLe_adjustable

end Ttc.AdjustableLazyProperCost
