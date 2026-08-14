/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.FiniteContinuingRetryGeneralDecomposition
import Ttc.Volume.CVDirectSequentialWarm
import Ttc.Volume.AmbientGaussianRejection

/-! # An unbounded state-updating continuing-retry phase

The state transition is the existing absorbing `retryStep`; this file runs it on an
infinite Ionescu--Tulcea path and stops at the first accepted state.  No fallback mass is
inserted into the returned law.  Termination follows from a supplied geometric contraction
of the actual survival marginals.
-/

namespace Ttc.UnboundedContinuingRetry

open MeasureTheory ProbabilityTheory Set
open Arlib Arlib.Probability
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryGeneralDecomposition
open Ttc.CV Ttc.CVSequentialPhaseSampler
open scoped ENNReal Classical BigOperators

variable {E C F : Type*} [MeasurableSpace E] [MeasurableSpace C] [MeasurableSpace F]

/-- The genuine infinite state-updating retry trajectory. -/
noncomputable def pathMeasure
    (candidate : Nat → Kernel E C) [∀ j : Nat, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (x : E) (fallback : F) : Measure (Nat → RetryState E F) :=
  inhomogeneousPathMeasure
    (schedule candidate A hA next hnext out hout roundCost hcost)
    (initialLaw x fallback)

instance pathMeasure.isProbabilityMeasure
    (candidate : Nat → Kernel E C) [∀ j : Nat, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (x : E) (fallback : F) :
    IsProbabilityMeasure
      (pathMeasure candidate A hA next hnext out hout roundCost hcost x fallback) := by
  unfold pathMeasure
  infer_instance

/-- Coordinate `j` of the infinite path has exactly the finite retry marginal at `j`. -/
theorem map_eval_pathMeasure_eq_marginal
    (candidate : Nat → Kernel E C) [∀ j : Nat, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (x : E) (fallback : F) (j : Nat) :
    (pathMeasure candidate A hA next hnext out hout roundCost hcost x fallback).map
        (fun omega ↦ omega j) =
      marginal candidate A hA next hnext out hout roundCost hcost x fallback j := by
  induction j with
  | zero =>
      simpa only [pathMeasure, marginal, Arlib.adaptiveMarginal] using
        Ttc.CVDirectSequentialWarm.map_eval_inhomogeneousPathMeasure_zero
          (schedule candidate A hA next hnext out hout roundCost hcost)
          (initialLaw x fallback)
  | succ j ih =>
      rw [show j + 1 = Nat.succ j by omega]
      rw [show Nat.succ j = j + 1 by omega,
        pathMeasure,
        Ttc.CVDirectSequentialWarm.map_eval_inhomogeneousPathMeasure_succ]
      change sampleFromKernel
          (schedule candidate A hA next hnext out hout roundCost hcost j)
          ((pathMeasure candidate A hA next hnext out hout roundCost hcost x fallback).map
            (fun omega ↦ omega j)) = _
      rw [ih]
      rfl

/-- The state selected at the first accepted coordinate.  Its value on the null
nontermination event is irrelevant. -/
noncomputable def terminalState (omega : Nat → RetryState E F) : RetryState E F :=
  firstAcceptedDraw (acceptedStates : Set (RetryState E F)) omega

theorem measurable_terminalState :
    Measurable (terminalState : (Nat → RetryState E F) → RetryState E F) :=
  measurable_firstAcceptedDraw measurableSet_acceptedStates

noncomputable def terminalOutput (omega : Nat → RetryState E F) : F :=
  output (terminalState omega)

theorem measurable_terminalOutput :
    Measurable (terminalOutput : (Nat → RetryState E F) → F) :=
  measurable_output.comp measurable_terminalState

noncomputable def terminalCost (omega : Nat → RetryState E F) : ENNReal :=
  accumulatedCost (terminalState omega)

theorem measurable_terminalCost :
    Measurable (terminalCost : (Nat → RetryState E F) → ENNReal) :=
  measurable_accumulatedCost.comp measurable_terminalState

/-- Geometric survival contraction for the finite marginals. -/
theorem survival_le_pow
    (candidate : Nat → Kernel E C) [∀ j : Nat, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (x : E) (fallback : F) {r : ENNReal}
    (hcontract : ∀ j,
      survival candidate A hA next hnext out hout roundCost hcost x fallback (j + 1) ≤
        r * survival candidate A hA next hnext out hout roundCost hcost x fallback j) :
    ∀ j, survival candidate A hA next hnext out hout roundCost hcost x fallback j ≤ r ^ j := by
  intro j
  induction j with
  | zero =>
      simpa only [survival, pow_zero] using
        (prob_le_one (μ := marginal candidate A hA next hnext out hout roundCost hcost
          x fallback 0) (s := Ttc.FiniteContinuingRetry.runningStates))
  | succ j ih =>
      calc
        survival candidate A hA next hnext out hout roundCost hcost x fallback (j + 1) ≤
            r * survival candidate A hA next hnext out hout roundCost hcost x fallback j :=
          hcontract j
        _ ≤ r * r ^ j := mul_le_mul_left' ih r
        _ = r ^ (j + 1) := by rw [pow_succ']

/-- A pointwise rejection ceiling implies contraction of the actual survival marginal.
This is the direct acceptance-schedule interface: no normalized surviving law is needed. -/
theorem survival_succ_le_mul_of_pointwise_reject
    (candidate : Nat → Kernel E C) [∀ j : Nat, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (x : E) (fallback : F) {r : ENNReal}
    (hreject : ∀ j (s : RetryState E F),
      accepted s = false → candidate j (current s) Aᶜ ≤ r) (j : Nat) :
    survival candidate A hA next hnext out hout roundCost hcost x fallback (j + 1) ≤
      r * survival candidate A hA next hnext out hout roundCost hcost x fallback j := by
  let rho := marginal candidate A hA next hnext out hout roundCost hcost x fallback j
  unfold survival marginal
  rw [Arlib.adaptiveMarginal, Measure.bind_apply
    Ttc.FiniteContinuingRetry.measurableSet_runningStates
    (schedule candidate A hA next hnext out hout roundCost hcost j).aemeasurable]
  have hpoint : ∀ s : RetryState E F,
      schedule candidate A hA next hnext out hout roundCost hcost j s
          Ttc.FiniteContinuingRetry.runningStates ≤
        Ttc.FiniteContinuingRetry.runningStates.indicator (fun _ ↦ r) s := by
    intro s
    rw [schedule, retryStep_runningStates]
    by_cases hs : accepted s = true
    · simp [hs, Ttc.FiniteContinuingRetry.runningStates, acceptedStates]
    · have hsf : accepted s = false := Bool.eq_false_of_not_eq_true hs
      rw [if_neg hs]
      rw [Set.indicator_of_mem]
      · exact hreject j s hsf
      · simpa [Ttc.FiniteContinuingRetry.runningStates, acceptedStates, hsf]
  calc
    (∫⁻ s, schedule candidate A hA next hnext out hout roundCost hcost j s
      Ttc.FiniteContinuingRetry.runningStates ∂rho) ≤
        ∫⁻ s, Ttc.FiniteContinuingRetry.runningStates.indicator (fun _ ↦ r) s ∂rho :=
      lintegral_mono hpoint
    _ = ∫⁻ _s in Ttc.FiniteContinuingRetry.runningStates, r ∂rho := by
      rw [lintegral_indicator Ttc.FiniteContinuingRetry.measurableSet_runningStates]
    _ = r * rho Ttc.FiniteContinuingRetry.runningStates := by simp

/-- A strict geometric contraction makes the infinite state-updating retry terminate almost
surely.  This proof uses only actual finite marginals, not iid regeneration. -/
theorem measure_neverAccepts_eq_zero
    (candidate : Nat → Kernel E C) [∀ j : Nat, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (x : E) (fallback : F) {r : ENNReal} (hr : r < 1)
    (hcontract : ∀ j,
      survival candidate A hA next hnext out hout roundCost hcost x fallback (j + 1) ≤
        r * survival candidate A hA next hnext out hout roundCost hcost x fallback j) :
    pathMeasure candidate A hA next hnext out hout roundCost hcost x fallback
      (neverAccepts (acceptedStates : Set (RetryState E F))) = 0 := by
  let mu := pathMeasure candidate A hA next hnext out hout roundCost hcost x fallback
  have hpow := survival_le_pow candidate A hA next hnext out hout roundCost hcost
    x fallback hcontract
  have hle : ∀ j : Nat,
      mu (neverAccepts (acceptedStates : Set (RetryState E F))) ≤ r ^ j := by
    intro j
    calc
      mu (neverAccepts (acceptedStates : Set (RetryState E F))) ≤
          mu ((fun omega : Nat → RetryState E F ↦ omega j) ⁻¹'
            Ttc.FiniteContinuingRetry.runningStates) := by
        apply measure_mono
        intro omega homega
        exact homega j
      _ = survival candidate A hA next hnext out hout roundCost hcost x fallback j := by
        rw [← Measure.map_apply (measurable_pi_apply j)
          Ttc.FiniteContinuingRetry.measurableSet_runningStates,
          map_eval_pathMeasure_eq_marginal]
        rfl
      _ ≤ r ^ j := hpow j
  have hzero : mu (neverAccepts (acceptedStates : Set (RetryState E F))) ≤ 0 :=
    ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr) hle
  exact nonpos_iff_eq_zero.mp hzero

/-- Pointwise rejection bounded by `r<1` is therefore sufficient for almost-sure
termination of the continuing retry. -/
theorem measure_neverAccepts_eq_zero_of_pointwise_reject
    (candidate : Nat → Kernel E C) [∀ j : Nat, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (x : E) (fallback : F) {r : ENNReal} (hr : r < 1)
    (hreject : ∀ j (s : RetryState E F),
      accepted s = false → candidate j (current s) Aᶜ ≤ r) :
    pathMeasure candidate A hA next hnext out hout roundCost hcost x fallback
      (neverAccepts (acceptedStates : Set (RetryState E F))) = 0 :=
  measure_neverAccepts_eq_zero candidate A hA next hnext out hout roundCost hcost x fallback
    hr (survival_succ_le_mul_of_pointwise_reject candidate A hA next hnext out hout
      roundCost hcost x fallback hreject)

/-- Exact first-hit output law.  The supplied premise is the ordinary first-hit
factorization: retry `j` contributes weight `w j` times the same target law.  Almost-sure
termination removes the only otherwise possible fallback atom. -/
theorem map_terminalOutput_eq_of_firstHit
    (mu : Measure (Nat → RetryState E F)) [IsProbabilityMeasure mu]
    (target : Measure F) (w : Nat → ENNReal)
    (hterm : mu (neverAccepts (acceptedStates : Set (RetryState E F))) = 0)
    (hfirst : ∀ j (T : Set F), MeasurableSet T →
      mu (firstAcceptsIn (acceptedStates : Set (RetryState E F))
        (output ⁻¹' T) j) = w j * target T)
    (hweights : ∑' j, w j = 1) :
    Measure.map terminalOutput mu = target := by
  ext T hT
  rw [Measure.map_apply measurable_terminalOutput hT]
  rw [← measure_sdiff_null (s := terminalOutput ⁻¹' T) hterm]
  have hset : terminalOutput ⁻¹' T \
      neverAccepts (acceptedStates : Set (RetryState E F)) =
      ⋃ j, firstAcceptsIn (acceptedStates : Set (RetryState E F))
        (output ⁻¹' T) j := by
    rw [iUnion_firstAcceptsIn]
    ext omega
    simp [terminalOutput, terminalState, and_comm]
  rw [hset, measure_iUnion
    (pairwise_disjoint_firstAcceptsIn
      (acceptedStates : Set (RetryState E F)) (output ⁻¹' T))
    (measurableSet_firstAcceptsIn measurableSet_acceptedStates
      (hT.preimage measurable_output))]
  simp_rw [hfirst _ T hT]
  rw [ENNReal.tsum_mul_right, hweights, one_mul]

/-- Number of candidate transitions actually attempted.  Unlike `roundCount`, this does
not charge the deterministic initial state as a retry.  Nontermination gives `⊤`. -/
noncomputable def transitionCount (omega : Nat → RetryState E F) : ENNReal :=
  ∑' j : Nat,
    (survives (acceptedStates : Set (RetryState E F)) (j + 1)).indicator
      (fun _ ↦ (1 : ENNReal)) omega

theorem measurable_transitionCount :
    Measurable (transitionCount : (Nat → RetryState E F) → ENNReal) := by
  unfold transitionCount
  exact Measurable.tsum fun j ↦ measurable_const.indicator
    (measurableSet_survives measurableSet_acceptedStates (j + 1))

/-- Expected retry count is geometric under the actual marginal contraction. -/
theorem lintegral_transitionCount_le
    (candidate : Nat → Kernel E C) [∀ j : Nat, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (x : E) (fallback : F) {r : ENNReal}
    (hcontract : ∀ j,
      survival candidate A hA next hnext out hout roundCost hcost x fallback (j + 1) ≤
        r * survival candidate A hA next hnext out hout roundCost hcost x fallback j) :
    (∫⁻ omega, transitionCount omega
      ∂pathMeasure candidate A hA next hnext out hout roundCost hcost x fallback) ≤
      (1 - r)⁻¹ := by
  let mu := pathMeasure candidate A hA next hnext out hout roundCost hcost x fallback
  have hpow := survival_le_pow candidate A hA next hnext out hout roundCost hcost
    x fallback hcontract
  have hsurv : ∀ j : Nat,
      mu (survives (acceptedStates : Set (RetryState E F)) (j + 1)) ≤ r ^ j := by
    intro j
    calc
      mu (survives (acceptedStates : Set (RetryState E F)) (j + 1)) ≤
          mu ((fun omega : Nat → RetryState E F ↦ omega j) ⁻¹'
            Ttc.FiniteContinuingRetry.runningStates) := by
        apply measure_mono
        intro omega homega
        exact homega j (by omega)
      _ = survival candidate A hA next hnext out hout roundCost hcost x fallback j := by
        rw [← Measure.map_apply (measurable_pi_apply j)
          Ttc.FiniteContinuingRetry.measurableSet_runningStates,
          map_eval_pathMeasure_eq_marginal]
        rfl
      _ ≤ r ^ j := hpow j
  calc
    (∫⁻ omega, transitionCount omega ∂mu) =
        ∑' j : Nat, ∫⁻ omega,
          (survives (acceptedStates : Set (RetryState E F)) (j + 1)).indicator
            (fun _ ↦ (1 : ENNReal)) omega ∂mu := by
      unfold transitionCount
      exact lintegral_tsum fun j ↦
        (measurable_const.indicator
          (measurableSet_survives measurableSet_acceptedStates (j + 1))).aemeasurable
    _ = ∑' j : Nat,
        mu (survives (acceptedStates : Set (RetryState E F)) (j + 1)) := by
      exact tsum_congr fun j ↦ lintegral_indicator_one
        (measurableSet_survives measurableSet_acceptedStates (j + 1))
    _ ≤ ∑' j : Nat, r ^ j := ENNReal.tsum_le_tsum hsurv
    _ = (1 - r)⁻¹ := ENNReal.tsum_geometric r

/-- Expected deterministic per-retry cost envelope. -/
theorem lintegral_costEnvelope_le
    (candidate : Nat → Kernel E C) [∀ j : Nat, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (x : E) (fallback : F) (B : ENNReal) {r : ENNReal}
    (hcontract : ∀ j,
      survival candidate A hA next hnext out hout roundCost hcost x fallback (j + 1) ≤
        r * survival candidate A hA next hnext out hout roundCost hcost x fallback j) :
    (∫⁻ omega, B * transitionCount omega
      ∂pathMeasure candidate A hA next hnext out hout roundCost hcost x fallback) ≤
      B * (1 - r)⁻¹ := by
  rw [lintegral_const_mul B measurable_transitionCount]
  exact mul_le_mul_left' (lintegral_transitionCount_le candidate A hA next hnext out hout
    roundCost hcost x fallback hcontract) B

end Ttc.UnboundedContinuingRetry

#print axioms Ttc.UnboundedContinuingRetry.map_eval_pathMeasure_eq_marginal
#print axioms Ttc.UnboundedContinuingRetry.measure_neverAccepts_eq_zero
#print axioms Ttc.UnboundedContinuingRetry.map_terminalOutput_eq_of_firstHit
#print axioms Ttc.UnboundedContinuingRetry.measure_neverAccepts_eq_zero_of_pointwise_reject
#print axioms Ttc.UnboundedContinuingRetry.lintegral_transitionCount_le
#print axioms Ttc.UnboundedContinuingRetry.lintegral_costEnvelope_le
