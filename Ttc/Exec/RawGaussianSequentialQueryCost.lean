/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.RawGaussianNormalization
import Ttc.Exec.LazyProperProposalCost

/-!
# Sequential membership cost of raw Gaussian rounds

This is the executable-semantics bridge available without reconstructing the stopped speedy
experiment.  Each active raw Gaussian round retains its queried proposal and has cost exactly
one; the lazy hold branch has cost zero.  Sequential cost is therefore the pointwise sum of
the recorded membership-query indicators.
-/

namespace Ttc.RawGaussianQueryCost

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains
open Ttc.MembershipQuery Ttc.RawGaussianMembership Ttc.LazyProperCost
open scoped ENNReal Classical

variable {n : Nat}

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- Cost and next state extracted from an actually traced raw proposal. -/
def rawQueryCostOutput (r : RawRound n) : ENNReal × State n :=
  (queryCost (rawRoundTrace r), (rawRoundOutput r).2)

theorem measurable_rawQueryCostOutput : Measurable (rawQueryCostOutput (n := n)) := by
  have hcost : Measurable (fun _r : RawRound n => (1 : ENNReal)) := measurable_const
  have heq : rawQueryCostOutput (n := n) =
      fun r => ((1 : ENNReal), (rawRoundOutput r).2) := by
    funext r
    simp [rawQueryCostOutput]
  rw [heq]
  exact hcost.prodMk (measurable_snd.comp measurable_rawRoundOutput)

@[simp] theorem rawQueryCostOutput_fst (r : RawRound n) :
    (rawQueryCostOutput r).1 = 1 := by
  simp [rawQueryCostOutput]

/-- A single active Gaussian round carrying its actual membership-query cost. -/
noncomputable def rawQueryCostedKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta) :
    Kernel (State n) (ENNReal × State n) :=
  Kernel.map
    (rawRoundKernel (MembershipOracle.ofMeasurableSet K hK) delta s hdelta)
    rawQueryCostOutput

instance {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) : IsMarkovKernel (rawQueryCostedKernel hK delta s hdelta) := by
  unfold rawQueryCostedKernel
  exact Kernel.IsMarkovKernel.map _ measurable_rawQueryCostOutput

/-- Forgetting the exact one-query cost gives the ordinary Gaussian Metropolis step. -/
theorem map_snd_rawQueryCostedKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (x : State n) :
    Measure.map Prod.snd (rawQueryCostedKernel hK delta s hdelta x) =
      metropolisGaussian K delta s x := by
  rw [rawQueryCostedKernel, Kernel.map_apply _ measurable_rawQueryCostOutput,
    Measure.map_map measurable_snd measurable_rawQueryCostOutput]
  have hcomp : Prod.snd ∘ rawQueryCostOutput (n := n) =
      Prod.snd ∘ rawRoundOutput := by rfl
  rw [hcomp, ← Measure.map_map measurable_snd measurable_rawRoundOutput,
    map_rawRoundKernel_output hK delta s hdelta x]
  exact map_snd_properProposalGaussianAux_apply hK delta s x

/-- An active raw round has exactly one membership query in expectation (indeed pointwise). -/
theorem lintegral_fst_rawQueryCostedKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (x : State n) :
    ∫⁻ z, z.1 ∂rawQueryCostedKernel hK delta s hdelta x = 1 := by
  rw [rawQueryCostedKernel, Kernel.map_apply _ measurable_rawQueryCostOutput,
    lintegral_map measurable_fst measurable_rawQueryCostOutput]
  simp only [rawQueryCostOutput_fst, lintegral_const, measure_univ, mul_one]

/-- The measurable support condition characterizing a lazy membership-query increment. -/
def zeroOrOneCost : Set (ENNReal × State n) := {z | z.1 = 0 ∨ z.1 = 1}

theorem measurableSet_zeroOrOneCost : MeasurableSet (zeroOrOneCost (n := n)) := by
  exact (measurableSet_eq_fun measurable_fst measurable_const).union
    (measurableSet_eq_fun measurable_fst measurable_const)

theorem rawQueryCostedKernel_zeroOrOne
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (x : State n) :
    rawQueryCostedKernel hK delta s hdelta x zeroOrOneCost = 1 := by
  rw [rawQueryCostedKernel, Kernel.map_apply _ measurable_rawQueryCostOutput,
    Measure.map_apply measurable_rawQueryCostOutput measurableSet_zeroOrOneCost]
  have hpre : rawQueryCostOutput (n := n) ⁻¹' zeroOrOneCost = Set.univ := by
    ext r
    simp [zeroOrOneCost]
  rw [hpre, measure_univ]

/-- Fair lazy mixture: zero-query hold or one actually traced raw proposal. -/
noncomputable def lazyRawQueryCostedKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta) :
    Kernel (State n) (ENNReal × State n) :=
  lazyCostedKernel (rawQueryCostedKernel hK delta s hdelta)

instance {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) : IsMarkovKernel (lazyRawQueryCostedKernel hK delta s hdelta) := by
  unfold lazyRawQueryCostedKernel
  infer_instance

theorem map_snd_lazyRawQueryCostedKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (x : State n) :
    Measure.map Prod.snd (lazyRawQueryCostedKernel hK delta s hdelta x) =
      lazy (metropolisGaussian K delta s) x :=
  map_snd_lazyCostedKernel _ _
    (map_snd_rawQueryCostedKernel hK delta s hdelta) x

theorem lintegral_fst_lazyRawQueryCostedKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (x : State n) :
    ∫⁻ z, z.1 ∂lazyRawQueryCostedKernel hK delta s hdelta x = (2 : ENNReal)⁻¹ := by
  rw [lazyRawQueryCostedKernel, lintegral_fst_lazyCostedKernel,
    lintegral_fst_rawQueryCostedKernel hK delta s hdelta x, mul_one]

theorem lazyRawQueryCostedKernel_zeroOrOne
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (x : State n) :
    lazyRawQueryCostedKernel hK delta s hdelta x zeroOrOneCost = 1 := by
  rw [lazyRawQueryCostedKernel, lazyCostedKernel_apply, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    rawQueryCostedKernel_zeroOrOne hK delta s hdelta x,
    Measure.dirac_apply' _ measurableSet_zeroOrOneCost]
  simp only [zeroOrOneCost, mem_setOf_eq, true_or, Set.indicator_of_mem, Pi.one_apply,
    mul_one]
  exact ENNReal.inv_two_add_inv_two

/-! ## Pointwise relation to the existing proper-proposal waiting cost -/

/-- Extended count of one-query rounds along a marked proposal path.  `proposal k` is the
actual point queried in round `k`; the count remains meaningful on a nonterminating path,
where it may be `∞`. -/
noncomputable def markedPathMembershipQueryCost
    {K : Set (State n)} (oracle : MembershipOracle K) (proposal : Nat → State n)
    (p : State n × LiftedGaussianPath n) : ENNReal :=
  ∑' k : Nat,
    {q : State n × LiftedGaussianPath n |
      ∀ i ≤ k, q.2 i = (false, q.1)}.indicator
      (fun _q => (queryCost (query oracle (proposal k)) : ENNReal)) p

/-- Since every raw proposal performs exactly one membership query, the extended query count
is pointwise the repository's existing proposal-wait cost, including the infinite case. -/
theorem markedPathMembershipQueryCost_eq_waitCost
    {K : Set (State n)} (oracle : MembershipOracle K) (proposal : Nat → State n)
    (p : State n × LiftedGaussianPath n) :
    markedPathMembershipQueryCost oracle proposal p = properProposalWaitCost p := by
  unfold markedPathMembershipQueryCost properProposalWaitCost
  apply tsum_congr
  intro k
  simp only [query_cost, Nat.cast_one]
  rfl

/-- Marked path obtained from the observable outputs of a raw-round path. -/
def rawMarkedPath (x : State n) (omega : Nat → RawRound n) : LiftedGaussianPath n
  | 0 => (false, x)
  | k + 1 => rawRoundOutput (omega (k + 1))

/-- The actual queried point in raw proposal transition `k+1`. -/
def rawProposalPoint (omega : Nat → RawRound n) (k : Nat) : State n :=
  (omega (k + 1)).1

/-- Extended membership-query count of a raw rejection path. -/
noncomputable def rawRejectionMembershipQueryCost
    {K : Set (State n)} (oracle : MembershipOracle K) (x : State n)
    (omega : Nat → RawRound n) : ENNReal :=
  markedPathMembershipQueryCost oracle (rawProposalPoint omega)
    (x, rawMarkedPath x omega)

/-- Pointwise identification with the existing wait-cost functional after mapping the raw
path to its proper marks and states. -/
theorem rawRejectionMembershipQueryCost_eq_waitCost
    {K : Set (State n)} (oracle : MembershipOracle K) (x : State n)
    (omega : Nat → RawRound n) :
    rawRejectionMembershipQueryCost oracle x omega =
      properProposalWaitCost (x, rawMarkedPath x omega) :=
  markedPathMembershipQueryCost_eq_waitCost oracle (rawProposalPoint omega)
    (x, rawMarkedPath x omega)

noncomputable def lazyRawQuerySchedule
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta) :
    Nat → Kernel (State n) (ENNReal × State n) :=
  fun _ => lazyRawQueryCostedKernel hK delta s hdelta

instance {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) (i : Nat) :
    IsMarkovKernel (lazyRawQuerySchedule hK delta s hdelta i) := by
  unfold lazyRawQuerySchedule
  infer_instance

noncomputable def lazyRawQueryExecution
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (mu : Measure (State n)) : Measure (Nat → ENNReal × State n) :=
  Ttc.SequentialCost.execution (lazyRawQuerySchedule hK delta s hdelta) mu

instance {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) (mu : Measure (State n)) [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (lazyRawQueryExecution hK delta s hdelta mu) := by
  unfold lazyRawQueryExecution
  infer_instance

theorem map_lazyRawQueryExecution_output
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (mu : Measure (State n)) [IsProbabilityMeasure mu] (t : Nat) :
    Measure.map (fun omega => (omega t).2)
        (lazyRawQueryExecution hK delta s hdelta mu) =
      iterate (lazy (metropolisGaussian K delta s)) mu t := by
  induction t with
  | zero =>
      exact Ttc.SequentialCost.map_execution_output_zero
        (lazyRawQuerySchedule hK delta s hdelta) mu
  | succ t ih =>
      change Measure.map (fun omega => (omega (t + 1)).2)
          (Ttc.SequentialCost.execution (lazyRawQuerySchedule hK delta s hdelta) mu) = _
      rw [Ttc.SequentialCost.map_execution_output_succ
          (lazyRawQuerySchedule hK delta s hdelta)
          (fun _ => lazy (metropolisGaussian K delta s))
          (fun _i x => map_snd_lazyRawQueryCostedKernel hK delta s hdelta x)]
      rw [show Measure.map (fun omega => (omega t).2)
          (Ttc.SequentialCost.execution (lazyRawQuerySchedule hK delta s hdelta) mu) =
            iterate (lazy (metropolisGaussian K delta s)) mu t by
        simpa only [lazyRawQueryExecution] using ih]
      rfl

theorem lintegral_lazyRawQueryTotalCost
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (mu : Measure (State n)) [IsProbabilityMeasure mu] (t : Nat) :
    ∫⁻ omega, Ttc.SequentialCost.totalCost t omega
        ∂lazyRawQueryExecution hK delta s hdelta mu =
      (t : ENNReal) * (2 : ENNReal)⁻¹ := by
  rw [lazyRawQueryExecution,
    Ttc.SequentialCost.lintegral_totalCost_eq_sum_stateMeans]
  simp_rw [Ttc.SequentialCost.stepMean, lazyRawQuerySchedule,
    lintegral_fst_lazyRawQueryCostedKernel hK delta s hdelta]
  simp_rw [lintegral_const]
  calc
    ∑ i ∈ Finset.range t, (2 : ENNReal)⁻¹ *
        Measure.map (fun omega => (omega i).2)
          (Ttc.SequentialCost.execution
            (lazyRawQuerySchedule hK delta s hdelta) mu) Set.univ
      = ∑ _i ∈ Finset.range t, (2 : ENNReal)⁻¹ := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [show Measure.map (fun omega => (omega i).2)
              (Ttc.SequentialCost.execution
                (lazyRawQuerySchedule hK delta s hdelta) mu) =
                iterate (lazy (metropolisGaussian K delta s)) mu i by
              simpa only [lazyRawQueryExecution] using
                map_lazyRawQueryExecution_output hK delta s hdelta mu i,
            measure_univ, mul_one]
    _ = (t : ENNReal) * (2 : ENNReal)⁻¹ := by simp

/-- The number of active raw rounds in a finite sequential execution. -/
noncomputable def recordedMembershipQueries
    (t : Nat) (omega : Nat → ENNReal × State n) : Nat :=
  ∑ i ∈ Finset.range t, if (omega (i + 1)).1 = 1 then 1 else 0

/-- Whenever every lazy increment is its constructed value `0` or `1`, sequential cost is
exactly the natural-number count of active one-query raw rounds. -/
theorem totalCost_eq_recordedMembershipQueries
    (t : Nat) (omega : Nat → ENNReal × State n)
    (h01 : ∀ i < t, (omega (i + 1)).1 = 0 ∨ (omega (i + 1)).1 = 1) :
    Ttc.SequentialCost.totalCost t omega =
      (recordedMembershipQueries t omega : ENNReal) := by
  rw [Ttc.SequentialCost.totalCost, recordedMembershipQueries,
    Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rcases h01 i (Finset.mem_range.1 hi) with hzero | hone
  · simp [hzero]
  · simp [hone]

#print axioms map_snd_rawQueryCostedKernel
#print axioms lintegral_fst_rawQueryCostedKernel
#print axioms map_snd_lazyRawQueryCostedKernel
#print axioms markedPathMembershipQueryCost_eq_waitCost
#print axioms rawRejectionMembershipQueryCost_eq_waitCost
#print axioms map_lazyRawQueryExecution_output
#print axioms lintegral_lazyRawQueryTotalCost
#print axioms totalCost_eq_recordedMembershipQueries

end Ttc.RawGaussianQueryCost
