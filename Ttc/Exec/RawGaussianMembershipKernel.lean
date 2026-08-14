/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.MembershipQueryTrace
import Mathlib.Probability.Distributions.Bernoulli

/-!
# Raw Gaussian proposal kernel retaining its membership query

This file exposes the random choices hidden by `properProposalGaussianAux`: the uniformly
sampled proposal point and the Gaussian Metropolis Bernoulli choice.  Its output also records
the body-membership answer and final state.  Thus the one-query trace from
`MembershipQueryTrace` is recoverable without inventing a ghost proposal point.
-/

namespace Ttc.RawGaussianMembership

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains
open Ttc.MembershipQuery
open scoped ENNReal Classical

variable {n : Nat}

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- Uniform proposal in the moving ball.  The positivity proof is retained as an argument
so the kernel is globally Markov rather than merely conditionally Markov. -/
noncomputable def ballProposalKernel (delta : Real) (hdelta : 0 < delta) :
    Kernel (State n) (State n) where
  toFun x := Arlib.uniformOn volume (ball x delta)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    have happ : ∀ x : State n,
        Arlib.uniformOn volume (ball x delta) A =
          volume (A ∩ ball x delta) / volume (ball x delta) :=
      fun x => Arlib.uniformOn_apply volume measurableSet_ball hA
    simp_rw [happ]
    simpa only [volume_ball_eq] using
      (measurable_volume_inter_ball hA delta).div_const
        (volume (ball (0 : State n) delta))

instance (delta : Real) (hdelta : 0 < delta) :
    IsMarkovKernel (ballProposalKernel (n := n) delta hdelta) := by
  refine ⟨fun x => ?_⟩
  exact Arlib.isProbabilityMeasure_uniformOn_ball volume x hdelta

/-- Bernoulli kernel for the Gaussian Metropolis filter, conditional on `(current,proposal)`.
`true` has mass `metropolisAccept s current proposal`. -/
noncomputable def metropolisChoiceKernel (s : Real) :
    Kernel (State n × State n) Bool where
  toFun p := metropolisAccept s p.1 p.2 • Measure.dirac true +
    (1 - metropolisAccept s p.1 p.2) • Measure.dirac false
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    simp_rw [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hA]
    exact ((continuous_metropolisAccept s).measurable.mul
      (measurable_one.indicator hA |>.comp measurable_const)).add
      ((measurable_const.sub (continuous_metropolisAccept s).measurable).mul
        (measurable_one.indicator hA |>.comp measurable_const))

instance (s : Real) : IsMarkovKernel (metropolisChoiceKernel (n := n) s) := by
  refine ⟨fun p => ⟨?_⟩⟩
  change (metropolisAccept s p.1 p.2 • Measure.dirac true +
    (1 - metropolisAccept s p.1 p.2) • Measure.dirac false) univ = 1
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    smul_eq_mul, smul_eq_mul, Measure.dirac_apply' _ MeasurableSet.univ,
    Measure.dirac_apply' _ MeasurableSet.univ]
  simp only [mem_univ, indicator_of_mem, Pi.one_apply, mul_one]
  exact add_tsub_cancel_of_le (metropolisAccept_le_one s p.1 p.2)

theorem metropolisChoiceKernel_apply (s : Real) (p : State n × State n)
    {A : Set Bool} (hA : MeasurableSet A) :
    metropolisChoiceKernel s p A =
      metropolisAccept s p.1 p.2 * A.indicator 1 true +
        (1 - metropolisAccept s p.1 p.2) * A.indicator 1 false := by
  change (metropolisAccept s p.1 p.2 • Measure.dirac true +
    (1 - metropolisAccept s p.1 p.2) • Measure.dirac false) A = _
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    smul_eq_mul, smul_eq_mul, Measure.dirac_apply' _ hA,
    Measure.dirac_apply' _ hA]

/-- Joint law of `(current, proposal)` from one moving-ball proposal. -/
noncomputable def currentProposalKernel (delta : Real) (hdelta : 0 < delta) :
    Kernel (State n) (State n × State n) :=
  Kernel.compProd Kernel.id
    (Kernel.prodMkLeft (State n) (ballProposalKernel delta hdelta))

instance (delta : Real) (hdelta : 0 < delta) :
    IsMarkovKernel (currentProposalKernel (n := n) delta hdelta) := by
  unfold currentProposalKernel
  infer_instance

theorem currentProposalKernel_apply (delta : Real) (hdelta : 0 < delta) (x : State n) :
    currentProposalKernel delta hdelta x =
      (ballProposalKernel delta hdelta x).map (fun y => (x, y)) := by
  ext A hA
  rw [currentProposalKernel, Kernel.compProd_apply hA, Kernel.id_apply, lintegral_dirac']
  · rw [Kernel.prodMkLeft_apply, Measure.map_apply (by fun_prop) hA]
  · exact Kernel.measurable_kernel_prodMk_left' hA x

/-- Joint law `((current,proposal), metropolisCoin)`. -/
noncomputable def rawChoicesKernel (delta s : Real) (hdelta : 0 < delta) :
    Kernel (State n) ((State n × State n) × Bool) :=
  Kernel.compProd (currentProposalKernel delta hdelta)
    (Kernel.comap (metropolisChoiceKernel s) Prod.snd measurable_snd)

instance (delta s : Real) (hdelta : 0 < delta) :
    IsMarkovKernel (rawChoicesKernel (n := n) delta s hdelta) := by
  unfold rawChoicesKernel
  infer_instance

/-- Raw observable record `(proposal, properMark, metropolisCoin, nextState)`.  Product types
are used so their measurable-space instances are standard. -/
abbrev RawRound (n : Nat) := State n × Bool × Bool × State n

/-- Deterministic control flow attached to the raw random choices. -/
def rawRoundOfChoices {K : Set (State n)} (oracle : MembershipOracle K)
    (q : (State n × State n) × Bool) : RawRound n :=
  let current := q.1.1
  let proposal := q.1.2
  let proper := oracle.answer proposal
  (proposal, proper, q.2,
    if proper && q.2 then proposal else current)

theorem measurable_rawRoundOfChoices {K : Set (State n)} (oracle : MembershipOracle K) :
    Measurable (rawRoundOfChoices oracle) := by
  unfold rawRoundOfChoices
  have hcurrent : Measurable (fun q : (State n × State n) × Bool => q.1.1) := by fun_prop
  have hproposal : Measurable (fun q : (State n × State n) × Bool => q.1.2) := by fun_prop
  have hproper : Measurable
      (fun q : (State n × State n) × Bool => oracle.answer q.1.2) :=
    oracle.measurable_answer.comp hproposal
  have hcoin : Measurable (fun q : (State n × State n) × Bool => q.2) := measurable_snd
  have hbothSet : MeasurableSet
      {q : (State n × State n) × Bool | (oracle.answer q.1.2 && q.2) = true} := by
    have heq : {q : (State n × State n) × Bool |
        (oracle.answer q.1.2 && q.2) = true} =
        {q | oracle.answer q.1.2 = true} ∩ {q | q.2 = true} := by
      ext q
      simp only [mem_setOf_eq, mem_inter_iff, Bool.and_eq_true]
    rw [heq]
    exact (measurableSet_eq_fun hproper measurable_const).inter
      (measurableSet_eq_fun hcoin measurable_const)
  have hnext : Measurable (fun q : (State n × State n) × Bool =>
      if oracle.answer q.1.2 && q.2 then q.1.2 else q.1.1) := by
    exact Measurable.ite hbothSet hproposal hcurrent
  exact hproposal.prodMk (hproper.prodMk (hcoin.prodMk hnext))

/-- The fully traced raw one-round kernel. -/
noncomputable def rawRoundKernel {K : Set (State n)} (oracle : MembershipOracle K)
    (delta s : Real) (hdelta : 0 < delta) : Kernel (State n) (RawRound n) :=
  Kernel.map (rawChoicesKernel delta s hdelta) (rawRoundOfChoices oracle)

instance {K : Set (State n)} (oracle : MembershipOracle K)
    (delta s : Real) (hdelta : 0 < delta) :
    IsMarkovKernel (rawRoundKernel oracle delta s hdelta) := by
  unfold rawRoundKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_rawRoundOfChoices oracle)

/-- Forget the retained proposal point and Metropolis coin. -/
def rawRoundOutput (r : RawRound n) : Bool × State n := (r.2.1, r.2.2.2)

theorem measurable_rawRoundOutput : Measurable (rawRoundOutput (n := n)) := by
  unfold rawRoundOutput
  fun_prop

/-- Recover the exact membership trace represented by a raw round. -/
def rawRoundTrace (r : RawRound n) : QueryTrace (State n) :=
  [{ point := r.1, response := r.2.1 }]

/-- Every point in the raw probabilistic kernel carries exactly one membership query. -/
@[simp] theorem rawRoundTrace_cost (r : RawRound n) :
    queryCost (rawRoundTrace r) = 1 := rfl

/-- The trace and proper mark agree by construction. -/
@[simp] theorem rawRoundTrace_response (r : RawRound n) :
    (rawRoundTrace r).head?.map QueryEvent.response = some r.2.1 := rfl

/-! ## Exact evaluation and the remaining analytic normalization -/

/-- Exact event formula for the operational raw kernel after forgetting the retained query.
This is the direct program semantics: propose uniformly in the ball, query `K`, and then use
the Metropolis coin only on the positive-query branch. -/
theorem map_rawRoundKernel_output_apply
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (x : State n) {t : Set (Bool × State n)} (ht : MeasurableSet t) :
    Measure.map rawRoundOutput
        (rawRoundKernel (MembershipOracle.ofMeasurableSet K hK) delta s hdelta x) t =
      ∫⁻ y,
        (if y ∈ K then
          metropolisAccept s x y * t.indicator 1 (true, y) +
            (1 - metropolisAccept s x y) * t.indicator 1 (true, x)
         else t.indicator 1 (false, x))
        ∂(Arlib.uniformOn volume (ball x delta)) := by
  classical
  have hraw := measurable_rawRoundOfChoices
    (MembershipOracle.ofMeasurableSet K hK)
  rw [Measure.map_apply measurable_rawRoundOutput ht,
    rawRoundKernel, Kernel.map_apply _ hraw,
    Measure.map_apply hraw (measurable_rawRoundOutput ht),
    rawChoicesKernel, Kernel.compProd_apply
      (hraw (measurable_rawRoundOutput ht))]
  simp_rw [Kernel.comap_apply]
  rw [currentProposalKernel_apply]
  rw [lintegral_map
    (Kernel.measurable_kernel_prodMk_left
      (hraw (measurable_rawRoundOutput ht))) (by fun_prop)]
  have hchoice : ∀ y : State n,
      metropolisChoiceKernel s (x, y)
          (Prod.mk (x, y) ⁻¹'
            rawRoundOfChoices (MembershipOracle.ofMeasurableSet K hK) ⁻¹'
              rawRoundOutput ⁻¹' t) =
        metropolisAccept s x y *
            (Prod.mk (x, y) ⁻¹'
              rawRoundOfChoices (MembershipOracle.ofMeasurableSet K hK) ⁻¹'
                rawRoundOutput ⁻¹' t).indicator 1 true +
          (1 - metropolisAccept s x y) *
            (Prod.mk (x, y) ⁻¹'
              rawRoundOfChoices (MembershipOracle.ofMeasurableSet K hK) ⁻¹'
                rawRoundOutput ⁻¹' t).indicator 1 false := by
    intro y
    apply metropolisChoiceKernel_apply
    exact (hraw (measurable_rawRoundOutput ht)).preimage (by fun_prop)
  simp_rw [hchoice]
  have hind : ∀ y : State n,
      metropolisAccept s x y *
            (Prod.mk (x, y) ⁻¹'
              rawRoundOfChoices (MembershipOracle.ofMeasurableSet K hK) ⁻¹'
                rawRoundOutput ⁻¹' t).indicator 1 true +
          (1 - metropolisAccept s x y) *
            (Prod.mk (x, y) ⁻¹'
              rawRoundOfChoices (MembershipOracle.ofMeasurableSet K hK) ⁻¹'
                rawRoundOutput ⁻¹' t).indicator 1 false =
        if y ∈ K then
          metropolisAccept s x y * t.indicator 1 (true, y) +
            (1 - metropolisAccept s x y) * t.indicator 1 (true, x)
        else t.indicator 1 (false, x) := by
    intro y
    by_cases hy : y ∈ K
    · have hans : (MembershipOracle.ofMeasurableSet K hK).answer y = true :=
        (MembershipOracle.ofMeasurableSet_answer K hK y).2 hy
      by_cases hty : (true, y) ∈ t <;> by_cases htx : (true, x) ∈ t <;>
        simp [rawRoundOfChoices, rawRoundOutput, hy, hans, hty, htx]
    · have hans : (MembershipOracle.ofMeasurableSet K hK).answer y = false :=
        (MembershipOracle.answer_eq_false_iff
          (MembershipOracle.ofMeasurableSet K hK) y).2 hy
      by_cases htf : (false, x) ∈ t
      · simp [rawRoundOfChoices, rawRoundOutput, hy, hans, htf,
          add_tsub_cancel_of_le (metropolisAccept_le_one s x y)]
      · simp [rawRoundOfChoices, rawRoundOutput, hy, hans, htf]
  simp_rw [hind]
  rfl

/-- The sole remaining bridge obligation, isolated as the explicit normalization identity.
It contains no operational or query-semantics content. -/
def RawNormalizationIdentity {K : Set (State n)} (hK : MeasurableSet K)
    (delta s : Real) : Prop :=
  ∀ (x : State n) (t : Set (Bool × State n)), MeasurableSet t →
    (∫⁻ y,
      (if y ∈ K then
        metropolisAccept s x y * t.indicator 1 (true, y) +
          (1 - metropolisAccept s x y) * t.indicator 1 (true, x)
       else t.indicator 1 (false, x))
      ∂(Arlib.uniformOn volume (ball x delta))) =
      properProposalGaussianAux K hK delta s x t

/-- Once the explicit normalization identity is supplied, the exact measure bridge follows
without any further probabilistic-program reasoning. -/
theorem map_rawRoundKernel_output_of_normalization
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (hnorm : RawNormalizationIdentity hK delta s) (x : State n) :
    Measure.map rawRoundOutput
        (rawRoundKernel (MembershipOracle.ofMeasurableSet K hK) delta s hdelta x) =
      properProposalGaussianAux K hK delta s x := by
  ext t ht
  rw [map_rawRoundKernel_output_apply hK delta s hdelta x ht]
  exact hnorm x t ht

#print axioms rawRoundTrace_cost
#print axioms map_rawRoundKernel_output_apply
#print axioms map_rawRoundKernel_output_of_normalization

end Ttc.RawGaussianMembership
