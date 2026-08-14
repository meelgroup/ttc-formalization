/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Exec.SequentialCostedKernel
import Ttc.Exec.KV97RoundedEndpointBridge
import Ttc.Sampler.ConstructHybridUncond

/-!
# An operational-cost interface for lazy hit-and-run

The repository's hit-and-run kernel is measure-theoretic: conditional on a direction it
uses `uniformOn volume (chordSet K x theta)`.  There is currently no kernel which computes
the two chord endpoints by scanning a finite family of facet inequalities, and hence no
proved equality between such a finite computation and `hitAndRun K`.

This file isolates precisely that missing implementation theorem.  A
`CostedKernelRealization P` is a costed Markov transition whose state marginal is exactly
`P`; its cost coordinate is required by the caller to record the operational
membership/facet-inspection cost.  From that one certificate we prove exact erasure for a
finite trajectory, additive expected cost, and compatibility with the operational KV97
rounding/rejection bridge.

Thus the results below do not silently count a denotational hit-and-run transition as one
membership query.  For an explicit polytope, it remains to construct the certificate by
proving that the finite max/min chord computation samples the same line-uniform law.
-/

namespace Ttc.CostedLazyHitAndRunAdapter

open MeasureTheory ProbabilityTheory
open Arlib Arlib.MarkovChains
open scoped ENNReal Classical BigOperators

variable {S : Type*} [MeasurableSpace S]

/-- A costed implementation certificate for a Markov kernel.

The intended interpretation of `stepBound` is a bound on the mean number of recorded
facet inspections or membership queries in one call of `kernel`.  This interpretation is
an operational premise: the measure theory can verify erasure and compose the recorded
cost, but cannot identify an arbitrary `ENNReal` coordinate with machine operations. -/
structure CostedKernelRealization (P : Kernel S S) where
  kernel : Kernel S (ENNReal × S)
  isMarkov : IsMarkovKernel kernel
  forget : ∀ x, Measure.map Prod.snd (kernel x) = P x
  stepBound : ENNReal
  mean_le : ∀ x, (∫⁻ z, z.1 ∂kernel x) ≤ stepBound

instance {P : Kernel S S} (R : CostedKernelRealization P) :
    IsMarkovKernel R.kernel := R.isMarkov

/-- The constant schedule associated with a one-step costed realization. -/
noncomputable def schedule {P : Kernel S S} (R : CostedKernelRealization P) :
    Nat → Kernel S (ENNReal × S) := fun _ => R.kernel

instance {P : Kernel S S} (R : CostedKernelRealization P) (_i : Nat) :
    IsMarkovKernel (schedule R _i) := by
  unfold schedule
  infer_instance

/-- The full costed trajectory started from `mu`. -/
noncomputable def execution {P : Kernel S S} (R : CostedKernelRealization P)
    (mu : Measure S) : Measure (Nat → ENNReal × S) :=
  Ttc.SequentialCost.execution (schedule R) mu

instance {P : Kernel S S} (R : CostedKernelRealization P)
    (mu : Measure S) [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (execution R mu) := by
  unfold execution
  infer_instance

/-- Cost together with the state reached after `t` transitions. -/
noncomputable def endpointLaw {P : Kernel S S} (R : CostedKernelRealization P)
    (mu : Measure S) (t : Nat) : Measure (ENNReal × S) :=
  Measure.map
    (fun omega => (Ttc.SequentialCost.totalCost t omega, (omega t).2))
    (execution R mu)

theorem measurable_endpointMap (t : Nat) :
    Measurable
      (fun omega : Nat → ENNReal × S =>
        (Ttc.SequentialCost.totalCost t omega, (omega t).2)) := by
  exact (Ttc.SequentialCost.measurable_totalCost t).prodMk
    (measurable_snd.comp (measurable_pi_apply t))

instance {P : Kernel S S} (R : CostedKernelRealization P)
    (mu : Measure S) [IsProbabilityMeasure mu] (t : Nat) :
    IsProbabilityMeasure (endpointLaw R mu t) :=
  Measure.isProbabilityMeasure_map (measurable_endpointMap t).aemeasurable

/-- Exact erasure of the homogeneous costed execution. -/
theorem map_execution_output_eq_iterate
    (P : Kernel S S) [IsMarkovKernel P]
    (R : CostedKernelRealization P)
    (mu : Measure S) [IsProbabilityMeasure mu] (t : Nat) :
    Measure.map (fun omega => (omega t).2) (execution R mu) =
      iterate P mu t := by
  induction t with
  | zero =>
      exact Ttc.SequentialCost.map_execution_output_zero (schedule R) mu
  | succ t ih =>
      change Measure.map (fun omega => (omega (t + 1)).2)
          (Ttc.SequentialCost.execution (schedule R) mu) = _
      rw [Ttc.SequentialCost.map_execution_output_succ
          (schedule R) (fun _ => P) (fun _ x => R.forget x)]
      rw [show Measure.map (fun omega => (omega t).2)
          (Ttc.SequentialCost.execution (schedule R) mu) = iterate P mu t by
            simpa only [execution] using ih]
      rfl

/-- Forgetting the accumulated cost gives exactly the ordinary iterate law. -/
theorem map_snd_endpointLaw
    (P : Kernel S S) [IsMarkovKernel P]
    (R : CostedKernelRealization P)
    (mu : Measure S) [IsProbabilityMeasure mu] (t : Nat) :
    Measure.map Prod.snd (endpointLaw R mu t) = iterate P mu t := by
  rw [endpointLaw, Measure.map_map measurable_snd (measurable_endpointMap t)]
  simpa [Function.comp_def] using map_execution_output_eq_iterate P R mu t

/-- The expected recorded cost of `t` calls is at most the sum of the one-step budgets. -/
theorem lintegral_fst_endpointLaw_le_sum
    {P : Kernel S S} [IsMarkovKernel P]
    (R : CostedKernelRealization P)
    (mu : Measure S) [IsProbabilityMeasure mu] (t : Nat) :
    (∫⁻ z, z.1 ∂endpointLaw R mu t) ≤
      ∑ _i ∈ Finset.range t, R.stepBound := by
  rw [endpointLaw, lintegral_map measurable_fst (measurable_endpointMap t)]
  exact Ttc.SequentialCost.lintegral_totalCost_le_sum_uniformBounds
    (schedule R) mu t (fun _ => R.stepBound) (fun _ _ x => R.mean_le x)

/-- Closed form of the preceding additive cost bound. -/
theorem lintegral_fst_endpointLaw_le
    {P : Kernel S S} [IsMarkovKernel P]
    (R : CostedKernelRealization P)
    (mu : Measure S) [IsProbabilityMeasure mu] (t : Nat) :
    (∫⁻ z, z.1 ∂endpointLaw R mu t) ≤ (t : ENNReal) * R.stepBound := by
  simpa using lintegral_fst_endpointLaw_le_sum R mu t

/-! ## Lazy hit-and-run and the high branch of the hybrid sampler -/

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- The exact missing operational object for lazy hit-and-run. -/
abbrev LazyHitAndRunRealization {n : Nat} (K : Set (State n)) :=
  CostedKernelRealization (lazy (hitAndRun K))

/-- In dimension at least `1100`, a lazy hit-and-run realization is also a realization of
the kernel selected by `kv97HybridKernel`. -/
noncomputable def highDimHybridRealization {n : Nat} (hn : 1100 ≤ n)
    (K : Set (State n)) (delta : Real) (R : LazyHitAndRunRealization K) :
    CostedKernelRealization (Ttc.kv97HybridKernel K delta) where
  kernel := R.kernel
  isMarkov := R.isMarkov
  forget := fun x => by
    simpa [Ttc.kv97HybridKernel, hn] using R.forget x
  stepBound := R.stepBound
  mean_le := R.mean_le

/-- Exact cost erasure for the high-dimensional branch of the all-dimensional sampler. -/
theorem map_snd_highDimHybridEndpointLaw {n : Nat} (hn : 1100 ≤ n)
    (K : Set (State n)) (delta : Real) (R : LazyHitAndRunRealization K)
    (mu : Measure (State n)) [IsProbabilityMeasure mu] (t : Nat) :
    Measure.map Prod.snd
        (endpointLaw (highDimHybridRealization hn K delta R) mu t) =
      iterate (Ttc.kv97HybridKernel K delta) mu t := by
  exact map_snd_endpointLaw _ _ _ _

/-! ## KV97 randomized-rounding composition -/

open Ttc.KV97RoundedEndpointBridge

variable {A : Type*} {n : Nat} {D : Ttc.DNF A}

/-- A costed realization of the continuous endpoint, followed by the existing operational
KV97 rounding/rejection sampler. -/
noncomputable def expectedQueryKV97SamplerOfRealization
    (P : Kernel (State n) (State n)) [IsMarkovKernel P]
    (R : CostedKernelRealization P)
    (mu : Measure (State n)) [IsProbabilityMeasure mu] (t : Nat)
    (M : A → Set (State n)) (rho : Int)
    (law : {c : Ttc.Cube A // c ∈ D} → Measure (State n))
    (i : {c : Ttc.Cube A // c ∈ D})
    (hmarg : iterate P mu t = law i)
    (hpos : 0 < Ttc.CostedKV97Rounding.roundedMeasure (law i)
      (integerAcceptance M rho i.val)) :
    ExpectedQueryFineSampler (kv97SampMeasure M rho law i) :=
  expectedQueryKV97Sampler (endpointLaw R mu t) M rho law i
    ((map_snd_endpointLaw P R mu t).trans hmarg) hpos

/-- Expected recorded facet/query cost after continuous execution and randomized-rounding
rejection.  `acceptLower` may be instantiated by the proved KV97 lower bound `1/8`. -/
theorem lintegral_fst_costedKV97Endpoint_le
    (P : Kernel (State n) (State n)) [IsMarkovKernel P]
    (R : CostedKernelRealization P)
    (mu : Measure (State n)) [IsProbabilityMeasure mu] (t : Nat)
    (M : A → Set (State n)) (rho : Int) (i : Ttc.Cube A)
    {acceptLower : ENNReal}
    (haccept : acceptLower ≤
      Ttc.CostedKV97Rounding.roundedMeasure (iterate P mu t)
        (integerAcceptance M rho i)) :
    (∫⁻ z, z.1 ∂costedFineEndpointLaw (endpointLaw R mu t) M rho i) ≤
      acceptLower⁻¹ * ((t : ENNReal) * R.stepBound + 1) := by
  exact lintegral_fst_costedFineEndpointLaw_le
    (endpointLaw R mu t) M rho i
      (by simpa [map_snd_endpointLaw P R mu t] using haccept)
      (lintegral_fst_endpointLaw_le R mu t)

/-- The public high-dimensional specialization: the continuous endpoint is exactly the
law used by `kv97LazyHitAndRunContLaw`, and the target is therefore exactly its existing
measure-valued KV97 sampler.  The only new argument is the operational lazy-hit-and-run
realization `R`. -/
noncomputable def expectedQueryKV97LazyHitAndRunSampler
    {Jt : Type}
    (epsPrime rf : Real)
    (Am : {c : Ttc.Cube A // c ∈ D} → Jt → State n)
    (bv : {c : Ttc.Cube A // c ∈ D} → Jt → Real)
    (rin Rout Mw : {c : Ttc.Cube A // c ∈ D} → Real)
    (sigma : {c : Ttc.Cube A // c ∈ D} → Measure (State n))
    (hsigma : ∀ j, IsProbabilityMeasure (sigma j))
    (M : A → Set (State n)) (rho : Int)
    (i : {c : Ttc.Cube A // c ∈ D})
    (R : LazyHitAndRunRealization
      (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf))
    (hpos : 0 < Ttc.CostedKV97Rounding.roundedMeasure
      (Ttc.kv97LazyHitAndRunContLaw epsPrime rf Am bv rin Rout Mw sigma i)
      (integerAcceptance M rho i.val)) :
    ExpectedQueryFineSampler
      (kv97SampMeasure M rho
        (Ttc.kv97LazyHitAndRunContLaw epsPrime rf Am bv rin Rout Mw sigma) i) := by
  letI : IsProbabilityMeasure (sigma i) := hsigma i
  exact expectedQueryKV97SamplerOfRealization
    (lazy (hitAndRun
      (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf)))
    R (sigma i)
    (Ttc.lazyHitAndRunUncondSteps n (rin i) (Rout i) (Mw i)
      (epsPrime / (4 *
        (volume (Arlib.KV97.inflated (Am i) (bv i)
          (Arlib.KV97.cOf epsPrime) rf)).toReal)))
    M rho (Ttc.kv97LazyHitAndRunContLaw epsPrime rf Am bv rin Rout Mw sigma) i
    rfl hpos

/-- The corresponding specialization for the high-dimensional branch of the hybrid
all-dimensional sampler.  This theorem proves that the branch choice does not introduce
an additional semantic premise. -/
noncomputable def expectedQueryKV97HybridHighSampler
    {Jt : Type} (hn : 1100 ≤ n)
    (epsPrime rf : Real)
    (Am : {c : Ttc.Cube A // c ∈ D} → Jt → State n)
    (bv : {c : Ttc.Cube A // c ∈ D} → Jt → Real)
    (rin Rout delta Mw : {c : Ttc.Cube A // c ∈ D} → Real)
    (sigma : {c : Ttc.Cube A // c ∈ D} → Measure (State n))
    (hsigma : ∀ j, IsProbabilityMeasure (sigma j))
    (M : A → Set (State n)) (rho : Int)
    (i : {c : Ttc.Cube A // c ∈ D})
    (R : LazyHitAndRunRealization
      (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf))
    (hpos : 0 < Ttc.CostedKV97Rounding.roundedMeasure
      (Ttc.kv97HybridContLaw epsPrime rf Am bv rin Rout delta Mw sigma i)
      (integerAcceptance M rho i.val)) :
    ExpectedQueryFineSampler
      (kv97SampMeasure M rho
        (Ttc.kv97HybridContLaw epsPrime rf Am bv rin Rout delta Mw sigma) i) := by
  letI : IsProbabilityMeasure (sigma i) := hsigma i
  let K := Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf
  exact expectedQueryKV97SamplerOfRealization
    (Ttc.kv97HybridKernel K (delta i))
    (highDimHybridRealization hn K (delta i) R) (sigma i)
    (Ttc.kv97HybridSteps n (rin i) (Rout i) (delta i) (Mw i)
      (epsPrime / (4 * (volume K).toReal)))
    M rho (Ttc.kv97HybridContLaw epsPrime rf Am bv rin Rout delta Mw sigma) i
    rfl hpos

/-! ## Axiom audit -/

#print axioms map_snd_endpointLaw
#print axioms lintegral_fst_endpointLaw_le
#print axioms map_snd_highDimHybridEndpointLaw
#print axioms expectedQueryKV97SamplerOfRealization
#print axioms lintegral_fst_costedKV97Endpoint_le
#print axioms expectedQueryKV97LazyHitAndRunSampler
#print axioms expectedQueryKV97HybridHighSampler

end Ttc.CostedLazyHitAndRunAdapter
