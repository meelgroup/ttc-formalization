/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Exec.FiniteFacetHitAndRunCost
import Ttc.Exec.RawBallWalkQueryCost

/-!
# Concrete all-dimensional costed KV97 sampler

This is the operational companion to `kv97SamplerOfHybridUncond`.  Above dimension 1099
it runs the finite-facet lazy hit-and-run implementation; below that threshold it runs the
existing raw lazy ball walk, whose active proposal records one membership query.  Both
branches erase exactly to `kv97HybridKernel`.

The high-dimensional cost counts inspected inequalities.  It does not count bit
operations for exact real inner products, comparisons, division, sphere sampling, or
interval sampling.  Thus the result is a polynomial facet/membership-inspection bound,
not a Turing-machine bit-complexity theorem.
-/

namespace Ttc.ConcreteHybridExpectedQuerySampler

open MeasureTheory ProbabilityTheory Set Pointwise
open Arlib Arlib.MarkovChains
open Ttc.CostedLazyHitAndRunAdapter
open Ttc.FiniteFacetHitAndRunCost
open Ttc.RawBallWalkQueryCost Ttc.RawGaussianQueryCost
open Ttc.KV97RoundedEndpointBridge
open scoped ENNReal Classical

variable {n : Nat} {ι : Type} [Fintype ι]

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- The existing raw zero-variance Gaussian execution is an operational realization of
one lazy ball-walk step, recording one membership query on the active half. -/
noncomputable def lazyBallWalkRealization
    {K : Set (State n)} (hK : MeasurableSet K) (delta : Real) (hdelta : 0 < delta) :
    CostedKernelRealization (lazy (ballWalk K delta)) where
  kernel := lazyRawQueryCostedKernel hK delta 0 hdelta
  isMarkov := inferInstance
  forget := map_snd_lazyRawQueryCostedKernel_eq_ballWalk hK delta hdelta
  stepBound := (2 : ENNReal)⁻¹
  mean_le := fun x => (lintegral_fst_lazyRawQueryCostedKernel hK delta 0 hdelta x).le

/-- The exact branch-dependent one-step inspection budget. -/
noncomputable def hybridStepInspectionBound (n : Nat) (facetCount : Nat) : ENNReal :=
  if 21 ≤ n then (2 : ENNReal)⁻¹ * facetCount else (2 : ENNReal)⁻¹

/-- A concrete realization of the all-dimensional hybrid kernel on a finite KV97 inflated
polytope. -/
noncomputable def hybridRealization
    (A : ι → State n) (b : ι → Real) (c r delta : Real)
    (hK : Bornology.IsBounded (Arlib.KV97.inflated A b c r))
    (hdelta : 0 < delta) [NeZero n] :
    CostedKernelRealization
      (Ttc.kv97HybridKernel (Arlib.KV97.inflated A b c r) delta) := by
  by_cases hhigh : 21 ≤ n
  · exact highDimHybridRealization hhigh _ delta
      (lazyHitAndRunInflatedRealization A b c r hK)
  · let R := lazyBallWalkRealization
      (Arlib.KV97.measurableSet_inflated A b c r) delta hdelta
    refine
      { kernel := R.kernel
        isMarkov := R.isMarkov
        forget := fun x => ?_
        stepBound := R.stepBound
        mean_le := R.mean_le }
    simpa [Ttc.kv97HybridKernel, hhigh] using R.forget x

theorem hybridRealization_stepBound
    (A : ι → State n) (b : ι → Real) (c r delta : Real)
    (hK : Bornology.IsBounded (Arlib.KV97.inflated A b c r))
    (hdelta : 0 < delta) [NeZero n] :
    (hybridRealization A b c r delta hK hdelta).stepBound =
      hybridStepInspectionBound n (Fintype.card ι) := by
  by_cases hhigh : 21 ≤ n
  · simp [hybridRealization, hhigh, hybridStepInspectionBound,
      highDimHybridRealization, lazyHitAndRunInflatedRealization_stepBound]
  · simp [hybridRealization, hhigh, hybridStepInspectionBound,
      lazyBallWalkRealization]

/-- The recorded continuous-chain inspection budget is polynomial once the already-proved
hybrid transition bound is substituted. -/
theorem hybrid_steps_mul_inspectionBound_le
    (hn : 1 ≤ n) {rin Rout delta Mw eps : Real}
    (hrin : 0 < rin) (hRout : 0 < Rout) (hdelta : 0 < delta)
    (hM : 1 ≤ Mw) (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    (Ttc.kv97HybridSteps n rin Rout delta Mw eps : ENNReal) *
        hybridStepInspectionBound n (Fintype.card ι) ≤
      ENNReal.ofReal (Ttc.hybridTransitionBound n rin Rout delta Mw eps) *
        hybridStepInspectionBound n (Fintype.card ι) := by
  gcongr
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal
    (Ttc.kv97HybridSteps_le_transitionBound hn hrin hRout hdelta hM heps0 heps1)

variable {A0 : Type*} {D : Ttc.DNF A0}

/-- One all-dimensional operational endpoint package matching exactly the continuous-law
family used by `kv97SamplerOfHybridUncond`. -/
noncomputable def expectedQueryKV97HybridConcrete
    (epsPrime rf : Real)
    (Am : {c : Ttc.Cube A0 // c ∈ D} → ι → State n)
    (bv : {c : Ttc.Cube A0 // c ∈ D} → ι → Real)
    (rin Rout delta Mw : {c : Ttc.Cube A0 // c ∈ D} → Real)
    (sigma : {c : Ttc.Cube A0 // c ∈ D} → Measure (State n))
    (hsigma : ∀ j, IsProbabilityMeasure (sigma j))
    (hbounded : ∀ j, Bornology.IsBounded
      (Arlib.KV97.inflated (Am j) (bv j) (Arlib.KV97.cOf epsPrime) rf))
    (hdelta : ∀ j, 0 < delta j) [NeZero n]
    (body : A0 → Set (State n)) (rho : Int)
    (i : {c : Ttc.Cube A0 // c ∈ D})
    (hpos : 0 < Ttc.CostedKV97Rounding.roundedMeasure
      (Ttc.kv97HybridContLaw epsPrime rf Am bv rin Rout delta Mw sigma i)
      (integerAcceptance body rho i.val)) :
    ExpectedQueryFineSampler
      (kv97SampMeasure body rho
        (Ttc.kv97HybridContLaw epsPrime rf Am bv rin Rout delta Mw sigma) i) := by
  letI : IsProbabilityMeasure (sigma i) := hsigma i
  let K := Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf
  exact expectedQueryKV97SamplerOfRealization
    (Ttc.kv97HybridKernel K (delta i))
    (hybridRealization (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf (delta i)
      (hbounded i) (hdelta i))
    (sigma i)
    (Ttc.kv97HybridSteps n (rin i) (Rout i) (delta i) (Mw i)
      (epsPrime / (4 * (volume K).toReal)))
    body rho (Ttc.kv97HybridContLaw epsPrime rf Am bv rin Rout delta Mw sigma) i
    rfl hpos

/-- Explicit expected inspection bound before substituting the existing polynomial bound
on `kv97HybridSteps`.  With KV97 acceptance lower bound `1/8`, the outer inverse is `8`. -/
theorem expected_inspections_kv97HybridConcrete_le
    (epsPrime rf : Real)
    (Am : {c : Ttc.Cube A0 // c ∈ D} → ι → State n)
    (bv : {c : Ttc.Cube A0 // c ∈ D} → ι → Real)
    (rin Rout delta Mw : {c : Ttc.Cube A0 // c ∈ D} → Real)
    (sigma : {c : Ttc.Cube A0 // c ∈ D} → Measure (State n))
    (hsigma : ∀ j, IsProbabilityMeasure (sigma j))
    (hbounded : ∀ j, Bornology.IsBounded
      (Arlib.KV97.inflated (Am j) (bv j) (Arlib.KV97.cOf epsPrime) rf))
    (hdelta : ∀ j, 0 < delta j) [NeZero n]
    (body : A0 → Set (State n)) (rho : Int)
    (i : {c : Ttc.Cube A0 // c ∈ D}) {acceptLower : ENNReal}
    (haccept : acceptLower ≤ Ttc.CostedKV97Rounding.roundedMeasure
      (Ttc.kv97HybridContLaw epsPrime rf Am bv rin Rout delta Mw sigma i)
      (integerAcceptance body rho i.val)) :
    let K := Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf
    let t := Ttc.kv97HybridSteps n (rin i) (Rout i) (delta i) (Mw i)
      (epsPrime / (4 * (volume K).toReal))
    let R := hybridRealization (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf (delta i)
      (hbounded i) (hdelta i)
    (∫⁻ z, z.1 ∂costedFineEndpointLaw (endpointLaw R (sigma i) t)
      body rho i.val) ≤
      acceptLower⁻¹ *
        ((t : ENNReal) * hybridStepInspectionBound n (Fintype.card ι) + 1) := by
  dsimp only
  letI : IsProbabilityMeasure (sigma i) := hsigma i
  rw [← hybridRealization_stepBound (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf
    (delta i) (hbounded i) (hdelta i)]
  apply lintegral_fst_costedKV97Endpoint_le
  simpa [Ttc.kv97HybridContLaw] using haccept

#print axioms hybridRealization
#print axioms hybrid_steps_mul_inspectionBound_le
#print axioms expectedQueryKV97HybridConcrete
#print axioms expected_inspections_kv97HybridConcrete_le

end Ttc.ConcreteHybridExpectedQuerySampler
