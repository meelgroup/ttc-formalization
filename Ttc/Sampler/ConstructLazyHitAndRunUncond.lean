/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Sampler.ConstructHitAndRun
import Ttc.Sampler.HitAndRunBackendUncond
import Ttc.Exec.KV97RoundedEndpointBridge

/-!
# An unconditional high-dimensional lazy hit-and-run KV97 sampler

This file replaces the uninhabited plain-walk `HitAndRunTheorem11Input` used by
`ConstructHitAndRun` with the theorem which is actually proved in this repository:
`Ttc.tvLe_iterate_lazy_hitAndRun_at_contract_shape_uncond`.

The differences are kept visible in every public definition.  The walk is lazy, the
dimension hypothesis is `1100 ≤ n`, and the deadline is

`4 * (2^8 * hitAndRunTheorem11Threshold n r R M eps)`.

Thus the count is `2^10` times the stale contract's count: `4` for laziness and `2^8` for
the proved `1/8000` overlap constant in place of the paper's `1/500`.  It counts Markov
transitions only.  No declaration below claims that a hit-and-run transition has an
operational implementation using a bounded number of polytope-facet or membership queries.
-/

namespace Ttc

open MeasureTheory Pointwise
open scoped ENNReal Classical

/-! ## Honest deadline and continuous law -/

/-- The proved contract-shaped lazy hit-and-run deadline. -/
noncomputable def lazyHitAndRunUncondDeadline
    (n : ℕ) (r R M eps : ℝ) : ℝ :=
  4 * (2 ^ 8 * hitAndRunTheorem11Threshold n r R M eps)

/-- Natural transition count used by the unconditional lazy hit-and-run sampler.  The
`max 0` only totalizes the definition away from the intended positive parameters. -/
noncomputable def lazyHitAndRunUncondSteps
    (n : ℕ) (r R M eps : ℝ) : ℕ :=
  ⌈max 0 (lazyHitAndRunUncondDeadline n r R M eps)⌉₊

theorem lazyHitAndRunUncondDeadline_le_steps
    (n : ℕ) (r R M eps : ℝ) :
    lazyHitAndRunUncondDeadline n r R M eps ≤
      (lazyHitAndRunUncondSteps n r R M eps : ℝ) :=
  (le_max_right _ _).trans (Nat.le_ceil _)

/-- The deadline in its closed polynomial form. -/
theorem lazyHitAndRunUncondDeadline_eq
    (n : ℕ) (r R M eps : ℝ) :
    lazyHitAndRunUncondDeadline n r R M eps =
      2 ^ 66 * (n : ℝ) ^ 2 * R ^ 2 / r ^ 2 * Real.log (8 * M / eps ^ 2) := by
  unfold lazyHitAndRunUncondDeadline hitAndRunTheorem11Threshold
  ring

/-- Ceiling overhead is less than one transition, stated without positivity assumptions. -/
theorem lazyHitAndRunUncondSteps_lt_deadline_add_one
    (n : ℕ) (r R M eps : ℝ) :
    (lazyHitAndRunUncondSteps n r R M eps : ℝ) <
      max 0 (2 ^ 66 * (n : ℝ) ^ 2 * R ^ 2 / r ^ 2 *
        Real.log (8 * M / eps ^ 2)) + 1 := by
  unfold lazyHitAndRunUncondSteps
  rw [lazyHitAndRunUncondDeadline_eq]
  exact Nat.ceil_lt_add_one (le_max_left _ _)

/-- The sampler's continuous law: the proved number of transitions of the lazy hit-and-run
kernel, with no target measure hidden in the definition. -/
noncomputable def kv97LazyHitAndRunContLaw {A : Type*} {n : ℕ} {D : DNF A} {Jt : Type}
    (epsPrime rf : ℝ)
    (Am : {c : Cube A // c ∈ D} → Jt → Space n)
    (bv : {c : Cube A // c ∈ D} → Jt → ℝ)
    (rin Rout Mw : {c : Cube A // c ∈ D} → ℝ)
    (sigma : {c : Cube A // c ∈ D} → Measure (Space n)) :
    {c : Cube A // c ∈ D} → Measure (Space n) := fun i =>
  Arlib.MarkovChains.iterate
    (Arlib.MarkovChains.lazy
      (Arlib.MarkovChains.hitAndRun
        (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf)))
    (sigma i)
    (lazyHitAndRunUncondSteps n (rin i) (Rout i) (Mw i)
      (epsPrime / (4 *
        (volume (Arlib.KV97.inflated (Am i) (bv i)
          (Arlib.KV97.cOf epsPrime) rf)).toReal)))

/-- Exact iterate identity; in particular, the continuous law is not defined to be the
target uniform measure. -/
theorem kv97LazyHitAndRunContLaw_eq_iterate
    {A : Type*} {n : ℕ} {D : DNF A} {Jt : Type}
    (epsPrime rf : ℝ)
    (Am : {c : Cube A // c ∈ D} → Jt → Space n)
    (bv : {c : Cube A // c ∈ D} → Jt → ℝ)
    (rin Rout Mw : {c : Cube A // c ∈ D} → ℝ)
    (sigma : {c : Cube A // c ∈ D} → Measure (Space n))
    (i : {c : Cube A // c ∈ D}) :
    kv97LazyHitAndRunContLaw epsPrime rf Am bv rin Rout Mw sigma i =
      Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy
          (Arlib.MarkovChains.hitAndRun
            (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf)))
        (sigma i)
        (lazyHitAndRunUncondSteps n (rin i) (Rout i) (Mw i)
          (epsPrime / (4 *
            (volume (Arlib.KV97.inflated (Am i) (bv i)
              (Arlib.KV97.cOf epsPrime) rf)).toReal))) := rfl

instance isProbabilityMeasure_kv97LazyHitAndRunContLaw
    {A : Type*} {n : ℕ} {D : DNF A} {Jt : Type}
    (epsPrime rf : ℝ)
    (Am : {c : Cube A // c ∈ D} → Jt → Space n)
    (bv : {c : Cube A // c ∈ D} → Jt → ℝ)
    (rin Rout Mw : {c : Cube A // c ∈ D} → ℝ)
    (sigma : {c : Cube A // c ∈ D} → Measure (Space n))
    (i : {c : Cube A // c ∈ D}) [IsProbabilityMeasure (sigma i)] :
    IsProbabilityMeasure
      (kv97LazyHitAndRunContLaw epsPrime rf Am bv rin Rout Mw sigma i) :=
  Arlib.MarkovChains.isProbabilityMeasure_iterate _ _ _

/-! ## Mixing and the `KV97Sampler` constructor -/

/-- Unconditional lazy hit-and-run mixing on a KV97 inflated body. -/
theorem tvLe_lazyHitAndRunLaw_inflated {n : ℕ} {ι : Type*}
    (hn : 1100 ≤ n) (Am : ι → Space n) (bv : ι → ℝ) (cc rf : ℝ)
    {zin zout : Space n} {rin Rout : ℝ} (hr : 0 < rin) (hR : 0 ≤ Rout)
    (hin : Metric.closedBall zin rin ⊆ Arlib.KV97.inflated Am bv cc rf)
    (hout : Arlib.KV97.inflated Am bv cc rf ⊆ Metric.closedBall zout Rout)
    {sigma : Measure (Space n)} [IsProbabilityMeasure sigma]
    {Mw eps : ℝ} (hM : 1 ≤ Mw) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {S : Set (Space n)} (hSm : MeasurableSet S)
    (hS : sigma S ≤ ENNReal.ofReal (eps / 2))
    (hdom : ∀ T, MeasurableSet T → sigma (T \ S) ≤ ENNReal.ofReal Mw *
      Arlib.uniformOn volume (Arlib.KV97.inflated Am bv cc rf) (T \ S)) :
    Arlib.TVLe
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy
          (Arlib.MarkovChains.hitAndRun (Arlib.KV97.inflated Am bv cc rf))) sigma
        (lazyHitAndRunUncondSteps n rin Rout Mw eps))
      (Arlib.uniformOn volume (Arlib.KV97.inflated Am bv cc rf))
      (ENNReal.ofReal eps) := by
  apply tvLe_iterate_lazy_hitAndRun_at_contract_shape_uncond hn
    (Arlib.KV97.measurableSet_inflated _ _ _ _)
    (Arlib.KV97.convex_inflated _ _ _ _)
    (Arlib.KV97.isClosed_inflated _ _ _ _)
    hr hR hin hout hM heps0 heps1 hSm hS hdom
  exact lazyHitAndRunUncondDeadline_le_steps n rin Rout Mw eps

/-- A `KV97Sampler` driven by the proved unconditional lazy hit-and-run theorem.

The live dimension restriction `1100 ≤ n` is explicit.  The remaining hypotheses describe
the inflated bodies and the supplied exceptional warm starts; there is no sampler-accuracy
or mixing-theorem binder. -/
noncomputable def kv97SamplerOfLazyHitAndRunUncond
    {A : Type*} {n : ℕ} {M : A → Set (Space n)} {D : DNF A} {ρ : ℤ} {epsPrime : ℝ}
    (hn : 1100 ≤ n) (hEps : 0 < epsPrime)
    (Jt : Type) [Fintype Jt]
    (Am : {c : Cube A // c ∈ D} → Jt → Space n)
    (bv : {c : Cube A // c ∈ D} → Jt → ℝ)
    (hdil : ∀ i, latticeScale ρ • region M i.val ⊆ Arlib.Polytope.body (Am i) (bv i))
    (rf : ℝ) (hr1 : 1 ≤ rf) (hcard : (Fintype.card Jt : ℝ) ≤ rf)
    (zin : {c : Cube A // c ∈ D} → Space n)
    (rin : {c : Cube A // c ∈ D} → ℝ)
    (hrin : ∀ i, 0 < rin i)
    (hin : ∀ i, Metric.closedBall (zin i) (rin i) ⊆
      Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf)
    (zout : {c : Cube A // c ∈ D} → Space n)
    (Rout : {c : Cube A // c ∈ D} → ℝ)
    (hRout : ∀ i, 0 ≤ Rout i)
    (hout : ∀ i, Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rf ⊆
      Metric.closedBall (zout i) (Rout i))
    (heps1 : ∀ i, epsPrime / (4 *
      (volume (Arlib.KV97.inflated (Am i) (bv i)
        (Arlib.KV97.cOf epsPrime) rf)).toReal) ≤ 1)
    (sigma : {c : Cube A // c ∈ D} → Measure (Space n))
    (hsigma : ∀ i, IsProbabilityMeasure (sigma i))
    (Mw : {c : Cube A // c ∈ D} → ℝ) (hM : ∀ i, 1 ≤ Mw i)
    (Sx : {c : Cube A // c ∈ D} → Set (Space n))
    (hSm : ∀ i, MeasurableSet (Sx i))
    (hS : ∀ i, sigma i (Sx i) ≤ ENNReal.ofReal
      (epsPrime / (4 *
        (volume (Arlib.KV97.inflated (Am i) (bv i)
          (Arlib.KV97.cOf epsPrime) rf)).toReal) / 2))
    (hdom : ∀ i, ∀ T, MeasurableSet T →
      sigma i (T \ Sx i) ≤ ENNReal.ofReal (Mw i) *
        Arlib.uniformOn volume
          (Arlib.KV97.inflated (Am i) (bv i)
            (Arlib.KV97.cOf epsPrime) rf) (T \ Sx i)) :
    KV97Sampler A n M D ρ epsPrime
      (kv97SampD M D ρ
        (kv97LazyHitAndRunContLaw epsPrime rf Am bv rin Rout Mw sigma)) where
  J := Jt
  fintypeJ := inferInstance
  Amat := Am
  bvec := bv
  dilate_eq := hdil
  facetBound := rf
  one_le_facetBound := hr1
  card_le_facetBound := hcard
  contLaw := kv97LazyHitAndRunContLaw epsPrime rf Am bv rin Rout Mw sigma
  isProbContLaw := by
    intro i
    haveI := hsigma i
    exact isProbabilityMeasure_kv97LazyHitAndRunContLaw _ _ _ _ _ _ _ _ _
  contVol := fun i =>
    (volume (Arlib.KV97.inflated (Am i) (bv i)
      (Arlib.KV97.cOf epsPrime) rf)).toReal
  contVol_pos := fun i =>
    toReal_volume_inflated_pos_of_closedBalls (hrin i) (hin i) (hout i)
  contVol_eq := fun _ => rfl
  law_tv := by
    intro i
    haveI := hsigma i
    have hpos : 0 < (volume
        (Arlib.KV97.inflated (Am i) (bv i)
          (Arlib.KV97.cOf epsPrime) rf)).toReal :=
      toReal_volume_inflated_pos_of_closedBalls (hrin i) (hin i) (hout i)
    exact tvLe_lazyHitAndRunLaw_inflated hn (Am i) (bv i)
      (Arlib.KV97.cOf epsPrime) rf (hrin i) (hRout i) (hin i) (hout i)
      (hM i) (div_pos hEps (by linarith)) (heps1 i) (hSm i) (hS i) (hdom i)
  sampD_eq := fun i x _ => kv97SampD_apply M ρ _ i x

/-! ## Existing KV97 endpoint bridge -/

/-- The existing measure-valued KV97 bridge turns the lazy hit-and-run continuous law into
a probability law on fine-lattice endpoints whenever the rejection event has positive
mass. -/
theorem isProbabilityMeasure_kv97LazyHitAndRunSampMeasure
    {A : Type*} {n : ℕ} {M : A → Set (Space n)} {D : DNF A} {ρ : ℤ} {Jt : Type}
    (epsPrime rf : ℝ)
    (Am : {c : Cube A // c ∈ D} → Jt → Space n)
    (bv : {c : Cube A // c ∈ D} → Jt → ℝ)
    (rin Rout Mw : {c : Cube A // c ∈ D} → ℝ)
    (sigma : {c : Cube A // c ∈ D} → Measure (Space n))
    (hsigma : ∀ i, IsProbabilityMeasure (sigma i))
    (i : {c : Cube A // c ∈ D})
    (hpos : 0 < Ttc.CostedKV97Rounding.roundedMeasure
      (kv97LazyHitAndRunContLaw epsPrime rf Am bv rin Rout Mw sigma i)
      (Ttc.KV97RoundedEndpointBridge.integerAcceptance M ρ i.val)) :
    IsProbabilityMeasure
      (Ttc.KV97RoundedEndpointBridge.kv97SampMeasure M ρ
        (kv97LazyHitAndRunContLaw epsPrime rf Am bv rin Rout Mw sigma) i) := by
  letI : ∀ j, IsProbabilityMeasure
      (kv97LazyHitAndRunContLaw epsPrime rf Am bv rin Rout Mw sigma j) := fun j => by
    haveI := hsigma j
    infer_instance
  exact Ttc.KV97RoundedEndpointBridge.isProbabilityMeasure_kv97SampMeasure
    M ρ _ i hpos

/-- The bridge also identifies every accepted endpoint mass with the `kv97SampD` formula. -/
theorem toReal_kv97LazyHitAndRunSampMeasure_singleton
    {A : Type*} {n : ℕ} {M : A → Set (Space n)} {D : DNF A} {ρ : ℤ} {Jt : Type}
    (epsPrime rf : ℝ)
    (Am : {c : Cube A // c ∈ D} → Jt → Space n)
    (bv : {c : Cube A // c ∈ D} → Jt → ℝ)
    (rin Rout Mw : {c : Cube A // c ∈ D} → ℝ)
    (sigma : {c : Cube A // c ∈ D} → Measure (Space n))
    (hsigma : ∀ i, IsProbabilityMeasure (sigma i))
    (i : {c : Cube A // c ∈ D})
    (hfinite : ((latticeScale ρ • region M i.val) ∩ intLattice n :
      Set (Space n)).Finite)
    (z : Fin n → ℤ)
    (hz : z ∈ Ttc.KV97RoundedEndpointBridge.integerAcceptance M ρ i.val) :
    (Ttc.KV97RoundedEndpointBridge.kv97SampMeasure M ρ
      (kv97LazyHitAndRunContLaw epsPrime rf Am bv rin Rout Mw sigma) i
      {Ttc.KV97RoundedEndpointBridge.fineEndpoint ρ z}).toReal =
      kv97SampD M D ρ
        (kv97LazyHitAndRunContLaw epsPrime rf Am bv rin Rout Mw sigma)
        i.val (Ttc.KV97RoundedEndpointBridge.fineEndpoint ρ z) := by
  letI : ∀ j, IsProbabilityMeasure
      (kv97LazyHitAndRunContLaw epsPrime rf Am bv rin Rout Mw sigma j) := fun j => by
    haveI := hsigma j
    infer_instance
  exact Ttc.KV97RoundedEndpointBridge.toReal_kv97SampMeasure_singleton
    M ρ _ i hfinite z hz

/-! ## Transition-count capstone

The following theorem is the strongest cost claim made here.  It is an explicit polynomial
bound on the number of Markov transitions.  It is deliberately not packaged as an
`ExpectedQueryFineSampler`: the repository has no operational hit-and-run kernel connecting
one transition (direction sampling plus exact chord sampling) to a recorded number of facet
or membership queries. -/

theorem kv97LazyHitAndRun_transitionCount_lt
    {A : Type*} {n : ℕ} {D : DNF A} {Jt : Type}
    (epsPrime rf : ℝ)
    (Am : {c : Cube A // c ∈ D} → Jt → Space n)
    (bv : {c : Cube A // c ∈ D} → Jt → ℝ)
    (rin Rout Mw : {c : Cube A // c ∈ D} → ℝ)
    (i : {c : Cube A // c ∈ D}) :
    (lazyHitAndRunUncondSteps n (rin i) (Rout i) (Mw i)
      (epsPrime / (4 *
        (volume (Arlib.KV97.inflated (Am i) (bv i)
          (Arlib.KV97.cOf epsPrime) rf)).toReal)) : ℝ) <
      max 0 (2 ^ 66 * (n : ℝ) ^ 2 * (Rout i) ^ 2 / (rin i) ^ 2 *
        Real.log (8 * Mw i /
          (epsPrime / (4 *
            (volume (Arlib.KV97.inflated (Am i) (bv i)
              (Arlib.KV97.cOf epsPrime) rf)).toReal)) ^ 2)) + 1 :=
  lazyHitAndRunUncondSteps_lt_deadline_add_one _ _ _ _ _

section AxiomCheck

#print axioms lazyHitAndRunUncondDeadline_eq
#print axioms lazyHitAndRunUncondSteps_lt_deadline_add_one
#print axioms kv97LazyHitAndRunContLaw_eq_iterate
#print axioms isProbabilityMeasure_kv97LazyHitAndRunContLaw
#print axioms tvLe_lazyHitAndRunLaw_inflated
#print axioms kv97SamplerOfLazyHitAndRunUncond
#print axioms isProbabilityMeasure_kv97LazyHitAndRunSampMeasure
#print axioms toReal_kv97LazyHitAndRunSampMeasure_singleton
#print axioms kv97LazyHitAndRun_transitionCount_lt

end AxiomCheck

end Ttc
