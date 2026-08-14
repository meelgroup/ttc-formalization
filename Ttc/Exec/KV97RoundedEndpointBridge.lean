/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Exec.CostedKV97Rounding
import Ttc.Sampler.Construct

/-!
# Operational randomized rounding versus `kv97SampD`

`Ttc.kv97SampD` is a real-valued point-mass formula.  The executable object built in
`CostedKV97Rounding` is instead a probability measure on integer vectors, conditioned on
the rounded vector lying in the dilated body.  This file records the exact bridge between
the two presentations and keeps the sole remaining normalization obligation explicit.
-/

namespace Ttc.KV97RoundedEndpointBridge

open MeasureTheory ProbabilityTheory Function Set
open Arlib Arlib.Probability Arlib.Lattice Arlib.Lattice.Rounding
open Ttc.CostedKV97Rounding
open scoped ENNReal Classical Pointwise

variable {A : Type*} {n : Nat} {D : DNF A}

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev LatticePoint (n : Nat) := Fin n -> Int

/-- Integer vectors accepted by the KV97 rejection step for cube `i`. -/
def integerAcceptance (M : A -> Set (State n)) (rho : Int) (i : Cube A) :
    Set (LatticePoint n) :=
  Arlib.KV97.latEmb n ⁻¹' (latticeScale rho • region M i)

theorem measurableSet_integerAcceptance (M : A -> Set (State n)) (rho : Int)
    (i : Cube A) : MeasurableSet (integerAcceptance M rho i) := by
  exact MeasurableSet.of_discrete

/-- Undo the dilation after integer randomized rounding. -/
noncomputable def fineEndpoint (rho : Int) (z : LatticePoint n) : State n :=
  (latticeScale rho)⁻¹ • Arlib.KV97.latEmb n z

theorem measurable_fineEndpoint (rho : Int) :
    Measurable (fineEndpoint (n := n) rho) := by
  exact measurable_of_countable _

theorem injective_fineEndpoint (rho : Int) :
    Function.Injective (fineEndpoint (n := n) rho) := by
  intro z w hzw
  apply Arlib.KV97.injective_latEmb
  have h := congrArg (fun x : State n => latticeScale rho • x) hzw
  have hc : latticeScale rho * (latticeScale rho)⁻¹ = (1 : Real) :=
    mul_inv_cancel₀ (latticeScale_ne_zero rho)
  simpa [fineEndpoint, smul_smul, hc] using h

theorem preimage_singleton_fineEndpoint (rho : Int) (z : LatticePoint n) :
    fineEndpoint (n := n) rho ⁻¹' {fineEndpoint rho z} = {z} := by
  ext w
  simp only [mem_preimage, mem_singleton_iff]
  exact (injective_fineEndpoint rho).eq_iff

/-- The ordinary fine-grid endpoint law obtained by conditioning the rounded integer
vector and undoing the dilation. -/
noncomputable def conditionedFineEndpointLaw (mu : Measure (State n))
    (M : A -> Set (State n)) (rho : Int) (i : Cube A) : Measure (State n) :=
  Measure.map (fineEndpoint rho)
    (Arlib.condOn (roundedMeasure mu) (integerAcceptance M rho i))

/-- The costed fine-grid endpoint law. -/
noncomputable def costedFineEndpointLaw (xi : Measure (ENNReal × State n))
    (M : A -> Set (State n)) (rho : Int) (i : Cube A) :
    Measure (ENNReal × State n) :=
  Measure.map (fun q : ENNReal × LatticePoint n => (q.1, fineEndpoint rho q.2))
    (costedKV97RejectionLaw xi (integerAcceptance M rho i))

theorem measurable_costedFineEndpointMap (rho : Int) :
    Measurable (fun q : ENNReal × LatticePoint n => (q.1, fineEndpoint rho q.2)) :=
  measurable_fst.prodMk ((measurable_fineEndpoint rho).comp measurable_snd)

theorem map_snd_costedFineEndpointLaw
    (xi : Measure (ENNReal × State n)) [IsProbabilityMeasure xi]
    (M : A -> Set (State n)) (rho : Int) (i : Cube A)
    (hpos : 0 < roundedMeasure (Measure.map Prod.snd xi)
      (integerAcceptance M rho i)) :
    Measure.map Prod.snd (costedFineEndpointLaw xi M rho i) =
      conditionedFineEndpointLaw (Measure.map Prod.snd xi) M rho i := by
  rw [costedFineEndpointLaw, conditionedFineEndpointLaw,
    Measure.map_map measurable_snd (measurable_costedFineEndpointMap rho)]
  have hcomp :
      Prod.snd ∘ (fun q : ENNReal × LatticePoint n => (q.1, fineEndpoint rho q.2)) =
        fineEndpoint rho ∘ Prod.snd := rfl
  rw [hcomp, ← Measure.map_map (measurable_fineEndpoint rho) measurable_snd,
    map_snd_costedKV97RejectionLaw xi
      (measurableSet_integerAcceptance M rho i) hpos]

theorem lintegral_fst_costedFineEndpointLaw
    (xi : Measure (ENNReal × State n)) [IsProbabilityMeasure xi]
    (M : A -> Set (State n)) (rho : Int) (i : Cube A) :
    (∫⁻ y, y.1 ∂costedFineEndpointLaw xi M rho i) =
      (roundedMeasure (Measure.map Prod.snd xi) (integerAcceptance M rho i))⁻¹ *
        ((∫⁻ z, z.1 ∂xi) + 1) := by
  rw [costedFineEndpointLaw,
    lintegral_map measurable_fst (measurable_costedFineEndpointMap rho)]
  exact lintegral_fst_costedKV97RejectionLaw xi
    (measurableSet_integerAcceptance M rho i)

/-- An acceptance lower bound and a continuous-endpoint query bound give the expected
query bound used by a TTC runtime theorem.  In particular, the KV97 `1/8` acceptance
theorem can be supplied as `haccept` without changing the operational law. -/
theorem lintegral_fst_costedFineEndpointLaw_le
    (xi : Measure (ENNReal × State n)) [IsProbabilityMeasure xi]
    (M : A -> Set (State n)) (rho : Int) (i : Cube A)
    {acceptLower continuousBound : ENNReal}
    (haccept : acceptLower ≤
      roundedMeasure (Measure.map Prod.snd xi) (integerAcceptance M rho i))
    (hcontinuous : (∫⁻ z, z.1 ∂xi) ≤ continuousBound) :
    (∫⁻ y, y.1 ∂costedFineEndpointLaw xi M rho i) ≤
      acceptLower⁻¹ * (continuousBound + 1) := by
  rw [lintegral_fst_costedFineEndpointLaw]
  exact mul_le_mul' (ENNReal.inv_le_inv.mpr haccept) (add_le_add hcontinuous le_rfl)

/-- A rounded singleton has exactly the `prodTent` weight used by `kv97SampD`. -/
theorem roundedMeasure_singleton (mu : Measure (State n))
    (z : LatticePoint n) :
    roundedMeasure mu {z} =
      ∫⁻ p, ENNReal.ofReal (prodTent (Arlib.KV97.latEmb n z) p) ∂mu := by
  rw [roundedMeasure, Measure.bind_apply (MeasurableSet.singleton z) (by fun_prop)]
  apply lintegral_congr
  intro p
  change roundLaw (WithLp.ofLp p) {z} = _
  rw [roundLaw_singleton]
  rfl

theorem toReal_roundedMeasure_singleton (mu : Measure (State n))
    [IsProbabilityMeasure mu] (z : LatticePoint n) :
    (roundedMeasure mu {z}).toReal =
      ∫ p, prodTent (Arlib.KV97.latEmb n z) p ∂mu := by
  rw [roundedMeasure_singleton,
    ← ofReal_integral_eq_lintegral_ofReal]
  · rw [ENNReal.toReal_ofReal]
    exact integral_nonneg fun p => prodTent_nonneg _ _
  · exact Integrable.of_bound
      (continuous_prodTent (Arlib.KV97.latEmb n z)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (prodTent_nonneg _ _)]
        exact Arlib.PointwiseRoute.prodTent_le_one (Arlib.KV97.latEmb n z) p)
  · exact Filter.Eventually.of_forall fun p => prodTent_nonneg _ _

/-- The one explicit bridge obligation between the two normalizer presentations. -/
def NormalizerIdentified (mu : Measure (State n)) (M : A -> Set (State n))
    (rho : Int) (i : {c : Cube A // c ∈ D}) : Prop :=
  (roundedMeasure mu (integerAcceptance M rho i.val)).toReal =
    ∑ᶠ k : ((latticeScale rho • region M i.val) ∩ intLattice n : Set (State n)),
      ∫ p, prodTent (k : State n) p ∂mu

/-- The accepted integer vectors and the integer lattice points of the dilated body are
the same finite index set, expressed as an equivalence of subtypes. -/
noncomputable def acceptedEmbedding (M : A -> Set (State n)) (rho : Int) (i : Cube A) :
    {z : LatticePoint n // z ∈ integerAcceptance M rho i} ->
      ((latticeScale rho • region M i) ∩ intLattice n : Set (State n)) :=
  fun z => ⟨Arlib.KV97.latEmb n z.1, z.2, by
    intro j
    exact ⟨z.1 j, rfl⟩⟩

theorem bijective_acceptedEmbedding (M : A -> Set (State n)) (rho : Int)
    (i : Cube A) : Function.Bijective (acceptedEmbedding M rho i) := by
  constructor
  · intro z w hzw
    apply Subtype.ext
    apply Arlib.KV97.injective_latEmb
    exact congrArg Subtype.val hzw
  · rintro ⟨x, hxP, hxL⟩
    let z : LatticePoint n := fun j => Classical.choose (hxL j)
    have hzx : Arlib.KV97.latEmb n z = x := by
      ext j
      exact (Classical.choose_spec (hxL j)).symm
    refine ⟨⟨z, ?_⟩, Subtype.ext hzx⟩
    change Arlib.KV97.latEmb n z ∈ latticeScale rho • region M i
    rw [hzx]
    exact hxP

noncomputable def acceptedEquiv (M : A -> Set (State n)) (rho : Int)
    (i : Cube A) :
    {z : LatticePoint n // z ∈ integerAcceptance M rho i} ≃
      ((latticeScale rho • region M i) ∩ intLattice n : Set (State n)) :=
  Equiv.ofBijective (acceptedEmbedding M rho i)
    (bijective_acceptedEmbedding M rho i)

/-- `NormalizerIdentified` follows from finiteness of the lattice points in the dilated
body.  This closes the only representation mismatch between the measure-valued rejection
sampler and the `finsum` denominator used by `kv97SampD`. -/
theorem normalizerIdentified_of_finite
    (mu : Measure (State n)) [IsProbabilityMeasure mu]
    (M : A -> Set (State n)) (rho : Int) (i : {c : Cube A // c ∈ D})
    (hfinite : ((latticeScale rho • region M i.val) ∩ intLattice n :
      Set (State n)).Finite) :
    NormalizerIdentified mu M rho i := by
  let e := acceptedEquiv M rho i.val
  letI : Fintype
      ((latticeScale rho • region M i.val) ∩ intLattice n : Set (State n)) :=
    hfinite.fintype
  letI : Fintype {z : LatticePoint n // z ∈ integerAcceptance M rho i.val} :=
    Fintype.ofEquiv _ e.symm
  unfold NormalizerIdentified
  have hrange : Set.range
      (fun z : {z : LatticePoint n // z ∈ integerAcceptance M rho i.val} => z.1) =
      integerAcceptance M rho i.val := by
    ext z
    simp
  rw [← hrange,
    Arlib.KV97.measure_range_eq_sum_singleton (roundedMeasure mu) Subtype.val_injective,
    ENNReal.toReal_sum (fun z _ => measure_ne_top (roundedMeasure mu) {z.1}),
    finsum_eq_sum_of_fintype]
  exact Fintype.sum_equiv e _ _ fun z => by
    rw [toReal_roundedMeasure_singleton]
    rfl

/-- A genuine measure realization of the mass function `kv97SampD`. -/
noncomputable def kv97SampMeasure
    (M : A -> Set (State n)) (rho : Int)
    (law : {c : Cube A // c ∈ D} -> Measure (State n))
    (i : {c : Cube A // c ∈ D}) : Measure (State n) :=
  conditionedFineEndpointLaw (law i) M rho i.val

theorem isProbabilityMeasure_kv97SampMeasure
    (M : A -> Set (State n)) (rho : Int)
    (law : {c : Cube A // c ∈ D} -> Measure (State n))
    [∀ i, IsProbabilityMeasure (law i)]
    (i : {c : Cube A // c ∈ D})
    (hpos : 0 < roundedMeasure (law i) (integerAcceptance M rho i.val)) :
    IsProbabilityMeasure (kv97SampMeasure M rho law i) := by
  unfold kv97SampMeasure conditionedFineEndpointLaw
  letI : IsProbabilityMeasure
      (Arlib.condOn (roundedMeasure (law i)) (integerAcceptance M rho i.val)) :=
    Arlib.isProbabilityMeasure_condOn _ hpos.ne' (measure_ne_top _ _)
  exact Measure.isProbabilityMeasure_map (measurable_fineEndpoint rho).aemeasurable

/-- `Arlib.KV97.roundedLaw` is the specialization of `roundedMeasure` to the
volume-density continuous law used by the repository's KV97 acceptance theorem. -/
theorem roundedMeasure_density_eq_roundedLaw
    (S : Set (State n)) (f : State n -> Real) :
    roundedMeasure ((volume.restrict S).withDensity fun p => ENNReal.ofReal (f p)) =
      Arlib.KV97.roundedLaw S f := by
  rfl

/-- On every accepted rounded point, the operational conditional probability is exactly
the point mass specified by `Ttc.kv97SampD`. -/
theorem toReal_condOn_singleton_eq_kv97SampD
    (M : A -> Set (State n)) (rho : Int)
    (law : {c : Cube A // c ∈ D} -> Measure (State n))
    [∀ i, IsProbabilityMeasure (law i)]
    (i : {c : Cube A // c ∈ D})
    (hnorm : NormalizerIdentified (law i) M rho i)
    (z : LatticePoint n) (hz : z ∈ integerAcceptance M rho i.val) :
    (Arlib.condOn (roundedMeasure (law i))
      (integerAcceptance M rho i.val) {z}).toReal =
      kv97SampD M D rho law i.val (fineEndpoint rho z) := by
  rw [Arlib.condOn_apply _ (measurableSet_integerAcceptance M rho i.val)
      (MeasurableSet.singleton z), Set.singleton_inter_of_mem hz,
    ENNReal.toReal_div, toReal_roundedMeasure_singleton,
    kv97SampD_apply M rho law i (fineEndpoint rho z), hnorm]
  congr 2
  have hc : latticeScale rho * (latticeScale rho)⁻¹ = (1 : Real) :=
    mul_inv_cancel₀ (latticeScale_ne_zero rho)
  simp [fineEndpoint, smul_smul, hc]

/-- Measure-level endpoint version of `toReal_condOn_singleton_eq_kv97SampD`:
after undoing the lattice dilation, the conditioned operational endpoint law has exactly
the `kv97SampD` mass at every accepted rounded point. -/
theorem toReal_conditionedFineEndpointLaw_singleton_eq_kv97SampD
    (M : A -> Set (State n)) (rho : Int)
    (law : {c : Cube A // c ∈ D} -> Measure (State n))
    [∀ i, IsProbabilityMeasure (law i)]
    (i : {c : Cube A // c ∈ D})
    (hnorm : NormalizerIdentified (law i) M rho i)
    (z : LatticePoint n) (hz : z ∈ integerAcceptance M rho i.val) :
    (conditionedFineEndpointLaw (law i) M rho i.val
      {fineEndpoint rho z}).toReal =
      kv97SampD M D rho law i.val (fineEndpoint rho z) := by
  rw [conditionedFineEndpointLaw,
    Measure.map_apply (measurable_fineEndpoint rho) (MeasurableSet.singleton _),
    preimage_singleton_fineEndpoint]
  exact toReal_condOn_singleton_eq_kv97SampD M rho law i hnorm z hz

theorem toReal_kv97SampMeasure_singleton
    (M : A -> Set (State n)) (rho : Int)
    (law : {c : Cube A // c ∈ D} -> Measure (State n))
    [∀ i, IsProbabilityMeasure (law i)]
    (i : {c : Cube A // c ∈ D})
    (hfinite : ((latticeScale rho • region M i.val) ∩ intLattice n :
      Set (State n)).Finite)
    (z : LatticePoint n) (hz : z ∈ integerAcceptance M rho i.val) :
    (kv97SampMeasure M rho law i {fineEndpoint rho z}).toReal =
      kv97SampD M D rho law i.val (fineEndpoint rho z) := by
  exact toReal_conditionedFineEndpointLaw_singleton_eq_kv97SampD
    M rho law i (normalizerIdentified_of_finite (law i) M rho i hfinite) z hz

/-- A compact, honest expected-query sampler package for TTC consumers. -/
structure ExpectedQueryFineSampler (target : Measure (State n)) where
  law : Measure (ENNReal × State n)
  probability : IsProbabilityMeasure law
  stateMarginal : Measure.map Prod.snd law = target
  expectedQueries : ENNReal
  expectedQueries_eq : (∫⁻ z, z.1 ∂law) = expectedQueries

/-- The operational KV97 rejection sampler as an expected-query sampler. -/
noncomputable def expectedQueryFineSampler
    (xi : Measure (ENNReal × State n)) [IsProbabilityMeasure xi]
    (M : A -> Set (State n)) (rho : Int) (i : Cube A)
    (hpos : 0 < roundedMeasure (Measure.map Prod.snd xi)
      (integerAcceptance M rho i)) :
    ExpectedQueryFineSampler
      (conditionedFineEndpointLaw (Measure.map Prod.snd xi) M rho i) where
  law := costedFineEndpointLaw xi M rho i
  probability := by
    unfold costedFineEndpointLaw costedKV97RejectionLaw
    letI : IsProbabilityMeasure
        (Ttc.CostedWarmPhaseRejection.costedRejectionLaw
          (costedRoundedLaw xi) (integerAcceptance M rho i)) :=
      Ttc.CostedWarmPhaseRejection.isProbabilityMeasure_costedRejectionLaw _
        (measurableSet_integerAcceptance M rho i)
    exact Measure.isProbabilityMeasure_map
      (measurable_costedFineEndpointMap rho).aemeasurable
  stateMarginal := map_snd_costedFineEndpointLaw xi M rho i hpos
  expectedQueries :=
    (roundedMeasure (Measure.map Prod.snd xi) (integerAcceptance M rho i))⁻¹ *
      ((∫⁻ z, z.1 ∂xi) + 1)
  expectedQueries_eq := lintegral_fst_costedFineEndpointLaw xi M rho i

/-- The same package with its target named as the measure realization of `kv97SampD`.
`toReal_kv97SampMeasure_singleton` supplies the exact mass-function specification. -/
noncomputable def expectedQueryKV97Sampler
    (xi : Measure (ENNReal × State n)) [IsProbabilityMeasure xi]
    (M : A -> Set (State n)) (rho : Int)
    (law : {c : Cube A // c ∈ D} -> Measure (State n))
    (i : {c : Cube A // c ∈ D})
    (hmarg : Measure.map Prod.snd xi = law i)
    (hpos : 0 < roundedMeasure (law i) (integerAcceptance M rho i.val)) :
    ExpectedQueryFineSampler (kv97SampMeasure M rho law i) :=
  let S := expectedQueryFineSampler xi M rho i.val (by simpa [hmarg] using hpos)
  { law := S.law
    probability := S.probability
    stateMarginal := S.stateMarginal.trans (by
      simpa only [kv97SampMeasure, hmarg])
    expectedQueries := S.expectedQueries
    expectedQueries_eq := S.expectedQueries_eq }

section KV97Acceptance

variable {J ι : Type*} [Fintype ι]

/-- The repository's measure-valued KV97 Lemma 1, transported to the exact acceptance
event used by `costedFineEndpointLaw`. -/
theorem one_eighth_le_roundedMeasure_integerAcceptance_of_kv97
    (xi : Measure (ENNReal × State n)) [IsProbabilityMeasure xi]
    (M : A -> Set (State n)) (rho : Int) (i : Cube A)
    {Amat : J -> State n} {bvec : J -> Real}
    {cen : State n} {gamma c r eps escape eta : Real}
    {f : State n -> Real} {lat : ι -> LatticePoint n}
    (hmarg : Measure.map Prod.snd xi =
      (volume.restrict (Arlib.KV97.inflated Amat bvec c r)).withDensity
        fun p => ENNReal.ofReal (f p))
    (hgamma : 0 < gamma) (hc : 0 ≤ c)
    (hball : Metric.ball cen gamma ⊆ Arlib.Polytope.body Amat bvec)
    (hfin : volume (Arlib.Polytope.body Amat bvec) ≠ ⊤)
    (heta0 : 0 ≤ eta) (heta : eta ≤ 1 / 4)
    (heps : eps ≤ 1 / 4) (hescape : escape ≤ 1 / 4)
    (hlow : ∀ j, (1 - eps) * (1 - escape) /
        (volume (Arlib.KV97.inflated Amat bvec c r)).toReal ≤
      ∫ p in Arlib.KV97.inflated Amat bvec c r,
        f p * prodTent (Arlib.KV97.latEmb n (lat j)) p)
    (hlattice_nonconv :
      (volume (Arlib.Polytope.body Amat bvec)).toReal ≤
        (1 + eta) * (Fintype.card ι : Real))
    (hthin : Arlib.KV97.kappaOf c r / gamma ≤ 1 / (n : Real))
    (hlat : Function.Injective lat)
    (henum : ∀ z, Arlib.KV97.latEmb n z ∈ latticeScale rho • region M i ↔
      ∃ j, lat j = z)
    (hf : Measurable f) (hf0 : ∀ p, 0 ≤ f p)
    (hint : ∀ j, IntegrableOn
      (fun p => f p * prodTent (Arlib.KV97.latEmb n (lat j)) p)
      (Arlib.KV97.inflated Amat bvec c r)) :
    (1 : Real) / 8 ≤
      (roundedMeasure (Measure.map Prod.snd xi) (integerAcceptance M rho i)).toReal := by
  rw [hmarg, roundedMeasure_density_eq_roundedLaw]
  exact Arlib.KV97.toReal_roundedLaw_ge_one_eighth
    hgamma hc hball hfin heta0 heta heps hescape hlow hlattice_nonconv hthin
    hlat henum hf hf0 hint

/-- Concrete expected actual membership-query bound obtained from KV97's proved `1/8`
acceptance theorem.  The inverse factor on the right is exactly `8`; it is left in
`ENNReal` form to compose without coercion losses with existing execution costs. -/
theorem lintegral_fst_costedFineEndpointLaw_le_of_kv97
    (xi : Measure (ENNReal × State n)) [IsProbabilityMeasure xi]
    (M : A -> Set (State n)) (rho : Int) (i : Cube A)
    {Amat : J -> State n} {bvec : J -> Real}
    {cen : State n} {gamma c r eps escape eta : Real}
    {f : State n -> Real} {lat : ι -> LatticePoint n}
    {continuousBound : ENNReal}
    (hmarg : Measure.map Prod.snd xi =
      (volume.restrict (Arlib.KV97.inflated Amat bvec c r)).withDensity
        fun p => ENNReal.ofReal (f p))
    (hgamma : 0 < gamma) (hc : 0 ≤ c)
    (hball : Metric.ball cen gamma ⊆ Arlib.Polytope.body Amat bvec)
    (hfin : volume (Arlib.Polytope.body Amat bvec) ≠ ⊤)
    (heta0 : 0 ≤ eta) (heta : eta ≤ 1 / 4)
    (heps : eps ≤ 1 / 4) (hescape : escape ≤ 1 / 4)
    (hlow : ∀ j, (1 - eps) * (1 - escape) /
        (volume (Arlib.KV97.inflated Amat bvec c r)).toReal ≤
      ∫ p in Arlib.KV97.inflated Amat bvec c r,
        f p * prodTent (Arlib.KV97.latEmb n (lat j)) p)
    (hlattice_nonconv :
      (volume (Arlib.Polytope.body Amat bvec)).toReal ≤
        (1 + eta) * (Fintype.card ι : Real))
    (hthin : Arlib.KV97.kappaOf c r / gamma ≤ 1 / (n : Real))
    (hlat : Function.Injective lat)
    (henum : ∀ z, Arlib.KV97.latEmb n z ∈ latticeScale rho • region M i ↔
      ∃ j, lat j = z)
    (hf : Measurable f) (hf0 : ∀ p, 0 ≤ f p)
    (hint : ∀ j, IntegrableOn
      (fun p => f p * prodTent (Arlib.KV97.latEmb n (lat j)) p)
      (Arlib.KV97.inflated Amat bvec c r))
    (hcontinuous : (∫⁻ z, z.1 ∂xi) ≤ continuousBound) :
    (∫⁻ y, y.1 ∂costedFineEndpointLaw xi M rho i) ≤
      (ENNReal.ofReal ((1 : Real) / 8))⁻¹ * (continuousBound + 1) := by
  have hreal := one_eighth_le_roundedMeasure_integerAcceptance_of_kv97
    xi M rho i hmarg hgamma hc hball hfin heta0 heta heps hescape hlow
      hlattice_nonconv hthin hlat henum hf hf0 hint
  exact lintegral_fst_costedFineEndpointLaw_le xi M rho i
    (ENNReal.ofReal_le_of_le_toReal hreal) hcontinuous

end KV97Acceptance

#print axioms map_snd_costedFineEndpointLaw
#print axioms lintegral_fst_costedFineEndpointLaw
#print axioms lintegral_fst_costedFineEndpointLaw_le
#print axioms toReal_condOn_singleton_eq_kv97SampD
#print axioms toReal_conditionedFineEndpointLaw_singleton_eq_kv97SampD
#print axioms expectedQueryFineSampler
#print axioms expectedQueryKV97Sampler
#print axioms one_eighth_le_roundedMeasure_integerAcceptance_of_kv97
#print axioms lintegral_fst_costedFineEndpointLaw_le_of_kv97

end Ttc.KV97RoundedEndpointBridge
