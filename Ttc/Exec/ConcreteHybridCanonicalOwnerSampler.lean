import Ttc.Exec.CanonicalOwnerPoissonAssembler
import Ttc.Exec.ConcreteHybridAcceptanceCost
import Ttc.Exec.KV97CanonicalAcceptance

/-!
# Concrete hybrid samplers as canonical-owner TTC streams

The finite mark used here is global: an enumerated fine-grid point receives its
global TTC index, while every other point receives the extra drop mark.  Thus a
cube sampler may generate points owned by another cube without rejection; the
canonical-owner projection simply ignores those cells.
-/

namespace Ttc.ConcreteHybridCanonicalOwnerSampler

open MeasureTheory ProbabilityTheory Set
open Ttc.KV97RoundedEndpointBridge
open Ttc.CostedMarkedPoissonIdentified
open Ttc.CostedMarkedPoissonTrajectory
open Ttc.CanonicalOwnerPoissonAssembler
open scoped ENNReal BigOperators Classical Pointwise

variable {n L : Nat}

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- Give points in the range of an injective TTC enumeration their unique
global index; all other points receive the extra drop mark. -/
noncomputable def globalIndexMark (pt : Fin L → State n) (x : State n) : Fin (L + 1) :=
  if h : ∃ s, pt s = x then h.choose.castSucc else Fin.last L

theorem globalIndexMark_apply (pt : Fin L → State n)
    (hpt : Function.Injective pt) (s : Fin L) :
    globalIndexMark pt (pt s) = s.castSucc := by
  unfold globalIndexMark
  split
  · next h =>
    exact congrArg Fin.castSucc (hpt h.choose_spec)
  · next h => exact (h ⟨s, rfl⟩).elim

theorem globalIndexMark_ne_last_imp_mem_range (pt : Fin L → State n) {x : State n}
    (hx : globalIndexMark pt x ≠ Fin.last L) : x ∈ Set.range pt := by
  by_contra h
  have hex : ¬ ∃ s, pt s = x := by simpa [Set.mem_range] using h
  exact hx (dif_neg hex)

theorem measurable_globalIndexMark (pt : Fin L → State n) :
    Measurable (globalIndexMark pt) := by
  apply (measurable_const : Measurable (fun _ : State n => Fin.last L)).measurable_of_countable_ne
  exact (Set.finite_range pt).countable.mono fun x hx =>
    globalIndexMark_ne_last_imp_mem_range pt hx.symm

theorem preimage_globalIndexMark_castSucc (pt : Fin L → State n)
    (hpt : Function.Injective pt) (s : Fin L) :
    globalIndexMark pt ⁻¹' {s.castSucc} = {pt s} := by
  ext x
  constructor
  · intro hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
    by_cases h : ∃ t, pt t = x
    · rw [globalIndexMark, dif_pos h] at hx
      have ht : h.choose = s := Fin.castSucc_injective L hx
      simpa [ht] using h.choose_spec.symm
    · rw [globalIndexMark, dif_neg h] at hx
      exact (Fin.castSucc_ne_last s hx.symm).elim
  · rintro rfl
    simp [globalIndexMark_apply pt hpt s]

/-- The real probability vector obtained by finitely marking a probability
measure. -/
noncomputable def markedProb (pt : Fin L → State n) (mu : Measure (State n)) :
    Fin (L + 1) → Real :=
  fun a => (Measure.map (globalIndexMark pt) mu {a}).toReal

theorem markedProb_nonneg (pt : Fin L → State n) (mu : Measure (State n)) (a) :
    0 ≤ markedProb pt mu a := ENNReal.toReal_nonneg

theorem categoricalLaw_markedProb (pt : Fin L → State n)
    (mu : Measure (State n)) [IsProbabilityMeasure mu] :
    categoricalLaw (markedProb pt mu) = Measure.map (globalIndexMark pt) mu := by
  let nu := Measure.map (globalIndexMark pt) mu
  haveI : IsProbabilityMeasure nu :=
    Measure.isProbabilityMeasure_map (measurable_globalIndexMark pt).aemeasurable
  apply Measure.ext_of_singleton
  intro a
  rw [categoricalLaw_singleton]
  change ENNReal.ofReal (nu {a}).toReal = nu {a}
  exact ENNReal.ofReal_toReal (measure_ne_top nu {a})

theorem markedProb_sum (pt : Fin L → State n)
    (mu : Measure (State n)) [IsProbabilityMeasure mu] :
    ∑ a, markedProb pt mu a = 1 := by
  let nu := Measure.map (globalIndexMark pt) mu
  haveI : IsProbabilityMeasure nu :=
    Measure.isProbabilityMeasure_map (measurable_globalIndexMark pt).aemeasurable
  have hu : categoricalLaw (markedProb pt mu) Set.univ = 1 := by
    rw [categoricalLaw_markedProb, measure_univ]
  unfold categoricalLaw at hu
  rw [Measure.sum_apply _ MeasurableSet.univ] at hu
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    smul_eq_mul, mul_one, tsum_fintype] at hu
  apply ENNReal.ofReal_eq_one.mp
  rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => markedProb_nonneg pt mu a)]
  exact hu

theorem markedProb_castSucc (pt : Fin L → State n)
    (hpt : Function.Injective pt) (mu : Measure (State n))
    [IsProbabilityMeasure mu] (s : Fin L) :
    markedProb pt mu s.castSucc = (mu {pt s}).toReal := by
  rw [markedProb, Measure.map_apply (measurable_globalIndexMark pt)
    (MeasurableSet.singleton _), preimage_globalIndexMark_castSucc pt hpt s]

/-- Convert a family of genuine fine-grid samplers into the exact independent
canonical-owner input expected by the TTC Poisson assembler. -/
noncomputable def canonicalMarkedFamily
    {I : Type*} [Fintype I]
    (pt : Fin L → State n) (target : I → Measure (State n))
    (hprob : ∀ i, IsProbabilityMeasure (target i))
    (S : ∀ i, ExpectedQueryFineSampler (target i))
    (lam : I → Real) (hlam : ∀ i, 0 ≤ lam i) :
    CubeMarkedFamily I L where
  q i := markedProb pt (target i)
  lam := lam
  lam_nonneg := hlam
  q_nonneg i a := markedProb_nonneg pt (target i) a
  q_sum i := by
    letI : IsProbabilityMeasure (target i) := hprob i
    exact markedProb_sum pt (target i)
  sampler i := by
    letI : IsProbabilityMeasure (target i) := hprob i
    exact finiteSamplerOfFine (S i) (globalIndexMark pt)
      (markedProb pt (target i)) (measurable_globalIndexMark pt)
      (categoricalLaw_markedProb pt (target i)).symm

theorem canonicalMarkedFamily_selectedRate
    {I : Type*} [Fintype I]
    (pt : Fin L → State n) (hpt : Function.Injective pt)
    (target : I → Measure (State n)) (hprob : ∀ i, IsProbabilityMeasure (target i))
    (S : ∀ i, ExpectedQueryFineSampler (target i))
    (lam : I → Real) (hlam : ∀ i, 0 ≤ lam i)
    (owner : Fin L → I) (s : Fin L) :
    (canonicalMarkedFamily pt target hprob S lam hlam).lam (owner s) *
        (canonicalMarkedFamily pt target hprob S lam hlam).q (owner s) s.castSucc =
      lam (owner s) * (target (owner s) {pt s}).toReal := by
  letI : IsProbabilityMeasure (target (owner s)) := hprob (owner s)
  change lam (owner s) * markedProb pt (target (owner s)) s.castSucc = _
  rw [markedProb_castSucc pt hpt]

variable {A : Type*}

/-- The cube selected by the actual TTC rate certificate for a global lattice
point.  This is the canonical owner used by the independent-stream assembler. -/
noncomputable def ttcOwner (T : TtcProb A n) (s : Fin T.Lidx) :
    {c : Cube A // c ∈ T.toDNF T.φ} :=
  ⟨(T.theta_eq s).choose, (T.theta_eq s).choose_spec.1⟩

theorem ttcOwner_point_mem (T : TtcProb A n) (s : Fin T.Lidx) :
    T.ptE s ∈ region T.M (ttcOwner T s).val :=
  (T.theta_eq s).choose_spec.2.1

theorem ttcOwner_rate (T : TtcProb A n) (s : Fin T.Lidx) :
    T.sampD (ttcOwner T s).val (T.ptE s) * T.vol (ttcOwner T s).val = T.θ s :=
  (T.theta_eq s).choose_spec.2.2.symm

/-- At the owner cube, the measure realization of any KV97 rounded law has the
point mass prescribed by `kv97SampD`. -/
theorem toReal_kv97SampMeasure_singleton_at_ttcOwner
    (T : TtcProb A n)
    (law : {c : Cube A // c ∈ T.toDNF T.φ} → Measure (State n))
    (hprob : ∀ i, IsProbabilityMeasure (law i)) (s : Fin T.Lidx) :
    (kv97SampMeasure T.M T.ρ law (ttcOwner T s) {T.ptE s}).toReal =
      kv97SampD T.M (T.toDNF T.φ) T.ρ law (ttcOwner T s).val (T.ptE s) := by
  let z : Fin n → Int := fun j => Classical.choose ((T.ptE_mem s).2 j)
  have hx : fineEndpoint T.ρ z = T.ptE s := by
    ext j
    simpa [fineEndpoint] using (Classical.choose_spec ((T.ptE_mem s).2 j)).symm
  have hz : z ∈ integerAcceptance T.M T.ρ (ttcOwner T s).val := by
    change Arlib.KV97.latEmb n z ∈ latticeScale T.ρ • region T.M (ttcOwner T s).val
    refine ⟨T.ptE s, ttcOwner_point_mem T s, ?_⟩
    rw [← hx]
    have hc : latticeScale T.ρ * (latticeScale T.ρ)⁻¹ = (1 : Real) :=
      mul_inv_cancel₀ (latticeScale_ne_zero T.ρ)
    simp [fineEndpoint, smul_smul, hc]
  letI (i : {c : Cube A // c ∈ T.toDNF T.φ}) : IsProbabilityMeasure (law i) :=
    hprob i
  simpa [hx] using toReal_kv97SampMeasure_singleton T.M T.ρ law
    (ttcOwner T s) (T.dilate_intLattice_finite (ttcOwner T s)) z hz

/-- If the per-cube target measures realize the `sampD` used by `T`, the
canonical-owner family has exactly `T.θ` as its retained rate vector. -/
theorem canonicalMarkedFamily_rate_eq_theta
    (T : TtcProb A n)
    (target : {c : Cube A // c ∈ T.toDNF T.φ} → Measure (State n))
    (hprob : ∀ i, IsProbabilityMeasure (target i))
    (S : ∀ i, ExpectedQueryFineSampler (target i))
    (hvol : ∀ i : {c : Cube A // c ∈ T.toDNF T.φ}, 0 ≤ T.vol i.val)
    (hsingle : ∀ s, (target (ttcOwner T s) {T.ptE s}).toReal =
      T.sampD (ttcOwner T s).val (T.ptE s)) (s : Fin T.Lidx) :
    let F := canonicalMarkedFamily T.ptE target hprob S
      (fun i => T.vol i.val) hvol
    F.lam (ttcOwner T s) * F.q (ttcOwner T s) s.castSucc = T.θ s := by
  dsimp only
  rw [canonicalMarkedFamily_selectedRate T.ptE T.ptE_inj target hprob S
    (fun i => T.vol i.val) hvol (ttcOwner T), hsingle, mul_comm, ttcOwner_rate]

/-- Exact TTC trajectory law obtained from independent concrete cube samplers;
non-owner marks are dropped, not retried. -/
theorem map_forgetCost_canonicalMarkedFamily_eq_trajLaw
    (T : TtcProb A n)
    (target : {c : Cube A // c ∈ T.toDNF T.φ} → Measure (State n))
    (hprob : ∀ i, IsProbabilityMeasure (target i))
    (S : ∀ i, ExpectedQueryFineSampler (target i))
    (hvol : ∀ i : {c : Cube A // c ∈ T.toDNF T.φ}, 0 ≤ T.vol i.val)
    (hsingle : ∀ s, (target (ttcOwner T s) {T.ptE s}).toReal =
      T.sampD (ttcOwner T s).val (T.ptE s)) :
    let F := canonicalMarkedFamily T.ptE target hprob S
      (fun i => T.vol i.val) hvol
    Measure.map (Ttc.SequentialCostedPathLumping.pathMap Prod.snd)
        (F.assembledTrajectoryLaw (ttcOwner T)) = Ttc.trajLaw T.θ := by
  dsimp only
  rw [CubeMarkedFamily.map_forgetCost_assembledTrajectoryLaw]
  congr 1
  funext s
  exact canonicalMarkedFamily_rate_eq_theta T target hprob S hvol hsingle s

/-- The corresponding recorded query mean is exactly the volume-weighted sum
of the per-cube sampler means. -/
theorem lintegral_canonicalMarkedFamily_queryCost
    (T : TtcProb A n)
    (target : {c : Cube A // c ∈ T.toDNF T.φ} → Measure (State n))
    (hprob : ∀ i, IsProbabilityMeasure (target i))
    (S : ∀ i, ExpectedQueryFineSampler (target i))
    (hvol : ∀ i : {c : Cube A // c ∈ T.toDNF T.φ}, 0 ≤ T.vol i.val)
    {J : Nat} (hJ : 0 < J) :
    let F := canonicalMarkedFamily T.ptE target hprob S
      (fun i => T.vol i.val) hvol
    (∫⁻ omega, Ttc.CostedInitialThinningTrajectory.finitePrefixQueryCost J omega
        ∂F.assembledTrajectoryLaw (ttcOwner T)) =
      ∑ i, ((T.vol i.val).toNNReal : ENNReal) * (S i).expectedQueries := by
  dsimp only
  exact CubeMarkedFamily.lintegral_finitePrefixQueryCost_assembledTrajectoryLaw
    _ (ttcOwner T) hJ

/-! ## Concrete hybrid specialization -/

abbrev CanonCube (T : TtcProb A n) := {c : Cube A // c ∈ T.toDNF T.φ}
abbrev CanonFacet (T : TtcProb A n) := Fin (Nat.card (FacetIndex (T.toDNF T.φ)))

/-- The actual all-dimensional hybrid continuous law at TTC's canonical
half-space data. -/
noncomputable def canonicalHybridContLaw (T : TtcProb A n)
    (rin Rout delta Mw : CanonCube T → Real)
    (sigma : CanonCube T → Measure (State n)) : CanonCube T → Measure (State n) :=
  Ttc.kv97HybridContLaw T.P.epsPrime T.P.r
    (canonAm T.atoms (T.toDNF T.φ))
    (canonBv T.atoms (T.toDNF T.φ) (latticeScale T.ρ))
    rin Rout delta Mw sigma

/-- The rounded/rejected fine-grid target of the concrete hybrid law. -/
noncomputable def canonicalHybridTarget (T : TtcProb A n)
    (rin Rout delta Mw : CanonCube T → Real)
    (sigma : CanonCube T → Measure (State n)) : CanonCube T → Measure (State n) :=
  fun i => kv97SampMeasure T.M T.ρ
    (canonicalHybridContLaw T rin Rout delta Mw sigma) i

theorem isProbabilityMeasure_canonicalHybridContLaw (T : TtcProb A n)
    (rin Rout delta Mw : CanonCube T → Real)
    (sigma : CanonCube T → Measure (State n))
    (hsigma : ∀ i, IsProbabilityMeasure (sigma i)) (i : CanonCube T) :
    IsProbabilityMeasure (canonicalHybridContLaw T rin Rout delta Mw sigma i) := by
  letI : IsProbabilityMeasure (sigma i) := hsigma i
  unfold canonicalHybridContLaw
  infer_instance

/-- Concrete operational per-cube sampler.  The only analytic premise is the
already-proved hybrid-chain TV estimate; every KV97 acceptance premise is
discharged by `one_eighth_le_roundedMeasure_canonical_of_tvLe`. -/
noncomputable def canonicalHybridFineSampler
    (T : TtcProb A n)
    (rin Rout delta Mw : CanonCube T → Real)
    (sigma : CanonCube T → Measure (State n))
    (hsigma : ∀ i, IsProbabilityMeasure (sigma i))
    (hbounded : ∀ i, Bornology.IsBounded
      (Arlib.KV97.inflated
        (canonAm T.atoms (T.toDNF T.φ) i)
        (canonBv T.atoms (T.toDNF T.φ) (latticeScale T.ρ) i)
        (Arlib.KV97.cOf T.P.epsPrime) T.P.r))
    (hdelta : ∀ i, 0 < delta i) [NeZero n]
    (htv : ∀ i, Arlib.TVLe (canonicalHybridContLaw T rin Rout delta Mw sigma i)
      (Arlib.uniformOn volume
        (Arlib.KV97.inflated
          (canonAm T.atoms (T.toDNF T.φ) i)
          (canonBv T.atoms (T.toDNF T.φ) (latticeScale T.ρ) i)
          (Arlib.KV97.cOf T.P.epsPrime) T.P.r))
      (ENNReal.ofReal (T.P.epsPrime / (4 *
        (volume (Arlib.KV97.inflated
          (canonAm T.atoms (T.toDNF T.φ) i)
          (canonBv T.atoms (T.toDNF T.φ) (latticeScale T.ρ) i)
          (Arlib.KV97.cOf T.P.epsPrime) T.P.r)).toReal))))
    (i : CanonCube T) :
    ExpectedQueryFineSampler (canonicalHybridTarget T rin Rout delta Mw sigma i) := by
  letI : IsProbabilityMeasure (sigma i) := hsigma i
  letI : IsProbabilityMeasure
      (canonicalHybridContLaw T rin Rout delta Mw sigma i) :=
    isProbabilityMeasure_canonicalHybridContLaw T rin Rout delta Mw sigma hsigma i
  apply Ttc.ConcreteHybridAcceptanceCost.expectedQueryKV97HybridConcreteOfEighth
    T.P.epsPrime T.P.r
    (canonAm T.atoms (T.toDNF T.φ))
    (canonBv T.atoms (T.toDNF T.φ) (latticeScale T.ρ))
    rin Rout delta Mw sigma hsigma hbounded hdelta T.M T.ρ i
  exact Ttc.KV97CanonicalAcceptance.one_eighth_le_roundedMeasure_canonical_of_tvLe
    T i (canonicalHybridContLaw T rin Rout delta Mw sigma i) (htv i)

theorem isProbabilityMeasure_canonicalHybridTarget
    (T : TtcProb A n)
    (rin Rout delta Mw : CanonCube T → Real)
    (sigma : CanonCube T → Measure (State n))
    (hsigma : ∀ i, IsProbabilityMeasure (sigma i))
    (hbounded : ∀ i, Bornology.IsBounded
      (Arlib.KV97.inflated
        (canonAm T.atoms (T.toDNF T.φ) i)
        (canonBv T.atoms (T.toDNF T.φ) (latticeScale T.ρ) i)
        (Arlib.KV97.cOf T.P.epsPrime) T.P.r))
    (hdelta : ∀ i, 0 < delta i) [NeZero n]
    (htv : ∀ i, Arlib.TVLe (canonicalHybridContLaw T rin Rout delta Mw sigma i)
      (Arlib.uniformOn volume
        (Arlib.KV97.inflated
          (canonAm T.atoms (T.toDNF T.φ) i)
          (canonBv T.atoms (T.toDNF T.φ) (latticeScale T.ρ) i)
          (Arlib.KV97.cOf T.P.epsPrime) T.P.r))
      (ENNReal.ofReal (T.P.epsPrime / (4 *
        (volume (Arlib.KV97.inflated
          (canonAm T.atoms (T.toDNF T.φ) i)
          (canonBv T.atoms (T.toDNF T.φ) (latticeScale T.ρ) i)
          (Arlib.KV97.cOf T.P.epsPrime) T.P.r)).toReal))))
    (i : CanonCube T) :
    IsProbabilityMeasure (canonicalHybridTarget T rin Rout delta Mw sigma i) := by
  let S := canonicalHybridFineSampler T rin Rout delta Mw sigma hsigma
    hbounded hdelta htv i
  letI : IsProbabilityMeasure S.law := S.probability
  rw [← S.stateMarginal]
  exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable

/-- The fully concrete per-cube family consumed by the canonical-owner Poisson
assembler. -/
noncomputable def concreteHybridCanonicalMarkedFamily
    (T : TtcProb A n)
    (rin Rout delta Mw : CanonCube T → Real)
    (sigma : CanonCube T → Measure (State n))
    (hsigma : ∀ i, IsProbabilityMeasure (sigma i))
    (hbounded : ∀ i, Bornology.IsBounded
      (Arlib.KV97.inflated
        (canonAm T.atoms (T.toDNF T.φ) i)
        (canonBv T.atoms (T.toDNF T.φ) (latticeScale T.ρ) i)
        (Arlib.KV97.cOf T.P.epsPrime) T.P.r))
    (hdelta : ∀ i, 0 < delta i) [NeZero n]
    (htv : ∀ i, Arlib.TVLe (canonicalHybridContLaw T rin Rout delta Mw sigma i)
      (Arlib.uniformOn volume
        (Arlib.KV97.inflated
          (canonAm T.atoms (T.toDNF T.φ) i)
          (canonBv T.atoms (T.toDNF T.φ) (latticeScale T.ρ) i)
          (Arlib.KV97.cOf T.P.epsPrime) T.P.r))
      (ENNReal.ofReal (T.P.epsPrime / (4 *
        (volume (Arlib.KV97.inflated
          (canonAm T.atoms (T.toDNF T.φ) i)
          (canonBv T.atoms (T.toDNF T.φ) (latticeScale T.ρ) i)
          (Arlib.KV97.cOf T.P.epsPrime) T.P.r)).toReal)))) :
    CubeMarkedFamily (CanonCube T) T.Lidx :=
  canonicalMarkedFamily T.ptE
    (canonicalHybridTarget T rin Rout delta Mw sigma)
    (isProbabilityMeasure_canonicalHybridTarget T rin Rout delta Mw sigma hsigma
      hbounded hdelta htv)
    (canonicalHybridFineSampler T rin Rout delta Mw sigma hsigma hbounded hdelta htv)
    (fun i => T.vol i.val) (fun i => (T.vol_pos i.val i.property).le)

/-- For a `TtcProb` whose `sampD` is the concrete hybrid rounded law, the
assembled operational cube streams erase exactly to its TTC trajectory. -/
theorem map_forgetCost_concreteHybridCanonical_eq_trajLaw
    (T : TtcProb A n)
    (rin Rout delta Mw : CanonCube T → Real)
    (sigma : CanonCube T → Measure (State n))
    (hsigma : ∀ i, IsProbabilityMeasure (sigma i))
    (hbounded : ∀ i, Bornology.IsBounded
      (Arlib.KV97.inflated
        (canonAm T.atoms (T.toDNF T.φ) i)
        (canonBv T.atoms (T.toDNF T.φ) (latticeScale T.ρ) i)
        (Arlib.KV97.cOf T.P.epsPrime) T.P.r))
    (hdelta : ∀ i, 0 < delta i) [NeZero n]
    (htv : ∀ i, Arlib.TVLe (canonicalHybridContLaw T rin Rout delta Mw sigma i)
      (Arlib.uniformOn volume
        (Arlib.KV97.inflated
          (canonAm T.atoms (T.toDNF T.φ) i)
          (canonBv T.atoms (T.toDNF T.φ) (latticeScale T.ρ) i)
          (Arlib.KV97.cOf T.P.epsPrime) T.P.r))
      (ENNReal.ofReal (T.P.epsPrime / (4 *
        (volume (Arlib.KV97.inflated
          (canonAm T.atoms (T.toDNF T.φ) i)
          (canonBv T.atoms (T.toDNF T.φ) (latticeScale T.ρ) i)
          (Arlib.KV97.cOf T.P.epsPrime) T.P.r)).toReal))))
    (hsampD : T.sampD = kv97SampD T.M (T.toDNF T.φ) T.ρ
      (canonicalHybridContLaw T rin Rout delta Mw sigma)) :
    Measure.map (Ttc.SequentialCostedPathLumping.pathMap Prod.snd)
        ((concreteHybridCanonicalMarkedFamily T rin Rout delta Mw sigma hsigma
          hbounded hdelta htv).assembledTrajectoryLaw (ttcOwner T)) =
      Ttc.trajLaw T.θ := by
  apply map_forgetCost_canonicalMarkedFamily_eq_trajLaw T
    (canonicalHybridTarget T rin Rout delta Mw sigma)
    (isProbabilityMeasure_canonicalHybridTarget T rin Rout delta Mw sigma hsigma
      hbounded hdelta htv)
    (canonicalHybridFineSampler T rin Rout delta Mw sigma hsigma hbounded hdelta htv)
    (fun i => (T.vol_pos i.val i.property).le)
  intro s
  unfold canonicalHybridTarget
  rw [toReal_kv97SampMeasure_singleton_at_ttcOwner T
    (canonicalHybridContLaw T rin Rout delta Mw sigma)
    (fun i => isProbabilityMeasure_canonicalHybridContLaw T rin Rout delta Mw sigma hsigma i)]
  rw [hsampD]

#print axioms globalIndexMark_apply
#print axioms measurable_globalIndexMark
#print axioms preimage_globalIndexMark_castSucc
#print axioms categoricalLaw_markedProb
#print axioms markedProb_sum
#print axioms markedProb_castSucc
#print axioms canonicalMarkedFamily
#print axioms canonicalMarkedFamily_selectedRate
#print axioms ttcOwner_point_mem
#print axioms ttcOwner_rate
#print axioms toReal_kv97SampMeasure_singleton_at_ttcOwner
#print axioms canonicalMarkedFamily_rate_eq_theta
#print axioms map_forgetCost_canonicalMarkedFamily_eq_trajLaw
#print axioms lintegral_canonicalMarkedFamily_queryCost
#print axioms canonicalHybridFineSampler
#print axioms concreteHybridCanonicalMarkedFamily
#print axioms map_forgetCost_concreteHybridCanonical_eq_trajLaw

end Ttc.ConcreteHybridCanonicalOwnerSampler
