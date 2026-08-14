import Ttc.Exec.ConcreteHybridCanonicalOwnerSampler
import Ttc.Exec.CostedCanonicalOwnerTTCPlugin
import Ttc.Sampler.RatesNonneg

/-!
# Canonical-owner execution for the hybrid polynomial sampler

This file deliberately introduces `polyHybridSampD` and `polyHybridRates`
instead of identifying them with the legacy `polySampD`, whose continuous law
is the non-lazy hit-and-run law in every dimension.  The concrete operational
sampler uses the newer lazy hit-and-run/ball-walk hybrid law.
-/

namespace Ttc.ConcreteHybridCanonicalOwnerPoly

open MeasureTheory ProbabilityTheory Set Pointwise
open Ttc.KV97RoundedEndpointBridge
open Ttc.ConcreteHybridCanonicalOwnerSampler
open Ttc.CanonicalOwnerPoissonAssembler
open scoped ENNReal BigOperators Classical

variable {A : Type*} {n : Nat}
variable (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)

abbrev CubeIndex :=
  {c : Cube A // c ∈ toDNFd (preprocess atoms phi)}

abbrev FacetIndex' := Fin (Nat.card (FacetIndex (toDNFd (preprocess atoms phi))))

noncomputable abbrev M := atomSet (algAtoms atoms phi eps delta)
noncomputable abbrev D := toDNFd (preprocess atoms phi)
noncomputable abbrev rho := algPrec atoms phi eps delta
noncomputable abbrev pt := algEnum atoms phi eps delta

/-- The continuous law actually executed by the all-dimensional operational
sampler. -/
noncomputable def polyHybridContLaw
    (rin Rout step Mw : CubeIndex atoms phi → Real)
    (sigma : CubeIndex atoms phi → Measure (Space n)) :
    CubeIndex atoms phi → Measure (Space n) :=
  kv97HybridContLaw (algBlock atoms phi eps delta).epsPrime
    (algBlock atoms phi eps delta).r
    (canonAm (algAtoms atoms phi eps delta) (D atoms phi))
    (canonBv (algAtoms atoms phi eps delta) (D atoms phi)
      (latticeScale (rho atoms phi eps delta)))
    rin Rout step Mw sigma

/-- The distinct discrete law induced by the operational hybrid chain. -/
noncomputable def polyHybridSampD
    (rin Rout step Mw : CubeIndex atoms phi → Real)
    (sigma : CubeIndex atoms phi → Measure (Space n)) :
    Cube A → Space n → Real :=
  kv97SampD (M atoms phi eps delta) (D atoms phi)
    (rho atoms phi eps delta)
    (polyHybridContLaw atoms phi eps delta rin Rout step Mw sigma)

/-- TTC level-zero rates for the operational hybrid sampler. -/
noncomputable def polyHybridRates
    (V : VolumeAlgorithm n) (omega : V.Ω)
    (rin Rout step Mw : CubeIndex atoms phi → Real)
    (sigma : CubeIndex atoms phi → Measure (Space n)) :
    Fin (algIndex atoms phi eps delta) → Real :=
  rates (M atoms phi eps delta) (preprocess atoms phi) (D atoms phi)
    (rho atoms phi eps delta)
    (polyHybridSampD atoms phi eps delta rin Rout step Mw sigma)
    (polyVol atoms phi eps delta V omega)

/-- Canonical owner in the actual preprocessed TTC decomposition. -/
noncomputable def polyOwner
    (hle : HasLatticeEnum (M atoms phi eps delta) (preprocess atoms phi)
      (rho atoms phi eps delta))
    (s : Fin (algIndex atoms phi eps delta)) : CubeIndex atoms phi :=
  ⟨cubeAt (M atoms phi eps delta) (preprocess atoms phi) (D atoms phi)
      (rho atoms phi eps delta) s,
    (cubeAt_spec (toDNFd_isDNFOf _) hle s).1⟩

theorem polyOwner_point_mem
    (hle : HasLatticeEnum (M atoms phi eps delta) (preprocess atoms phi)
      (rho atoms phi eps delta))
    (s : Fin (algIndex atoms phi eps delta)) :
    pt atoms phi eps delta s ∈
      region (M atoms phi eps delta) (polyOwner atoms phi eps delta hle s).val :=
  (cubeAt_spec (toDNFd_isDNFOf _) hle s).2

/-- Fine-grid target of one concrete hybrid cube sampler. -/
noncomputable def polyHybridTarget
    (rin Rout step Mw : CubeIndex atoms phi → Real)
    (sigma : CubeIndex atoms phi → Measure (Space n))
    (i : CubeIndex atoms phi) : Measure (Space n) :=
  kv97SampMeasure (M atoms phi eps delta) (rho atoms phi eps delta)
    (polyHybridContLaw atoms phi eps delta rin Rout step Mw sigma) i

/-- The target singleton at an owned global lattice point is exactly the
hybrid `sampD` mass. -/
theorem toReal_polyHybridTarget_singleton_owner
    (hle : HasLatticeEnum (M atoms phi eps delta) (preprocess atoms phi)
      (rho atoms phi eps delta))
    (rin Rout step Mw : CubeIndex atoms phi → Real)
    (sigma : CubeIndex atoms phi → Measure (Space n))
    (hsigma : ∀ i, IsProbabilityMeasure (sigma i))
    (s : Fin (algIndex atoms phi eps delta)) :
    (polyHybridTarget atoms phi eps delta rin Rout step Mw sigma
      (polyOwner atoms phi eps delta hle s) {pt atoms phi eps delta s}).toReal =
      polyHybridSampD atoms phi eps delta rin Rout step Mw sigma
        (polyOwner atoms phi eps delta hle s).val (pt atoms phi eps delta s) := by
  let x := pt atoms phi eps delta s
  let i := polyOwner atoms phi eps delta hle s
  let z : Fin n → Int := fun j => Classical.choose ((latticeEnum_mem hle s).2 j)
  have hx : fineEndpoint (rho atoms phi eps delta) z = x := by
    change fineEndpoint (rho atoms phi eps delta) z =
      latticeEnum (M atoms phi eps delta) (preprocess atoms phi)
        (rho atoms phi eps delta) s
    ext j
    simpa [fineEndpoint] using
      (Classical.choose_spec ((latticeEnum_mem hle s).2 j)).symm
  have hz : z ∈ integerAcceptance (M atoms phi eps delta)
      (rho atoms phi eps delta) i.val := by
    change Arlib.KV97.latEmb n z ∈
      latticeScale (rho atoms phi eps delta) • region (M atoms phi eps delta) i.val
    refine ⟨x, polyOwner_point_mem atoms phi eps delta hle s, ?_⟩
    rw [← hx]
    have hc : latticeScale (rho atoms phi eps delta) *
        (latticeScale (rho atoms phi eps delta))⁻¹ = (1 : Real) :=
      mul_inv_cancel₀ (latticeScale_ne_zero _)
    simp [fineEndpoint, smul_smul, hc]
  have hfine : (region (M atoms phi eps delta) i.val ∩
      fineLattice n (latticeScale (rho atoms phi eps delta))).Finite := by
    refine (Set.finite_range (pt atoms phi eps delta)).subset ?_
    rintro y ⟨hyreg, hylat⟩
    have hysol : y ∈ sol (M atoms phi eps delta) (preprocess atoms phi) :=
      (toDNFd_isDNFOf (preprocess atoms phi) (induced (M atoms phi eps delta) y)).1
        ⟨i.val, i.property, hyreg⟩
    obtain ⟨t, ht⟩ := latticeEnum_onto hle y ⟨hysol, hylat⟩
    exact ⟨t, ht⟩
  have hdil : ((latticeScale (rho atoms phi eps delta) •
      region (M atoms phi eps delta) i.val) ∩ intLattice n : Set (Space n)).Finite := by
    rw [← smul_inter_fineLattice (latticeScale_ne_zero _) _]
    exact hfine.image _
  letI (j : CubeIndex atoms phi) : IsProbabilityMeasure
      (polyHybridContLaw atoms phi eps delta rin Rout step Mw sigma j) := by
    unfold polyHybridContLaw
    letI : IsProbabilityMeasure (sigma j) := hsigma j
    infer_instance
  simpa [polyHybridTarget, polyHybridSampD, hx, x, i] using
    toReal_kv97SampMeasure_singleton (M atoms phi eps delta)
      (rho atoms phi eps delta)
      (polyHybridContLaw atoms phi eps delta rin Rout step Mw sigma)
      i hdil z hz

/-- Concrete expected-query sampler for a cube, with no sampler-law binder.
The quantitative `1/8` certificate is kept explicit here because the direct
algorithm data are not bundled as a `TtcProb`. -/
noncomputable def polyHybridFineSampler
    (rin Rout step Mw : CubeIndex atoms phi → Real)
    (sigma : CubeIndex atoms phi → Measure (Space n))
    (hsigma : ∀ i, IsProbabilityMeasure (sigma i))
    (hbounded : ∀ i, Bornology.IsBounded
      (Arlib.KV97.inflated
        (canonAm (algAtoms atoms phi eps delta) (D atoms phi) i)
        (canonBv (algAtoms atoms phi eps delta) (D atoms phi)
          (latticeScale (rho atoms phi eps delta)) i)
        (Arlib.KV97.cOf (algBlock atoms phi eps delta).epsPrime)
        (algBlock atoms phi eps delta).r))
    (hstep : ∀ i, 0 < step i) [NeZero n]
    (heighth : ∀ i, ENNReal.ofReal ((1 : Real) / 8) ≤
      Ttc.CostedKV97Rounding.roundedMeasure
        (polyHybridContLaw atoms phi eps delta rin Rout step Mw sigma i)
        (integerAcceptance (M atoms phi eps delta) (rho atoms phi eps delta) i.val))
    (i : CubeIndex atoms phi) :
    ExpectedQueryFineSampler
      (polyHybridTarget atoms phi eps delta rin Rout step Mw sigma i) :=
  Ttc.ConcreteHybridAcceptanceCost.expectedQueryKV97HybridConcreteOfEighth
    (algBlock atoms phi eps delta).epsPrime (algBlock atoms phi eps delta).r
    (canonAm (algAtoms atoms phi eps delta) (D atoms phi))
    (canonBv (algAtoms atoms phi eps delta) (D atoms phi)
      (latticeScale (rho atoms phi eps delta)))
    rin Rout step Mw sigma hsigma hbounded hstep (M atoms phi eps delta)
    (rho atoms phi eps delta) i (heighth i)

theorem isProbabilityMeasure_polyHybridTarget
    (rin Rout step Mw : CubeIndex atoms phi → Real)
    (sigma : CubeIndex atoms phi → Measure (Space n))
    (hsigma : ∀ i, IsProbabilityMeasure (sigma i))
    (hbounded : ∀ i, Bornology.IsBounded
      (Arlib.KV97.inflated
        (canonAm (algAtoms atoms phi eps delta) (D atoms phi) i)
        (canonBv (algAtoms atoms phi eps delta) (D atoms phi)
          (latticeScale (rho atoms phi eps delta)) i)
        (Arlib.KV97.cOf (algBlock atoms phi eps delta).epsPrime)
        (algBlock atoms phi eps delta).r))
    (hstep : ∀ i, 0 < step i) [NeZero n]
    (heighth : ∀ i, ENNReal.ofReal ((1 : Real) / 8) ≤
      Ttc.CostedKV97Rounding.roundedMeasure
        (polyHybridContLaw atoms phi eps delta rin Rout step Mw sigma i)
        (integerAcceptance (M atoms phi eps delta) (rho atoms phi eps delta) i.val))
    (i : CubeIndex atoms phi) :
    IsProbabilityMeasure (polyHybridTarget atoms phi eps delta rin Rout step Mw sigma i) := by
  let S := polyHybridFineSampler atoms phi eps delta rin Rout step Mw sigma hsigma
    hbounded hstep heighth i
  letI : IsProbabilityMeasure S.law := S.probability
  rw [← S.stateMarginal]
  exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable

/-- The pointwise per-coin family for the canonical-owner assembler.  Its only
remaining non-geometric premise is the direct canonical `1/8` certificate. -/
noncomputable def polyHybridMarkedFamily
    (V : VolumeAlgorithm n) (omega : V.Ω)
    (rin Rout step Mw : CubeIndex atoms phi → Real)
    (sigma : CubeIndex atoms phi → Measure (Space n))
    (hsigma : ∀ i, IsProbabilityMeasure (sigma i))
    (hbounded : ∀ i, Bornology.IsBounded
      (Arlib.KV97.inflated
        (canonAm (algAtoms atoms phi eps delta) (D atoms phi) i)
        (canonBv (algAtoms atoms phi eps delta) (D atoms phi)
          (latticeScale (rho atoms phi eps delta)) i)
        (Arlib.KV97.cOf (algBlock atoms phi eps delta).epsPrime)
        (algBlock atoms phi eps delta).r))
    (hstep : ∀ i, 0 < step i) [NeZero n]
    (heighth : ∀ i, ENNReal.ofReal ((1 : Real) / 8) ≤
      Ttc.CostedKV97Rounding.roundedMeasure
        (polyHybridContLaw atoms phi eps delta rin Rout step Mw sigma i)
        (integerAcceptance (M atoms phi eps delta) (rho atoms phi eps delta) i.val)) :
    CubeMarkedFamily (CubeIndex atoms phi) (algIndex atoms phi eps delta) :=
  canonicalMarkedFamily (pt atoms phi eps delta)
    (polyHybridTarget atoms phi eps delta rin Rout step Mw sigma)
    (isProbabilityMeasure_polyHybridTarget atoms phi eps delta rin Rout step Mw sigma
      hsigma hbounded hstep heighth)
    (polyHybridFineSampler atoms phi eps delta rin Rout step Mw sigma hsigma
      hbounded hstep heighth)
    (fun i => max (polyVol atoms phi eps delta V omega i.val) 0)
    (fun _ => le_max_right _ _)

theorem polyHybridMarkedFamily_selectedRate
    (V : VolumeAlgorithm n) (omega : V.Ω)
    (hle : HasLatticeEnum (M atoms phi eps delta) (preprocess atoms phi)
      (rho atoms phi eps delta))
    (rin Rout step Mw : CubeIndex atoms phi → Real)
    (sigma : CubeIndex atoms phi → Measure (Space n))
    (hsigma : ∀ i, IsProbabilityMeasure (sigma i))
    (hbounded : ∀ i, Bornology.IsBounded
      (Arlib.KV97.inflated
        (canonAm (algAtoms atoms phi eps delta) (D atoms phi) i)
        (canonBv (algAtoms atoms phi eps delta) (D atoms phi)
          (latticeScale (rho atoms phi eps delta)) i)
        (Arlib.KV97.cOf (algBlock atoms phi eps delta).epsPrime)
        (algBlock atoms phi eps delta).r))
    (hstep : ∀ i, 0 < step i) [NeZero n]
    (heighth : ∀ i, ENNReal.ofReal ((1 : Real) / 8) ≤
      Ttc.CostedKV97Rounding.roundedMeasure
        (polyHybridContLaw atoms phi eps delta rin Rout step Mw sigma i)
        (integerAcceptance (M atoms phi eps delta) (rho atoms phi eps delta) i.val))
    (s : Fin (algIndex atoms phi eps delta)) :
    let F := polyHybridMarkedFamily atoms phi eps delta V omega rin Rout step Mw sigma
      hsigma hbounded hstep heighth
    F.lam (polyOwner atoms phi eps delta hle s) *
        F.q (polyOwner atoms phi eps delta hle s) s.castSucc =
      max (polyHybridRates atoms phi eps delta V omega rin Rout step Mw sigma s) 0 := by
  unfold polyHybridMarkedFamily
  dsimp only
  rw [canonicalMarkedFamily_selectedRate (pt atoms phi eps delta)
    (latticeEnum_injective _ _ _)]
  rw [toReal_polyHybridTarget_singleton_owner atoms phi eps delta hle
    rin Rout step Mw sigma hsigma s]
  let q := polyHybridSampD atoms phi eps delta rin Rout step Mw sigma
      (polyOwner atoms phi eps delta hle s).val (pt atoms phi eps delta s)
  have hq : 0 ≤ q := kv97SampD_nonneg _ _ _ _ _ _
  unfold polyHybridRates rates
  change max (polyVol atoms phi eps delta V omega
      (polyOwner atoms phi eps delta hle s).val) 0 * q =
    max (q * polyVol atoms phi eps delta V omega
      (polyOwner atoms phi eps delta hle s).val) 0
  by_cases hv : 0 ≤ polyVol atoms phi eps delta V omega
      (polyOwner atoms phi eps delta hle s).val
  · rw [max_eq_left hv, max_eq_left (mul_nonneg hq hv), mul_comm]
  · have hv' : polyVol atoms phi eps delta V omega
        (polyOwner atoms phi eps delta hle s).val ≤ 0 := le_of_not_ge hv
    rw [max_eq_right hv', max_eq_right (mul_nonpos_of_nonneg_of_nonpos hq hv')]
    simp

theorem measurable_polyHybridRates (V : VolumeAlgorithm n)
    (rin Rout step Mw : CubeIndex atoms phi → Real)
    (sigma : CubeIndex atoms phi → Measure (Space n)) :
    Measurable[V.mΩ] fun omega : V.Ω =>
      polyHybridRates atoms phi eps delta V omega rin Rout step Mw sigma := by
  letI := V.mΩ
  exact measurable_pi_lambda _ fun _ =>
    measurable_const.mul (measurable_polyVol atoms phi eps delta V _)

/-- Honest coin-indexed TTC trajectory kernel for the hybrid rates. -/
noncomputable def polyHybridKernel (V : VolumeAlgorithm n)
    (rin Rout step Mw : CubeIndex atoms phi → Real)
    (sigma : CubeIndex atoms phi → Measure (Space n)) :
    @Kernel V.Ω (Nat → Fin (algIndex atoms phi eps delta) → Nat) V.mΩ _ :=
  letI := V.mΩ
  { toFun := fun omega =>
      trajLaw (polyHybridRates atoms phi eps delta V omega rin Rout step Mw sigma)
    measurable' := measurable_trajLaw.comp
      (measurable_polyHybridRates atoms phi eps delta V rin Rout step Mw sigma) }

instance isMarkovKernel_polyHybridKernel (V : VolumeAlgorithm n)
    (rin Rout step Mw : CubeIndex atoms phi → Real)
    (sigma : CubeIndex atoms phi → Measure (Space n)) :
    IsMarkovKernel (polyHybridKernel atoms phi eps delta V rin Rout step Mw sigma) :=
  ⟨fun _ => isProbabilityMeasure_trajLaw _⟩

/-- Construct the outer canonical-owner plug-in once the sole outer
measurability seam (a kernel with the displayed fibers) is supplied. -/
noncomputable def polyHybridTrajectoryPlugin
    (V : ExpectedQueryVolumeAlgorithm n)
    (hle : HasLatticeEnum (M atoms phi eps delta) (preprocess atoms phi)
      (rho atoms phi eps delta))
    (rin Rout step Mw : CubeIndex atoms phi → Real)
    (sigma : CubeIndex atoms phi → Measure (Space n))
    (hsigma : ∀ i, IsProbabilityMeasure (sigma i))
    (hbounded : ∀ i, Bornology.IsBounded
      (Arlib.KV97.inflated
        (canonAm (algAtoms atoms phi eps delta) (D atoms phi) i)
        (canonBv (algAtoms atoms phi eps delta) (D atoms phi)
          (latticeScale (rho atoms phi eps delta)) i)
        (Arlib.KV97.cOf (algBlock atoms phi eps delta).epsPrime)
        (algBlock atoms phi eps delta).r))
    (hstep : ∀ i, 0 < step i) [NeZero n]
    (heighth : ∀ i, ENNReal.ofReal ((1 : Real) / 8) ≤
      Ttc.CostedKV97Rounding.roundedMeasure
        (polyHybridContLaw atoms phi eps delta rin Rout step Mw sigma i)
        (integerAcceptance (M atoms phi eps delta) (rho atoms phi eps delta) i.val))
    (K : @Kernel V.Ω
      (Ttc.CostedCanonicalOwnerTTCPlugin.CostedCountPath
        (algIndex atoms phi eps delta)) V.mΩ _)
    (hK : @IsMarkovKernel V.Ω _ V.mΩ _ K)
    (happly : ∀ omega, K omega =
      (polyHybridMarkedFamily atoms phi eps delta V.toVolumeAlgorithm omega
        rin Rout step Mw sigma hsigma hbounded hstep heighth).assembledTrajectoryLaw
          (polyOwner atoms phi eps delta hle)) :
    letI := V.mΩ
    Ttc.CostedCanonicalOwnerTTCPlugin.CanonicalOwnerTrajectoryPlugin
      (CubeIndex atoms phi) (algIndex atoms phi eps delta) V.Ω := by
  letI := V.mΩ
  exact
    { family := fun omega => polyHybridMarkedFamily atoms phi eps delta
        V.toVolumeAlgorithm omega rin Rout step Mw sigma hsigma hbounded hstep heighth
      owner := polyOwner atoms phi eps delta hle
      trajectoryKernel := K
      trajectoryKernel_markov := hK
      trajectoryKernel_apply := happly }

theorem polyHybridTrajectoryPlugin_rate
    (V : ExpectedQueryVolumeAlgorithm n)
    (hle : HasLatticeEnum (M atoms phi eps delta) (preprocess atoms phi)
      (rho atoms phi eps delta))
    (rin Rout step Mw : CubeIndex atoms phi → Real)
    (sigma : CubeIndex atoms phi → Measure (Space n))
    (hsigma : ∀ i, IsProbabilityMeasure (sigma i))
    (hbounded : ∀ i, Bornology.IsBounded
      (Arlib.KV97.inflated
        (canonAm (algAtoms atoms phi eps delta) (D atoms phi) i)
        (canonBv (algAtoms atoms phi eps delta) (D atoms phi)
          (latticeScale (rho atoms phi eps delta)) i)
        (Arlib.KV97.cOf (algBlock atoms phi eps delta).epsPrime)
        (algBlock atoms phi eps delta).r))
    (hstep : ∀ i, 0 < step i) [NeZero n]
    (heighth : ∀ i, ENNReal.ofReal ((1 : Real) / 8) ≤
      Ttc.CostedKV97Rounding.roundedMeasure
        (polyHybridContLaw atoms phi eps delta rin Rout step Mw sigma i)
        (integerAcceptance (M atoms phi eps delta) (rho atoms phi eps delta) i.val))
    (K : @Kernel V.Ω
      (Ttc.CostedCanonicalOwnerTTCPlugin.CostedCountPath
        (algIndex atoms phi eps delta)) V.mΩ _)
    (hK : @IsMarkovKernel V.Ω _ V.mΩ _ K)
    (happly : ∀ omega, K omega =
      (polyHybridMarkedFamily atoms phi eps delta V.toVolumeAlgorithm omega
        rin Rout step Mw sigma hsigma hbounded hstep heighth).assembledTrajectoryLaw
          (polyOwner atoms phi eps delta hle))
    (omega : V.Ω) (s : Fin (algIndex atoms phi eps delta)) :
    letI := V.mΩ
    let P := polyHybridTrajectoryPlugin atoms phi eps delta V hle rin Rout step Mw
      sigma hsigma hbounded hstep heighth K hK happly
    (P.family omega).lam (P.owner s) * (P.family omega).q (P.owner s) s.castSucc =
      max (polyHybridRates atoms phi eps delta V.toVolumeAlgorithm omega
        rin Rout step Mw sigma s) 0 := by
  letI := V.mΩ
  dsimp only [polyHybridTrajectoryPlugin]
  exact polyHybridMarkedFamily_selectedRate atoms phi eps delta V.toVolumeAlgorithm
    omega hle rin Rout step Mw sigma hsigma hbounded hstep heighth s

/-- Exact cost-erasure theorem for the hybrid-rate plug-in.  This is parallel
to the legacy `map_forgetCost_canonicalCostedPolyJoint`, without identifying the
two rate families. -/
theorem map_forgetCost_polyHybridCanonicalJoint
    (V : ExpectedQueryVolumeAlgorithm n)
    (rin Rout step Mw : CubeIndex atoms phi → Real)
    (sigma : CubeIndex atoms phi → Measure (Space n))
    (P : @Ttc.CostedCanonicalOwnerTTCPlugin.CanonicalOwnerTrajectoryPlugin
      (CubeIndex atoms phi) _ (algIndex atoms phi eps delta) V.Ω V.mΩ)
    (hrate : letI := V.mΩ
      ∀ omega s, (P.family omega).lam (P.owner s) *
          (P.family omega).q (P.owner s) s.castSucc =
        max (polyHybridRates atoms phi eps delta V.toVolumeAlgorithm omega
          rin Rout step Mw sigma s) 0) :
    letI := V.mΩ
    Measure.map (Prod.map id
        (Ttc.SequentialCostedPathLumping.pathMap Prod.snd))
      (Ttc.CostedCanonicalOwnerTTCPlugin.canonicalCostedPolyJoint
        (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P) =
      V.μ.compProd (polyHybridKernel atoms phi eps delta V.toVolumeAlgorithm
        rin Rout step Mw sigma) := by
  letI := V.mΩ
  letI : IsProbabilityMeasure V.μ := V.isProb
  letI : IsMarkovKernel P.trajectoryKernel := P.trajectoryKernel_markov
  have hpoint : ∀ omega,
      Measure.map (Ttc.SequentialCostedPathLumping.pathMap Prod.snd)
          (P.trajectoryKernel omega) =
        polyHybridKernel atoms phi eps delta V.toVolumeAlgorithm
          rin Rout step Mw sigma omega := by
    intro omega
    rw [P.map_forgetCost_trajectoryKernel]
    calc
      trajLaw (fun s => (P.family omega).lam (P.owner s) *
          (P.family omega).q (P.owner s) s.castSucc) =
          trajLaw (fun s => max
            (polyHybridRates atoms phi eps delta V.toVolumeAlgorithm omega
              rin Rout step Mw sigma s) 0) := by
            congr 1
            funext s
            exact hrate omega s
      _ = trajLaw (polyHybridRates atoms phi eps delta V.toVolumeAlgorithm omega
          rin Rout step Mw sigma) :=
        (trajLaw_max_zero _).symm
  simpa only [Ttc.CostedCanonicalOwnerTTCPlugin.canonicalCostedPolyJoint,
    Measure.map_id] using
    (Ttc.SequentialCostedPathLumping.map_compProd_prodMap_of_pointwise
      V.μ P.trajectoryKernel
      (polyHybridKernel atoms phi eps delta V.toVolumeAlgorithm rin Rout step Mw sigma)
      measurable_id
      (Ttc.SequentialCostedPathLumping.measurable_pathMap measurable_snd) hpoint)

/-- Accuracy transfer for hybrid rates.  The remaining premise `hsemantic` is
exactly the legacy theorem that still has to be generalized from `polySampD` to
an arbitrary certified sampler law. -/
theorem polyHybridCanonicalJoint_accuracy_of_semantic
    (V : ExpectedQueryVolumeAlgorithm n)
    (rin Rout step Mw : CubeIndex atoms phi → Real)
    (sigma : CubeIndex atoms phi → Measure (Space n))
    (P : @Ttc.CostedCanonicalOwnerTTCPlugin.CanonicalOwnerTrajectoryPlugin
      (CubeIndex atoms phi) _ (algIndex atoms phi eps delta) V.Ω V.mΩ)
    (hrate : letI := V.mΩ
      ∀ omega s, (P.family omega).lam (P.owner s) *
          (P.family omega).q (P.owner s) s.castSucc =
        max (polyHybridRates atoms phi eps delta V.toVolumeAlgorithm omega
          rin Rout step Mw sigma s) 0)
    (hsemantic : letI := V.mΩ
      1 - delta ≤
        ((V.μ.compProd (polyHybridKernel atoms phi eps delta V.toVolumeAlgorithm
          rin Rout step Mw sigma))
          (Ttc.CostedTTCPlugin.idealPolyAccuracyEvent
            (atoms := atoms) (phi := phi) (eps := eps) (delta := delta)
            V.toVolumeAlgorithm)).toReal) :
    letI := V.mΩ
    1 - delta ≤
      ((Ttc.CostedCanonicalOwnerTTCPlugin.canonicalCostedPolyJoint
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P)
        (Ttc.CostedCanonicalOwnerTTCPlugin.canonicalCostedPolyAccuracyEvent
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P)).toReal := by
  letI := V.mΩ
  letI : IsProbabilityMeasure V.μ := V.isProb
  letI : IsMarkovKernel P.trajectoryKernel := P.trajectoryKernel_markov
  let stateMap :
      V.Ω × Ttc.CostedCanonicalOwnerTTCPlugin.CostedCountPath
          (algIndex atoms phi eps delta) →
        V.Ω × Ttc.CostedCanonicalOwnerTTCPlugin.CountPath
          (algIndex atoms phi eps delta) :=
    Prod.map id (Ttc.SequentialCostedPathLumping.pathMap Prod.snd)
  let idealEvent := Ttc.CostedTTCPlugin.idealPolyAccuracyEvent
    (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V.toVolumeAlgorithm
  have hstate : Measurable stateMap := measurable_id.prodMap
    (Ttc.SequentialCostedPathLumping.measurable_pathMap measurable_snd)
  have hideal : MeasurableSet idealEvent :=
    Ttc.CostedTTCPlugin.measurableSet_idealPolyAccuracyEvent V.toVolumeAlgorithm
  have hevent :
      Ttc.CostedCanonicalOwnerTTCPlugin.canonicalCostedPolyAccuracyEvent
        (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P =
      stateMap ⁻¹' idealEvent := rfl
  have hjoint := map_forgetCost_polyHybridCanonicalJoint atoms phi eps delta V
    rin Rout step Mw sigma P hrate
  have heq :
      (Ttc.CostedCanonicalOwnerTTCPlugin.canonicalCostedPolyJoint
        (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P)
          (Ttc.CostedCanonicalOwnerTTCPlugin.canonicalCostedPolyAccuracyEvent
            (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P) =
      (V.μ.compProd (polyHybridKernel atoms phi eps delta V.toVolumeAlgorithm
        rin Rout step Mw sigma)) idealEvent := by
    rw [hevent, ← Measure.map_apply hstate hideal, hjoint]
  rwa [heq]

/-- Hybrid accuracy plus the generic canonical-owner expected-query bound.
All operational sampling details are discharged before this theorem; the sole
semantic premise is the generalized TTC accuracy statement above. -/
theorem polyHybridCanonicalJoint_accuracy_and_expectedQueries_of_semantic
    (V : ExpectedQueryVolumeAlgorithm n)
    (rin Rout step Mw : CubeIndex atoms phi → Real)
    (sigma : CubeIndex atoms phi → Measure (Space n))
    (P : @Ttc.CostedCanonicalOwnerTTCPlugin.CanonicalOwnerTrajectoryPlugin
      (CubeIndex atoms phi) _ (algIndex atoms phi eps delta) V.Ω V.mΩ)
    (hrate : letI := V.mΩ
      ∀ omega s, (P.family omega).lam (P.owner s) *
          (P.family omega).q (P.owner s) s.castSucc =
        max (polyHybridRates atoms phi eps delta V.toVolumeAlgorithm omega
          rin Rout step Mw sigma s) 0)
    (hsemantic : letI := V.mΩ
      1 - delta ≤
        ((V.μ.compProd (polyHybridKernel atoms phi eps delta V.toVolumeAlgorithm
          rin Rout step Mw sigma))
          (Ttc.CostedTTCPlugin.idealPolyAccuracyEvent
            (atoms := atoms) (phi := phi) (eps := eps) (delta := delta)
            V.toVolumeAlgorithm)).toReal)
    {J : Nat} (hJ : 0 < J) :
    letI := V.mΩ
    (1 - delta ≤
      ((Ttc.CostedCanonicalOwnerTTCPlugin.canonicalCostedPolyJoint
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P)
        (Ttc.CostedCanonicalOwnerTTCPlugin.canonicalCostedPolyAccuracyEvent
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P)).toReal) ∧
    ((∫⁻ z, Ttc.CostedCanonicalOwnerTTCPlugin.canonicalActualPolyQueryCost
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P J z
        ∂Ttc.CostedCanonicalOwnerTTCPlugin.canonicalCostedPolyJoint
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V P) ≤
      Ttc.ttcPolyVolumeQueryBound atoms phi eps delta V +
        ∫⁻ omega, P.expectedSampleQueries omega ∂V.μ) := by
  letI := V.mΩ
  exact ⟨polyHybridCanonicalJoint_accuracy_of_semantic atoms phi eps delta V
      rin Rout step Mw sigma P hrate hsemantic,
    Ttc.CostedCanonicalOwnerTTCPlugin.lintegral_canonicalActualPolyQueryCost_le
      V P hJ⟩

#print axioms toReal_polyHybridTarget_singleton_owner
#print axioms polyHybridFineSampler
#print axioms polyHybridMarkedFamily
#print axioms polyHybridMarkedFamily_selectedRate
#print axioms polyHybridTrajectoryPlugin
#print axioms polyHybridTrajectoryPlugin_rate
#print axioms map_forgetCost_polyHybridCanonicalJoint
#print axioms polyHybridCanonicalJoint_accuracy_of_semantic
#print axioms polyHybridCanonicalJoint_accuracy_and_expectedQueries_of_semantic

end Ttc.ConcreteHybridCanonicalOwnerPoly
